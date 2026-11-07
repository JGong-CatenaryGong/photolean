"""Lean certificate harness for the relation audit.

For every manifest certificate the audit generates a temporary Lean file under
the isolated checkout (``.lake/tmp/relation-audit``) or the system temporary
directory.  The generated file contains, for each certificate:

    #check <certificate>                                   -- existence
    example : certificateKind <certificate> = <Kind.k> := rfl   -- kind equality
    #print axioms <certificate>                            -- axiom footprint

Additional declarations used as evidence (premise signatures, rfl witnesses,
kind-specific witnesses) get their own existence and axiom checks.  Premise
badges beyond ``explicit`` and composition bridge/discharge evidence are not
Lean-checked for existence: contract section 6 requires typed expected-evidence
checks tied to the record and premise IDs, so the validator rejects those
claims instead of treating declaration existence as evidence.

The Lean process is run through ``proofs/scripts/lake env lean --json`` so the
repository's pinned toolchain and mathlib cache are used.  If Lean cannot run,
the outcome is SKIP, never PASS: the caller turns a skip into a non-zero exit.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from typing import Any, Iterable


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

_AXIOM_DATA = re.compile(
    r"^'(?P<decl>.+?)' (?:does not depend on any axioms"
    r"|depends on axioms: \[(?P<axioms>.*)\])$",
    re.DOTALL,
)


@dataclass
class LineCheck:
    """One generated Lean command, mapped back to one audit check."""

    line: int
    check_id: str
    role: str           # "exists" | "kind" | "axioms"
    decl: str
    location: str
    fail_code: str
    need_info: bool = False
    binder: str | None = None
    expected_axioms: frozenset[str] | None = None
    pass_code: str = "lean.certificateKind"


@dataclass
class LeanFinding:
    status: str         # PASS | FAIL | SKIP
    code: str
    message: str
    location: str = ""


@dataclass
class LeanOutcome:
    status: str
    findings: list[LeanFinding] = field(default_factory=list)
    source: str = ""
    source_path: str = ""
    command: list[str] = field(default_factory=list)
    skipped_reason: str = ""


class SourceBuilder:
    """Builds the generated Lean file and remembers line -> check mappings."""

    def __init__(self, imports: Iterable[str] = (), prelude: str | None = None):
        self.imports = sorted({item for item in imports if item})
        self.prelude = prelude
        self.lines: list[str] = []
        self.checks: list[LineCheck] = []

    def _emit(self, text: str) -> int:
        self.lines.append(text)
        return len(self.lines)

    def _add(self, text: str, **kwargs: Any) -> None:
        line = self._emit(text)
        self.checks.append(LineCheck(line=line, **kwargs))

    def add_certificate(self, check_id: str, location: str, certificate: str,
                        kind_function: str, expected_constructor: str,
                        kind_fail_code: str = "lean.certificateKind",
                        expected_axioms: frozenset[str] | None = None) -> None:
        self._add(
            f"#check {certificate}",
            check_id=f"{check_id}.exists",
            role="exists",
            decl=certificate,
            location=location,
            fail_code="lean.existence",
            need_info=True,
        )
        self._add(
            f"example : {kind_function} {certificate} = {expected_constructor} := rfl",
            check_id=f"{check_id}.kind",
            role="kind",
            decl=certificate,
            location=location,
            fail_code=kind_fail_code,
        )
        self._add(
            f"#print axioms {certificate}",
            check_id=f"{check_id}.axioms",
            role="axioms",
            decl=certificate,
            location=location,
            fail_code="lean.axioms",
            need_info=True,
            expected_axioms=expected_axioms,
        )

    def add_term_equality(self, check_id: str, location: str,
                          lhs: str, rhs: str,
                          fail_code: str = "lean.rflCheck",
                          pass_code: str = "lean.rflCheck") -> None:
        self._add(
            f"example : {lhs} = {rhs} := rfl",
            check_id=check_id,
            role="kind",
            decl=f"{lhs} = {rhs}",
            location=location,
            fail_code=fail_code,
            pass_code=pass_code,
        )

    def add_declaration(self, check_id: str, location: str, declaration: str,
                        binder: str | None = None,
                        existence_code: str = "lean.evidenceExistence",
                        axioms_code: str = "lean.axioms",
                        expected_axioms: frozenset[str] | None = None) -> None:
        if not declaration:
            return
        self._add(
            f"#check {declaration}",
            check_id=f"{check_id}.exists",
            role="exists",
            decl=declaration,
            location=location,
            fail_code=existence_code,
            need_info=True,
            binder=binder,
        )
        self._add(
            f"#print axioms {declaration}",
            check_id=f"{check_id}.axioms",
            role="axioms",
            decl=declaration,
            location=location,
            fail_code=axioms_code,
            need_info=True,
            expected_axioms=expected_axioms,
        )

    def build(self) -> str:
        header = [
            "-- Generated by tools/relation_audit.py for one audit run.",
            "-- Temporary file; not part of the repository.",
        ]
        body = [f"import {module}" for module in self.imports]
        if self.prelude:
            body.extend(self.prelude.splitlines())
        prefix = header + body + [""]
        offset = len(prefix)
        for check in self.checks:
            check.line += offset
        rendered = prefix + self.lines + [""]
        return "\n".join(rendered)


class LeanHarness:
    def __init__(self, repo_root: str, lean_roots: Iterable[str] = (),
                 timeout: float = 300.0, keep_temps: bool = False):
        self.repo_root = os.path.abspath(repo_root)
        self.lean_roots = [os.path.abspath(root) for root in lean_roots if root]
        self.timeout = timeout
        self.keep_temps = keep_temps
        self.lake = os.path.join(self.repo_root, "proofs", "scripts", "lake")
        self.toolchain_lean = os.path.join(
            self.repo_root, ".toolchain", "lean-4.17.0-linux", "bin", "lean")

    # --------------------------------------------------------------- readiness
    def unavailable_reason(self) -> str | None:
        if not os.path.isfile(self.lake):
            return f"missing launcher {self.lake}"
        if not os.access(self.lake, os.X_OK):
            return f"launcher is not executable: {self.lake}"
        if not os.path.isfile(self.toolchain_lean):
            return f"missing Lean toolchain binary {self.toolchain_lean}"
        return None

    # ------------------------------------------------------------------ build
    def build_source(self, checks: Iterable[Any], imports: Iterable[str] = (),
                     prelude: str | None = None) -> tuple[str, list[LineCheck]]:
        """Build source from ``(check_id, location, description)`` tuples.

        ``description`` is a dict with one of the shapes accepted by
        ``SourceBuilder.add_certificate`` / ``add_declaration``.  This keeps the
        validator independent from the Lean API surface.
        """
        builder = SourceBuilder(imports=imports, prelude=prelude)
        for spec in checks:
            if spec["shape"] == "certificate":
                builder.add_certificate(
                    check_id=spec["check_id"],
                    location=spec["location"],
                    certificate=spec["certificate"],
                    kind_function=spec["kind_function"],
                    expected_constructor=spec["expected_constructor"],
                    kind_fail_code=spec.get("kind_fail_code", "lean.certificateKind"),
                    expected_axioms=spec.get("expected_axioms"),
                )
            elif spec["shape"] == "term_equality":
                builder.add_term_equality(
                    check_id=spec["check_id"],
                    location=spec["location"],
                    lhs=spec["lhs"],
                    rhs=spec["rhs"],
                    fail_code=spec.get("fail_code", "lean.rflCheck"),
                    pass_code=spec.get("pass_code", "lean.rflCheck"),
                )
            elif spec["shape"] == "declaration":
                builder.add_declaration(
                    check_id=spec["check_id"],
                    location=spec["location"],
                    declaration=spec["declaration"],
                    binder=spec.get("binder"),
                    existence_code=spec.get("existence_code", "lean.evidenceExistence"),
                    axioms_code=spec.get("axioms_code", "lean.axioms"),
                    expected_axioms=spec.get("expected_axioms"),
                )
            else:
                raise ValueError(f"unknown Lean check shape {spec['shape']!r}")
        return builder.build(), builder.checks

    # -------------------------------------------------------------------- run
    def run(self, checks: Iterable[Any], imports: Iterable[str] = (),
            prelude: str | None = None) -> LeanOutcome:
        reason = self.unavailable_reason()
        if reason:
            return LeanOutcome(
                status="SKIP",
                findings=[LeanFinding("SKIP", "lean.unavailable",
                                      f"Lean checks did not run: {reason}")],
                skipped_reason=reason,
            )
        source, line_checks = self.build_source(checks, imports, prelude)
        temp_dir = None
        try:
            temp_dir = self._make_temp_dir()
            path = os.path.join(temp_dir, "RelationAuditCheck.lean")
            with open(path, "w", encoding="utf-8") as handle:
                handle.write(source)
            command = [self.lake, "env", "lean", "--json", path]
            env = os.environ.copy()
            if self.lean_roots:
                existing = env.get("LEAN_PATH", "")
                parts = list(self.lean_roots)
                if existing:
                    parts.append(existing)
                env["LEAN_PATH"] = os.pathsep.join(parts)
            try:
                completed = subprocess.run(
                    command,
                    cwd=self.repo_root,
                    env=env,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    timeout=self.timeout,
                )
            except subprocess.TimeoutExpired:
                return LeanOutcome(
                    status="FAIL",
                    findings=[LeanFinding(
                        "FAIL", "lean.timeout",
                        f"Lean check timed out after {self.timeout:.0f}s")],
                    source=source,
                    source_path=path if self.keep_temps else "",
                    command=command,
                )
            except OSError as exc:
                return LeanOutcome(
                    status="SKIP",
                    findings=[LeanFinding("SKIP", "lean.unavailable",
                                          f"could not start Lean: {exc}")],
                    source=source,
                    command=command,
                    skipped_reason=str(exc),
                )
            outcome = self._parse(completed, line_checks, source, path, command)
            return outcome
        finally:
            if temp_dir and not self.keep_temps:
                shutil.rmtree(temp_dir, ignore_errors=True)

    def _make_temp_dir(self) -> str:
        parent = os.path.join(self.repo_root, ".lake", "tmp")
        try:
            os.makedirs(os.path.join(parent, "relation-audit"), exist_ok=True)
            return tempfile.mkdtemp(prefix="run-", dir=os.path.join(parent, "relation-audit"))
        except OSError:
            return tempfile.mkdtemp(prefix="relation-audit-")

    # ------------------------------------------------------------------ parse
    def _parse(self, completed: subprocess.CompletedProcess, line_checks: list[LineCheck],
               source: str, path: str, command: list[str]) -> LeanOutcome:
        findings: list[LeanFinding] = []
        by_line: dict[int, LineCheck] = {check.line: check for check in line_checks}
        errors: dict[int, list[str]] = {}
        infos: dict[int, list[str]] = {}
        global_errors: list[str] = []
        warnings: list[str] = []

        for raw in completed.stdout.splitlines():
            raw = raw.strip()
            if not raw:
                continue
            try:
                message = json.loads(raw)
            except json.JSONDecodeError:
                # Lean occasionally prints non-JSON progress text; keep it as
                # an unmapped diagnostic so it cannot be lost.
                global_errors.append(raw)
                continue
            if not isinstance(message, dict):
                continue
            data = str(message.get("data", ""))
            severity = message.get("severity", "")
            pos = message.get("pos") or {}
            line = pos.get("line") if isinstance(pos, dict) else None
            if severity == "error":
                if isinstance(line, int) and line in by_line:
                    errors.setdefault(line, []).append(data)
                else:
                    global_errors.append(data)
            elif severity == "information":
                if isinstance(line, int):
                    infos.setdefault(line, []).append(data)
            elif severity == "warning":
                warnings.append(data)

        def add(status: str, code: str, message: str, location: str) -> None:
            findings.append(LeanFinding(status, code, message, location))

        for line, check in sorted(by_line.items()):
            if line in errors:
                detail = " | ".join(errors[line])
                add("FAIL", check.fail_code,
                    f"Lean rejected {check.decl!r}: {detail[:500]}", check.location)
                continue
            if check.role == "kind":
                add("PASS", check.pass_code,
                    f"{check.check_id} elaborated with rfl", check.location)
                continue
            data_items = infos.get(line, [])
            if check.need_info and not data_items:
                add("FAIL", "lean.missingInfo",
                    f"no Lean information message for {check.decl!r}", check.location)
                continue
            if check.role == "exists":
                text = data_items[-1]
                if check.binder and check.binder not in text:
                    add("FAIL", "lean.premiseSignature",
                        f"binder {check.binder!r} not found in checked signature "
                        f"of {check.decl!r}", check.location)
                    continue
                add("PASS", "lean.exists",
                    f"declaration exists: {check.decl}", check.location)
                continue
            if check.role == "axioms":
                axioms = _parse_axioms(data_items[-1])
                if axioms is None:
                    add("FAIL", "lean.axioms",
                        f"could not parse axiom footprint of {check.decl!r}: "
                        f"{data_items[-1][:300]!r}", check.location)
                    continue
                disallowed = sorted(set(axioms) - ALLOWED_AXIOMS)
                if disallowed:
                    add("FAIL", "lean.axioms",
                        f"{check.decl!r} depends on disallowed axioms: "
                        f"{', '.join(disallowed)}", check.location)
                    continue
                if check.expected_axioms is not None and axioms != set(check.expected_axioms):
                    add("FAIL", "lean.axiomFootprint",
                        f"{check.decl!r} declares axiom footprint "
                        f"{sorted(check.expected_axioms)!r} but Lean reports "
                        f"{sorted(axioms)!r}", check.location)
                    continue
                rendered = ", ".join(sorted(axioms)) if axioms else "none"
                add("PASS", "lean.axioms",
                    f"allowed axiom footprint for {check.decl}: {rendered}",
                    check.location)

        if global_errors:
            add("FAIL", "lean.source",
                "Lean reported errors outside generated check lines: "
                + " | ".join(global_errors)[:800], "<lean>")
        if completed.returncode != 0 and not errors and not global_errors:
            stderr = (completed.stderr or "").strip()
            add("FAIL", "lean.exit",
                f"Lean exited with status {completed.returncode}: {stderr[:500]}",
                "<lean>")
        if completed.returncode == 0 and not errors and not global_errors:
            add("PASS", "lean.run", f"Lean accepted {len(line_checks)} generated checks",
                "<lean>")
        if warnings:
            add("PASS", "lean.warnings",
                f"{len(warnings)} Lean warning(s); axiom footprints decide acceptance",
                "<lean>")

        status = "FAIL" if any(item.status == "FAIL" for item in findings) else "PASS"
        return LeanOutcome(
            status=status,
            findings=findings,
            source=source,
            source_path=path if self.keep_temps else "",
            command=command,
        )


def _parse_axioms(data: str) -> set[str] | None:
    match = _AXIOM_DATA.match(data.strip())
    if not match:
        return None
    if "does not depend" in data:
        return set()
    raw = match.group("axioms") or ""
    return {item.strip() for item in raw.split(",") if item.strip()}
