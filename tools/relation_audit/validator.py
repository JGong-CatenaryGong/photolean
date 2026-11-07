"""Fail-closed semantic validator for the certified relation audit.

The validator reads the manifest and the checked-in schema, adapts to the
schema's property spellings (see ``interface.py``), and runs every gate listed
in docs/RELATION-AUDIT-CONTRACT.md section 8.  Any failed check, and any check
that could not run, makes the process exit non-zero.

Nothing here writes to the repository: the only generated artifact is the
temporary Lean file inside ``.lake/tmp/relation-audit`` (or the system temporary
directory), which is removed after the run.
"""

from __future__ import annotations

import hashlib
import itertools
import os
import re
import subprocess
from typing import Any, Iterable

from . import json_schema
from .interface import SchemaInterface
from .lean import ALLOWED_AXIOMS, LeanHarness
from .report import Report


CERTIFIED_KINDS = (
    "definitionalIdentity",
    "implication",
    "equivalence",
    "conditionalComposition",
    "observationalEquivalence",
    "distinguishability",
    "refutation",
)
AUDIT_STATUSES = ("certified", "unresolved", "notEstablished", "outOfScope")
NON_CERTIFICATE_STATUSES = tuple(s for s in AUDIT_STATUSES if s != "certified")
PREMISE_BADGES = ("explicit", "nonvacuous", "nonredundant", "weakest")
# Contract section 6: these badges need typed expected-evidence tied to the
# record and premise IDs.  Declaration existence (even with an allowed axiom
# footprint) is insufficient, so until the typed checks exist the validator
# rejects every claim instead of passing it.
UNTYPED_BADGES = {
    "nonvacuous":
        "non-vacuity needs typed evidence of `exists delta, Pi delta` tied to the "
        "record and premise IDs",
    "nonredundant":
        "non-redundancy needs a typed residual-context countermodel for every "
        "premise, tied to the record and premise IDs",
    "weakest":
        "weakest needs a typed minimality proof over the declared alternative "
        "premise preorder, tied to the record and premise IDs",
}
SCOPE_KINDS = ("global", "restricted", "outOfScope")
DEPENDENCY_KINDS = ("leanProbe", "sourceScan", "census", "search")
DISTINGUISHABILITY_FORMS = ("separatingObservation", "identifiabilityDecoder")

EXPECTED_THEORY_COUNT = 17
EXPECTED_PAIR_COUNT = EXPECTED_THEORY_COUNT * (EXPECTED_THEORY_COUNT - 1) // 2

# Definitions the semantic model needs to discover.  Nested inline objects
# (badges, bridges, translations) may be spelled differently or inlined; they
# are read through the alias table instead.
REQUIRED_DEFS = ("manifest", "snapshot", "scope", "statement", "query",
                 "certificate", "record")

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_GIT_SHA_RE = re.compile(r"^[0-9a-f]{7,40}$")
_URL_RE = re.compile(r"^(?:https?://|doi:|urn:)")
_MISSING = object()


class ContractError(Exception):
    """A manifest or schema file could not be loaded at all."""


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: str) -> str:
    with open(path, "rb") as handle:
        return sha256_bytes(handle.read())


def _nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _string_list(value: Any) -> bool:
    return isinstance(value, list) and all(isinstance(item, str) for item in value)


def _lean_string(value: str) -> str:
    """Render a Lean string literal, escaping quotes and backslashes."""
    escaped = value.replace("\\", "\\\\").replace('"', '\\"')
    return f'"{escaped}"'


def _lean_string_list(values: Iterable[str]) -> str:
    return "[" + ", ".join(_lean_string(item) for item in values) + "]"


def _lean_string_lists(values: Iterable[Iterable[str]]) -> str:
    return "[" + ", ".join(_lean_string_list(items) for items in values) + "]"


class AuditValidator:
    def __init__(self, manifest: dict[str, Any], schema: json_schema.Schema,
                 repo_root: str, manifest_path: str, schema_path: str,
                 mode: str = "full", no_lean: bool = False,
                 lean_roots: Iterable[str] = (), lean_timeout: float = 300.0,
                 keep_temps: bool = False, lean_source_out: str | None = None):
        if mode not in ("full", "pilot"):
            raise ValueError(f"unknown audit mode {mode!r}")
        if not isinstance(manifest, dict):
            raise ContractError("manifest root must be a JSON object")
        self.manifest = manifest
        self.schema = schema
        self.repo_root = os.path.abspath(repo_root)
        self.manifest_path = manifest_path
        self.schema_path = schema_path
        self.mode = mode
        self.no_lean = no_lean
        self.lean_roots = list(lean_roots)
        self.lean_timeout = lean_timeout
        self.keep_temps = keep_temps
        self.lean_source_out = lean_source_out
        self.iface = SchemaInterface(schema)
        self.report = Report(manifest=manifest_path, schema=schema_path, mode=mode)
        self.harness = LeanHarness(self.repo_root, self.lean_roots,
                                   timeout=lean_timeout, keep_temps=keep_temps)

        self.inventory: list[str] = []
        self.snapshots: list[dict[str, Any]] = []
        self.scopes: list[dict[str, Any]] = []
        self.statements: list[dict[str, Any]] = []
        self.queries: list[dict[str, Any]] = []
        self.certificates: list[dict[str, Any]] = []
        self.records: list[dict[str, Any]] = []

        self.snapshot_map: dict[str, dict[str, Any]] = {}
        self.scope_map: dict[str, dict[str, Any]] = {}
        self.statement_map: dict[str, dict[str, Any]] = {}
        self.query_map: dict[str, dict[str, Any]] = {}
        self.certificate_map: dict[str, dict[str, Any]] = {}
        self.record_map: dict[str, dict[str, Any]] = {}

        self.certificate_premises: dict[str, dict[str, dict[str, Any]]] = {}
        self.record_premises: dict[str, dict[str, dict[str, Any]]] = {}
        self.lean_specs: list[dict[str, Any]] = []
        self._git_object_cache: dict[tuple[str, str], bytes | None] = {}
        self._artifact_hash_checked: set[tuple[str, str, str]] = set()
        self.provenance_checked = 0
        self._schema_hash = ""
        self._toolchain = ""
        self._mathlib_rev = ""
        self._head_sha = ""

        self.structure_gate = self.report.gate("structure", "JSON/schema, unique IDs, required fields")
        self.reference_gate = self.report.gate("references", "endpoint, query, scope, snapshot and certificate resolution")
        self.semantics_gate = self.report.gate("semantics", "statuses, conflicts, premises, badges, composition")
        self.provenance_gate = self.report.gate("provenance", "source provenance, rationale, dependency evidence")
        self.snapshot_gate = self.report.gate("snapshot", "toolchain, schema and artifact hashes")
        self.coverage_gate = self.report.gate("coverage", "17-theory inventory and 136-pair registry coverage")
        self.lean_gate = self.report.gate("lean", "certificate existence, certificateKind equality, axioms")

    # ------------------------------------------------------------------ public
    def run(self) -> Report:
        self._check_schema()
        self._collect()
        self._check_ids()
        self._check_enums()
        self._check_scopes()
        self._check_statements()
        self._check_queries()
        self._check_snapshots()
        self._check_certificates()
        self._check_records()
        self._check_lean()
        self._finalize()
        return self.report

    # ------------------------------------------------------------------ schema
    def _check_schema(self) -> None:
        errors = self.schema.validate(self.manifest)
        if errors:
            for error in errors:
                self.structure_gate.fail("schema.invalid", error.message, error.path)
        else:
            self.structure_gate.pass_(
                "schema.valid", "manifest validates against the checked-in schema")
        discovered = self.iface.discovered()
        missing_defs = sorted(kind for kind in REQUIRED_DEFS
                              if discovered.get(kind) == "<absent>")
        if missing_defs:
            self.structure_gate.fail(
                "schema.interface",
                "schema does not expose recognizable definitions for: "
                + ", ".join(missing_defs),
                "<schema>")
        self.report.metadata["interface"] = self.iface.expected_interface()

    # ----------------------------------------------------------------- collect
    def _list(self, kind: str) -> list[dict[str, Any]]:
        raw = self.iface.get(self.manifest, "manifest", kind, _MISSING)
        if raw is _MISSING:
            self.structure_gate.fail(
                "interface.missingField", f"manifest has no {kind!r} list", "<manifest>")
            return []
        if not isinstance(raw, list):
            self.structure_gate.fail(
                "interface.wrongType", f"manifest {kind!r} must be an array", kind)
            return []
        entries: list[dict[str, Any]] = []
        for index, item in enumerate(raw):
            if isinstance(item, dict):
                entries.append(item)
            else:
                self.structure_gate.fail(
                    "structure.entry", f"{kind}[{index}] is not an object", f"{kind}[{index}]")
        return entries

    def _collect(self) -> None:
        raw_inventory = self.iface.get(self.manifest, "manifest", "theoryInventory", [])
        self.inventory = [item for item in raw_inventory if isinstance(item, str)] \
            if isinstance(raw_inventory, list) else []
        self.snapshots = self._list("snapshots")
        self.scopes = self._list("scopes")
        self.statements = self._list("statements")
        self.queries = self._list("queries")
        self.certificates = self._list("certificates")
        self.records = self._list("records")

        self._schema_hash = sha256_file(self.schema_path)
        toolchain_path = os.path.join(self.repo_root, "lean-toolchain")
        if os.path.isfile(toolchain_path):
            with open(toolchain_path, encoding="utf-8") as handle:
                self._toolchain = handle.read().strip()
        manifest_path = os.path.join(self.repo_root, "lake-manifest.json")
        if os.path.isfile(manifest_path):
            import json
            try:
                with open(manifest_path, encoding="utf-8") as handle:
                    lake_manifest = json.load(handle)
                for package in lake_manifest.get("packages", []):
                    if isinstance(package, dict) and package.get("name") == "mathlib":
                        self._mathlib_rev = str(package.get("rev", ""))
                        break
            except (OSError, ValueError, TypeError):
                self._mathlib_rev = ""
        self._head_sha = self._git(["rev-parse", "HEAD"], default="").strip()
        self.report.metadata.update({
            "schemaVersion": self.iface.get(
                self.manifest, "manifest", "schemaVersion", None),
            "schemaSha256": self._schema_hash,
            "toolchain": self._toolchain,
            "headSha": self._head_sha,
            "manifestSha256": sha256_file(self.manifest_path),
            "theoryCount": len(self.inventory),
            "recordCount": len(self.records),
            "certificateCount": len(self.certificates),
            "snapshots": [self.iface.get(item, "snapshot", "id", "?")
                          for item in self.snapshots],
        })

    # --------------------------------------------------------------------- IDs
    def _check_ids(self) -> None:
        mapping_by_kind = {
            "snapshots": "snapshot_map",
            "scopes": "scope_map",
            "statements": "statement_map",
            "queries": "query_map",
            "certificates": "certificate_map",
            "records": "record_map",
        }
        singulars = {
            "snapshots": "snapshot", "scopes": "scope", "statements": "statement",
            "queries": "query", "certificates": "certificate", "records": "record",
        }
        for kind, attribute in mapping_by_kind.items():
            items = getattr(self, kind)
            singular = singulars[kind]
            mapping: dict[str, dict[str, Any]] = {}
            for index, item in enumerate(items):
                location = f"{kind}[{index}]"
                ident = self.iface.get(item, singular, "id", None)
                if not _nonempty_string(ident):
                    self.structure_gate.fail(
                        "id.missing", f"{kind}[{index}] has no non-empty id", location)
                    continue
                if ident in mapping:
                    self.structure_gate.fail(
                        "id.duplicate", f"duplicate id {ident!r} in {kind}", location)
                    continue
                mapping[ident] = item
            setattr(self, attribute, mapping)
        if not self.structure_gate.failures():
            self.structure_gate.pass_(
                "id.unique",
                f"unique ids: {len(self.snapshot_map)} snapshots, {len(self.scope_map)} scopes, "
                f"{len(self.statement_map)} statements, {len(self.query_map)} queries, "
                f"{len(self.certificate_map)} certificates, {len(self.record_map)} records")

    # --------------------------------------------------------------- inventory
    def _check_enums(self) -> None:
        status_enum = self.iface.enum("record", "status")
        if status_enum is not None and set(status_enum) != set(AUDIT_STATUSES):
            self.structure_gate.fail(
                "schema.statusEnum",
                f"schema status enum {status_enum!r} differs from the contract statuses "
                f"{list(AUDIT_STATUSES)!r}", "<schema>")
        kind_enum = self.iface.enum("record", "relationKind")
        if kind_enum is not None and set(kind_enum) != set(CERTIFIED_KINDS):
            self.structure_gate.fail(
                "schema.kindEnum",
                f"schema relation-kind enum {kind_enum!r} differs from the seven "
                "certified kinds", "<schema>")

        manifest_mode = self.iface.get(self.manifest, "manifest", "mode", None)
        if manifest_mode is not None and manifest_mode != self.mode:
            self.structure_gate.fail(
                "mode.mismatch",
                f"manifest declares mode {manifest_mode!r} but the run requested "
                f"{self.mode!r}", "<manifest>.mode")
        pair_count = self.iface.get(self.manifest, "manifest", "pairCount", None)
        if pair_count is not None and pair_count != EXPECTED_PAIR_COUNT:
            self.structure_gate.fail(
                "coverage.pairCount",
                f"manifest declares pairCount {pair_count!r}, expected "
                f"{EXPECTED_PAIR_COUNT}", "<manifest>.pairCount")

        if len(self.inventory) != EXPECTED_THEORY_COUNT:
            self.structure_gate.fail(
                "coverage.inventory",
                f"theory inventory has {len(self.inventory)} entries, expected "
                f"{EXPECTED_THEORY_COUNT}", "<manifest>.theoryInventory")
        elif len(set(self.inventory)) != EXPECTED_THEORY_COUNT:
            self.structure_gate.fail(
                "coverage.inventoryDuplicate",
                "theory inventory contains duplicate ids", "<manifest>.theoryInventory")
        else:
            self.structure_gate.pass_(
                "coverage.inventory", "17 distinct theory ids in the inventory")

    # ------------------------------------------------------------------ scopes
    def _check_scopes(self) -> None:
        if not self.scopes:
            self.reference_gate.fail("scope.empty", "no scopes registered", "scopes")
        for index, scope in enumerate(self.scopes):
            location = f"scopes[{index}]"
            ident = self.iface.get(scope, "scope", "id", None)
            kind = self.iface.get(scope, "scope", "kind", None)
            description = self.iface.get(scope, "scope", "description", None)
            if not _nonempty_string(description):
                self.semantics_gate.fail(
                    "scope.description", "scope has no description", location)
            if kind not in SCOPE_KINDS:
                self.semantics_gate.fail(
                    "scope.kind", f"scope {ident!r} has invalid kind {kind!r}", location)
            theories = self.iface.get(scope, "scope", "theories", None)
            if theories is not None:
                if not isinstance(theories, list) or not theories \
                        or not _string_list(theories):
                    self.semantics_gate.fail(
                        "scope.theories",
                        f"scope {ident!r} theories must be a non-empty string array",
                        location)
                else:
                    unknown = sorted(set(theories) - set(self.inventory))
                    if unknown:
                        self.semantics_gate.fail(
                            "scope.theoriesUnknown",
                            f"scope {ident!r} names theories outside the inventory: "
                            f"{unknown}", location)
            self._check_provenance(
                self.iface.get(scope, "scope", "provenance", _MISSING),
                f"scope {ident!r}", location)

    # -------------------------------------------------------------- statements
    def _check_statements(self) -> None:
        inventory = set(self.inventory)
        for index, statement in enumerate(self.statements):
            location = f"statements[{index}]"
            ident = self.iface.get(statement, "statement", "id", None)
            theory = self.iface.get(statement, "statement", "theory", None)
            artifact = self.iface.get(statement, "statement", "artifact", None)
            digest = self.iface.get(statement, "statement", "sha256", None)
            context = self.iface.get(statement, "statement", "context", None)
            if not _nonempty_string(theory):
                self.reference_gate.fail(
                    "statement.theory", f"statement {ident!r} has no theory", location)
            elif theory not in inventory:
                self.reference_gate.fail(
                    "statement.theoryUnknown",
                    f"statement {ident!r} names theory {theory!r} outside the inventory",
                    location)
            if not _nonempty_string(artifact):
                self.reference_gate.fail(
                    "statement.artifact", f"statement {ident!r} has no artifact", location)
            elif self._resolve_artifact_path(artifact) is None:
                self.reference_gate.fail(
                    "statement.artifactPath",
                    f"statement {ident!r} artifact {artifact!r} is not a repository-relative path",
                    location)
            if not isinstance(digest, str) or not _SHA256_RE.match(digest):
                self.reference_gate.fail(
                    "statement.hash",
                    f"statement {ident!r} has no valid sha256 artifact hash", location)
            if not _nonempty_string(context):
                self.reference_gate.fail(
                    "statement.context", f"statement {ident!r} has no context", location)
            self._check_provenance(
                self.iface.get(statement, "statement", "provenance", _MISSING),
                f"statement {ident!r}", location)
        if self.statements:
            self.reference_gate.pass_(
                "statement.count", f"{len(self.statements)} statement references checked")

    def _check_queries(self) -> None:
        for index, query in enumerate(self.queries):
            location = f"queries[{index}]"
            ident = self.iface.get(query, "query", "id", None)
            source = self.iface.get(query, "query", "source", None)
            target = self.iface.get(query, "query", "target", None)
            context = self.iface.get(query, "query", "context", None)
            for role, value in (("source", source), ("target", target)):
                if not _nonempty_string(value):
                    self.reference_gate.fail(
                        "query.endpoint", f"query {ident!r} has no {role}", location)
                elif value not in self.statement_map:
                    self.reference_gate.fail(
                        "ref.statement",
                        f"query {ident!r} {role} {value!r} does not resolve", location)
            if not _nonempty_string(context):
                self.reference_gate.fail(
                    "query.context", f"query {ident!r} has no shared context", location)
            self._check_provenance(
                self.iface.get(query, "query", "provenance", _MISSING),
                f"query {ident!r}", location)
        if self.queries:
            self.reference_gate.pass_(
                "query.count", f"{len(self.queries)} queries checked")

    # --------------------------------------------------------------- snapshots
    def _check_snapshots(self) -> None:
        if not self.snapshots:
            self.snapshot_gate.fail("snapshot.empty", "no snapshot registered", "snapshots")
            return
        for index, snapshot in enumerate(self.snapshots):
            location = f"snapshots[{index}]"
            ident = self.iface.get(snapshot, "snapshot", "id", None)
            tree = self.iface.get(snapshot, "snapshot", "treeSha", None)
            toolchain = self.iface.get(snapshot, "snapshot", "toolchain", None)
            schema_hash = self.iface.get(snapshot, "snapshot", "schemaSha256", None)
            artifacts = self.iface.get(snapshot, "snapshot", "artifacts", None)
            dirty = self.iface.get(snapshot, "snapshot", "dirty", False)
            if not isinstance(dirty, bool):
                self.snapshot_gate.fail(
                    "snapshot.dirty",
                    f"snapshot {ident!r} dirty flag must be boolean", location)
                dirty = False

            resolved_sha = ""
            if not isinstance(tree, str) or not _GIT_SHA_RE.match(tree):
                self.snapshot_gate.fail(
                    "snapshot.treeSha", f"snapshot {ident!r} has invalid treeSha {tree!r}", location)
            else:
                resolved_sha = self._git(
                    ["rev-parse", "--verify", "--quiet", f"{tree}^{{commit}}"], default="").strip()
                if not resolved_sha:
                    self.snapshot_gate.fail(
                        "snapshot.unknownCommit",
                        f"snapshot {ident!r} treeSha {tree!r} is not a commit in this repository "
                        "(stale snapshot)", location)
            if toolchain != self._toolchain:
                self.snapshot_gate.fail(
                    "snapshot.toolchain",
                    f"snapshot {ident!r} toolchain {toolchain!r} does not match "
                    f"lean-toolchain {self._toolchain!r} (stale snapshot)", location)
            if schema_hash != self._schema_hash:
                self.snapshot_gate.fail(
                    "snapshot.schemaHash",
                    f"snapshot {ident!r} schema hash does not match the checked-in schema "
                    "(stale snapshot)", location)
            mathlib_rev = self.iface.get(snapshot, "snapshot", "mathlibRev", None)
            if mathlib_rev is not None and self._mathlib_rev \
                    and mathlib_rev != self._mathlib_rev:
                self.snapshot_gate.fail(
                    "snapshot.mathlibRev",
                    f"snapshot {ident!r} mathlib revision {mathlib_rev!r} does not match "
                    f"lake-manifest.json {self._mathlib_rev!r} (stale snapshot)", location)
            if not isinstance(artifacts, dict) or not artifacts:
                self.snapshot_gate.fail(
                    "snapshot.artifacts", f"snapshot {ident!r} has no artifact hash map", location)
                continue
            for path, recorded in sorted(artifacts.items()):
                rel = self._resolve_artifact_path(path)
                if rel is None:
                    self.snapshot_gate.fail(
                        "snapshot.artifactPath",
                        f"snapshot {ident!r} artifact {path!r} is not repository-relative",
                        location)
                    continue
                if not isinstance(recorded, str) or not _SHA256_RE.match(recorded):
                    self.snapshot_gate.fail(
                        "snapshot.artifactHash",
                        f"snapshot {ident!r} has malformed hash for {path!r}", location)
                    continue
                if not resolved_sha:
                    continue
                if dirty:
                    content = self._working_file(rel)
                    where = "working tree"
                else:
                    content = self._git_object(resolved_sha, rel)
                    where = f"snapshot commit {resolved_sha[:12]}"
                if content is None:
                    self.snapshot_gate.fail(
                        "snapshot.artifactMissing",
                        f"snapshot {ident!r} pins {path!r} but the file is absent from "
                        f"the {where}", location)
                    continue
                if sha256_bytes(content) != recorded:
                    self.snapshot_gate.fail(
                        "snapshot.staleArtifact",
                        f"snapshot {ident!r} pins {path!r} with a hash that does not match "
                        f"the {where} (stale snapshot)", location)
        for statement in self.statements:
            statement_id = self.iface.get(statement, "statement", "id", "?")
            path = self.iface.get(statement, "statement", "artifact", None)
            digest = self.iface.get(statement, "statement", "sha256", None)
            if not _nonempty_string(path) or not isinstance(digest, str):
                continue
            rel = self._resolve_artifact_path(path)
            pinned = False
            for snapshot in self.snapshots:
                artifacts = self.iface.get(snapshot, "snapshot", "artifacts", {})
                if isinstance(artifacts, dict) and artifacts.get(rel) == digest:
                    pinned = True
                    break
            if not pinned:
                self.snapshot_gate.fail(
                    "snapshot.statementPin",
                    f"statement {statement_id!r} artifact {path!r} is not pinned with its "
                    "declared hash by any snapshot", f"statements[{statement_id}]")
        dirty_snapshots = []
        for snapshot in self.snapshots:
            if self.iface.get(snapshot, "snapshot", "dirty", False) is True:
                snapshot_id = self.iface.get(snapshot, "snapshot", "id", "?")
                dirty_snapshots.append(snapshot_id)
                self.snapshot_gate.pass_(
                    "snapshot.dirty",
                    f"snapshot {snapshot_id!r} is dirty; artifact hashes were matched "
                    "against the working tree, not the commit", "snapshots")
        if dirty_snapshots:
            self.report.metadata["snapshotDirty"] = True
            self.report.caveats.append({
                "code": "snapshotDirty",
                "message": "dirty snapshot(s) "
                           + ", ".join(repr(item) for item in dirty_snapshots)
                           + ": artifact hashes were matched against the working tree; a "
                             "full-mode PASS on a dirty tree needs independent review.",
            })
        if not self.snapshot_gate.failures():
            self.snapshot_gate.pass_(
                "snapshot.valid",
                f"{len(self.snapshots)} snapshot(s) match toolchain, schema and artifacts")

    # ------------------------------------------------------------ certificates
    def _check_certificates(self) -> None:
        for index, certificate in enumerate(self.certificates):
            location = f"certificates[{index}]"
            ident = self.iface.get(certificate, "certificate", "id", None)
            kind = self.iface.get(certificate, "certificate", "kind", None)
            module = self.iface.get(certificate, "certificate", "module", None)
            lean_name = self.iface.get(certificate, "certificate", "lean", None)
            kind_function = self.iface.get(certificate, "certificate", "kindFunction", None)
            constructor = self.iface.get(certificate, "certificate", "constructor", None)

            if kind == "adjudication":
                self.semantics_gate.fail(
                    "kind.adjudication",
                    f"certificate {ident!r} uses 'adjudication' as a primitive kind; it is a "
                    "collection of certified relations, not a constructor", location)
            elif kind not in CERTIFIED_KINDS:
                self.semantics_gate.fail(
                    "kind.invalid", f"certificate {ident!r} has invalid kind {kind!r}", location)
            for field, value in (("module", module), ("lean", lean_name),
                                 ("kindFunction", kind_function),
                                 ("constructor", constructor)):
                if not _nonempty_string(value):
                    self.semantics_gate.fail(
                        "certificate.field",
                        f"certificate {ident!r} has no {field}", location)
            if kind in CERTIFIED_KINDS and _nonempty_string(constructor):
                constructor_leaf = constructor.rsplit(".", 1)[-1]
                if constructor_leaf != kind:
                    self.semantics_gate.fail(
                        "certificate.kindConstructorMismatch",
                        f"certificate {ident!r} declares kind {kind!r} but its expected "
                        f"constructor {constructor!r} names {constructor_leaf!r}", location)

            premises = self.iface.get(certificate, "certificate", "premises", [])
            premise_map = self._check_premises(premises, f"certificate {ident!r}",
                                               f"{location}.premises", scope="certificate")
            self.certificate_premises[ident] = premise_map if isinstance(ident, str) else {}

            axiom_footprint = self.iface.get(
                certificate, "certificate", "axiomFootprint", None)
            expected_axioms: frozenset[str] | None = None
            if axiom_footprint is not None:
                if not isinstance(axiom_footprint, list) \
                        or not _string_list(axiom_footprint):
                    self.semantics_gate.fail(
                        "certificate.axiomFootprint",
                        f"certificate {ident!r} axiomFootprint must be a string array",
                        location)
                else:
                    disallowed = sorted(set(axiom_footprint) - ALLOWED_AXIOMS)
                    if disallowed:
                        self.semantics_gate.fail(
                            "certificate.axiomFootprint",
                            f"certificate {ident!r} declares disallowed axioms "
                            f"{disallowed!r}", location)
                    expected_axioms = frozenset(axiom_footprint)

            complete_fields = (_nonempty_string(module) and _nonempty_string(lean_name)
                               and _nonempty_string(kind_function)
                               and _nonempty_string(constructor))
            if not complete_fields:
                self.lean_gate.skip(
                    "lean.certificateIncomplete",
                    f"certificate {ident!r} is missing module/lean/kindFunction/constructor; "
                    "no Lean check could be generated, which is not PASS", location)
            if complete_fields:
                self.lean_specs.append({
                    "shape": "certificate",
                    "check_id": f"certificates[{index}]",
                    "location": location,
                    "certificate": lean_name,
                    "kind_function": kind_function,
                    "expected_constructor": constructor,
                    "expected_axioms": expected_axioms,
                })
                # The certificate's canonical premise projection is checked
                # definitionally against the manifest's certificate premise IDs.
                # This closes the hole where a manifest could attribute premises
                # to a certificate that its Lean value does not carry, and it
                # feeds the parent-premise projection of any composition.
                namespace = kind_function.rsplit(".", 1)[0] if "." in kind_function else ""
                if namespace and complete_fields:
                    self._add_term_equality_spec(
                        f"{location}.premiseIds",
                        f"{location}.premises",
                        f"{namespace}.certificatePremiseIDs {lean_name}",
                        _lean_string_list(list(premise_map)),
                        fail_code="lean.certificatePremiseIDs",
                        pass_code="lean.certificatePremiseIDs",
                    )

            semantics = self.iface.get(certificate, "certificate", "semantics", {})
            if semantics is None:
                semantics = {}
            if not isinstance(semantics, dict):
                self.semantics_gate.fail(
                    "semantics.type", f"certificate {ident!r} semantics must be an object", location)
                semantics = {}
            self._check_certificate_semantics(ident, kind, semantics, location)
            source_path = self.iface.get(certificate, "certificate", "sourcePath", None)
            source_hash = self.iface.get(certificate, "certificate", "sourceSha256", None)
            if source_path is not None or source_hash is not None:
                self._check_certificate_source_pin(ident, location, source_path, source_hash)

        if self.certificates:
            self.semantics_gate.pass_(
                "certificate.count",
                f"{len(self.certificates)} certificate row(s) inspected")

    def _check_certificate_semantics(self, ident: Any, kind: Any, semantics: dict[str, Any],
                                     location: str) -> None:
        context = self.iface.get(semantics, "semantics", "context", None)
        if not _nonempty_string(context):
            self.semantics_gate.fail(
                "semantics.context",
                f"certificate {ident!r} requires a shared context Delta", location)
        translations = self.iface.get(semantics, "semantics", "translations", None)
        if not isinstance(translations, dict):
            self.semantics_gate.fail(
                "semantics.translations",
                f"certificate {ident!r} requires left/right endpoint translations", location)
        else:
            for side in ("left", "right"):
                value = translations.get(side)
                if not _nonempty_string(value):
                    self.semantics_gate.fail(
                        "semantics.translations",
                        f"certificate {ident!r} translation.{side} is missing", location)
        premise_predicate = self.iface.get(
            semantics, "semantics", "premisePredicate", None)
        if not _nonempty_string(premise_predicate):
            self.semantics_gate.fail(
                "semantics.premisePredicate",
                f"certificate {ident!r} requires a premise predicate Pi", location)

        def require(field: str, code: str) -> Any:
            value = self.iface.get(semantics, "semantics", field, None)
            if not _nonempty_string(value):
                self.semantics_gate.fail(
                    code, f"certificate {ident!r} ({kind}) requires semantics.{field}", location)
                return None
            return value

        if kind == "definitionalIdentity":
            witness = require("rflWitness", "semantics.rflWitness")
            require("translation", "semantics.translation")
            witness_axioms: frozenset[str] | None = None
            declared_witness_axioms = self.iface.get(
                semantics, "semantics", "rflWitnessAxiomFootprint", None)
            if declared_witness_axioms is not None:
                if not isinstance(declared_witness_axioms, list) \
                        or not _string_list(declared_witness_axioms):
                    self.semantics_gate.fail(
                        "semantics.rflWitnessAxiomFootprint",
                        f"certificate {ident!r} rflWitnessAxiomFootprint must be a "
                        "string array", location)
                else:
                    disallowed = sorted(set(declared_witness_axioms) - ALLOWED_AXIOMS)
                    if disallowed:
                        self.semantics_gate.fail(
                            "semantics.rflWitnessAxiomFootprint",
                            f"certificate {ident!r} declares disallowed rfl-witness "
                            f"axioms {disallowed!r}", location)
                    witness_axioms = frozenset(declared_witness_axioms)
            if witness:
                # Contract section 5: definitional identity is established by the
                # fresh rfl elaboration below, not by an empty axiom footprint.
                # The standard allowed-axiom whitelist applies to this witness
                # exactly as it does to every other certificate; when the schema
                # declares an exact footprint, it must match Lean's output.
                self._add_declaration_spec(
                    f"{location}.rflWitness", f"{location}.semantics.rflWitness",
                    witness,
                    existence_code="semantics.rflWitness",
                    expected_axioms=witness_axioms)
            rfl_check = self.iface.get(semantics, "semantics", "rflCheck", None)
            if not isinstance(rfl_check, dict):
                self.semantics_gate.fail(
                    "semantics.rflCheck",
                    f"certificate {ident!r} (definitionalIdentity) requires an rfl check "
                    "with lhs/rhs", location)
            else:
                lhs = rfl_check.get("lhs")
                rhs = rfl_check.get("rhs")
                if not _nonempty_string(lhs) or not _nonempty_string(rhs):
                    self.semantics_gate.fail(
                        "semantics.rflCheck",
                        f"certificate {ident!r} rfl check needs non-empty lhs and rhs",
                        location)
                else:
                    self.lean_specs.append({
                        "shape": "term_equality",
                        "check_id": f"{location}.rflCheck",
                        "location": f"{location}.semantics.rflCheck",
                        "lhs": lhs,
                        "rhs": rhs,
                    })
        elif kind == "observationalEquivalence":
            channels = self.iface.get(semantics, "semantics", "channels", None)
            if not isinstance(channels, list) or not channels or not _string_list(channels):
                self.semantics_gate.fail(
                    "semantics.channels",
                    f"certificate {ident!r} (observationalEquivalence) requires a non-empty "
                    "list of observation channels", location)
        elif kind == "distinguishability":
            form = self.iface.get(semantics, "semantics", "form", None)
            if form not in DISTINGUISHABILITY_FORMS:
                self.semantics_gate.fail(
                    "semantics.form",
                    f"certificate {ident!r} distinguishability form {form!r} must be one of "
                    f"{list(DISTINGUISHABILITY_FORMS)}", location)
            witness = require("witness", "semantics.witness")
            if witness:
                self._add_declaration_spec(
                    f"{location}.distWitness", f"{location}.semantics.witness", witness)
        elif kind == "refutation":
            counterexample = require("counterexample", "semantics.counterexample")
            require("target", "semantics.target")
            if counterexample:
                self._add_declaration_spec(
                    f"{location}.counterexample", f"{location}.semantics.counterexample",
                    counterexample)
        elif kind == "conditionalComposition":
            if not self.iface.get(semantics, "semantics", "translation", None):
                self.semantics_gate.fail(
                    "semantics.translation",
                    f"certificate {ident!r} (conditionalComposition) requires a declared "
                    "translation", location)

    # ---------------------------------------------------------------- premises
    def _check_premises(self, premises: Any, owner: str, location: str,
                        scope: str) -> dict[str, dict[str, Any]]:
        mapping: dict[str, dict[str, Any]] = {}
        if premises is None:
            return mapping
        if not isinstance(premises, list):
            self.semantics_gate.fail(
                "premise.type", f"{owner} premises must be an array", location)
            return mapping
        for index, premise in enumerate(premises):
            where = f"{location}[{index}]"
            if not isinstance(premise, dict):
                self.semantics_gate.fail(
                    "premise.type", f"{owner} premise {index} is not an object", where)
                continue
            ident = self.iface.get(premise, "premise", "id", None)
            if not _nonempty_string(ident):
                self.semantics_gate.fail(
                    "premise.id", f"{owner} premise {index} has no id", where)
                continue
            if ident in mapping:
                self.semantics_gate.fail(
                    "premise.duplicate", f"{owner} repeats premise id {ident!r}", where)
                continue
            statement = self.iface.get(premise, "premise", "statement", None)
            if not _nonempty_string(statement):
                self.semantics_gate.fail(
                    "premise.statement", f"{owner} premise {ident!r} has no statement text", where)
            explicit = self.iface.get(premise, "premise", "explicit", False)
            signature_name = self.iface.get(premise, "premise", "signatureName", None)
            signature_decl = self.iface.get(premise, "premise", "signatureDeclaration", None)
            if explicit is True:
                if not _nonempty_string(signature_name) or not _nonempty_string(signature_decl):
                    self.semantics_gate.fail(
                        "premise.explicitMissing",
                        f"{owner} premise {ident!r} claims explicit but has no "
                        "signatureName/signatureDeclaration", where)
                else:
                    self._add_declaration_spec(
                        f"{where}.signature", where, signature_decl,
                        binder=signature_name,
                        existence_code="lean.premiseSignature")
            elif explicit not in (False, None):
                self.semantics_gate.fail(
                    "premise.explicitType", f"{owner} premise {ident!r} explicit must be boolean",
                    where)
            mapping[ident] = premise
        return mapping

    # ----------------------------------------------------------------- records
    def _check_records(self) -> None:
        if not self.records:
            self.semantics_gate.fail("record.empty", "manifest contains no audit records", "records")
            return
        groups: dict[tuple[Any, Any, Any], list[dict[str, Any]]] = {}
        pairs: set[frozenset[str]] = set()
        resolved_pairs: set[frozenset[str]] = set()
        status_counts = {status: 0 for status in AUDIT_STATUSES}
        kind_counts = {kind: 0 for kind in CERTIFIED_KINDS}
        unresolved_records: list[dict[str, Any]] = []

        for index, record in enumerate(self.records):
            location = f"records[{index}]"
            ident = self.iface.get(record, "record", "id", None)
            query_id = self.iface.get(record, "record", "queryId", None)
            version = self.iface.get(record, "record", "statementVersion", None)
            scope_id = self.iface.get(record, "record", "scope", None)
            status = self.iface.get(record, "record", "status", None)
            snapshot_id = self.iface.get(record, "record", "snapshot", None)

            for field, value in (("queryId", query_id), ("statementVersion", version),
                                 ("scope", scope_id), ("snapshot", snapshot_id)):
                if not _nonempty_string(value):
                    self.structure_gate.fail(
                        "record.field", f"record {ident!r} has no {field}", location)

            if status not in AUDIT_STATUSES:
                self.semantics_gate.fail(
                    "status.invalid", f"record {ident!r} has invalid status {status!r}", location)
            else:
                status_counts[status] += 1
                if status == "unresolved":
                    unresolved_records.append({
                        "record": ident,
                        "queryId": query_id,
                        "statementVersion": version,
                        "scope": scope_id,
                    })

            groups.setdefault((query_id, version, scope_id), []).append(record)

            scope = self.scope_map.get(scope_id) if isinstance(scope_id, str) else None
            if scope is None:
                self.reference_gate.fail(
                    "ref.scope", f"record {ident!r} scope {scope_id!r} does not resolve", location)
            query = self.query_map.get(query_id) if isinstance(query_id, str) else None
            if query is None:
                self.reference_gate.fail(
                    "ref.query", f"record {ident!r} query {query_id!r} does not resolve", location)
            snapshot = self.snapshot_map.get(snapshot_id) if isinstance(snapshot_id, str) else None
            if snapshot is None:
                self.reference_gate.fail(
                    "ref.snapshot",
                    f"record {ident!r} snapshot {snapshot_id!r} does not resolve", location)

            self._check_provenance(
                self.iface.get(record, "record", "provenance", _MISSING),
                f"record {ident!r}", location,
                require_rationale=(status != "certified"))

            premise_map = self._check_premises(
                self.iface.get(record, "record", "premises", []),
                f"record {ident!r}", f"{location}.premises", scope="record")
            if isinstance(ident, str):
                self.record_premises[ident] = premise_map

            if scope is not None and query is not None:
                self._check_scope_jurisdiction(record, ident, location, scope, query)

            if query is not None:
                self._record_pair(record, ident, query, location, pairs, resolved_pairs, status)

            if status == "certified":
                kind = self._check_certified_record(record, ident, location, scope,
                                                    query, snapshot, premise_map)
                if kind in kind_counts:
                    kind_counts[kind] += 1
            elif status in NON_CERTIFICATE_STATUSES:
                self._check_non_certified_record(record, ident, location, status, scope, snapshot)
            self._check_dependencies(record, ident, location, status)

        for key, group in groups.items():
            self._check_conflicts(key, group)
        if not self.semantics_gate.failures():
            self.semantics_gate.pass_(
                "record.valid",
                f"{len(self.records)} audit record(s) passed status, conflict, premise, "
                "badge and composition checks")
        self._check_pair_coverage(pairs, resolved_pairs, status_counts, kind_counts,
                                  unresolved_records)

    def _query_theories(self, query: dict[str, Any]) -> tuple[str | None, str | None]:
        source_id = self.iface.get(query, "query", "source", None)
        target_id = self.iface.get(query, "query", "target", None)
        source = self.statement_map.get(source_id) if isinstance(source_id, str) else None
        target = self.statement_map.get(target_id) if isinstance(target_id, str) else None
        if source is None or target is None:
            return None, None
        return (self.iface.get(source, "statement", "theory", None),
                self.iface.get(target, "statement", "theory", None))

    def _check_scope_jurisdiction(self, record: dict[str, Any], ident: Any,
                                  location: str, scope: dict[str, Any],
                                  query: dict[str, Any]) -> None:
        theories = self.iface.get(scope, "scope", "theories", None)
        if theories is None:
            return
        if not isinstance(theories, list):
            return
        source_theory, target_theory = self._query_theories(query)
        if not _nonempty_string(source_theory) or not _nonempty_string(target_theory):
            return
        needed = {source_theory, target_theory}
        missing = sorted(needed - set(theories))
        if missing:
            self.semantics_gate.fail(
                "scope.jurisdiction",
                f"record {ident!r} endpoints {sorted(needed)!r} are not covered by scope "
                f"{self.iface.get(scope, 'scope', 'id', '?')!r} theories {theories!r} "
                f"(missing {missing!r})", location)

    def _record_pair(self, record: dict[str, Any], ident: Any, query: dict[str, Any],
                     location: str, pairs: set[frozenset[str]],
                     resolved_pairs: set[frozenset[str]], status: Any) -> None:
        source_id = self.iface.get(query, "query", "source", None)
        target_id = self.iface.get(query, "query", "target", None)
        source = self.statement_map.get(source_id) if isinstance(source_id, str) else None
        target = self.statement_map.get(target_id) if isinstance(target_id, str) else None
        if source is None or target is None:
            return
        source_theory = self.iface.get(source, "statement", "theory", None)
        target_theory = self.iface.get(target, "statement", "theory", None)
        if not _nonempty_string(source_theory) or not _nonempty_string(target_theory):
            return
        if source_theory == target_theory:
            # Intra-theory records are legal in the schema (a scope may name one theory);
            # they simply do not contribute to the 136 unordered cross-theory pairs.
            return
        pair = frozenset((source_theory, target_theory))
        pairs.add(pair)
        if status == "certified":
            resolved_pairs.add(pair)
        self._check_record_artifact_hashes(ident, location, query, record)

    def _check_record_artifact_hashes(self, ident: Any, location: str, query: dict[str, Any],
                                      record: dict[str, Any]) -> None:
        snapshot_id = self.iface.get(record, "record", "snapshot", None)
        snapshot = self.snapshot_map.get(snapshot_id) if isinstance(snapshot_id, str) else None
        if snapshot is None:
            return
        tree = self.iface.get(snapshot, "snapshot", "treeSha", None)
        artifacts = self.iface.get(snapshot, "snapshot", "artifacts", {})
        dirty = self.iface.get(snapshot, "snapshot", "dirty", False) is True
        resolved = self._git(["rev-parse", "--verify", "--quiet", f"{tree}^{{commit}}"],
                             default="").strip() if isinstance(tree, str) else ""
        for role in ("source", "target"):
            statement_id = self.iface.get(query, "query", role, None)
            statement = self.statement_map.get(statement_id) if isinstance(statement_id, str) else None
            if statement is None:
                continue
            path = self.iface.get(statement, "statement", "artifact", None)
            digest = self.iface.get(statement, "statement", "sha256", None)
            if not isinstance(path, str) or not isinstance(artifacts, dict):
                continue
            rel = self._resolve_artifact_path(path)
            cache_key = (str(snapshot_id), str(statement_id), str(rel))
            if cache_key in self._artifact_hash_checked:
                continue
            self._artifact_hash_checked.add(cache_key)
            recorded = artifacts.get(rel) if rel else None
            if recorded is None:
                self.snapshot_gate.fail(
                    "snapshot.artifactMissing",
                    f"record {ident!r} statement {statement_id!r} artifact {path!r} is not "
                    "pinned by the record snapshot", location)
                continue
            if digest != recorded:
                self.snapshot_gate.fail(
                    "snapshot.hashMismatch",
                    f"statement {statement_id!r} declares hash {digest!r} but snapshot "
                    f"{snapshot_id!r} pins {recorded!r} (stale snapshot)", location)
                continue
            if dirty:
                content = self._working_file(rel)
                if content is not None and sha256_bytes(content) != digest:
                    self.snapshot_gate.fail(
                        "snapshot.staleArtifact",
                        f"statement {statement_id!r} hash does not match artifact content in "
                        f"the dirty snapshot {snapshot_id!r} (stale snapshot)", location)
            elif resolved:
                content = self._git_object(resolved, rel)
                if content is not None and sha256_bytes(content) != digest:
                    self.snapshot_gate.fail(
                        "snapshot.staleArtifact",
                        f"statement {statement_id!r} hash does not match artifact content at "
                        f"snapshot {snapshot_id!r} (stale snapshot)", location)

    def _check_conflicts(self, key: tuple[Any, Any, Any],
                         group: list[dict[str, Any]]) -> None:
        if len(group) < 2:
            return
        statuses = {self.iface.get(item, "record", "status", None) for item in group}
        ids = [self.iface.get(item, "record", "id", "?") for item in group]
        if len(statuses) > 1:
            self.semantics_gate.fail(
                "conflict.statuses",
                f"records {ids!r} share (queryId, statementVersion, scope)={key!r} but "
                f"declare different statuses {sorted(map(str, statuses))!r}",
                f"records[{key!r}]")
        # Contract sections 7 and 8: different certified relation kinds are not
        # inherently contradictory.  A pair may carry several certified
        # relations, especially when their observational contexts differ, and a
        # certified relation may coexist with an unresolved query about another
        # statement version or scope.  Only the conflict key above groups
        # records; there is no kind-level or pair-level exclusivity.

    # ------------------------------------------------------------ status kinds
    def _check_certified_record(self, record: dict[str, Any], ident: Any, location: str,
                                scope: dict[str, Any] | None, query: dict[str, Any] | None,
                                snapshot: dict[str, Any] | None,
                                premise_map: dict[str, dict[str, Any]]) -> Any:
        kind = self.iface.get(record, "record", "relationKind", None)
        certificate_id = self.iface.get(record, "record", "certificate", None)
        if kind == "adjudication":
            self.semantics_gate.fail(
                "kind.adjudication",
                f"record {ident!r} labels 'adjudication' as a primitive relation kind", location)
        elif kind not in CERTIFIED_KINDS:
            self.semantics_gate.fail(
                "kind.invalid", f"record {ident!r} has invalid relation kind {kind!r}", location)
        certificate = (self.certificate_map.get(certificate_id)
                       if isinstance(certificate_id, str) else None)
        if certificate is None:
            self.reference_gate.fail(
                "ref.certificate",
                f"certified record {ident!r} certificate {certificate_id!r} does not resolve",
                location)
        else:
            certificate_kind = self.iface.get(certificate, "certificate", "kind", None)
            if certificate_kind != kind:
                self.semantics_gate.fail(
                    "status.certificateMismatch",
                    f"record {ident!r} declares {kind!r} but certificate "
                    f"{certificate_id!r} has kind {certificate_kind!r}", location)
        for field in ("premises", "badges"):
            if not self.iface.has(record, "record", field):
                self.semantics_gate.fail(
                    "record.fieldMissing",
                    f"certified record {ident!r} must declare {field!r} (an empty value is "
                    "allowed when nothing is claimed)", location)
        for field in ("candidate", "dependencies"):
            if self.iface.has(record, "record", field):
                self.semantics_gate.fail(
                    "status.fieldUnexpected",
                    f"certified record {ident!r} must not carry {field!r}", location)
        if scope is not None:
            if self.iface.get(scope, "scope", "kind", None) == "outOfScope":
                self.semantics_gate.fail(
                    "scope.outOfScopeMismatch",
                    f"record {ident!r} is certified but its scope is declared outOfScope",
                    location)
        rational = self.iface.get(record, "record", "rationale", None)
        if rational is not None and not _nonempty_string(rational):
            self.semantics_gate.fail(
                "status.rationale", f"record {ident!r} rationale is empty", location)
        if kind == "conditionalComposition":
            self._check_composition(record, ident, certificate, location, premise_map)
        else:
            composition = self.iface.get(record, "record", "composition", None)
            if composition not in (None, {}, []):
                self.semantics_gate.fail(
                    "composition.unexpected",
                    f"record {ident!r} carries composition evidence for kind {kind!r}", location)
            self._check_premise_closure(record, ident, certificate, location, premise_map)
        self._check_badges(record, ident, location, premise_map)
        return kind

    def _check_non_certified_record(self, record: dict[str, Any], ident: Any, location: str,
                                    status: Any, scope: dict[str, Any] | None,
                                    snapshot: dict[str, Any] | None) -> None:
        kind = self.iface.get(record, "record", "relationKind", None)
        certificate_id = self.iface.get(record, "record", "certificate", None)
        if kind not in (None, ""):
            self.semantics_gate.fail(
                "status.kindUnexpected",
                f"record {ident!r} has status {status!r} but declares relation kind {kind!r}",
                location)
        if certificate_id not in (None, ""):
            self.semantics_gate.fail(
                "status.certificateUnexpected",
                f"record {ident!r} has status {status!r} but references a certificate", location)
        for field in ("premises", "badges", "composition"):
            if self.iface.has(record, "record", field):
                self.semantics_gate.fail(
                    "status.fieldUnexpected",
                    f"record {ident!r} has status {status!r} but carries {field!r}",
                    location)
        if status != "unresolved" and self.iface.has(record, "record", "candidate"):
            self.semantics_gate.fail(
                "status.candidateUnexpected",
                f"record {ident!r} has status {status!r} but carries a candidate", location)
        if status != "notEstablished" and self.iface.has(record, "record", "dependencies"):
            self.semantics_gate.fail(
                "status.dependenciesUnexpected",
                f"record {ident!r} has status {status!r} but carries dependencies", location)
        rational = self.iface.get(record, "record", "rationale", None)
        if not _nonempty_string(rational):
            self.semantics_gate.fail(
                "status.rationale",
                f"record {ident!r} status {status!r} requires a human rationale", location)
        if status == "unresolved":
            candidate = self.iface.get(record, "record", "candidate", None)
            if candidate not in CERTIFIED_KINDS:
                self.semantics_gate.fail(
                    "status.candidate",
                    f"unresolved record {ident!r} must name a candidate relation kind from the "
                    "seven certified kinds", location)
            if scope is not None and self.iface.get(scope, "scope", "kind", None) == "outOfScope":
                self.semantics_gate.fail(
                    "scope.outOfScopeMismatch",
                    f"unresolved record {ident!r} cannot use an outOfScope scope", location)
        elif status == "notEstablished":
            dependencies = self.iface.get(record, "record", "dependencies", None)
            if not isinstance(dependencies, list) or not dependencies:
                self.semantics_gate.fail(
                    "status.dependencies",
                    f"notEstablished record {ident!r} requires machine-recomputable dependency "
                    "evidence", location)
            if scope is not None and self.iface.get(scope, "scope", "kind", None) == "outOfScope":
                self.semantics_gate.fail(
                    "scope.outOfScopeMismatch",
                    f"notEstablished record {ident!r} cannot use an outOfScope scope", location)
        elif status == "outOfScope":
            if scope is None or self.iface.get(scope, "scope", "kind", None) != "outOfScope":
                self.semantics_gate.fail(
                    "scope.outOfScopeMismatch",
                    f"outOfScope record {ident!r} must reference a scope whose kind is "
                    "'outOfScope'", location)

    # ------------------------------------------------------------- composition
    def _check_composition(self, record: dict[str, Any], ident: Any,
                           certificate: dict[str, Any] | None, location: str,
                           premise_map: dict[str, dict[str, Any]]) -> None:
        """Validate composition evidence against the canonical Lean projections.

        The Lean ``ConditionalComposition`` constructor is proof-relevant and
        authoritative: it carries the typed parents, middle alignment, premise
        propagation, bridges and discharges, and computes the child comparison
        and conclusion.  The manifest therefore does not reconstruct a second
        combinator application.  It names the two parent certificates and the
        mediator; the validator resolves the parents to their Lean certificate
        names and generates the definitional checks for
        ``certificateParentIDs``, ``certificateParentKinds``,
        ``certificateParentPremiseIDs``, ``certificateBridgeIDs``,
        ``certificateDischargeIDs``, ``certificateMediating?`` and
        ``certificateCompositionForm?``.
        """
        composition = self.iface.get(record, "record", "composition", None)
        if not isinstance(composition, dict):
            self.semantics_gate.fail(
                "composition.missing",
                f"conditionalComposition record {ident!r} has no composition evidence", location)
            return
        parents = self.iface.get(composition, "composition", "parents", None)
        mediators = self.iface.get(composition, "composition", "mediators", None)
        translations = self.iface.get(composition, "composition", "translations", None)
        bridges = self.iface.get(composition, "composition", "bridges", None)
        discharges = self.iface.get(composition, "composition", "discharges", [])

        parent_ids: list[str] = []
        parent_rows: list[dict[str, Any]] = []
        parent_premises: set[str] = set()
        parent_premise_map: dict[str, dict[str, Any]] = {}
        if not isinstance(parents, list) or len(parents) != 2 or not _string_list(parents):
            self.semantics_gate.fail(
                "composition.parents",
                f"conditionalComposition record {ident!r} must name exactly two parent "
                "certificates in left-to-right order (the Lean ConditionalComposition "
                "constructor is binary)", location)
        else:
            for parent_id in parents:
                parent = self.certificate_map.get(parent_id)
                if parent is None:
                    self.reference_gate.fail(
                        "ref.parent",
                        f"record {ident!r} parent certificate {parent_id!r} does not resolve",
                        location)
                    parent_rows = []
                    continue
                parent_ids.append(parent_id)
                parent_rows.append(parent)
                parent_kind = self.iface.get(parent, "certificate", "kind", None)
                if parent_kind not in CERTIFIED_KINDS:
                    self.semantics_gate.fail(
                        "composition.parentKind",
                        f"record {ident!r} parent {parent_id!r} is not a certified kind",
                        location)
                inherited = self.certificate_premises.get(parent_id, {})
                parent_premises.update(inherited)
                for premise_id, premise in inherited.items():
                    if premise_id in parent_premise_map:
                        existing = self.iface.get(
                            parent_premise_map[premise_id], "premise", "statement", None)
                        incoming = self.iface.get(premise, "premise", "statement", None)
                        if _nonempty_string(existing) and _nonempty_string(incoming) \
                                and existing != incoming:
                            self.semantics_gate.fail(
                                "composition.parentPremiseMismatch",
                                f"record {ident!r} parents disagree about premise "
                                f"{premise_id!r}", location)
                    else:
                        parent_premise_map[premise_id] = premise

        mediator_row: dict[str, Any] | None = None
        if not isinstance(mediators, list) or len(mediators) != 1 \
                or not _string_list(mediators):
            self.semantics_gate.fail(
                "composition.mediators",
                f"conditionalComposition record {ident!r} must name exactly one mediating "
                "endpoint (the binary composition's middle proposition)", location)
        else:
            mediator = mediators[0]
            mediator_row = self.statement_map.get(mediator)
            if mediator_row is None:
                self.reference_gate.fail(
                    "ref.mediator",
                    f"record {ident!r} mediator {mediator!r} does not resolve", location)
            elif not _nonempty_string(
                    self.iface.get(mediator_row, "statement", "declaration", None)):
                self.semantics_gate.fail(
                    "composition.mediatorDeclaration",
                    f"record {ident!r} mediator {mediator!r} has no Lean declaration, so "
                    "certificateMediating? cannot be pinned", location)

        if not isinstance(translations, list) or not translations:
            self.semantics_gate.fail(
                "composition.translations",
                f"conditionalComposition record {ident!r} must name endpoint translations",
                location)
        else:
            for index, translation in enumerate(translations):
                if not isinstance(translation, dict):
                    self.semantics_gate.fail(
                        "composition.translation",
                        f"record {ident!r} translation {index} is not an object", location)
                    continue
                for role in ("from", "to"):
                    endpoint = translation.get(role)
                    if not _nonempty_string(endpoint) or endpoint not in self.statement_map:
                        self.reference_gate.fail(
                            "ref.translation",
                            f"record {ident!r} translation {index} {role} endpoint "
                            f"{endpoint!r} does not resolve", location)
                if not _nonempty_string(translation.get("description")):
                    self.semantics_gate.fail(
                        "composition.translation",
                        f"record {ident!r} translation {index} has no description", location)

        # Contract section 4: bridges may be empty when the parent contexts
        # already align.  A declared bridge, however, is not evidence by
        # declaration existence alone: typed expected-evidence tied to the
        # record and premise IDs is not implemented yet, so every declared
        # bridge is rejected explicitly (contract section 6 policy applied to
        # bridge evidence).
        bridge_ids: list[str] = []
        if bridges is None:
            bridges = []
        if not isinstance(bridges, list):
            self.semantics_gate.fail(
                "composition.bridges",
                f"conditionalComposition record {ident!r} bridges must be an array "
                "(an omitted or empty array is allowed)", location)
            bridges = []
        for index, bridge in enumerate(bridges):
            where = f"{location}.composition.bridges[{index}]"
            if not isinstance(bridge, dict):
                self.semantics_gate.fail(
                    "composition.bridge", f"bridge {index} is not an object", where)
                continue
            premise_id = self.iface.get(bridge, "bridge", "premiseId", None)
            if not _nonempty_string(premise_id):
                self.semantics_gate.fail(
                    "composition.bridge", f"bridge {index} has no premiseId", where)
            else:
                bridge_ids.append(premise_id)
            statement = self.iface.get(bridge, "bridge", "statement", None)
            if not _nonempty_string(statement):
                self.semantics_gate.fail(
                    "composition.bridge",
                    f"bridge {premise_id!r} has no statement", where)
            witness = self.iface.get(bridge, "bridge", "witness", None)
            if not _nonempty_string(witness):
                self.semantics_gate.fail(
                    "composition.bridgeWitness",
                    f"bridge {premise_id!r} has no Lean witness", where)
            self.semantics_gate.fail(
                "composition.bridgeUnsupported",
                f"record {ident!r} declares bridge premise {premise_id!r}, but typed "
                "bridge evidence tied to the record and premise IDs is not implemented; "
                "a declaration name is not accepted as bridge evidence", where)

        # Contract section 4: a premise may be omitted only with a typed
        # discharge certificate.  No typed discharge check exists yet, so every
        # declared discharge is rejected explicitly.
        discharge_ids: list[str] = []
        if discharges is None:
            discharges = []
        if not isinstance(discharges, list):
            self.semantics_gate.fail(
                "composition.discharges", "discharges must be an array", location)
            discharges = []
        for index, discharge in enumerate(discharges):
            where = f"{location}.composition.discharges[{index}]"
            if not isinstance(discharge, dict):
                self.semantics_gate.fail(
                    "composition.discharge", f"discharge {index} is not an object", where)
                continue
            premise_id = self.iface.get(discharge, "discharge", "premiseId", None)
            witness = self.iface.get(discharge, "discharge", "witness", None)
            if not _nonempty_string(premise_id):
                self.semantics_gate.fail(
                    "composition.discharge", f"discharge {index} has no premiseId", where)
            else:
                discharge_ids.append(premise_id)
            if not _nonempty_string(witness):
                self.semantics_gate.fail(
                    "composition.dischargeWitness",
                    f"discharge {premise_id!r} has no Lean witness", where)
            self.semantics_gate.fail(
                "composition.dischargeUnsupported",
                f"record {ident!r} declares discharge of premise {premise_id!r}, but "
                "typed discharge evidence tied to the record and premise IDs is not "
                "implemented; a declaration name is not accepted as discharge evidence",
                where)

        cert_id = self.iface.get(certificate, "certificate", "id", "") if certificate else ""
        cert_premises = set(self.certificate_premises.get(cert_id, {}))
        record_premises = set(premise_map)
        required = cert_premises | parent_premises
        discharge_set = set(discharge_ids)
        missing = sorted(required - record_premises - discharge_set)
        for premise_id in missing:
            self.semantics_gate.fail(
                "premise.closure",
                f"conditionalComposition record {ident!r} omits parent/own premise "
                f"{premise_id!r} without a discharge certificate", location)
        record_premise_map = {premise_id: premise_map[premise_id]
                              for premise_id in record_premises}
        for premise_id in sorted(record_premises & required):
            inherited = parent_premise_map.get(premise_id)
            if inherited is None:
                continue
            child_statement = self.iface.get(
                record_premise_map.get(premise_id, {}), "premise", "statement", None)
            parent_statement = self.iface.get(
                inherited, "premise", "statement", None)
            if _nonempty_string(child_statement) and _nonempty_string(parent_statement) \
                    and child_statement != parent_statement:
                self.semantics_gate.fail(
                    "premise.inheritedMismatch",
                    f"record {ident!r} premise {premise_id!r} does not match the statement "
                    "propagated by its parent certificate", location)
        bridge_set = set(bridge_ids)
        unknown = sorted(record_premises - required - bridge_set)
        for premise_id in unknown:
            role = self.iface.get(
                record_premise_map.get(premise_id, {}), "premise", "role", None)
            if role == "local":
                continue
            self.semantics_gate.fail(
                "premise.unknown",
                f"record {ident!r} declares premise {premise_id!r} that is neither carried by "
                "a parent certificate, declared as a bridge, nor marked role=local", location)
        for premise_id in sorted(discharge_set & record_premises):
            self.semantics_gate.fail(
                "composition.dischargePresent",
                f"record {ident!r} both declares and discharges premise {premise_id!r}",
                location)
        for premise_id in sorted(bridge_set - record_premises):
            self.semantics_gate.fail(
                "bridge.premiseMissing",
                f"bridge premise {premise_id!r} of record {ident!r} is not declared on the "
                "record", location)
        for premise_id in sorted(discharge_set - required):
            self.semantics_gate.fail(
                "discharge.unknown",
                f"record {ident!r} discharges premise {premise_id!r} that is not required",
                location)

        # The composed form is computed from the two typed parents: only two
        # equivalences compose to an equivalence.  The certificate type is
        # authoritative; a metadata conclusionKind must agree with it.
        expected_form = "implication"
        if len(parent_rows) == 2 and all(
                self.iface.get(parent, "certificate", "kind", None) == "equivalence"
                for parent in parent_rows):
            expected_form = "equivalence"
        declared_form = self.iface.get(
            composition, "composition", "conclusionKind", None)
        if declared_form is not None and declared_form != expected_form:
            self.semantics_gate.fail(
                "composition.conclusionKind",
                f"record {ident!r} declares composition conclusionKind {declared_form!r} but "
                f"the parent kinds compute {expected_form!r}", location)
        if certificate is not None:
            cert_semantics = self.iface.get(
                certificate, "certificate", "semantics", {})
            cert_form = self.iface.get(
                cert_semantics, "semantics", "conclusionKind", None) \
                if isinstance(cert_semantics, dict) else None
            if cert_form is not None and cert_form != expected_form:
                self.semantics_gate.fail(
                    "semantics.conclusionKind",
                    f"certificate {ident!r} semantics conclusionKind {cert_form!r} does not "
                    f"match the form computed from its parent kinds {expected_form!r}",
                    location)

        self._add_composition_lean_checks(
            ident, location, certificate, parent_ids, parent_rows, mediator_row,
            bridge_ids, discharge_ids, expected_form)

    def _add_composition_lean_checks(self, ident: Any, location: str,
                                     certificate: dict[str, Any] | None,
                                     parent_ids: list[str],
                                     parent_rows: list[dict[str, Any]],
                                     mediator_row: dict[str, Any] | None,
                                     bridge_ids: list[str],
                                     discharge_ids: list[str],
                                     expected_form: str) -> None:
        """Generate the canonical projection checks for one composition.

        Every check is a generated ``example : lhs = rhs := rfl``.  The expected
        values are derived from the manifest (parent certificate Lean names,
        parent kinds, parent premise IDs, declared bridges/discharges, the
        mediator's Lean declaration and the form computed from the parent
        kinds); the left-hand sides are the computable projections of the child
        certificate.  A manifest cannot satisfy these by naming parents next to
        an independently proved child conclusion, because the child Lean value
        itself must expose exactly these projections.
        """
        if certificate is None:
            self.lean_gate.skip(
                "lean.compositionIncomplete",
                f"composition record {ident!r} has no resolved child certificate; no "
                "canonical projection check could be generated, which is not PASS",
                location)
            return
        if len(parent_rows) != 2 or len(parent_ids) != 2:
            self.lean_gate.skip(
                "lean.compositionIncomplete",
                f"composition record {ident!r} does not resolve exactly two parent "
                "certificates; no canonical projection check could be generated, which "
                "is not PASS", location)
            return
        if mediator_row is None:
            self.lean_gate.skip(
                "lean.compositionIncomplete",
                f"composition record {ident!r} does not resolve its mediating statement; "
                "no certificateMediating? check could be generated, which is not PASS",
                location)
            return
        child_lean = self.iface.get(certificate, "certificate", "lean", None)
        kind_function = self.iface.get(certificate, "certificate", "kindFunction", None)
        if not _nonempty_string(child_lean) or not _nonempty_string(kind_function):
            self.lean_gate.skip(
                "lean.compositionIncomplete",
                f"composition record {ident!r} child certificate has no lean/kindFunction; "
                "no canonical projection check could be generated, which is not PASS",
                location)
            return
        namespace = kind_function.rsplit(".", 1)[0] if "." in kind_function else ""
        if not namespace:
            self.lean_gate.skip(
                "lean.compositionIncomplete",
                f"composition record {ident!r} kindFunction {kind_function!r} has no "
                "namespace, so the CompositionForm type cannot be named; this is not PASS",
                location)
            return
        parent_leannames: list[str] = []
        parent_constructors: list[str] = []
        parent_premise_lists: list[list[str]] = []
        for parent_id, parent in zip(parent_ids, parent_rows):
            lean_name = self.iface.get(parent, "certificate", "lean", None)
            constructor = self.iface.get(parent, "certificate", "constructor", None)
            if not _nonempty_string(lean_name) or not _nonempty_string(constructor):
                self.lean_gate.skip(
                    "lean.compositionIncomplete",
                    f"composition record {ident!r} parent {parent_id!r} has no "
                    "lean/constructor; no canonical projection check could be generated, "
                    "which is not PASS", location)
                return
            parent_leannames.append(lean_name)
            parent_constructors.append(constructor)
            parent_premise_lists.append(
                list(self.certificate_premises.get(parent_id, {})))
        mediator_decl = self.iface.get(mediator_row, "statement", "declaration", None)
        if not _nonempty_string(mediator_decl):
            self.lean_gate.skip(
                "lean.compositionIncomplete",
                f"composition record {ident!r} mediator has no Lean declaration; no "
                "certificateMediating? check could be generated, which is not PASS",
                location)
            return

        parent_kinds_rhs = "[" + ", ".join(parent_constructors) + "]"
        checks = (
            ("parentIDs", f"{namespace}.certificateParentIDs {child_lean}",
             _lean_string_list(parent_leannames), "lean.compositionParentIDs"),
            ("parentKinds", f"{namespace}.certificateParentKinds {child_lean}",
             parent_kinds_rhs, "lean.compositionParentKinds"),
            ("parentPremiseIDs", f"{namespace}.certificateParentPremiseIDs {child_lean}",
             _lean_string_lists(parent_premise_lists), "lean.compositionParentPremiseIDs"),
            ("bridgeIDs", f"{namespace}.certificateBridgeIDs {child_lean}",
             _lean_string_list(bridge_ids), "lean.compositionBridgeIDs"),
            ("dischargeIDs", f"{namespace}.certificateDischargeIDs {child_lean}",
             _lean_string_list(discharge_ids), "lean.compositionDischargeIDs"),
            ("mediating",
             f"({namespace}.certificateMediating? {child_lean}).map "
             f"(fun s => s.statementId)",
             f"some {_lean_string(mediator_decl)}", "lean.compositionMediating"),
            ("form", f"{namespace}.certificateCompositionForm? {child_lean}",
             f"some {namespace}.CompositionForm.{expected_form}",
             "lean.compositionForm"),
        )
        for suffix, lhs, rhs, code in checks:
            self._add_term_equality_spec(
                f"{location}.composition.{suffix}",
                f"{location}.composition",
                lhs, rhs,
                fail_code=code,
                pass_code=code,
            )

    def _check_premise_closure(self, record: dict[str, Any], ident: Any,
                               certificate: dict[str, Any] | None, location: str,
                               premise_map: dict[str, dict[str, Any]]) -> None:
        record_premises = set(premise_map)
        cert_id = self.iface.get(certificate, "certificate", "id", "") if certificate else ""
        required = set(self.certificate_premises.get(cert_id, {}))
        missing = sorted(required - record_premises)
        for premise_id in missing:
            self.semantics_gate.fail(
                "premise.closure",
                f"record {ident!r} omits certificate premise {premise_id!r}", location)
        extra = sorted(record_premises - required)
        for premise_id in extra:
            self.semantics_gate.fail(
                "premise.unknown",
                f"record {ident!r} declares premise {premise_id!r} absent from its certificate",
                location)

    # ------------------------------------------------------------------ badges
    def _check_badges(self, record: dict[str, Any], ident: Any, location: str,
                      premise_map: dict[str, dict[str, Any]]) -> None:
        badges = self.iface.get(record, "record", "badges", None)
        if badges is None:
            # An omitted badge is the absence of a claim, not a negative result.
            return
        if not isinstance(badges, dict):
            self.semantics_gate.fail(
                "badge.type", f"record {ident!r} badges must be an object", location)
            return
        unknown = sorted(set(badges) - set(PREMISE_BADGES))
        for name in unknown:
            self.semantics_gate.fail(
                "badge.unknown", f"record {ident!r} declares unknown badge {name!r}", location)

        if "explicit" in badges:
            earned = self.iface.get(badges["explicit"], "badge", "earned", None) \
                if isinstance(badges["explicit"], dict) else None
            if earned is not None and earned is not True:
                self.semantics_gate.fail(
                    "badge.explicitSignature",
                    f"record {ident!r} explicit badge is not earned", location)
            claimed_ids = self.iface.get(
                badges["explicit"], "badge", "premiseIds", None) \
                if isinstance(badges["explicit"], dict) else None
            if not isinstance(claimed_ids, list) or not _string_list(claimed_ids):
                self.semantics_gate.fail(
                    "badge.explicitPremiseIds",
                    f"record {ident!r} explicit badge requires the checked premiseIds "
                    "list", location)
            else:
                missing = sorted(set(premise_map) - set(claimed_ids))
                extra = sorted(set(claimed_ids) - set(premise_map))
                if missing or extra:
                    self.semantics_gate.fail(
                        "badge.explicitPremiseIds",
                        f"record {ident!r} explicit badge premiseIds {claimed_ids!r} "
                        f"do not equal the record premise set {sorted(premise_map)!r} "
                        f"(missing {missing!r}, extra {extra!r})", location)
            if premise_map and not all(
                    self.iface.get(premise, "premise", "explicit", False) is True
                    for premise in premise_map.values()):
                self.semantics_gate.fail(
                    "badge.explicitSignature",
                    f"record {ident!r} claims the explicit badge but not every premise is "
                    "marked explicit", location)
            for premise_id, premise in premise_map.items():
                binder = self.iface.get(premise, "premise", "signatureName", None)
                declaration = self.iface.get(premise, "premise", "signatureDeclaration", None)
                if not _nonempty_string(binder) or not _nonempty_string(declaration):
                    self.semantics_gate.fail(
                        "badge.explicitSignature",
                        f"record {ident!r} premise {premise_id!r} has no checked Lean signature",
                        location)

        # Contract section 6: every badge witness needs a typed expected-evidence
        # check tied to the record and premise IDs.  Until those checks exist,
        # reject the claim; a declaration name (even an existing one with an
        # allowed axiom footprint) must not earn a badge.
        for name in UNTYPED_BADGES:
            if name not in badges:
                continue
            self.semantics_gate.fail(
                f"badge.{name}Unsupported",
                f"record {ident!r} claims badge {name!r}, but {UNTYPED_BADGES[name]}; "
                "declaration existence is not accepted as evidence", location)

    def _check_certificate_source_pin(self, ident: Any, location: str,
                                      source_path: Any, source_hash: Any) -> None:
        if not _nonempty_string(source_path):
            self.snapshot_gate.fail(
                "snapshot.certificateSource",
                f"certificate {ident!r} has a source hash but no sourcePath", location)
            return
        if not isinstance(source_hash, str) or not _SHA256_RE.match(source_hash):
            self.snapshot_gate.fail(
                "snapshot.certificateSource",
                f"certificate {ident!r} sourcePath {source_path!r} has no sha256", location)
            return
        rel = self._resolve_artifact_path(source_path)
        if rel is None:
            self.snapshot_gate.fail(
                "snapshot.certificateSource",
                f"certificate {ident!r} sourcePath {source_path!r} is not repository-relative",
                location)
            return
        pinned = False
        for snapshot in self.snapshots:
            artifacts = self.iface.get(snapshot, "snapshot", "artifacts", {})
            if isinstance(artifacts, dict) and artifacts.get(rel) == source_hash:
                pinned = True
                break
        if not pinned:
            self.snapshot_gate.fail(
                "snapshot.certificateSourceMissing",
                f"certificate {ident!r} source {source_path!r} is not pinned with hash "
                f"{source_hash!r} by any snapshot", location)

    # ------------------------------------------------------------- provenance
    def _check_provenance(self, provenance: Any, owner: str, location: str,
                          require_rationale: bool = False) -> None:
        if provenance is _MISSING or provenance is None:
            self.provenance_gate.fail(
                "provenance.missing", f"{owner} has no provenance record", location)
            return
        if not isinstance(provenance, dict):
            self.provenance_gate.fail(
                "provenance.type", f"{owner} provenance must be an object", location)
            return
        self.provenance_checked += 1
        kind = self.iface.get(provenance, "provenance", "kind", None)
        if kind not in ("source", "manual", "computed", "imported"):
            self.provenance_gate.fail(
                "provenance.kind", f"{owner} has invalid provenance kind {kind!r}", location)
        references = self.iface.get(provenance, "provenance", "references", None)
        if not isinstance(references, list) or not references:
            self.provenance_gate.fail(
                "provenance.references", f"{owner} has no source references", location)
        else:
            for index, reference in enumerate(references):
                if not isinstance(reference, dict):
                    self.provenance_gate.fail(
                        "provenance.reference", f"{owner} reference {index} is not an object",
                        location)
                    continue
                artifact = self.iface.get(reference, "reference", "artifact", None)
                if not _nonempty_string(artifact):
                    self.provenance_gate.fail(
                        "provenance.reference", f"{owner} reference {index} has no artifact",
                        location)
                elif _URL_RE.match(artifact):
                    continue
                elif not os.path.exists(os.path.join(self.repo_root, artifact)):
                    self.provenance_gate.fail(
                        "provenance.referenceMissing",
                        f"{owner} reference {artifact!r} does not exist in the repository",
                        location)
        rationale = self.iface.get(provenance, "provenance", "rationale", None)
        if (require_rationale or kind == "manual") and not _nonempty_string(rationale):
            self.provenance_gate.fail(
                "provenance.rationale",
                f"{owner} requires a human rationale for a manual/non-certified status",
                location)

    def _check_dependencies(self, record: dict[str, Any], ident: Any, location: str,
                            status: Any) -> None:
        dependencies = self.iface.get(record, "record", "dependencies", None)
        if dependencies in (None, []):
            return
        if not isinstance(dependencies, list):
            self.provenance_gate.fail(
                "dependency.type", f"record {ident!r} dependencies must be an array", location)
            return
        for index, dependency in enumerate(dependencies):
            where = f"{location}.dependencies[{index}]"
            if not isinstance(dependency, dict):
                self.provenance_gate.fail(
                    "dependency.type", f"dependency {index} is not an object", where)
                continue
            kind = self.iface.get(dependency, "dependency", "kind", None)
            reference = self.iface.get(dependency, "dependency", "reference", None)
            recompute = self.iface.get(dependency, "dependency", "recompute", None)
            if kind not in DEPENDENCY_KINDS:
                self.provenance_gate.fail(
                    "dependency.kind",
                    f"dependency {index} has invalid kind {kind!r}", where)
            if not _nonempty_string(recompute):
                self.provenance_gate.fail(
                    "dependency.recompute",
                    f"dependency {index} has no machine-recomputable command", where)
            if not _nonempty_string(reference):
                self.provenance_gate.fail(
                    "dependency.reference", f"dependency {index} has no reference", where)
                continue
            if kind == "leanProbe":
                self._add_declaration_spec(
                    f"{where}.probe", where, reference,
                    existence_code="dependency.leanProbe")
            elif kind in ("sourceScan", "census"):
                if not _URL_RE.match(reference) and not os.path.exists(
                        os.path.join(self.repo_root, reference)):
                    self.provenance_gate.fail(
                        "dependency.referenceMissing",
                        f"dependency reference {reference!r} does not exist", where)
            digest = self.iface.get(dependency, "dependency", "sha256", None)
            if digest is not None:
                if not isinstance(digest, str) or not _SHA256_RE.match(digest):
                    self.provenance_gate.fail(
                        "dependency.hash", f"dependency {index} has malformed sha256", where)
                elif kind in ("sourceScan", "census") and not _URL_RE.match(reference):
                    path = os.path.join(self.repo_root, reference)
                    if os.path.isfile(path) and sha256_file(path) != digest:
                        self.provenance_gate.fail(
                            "dependency.stale", f"dependency reference {reference!r} hash "
                            "does not match the working tree", where)

    # ---------------------------------------------------------------- coverage
    def _check_pair_coverage(self, pairs: set[frozenset[str]], resolved_pairs: set[frozenset[str]],
                             status_counts: dict[str, int], kind_counts: dict[str, int],
                             unresolved_records: list[dict[str, Any]]) -> None:
        universe = {frozenset(pair) for pair in itertools.combinations(self.inventory, 2)}
        missing = sorted(tuple(sorted(pair)) for pair in universe - pairs)
        self.report.coverage = {
            "mode": self.mode,
            "theoryCount": len(self.inventory),
            "expectedTheoryCount": EXPECTED_THEORY_COUNT,
            "pairUniverse": len(universe),
            "expectedPairUniverse": EXPECTED_PAIR_COUNT,
            "coveredPairs": len(pairs & universe),
            "missingPairs": [list(pair) for pair in missing],
            "registryCoverage": round(len(pairs & universe) / EXPECTED_PAIR_COUNT, 6)
            if EXPECTED_PAIR_COUNT else 0.0,
            "resolvedPairs": len(resolved_pairs & universe),
            "resolvedCoverage": round(len(resolved_pairs & universe) / EXPECTED_PAIR_COUNT, 6)
            if EXPECTED_PAIR_COUNT else 0.0,
            "resolvedCoverageComplete": (
                len(resolved_pairs & universe) == EXPECTED_PAIR_COUNT
                and status_counts.get("unresolved", 0) == 0
            ),
            "unresolvedRecords": status_counts.get("unresolved", 0),
        }
        self.report.counts = {
            "records": len(self.records),
            "byStatus": status_counts,
            "certifiedByKind": kind_counts,
            "certificates": len(self.certificates),
            "statements": len(self.statements),
            "queries": len(self.queries),
            "scopes": len(self.scopes),
            "snapshots": len(self.snapshots),
        }
        self.report.unresolved = unresolved_records

        if self.mode == "full":
            if len(universe) != EXPECTED_PAIR_COUNT:
                self.coverage_gate.fail(
                    "coverage.inventorySize",
                    f"pair universe is {len(universe)}, expected {EXPECTED_PAIR_COUNT} from 17 "
                    "distinct theory ids", "<manifest>.theoryInventory")
            for pair in missing:
                self.coverage_gate.fail(
                    "coverage.missingPair",
                    f"no audit record covers theory pair {pair[0]!r} / {pair[1]!r}",
                    "records")
            if not missing and len(universe) == EXPECTED_PAIR_COUNT:
                self.coverage_gate.pass_(
                    "coverage.registry",
                    f"registry coverage {len(pairs & universe)}/{EXPECTED_PAIR_COUNT} pairs "
                    "(136/136)")
        else:
            certified_kinds = {kind for kind, count in kind_counts.items() if count}
            for kind in CERTIFIED_KINDS:
                if kind not in certified_kinds:
                    self.coverage_gate.fail(
                        "coverage.pilotKind",
                        f"pilot manifest has no certified {kind!r} record", "records")
            if status_counts.get("unresolved", 0) == 0:
                self.coverage_gate.fail(
                    "coverage.pilotStatus",
                    "pilot manifest has no unresolved record", "records")
            if status_counts.get("notEstablished", 0) == 0:
                self.coverage_gate.fail(
                    "coverage.pilotStatus",
                    "pilot manifest has no notEstablished record", "records")
            if not self.coverage_gate.failures():
                self.coverage_gate.pass_(
                    "coverage.pilot",
                    "pilot covers all seven certified kinds and both principal "
                    "non-certificate statuses")

        if self.report.coverage["resolvedCoverageComplete"]:
            self.coverage_gate.pass_(
                "coverage.resolved",
                f"resolved coverage {EXPECTED_PAIR_COUNT}/{EXPECTED_PAIR_COUNT} with no "
                "unresolved records")
        elif self.report.coverage["resolvedPairs"]:
            self.coverage_gate.pass_(
                "coverage.resolvedCount",
                f"resolved coverage {self.report.coverage['resolvedPairs']}/"
                f"{EXPECTED_PAIR_COUNT} pairs; not claiming completeness")

    # -------------------------------------------------------------------- Lean
    def _add_term_equality_spec(self, check_id: str, location: str,
                                lhs: str, rhs: str,
                                fail_code: str, pass_code: str) -> None:
        if not _nonempty_string(lhs) or not _nonempty_string(rhs):
            return
        self.lean_specs.append({
            "shape": "term_equality",
            "check_id": check_id,
            "location": location,
            "lhs": lhs,
            "rhs": rhs,
            "fail_code": fail_code,
            "pass_code": pass_code,
        })

    def _add_declaration_spec(self, check_id: str, location: str, declaration: str,
                              binder: str | None = None,
                              existence_code: str = "lean.evidenceExistence",
                              axioms_code: str = "lean.axioms",
                              expected_axioms: frozenset[str] | None = None) -> None:
        if not _nonempty_string(declaration):
            return
        self.lean_specs.append({
            "shape": "declaration",
            "check_id": check_id,
            "location": location,
            "declaration": declaration,
            "binder": binder,
            "existence_code": existence_code,
            "axioms_code": axioms_code,
            "expected_axioms": expected_axioms,
        })

    def _check_lean(self) -> None:
        if not self.lean_specs:
            if self.certificates:
                self.lean_gate.skip(
                    "lean.noChecks",
                    "certificates are present but no Lean check could be generated; "
                    "this is not PASS", "<lean>")
            return
        if self.no_lean:
            self.lean_gate.skip(
                "lean.notRequested",
                f"{len(self.lean_specs)} Lean check(s) were not run because --no-lean was "
                "given; skipped Lean checks are not PASS", "<lean>")
            return
        modules = []
        for certificate in self.certificates:
            module = self.iface.get(certificate, "certificate", "module", None)
            if _nonempty_string(module):
                modules.append(module)
        outcome = self.harness.run(self.lean_specs, imports=modules)
        for finding in outcome.findings:
            self.lean_gate.add(finding.status, finding.code, finding.message, finding.location)
        if outcome.skipped_reason:
            self.lean_gate.skip(
                "lean.skipped", f"Lean gate skipped: {outcome.skipped_reason}", "<lean>")
        lean_metadata = {
            "requested": True,
            "checks": len(self.lean_specs),
            "status": outcome.status,
        }
        if self.keep_temps:
            lean_metadata["sourcePath"] = outcome.source_path
            lean_metadata["command"] = outcome.command
        if self.lean_source_out and outcome.source:
            try:
                with open(self.lean_source_out, "w", encoding="utf-8") as handle:
                    handle.write(outcome.source)
            except OSError as exc:
                self.lean_gate.fail(
                    "lean.sourceOut",
                    f"could not write the generated Lean source to "
                    f"{self.lean_source_out!r}: {exc}", "<lean>")
            else:
                lean_metadata["sourceOut"] = self.lean_source_out
                lean_metadata["sourceOutSha256"] = sha256_bytes(
                    outcome.source.encode("utf-8"))
        self.report.metadata["lean"] = lean_metadata

    # ------------------------------------------------------------------ finish
    def _finalize(self) -> None:
        if self.provenance_checked and not self.provenance_gate.findings:
            self.provenance_gate.pass_(
                "provenance.valid",
                f"{self.provenance_checked} provenance record(s) reference existing "
                "sources and carry the required rationale")
        self.report.metadata["gates"] = {
            name: gate.status for name, gate in self.report.gates.items()
        }
        self.report.metadata["requestedChecks"] = sum(
            len(gate.findings) for gate in self.report.gates.values())

    # ---------------------------------------------------------------- helpers
    def _resolve_artifact_path(self, path: Any) -> str | None:
        if not isinstance(path, str) or not path.strip():
            return None
        if os.path.isabs(path) or path.startswith("~"):
            return None
        rel = os.path.normpath(path).replace(os.sep, "/")
        if rel.startswith("../") or rel == ".." or rel.startswith("/"):
            return None
        return rel

    def _git(self, args: list[str], default: str | None = None) -> str:
        try:
            completed = subprocess.run(
                ["git", "-C", self.repo_root] + args,
                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True, timeout=60,
            )
        except (OSError, subprocess.TimeoutExpired):
            if default is None:
                raise
            return default
        if completed.returncode != 0:
            if default is None:
                return ""
            return default
        return completed.stdout

    def _working_file(self, path: str) -> bytes | None:
        full = os.path.join(self.repo_root, path)
        if not os.path.isfile(full):
            return None
        with open(full, "rb") as handle:
            return handle.read()

    def _git_object(self, commit: str, path: str) -> bytes | None:
        key = (commit, path)
        if key in self._git_object_cache:
            return self._git_object_cache[key]
        try:
            completed = subprocess.run(
                ["git", "-C", self.repo_root, "show", f"{commit}:{path}"],
                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, timeout=60,
            )
        except (OSError, subprocess.TimeoutExpired):
            self._git_object_cache[key] = None
            return None
        if completed.returncode != 0:
            # Untracked working-tree file at HEAD is acceptable; a historical
            # snapshot must resolve through git.
            working = os.path.join(self.repo_root, path)
            if commit == self._head_sha and os.path.isfile(working):
                with open(working, "rb") as handle:
                    data = handle.read()
            else:
                data = None
        else:
            data = completed.stdout
        self._git_object_cache[key] = data
        return data


def load_manifest(path: str) -> dict[str, Any]:
    import json
    try:
        with open(path, encoding="utf-8") as handle:
            data = json.load(handle)
    except OSError as exc:
        raise ContractError(f"cannot read manifest {path}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise ContractError(f"manifest {path} is not valid JSON: {exc}") from exc
    if not isinstance(data, dict):
        raise ContractError(f"manifest {path} must be a JSON object")
    return data
