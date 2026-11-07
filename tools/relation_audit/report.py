"""Audit report model: checks, gates, coverage, and exit-code policy.

Policy (fail-closed, per docs/RELATION-AUDIT-CONTRACT.md section 8):

* any FAIL finding          -> overall FAIL       -> exit 1;
* any SKIP finding          -> overall INCOMPLETE -> exit 2;
* only PASS findings        -> overall PASS       -> exit 0.

A gate that contains no check is ``NOT_APPLICABLE``; it is never reported as
PASS.  In particular, when Lean checks are requested but cannot run, the Lean
gate carries SKIP findings, so the run cannot exit zero.
"""

from __future__ import annotations

from typing import Any


PASS = "PASS"
FAIL = "FAIL"
SKIP = "SKIP"
NOT_APPLICABLE = "NOT_APPLICABLE"
INCOMPLETE = "INCOMPLETE"

EXIT_PASS = 0
EXIT_FAIL = 1
EXIT_INCOMPLETE = 2


class Finding:
    """One machine-checkable audit result."""

    def __init__(self, status: str, code: str, message: str, location: str = ""):
        if status not in (PASS, FAIL, SKIP):
            raise ValueError(f"invalid finding status {status!r}")
        self.status = status
        self.code = code
        self.message = message
        self.location = location

    def to_json(self) -> dict[str, Any]:
        data = {"status": self.status, "code": self.code, "message": self.message}
        if self.location:
            data["location"] = self.location
        return data

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        return f"Finding({self.status!r}, {self.code!r}, {self.message!r})"


class Gate:
    def __init__(self, name: str, description: str = ""):
        self.name = name
        self.description = description
        self.findings: list[Finding] = []

    def add(self, status: str, code: str, message: str, location: str = "") -> Finding:
        finding = Finding(status, code, message, location)
        self.findings.append(finding)
        return finding

    def pass_(self, code: str, message: str, location: str = "") -> Finding:
        return self.add(PASS, code, message, location)

    def fail(self, code: str, message: str, location: str = "") -> Finding:
        return self.add(FAIL, code, message, location)

    def skip(self, code: str, message: str, location: str = "") -> Finding:
        return self.add(SKIP, code, message, location)

    @property
    def status(self) -> str:
        if not self.findings:
            return NOT_APPLICABLE
        if any(item.status == FAIL for item in self.findings):
            return FAIL
        if any(item.status == SKIP for item in self.findings):
            return INCOMPLETE
        return PASS

    def failures(self) -> list[Finding]:
        return [item for item in self.findings if item.status == FAIL]

    def skips(self) -> list[Finding]:
        return [item for item in self.findings if item.status == SKIP]

    def to_json(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "description": self.description,
            "status": self.status,
            "counts": {
                "PASS": sum(1 for f in self.findings if f.status == PASS),
                "FAIL": sum(1 for f in self.findings if f.status == FAIL),
                "SKIP": sum(1 for f in self.findings if f.status == SKIP),
            },
            "findings": [item.to_json() for item in self.findings],
        }


class Report:
    """Aggregates gates and the coverage/count sections of the audit report."""

    def __init__(self, manifest: str, schema: str, mode: str):
        self.manifest = manifest
        self.schema = schema
        self.mode = mode
        self.gates: dict[str, Gate] = {}
        self.metadata: dict[str, Any] = {}
        self.coverage: dict[str, Any] = {}
        self.counts: dict[str, Any] = {}
        self.unresolved: list[dict[str, Any]] = []
        self.caveats: list[dict[str, str]] = []

    def gate(self, name: str, description: str = "") -> Gate:
        if name not in self.gates:
            self.gates[name] = Gate(name, description)
        return self.gates[name]

    @property
    def status(self) -> str:
        statuses = [gate.status for gate in self.gates.values()]
        if any(status == FAIL for status in statuses):
            return FAIL
        if any(status == INCOMPLETE for status in statuses):
            return INCOMPLETE
        if any(status == PASS for status in statuses):
            return PASS
        return NOT_APPLICABLE

    @property
    def exit_code(self) -> int:
        status = self.status
        if status == PASS:
            return EXIT_PASS
        if status == FAIL:
            return EXIT_FAIL
        return EXIT_INCOMPLETE

    def all_findings(self) -> list[Finding]:
        return [finding for gate in self.gates.values() for finding in gate.findings]

    def to_json(self) -> dict[str, Any]:
        return {
            "tool": "relation_audit",
            "contract": "docs/RELATION-AUDIT-CONTRACT.md",
            "manifest": self.manifest,
            "schema": self.schema,
            "mode": self.mode,
            "status": self.status,
            "exitCode": self.exit_code,
            "metadata": self.metadata,
            "coverage": self.coverage,
            "counts": self.counts,
            "unresolved": self.unresolved,
            "caveats": self.caveats,
            "gates": {name: gate.to_json() for name, gate in self.gates.items()},
            "failureCount": sum(1 for f in self.all_findings() if f.status == FAIL),
            "skipCount": sum(1 for f in self.all_findings() if f.status == SKIP),
        }
