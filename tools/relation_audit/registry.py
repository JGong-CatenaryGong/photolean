"""Deterministic generator and checker for the production 136-pair registry.

The production registry is **derived** from the accepted R1/R2/R3 inputs:

* ``relation_audit/pilot.json`` (R1 accepted pilot manifest),
* ``relation_audit/generated/pair_inventory.json`` (R2 accepted 136-pair census),
* ``relation_audit/generated/relations_inventory.json`` (R2 accepted 78-row scan),
* ``relation_audit/dispositions.json`` (R2 accepted disposition ledger),
* the three ``relation_audit/migration/sections*.json`` fragments (R3 accepted),
* the accepted reports under ``relation_audit/reports/`` (hash pins),
* ``PhotoLean/Relations.lean`` and ``tools/counts.py`` (original census sources).

There is deliberately no second list of certificate IDs.  Every certificate row
in the registry is read either from the R1 pilot or from an R3 fragment; every
pair record is derived from the pair inventory and the certificate/fragment pair
association.  A certificate whose endpoints do not match its declared pair
association is retained as non-pair evidence rather than used to manufacture
pair coverage (the R3 ``kernel_marcusIC`` pin is the concrete case).

Running ``--generate`` writes:

* ``relation_audit/registry.json`` — the production full manifest;
* ``relation_audit/reports/registry-report.json`` — machine-readable mapping and
  input hash pins;
* ``relation_audit/reports/registry-report.md`` — human-readable summary.

Running ``--check`` re-derives everything, compares the registry and report byte
for byte with the checked-in copies, and fails on stale input hashes, missing
accepted certificates, invalid pair associations, hand-added certificate rows,
or any pair-coverage/status drift.

The module is standard-library only and never edits an accepted input.
"""

from __future__ import annotations

import ast
import copy
import hashlib
import json
import os
import re
from dataclasses import dataclass
from typing import Any, Iterable

SCHEMA_VERSION = "1.2.0"
PAIR_COUNT = 136
THEORY_COUNT = 17
SNAPSHOT_ID = "snap-relation-audit-2026-10-31"
GENERATED_KIND = "relation-full-registry-generation"
REPORT_SCHEMA_VERSION = "1.0.0"

REGISTRY_PATH = "relation_audit/registry.json"
REPORT_PATH = "relation_audit/reports/registry-report.json"
REPORT_MD_PATH = "relation_audit/reports/registry-report.md"

PILOT_PATH = "relation_audit/pilot.json"
SCHEMA_PATH = "relation_audit/schema.json"
DISPOSITIONS_PATH = "relation_audit/dispositions.json"
PAIR_INVENTORY_PATH = "relation_audit/generated/pair_inventory.json"
RELATIONS_INVENTORY_PATH = "relation_audit/generated/relations_inventory.json"
RELATIONS_SOURCE = "PhotoLean/Relations.lean"
COUNTS_SOURCE = "tools/counts.py"
PILOT_REPORT_PATH = "relation_audit/reports/production-pilot.json"
INVENTORY_REPORT_PATH = "relation_audit/reports/inventory-report.json"
MIGRATION_REPORT_PATH = "relation_audit/reports/migration-report.json"
FRAGMENT_PATHS = (
    "relation_audit/migration/sections01_05.json",
    "relation_audit/migration/sections06_10.json",
    "relation_audit/migration/sections11_17.json",
)

NON_EXISTENCE_PHRASE = "not a claim of logical non-existence"
CONSERVATIVE_ABSENCE_PHRASES = (
    NON_EXISTENCE_PHRASE,
    "not logical non-existence",
)
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
DEPENDENCY_KINDS = ("leanProbe", "sourceScan", "census", "search")


class RegistryError(Exception):
    """Raised when the accepted inputs or the derived registry are inconsistent."""

    def __init__(self, findings: Iterable["Finding"]):
        self.findings = list(findings)
        super().__init__("; ".join(f"{item.code}: {item.message}"
                                   for item in self.findings[:3]))


@dataclass(frozen=True)
class Finding:
    code: str
    message: str
    location: str = ""

    def as_dict(self) -> dict[str, str]:
        return {"code": self.code, "message": self.message, "location": self.location}

    def __str__(self) -> str:
        where = f" [{self.location}]" if self.location else ""
        return f"{self.code}{where}: {self.message}"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: str) -> str:
    with open(path, "rb") as handle:
        return sha256_bytes(handle.read())


def canonical_json(value: Any) -> str:
    """Deterministic JSON used for both file output and byte comparisons."""
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def slug(value: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9]+", "-", value).strip("-")
    return cleaned or "value"


def _read_json(root: str, relative: str) -> dict[str, Any]:
    path = os.path.join(root, relative)
    with open(path, encoding="utf-8") as handle:
        return json.load(handle)


def _read_text(root: str, relative: str) -> str:
    with open(os.path.join(root, relative), encoding="utf-8") as handle:
        return handle.read()


# --------------------------------------------------------------------------- inputs
def load_inputs(root: str) -> dict[str, Any]:
    """Load every accepted input and source artifact, with SHA-256 pins."""
    root = os.path.abspath(root)
    inputs: dict[str, Any] = {
        "root": root,
        "schema": _read_json(root, SCHEMA_PATH),
        "pilot": _read_json(root, PILOT_PATH),
        "dispositions": _read_json(root, DISPOSITIONS_PATH),
        "pair_inventory": _read_json(root, PAIR_INVENTORY_PATH),
        "relations_inventory": _read_json(root, RELATIONS_INVENTORY_PATH),
        "pilot_report": _read_json(root, PILOT_REPORT_PATH),
        "inventory_report": _read_json(root, INVENTORY_REPORT_PATH),
        "migration_report": _read_json(root, MIGRATION_REPORT_PATH),
        "fragments": [],
        "fragment_paths": list(FRAGMENT_PATHS),
        "hashes": {},
        "relations_source": _read_text(root, RELATIONS_SOURCE),
        "counts_source": _read_text(root, COUNTS_SOURCE),
    }
    for name, relative in (
        ("schema", SCHEMA_PATH),
        ("pilot", PILOT_PATH),
        ("dispositions", DISPOSITIONS_PATH),
        ("pair_inventory", PAIR_INVENTORY_PATH),
        ("relations_inventory", RELATIONS_INVENTORY_PATH),
        ("pilot_report", PILOT_REPORT_PATH),
        ("inventory_report", INVENTORY_REPORT_PATH),
        ("migration_report", MIGRATION_REPORT_PATH),
        ("relations_source", RELATIONS_SOURCE),
        ("counts_source", COUNTS_SOURCE),
    ):
        inputs["hashes"][relative] = sha256_file(os.path.join(root, relative))
        inputs[name + "_path"] = relative
    for relative in FRAGMENT_PATHS:
        fragment = _read_json(root, relative)
        inputs["fragments"].append(fragment)
        inputs["hashes"][relative] = sha256_file(os.path.join(root, relative))
        lean_source = fragment.get("leanSource")
        if lean_source:
            inputs["hashes"][lean_source] = sha256_file(
                os.path.join(root, lean_source))
    return inputs


def _finding(code: str, message: str, location: str = "") -> Finding:
    return Finding(code=code, message=message, location=location)


# ----------------------------------------------------------------------- validation
def validate_accepted_inputs(inputs: dict[str, Any]) -> list[Finding]:
    """Fail-closed checks over the accepted R1/R2/R3 inputs and their hash pins."""
    findings: list[Finding] = []
    root = inputs["root"]
    schema = inputs["schema"]
    pilot = inputs["pilot"]
    dispositions = inputs["dispositions"]
    pair_inventory = inputs["pair_inventory"]
    relations_inventory = inputs["relations_inventory"]
    pilot_report = inputs["pilot_report"]
    inventory_report = inputs["inventory_report"]
    migration_report = inputs["migration_report"]
    fragments = inputs["fragments"]
    hashes = inputs["hashes"]

    # -- schema ------------------------------------------------------------
    schema_props = schema.get("properties", {})
    schema_version = (schema_props.get("schemaVersion") or {}).get("const")
    schema_pair_count = (schema_props.get("pairCount") or {}).get("const")
    if schema_version != SCHEMA_VERSION:
        findings.append(_finding(
            "input.schemaVersion",
            f"schemaVersion is {schema_version!r}, expected {SCHEMA_VERSION!r}",
            SCHEMA_PATH))
    if schema_pair_count != PAIR_COUNT:
        findings.append(_finding(
            "input.pairCount",
            f"schema pairCount is {schema_pair_count!r}, expected {PAIR_COUNT}",
            SCHEMA_PATH))
    if hashes.get(SCHEMA_PATH) != pilot_report.get("metadata", {}).get("schemaSha256"):
        findings.append(_finding(
            "input.drift",
            "schema hash does not match the accepted R1 report metadata",
            SCHEMA_PATH))
    if pilot_report.get("status") != "PASS" or pilot_report.get("exitCode") != 0:
        findings.append(_finding(
            "input.pilotReport",
            "accepted R1 production report is not a PASS with exit 0",
            PILOT_REPORT_PATH))
    if pilot_report.get("metadata", {}).get("manifestSha256") != hashes.get(PILOT_PATH):
        findings.append(_finding(
            "input.drift",
            "pilot hash does not match the accepted R1 report metadata",
            PILOT_PATH))
    if pilot.get("mode") != "pilot":
        findings.append(_finding(
            "pilot.mode", f"R1 pilot mode is {pilot.get('mode')!r}, expected 'pilot'",
            PILOT_PATH))
    if pilot.get("schemaVersion") != SCHEMA_VERSION:
        findings.append(_finding(
            "pilot.schemaVersion",
            f"R1 pilot schemaVersion is {pilot.get('schemaVersion')!r}", PILOT_PATH))
    if pilot.get("pairCount") != PAIR_COUNT:
        findings.append(_finding(
            "pilot.pairCount", f"R1 pilot pairCount is {pilot.get('pairCount')!r}", PILOT_PATH))

    theory_inventory = pilot.get("theoryInventory")
    if not isinstance(theory_inventory, list) or len(theory_inventory) != THEORY_COUNT \
            or len(set(theory_inventory)) != THEORY_COUNT:
        findings.append(_finding(
            "input.theoryInventory",
            "R1 theoryInventory must contain 17 unique theory ids", PILOT_PATH))
        theory_inventory = list(theory_inventory or [])
    if pair_inventory.get("source", {}).get("theories") != theory_inventory:
        findings.append(_finding(
            "pairInventory.theories",
            "pair inventory theory list differs from the R1 theory inventory",
            PAIR_INVENTORY_PATH))
    counts_theories = _counts_theories(inputs["counts_source"])
    if counts_theories != theory_inventory:
        findings.append(_finding(
            "counts.theories",
            f"tools/counts.py THEORIES {counts_theories!r} differs from the R1 theory inventory",
            COUNTS_SOURCE))

    # -- accepted hash pins -------------------------------------------------
    source_of_truth = inventory_report.get("sourceOfTruth", {})
    generated = inventory_report.get("generatedArtifacts", {})
    pin_checks = (
        (PILOT_PATH, source_of_truth.get("pilotSha256"), "pilot"),
        (DISPOSITIONS_PATH, source_of_truth.get("dispositionsSha256"), "dispositions"),
        (PAIR_INVENTORY_PATH, generated.get("pairsSha256"), "pair inventory"),
        (RELATIONS_INVENTORY_PATH, generated.get("declarationsSha256"), "declaration inventory"),
        (RELATIONS_SOURCE, source_of_truth.get("relationsSha256"), "Relations.lean"),
        (COUNTS_SOURCE, source_of_truth.get("scannerSha256"), "counts.py"),
    )
    for relative, expected, label in pin_checks:
        if not expected or hashes.get(relative) != expected:
            findings.append(_finding(
                "input.drift",
                f"{label} hash {hashes.get(relative)!r} does not match the accepted R2 "
                f"report pin {expected!r}",
                relative))
    if pair_inventory.get("source", {}).get("scannerSha256") != hashes.get(COUNTS_SOURCE):
        findings.append(_finding(
            "pairInventory.scanner",
            "pair inventory scanner hash does not match tools/counts.py",
            PAIR_INVENTORY_PATH))
    if pair_inventory.get("artifactKind") != "relation-pair-inventory":
        findings.append(_finding(
            "pairInventory.kind", "input is not a relation-pair inventory",
            PAIR_INVENTORY_PATH))

    # -- 136-pair universe --------------------------------------------------
    pairs = pair_inventory.get("pairs")
    if not isinstance(pairs, list) or len(pairs) != PAIR_COUNT:
        findings.append(_finding(
            "pairInventory.count",
            f"pair inventory has {len(pairs) if isinstance(pairs, list) else 'no'} pairs, "
            f"expected {PAIR_COUNT}", PAIR_INVENTORY_PATH))
        pairs = []
    pair_by_id: dict[str, dict[str, Any]] = {}
    seen_pairs: set[frozenset[str]] = set()
    for index, pair in enumerate(pairs):
        location = f"{PAIR_INVENTORY_PATH}.pairs[{index}]"
        pair_id = pair.get("pairId")
        theories = pair.get("theories")
        if not isinstance(pair_id, str) or not pair_id:
            findings.append(_finding("pairInventory.pairId", "pair has no id", location))
            continue
        if pair_id in pair_by_id:
            findings.append(_finding("pairInventory.duplicate", f"duplicate pair id {pair_id!r}",
                                     location))
        pair_by_id[pair_id] = pair
        if not isinstance(theories, list) or len(theories) != 2 \
                or any(item not in theory_inventory for item in theories):
            findings.append(_finding(
                "pairInventory.theories",
                f"pair {pair_id!r} has invalid theories {theories!r}", location))
            continue
        if len(set(theories)) != 2:
            findings.append(_finding(
                "pairInventory.intraTheory",
                f"pair {pair_id!r} is not a cross-theory pair", location))
        expected_id = "P-" + "-".join(theories)
        if pair_id != expected_id:
            findings.append(_finding(
                "pairInventory.pairId",
                f"pair id {pair_id!r} is not the canonical {expected_id!r}", location))
        key = frozenset(theories)
        if key in seen_pairs:
            findings.append(_finding(
                "pairInventory.duplicate", f"duplicate unordered pair {sorted(key)!r}", location))
        seen_pairs.add(key)
        if pair.get("auditJudgment") is not None:
            findings.append(_finding(
                "pairInventory.auditJudgment",
                f"pair {pair_id!r} carries an auditJudgment; the inventory is metadata only",
                location))
        if (pair.get("migration") or {}).get("status") != "not-audited":
            findings.append(_finding(
                "pairInventory.migrationStatus",
                f"pair {pair_id!r} migration status is not 'not-audited'", location))
    expected_universe = {frozenset(item) for item in _combinations(theory_inventory, 2)}
    if seen_pairs != expected_universe:
        missing = sorted(tuple(sorted(item)) for item in expected_universe - seen_pairs)
        findings.append(_finding(
            "pairInventory.universe",
            f"pair inventory universe differs from C(17,2); missing {missing[:6]!r}",
            PAIR_INVENTORY_PATH))
    if pair_inventory.get("unaccountedPairs"):
        findings.append(_finding(
            "pairInventory.unaccounted",
            f"pair inventory reports unaccounted pairs {pair_inventory.get('unaccountedPairs')!r}",
            PAIR_INVENTORY_PATH))
    if pair_inventory.get("bothEdgeAndAbsence"):
        findings.append(_finding(
            "pairInventory.bothEdgeAndAbsence",
            "pair inventory reports pairs in both edge and absence registries",
            PAIR_INVENTORY_PATH))
    counts = pair_inventory.get("counts", {})
    if counts.get("pairs") != PAIR_COUNT or counts.get("legacyCoveredPairs") != PAIR_COUNT:
        findings.append(_finding(
            "pairInventory.counts",
            f"pair inventory counts are inconsistent: {counts!r}", PAIR_INVENTORY_PATH))
    if counts.get("legacyEdges") != 26 or counts.get("legacyUniqueAbsences") != 110:
        findings.append(_finding(
            "pairInventory.legacyCounts",
            f"legacy edge/absence counts changed: {counts!r}", PAIR_INVENTORY_PATH))

    # -- dispositions -------------------------------------------------------
    entries = dispositions.get("entries")
    if not isinstance(entries, list) or len(entries) != 78:
        findings.append(_finding(
            "dispositions.count",
            f"disposition ledger has {len(entries) if isinstance(entries, list) else 'no'} "
            "entries, expected 78", DISPOSITIONS_PATH))
        entries = []
    disposition_vocab = {item.get("id") for item in dispositions.get("dispositionVocabulary", [])}
    role_vocab = {item.get("id") for item in dispositions.get("relationRoleVocabulary", [])}
    seen_declarations: set[str] = set()
    for index, entry in enumerate(entries):
        location = f"{DISPOSITIONS_PATH}.entries[{index}]"
        declaration_id = entry.get("declarationId")
        if not isinstance(declaration_id, str) or not declaration_id:
            findings.append(_finding("dispositions.id", "entry has no declarationId", location))
            continue
        if declaration_id in seen_declarations:
            findings.append(_finding(
                "dispositions.duplicate", f"duplicate declarationId {declaration_id!r}", location))
        seen_declarations.add(declaration_id)
        if entry.get("disposition") not in disposition_vocab:
            findings.append(_finding(
                "dispositions.disposition",
                f"{declaration_id!r} has unknown disposition {entry.get('disposition')!r}",
                location))
        if entry.get("relationRole") not in role_vocab:
            findings.append(_finding(
                "dispositions.role",
                f"{declaration_id!r} has unknown relationRole {entry.get('relationRole')!r}",
                location))
        for pair_id in list(entry.get("pairIds") or []) + list(entry.get("relatedPairIds") or []):
            if pair_id not in pair_by_id:
                findings.append(_finding(
                    "dispositions.pair",
                    f"{declaration_id!r} names unknown pair {pair_id!r}", location))
        if not entry.get("rationale") or not entry.get("provenance", {}).get("references"):
            findings.append(_finding(
                "dispositions.provenance",
                f"{declaration_id!r} has no rationale or provenance references", location))
        if not entry.get("nonAuditMetadata"):
            findings.append(_finding(
                "dispositions.nonAuditMetadata",
                f"{declaration_id!r} is not marked nonAuditMetadata", location))
    certificate_required = [
        entry for entry in entries if entry.get("disposition") == "certificate-required"
    ]
    if len(certificate_required) != 41:
        findings.append(_finding(
            "dispositions.queue",
            f"certificate-required queue has {len(certificate_required)} rows, expected 41",
            DISPOSITIONS_PATH))

    # -- relations inventory ------------------------------------------------
    if relations_inventory.get("artifactKind") != "relation-declaration-inventory":
        findings.append(_finding(
            "relationsInventory.kind", "input is not a relation-declaration inventory",
            RELATIONS_INVENTORY_PATH))
    declarations = relations_inventory.get("declarations")
    if not isinstance(declarations, list) or len(declarations) != 78:
        findings.append(_finding(
            "relationsInventory.count",
            "declaration inventory does not contain the accepted 78 rows",
            RELATIONS_INVENTORY_PATH))
    else:
        inventory_ids = {item.get("declarationId") for item in declarations}
        if inventory_ids != seen_declarations:
            findings.append(_finding(
                "relationsInventory.ids",
                "declaration inventory ids are not in one-to-one correspondence with the "
                "disposition ledger", RELATIONS_INVENTORY_PATH))

    # -- migration fragments ------------------------------------------------
    queue_ids = {entry["declarationId"] for entry in certificate_required}
    fragment_entries: list[dict[str, Any]] = []
    seen_fragment_ids: set[str] = set()
    for fragment, relative in zip(fragments, FRAGMENT_PATHS):
        if fragment.get("artifactKind") != "relation-migration-fragment":
            findings.append(_finding(
                "fragment.kind", "input is not a relation-migration fragment", relative))
        if fragment.get("scope") != "migration-fragment":
            findings.append(_finding(
                "fragment.scope", f"fragment scope is {fragment.get('scope')!r}", relative))
        lean_source = fragment.get("leanSource")
        if not lean_source or not os.path.isfile(os.path.join(root, lean_source)):
            findings.append(_finding(
                "fragment.leanSource", f"fragment lean source {lean_source!r} is missing",
                relative))
        else:
            actual = sha256_file(os.path.join(root, lean_source))
            declared = fragment.get("leanSourceSha256")
            if declared and actual != declared:
                findings.append(_finding(
                    "input.drift",
                    f"fragment lean source hash {actual!r} differs from declared {declared!r}",
                    lean_source))
        for entry in fragment.get("entries", []):
            declaration_id = entry.get("declarationId")
            if not isinstance(declaration_id, str):
                findings.append(_finding("fragment.id", "fragment entry has no id", relative))
                continue
            if declaration_id in seen_fragment_ids:
                findings.append(_finding(
                    "fragment.duplicate", f"duplicate fragment entry {declaration_id!r}",
                    relative))
            seen_fragment_ids.add(declaration_id)
            fragment_entries.append(entry)
            outcome = entry.get("outcome")
            if outcome == "certified":
                for field in ("certificate", "relationKind", "certificateConstructor",
                              "leanModule", "premises", "statement"):
                    if field not in entry or entry.get(field) in (None, ""):
                        findings.append(_finding(
                            "fragment.certificate",
                            f"certified row {declaration_id!r} is missing {field!r}", relative))
                if entry.get("relationKind") not in CERTIFIED_KINDS:
                    findings.append(_finding(
                        "fragment.kind",
                        f"certified row {declaration_id!r} has kind "
                        f"{entry.get('relationKind')!r}", relative))
                if entry.get("axiomFootprint") is None:
                    findings.append(_finding(
                        "fragment.axiomFootprint",
                        f"certified row {declaration_id!r} has no axiom footprint", relative))
            elif outcome == "reclassified":
                if not entry.get("targetCategory") or not entry.get("rationale"):
                    findings.append(_finding(
                        "fragment.reclassified",
                        f"reclassified row {declaration_id!r} lacks targetCategory or rationale",
                        relative))
            else:
                findings.append(_finding(
                    "fragment.outcome",
                    f"row {declaration_id!r} has unknown outcome {outcome!r}", relative))
    missing_queue = sorted(queue_ids - seen_fragment_ids)
    extra_queue = sorted(seen_fragment_ids - queue_ids)
    if missing_queue or extra_queue:
        findings.append(_finding(
            "fragment.queue",
            f"fragments do not cover the R2 certificate-required queue exactly; "
            f"missing {missing_queue[:6]!r}, extra {extra_queue[:6]!r}", FRAGMENT_PATHS[0]))

    # -- accepted report cross-checks --------------------------------------
    report_counts = migration_report.get("counts", {})
    certified_rows = [entry for entry in fragment_entries if entry.get("outcome") == "certified"]
    reclassified_rows = [
        entry for entry in fragment_entries if entry.get("outcome") == "reclassified"
    ]
    if report_counts.get("certified") != len(certified_rows) \
            or report_counts.get("reclassified") != len(reclassified_rows) \
            or report_counts.get("declarations") != len(fragment_entries):
        findings.append(_finding(
            "input.drift",
            "accepted R3 report counts do not match the fragments: "
            f"report {report_counts!r}, fragments certified={len(certified_rows)} "
            f"reclassified={len(reclassified_rows)}", MIGRATION_REPORT_PATH))
    reported_certificates = {
        item.get("certificate") for item in migration_report.get("certificates", [])
    }
    fragment_certificates = {entry.get("certificate") for entry in certified_rows}
    if reported_certificates != fragment_certificates:
        findings.append(_finding(
            "input.drift",
            "accepted R3 report certificate list differs from the fragments",
            MIGRATION_REPORT_PATH))
    if inventory_report.get("status") != "INVENTORY_ONLY":
        findings.append(_finding(
            "input.inventoryReport",
            f"accepted R2 inventory status is {inventory_report.get('status')!r}",
            INVENTORY_REPORT_PATH))

    # -- R1 pilot internal references --------------------------------------
    pilot_findings = _validate_pilot(pilot, root, hashes)
    findings.extend(pilot_findings)

    # -- every accepted certificate has a unique Lean declaration ----------
    certificates = pilot.get("certificates", [])
    lean_names = [item.get("lean") for item in certificates if isinstance(item, dict)]
    if len(lean_names) != len(set(lean_names)):
        findings.append(_finding(
            "pilot.certificateDuplicate",
            "R1 pilot repeats a Lean certificate declaration", PILOT_PATH))
    fragment_cert_names = [entry.get("certificate") for entry in certified_rows]
    if len(fragment_cert_names) != len(set(fragment_cert_names)):
        findings.append(_finding(
            "fragment.certificateDuplicate",
            "R3 fragments repeat a Lean certificate declaration", FRAGMENT_PATHS[0]))
    if set(lean_names) & set(fragment_cert_names):
        findings.append(_finding(
            "input.certificateDuplicate",
            "R1 and R3 certificate sets overlap", PILOT_PATH))

    # -- candidate rows -----------------------------------------------------
    candidates = []
    for pair in pairs:
        candidate = pair.get("candidate")
        if candidate:
            if candidate.get("kind") != "unresolved-candidate":
                findings.append(_finding(
                    "pairInventory.candidate",
                    f"pair {pair.get('pairId')!r} has unexpected candidate kind "
                    f"{candidate.get('kind')!r}", PAIR_INVENTORY_PATH))
            candidates.append(pair)
    if len(candidates) != 6:
        findings.append(_finding(
            "pairInventory.candidates",
            f"pair inventory has {len(candidates)} undelivered candidates, expected 6",
            PAIR_INVENTORY_PATH))

    return findings


def _counts_theories(source: str) -> list[str]:
    """Extract the literal ``THEORIES`` list from tools/counts.py without executing it."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 \
                and isinstance(node.targets[0], ast.Name) \
                and node.targets[0].id == "THEORIES":
            try:
                value = ast.literal_eval(node.value)
            except (ValueError, SyntaxError):
                return []
            if isinstance(value, list) and all(isinstance(item, str) for item in value):
                return value
    return []


def _combinations(items: list[str], size: int) -> list[tuple[str, ...]]:
    if size == 0:
        return [()]
    result: list[tuple[str, ...]] = []
    for index, item in enumerate(items):
        for tail in _combinations(items[index + 1:], size - 1):
            result.append((item,) + tail)
    return result


def _validate_pilot(pilot: dict[str, Any], root: str, hashes: dict[str, str]) -> list[Finding]:
    findings: list[Finding] = []
    statements = pilot.get("statements", [])
    queries = pilot.get("queries", [])
    certificates = pilot.get("certificates", [])
    records = pilot.get("records", [])
    statement_map = {item.get("id"): item for item in statements if isinstance(item, dict)}
    query_map = {item.get("id"): item for item in queries if isinstance(item, dict)}
    certificate_map = {item.get("id"): item for item in certificates if isinstance(item, dict)}
    record_ids = [item.get("id") for item in records if isinstance(item, dict)]
    if len(record_ids) != len(set(record_ids)):
        findings.append(_finding("pilot.recordDuplicate", "R1 pilot repeats a record id",
                                 PILOT_PATH))
    if len(statement_map) != len(statements):
        findings.append(_finding("pilot.statementDuplicate", "R1 pilot repeats a statement id",
                                 PILOT_PATH))
    if len(query_map) != len(queries):
        findings.append(_finding("pilot.queryDuplicate", "R1 pilot repeats a query id", PILOT_PATH))
    if len(certificate_map) != len(certificates):
        findings.append(_finding("pilot.certificateDuplicate",
                                 "R1 pilot repeats a certificate id", PILOT_PATH))
    for statement in statements:
        artifact = statement.get("artifact")
        digest = statement.get("sha256")
        if not artifact or not digest:
            findings.append(_finding("pilot.statement",
                                     f"statement {statement.get('id')!r} is incomplete", PILOT_PATH))
            continue
        full = os.path.join(root, artifact)
        if not os.path.isfile(full):
            findings.append(_finding("pilot.statementArtifact",
                                     f"statement {statement.get('id')!r} artifact missing",
                                     artifact))
        elif sha256_file(full) != digest:
            findings.append(_finding("pilot.statementHash",
                                     f"statement {statement.get('id')!r} hash is stale", artifact))
    for query in queries:
        if query.get("source") not in statement_map or query.get("target") not in statement_map:
            findings.append(_finding("pilot.query",
                                     f"query {query.get('id')!r} endpoint does not resolve",
                                     PILOT_PATH))
    for record in records:
        query = query_map.get(record.get("queryId"))
        if query is None:
            findings.append(_finding("pilot.recordQuery",
                                     f"record {record.get('id')!r} query does not resolve",
                                     PILOT_PATH))
        status = record.get("status")
        if status == "certified":
            certificate = certificate_map.get(record.get("certificate"))
            if certificate is None:
                findings.append(_finding("pilot.recordCertificate",
                                         f"record {record.get('id')!r} certificate does not resolve",
                                         PILOT_PATH))
            elif certificate.get("kind") != record.get("relationKind"):
                findings.append(_finding("pilot.recordKind",
                                         f"record {record.get('id')!r} kind differs from its "
                                         "certificate", PILOT_PATH))
        elif status in ("unresolved", "notEstablished"):
            if not record.get("rationale"):
                findings.append(_finding("pilot.rationale",
                                         f"record {record.get('id')!r} has no rationale",
                                         PILOT_PATH))
            if status == "notEstablished" and not record.get("dependencies"):
                findings.append(_finding("pilot.dependencies",
                                         f"record {record.get('id')!r} has no dependencies",
                                         PILOT_PATH))
        else:
            findings.append(_finding("pilot.status",
                                     f"record {record.get('id')!r} has status {status!r}",
                                     PILOT_PATH))
    # Snapshot pins are matched against the working tree because the relation
    # layer is intentionally uncommitted (the accepted R1 caveat).
    snapshots = pilot.get("snapshots", [])
    if len(snapshots) != 1:
        findings.append(_finding("pilot.snapshot", "R1 pilot must pin exactly one snapshot",
                                 PILOT_PATH))
    for snapshot in snapshots:
        artifacts = snapshot.get("artifacts") or {}
        for path, recorded in artifacts.items():
            full = os.path.join(root, path)
            if not os.path.isfile(full):
                findings.append(_finding("pilot.snapshotArtifact",
                                         f"snapshot artifact {path!r} is missing", path))
            elif sha256_file(full) != recorded:
                findings.append(_finding("pilot.snapshotHash",
                                         f"snapshot artifact {path!r} hash is stale", path))
    return findings


# ------------------------------------------------------------------------- building
def build_registry(inputs: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    """Derive the production registry and its mapping report from accepted inputs."""
    findings = validate_accepted_inputs(inputs)
    if findings:
        raise RegistryError(findings)
    return _build(inputs)


def _build(inputs: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    root = inputs["root"]
    pilot = inputs["pilot"]
    pair_inventory = inputs["pair_inventory"]
    fragments = inputs["fragments"]
    dispositions = inputs["dispositions"]
    pair_by_id = {pair["pairId"]: pair for pair in pair_inventory["pairs"]}
    theory_inventory = list(pilot["theoryInventory"])
    theory_set = set(theory_inventory)

    snapshot = copy.deepcopy(pilot["snapshots"][0])
    snapshot["artifacts"] = dict(snapshot.get("artifacts") or {})
    statements = copy.deepcopy(pilot["statements"])
    queries = copy.deepcopy(pilot["queries"])
    certificates = copy.deepcopy(pilot["certificates"])
    records = copy.deepcopy(pilot["records"])
    scopes = copy.deepcopy(pilot["scopes"])

    statement_map = {item["id"]: item for item in statements}
    statement_keys: dict[tuple[str, str], str] = {}
    query_map = {item["id"]: item for item in queries}
    certificate_map = {item["id"]: item for item in certificates}
    record_ids = {item["id"] for item in records}
    scope_ids = {item["id"] for item in scopes}

    artifact_hashes: dict[str, str] = {}

    def artifact_hash(path: str) -> str:
        if path not in artifact_hashes:
            full = os.path.join(root, path)
            if not os.path.isfile(full):
                raise RegistryError([_finding(
                    "registry.artifactMissing", f"artifact {path!r} does not exist", path)])
            artifact_hashes[path] = sha256_file(full)
        return artifact_hashes[path]

    def add_statement(statement: dict[str, Any]) -> str:
        ident = statement["id"]
        if ident in statement_map:
            raise RegistryError([_finding(
                "registry.statementDuplicate", f"statement id {ident!r} is duplicated", ident)])
        statement_map[ident] = statement
        statements.append(statement)
        return ident

    def add_query(query: dict[str, Any]) -> str:
        ident = query["id"]
        if ident in query_map:
            raise RegistryError([_finding(
                "registry.queryDuplicate", f"query id {ident!r} is duplicated", ident)])
        query_map[ident] = query
        queries.append(query)
        return ident

    def add_record(record: dict[str, Any]) -> str:
        ident = record["id"]
        if ident in record_ids:
            raise RegistryError([_finding(
                "registry.recordDuplicate", f"record id {ident!r} is duplicated", ident)])
        record_ids.add(ident)
        records.append(record)
        return ident

    def add_scope(scope: dict[str, Any]) -> str:
        ident = scope["id"]
        if ident in scope_ids:
            raise RegistryError([_finding(
                "registry.scopeDuplicate", f"scope id {ident!r} is duplicated", ident)])
        scope_ids.add(ident)
        scopes.append(scope)
        return ident

    def pin_artifact(path: str) -> None:
        snapshot["artifacts"][path] = artifact_hash(path)

    mapping: list[dict[str, Any]] = []
    pair_records: dict[str, list[str]] = {pair_id: [] for pair_id in pair_by_id}
    record_pair: dict[str, str | None] = {}

    # ---- R1 pilot certificate mapping -----------------------------------
    used_pilot_certificates: set[str] = set()
    for record in records:
        if record.get("status") == "certified":
            used_pilot_certificates.add(record.get("certificate"))
        pair = _record_pair(record, query_map, statement_map, theory_set, pair_by_id)
        record_pair[record["id"]] = pair
        if pair:
            pair_records[pair].append(record["id"])
    for certificate in pilot["certificates"]:
        ident = certificate["id"]
        cert_records = [record for record in records
                        if record.get("certificate") == ident]
        pair_ids = sorted({
            record_pair[record["id"]] for record in cert_records
            if record.get("id") in record_pair and record_pair[record["id"]]
        })
        if ident in used_pilot_certificates:
            outcome = "pair-record" if pair_ids else "intra-theory-record"
            reason = None
        else:
            outcome = "composition-parent"
            reason = ("Accepted R1 composition parent certificate; consumed by the "
                      "conditionalComposition record and not a direct pair record itself.")
        mapping.append({
            "source": "R1 pilot",
            "declarationId": None,
            "certificate": ident,
            "kind": certificate.get("kind"),
            "pairIds": pair_ids,
            "outcome": outcome,
            "registryCertificate": ident,
            "recordIds": [record["id"] for record in cert_records],
            "reason": reason,
        })

    # ---- R3 fragment certificates and pair records -----------------------
    accepted_certificate_names = {
        item.get("lean") for item in pilot["certificates"]
    } | {item.get("certificate") for fragment in fragments for item in fragment["entries"]
         if item.get("outcome") == "certified"}
    fragment_certificate_rows: list[dict[str, Any]] = []
    reclassified_rows: list[dict[str, Any]] = []

    for fragment, relative in zip(fragments, inputs["fragment_paths"]):
        lean_source = fragment["leanSource"]
        pin_artifact(lean_source)
        for entry in fragment["entries"]:
            outcome = entry["outcome"]
            if outcome == "reclassified":
                reclassified_rows.append({
                    "declarationId": entry["declarationId"],
                    "pairIds": list(entry.get("pairIds") or []),
                    "targetCategory": entry.get("targetCategory"),
                    "evidence": entry.get("evidenceLeanName"),
                    "leanModule": entry.get("leanModule"),
                    "rationale": entry.get("rationale"),
                    "section": entry.get("section"),
                })
                continue
            if outcome != "certified":
                continue
            certificate_id = "cert-" + slug(entry["declarationId"])
            if certificate_id in certificate_map:
                raise RegistryError([_finding(
                    "registry.certificateDuplicate",
                    f"certificate id {certificate_id!r} is duplicated", relative)])
            certificate = _certificate_from_fragment(entry, fragment, certificate_id, root)
            certificates.append(certificate)
            certificate_map[certificate_id] = certificate
            pin_artifact(lean_source)
            if certificate.get("sourcePath"):
                pin_artifact(certificate["sourcePath"])

            pair_ids = list(entry.get("pairIds") or [])
            statement = entry["statement"]
            left_theory = _strip_photo(statement["left"]["theory"])
            right_theory = _strip_photo(statement["right"]["theory"])
            endpoint_theories = {left_theory, right_theory}
            pair_id: str | None = None
            pair_reason: str | None = None
            if not pair_ids:
                pair_reason = ("Kernel-to-theory or otherwise non-pair certificate: the R3 "
                               "fragment declares no pair association, so it is retained as "
                               "non-pair evidence and must not manufacture pair coverage.")
            elif len(pair_ids) != 1:
                raise RegistryError([_finding(
                    "registry.pairAssociation",
                    f"{entry['declarationId']!r} declares multiple pair ids {pair_ids!r}",
                    relative)])
            else:
                candidate_pair = pair_by_id.get(pair_ids[0])
                if candidate_pair is None:
                    raise RegistryError([_finding(
                        "registry.pairUnknown",
                        f"{entry['declarationId']!r} names unknown pair {pair_ids[0]!r}",
                        relative)])
                if endpoint_theories != set(candidate_pair["theories"]):
                    pair_reason = (
                        f"Accepted R3 certificate {entry['certificate']} has endpoints "
                        f"{sorted(endpoint_theories)!r}, which do not match the declared pair "
                        f"{pair_ids[0]!r} {sorted(candidate_pair['theories'])!r}; using it as a "
                        "pair record would manufacture a pair that the certificate does not "
                        "state. It is retained as non-pair kernel evidence."
                    )
                else:
                    pair_id = pair_ids[0]

            record_ids_for_cert: list[str] = []
            if pair_id is not None:
                left_statement_id = _fragment_statement(
                    entry, "left", add_statement, statement_map, statement_keys,
                    pin_artifact, artifact_hash)
                right_statement_id = _fragment_statement(
                    entry, "right", add_statement, statement_map, statement_keys,
                    pin_artifact, artifact_hash)
                if left_statement_id == right_statement_id:
                    raise RegistryError([_finding(
                        "registry.pairEndpoint",
                        f"{entry['declarationId']!r} resolves both endpoints to the same "
                        "statement", relative)])
                query_id = "q-" + slug(entry["declarationId"])
                version = f"{left_statement_id}@1.0.0|{right_statement_id}@1.0.0"
                provenance = _fragment_provenance(entry, fragment)
                query = {
                    "id": query_id,
                    "source": left_statement_id,
                    "target": right_statement_id,
                    "context": entry.get("sharedContext") or "relation-audit shared context",
                    "provenance": provenance,
                    "question": (f"Does the accepted {entry['relationKind']} certificate "
                                 f"{entry['certificate']} relate these two statements?"),
                }
                add_query(query)
                record = {
                    "id": "rec-" + slug(entry["declarationId"]),
                    "queryId": query_id,
                    "statementVersion": version,
                    "scope": "global",
                    "snapshot": snapshot["id"],
                    "status": "certified",
                    "relationKind": entry["relationKind"],
                    "certificate": certificate_id,
                    "premises": [
                        {"id": premise["id"], "statement": premise["statement"]}
                        for premise in entry.get("premises", [])
                    ],
                    "badges": {},
                    "rationale": (
                        f"Certified from the accepted R3 declaration "
                        f"{entry['declarationId']}; certificate {entry['certificate']}."
                    ),
                    "provenance": provenance,
                }
                add_record(record)
                record_ids_for_cert.append(record["id"])
                pair_records[pair_id].append(record["id"])
                record_pair[record["id"]] = pair_id
            mapping.append({
                "source": "R3 migration",
                "declarationId": entry["declarationId"],
                "certificate": entry["certificate"],
                "kind": entry["relationKind"],
                "pairIds": pair_ids,
                "endpointTheories": sorted(endpoint_theories),
                "outcome": "pair-record" if pair_id else "non-pair-evidence",
                "registryCertificate": certificate_id,
                "recordIds": record_ids_for_cert,
                "reason": pair_reason,
            })
            fragment_certificate_rows.append(entry)

    # ---- make sure every accepted certificate is accounted for -----------
    registered_certificate_names = {item["lean"] for item in certificates}
    if registered_certificate_names != accepted_certificate_names:
        missing = sorted(accepted_certificate_names - registered_certificate_names)
        extra = sorted(registered_certificate_names - accepted_certificate_names)
        raise RegistryError([_finding(
            "registry.certificateCoverage",
            f"registry certificate set differs from accepted inputs; missing {missing[:6]!r}, "
            f"extra {extra[:6]!r}", REGISTRY_PATH)])

    # ---- pair-level decisions -------------------------------------------
    candidate_pairs = {
        pair["pairId"]: pair for pair in pair_inventory["pairs"] if pair.get("candidate")
    }
    unresolved_ids: list[str] = []
    not_established_ids: list[str] = []
    generated_records: dict[str, list[str]] = {pair_id: [] for pair_id in pair_by_id}
    for pair in pair_inventory["pairs"]:
        pair_id = pair["pairId"]
        if pair_records[pair_id]:
            generated_records[pair_id] = list(pair_records[pair_id])
            if any(records_by_id(records, record_id).get("status") == "unresolved"
                   for record_id in pair_records[pair_id]):
                unresolved_ids.append(pair_id)
            if any(records_by_id(records, record_id).get("status") == "notEstablished"
                   for record_id in pair_records[pair_id]):
                not_established_ids.append(pair_id)
            continue
        # No accepted record yet: create either the unresolved candidate or the
        # conservative scoped notEstablished record.
        if pair_id in candidate_pairs:
            record = _candidate_record(
                pair, snapshot, scopes, add_scope, statements, statement_map,
                queries, query_map, add_statement, add_query, add_record, pin_artifact,
                artifact_hash, root, theory_inventory)
            unresolved_ids.append(pair_id)
            generated_records[pair_id] = [record]
            record_pair[record] = pair_id
        else:
            record = _not_established_record(
                pair, pair_by_id, snapshot, scopes, add_scope, statements, statement_map,
                queries, query_map, add_statement, add_query, add_record, pin_artifact,
                artifact_hash, root, theory_inventory, dispositions, fragment_certificate_rows,
                reclassified_rows, inputs["hashes"])
            not_established_ids.append(pair_id)
            generated_records[pair_id] = [record]
            record_pair[record] = pair_id

    # ---- coverage and status checks -------------------------------------
    covered_pairs = {pair for pair, ids in generated_records.items() if ids}
    if covered_pairs != set(pair_by_id):
        missing = sorted(set(pair_by_id) - covered_pairs)
        raise RegistryError([_finding(
            "registry.coverage", f"uncovered pairs after generation: {missing[:8]!r}",
            REGISTRY_PATH)])
    resolved_pairs = {
        pair for pair, ids in generated_records.items()
        if any(records_by_id(records, rid).get("status") == "certified" for rid in ids)
    }
    if set(unresolved_ids) != set(candidate_pairs):
        raise RegistryError([_finding(
            "registry.candidates",
            f"unresolved candidate pairs {sorted(unresolved_ids)!r} differ from the accepted "
            f"candidate set {sorted(candidate_pairs)!r}", REGISTRY_PATH)])
    for pair_id in unresolved_ids:
        for record_id in generated_records[pair_id]:
            record = records_by_id(records, record_id)
            if record.get("status") == "unresolved":
                if "dependencies" in record:
                    raise RegistryError([_finding(
                        "registry.unresolvedDependency",
                        f"unresolved record {record_id!r} carries dependencies", record_id)])
                if record.get("candidate") not in CERTIFIED_KINDS:
                    raise RegistryError([_finding(
                        "registry.unresolvedCandidate",
                        f"unresolved record {record_id!r} has no valid candidate kind", record_id)])
    for pair_id in not_established_ids:
        for record_id in generated_records[pair_id]:
            record = records_by_id(records, record_id)
            if record.get("status") != "notEstablished":
                continue
            _assert_conservative_absence(record)

    # ---- snapshot artifact pinning --------------------------------------
    for statement in statements:
        pin_artifact(statement["artifact"])
        if statement["sha256"] != artifact_hash(statement["artifact"]):
            raise RegistryError([_finding(
                "registry.statementHash",
                f"statement {statement['id']!r} declares a stale artifact hash",
                statement["id"])])
    for certificate in certificates:
        if certificate.get("sourcePath"):
            pin_artifact(certificate["sourcePath"])
    for record in records:
        if record.get("status") == "certified":
            query = query_map[record["queryId"]]
            for role in ("source", "target"):
                statement_id = query[role]
                statement = statement_map[statement_id]
                if snapshot["artifacts"].get(statement["artifact"]) != statement["sha256"]:
                    raise RegistryError([_finding(
                        "registry.snapshotPin",
                        f"statement {statement_id!r} is not pinned by the production snapshot",
                        statement_id)])

    # ---- assemble manifest ----------------------------------------------
    manifest = {
        "$schema": "relation_audit/schema.json",
        "schemaVersion": SCHEMA_VERSION,
        "mode": "full",
        "description": (
            "Production full relation registry for the 136-pair PhotoLean theory "
            "universe. It is generated deterministically from the accepted R1 pilot, "
            "R2 inventory/dispositions, and R3 migration fragments; it covers all 136 "
            "pairs but resolves only the pairs with an accepted certificate. Unresolved "
            "candidates and scoped notEstablished records are explicit; no logical "
            "non-existence or historical-genealogy claim is made."
        ),
        "pairCount": PAIR_COUNT,
        "theoryInventory": theory_inventory,
        "snapshots": [snapshot],
        "scopes": scopes,
        "statements": statements,
        "queries": queries,
        "certificates": certificates,
        "records": records,
    }

    status_counts = {status: 0 for status in AUDIT_STATUSES}
    kind_counts = {kind: 0 for kind in CERTIFIED_KINDS}
    for record in records:
        status = record.get("status")
        if status in status_counts:
            status_counts[status] += 1
        if status == "certified" and record.get("relationKind") in kind_counts:
            kind_counts[record["relationKind"]] += 1

    pair_decisions: list[dict[str, Any]] = []
    for pair in pair_inventory["pairs"]:
        pair_id = pair["pairId"]
        ids = generated_records[pair_id]
        statuses = [records_by_id(records, rid).get("status") for rid in ids]
        primary = "certified" if "certified" in statuses else (
            "unresolved" if "unresolved" in statuses else (
                "notEstablished" if "notEstablished" in statuses else statuses[0]))
        pair_decisions.append({
            "pairId": pair_id,
            "theories": pair["theories"],
            "legacyLabel": pair.get("legacy", {}).get("label"),
            "legacySubtype": pair.get("legacy", {}).get("subtype"),
            "ambiguous": bool(pair.get("ambiguous")),
            "candidate": bool(pair.get("candidate")),
            "status": primary,
            "recordIds": ids,
            "certifiedRecordIds": [
                rid for rid in ids if records_by_id(records, rid).get("status") == "certified"
            ],
            "reclassifiedDeclarationIds": [
                row["declarationId"] for row in reclassified_rows
                if pair_id in row["pairIds"]
            ],
        })

    exceptional_decisions = _exceptional_decisions(
        pair_by_id, generated_records, records, mapping, candidate_pairs,
        reclassified_rows, inputs)

    report = {
        "artifactKind": GENERATED_KIND,
        "schemaVersion": REPORT_SCHEMA_VERSION,
        "scope": "production-full-registry",
        "status": "REGISTRY_GENERATED",
        "sourceOfTruth": {
            "pilot": PILOT_PATH,
            "pairInventory": PAIR_INVENTORY_PATH,
            "relationsInventory": RELATIONS_INVENTORY_PATH,
            "dispositions": DISPOSITIONS_PATH,
            "fragments": list(FRAGMENT_PATHS),
            "relationsSource": RELATIONS_SOURCE,
            "countsSource": COUNTS_SOURCE,
            "acceptedReports": [
                PILOT_REPORT_PATH, INVENTORY_REPORT_PATH, MIGRATION_REPORT_PATH,
            ],
            "note": (
                "Certificates and pair associations are read from the R1 pilot and R3 "
                "fragments; there is no second hand-maintained certificate list."
            ),
        },
        "inputs": dict(sorted(inputs["hashes"].items())),
        "registrySha256": sha256_bytes(
            canonical_json(manifest).encode("utf-8")),
        "counts": {
            "theoryCount": len(theory_inventory),
            "pairUniverse": len(pair_by_id),
            "records": len(records),
            "byStatus": status_counts,
            "certifiedByKind": kind_counts,
            "certificates": len(certificates),
            "acceptedCertificates": len(accepted_certificate_names),
            "pairCertifiedRecords": sum(
                len(item["recordIds"]) for item in mapping if item["outcome"] == "pair-record"
            ),
            "nonPairRecordCertificates": sum(
                1 for item in mapping if item["outcome"] != "pair-record"
            ),
            "nonPairEvidenceCertificates": sum(
                1 for item in mapping if item["outcome"] == "non-pair-evidence"
            ),
            "intraTheoryRecordCertificates": sum(
                1 for item in mapping if item["outcome"] == "intra-theory-record"
            ),
            "compositionParentCertificates": sum(
                1 for item in mapping if item["outcome"] == "composition-parent"
            ),
            "reclassifiedRows": len(reclassified_rows),
            "statements": len(statements),
            "queries": len(queries),
            "scopes": len(scopes),
            "snapshots": 1,
        },
        "coverage": {
            "coveredPairs": len(covered_pairs),
            "missingPairs": [],
            "resolvedPairs": len(resolved_pairs),
            "resolvedCoverage": round(len(resolved_pairs) / PAIR_COUNT, 6),
            "resolvedCoverageComplete": False,
            "unresolvedPairs": sorted(unresolved_ids),
            "unresolvedRecords": status_counts["unresolved"],
            "notEstablishedRecords": status_counts["notEstablished"],
        },
        "certificateMapping": mapping,
        "reclassifiedEvidence": reclassified_rows,
        "pairDecisions": pair_decisions,
        "exceptionalDecisions": exceptional_decisions,
        "nonClaims": [
            "136/136 is registry coverage (every pair has an audit record), not resolved "
            "coverage; resolved coverage is the certified-pair count and is not complete.",
            "No notEstablished record asserts logical non-existence; each one asserts only "
            "that no direct certificate is established in the stated snapshot/scope.",
            "Legacy edge/absence labels are input metadata, not audit judgments, and are not "
            "promoted to certified or notEstablished status automatically.",
            "Kernel-only pins and reclassified rows are not pair certificates and do not "
            "manufacture pair coverage.",
            "The snapshot is dirty by construction (the relation-audit layer is uncommitted); "
            "the full-mode result carries that caveat and needs independent review.",
            "No historical-genealogy, manuscript, or physical-identity claim is made.",
        ],
    }
    return manifest, report


def records_by_id(records: list[dict[str, Any]], record_id: str) -> dict[str, Any]:
    for record in records:
        if record.get("id") == record_id:
            return record
    raise KeyError(record_id)


def _record_pair(record: dict[str, Any], query_map: dict[str, dict[str, Any]],
                 statement_map: dict[str, dict[str, Any]],
                 theory_set: set[str],
                 pair_by_id: dict[str, dict[str, Any]]) -> str | None:
    query = query_map.get(record.get("queryId"))
    if query is None:
        return None
    source = statement_map.get(query.get("source"))
    target = statement_map.get(query.get("target"))
    if source is None or target is None:
        return None
    left = source.get("theory")
    right = target.get("theory")
    if left not in theory_set or right not in theory_set or left == right:
        return None
    for pair in pair_by_id.values():
        if set(pair["theories"]) == {left, right}:
            return pair["pairId"]
    return None


def _strip_photo(theory: str) -> str:
    prefix = "PhotoLean."
    return theory[len(prefix):] if isinstance(theory, str) and theory.startswith(prefix) else theory


def _certificate_from_fragment(entry: dict[str, Any], fragment: dict[str, Any],
                               certificate_id: str, root: str) -> dict[str, Any]:
    statement = entry["statement"]
    kind = entry["relationKind"]
    premise_predicate = statement.get("premisePredicate")
    if not premise_predicate:
        if entry.get("premises"):
            raise RegistryError([_finding(
                "registry.premisePredicate",
                f"{entry['declarationId']!r} has premises but no premise predicate",
                entry["declarationId"])])
        context_type, _ = _context_info(entry)
        premise_predicate = f"fun _ : {context_type} => True"
    semantics: dict[str, Any] = {
        "context": entry.get("sharedContext") or "relation-audit shared context",
        "translations": {
            "left": statement["translations"]["left"],
            "right": statement["translations"]["right"],
        },
        "premisePredicate": premise_predicate,
    }
    if kind == "definitionalIdentity":
        witness = statement.get("definitionalWitness") or {}
        semantics["rflWitness"] = witness.get("functionWitness")
        semantics["rflWitnessAxiomFootprint"] = list(entry.get("axiomFootprint") or [])
        semantics["translation"] = statement["translations"]["left"]
        rfl_check = statement.get("rflCheck")
        if not rfl_check:
            rfl_check = _synthesize_rfl_check(entry)
        semantics["rflCheck"] = {"lhs": rfl_check["lhs"], "rhs": rfl_check["rhs"]}
    elif kind == "observationalEquivalence":
        semantics["channels"] = [
            channel["name"] for channel in statement.get("channels", [])
        ]
    elif kind == "conditionalComposition":
        semantics["translation"] = statement["translations"]["left"]
    certificate = {
        "id": certificate_id,
        "kind": kind,
        "module": entry["leanModule"],
        "lean": entry["certificate"],
        "kindFunction": entry.get("kindFunction") or "PhotoLean.RelationAudit.certificateKind",
        "constructor": entry["certificateConstructor"],
        "premises": [
            {"id": premise["id"], "statement": premise["statement"]}
            for premise in entry.get("premises", [])
        ],
        "semantics": semantics,
        "axiomFootprint": list(entry.get("axiomFootprint") or []),
        "sourcePath": fragment.get("leanSource"),
        "sourceSha256": fragment.get("leanSourceSha256") or sha256_file(
            os.path.join(root, fragment["leanSource"])),
    }
    return certificate


_CONTEXT_RE = re.compile(r"^(?P<name>[A-Za-z_][\w.']*)\s*=\s*\{(?P<fields>.*)\}\s*$")


def _context_info(entry: dict[str, Any]) -> tuple[str, list[str]]:
    shared = (entry.get("sharedContext") or "").strip()
    match = _CONTEXT_RE.match(shared)
    if not match:
        return shared, []
    name = match.group("name")
    if "." not in name:
        name = f"{entry['leanModule']}.{name}"
    fields = [item.split(":", 1)[0].strip() for item in match.group("fields").split(",")]
    return name, [field for field in fields if field]


def _synthesize_rfl_check(entry: dict[str, Any]) -> dict[str, str]:
    """Derive the fresh lambda-level ``rfl`` check for a fragment that omits it.

    Only the identity-translation case is supported.  The accepted R3 fragments
    supply ``rflCheck`` for every definitional row except ``kernel_marcusIC``;
    this adapter is therefore narrow on purpose and fails closed otherwise.
    """
    statement = entry["statement"]
    context_type, fields = _context_info(entry)
    if not fields:
        raise RegistryError([_finding(
            "registry.rflCheck",
            f"{entry['declarationId']!r} has no rflCheck and its context fields cannot be "
            "recovered", entry["declarationId"])])
    translations = statement.get("translations") or {}
    for side in ("left", "right"):
        value = translations.get(side) or ""
        match = re.match(r"^fun\s+(\w+)\s*(?::[^=]+)?=>\s*(\w+)\s*$", value.strip())
        if not match or match.group(1) != match.group(2):
            raise RegistryError([_finding(
                "registry.rflCheck",
                f"{entry['declarationId']!r} has no rflCheck and its {side} translation is "
                "not the identity", entry["declarationId"])])

    def render(term: str) -> str:
        rendered = term
        for theory in _THEORY_NAMES:
            rendered = re.sub(
                r"(?<![\w.])" + re.escape(theory) + r"\.",
                f"PhotoLean.{theory}.",
                rendered,
            )
        for field in fields:
            rendered = re.sub(
                r"(?<![\w.])" + re.escape(field) + r"(?![\w'])",
                f"δ.{field}",
                rendered,
            )
        return f"(fun δ : {context_type} => {rendered})"

    return {"lhs": render(statement["left"]["term"]),
            "rhs": render(statement["right"]["term"])}


_THEORY_NAMES = [
    "Kernel", "Marcus", "Hammond", "BEP", "Kasha", "Sabatier", "Goldschmidt", "SymmetryFactor",
    "KashaVavilov", "SternVolmer", "QuantumYield", "FluorPhos", "EnergyGapLaw",
    "StokesShift", "ICvsISC", "Forster", "Einstein", "RACI",
]


def _fragment_statement(entry: dict[str, Any], side: str, add_statement,
                        statement_map: dict[str, dict[str, Any]],
                        statement_keys: dict[tuple[str, str], str],
                        pin_artifact, artifact_hash) -> str:
    raw = entry["statement"][side]
    theory = _strip_photo(raw["theory"])
    declaration = raw["statementId"]
    artifact, _, locator = raw.get("provenance", "").partition("#")
    if not artifact:
        artifact = entry.get("sourceArtifact") or RELATIONS_SOURCE
    key = (theory, declaration)
    if key in statement_keys:
        return statement_keys[key]
    ident = "stmt-" + slug(f"{theory}-{declaration}")
    if ident in statement_map:
        raise RegistryError([_finding(
            "registry.statementDuplicate",
            f"statement id {ident!r} collides across fragment endpoints", declaration)])
    references = [{"artifact": artifact, "locator": locator or "endpoint declaration"}]
    for reference in (entry.get("statementProvenance") or {}).get("references", []):
        if reference not in references:
            references.append(reference)
    statement = {
        "id": ident,
        "theory": theory,
        "version": "1.0.0",
        "artifact": artifact,
        "sha256": artifact_hash(artifact),
        "context": entry.get("sharedContext") or "relation-audit shared context",
        "declaration": declaration,
        "description": f"Endpoint declaration for accepted R3 row {entry['declarationId']}.",
        "provenance": {"kind": "source", "references": references},
    }
    pin_artifact(artifact)
    add_statement(statement)
    statement_keys[key] = ident
    return ident


def _fragment_provenance(entry: dict[str, Any], fragment: dict[str, Any]) -> dict[str, Any]:
    references: list[dict[str, str]] = []
    for reference in (entry.get("statementProvenance") or {}).get("references", []):
        if reference and reference not in references:
            references.append(reference)
    source_artifact = entry.get("sourceArtifact")
    source_locator = entry.get("sourceLocator")
    if source_artifact:
        candidate = {"artifact": source_artifact, "locator": source_locator or "row"}
        if candidate not in references:
            references.append(candidate)
    candidate = {"artifact": fragment["leanSource"], "locator": entry["certificate"]}
    if candidate not in references:
        references.append(candidate)
    if not references:
        references = [{"artifact": RELATIONS_SOURCE, "locator": entry["declarationId"]}]
    return {
        "kind": "source",
        "references": references,
        "note": f"Accepted R3 migration row {entry['declarationId']}.",
    }


def _theory_artifact(root: str, theory: str) -> str:
    base = os.path.join(root, "PhotoLean", theory)
    for name in ("Basic.lean", "Main.lean"):
        candidate = os.path.join(base, name)
        if os.path.isfile(candidate):
            return f"PhotoLean/{theory}/{name}"
    candidates = sorted(
        f"PhotoLean/{theory}/{item}"
        for item in os.listdir(base)
        if item.endswith(".lean")
    ) if os.path.isdir(base) else []
    if not candidates:
        raise RegistryError([_finding(
            "registry.theoryArtifact", f"theory {theory!r} has no Lean module", theory)])
    return candidates[0]


def _theory_anchor(theory: str, snapshot_id: str, tree_sha: str, root: str,
                   add_statement, statement_map, pin_artifact, artifact_hash) -> str:
    ident = "stmt-theory-" + slug(theory)
    if ident in statement_map:
        return ident
    artifact = _theory_artifact(root, theory)
    statement = {
        "id": ident,
        "theory": theory,
        "version": "1.0.0",
        "artifact": artifact,
        "sha256": artifact_hash(artifact),
        "context": f"theory-level comparison anchor at snapshot {tree_sha[:12]}",
        "description": (
            "Theory-level anchor used only for pair-scoped absence/candidate records; it "
            "does not assert a single declaration."
        ),
        "provenance": {
            "kind": "source",
            "references": [
                {"artifact": artifact, "locator": "theory module surface"},
                {"artifact": COUNTS_SOURCE, "locator": "THEORIES"},
            ],
        },
    }
    pin_artifact(artifact)
    return add_statement(statement)


def _pair_query(pair: dict[str, Any], snapshot_id: str, tree_sha: str, root: str,
                add_statement, statement_map, add_query, query_map,
                pin_artifact, artifact_hash) -> tuple[str, str, str]:
    left, right = pair["theories"]
    left_id = _theory_anchor(left, snapshot_id, tree_sha, root, add_statement,
                             statement_map, pin_artifact, artifact_hash)
    right_id = _theory_anchor(right, snapshot_id, tree_sha, root, add_statement,
                              statement_map, pin_artifact, artifact_hash)
    query_id = "q-pair-" + pair["pairId"]
    if query_id in query_map:
        return query_id, left_id, right_id
    query = {
        "id": query_id,
        "source": left_id,
        "target": right_id,
        "context": (
            f"pair-scoped comparison anchor for {left}/{right} at snapshot {tree_sha[:12]}"
        ),
        "provenance": {
            "kind": "source",
            "references": [
                {"artifact": PAIR_INVENTORY_PATH, "locator": pair["pairId"]},
                {"artifact": RELATIONS_SOURCE,
                 "locator": (pair.get("legacy", {}) or {}).get(
                     "citation", "legacy pair census")},
            ],
        },
        "question": (
            "Is a direct certified relation registered for this pair in the stated "
            "snapshot/scope?"
        ),
    }
    add_query(query)
    return query_id, left_id, right_id


def _candidate_record(pair: dict[str, Any], snapshot: dict[str, Any], scopes: list,
                      add_scope, statements: list, statement_map, queries: list,
                      query_map, add_statement, add_query, add_record, pin_artifact,
                      artifact_hash, root: str, theory_inventory: list[str]) -> str:
    query_id, left_id, right_id = _pair_query(
        pair, snapshot["id"], snapshot["treeSha"], root, add_statement, statement_map,
        add_query, query_map, pin_artifact, artifact_hash)
    candidate = pair.get("candidate") or {}
    reason = candidate.get("reason") or "undelivered candidate relation"
    kind = "conditionalComposition" if "composition" in reason.lower() else "implication"
    rationale = (
        f"Undelivered candidate relation for pair {pair['pairId']} "
        f"({pair['theories'][0]}/{pair['theories'][1]}): {reason} No certificate exists in "
        "the accepted R1/R3 evidence, so the candidate remains unresolved. This is not a "
        "negative result and not a claim of logical non-existence."
    )
    provenance = {
        "kind": "manual",
        "references": [
            {"artifact": PAIR_INVENTORY_PATH, "locator": f"{pair['pairId']} candidate"},
            {"artifact": RELATIONS_SOURCE,
             "locator": (pair.get("legacy", {}) or {}).get("citation", "legacy pair census")},
        ],
        "rationale": rationale,
    }
    record = {
        "id": "rec-candidate-" + slug(pair["pairId"]),
        "queryId": query_id,
        "statementVersion": f"{left_id}@1.0.0|{right_id}@1.0.0",
        "scope": "global",
        "snapshot": snapshot["id"],
        "status": "unresolved",
        "candidate": kind,
        "rationale": rationale,
        "provenance": provenance,
    }
    add_record(record)
    return record["id"]


def _not_established_record(pair: dict[str, Any], pair_by_id: dict[str, Any],
                            snapshot: dict[str, Any], scopes: list, add_scope,
                            statements: list, statement_map, queries: list, query_map,
                            add_statement, add_query, add_record, pin_artifact,
                            artifact_hash, root: str, theory_inventory: list[str],
                            dispositions: dict[str, Any],
                            fragment_certificate_rows: list[dict[str, Any]],
                            reclassified_rows: list[dict[str, Any]],
                            hashes: dict[str, str]) -> str:
    left, right = pair["theories"]
    pair_id = pair["pairId"]
    scope_id = "scope-" + slug(pair_id)
    if scope_id not in {item["id"] for item in scopes}:
        add_scope({
            "id": scope_id,
            "kind": "restricted",
            "dimension": "relation",
            "description": (
                f"Pair-scoped snapshot audit scope for {left}/{right}; it covers only this "
                "unordered pair."
            ),
            "boundary": (
                "The record asserts only that no direct certificate is established in the "
                "stated snapshot under this pair-restricted relation scope. It is not a "
                "logical non-existence or historical-genealogy claim."
            ),
            "theories": [left, right],
            "provenance": {
                "kind": "source",
                "references": [
                    {"artifact": PAIR_INVENTORY_PATH, "locator": pair_id},
                    {"artifact": DISPOSITIONS_PATH, "locator": "entries for this pair"},
                ],
            },
        })
    query_id, left_id, right_id = _pair_query(
        pair, snapshot["id"], snapshot["treeSha"], root, add_statement, statement_map,
        add_query, query_map, pin_artifact, artifact_hash)

    legacy = pair.get("legacy", {}) or {}
    legacy_label = legacy.get("label")
    legacy_note = (
        f"The legacy census labels this pair {legacy_label!r} "
        f"({legacy.get('subtype')!r}); that label is metadata only and is not an audit "
        "judgment."
    )
    pair_reclassified = [
        row for row in reclassified_rows if pair_id in row["pairIds"]
    ]
    reclassified_note = ""
    if pair_reclassified:
        rendered = ", ".join(
            f"{row['declarationId']} ({row['targetCategory']})" for row in pair_reclassified
        )
        reclassified_note = (
            " Accepted R3 rows for this pair were reclassified as non-certificate evidence: "
            f"{rendered}; they were not promoted to certified relations."
        )
    ambiguity_note = ""
    if pair.get("ambiguous"):
        ambiguity = pair["ambiguous"]
        ambiguity_note = (
            " The census flags an edge/absence ambiguity for this pair "
            f"(absence reading: {ambiguity.get('absenceReading')!r}; edge reading: "
            f"{ambiguity.get('edgeReading')!r}); both readings are preserved and this "
            "record does not resolve the ambiguity."
        )
    rationale = (
        f"Scoped snapshot absence for pair {pair_id} ({left}/{right}): no direct "
        "cross-theory certificate is registered in the accepted R1/R3 evidence at this "
        f"snapshot ({snapshot['treeSha'][:12]}) under the pair-restricted relation scope. "
        f"{legacy_note}{reclassified_note}{ambiguity_note} This record asserts only the "
        "absence of a delivered direct certificate in the stated snapshot/scope; it is "
        f"{NON_EXISTENCE_PHRASE}."
    )
    dependency_recompute = f"python3 tools/relation_audit_registry.py --explain-pair {pair_id}"
    dependencies = [
        {
            "kind": "sourceScan",
            "reference": DISPOSITIONS_PATH,
            "recompute": dependency_recompute,
            "sha256": hashes.get(DISPOSITIONS_PATH, ""),
            "summary": (
                "Recomputes the pair's disposition and fragment mapping from the accepted "
                "ledger; no certified record is selected for this pair."
            ),
        },
        {
            "kind": "census",
            "reference": COUNTS_SOURCE,
            "recompute": "python3 tools/counts.py --no-lean",
            "sha256": hashes.get(COUNTS_SOURCE, ""),
            "summary": (
                "Recomputes the legacy 136-pair census; the pair is present, but census "
                "completeness is not an audit certificate."
            ),
        },
    ]
    provenance = {
        "kind": "manual",
        "references": [
            {"artifact": PAIR_INVENTORY_PATH, "locator": pair_id},
            {"artifact": RELATIONS_SOURCE,
             "locator": legacy.get("citation", "legacy pair census")},
            {"artifact": DISPOSITIONS_PATH, "locator": "entries for this pair"},
        ],
        "rationale": rationale,
    }
    record = {
        "id": "rec-notestablished-" + slug(pair_id),
        "queryId": query_id,
        "statementVersion": f"{left_id}@1.0.0|{right_id}@1.0.0",
        "scope": scope_id,
        "snapshot": snapshot["id"],
        "status": "notEstablished",
        "rationale": rationale,
        "dependencies": dependencies,
        "provenance": provenance,
    }
    add_record(record)
    return record["id"]


def _assert_conservative_absence(record: dict[str, Any]) -> None:
    rationale = record.get("rationale") or ""
    if not any(phrase in rationale for phrase in CONSERVATIVE_ABSENCE_PHRASES):
        raise RegistryError([_finding(
            "registry.conservativeAbsence",
            f"notEstablished record {record.get('id')!r} does not state the non-existence "
            "non-claim", record.get("id"))])
    dependencies = record.get("dependencies")
    if not isinstance(dependencies, list) or not dependencies:
        raise RegistryError([_finding(
            "registry.dependencyMissing",
            f"notEstablished record {record.get('id')!r} has no dependencies",
            record.get("id"))])
    for dependency in dependencies:
        if dependency.get("kind") not in ("sourceScan", "census", "search"):
            raise RegistryError([_finding(
                "registry.dependencyKind",
                f"notEstablished record {record.get('id')!r} has dependency kind "
                f"{dependency.get('kind')!r}; Lean probes would masquerade as negative "
                "theorem evidence", record.get("id"))])
        if not dependency.get("recompute") or not dependency.get("reference"):
            raise RegistryError([_finding(
                "registry.dependencyShape",
                f"notEstablished record {record.get('id')!r} has an incomplete dependency",
                record.get("id"))])


def _exceptional_decisions(pair_by_id: dict[str, Any],
                           generated_records: dict[str, list[str]],
                           records: list[dict[str, Any]],
                           mapping: list[dict[str, Any]],
                           candidate_pairs: dict[str, Any],
                           reclassified_rows: list[dict[str, Any]],
                           inputs: dict[str, Any]) -> list[dict[str, Any]]:
    decisions: list[dict[str, Any]] = []
    for pair_id, pair in pair_by_id.items():
        if pair.get("ambiguous"):
            decisions.append({
                "pairId": pair_id,
                "kind": "census-ambiguity",
                "decision": "preserved as notEstablished; both readings recorded; no direct "
                            "certificate and no resolution of the ambiguity",
            })
    for row in mapping:
        if row["outcome"] == "non-pair-evidence":
            decisions.append({
                "pairId": (row.get("pairIds") or [None])[0],
                "kind": "non-pair-certificate",
                "declarationId": row.get("declarationId"),
                "certificate": row.get("certificate"),
                "decision": row.get("reason"),
            })
    for pair_id in sorted(candidate_pairs):
        decisions.append({
            "pairId": pair_id,
            "kind": "undelivered-candidate",
            "decision": "represented as unresolved; no dependencies and no negative claim",
        })
    decisions.append({
        "pairId": "P-Goldschmidt-Marcus",
        "kind": "reused-pilot-absence",
        "decision": "reuses the accepted R1 scoped notEstablished record instead of "
                    "duplicating it",
    })
    for row in reclassified_rows:
        decisions.append({
            "pairId": (row["pairIds"] or [None])[0],
            "kind": "reclassified-non-certificate",
            "declarationId": row["declarationId"],
            "targetCategory": row["targetCategory"],
            "decision": "retained as non-certificate evidence; not promoted",
        })
    return decisions


# --------------------------------------------------------------------------- checking
def check_registry(inputs: dict[str, Any], registry: dict[str, Any],
                   report: dict[str, Any]) -> list[Finding]:
    """Compare a checked-in registry/report against a fresh derivation."""
    findings: list[Finding] = []
    if report.get("artifactKind") != GENERATED_KIND:
        findings.append(_finding(
            "registry.reportKind", "registry report has the wrong artifactKind", REPORT_PATH))
        return findings
    findings.extend(validate_accepted_inputs(inputs))
    for relative, expected in (report.get("inputs") or {}).items():
        actual = inputs["hashes"].get(relative)
        if actual is None:
            findings.append(_finding(
                "input.missing", f"input {relative!r} is missing", relative))
        elif actual != expected:
            findings.append(_finding(
                "input.drift",
                f"input {relative!r} hash {actual!r} drifted from the pinned {expected!r}",
                relative))
    try:
        generated, generated_report = _build(inputs)
    except RegistryError as exc:
        return findings + exc.findings
    expected_registry = canonical_json(generated)
    actual_registry = canonical_json(registry)
    if expected_registry != actual_registry:
        findings.append(_finding(
            "registry.drift",
            "checked-in registry.json is not byte-identical to the deterministic "
            "regeneration", REGISTRY_PATH))
    if report.get("registrySha256") != generated_report.get("registrySha256"):
        findings.append(_finding(
            "registry.reportHash",
            "registry report does not pin the regenerated registry hash", REPORT_PATH))
    expected_report = canonical_json(generated_report)
    actual_report = canonical_json(report)
    if expected_report != actual_report:
        findings.append(_finding(
            "registry.reportDrift",
            "checked-in registry-report.json is not byte-identical to the deterministic "
            "regeneration", REPORT_PATH))
    return findings


def render_report_markdown(report: dict[str, Any]) -> str:
    counts = report["counts"]
    coverage = report["coverage"]
    lines = [
        "# Production 136-Pair Relation Registry",
        "",
        "Generated by `tools/relation_audit_registry.py --generate`; do not edit by hand.",
        "",
        "## Coverage",
        "",
        f"- theory inventory: {counts['theoryCount']}/17",
        f"- pair universe: {counts['pairUniverse']}/136",
        f"- registry coverage: {coverage['coveredPairs']}/136 pairs",
        f"- resolved coverage: {coverage['resolvedPairs']}/136 pairs "
        f"(complete={str(coverage['resolvedCoverageComplete']).lower()})",
        f"- unresolved candidate records: {coverage['unresolvedRecords']}",
        f"- scoped notEstablished records: {coverage['notEstablishedRecords']}",
        "",
        "## Records",
        "",
        "| status | records |",
        "|---|---|",
    ]
    for status in AUDIT_STATUSES:
        lines.append(f"| `{status}` | {counts['byStatus'].get(status, 0)} |")
    lines.extend(["", "## Certified kinds", "", "| kind | records |", "|---|---|"])
    for kind in CERTIFIED_KINDS:
        lines.append(f"| `{kind}` | {counts['certifiedByKind'].get(kind, 0)} |")
    lines.extend([
        "",
        "## Unresolved candidates",
        "",
    ])
    for pair_id in coverage["unresolvedPairs"]:
        lines.append(f"- `{pair_id}`")
    lines.extend([
        "",
        "## Explicit non-claims",
        "",
    ])
    for item in report["nonClaims"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def render_validator_report(report: dict[str, Any]) -> str:
    """Human-readable summary of the real full-validator JSON report."""
    coverage = report.get("coverage", {})
    counts = report.get("counts", {})
    lines = [
        "# Production Full Validator Report",
        "",
        f"- status: `{report.get('status')}` (exit {report.get('exitCode')})",
        f"- mode: `{report.get('mode')}`",
        f"- manifest: `{report.get('manifest')}`",
        f"- schema: `{report.get('schema')}`",
        "",
        "## Gates",
        "",
        "| gate | status | findings |",
        "|---|---|---|",
    ]
    for name, gate in (report.get("gates") or {}).items():
        lines.append(f"| `{name}` | {gate.get('status')} | {len(gate.get('findings', []))} |")
    lines.extend([
        "",
        "## Coverage",
        "",
        f"- theories: {coverage.get('theoryCount')}/{coverage.get('expectedTheoryCount')}",
        f"- registry: {coverage.get('coveredPairs')}/{coverage.get('expectedPairUniverse')} pairs",
        f"- resolved: {coverage.get('resolvedPairs')}/{coverage.get('expectedPairUniverse')} "
        f"pairs (complete={str(coverage.get('resolvedCoverageComplete')).lower()})",
        f"- unresolved records: {coverage.get('unresolvedRecords')}",
        "",
        "## Counts",
        "",
        f"- records: {counts.get('records')}",
        f"- by status: `{counts.get('byStatus')}`",
        f"- certified by kind: `{counts.get('certifiedByKind')}`",
        f"- certificates: {counts.get('certificates')}",
        "",
        "## Caveats",
        "",
    ])
    for caveat in report.get("caveats", []):
        lines.append(f"- `{caveat.get('code')}`: {caveat.get('message')}")
    lines.append("")
    return "\n".join(lines)


# ------------------------------------------------------------------------------- CLI
def main(argv: list[str] | None = None) -> int:
    import argparse
    import sys

    default_root = _repo_root_from(os.path.dirname(os.path.abspath(__file__)))
    parser = argparse.ArgumentParser(
        prog="relation_audit_registry.py",
        description="Deterministic generator/checker for the production 136-pair registry.",
    )
    parser.add_argument("--root", default=default_root,
                        help="repository root (default: the checkout containing this tool)")
    parser.add_argument("--registry", default=None,
                        help=f"registry path (default: {REGISTRY_PATH})")
    parser.add_argument("--report", default=None,
                        help=f"machine-readable report path (default: {REPORT_PATH})")
    parser.add_argument("--markdown", default=None,
                        help=f"human-readable report path (default: {REPORT_MD_PATH})")
    parser.add_argument("--generate", action="store_true",
                        help="write the registry and report")
    parser.add_argument("--check", action="store_true",
                        help="re-derive and compare the checked-in registry and report")
    parser.add_argument("--explain-pair", default=None, metavar="PAIR_ID",
                        help="print the accepted inputs and registry decision for one pair")
    parser.add_argument("--render-validator-report", nargs=2, metavar=("JSON", "MD"),
                        help="render a real validator JSON report as markdown")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args(argv)

    if args.render_validator_report:
        source, destination = args.render_validator_report
        try:
            with open(source, encoding="utf-8") as handle:
                report = json.load(handle)
        except (OSError, json.JSONDecodeError) as exc:
            print(f"ERROR: cannot read validator report {source}: {exc}", file=sys.stderr)
            return 2
        with open(destination, "w", encoding="utf-8") as handle:
            handle.write(render_validator_report(report))
        if not args.quiet:
            print(f"wrote {destination}")
        return 0

    if not args.generate and not args.check and not args.explain_pair:
        parser.error("one of --generate, --check, or --explain-pair is required")

    root = os.path.abspath(args.root)
    try:
        inputs = load_inputs(root)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"ERROR: cannot load accepted inputs: {exc}", file=sys.stderr)
        return 2

    if args.explain_pair:
        return _explain_pair(inputs, args.explain_pair, args.registry, root)

    registry_path = os.path.join(root, args.registry or REGISTRY_PATH)
    report_path = os.path.join(root, args.report or REPORT_PATH)
    markdown_path = os.path.join(root, args.markdown or REPORT_MD_PATH)

    if args.generate:
        try:
            registry, report = build_registry(inputs)
        except RegistryError as exc:
            for finding in exc.findings:
                print(f"ERROR: {finding}", file=sys.stderr)
            return 1
        os.makedirs(os.path.dirname(registry_path), exist_ok=True)
        os.makedirs(os.path.dirname(report_path), exist_ok=True)
        with open(registry_path, "w", encoding="utf-8") as handle:
            handle.write(canonical_json(registry))
        with open(report_path, "w", encoding="utf-8") as handle:
            handle.write(canonical_json(report))
        with open(markdown_path, "w", encoding="utf-8") as handle:
            handle.write(render_report_markdown(report))
        if not args.quiet:
            counts = report["counts"]
            coverage = report["coverage"]
            print(
                "registry: OK "
                f"({counts['records']} records, "
                f"{coverage['coveredPairs']}/136 pairs covered, "
                f"{coverage['resolvedPairs']}/136 resolved, "
                f"{counts['certificates']} certificates)"
            )
            print(f"wrote {registry_path}")
            print(f"wrote {report_path}")
            print(f"wrote {markdown_path}")
        return 0

    # --check
    try:
        with open(registry_path, encoding="utf-8") as handle:
            registry = json.load(handle)
        with open(report_path, encoding="utf-8") as handle:
            report = json.load(handle)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"ERROR: cannot read checked-in registry/report: {exc}", file=sys.stderr)
        return 2
    findings = check_registry(inputs, registry, report)
    if findings:
        for finding in findings:
            print(f"FAIL: {finding}", file=sys.stderr)
        return 1
    if not args.quiet:
        print(
            "registry check: OK "
            f"({report['counts']['records']} records, "
            f"{report['coverage']['coveredPairs']}/136 pairs covered, "
            f"{report['coverage']['resolvedPairs']}/136 resolved; "
            "deterministic regeneration is byte-identical)"
        )
    return 0


def _repo_root_from(start: str) -> str:
    current = os.path.abspath(start)
    while True:
        if os.path.isfile(os.path.join(current, "proofs", "ENGINE.yml")):
            return current
        parent = os.path.dirname(current)
        if parent == current:
            return os.path.abspath(start)
        current = parent


def _explain_pair(inputs: dict[str, Any], pair_id: str, registry_override: str | None,
                  root: str) -> int:
    pair_inventory = inputs["pair_inventory"]
    pair = next(
        (item for item in pair_inventory.get("pairs", []) if item.get("pairId") == pair_id),
        None,
    )
    if pair is None:
        print(f"ERROR: unknown pair {pair_id!r}", file=sys.stderr)
        return 1
    print(f"pair: {pair_id}")
    print(f"theories: {pair.get('theories')}")
    print(f"legacy: label={pair.get('legacy', {}).get('label')!r} "
          f"subtype={pair.get('legacy', {}).get('subtype')!r}")
    print(f"candidate: {bool(pair.get('candidate'))}")
    print(f"ambiguous: {bool(pair.get('ambiguous'))}")
    print("dispositions:")
    found = False
    for entry in inputs["dispositions"].get("entries", []):
        if pair_id in (entry.get("pairIds") or []) or pair_id in (entry.get("relatedPairIds") or []):
            found = True
            print(f"  {entry['declarationId']}: disposition={entry['disposition']!r} "
                  f"role={entry['relationRole']!r} outcome=fragment")
        elif pair_id in (entry.get("pairIds") or []):
            found = True
    if not found:
        print("  (none; the pair is not named by the 78-row disposition ledger)")
    print("fragments:")
    found_fragment = False
    for fragment, relative in zip(inputs["fragments"], inputs["fragment_paths"]):
        for entry in fragment.get("entries", []):
            if pair_id in (entry.get("pairIds") or []):
                found_fragment = True
                print(f"  {entry['declarationId']}: outcome={entry.get('outcome')!r} "
                      f"kind={entry.get('relationKind')!r} certificate={entry.get('certificate')!r}")
    if not found_fragment:
        print("  (none)")
    registry_path = os.path.join(root, registry_override or REGISTRY_PATH)
    if os.path.isfile(registry_path):
        try:
            with open(registry_path, encoding="utf-8") as handle:
                registry = json.load(handle)
        except (OSError, json.JSONDecodeError):
            registry = {}
        statement_map = {item["id"]: item for item in registry.get("statements", [])}
        query_map = {item["id"]: item for item in registry.get("queries", [])}
        print("registry records:")
        for record in registry.get("records", []):
            query = query_map.get(record.get("queryId"), {})
            source = statement_map.get(query.get("source"), {})
            target = statement_map.get(query.get("target"), {})
            if {source.get("theory"), target.get("theory")} == set(pair.get("theories") or []):
                print(f"  {record['id']}: status={record.get('status')!r} "
                      f"kind={record.get('relationKind')!r} "
                      f"certificate={record.get('certificate')!r}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
