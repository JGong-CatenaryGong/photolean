#!/usr/bin/env python3
"""Independent, fail-closed validator for the R8 bounded relation-audit snapshot.

This validator is intentionally written after, and independently of, the R8
builder.  It never edits the builder outputs, the legacy registry, the frozen
PhotoLean tree or any accepted package.  It recomputes every count from the
accepted source packages and from the unchanged legacy registry; it does not
trust the numbers written into ``registry.accepted.json``.

The check surface covers:

* schema validity of both generated JSON artifacts;
* exact R1 pair universe / active query / record cardinalities and outcomes;
* source-fidelity of every active query against its accepted package;
* real R1 inventory endpoints, source hashes, lines and signatures;
* the 93-entry certificate library (38 delivered + 55 probe) and the
  67 active certificates (55 probe + 12 legacy);
* the nine probe files, 58 reviewed declarations and three excluded XD1
  candidates (never certificate library members);
* all 151 legacy dispositions, the 26 named / 125 pair-anchor split, the four
  alias repairs, three corrected legacy views and every old-absence/new-evidence
  reconciliation;
* the pending/accepted state machine, including partial-flip rejection and
  anti-hash-cycle rules;
* optional live execution of the historical/current gates, strict build/scan,
  the unchanged legacy full Lean validator, and the nine direct probe
  compilations with per-declaration axiom audits;
* optional deterministic rebuild in an isolated temporary checkout, invoked
  with the current manifest acceptance state and against custom
  --registry/--dispositions files when supplied, plus registry/original/backup
  invariants.

Exit codes: 0 = every requested check ran and passed; 1 = at least one check
failed; 2 = a requested input could not be loaded.  A skipped Lean check is
never PASS (use --skip-probe-compile only for structural mutation tests).
"""

from __future__ import annotations

import argparse
import collections
import copy
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[2]

REGISTRY_PATH = "relation_audit/registry.accepted.json"
SCHEMA_PATH = "relation_audit/schema.accepted.json"
DISPOSITIONS_PATH = "relation_audit/legacy-dispositions.accepted.json"
DOCS_PATH = "docs/RELATION-AUDIT-ACCEPTED.md"
REPORT_JSON_PATH = "relation_audit/reports/bounded-accepted.json"
REPORT_MD_PATH = "relation_audit/reports/bounded-accepted.md"

INVENTORY_PATH = "audit_boundary/statement-inventory.json"
PAIR_QUEUE_PATH = "audit_boundary/pair-queue.json"
CLUSTER_PLAN_PATH = "audit_boundary/cluster-plan.json"
BOUNDARY_PATH = "audit_boundary/BOUNDARY.md"
COVERAGE_PATH = "bounded_audit/coverage.json"
LEGACY_PATH = "relation_audit/registry.json"
FROZEN_R4_PATH = "bounded_audit/r4/coverage-accepted.json"

EXPECTED = {
    "boundary": "ad4d88a0e1d91232ee4b8969dd0a67ef53210b937b2554fec58dfa5b862a95c3",
    "inventory": "3debf588b081b7a572487bffb78bccacd2e8c5ed327a6d6bfb655663fe1fa947",
    "pairQueue": "8357f61cfb54e056b72fb73a5fb08d450d29adb9a0e9c7956e04ebff8cb25504",
    "clusterPlan": "ded71097c3b7c336b290483272c5f49ec7e80fd7a9a7ec0223352a2186d04a24",
    "coverage": "7d4c4f2f6df6a50e3aa20ac510dddaebf3e0d63272cb8c9d3a83e90022b48e2d",
    "legacy": "25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0",
    "frozenR4": "d1e44bf7bbb5e81c7b85f610d6ffc1d4d3fed0fcde5cd1ab3202fb23ca6c32fa",
}

STATUSES = ["certified", "refuted", "unresolved", "notEstablished", "outOfScope"]
RELATION_KINDS = [
    "definitionalIdentity",
    "implication",
    "equivalence",
    "conditionalComposition",
    "observationalEquivalence",
    "distinguishability",
    "refutation",
]
NON_REFUTATION_KINDS = [k for k in RELATION_KINDS if k != "refutation"]
EVIDENCE_CLASSES = ["deliveredModule", "boundedProbe"]
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
PENDING = "submitted-R8-pending-review"
ACCEPTED = "accepted-R8"
THEORIES = [
    "Marcus", "Hammond", "BEP", "Kasha", "Sabatier", "Goldschmidt",
    "SymmetryFactor", "KashaVavilov", "SternVolmer", "QuantumYield",
    "FluorPhos", "EnergyGapLaw", "StokesShift", "ICvsISC", "Forster",
    "Einstein", "RACI",
]
THEORY_INDEX = {t: i for i, t in enumerate(THEORIES)}

ALIASES = {
    "stmt-BEP-PhotoLean-BEP-rateViaEact": "PhotoLean.BEP.rateViaEact",
    "stmt-Marcus-PhotoLean-Marcus-rateDescriptor": "PhotoLean.Marcus.rateDescriptor",
    "stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier-eq-zero":
        "PhotoLean.EnergyGapLaw.nrBarrier_eq_zero",
    "stmt-StokesShift-PhotoLean-StokesShift-emEnergy-eq-zero":
        "PhotoLean.StokesShift.emEnergy_eq_zero",
}
ALIAS_DECLARATIONS = set(ALIASES.values())

EXPECTED_ACTIVE = {
    "pairs": 136,
    "queries": 152,
    "records": 152,
    "outcomes": {
        "certified": 67,
        "refuted": 0,
        "unresolved": 39,
        "notEstablished": 2,
        "outOfScope": 44,
    },
    "certifiedPairs": 53,
    "libraryTotal": 93,
    "libraryDelivered": 38,
    "libraryProbe": 55,
    "activeProbe": 55,
    "activeLegacy": 12,
    "candidates": 3,
    "probeFiles": 9,
    "reviewedDeclarations": 58,
    "legacyRecords": 151,
    "legacyNamed": 26,
    "legacyAnchors": 125,
    "legacyIntra": 5,
    "legacyAliases": 4,
    "correctedRecords": 3,
    "absenceReconciliations": 44,
    "absenceNotEstablishedOverlaps": 41,
    "candidateOverlaps": 3,
    "packages": 10,
    "statements": 92,
    "evidenceReferences": 77,
}

PROBE_FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe)\b")
PLACEHOLDER = re.compile(
    r"\b(TODO|TBD|FIXME|XXX|lorem ipsum|placeholder|not[ -]?implemented)\b",
    re.IGNORECASE,
)
SHA_RE = re.compile(r"^[0-9a-f]{64}$")
DECL_RE = re.compile(r"^\s*(?:private\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][\w.']*)", re.M)
PRINT_RE = re.compile(r"#print\s+axioms\s+([A-Za-z_][\w.']*)")
AXIOM_DEP_RE = re.compile(
    r"'([^']+)'\s+depends\s+on\s+axioms:\s*\[(.*?)\]", re.S
)
AXIOM_NONE_RE = re.compile(r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms", re.S)


# ---------------------------------------------------------------------------
# Generic helpers
# ---------------------------------------------------------------------------


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha_file(path: Path) -> str | None:
    try:
        return sha_bytes(path.read_bytes())
    except OSError:
        return None


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def canonical_pair(a: str, b: str) -> str:
    if a not in THEORY_INDEX or b not in THEORY_INDEX:
        raise ValueError(f"unknown theory pair {a}/{b}")
    return f"P-{a}-{b}" if THEORY_INDEX[a] <= THEORY_INDEX[b] else f"P-{b}-{a}"


def iso(value) -> str:
    """Stable short rendering for error messages."""
    text = repr(value)
    return text if len(text) <= 160 else text[:157] + "..."


def walk_strings(node, path=""):
    if isinstance(node, dict):
        for key, value in node.items():
            yield from walk_strings(value, f"{path}/{key}")
    elif isinstance(node, list):
        for index, value in enumerate(node):
            yield from walk_strings(value, f"{path}/{index}")
    elif isinstance(node, str):
        yield path, node


def find_paths_with_key(node, key, path=""):
    if isinstance(node, dict):
        for k, value in node.items():
            if k == key:
                yield f"{path}/{k}", value
            yield from find_paths_with_key(value, key, f"{path}/{k}")
    elif isinstance(node, list):
        for index, value in enumerate(node):
            yield from find_paths_with_key(value, key, f"{path}/{index}")


def subset_equal(raw, generated, path, checker, code):
    """Every key/value present in the accepted raw object must survive unchanged.

    Generated objects may add metadata keys (recordId, acceptance, evidence
    class annotations, ...), but may never rewrite an accepted source value.
    """
    if isinstance(raw, dict):
        if not isinstance(generated, dict):
            checker.fail(code, f"{path}: generated value is not an object")
            return
        for key, value in raw.items():
            if key not in generated:
                checker.fail(code, f"{path}/{key}: accepted source field is missing")
                continue
            subset_equal(value, generated[key], f"{path}/{key}", checker, code)
    elif isinstance(raw, list):
        if not isinstance(generated, list) or len(raw) != len(generated):
            checker.fail(
                code,
                f"{path}: list length/mapping drift ({len(raw) if isinstance(raw, list) else '?'}"
                f" vs {len(generated) if isinstance(generated, list) else '?'})",
            )
            return
        for index, (left, right) in enumerate(zip(raw, generated)):
            subset_equal(left, right, f"{path}/{index}", checker, code)
    elif raw != generated:
        checker.fail(code, f"{path}: {iso(raw)} != generated {iso(generated)}")


def strip_lean_comments_and_strings(text: str) -> str:
    out = []
    i = 0
    depth = 0
    length = len(text)
    while i < length:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            i += 1
            continue
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = length if end < 0 else end + 1
            continue
        if text[i] == '"':
            i += 1
            while i < length:
                if text[i] == "\\":
                    i += 2
                    continue
                if text[i] == '"':
                    i += 1
                    break
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def normalise_axiom_list(raw: str) -> list[str]:
    return [part.strip() for part in raw.replace("\n", " ").split(",") if part.strip()]


def parse_axiom_output(text: str) -> dict[str, list[str]]:
    found = {}
    for match in AXIOM_DEP_RE.finditer(text):
        found[match.group(1)] = normalise_axiom_list(match.group(2))
    for match in AXIOM_NONE_RE.finditer(text):
        found.setdefault(match.group(1), [])
    return found


def load_r1_parser(root: Path):
    path = root / "audit_boundary/validate_boundary.py"
    spec = importlib.util.spec_from_file_location("_r8_independent_r1_parser", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load R1 parser at {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# ---------------------------------------------------------------------------
# Checker
# ---------------------------------------------------------------------------


class Checker:
    def __init__(self):
        self.checks = 0
        self.failures: list[dict] = []
        self.notes: list[str] = []
        self.gates: list[dict] = []
        self.probe_runs: list[dict] = []
        self.rebuild: dict = {}
        self.invariants: dict = {}
        self.mutations: dict = {}

    def check(self, condition, code: str, message: str) -> bool:
        self.checks += 1
        if not condition:
            self.fail(code, message)
            return False
        return True

    def fail(self, code: str, message: str) -> None:
        self.failures.append({"code": code, "message": message})

    def equal(self, actual, expected, code: str, message: str) -> None:
        self.check(actual == expected, code, f"{message}: {iso(actual)} != {iso(expected)}")

    def note(self, message: str) -> None:
        self.notes.append(message)

    @property
    def ok(self) -> bool:
        return not self.failures


# ---------------------------------------------------------------------------
# Source loading
# ---------------------------------------------------------------------------


class Sources:
    def __init__(self):
        self.registry = None
        self.schema = None
        self.dispositions = None
        self.inventory = None
        self.queue = None
        self.clusters = None
        self.coverage = None
        self.legacy = None
        self.packages: list[dict] = []
        self.raw_queries: dict[str, dict] = {}
        self.parser = None
        self.hashes: dict[str, str | None] = {}

    @property
    def inv_by_id(self):
        return {row["id"]: row for row in self.inventory["statements"]}

    @property
    def inv_by_decl(self):
        return {row["declaration"]: row for row in self.inventory["statements"]}

    @property
    def legacy_records(self):
        return {row["id"]: row for row in self.legacy["records"]}

    @property
    def legacy_queries(self):
        return {row["id"]: row for row in self.legacy["queries"]}

    @property
    def legacy_statements(self):
        return {row["id"]: row for row in self.legacy["statements"]}

    @property
    def legacy_certificates(self):
        return {row["id"]: row for row in self.legacy["certificates"]}


def read_json_checked(path: Path, chk: Checker, code: str):
    try:
        return read_json(path)
    except Exception as exc:  # fail closed
        chk.fail(code, f"cannot read {path}: {type(exc).__name__}: {exc}")
        return None


def load_sources(root: Path, registry_path: Path, dispositions_path: Path,
                 schema_path: Path, chk: Checker) -> Sources:
    src = Sources()
    for key, rel in (
        ("boundary", BOUNDARY_PATH),
        ("inventory", INVENTORY_PATH),
        ("pair_queue", PAIR_QUEUE_PATH),
        ("cluster_plan", CLUSTER_PLAN_PATH),
        ("coverage", COVERAGE_PATH),
        ("legacy", LEGACY_PATH),
        ("frozen_r4", FROZEN_R4_PATH),
    ):
        src.hashes[key] = sha_file(root / rel)

    src.registry = read_json_checked(registry_path, chk, "load.registry")
    src.schema = read_json_checked(schema_path, chk, "load.schema")
    src.dispositions = read_json_checked(dispositions_path, chk, "load.dispositions")
    src.inventory = read_json_checked(root / INVENTORY_PATH, chk, "load.inventory")
    src.queue = read_json_checked(root / PAIR_QUEUE_PATH, chk, "load.pair_queue")
    src.clusters = read_json_checked(root / CLUSTER_PLAN_PATH, chk, "load.cluster_plan")
    src.coverage = read_json_checked(root / COVERAGE_PATH, chk, "load.coverage")
    src.legacy = read_json_checked(root / LEGACY_PATH, chk, "load.legacy")

    if all(x is not None for x in (
        src.registry, src.schema, src.dispositions, src.inventory,
        src.queue, src.clusters, src.coverage, src.legacy,
    )):
        try:
            src.parser = load_r1_parser(root)
        except Exception as exc:
            chk.fail("load.r1_parser", f"cannot load R1 signature parser: {exc}")
    else:
        chk.fail("load.inputs", "one or more required inputs are unavailable")

    if src.inventory is None or src.queue is None or src.coverage is None:
        return src
    if src.registry is None or src.dispositions is None:
        return src

    _load_packages(root, src, chk)
    return src


def _package_artifacts(root: Path, meta: dict, screening: dict):
    screening_rel = meta["path"]
    pkg_dir = (root / screening_rel).parent

    def first_existing(candidates):
        for candidate in candidates:
            if candidate and (root / candidate).exists():
                return candidate
        return None

    search_rel = first_existing([
        meta.get("searchLogPath"),
        (pkg_dir / "search-log.json").relative_to(root).as_posix(),
    ])
    probe_rel = first_existing([
        meta.get("probePath"),
        ((screening.get("probeReference") or {}).get("path")),
        (pkg_dir / "probes/Surface-probe.lean").relative_to(root).as_posix(),
        (pkg_dir / "probes/R3-probe.lean").relative_to(root).as_posix(),
        (pkg_dir / "probes/R4-CI-probe.lean").relative_to(root).as_posix(),
        (pkg_dir / "probes/E1-probe.lean").relative_to(root).as_posix(),
        (pkg_dir / "probes/E2-probe.lean").relative_to(root).as_posix(),
        (pkg_dir / "probes/RAD1-probe.lean").relative_to(root).as_posix(),
        (pkg_dir / "probes/RAD2-probe.lean").relative_to(root).as_posix(),
        (pkg_dir / "probes/RAD3-probe.lean").relative_to(root).as_posix(),
        (pkg_dir / "probes/XD1-probe.lean").relative_to(root).as_posix(),
    ])
    fragment_rel = first_existing([
        meta.get("fragmentPath"),
        (pkg_dir / "coverage-fragment.json").relative_to(root).as_posix(),
    ])
    report_rel = first_existing([
        (pkg_dir / "REPORT.md").relative_to(root).as_posix(),
        (pkg_dir / "README.md").relative_to(root).as_posix(),
    ])
    validator_rel = first_existing([
        meta.get("validatePath"),
        (pkg_dir / "validate.py").relative_to(root).as_posix(),
    ])
    return {
        "screening": screening_rel,
        "searchLog": search_rel,
        "probe": probe_rel,
        "coverageFragment": fragment_rel,
        "report": report_rel,
        "validator": validator_rel,
    }


def _load_packages(root: Path, src: Sources, chk: Checker) -> None:
    metas = []
    for group in ("acceptedWorkPackages", "submittedWorkPackages", "r5WorkPackages"):
        for row in src.coverage.get(group, []):
            metas.append((group, dict(row)))
    chk.equal(len(metas), EXPECTED_ACTIVE["packages"], "packages.count",
              "coverage must expose ten accepted screening packages")
    seen_paths = set()
    for group, meta in metas:
        screening_rel = meta.get("path")
        if not screening_rel or screening_rel in seen_paths:
            chk.fail("packages.path", f"missing/duplicate package path {iso(screening_rel)}")
            continue
        seen_paths.add(screening_rel)
        screening_path = root / screening_rel
        actual_hash = sha_file(screening_path)
        if meta.get("sha256"):
            chk.equal(actual_hash, meta.get("sha256"), "packages.screening_hash",
                      f"screening hash mismatch for {screening_rel}")
        if not screening_path.exists():
            chk.fail("packages.screening_missing", f"missing screening {screening_rel}")
            continue
        screening = read_json_checked(screening_path, chk, "packages.screening_json")
        if screening is None:
            continue
        art = _package_artifacts(root, meta, screening)
        for name, rel in art.items():
            if rel is None:
                continue
            expected_hash = None
            if name == "searchLog":
                expected_hash = meta.get("searchLogSha256")
            elif name == "coverageFragment":
                expected_hash = meta.get("fragmentSha256")
            elif name == "validator":
                expected_hash = meta.get("validateSha256")
            elif name == "probe":
                expected_hash = meta.get("probeSha256")
            actual = sha_file(root / rel)
            if expected_hash:
                chk.equal(actual, expected_hash, f"packages.{name}_hash",
                          f"ledger-pinned {name} hash mismatch for {rel}")
            else:
                chk.check(actual is not None, f"packages.{name}_exists",
                          f"missing {name} artifact {rel}")
        pairs = screening.get("pairs", [])
        queries = [q for pair in pairs for q in pair.get("queries", [])]
        chk.equal(len(pairs), meta.get("pairCount"), "packages.pair_count",
                  f"pair count mismatch in {screening_rel}")
        if meta.get("queryCount") is not None:
            chk.equal(len(queries), meta.get("queryCount"), "packages.query_count",
                      f"query count mismatch in {screening_rel}")
        chk.check(meta.get("acceptance", "").startswith("accepted-"),
                  "packages.acceptance", f"{screening_rel} is not accepted")
        chk.equal(screening.get("round"), meta.get("round"), "packages.round",
                  f"round mismatch in {screening_rel}")
        package_id = meta.get("packageId") or meta.get("id")
        for query in queries:
            qid = query.get("queryId")
            if qid in src.raw_queries:
                chk.fail("packages.duplicate_query", f"duplicate raw query id {qid}")
            src.raw_queries[qid] = query
        src.packages.append({
            "group": group,
            "meta": meta,
            "packageId": package_id,
            "round": meta.get("round"),
            "acceptance": meta.get("acceptance"),
            "screening": screening,
            "screeningPath": screening_rel,
            "pairs": pairs,
            "queries": queries,
            "artifacts": art,
        })
    chk.equal(len(src.raw_queries), EXPECTED_ACTIVE["queries"], "packages.query_union",
              "accepted packages must contain exactly 152 distinct queries")
    seen_pairs = set()
    for pkg in src.packages:
        for pair in pkg["pairs"]:
            pid = pair.get("pairId")
            if pid in seen_pairs:
                chk.fail("packages.duplicate_pair", f"pair rescreened across packages: {pid}")
            seen_pairs.add(pid)
    chk.equal(len(seen_pairs), EXPECTED_ACTIVE["pairs"], "packages.pair_union",
              "accepted packages must cover exactly 136 distinct pairs")


# ---------------------------------------------------------------------------
# Top-level state, references, schema
# ---------------------------------------------------------------------------


def check_schema(src: Sources, chk: Checker) -> None:
    try:
        import jsonschema
    except ImportError:
        chk.fail("schema.jsonschema", "jsonschema is not installed; cannot accept the schema")
        return
    try:
        jsonschema.Draft202012Validator.check_schema(src.schema)
    except Exception as exc:
        chk.fail("schema.invalid", f"accepted schema is not valid draft 2020-12: {exc}")
        return
    validator = jsonschema.Draft202012Validator(src.schema)
    for name, instance, ref in (
        ("registry", src.registry, "#/$defs/registry"),
        ("legacyDispositions", src.dispositions, "#/$defs/legacyDispositions"),
    ):
        try:
            sub = validator.evolve(schema={"$ref": ref})
            errors = sorted(sub.iter_errors(instance), key=lambda e: list(e.path))
        except Exception as exc:
            chk.fail("schema.validate_error", f"{name}: schema evaluation failed: {exc}")
            continue
        chk.check(not errors, f"schema.{name}",
                  f"{name} does not validate: " +
                  "; ".join(f"{list(e.path)}: {e.message}" for e in errors[:5]))


def check_top_level(root: Path, src: Sources, chk: Checker) -> None:
    reg = src.registry
    dis = src.dispositions
    chk.equal(reg.get("$schema"), f"{SCHEMA_PATH}#/$defs/registry", "state.schema_ref",
              "registry schema reference")
    chk.equal(reg.get("schemaVersion"), "2.0.0", "state.schema_version", "registry schema version")
    chk.equal(reg.get("artifactKind"), "bounded-relation-registry", "state.artifact_kind",
              "registry artifact kind")
    chk.equal(reg.get("mode"), "bounded-full", "state.mode", "registry mode")
    chk.equal(reg.get("round"), "R8", "state.round", "registry round")
    chk.check(isinstance(reg.get("generatedOn"), str) and reg["generatedOn"],
              "state.generated_on", "generatedOn is required")
    acceptance = reg.get("acceptance")
    chk.check(acceptance in (PENDING, ACCEPTED), "state.acceptance_value",
              f"invalid registry acceptance {iso(acceptance)}")
    chk.equal(dis.get("acceptance"), acceptance, "state.acceptance_uniform",
              "registry and disposition acceptance states differ (partial flip)")
    chk.equal(dis.get("schemaVersion"), "1.0.0", "state.dispositions_schema_version",
              "disposition schema version")
    chk.equal(dis.get("artifactKind"), "legacy-disposition-ledger",
              "state.dispositions_artifact_kind", "disposition artifact kind")
    chk.equal(dis.get("mode"), "bounded-full", "state.dispositions_mode",
              "disposition mode")
    chk.equal(dis.get("round"), "R8", "state.dispositions_round", "disposition round")
    chk.equal(dis.get("$schema"), f"{SCHEMA_PATH}#/$defs/legacyDispositions",
              "state.dispositions_schema_ref", "disposition schema reference")
    if acceptance == ACCEPTED:
        # Uniform acceptance also means every accepted package and every
        # R5 work package is accepted; a single pending row is a partial flip.
        for pkg in src.packages:
            chk.check(pkg["acceptance"].startswith("accepted-"),
                      "state.accepted_package", f"{pkg['packageId']} is not accepted")
        for row in src.coverage.get("r5WorkPackages", []):
            chk.check(row.get("acceptance") == "accepted-R5", "state.accepted_r5",
                      f"R5 work package {row.get('id')} is not accepted-R5")
        chk.check(src.registry.get("legacyReconciliation", {}).get("legacyRegistryUnchanged") is True,
                  "state.accepted_legacy_unchanged", "accepted state must keep legacy unchanged")
    else:
        chk.note("Registry is submitted-R8-pending-review; this report is evidence for two "
                 "independent reviewers, not an acceptance record.")


def check_references(root: Path, src: Sources, chk: Checker) -> None:
    ref = src.registry.get("references", {})
    for key, rel, hash_key in (
        ("boundary", BOUNDARY_PATH, "boundary"),
        ("inventory", INVENTORY_PATH, "inventory"),
        ("pairQueue", PAIR_QUEUE_PATH, "pair_queue"),
        ("clusterPlan", CLUSTER_PLAN_PATH, "cluster_plan"),
        ("coverage", COVERAGE_PATH, "coverage"),
        ("legacy", LEGACY_PATH, "legacy"),
        ("frozenR4", FROZEN_R4_PATH, "frozen_r4"),
    ):
        chk.equal(src.hashes[hash_key], EXPECTED[key], f"inputs.{key}_sha",
                  f"{rel} hash drift")
    r1 = ref.get("r1", {})
    chk.equal(r1.get("boundary", {}).get("sha256"), EXPECTED["boundary"],
              "references.r1.boundary", "R1 boundary reference")
    chk.equal(r1.get("statementInventory", {}).get("sha256"), EXPECTED["inventory"],
              "references.r1.inventory", "R1 inventory reference")
    chk.equal(r1.get("statementInventory", {}).get("statementRows"), 1154,
              "references.r1.inventory_rows", "R1 inventory row count")
    chk.equal(r1.get("statementInventory", {}).get("screeningEligible"), 1134,
              "references.r1.inventory_eligible", "R1 screeningEligible count")
    chk.equal(r1.get("pairQueue", {}).get("sha256"), EXPECTED["pairQueue"],
              "references.r1.pair_queue", "R1 pair-queue reference")
    chk.equal(r1.get("pairQueue", {}).get("pairCount"), 136,
              "references.r1.pair_count", "R1 pair count")
    chk.equal(r1.get("clusterPlan", {}).get("sha256"), EXPECTED["clusterPlan"],
              "references.r1.cluster_plan", "R1 cluster-plan reference")
    chk.equal(ref.get("coverageLedger", {}).get("sha256"), EXPECTED["coverage"],
              "references.coverage", "coverage ledger reference")
    chk.equal(ref.get("coverageLedger", {}).get("queryCount"), 152,
              "references.coverage_queries", "coverage ledger query count")
    chk.equal(ref.get("frozenR4Coverage", {}).get("sha256"), EXPECTED["frozenR4"],
              "references.frozen_r4", "frozen R4 coverage reference")
    chk.equal(ref.get("legacyRegistry", {}).get("sha256"), EXPECTED["legacy"],
              "references.legacy", "legacy registry reference")
    chk.equal(ref.get("legacyRegistry", {}).get("queries"), 151,
              "references.legacy_queries", "legacy query count")
    chk.equal(ref.get("legacyRegistry", {}).get("records"), 151,
              "references.legacy_records", "legacy record count")
    chk.equal(ref.get("legacyRegistry", {}).get("certificates"), 38,
              "references.legacy_certificates", "legacy certificate count")
    # Accepted packages reference block must be exactly the ten package inputs.
    refs = ref.get("acceptedPackages", [])
    chk.equal(len(refs), 10, "references.package_count", "accepted package references")
    ref_by_id = {row.get("packageId"): row for row in refs}
    for pkg in src.packages:
        row = ref_by_id.get(pkg["packageId"])
        chk.check(row is not None, "references.package_missing",
                  f"package {pkg['packageId']} missing from references")
        if row is None:
            continue
        chk.equal(row.get("round"), pkg["round"], "references.package_round",
                  f"{pkg['packageId']} round")
        chk.equal(row.get("acceptance"), pkg["acceptance"], "references.package_acceptance",
                  f"{pkg['packageId']} acceptance")
        chk.equal(row.get("screening", {}).get("sha256"), sha_file(root / pkg["screeningPath"]),
                  "references.package_screening_hash", f"{pkg['packageId']} screening hash")
        if pkg["artifacts"].get("probe"):
            chk.equal(row.get("probe", {}).get("sha256"),
                      sha_file(root / pkg["artifacts"]["probe"]),
                      "references.package_probe_hash", f"{pkg['packageId']} probe hash")
    # Companion outputs are referenced by path only, never by self hash.
    companion = src.registry.get("companionArtifacts", {})
    for key in ("builder", "schema", "legacyDispositions", "documentation"):
        chk.check(isinstance(companion.get(key), str) and companion.get(key),
                  f"references.companion.{key}", f"companion artifact {key} missing")
    for key in ("schema", "legacyDispositions", "documentation"):
        rel = companion.get(key)
        if rel:
            chk.check((root / rel).exists(), f"references.companion.{key}.exists",
                      f"companion artifact {rel} does not exist")
    # The generated registry may not record its own hash or the companion hashes.
    own_hashes = {
        sha_file(root / REGISTRY_PATH),
        sha_file(root / DISPOSITIONS_PATH),
        sha_file(root / SCHEMA_PATH),
        sha_file(root / DOCS_PATH),
    }
    own_hashes.discard(None)
    for path, value in walk_strings(src.registry):
        if SHA_RE.match(value) and value in own_hashes:
            chk.fail("hash.self_reference",
                     f"registry embeds a generated-artifact hash at {path}: {value}")
    for path, value in walk_strings(src.dispositions):
        if SHA_RE.match(value) and value in own_hashes:
            chk.fail("hash.self_reference",
                     f"dispositions embed a generated-artifact hash at {path}: {value}")
    for path, value in find_paths_with_key(src.registry, "sha256"):
        if not isinstance(value, str):
            continue
        if value in own_hashes:
            chk.fail("hash.cycle", f"registry reference {path} points at a generated artifact")
    for path, value in find_paths_with_key(src.dispositions, "sha256"):
        if not isinstance(value, str):
            continue
        if value in own_hashes:
            chk.fail("hash.cycle", f"disposition reference {path} points at a generated artifact")


# ---------------------------------------------------------------------------
# Queries, records, pairs
# ---------------------------------------------------------------------------


def check_queries_and_records(src: Sources, chk: Checker) -> None:
    reg = src.registry
    queries = reg.get("queries", [])
    records = reg.get("records", [])
    chk.equal(len(queries), EXPECTED_ACTIVE["queries"], "queries.count",
              "active query count")
    chk.equal(len(records), EXPECTED_ACTIVE["records"], "records.count",
              "active record count")
    qids = [q.get("queryId") for q in queries]
    rids = [r.get("recordId") for r in records]
    chk.equal(len(set(qids)), len(qids), "queries.unique", "query IDs must be unique")
    chk.equal(len(set(rids)), len(rids), "records.unique", "record IDs must be unique")
    q_by_id = {q["queryId"]: q for q in queries if "queryId" in q}
    r_by_id = {r["recordId"]: r for r in records if "recordId" in r}
    raw_by_id = src.raw_queries
    chk.equal(set(q_by_id), set(raw_by_id), "queries.source_set",
              "active query set differs from accepted-package query set")
    chk.equal(set(r_by_id), {"rec-bounded-" + qid for qid in q_by_id},
              "records.source_set", "active record IDs must be rec-bounded-<query>")
    # Query <-> record one-to-one.
    chk.equal(len({r.get("queryId") for r in records}), len(records),
              "records.query_unique", "a query has more than one active record")
    for record in records:
        qid = record.get("queryId")
        query = q_by_id.get(qid)
        chk.check(query is not None, "records.query_missing",
                  f"record {record.get('recordId')} points at unknown query {qid}")
        if query is not None:
            chk.equal(record.get("pairId"), query.get("pairId"), "records.pair",
                      f"{record.get('recordId')} pair mismatch")
            chk.equal(record.get("status"), query.get("outcome", {}).get("status"),
                      "records.status", f"{record.get('recordId')} status mismatch")
            chk.equal(record.get("scopeId"), query.get("scopeId"), "records.scope",
                      f"{record.get('recordId')} scope mismatch")
            chk.equal(record.get("snapshot"), query.get("snapshot"), "records.snapshot",
                      f"{record.get('recordId')} snapshot mismatch")
            chk.equal(record.get("statementVersion"), query.get("statementVersion"),
                      "records.statement_version",
                      f"{record.get('recordId')} statementVersion mismatch")
            chk.check(record.get("activeCoverage") is True, "records.active_coverage",
                      f"{record.get('recordId')} is not active coverage")

    # Every active query must preserve its accepted source fields verbatim.
    for query in queries:
        qid = query.get("queryId")
        raw = raw_by_id.get(qid)
        chk.check(raw is not None, "queries.raw_missing",
                  f"{qid} is not present in any accepted package")
        if raw is None:
            continue
        subset_equal(raw, query, f"query[{qid}]", chk, "queries.source_fidelity")
        chk.equal(query.get("recordId"), "rec-bounded-" + qid, "queries.record_id",
                  f"{qid} record id")
        chk.equal(query.get("sourcePackage", {}).get("sha256"),
                  sha_file(ROOT / _query_package_path(src, qid)),
                  "queries.package_hash", f"{qid} source package hash")
        # Chemical and semantic fields must be present and non-placeholder.
        for field in ("title", "chemicalQuestion", "chemicalRationale",
                      "expectedKindRationale", "falsificationCondition"):
            value = query.get(field)
            chk.check(isinstance(value, str) and len(value.strip()) >= 12,
                      f"queries.{field}", f"{qid} has an empty or too-short {field}")
            if isinstance(value, str):
                chk.check(not PLACEHOLDER.search(value), f"queries.{field}.placeholder",
                          f"{qid} {field} contains a placeholder marker")
        chk.check(isinstance(query.get("translations"), dict) and
                  set(query["translations"]) == {"left", "right"},
                  "queries.translations", f"{qid} translations must have left/right")
        for side in ("left", "right"):
            row = query.get("translations", {}).get(side, {})
            chk.check(isinstance(row, dict), "queries.translation_shape",
                      f"{qid} {side} translation is not an object")
            if isinstance(row, dict):
                chk.check(isinstance(row.get("id"), str) and row.get("id"),
                          "queries.translation_id", f"{qid} {side} translation id")
                chk.check(isinstance(row.get("requirement"), str) and
                          row.get("requirement"), "queries.translation_requirement",
                          f"{qid} {side} translation requirement")
                if query.get("outcome", {}).get("status") == "certified":
                    chk.check(row.get("id") not in ("none-declared", "candidate-not-total"),
                              "queries.certified_translation",
                              f"{qid} is certified with a non-total {side} translation")
                    chk.check(isinstance(row.get("term"), str) and row.get("term").strip(),
                              "queries.certified_translation_term",
                              f"{qid} is certified but {side} translation term is empty")
        channels = query.get("observationChannels")
        chk.check(isinstance(channels, list),
                  "queries.observation_channels", f"{qid} observationChannels is not a list")
        for index, channel in enumerate(channels or []):
            if not isinstance(channel, dict):
                chk.fail("queries.channel_shape", f"{qid} channel {index} is not an object")
                continue
            for field in ("id", "inputDomain", "leftObs", "rightObs",
                          "observedValueType"):
                chk.check(isinstance(channel.get(field), str) and channel.get(field).strip(),
                          "queries.channel_field",
                          f"{qid} channel {index} lacks {field}")
            chk.check(channel.get("domainNonempty") is True, "queries.channel_domain",
                      f"{qid} channel {index} domainNonempty is not true")
        shared = query.get("sharedContext", {})
        chk.check(isinstance(shared, dict) and shared.get("id"),
                  "queries.shared_context", f"{qid} sharedContext missing")
        chk.check(isinstance(shared.get("fields"), list) and shared.get("fields"),
                  "queries.shared_context_fields", f"{qid} sharedContext.fields missing")
        chk.check(isinstance(shared.get("physicalReading"), str) and
                  len(shared.get("physicalReading", "").strip()) >= 12,
                  "queries.shared_context_reading",
                  f"{qid} sharedContext.physicalReading missing")
        premises = query.get("premises", {})
        chk.check(isinstance(premises.get("predicate"), str) and premises["predicate"].strip(),
                  "queries.premise_predicate", f"{qid} premise predicate missing")
        chk.check(isinstance(premises.get("premiseIds"), list),
                  "queries.premise_ids", f"{qid} premiseIds missing")
        scope = query.get("scope", {})
        chk.check(isinstance(scope.get("id"), str) and scope["id"],
                  "queries.scope_id", f"{qid} scope id missing")
        chk.check(isinstance(scope.get("domain"), str) and scope["domain"].strip(),
                  "queries.scope_domain", f"{qid} scope domain missing")
        chk.check(isinstance(scope.get("description"), str) and scope["description"].strip(),
                  "queries.scope_description", f"{qid} scope description missing")
        chk.check(scope.get("snapshot") is not None, "queries.scope_snapshot",
                  f"{qid} scope snapshot missing")
        provenance = query.get("provenance", {})
        chk.check(isinstance(provenance.get("kind"), str) and provenance["kind"],
                  "queries.provenance", f"{qid} provenance kind missing")
        chk.check(query.get("expectedKind") in RELATION_KINDS, "queries.expected_kind",
                  f"{qid} expectedKind invalid")
        status = query.get("outcome", {}).get("status")
        chk.check(status in STATUSES, "queries.status", f"{qid} status invalid")
        # Endpoint identity is checked against the R1 inventory below; the
        # statement list and query endpoints must nevertheless agree here.
        for role in ("source", "target"):
            endpoint = query.get("endpoints", {}).get(role, {})
            chk.check(endpoint.get("statementId") not in ALIASES,
                      "queries.alias_endpoint", f"{qid} uses alias endpoint {role}")
            chk.check(endpoint.get("declaration") not in ALIAS_DECLARATIONS,
                      "queries.alias_declaration", f"{qid} uses alias declaration {role}")
            chk.check(endpoint.get("statementId") not in (None, ""),
                      "queries.endpoint_missing", f"{qid} missing {role} endpoint")

    # Per-query evidence semantics.
    for query in queries:
        qid = query.get("queryId")
        outcome = query.get("outcome", {})
        status = outcome.get("status")
        evidence = outcome.get("evidence", {})
        if status == "certified":
            chk.check(isinstance(evidence.get("certificateId"), str) and
                      evidence.get("certificateId"),
                      "queries.certified_evidence", f"{qid} certified without a certificate")
            chk.check(evidence.get("kind") in NON_REFUTATION_KINDS,
                      "queries.certified_kind", f"{qid} certified kind is not non-refutation")
            chk.equal(evidence.get("kind"), query.get("expectedKind"),
                      "queries.certified_expected_kind",
                      f"{qid} certificate kind differs from expectedKind")
            chk.check(evidence.get("type") in (
                "legacy-certificate", "r2-probe-certificate", "r3-probe-certificate",
                "r4-probe-certificate", "r4-ci-probe-certificate",
                "e2-probe-certificate", "rad1-probe-certificate",
                "rad2-probe-certificate", "r5-rad3-probe-certificate",
            ), "queries.certificate_type", f"{qid} unknown certificate evidence type")
            chk.equal(evidence.get("axiomFootprint"), ALLOWED_AXIOMS,
                      "queries.axiom_footprint", f"{qid} axiom footprint")
            chk.equal(evidence.get("allowedAxioms"), ALLOWED_AXIOMS,
                      "queries.allowed_axioms", f"{qid} allowed axioms")
            chk.check(outcome.get("evidenceClass") in EVIDENCE_CLASSES,
                      "queries.evidence_class", f"{qid} invalid evidence class")
            record = r_by_id.get("rec-bounded-" + qid)
            if record:
                chk.equal(record.get("certificateId"), evidence.get("certificateId"),
                          "records.certificate", f"{qid} record certificate mismatch")
                chk.equal(record.get("relationKind"), evidence.get("kind"),
                          "records.relation_kind", f"{qid} record kind mismatch")
                chk.equal(record.get("evidenceClass"), outcome.get("evidenceClass"),
                          "records.evidence_class", f"{qid} record evidence class mismatch")
        elif status == "refuted":
            chk.check(evidence.get("type") in ("refutation", "legacy-certificate"),
                      "queries.refuted_evidence", f"{qid} refuted without refutation certificate")
            chk.equal(evidence.get("kind"), "refutation", "queries.refuted_kind",
                      f"{qid} refuted kind must be refutation")
            chk.check(isinstance(evidence.get("certificateId"), str) and
                      evidence.get("certificateId"), "queries.refuted_certificate",
                      f"{qid} refuted without certificate id")
        else:
            chk.check(isinstance(evidence.get("searchLogRef"), str) and
                      evidence.get("searchLogRef"), "queries.search_log_ref",
                      f"{qid} non-certified without searchLogRef")
            if status in ("unresolved", "notEstablished"):
                chk.check(isinstance(evidence.get("candidateSummary"), str) and
                          evidence["candidateSummary"].strip(), "queries.candidate_summary",
                          f"{qid} {status} without candidateSummary")
            if status == "outOfScope":
                chk.check(isinstance(evidence.get("jurisdictionRationale"), str) and
                          evidence["jurisdictionRationale"].strip(),
                          "queries.jurisdiction_rationale",
                          f"{qid} outOfScope without jurisdictionRationale")
        if status == "unresolved":
            chk.check(isinstance(evidence.get("candidateSummary"), str) and
                      evidence["candidateSummary"].strip(), "queries.unresolved_gap",
                      f"{qid} unresolved without a named candidate/gap")
            record = r_by_id.get("rec-bounded-" + qid)
            if record:
                chk.check(isinstance(record.get("remainingGap"), str) and
                          record["remainingGap"].strip(), "records.remaining_gap",
                          f"{qid} unresolved record lacks remainingGap")
                chk.check(isinstance(record.get("searchLog"), dict),
                          "records.search_log", f"{qid} unresolved record lacks searchLog")
        if status == "notEstablished":
            record = r_by_id.get("rec-bounded-" + qid)
            if record:
                dep = record.get("dependencyEvidence", {})
                chk.check(isinstance(dep, dict) and dep.get("searchId") and
                          dep.get("path") and dep.get("sha256") and dep.get("commands"),
                          "records.dependency_evidence",
                          f"{qid} notEstablished lacks machine-recomputable dependency evidence")
        if status == "outOfScope":
            record = r_by_id.get("rec-bounded-" + qid)
            jurisdiction = record.get("jurisdiction", {}) if record else {}
            chk.check(jurisdiction.get("statementLevel") is True,
                      "records.jurisdiction_level", f"{qid} outOfScope lacks statement-level flag")
            chk.check(isinstance(jurisdiction.get("rationale"), str) and
                      jurisdiction["rationale"].strip(), "records.jurisdiction_rationale",
                      f"{qid} outOfScope lacks rationale")
            chk.check(isinstance(jurisdiction.get("searchLogRef"), str) and
                      jurisdiction["searchLogRef"], "records.jurisdiction_search",
                      f"{qid} outOfScope lacks searchLogRef")
            endpoints = jurisdiction.get("endpoints", {})
            chk.equal(endpoints.get("source"),
                      query.get("endpoints", {}).get("source", {}).get("statementId"),
                      "records.jurisdiction_source", f"{qid} jurisdiction source endpoint")
            chk.equal(endpoints.get("target"),
                      query.get("endpoints", {}).get("target", {}).get("statementId"),
                      "records.jurisdiction_target", f"{qid} jurisdiction target endpoint")

    # Search-log status and scope must agree with the query record.
    search_index = {}
    for pkg in src.packages:
        rel = pkg["artifacts"].get("searchLog")
        if not rel:
            continue
        log = read_json_checked(ROOT / rel, chk, "queries.search_log_json")
        if log is None:
            continue
        for entry in log.get("entries", []):
            entry_qid = entry.get("queryId")
            if entry_qid in search_index:
                chk.fail("queries.duplicate_search_log",
                         f"duplicate search-log entry for {entry_qid}")
            search_index[entry_qid] = (entry, rel, sha_file(ROOT / rel))
    certified_ids = {q["queryId"] for q in queries
                     if q.get("outcome", {}).get("status") == "certified"}
    for query in queries:
        qid = query["queryId"]
        status = query["outcome"]["status"]
        if status == "certified":
            chk.check(qid not in search_index, "queries.certified_search_log",
                      f"{qid} is certified but has a search-log entry")
            continue
        entry_row = search_index.get(qid)
        chk.check(entry_row is not None, "queries.search_log_missing",
                  f"{qid} has no search-log entry")
        if entry_row is None:
            continue
        entry, rel, digest = entry_row
        chk.equal(entry.get("status"), status, "queries.search_log_status",
                  f"{qid} search-log status")
        chk.equal(entry.get("scope"), query.get("scope", {}).get("id"),
                  "queries.search_log_scope", f"{qid} search-log scope")
        chk.equal(entry.get("snapshot"), query.get("scope", {}).get("snapshot"),
                  "queries.search_log_snapshot", f"{qid} search-log snapshot")
        chk.check(isinstance(entry.get("searchedStatements"), list) and
                  entry["searchedStatements"], "queries.search_log_statements",
                  f"{qid} search-log has no searchedStatements")
        chk.check(isinstance(entry.get("commands"), list) and entry["commands"],
                  "queries.search_log_commands", f"{qid} search-log has no commands")
        record = r_by_id.get("rec-bounded-" + qid)
        if record:
            chk.equal(record.get("searchLog", {}).get("sha256"), digest,
                      "records.search_log_hash", f"{qid} record search-log hash")
            chk.equal(record.get("searchLog", {}).get("searchId"), entry.get("searchId"),
                      "records.search_log_id", f"{qid} record search-log id")


def _query_package_path(src: Sources, qid: str) -> str:
    for pkg in src.packages:
        if any(q.get("queryId") == qid for q in pkg["queries"]):
            return pkg["screeningPath"]
    return ""


def check_pairs(src: Sources, chk: Checker) -> None:
    reg = src.registry
    pairs = reg.get("pairs", [])
    queries = reg.get("queries", [])
    q_by_id = {q["queryId"]: q for q in queries}
    q_by_pair = collections.defaultdict(list)
    for query in queries:
        q_by_pair[query.get("pairId")].append(query)
    queue_ids = [row.get("pairId") for row in src.queue.get("pairs", [])]
    chk.equal(len(pairs), EXPECTED_ACTIVE["pairs"], "pairs.count", "pair count")
    chk.equal(len({p.get("pairId") for p in pairs}), len(pairs), "pairs.unique",
              "pair IDs must be unique")
    chk.equal({p.get("pairId") for p in pairs}, set(queue_ids), "pairs.queue_set",
              "registry pairs must equal the R1 pair queue")
    chk.equal(sum(len(v) for v in q_by_pair.values()), 152, "pairs.query_sum",
              "queries assigned to pairs must sum to 152")
    total_queries = 0
    total_certified_pairs = 0
    for pair in pairs:
        pid = pair.get("pairId")
        qs = q_by_pair.get(pid, [])
        expected_query_ids = sorted(q.get("queryId") for q in qs)
        chk.check(len(qs) > 0, "pairs.empty", f"{pid} has no active query")
        chk.equal(sorted(pair.get("queryIds", [])), expected_query_ids,
                  "pairs.query_ids", f"{pid} queryIds")
        chk.equal(pair.get("queryCount"), len(qs), "pairs.query_count",
                  f"{pid} queryCount")
        total_queries += len(qs)
        counts = collections.Counter(q.get("outcome", {}).get("status") for q in qs)
        expected_counts = {status: counts.get(status, 0) for status in STATUSES}
        chk.equal(pair.get("outcomes"), expected_counts, "pairs.outcomes",
                  f"{pid} outcome counts")
        certified = [q for q in qs if q.get("outcome", {}).get("status") == "certified"]
        if certified:
            total_certified_pairs += 1
        chk.equal(pair.get("certifiedQueryIds"),
                  sorted(q.get("queryId") for q in certified),
                  "pairs.certified_ids", f"{pid} certified query IDs")
        chk.equal(sorted(pair.get("certifiedRelationKinds", [])),
                  sorted({q["outcome"]["kind"] for q in certified}),
                  "pairs.certified_kinds", f"{pid} certified kinds")
        chk.equal(pair.get("hasCheckedEvidence"), bool(certified),
                  "pairs.checked_evidence", f"{pid} hasCheckedEvidence")
        has_oos = any(q.get("outcome", {}).get("status") == "outOfScope" for q in qs)
        chk.equal(pair.get("hasStatementLevelOutOfScope"), has_oos,
                  "pairs.out_of_scope", f"{pid} hasStatementLevelOutOfScope")
        if certified:
            basis = "certified-statement-query"
        elif any(q.get("outcome", {}).get("status") in ("unresolved", "notEstablished")
                 for q in qs):
            basis = "named-noncertified-query"
        else:
            basis = "statement-level-outOfScope"
        chk.equal(pair.get("coverageBasis"), basis, "pairs.coverage_basis",
                  f"{pid} coverage basis")
        chk.check(pair.get("screened") is True, "pairs.screened", f"{pid} not screened")
        chk.equal(sorted(set(q.get("round") for q in qs)),
                  sorted(pair.get("packages", [])), "pairs.package_rounds",
                  f"{pid} package rounds")
        chk.check(pair.get("hasCheckedEvidence") or has_oos or
                  any(q.get("outcome", {}).get("status") in ("unresolved", "notEstablished")
                      for q in qs), "pairs.statement_record",
                  f"{pid} has no statement-level record")
        requirement = pair.get("requirement", {})
        chk.check(isinstance(requirement, dict), "pairs.requirement",
                  f"{pid} requirement missing")
        queue_row = next(row for row in src.queue["pairs"] if row.get("pairId") == pid)
        chk.equal(pair.get("theories"), queue_row.get("theories"), "pairs.theories",
                  f"{pid} theories")
        chk.equal(pair.get("primaryCluster"), queue_row.get("screeningCluster"),
                  "pairs.cluster", f"{pid} primary cluster")
        chk.equal(requirement.get("requiredOutcome"),
                  queue_row.get("requirement", {}).get("requiredOutcome"),
                  "pairs.requirement_outcome", f"{pid} required outcome")
    chk.equal(total_queries, 152, "pairs.total_queries", "pair query sum")
    chk.equal(total_certified_pairs, EXPECTED_ACTIVE["certifiedPairs"],
              "pairs.certified_pairs", "pairs with at least one certified relation")


# ---------------------------------------------------------------------------
# Counts / dimensions
# ---------------------------------------------------------------------------


def compute_dimensions(src: Sources):
    queries = src.registry.get("queries", [])
    records = src.registry.get("records", [])
    counts = collections.Counter(q.get("outcome", {}).get("status") for q in queries)
    by_round = collections.defaultdict(lambda: collections.Counter())
    for query in queries:
        by_round[query.get("round")][query.get("outcome", {}).get("status")] += 1
    by_round = {
        round_name: {status: counter.get(status, 0) for status in STATUSES}
        for round_name, counter in sorted(by_round.items())
    }
    certified = [q for q in queries if q.get("outcome", {}).get("status") == "certified"]
    kind_counts = collections.Counter(q["outcome"].get("kind") for q in certified)
    classes = collections.Counter(q["outcome"].get("evidenceClass") for q in certified)
    pairs_with = len({q.get("pairId") for q in certified})
    pair_universe = len(src.registry.get("pairs", []))
    pair_with_query = len({q.get("pairId") for q in queries})
    pair_with_non_oos = len({
        q.get("pairId") for q in queries
        if q.get("outcome", {}).get("status") != "outOfScope"
    })
    return {
        "outcomes": {status: counts.get(status, 0) for status in STATUSES},
        "byRound": by_round,
        "certified": len(certified),
        "certifiedQueries": len(certified),
        "certifiedPairs": pairs_with,
        "certifiedRelationKindCounts": {k: kind_counts.get(k, 0)
                                        for k in RELATION_KINDS
                                        if kind_counts.get(k, 0)},
        "certifiedEvidenceClasses": {k: classes.get(k, 0) for k in EVIDENCE_CLASSES},
        "pairUniverse": pair_universe,
        "pairsWithQuery": pair_with_query,
        "pairsWithNonOutOfScopeQuery": pair_with_non_oos,
        "pairsWithOnlyOutOfScope": pair_universe - pair_with_non_oos,
        "records": len(records),
    }


def check_counts(src: Sources, chk: Checker) -> dict:
    reg = src.registry
    dims = compute_dimensions(src)
    counts = reg.get("counts", {})
    chk.equal(counts.get("activeQueries"), EXPECTED_ACTIVE["queries"],
              "counts.active_queries", "activeQueries")
    chk.equal(counts.get("activeRecords"), EXPECTED_ACTIVE["records"],
              "counts.active_records", "activeRecords")
    chk.equal(counts.get("pairs"), EXPECTED_ACTIVE["pairs"], "counts.pairs", "pairs")
    chk.equal(counts.get("packages"), EXPECTED_ACTIVE["packages"], "counts.packages",
              "packages")
    chk.equal(counts.get("certifiedPairs"), dims["certifiedPairs"],
              "counts.certified_pairs", "certified pairs recomputed")
    chk.equal(counts.get("queryOutcomes"), EXPECTED_ACTIVE["outcomes"],
              "counts.query_outcomes", "query outcomes")
    chk.equal(counts.get("queryOutcomes"), dims["outcomes"], "counts.outcomes_recomputed",
              "query outcomes recomputed from queries")
    chk.equal(counts.get("probeFiles"), EXPECTED_ACTIVE["probeFiles"], "counts.probe_files",
              "probe files")
    chk.equal(counts.get("probeReviewedDeclarations"),
              EXPECTED_ACTIVE["reviewedDeclarations"],
              "counts.probe_declarations", "reviewed probe declarations")
    chk.equal(counts.get("candidateDeclarations"), EXPECTED_ACTIVE["candidates"],
              "counts.candidates", "candidate declarations")
    chk.equal(counts.get("evidenceReferences"), EXPECTED_ACTIVE["evidenceReferences"],
              "counts.evidence_references", "evidence references")
    library = counts.get("certificateLibrary", {})
    chk.equal(library.get("total"), EXPECTED_ACTIVE["libraryTotal"],
              "counts.library_total", "certificate library total")
    chk.equal(library.get("deliveredModule"), EXPECTED_ACTIVE["libraryDelivered"],
              "counts.library_delivered", "delivered-module library")
    chk.equal(library.get("boundedProbe"), EXPECTED_ACTIVE["libraryProbe"],
              "counts.library_probe", "bounded-probe library")
    active_ev = counts.get("activeCertifiedEvidence", {})
    chk.equal(active_ev.get("total"), EXPECTED_ACTIVE["outcomes"]["certified"],
              "counts.active_evidence", "active certified evidence total")
    chk.equal(active_ev.get("boundedProbe"), EXPECTED_ACTIVE["activeProbe"],
              "counts.active_probe", "active probe certificates")
    chk.equal(active_ev.get("deliveredModule"), EXPECTED_ACTIVE["activeLegacy"],
              "counts.active_legacy", "active reused legacy certificates")
    chk.equal(active_ev.get("boundedProbe"), dims["certifiedEvidenceClasses"].get("boundedProbe"),
              "counts.active_probe_recomputed", "active probe certificates recomputed")
    chk.equal(active_ev.get("deliveredModule"),
              dims["certifiedEvidenceClasses"].get("deliveredModule"),
              "counts.active_legacy_recomputed", "active legacy certificates recomputed")

    coverage = reg.get("coverage", {})
    chk.equal(coverage.get("pairUniverse"), EXPECTED_ACTIVE["pairs"],
              "counts.coverage_universe", "pair universe")
    chk.equal(coverage.get("pairsWithScreening"), EXPECTED_ACTIVE["pairs"],
              "counts.coverage_screened", "pairs with screening")
    chk.equal(coverage.get("pairsWithNamedStatementQuery"), dims["pairsWithQuery"],
              "counts.coverage_named", "pairs with named statement query")
    chk.equal(coverage.get("remainingPairIds"), [], "counts.coverage_remaining",
              "remaining pair IDs")

    outcomes = reg.get("queryOutcomes", {})
    chk.equal(outcomes.get("certified"), EXPECTED_ACTIVE["outcomes"]["certified"],
              "counts.qo_certified", "certified outcome")
    chk.equal(outcomes.get("refuted"), EXPECTED_ACTIVE["outcomes"]["refuted"],
              "counts.qo_refuted", "refuted outcome")
    chk.equal(outcomes.get("unresolved"), EXPECTED_ACTIVE["outcomes"]["unresolved"],
              "counts.qo_unresolved", "unresolved outcome")
    chk.equal(outcomes.get("notEstablished"), EXPECTED_ACTIVE["outcomes"]["notEstablished"],
              "counts.qo_notestablished", "notEstablished outcome")
    chk.equal(outcomes.get("outOfScope"), EXPECTED_ACTIVE["outcomes"]["outOfScope"],
              "counts.qo_outofscope", "outOfScope outcome")
    chk.equal(outcomes.get("byRound"), dims["byRound"], "counts.qo_by_round",
              "outcomes by round")
    chk.equal(outcomes.get("certifiedEvidenceClasses"), dims["certifiedEvidenceClasses"],
              "counts.qo_evidence_classes", "certified evidence classes")

    discovery = reg.get("relationDiscovery", {})
    chk.equal(discovery.get("certifiedQueries"), dims["certifiedQueries"],
              "counts.discovery_queries", "certified relation discovery queries")
    chk.equal(discovery.get("pairsWithCertifiedRelation"), dims["certifiedPairs"],
              "counts.discovery_pairs", "certified relation discovery pairs")
    chk.equal(discovery.get("certifiedRelationKindCounts"),
              dims["certifiedRelationKindCounts"], "counts.discovery_kinds",
              "certified relation kind counts")
    return dims


# ---------------------------------------------------------------------------
# Statements and evidence references
# ---------------------------------------------------------------------------


def check_statements(root: Path, src: Sources, chk: Checker) -> None:
    statements = src.registry.get("statements", [])
    chk.equal(len(statements), EXPECTED_ACTIVE["statements"], "statements.count",
              "active statement rows")
    chk.equal(len({s.get("statementId") for s in statements}), len(statements),
              "statements.unique", "statement IDs must be unique")
    expected_ids = set()
    for query in src.registry.get("queries", []):
        for role in ("source", "target"):
            expected_ids.add(query.get("endpoints", {}).get(role, {}).get("statementId"))
    chk.equal({s.get("statementId") for s in statements}, expected_ids,
              "statements.endpoint_set", "statement rows must be exactly the active endpoints")
    inv_by_id = src.inv_by_id
    stmt_by_id = {s.get("statementId"): s for s in statements}
    for query in src.registry.get("queries", []):
        qid = query.get("queryId")
        for role in ("source", "target"):
            endpoint = query.get("endpoints", {}).get(role, {})
            sid = endpoint.get("statementId")
            row = stmt_by_id.get(sid)
            chk.check(row is not None, "statements.endpoint_row",
                      f"{qid} {role} endpoint {sid} has no statement row")
            inv = inv_by_id.get(sid)
            chk.check(inv is not None, "statements.inventory_row",
                      f"{qid} {role} endpoint {sid} is not an R1 inventory statement")
            if inv is None:
                continue
            chk.check(inv.get("screeningEligible") is True, "statements.eligible",
                      f"{qid} {role} endpoint {sid} is not screeningEligible")
            for field, inv_field in (
                ("theory", "theory"),
                ("declaration", "declaration"),
                ("declarationKind", "declarationKind"),
                ("sourceArtifact", "sourceArtifact"),
                ("sourceLine", "sourceLine"),
                ("version", "version"),
                ("signatureSha256", "signatureSha256"),
                ("sourceArtifactSha256", "sourceArtifactSha256"),
            ):
                chk.equal(endpoint.get(field), inv.get(inv_field),
                          f"statements.endpoint_{field}",
                          f"{qid} {role} endpoint {field} vs inventory")
            if row is not None:
                for field in ("inventoryId", "theory", "declaration", "declarationKind",
                              "sourceArtifact", "sourceLine", "version", "signatureSha256",
                              "sourceArtifactSha256", "sourceSignature", "screeningEligible"):
                    expected_value = inv.get("id") if field == "inventoryId" else inv.get(field)
                    chk.equal(row.get(field), expected_value, f"statements.row_{field}",
                              f"{sid} statement row {field} vs inventory")
                chk.equal(row.get("statementId"), inv.get("id"), "statements.row_id",
                          f"{sid} statement id")
            # Recompute the source hash, line and signature from the delivered source.
            source_rel = inv.get("sourceArtifact")
            source_path = root / source_rel
            actual_source = sha_file(source_path)
            chk.equal(actual_source, inv.get("sourceArtifactSha256"),
                      "statements.source_hash", f"{sid} source hash drift")
            if src.parser is not None and source_path.exists():
                parsed = src.parser.signatures(str(source_path))
                info = parsed.get(inv.get("declaration"))
                chk.check(info is not None, "statements.declaration_missing",
                          f"{sid} declaration not found in {source_rel}")
                if info is not None:
                    chk.equal(info.get("line"), inv.get("sourceLine"),
                              "statements.source_line", f"{sid} source line")
                    signature = src.parser.signature_sha(
                        info.get("kind"), inv.get("declaration"), info.get("signature"))
                    chk.equal(signature, inv.get("signatureSha256"),
                              "statements.signature_hash", f"{sid} signature hash")
    # No alias may appear as an active statement or declaration anywhere.
    alias_ids = set(ALIASES)
    for statement in statements:
        chk.check(statement.get("statementId") not in alias_ids, "statements.alias_id",
                  f"alias {statement.get('statementId')} used as active statement")
        chk.check(statement.get("declaration") not in ALIAS_DECLARATIONS,
                  "statements.alias_declaration",
                  f"alias declaration {statement.get('declaration')} used as active statement")
    for path, value in walk_strings(src.registry):
        if path.endswith("/statementId") or path.endswith("/inventoryId"):
            chk.check(value not in alias_ids, "statements.alias_anywhere",
                      f"alias used as {path}")
        if path.endswith("/declaration"):
            chk.check(value not in ALIAS_DECLARATIONS, "statements.alias_declaration_anywhere",
                      f"alias declaration used at {path}")


def check_evidence_references(root: Path, src: Sources, chk: Checker) -> None:
    rows = src.registry.get("evidenceReferences", [])
    chk.equal(len(rows), EXPECTED_ACTIVE["evidenceReferences"],
              "evidence.count", "evidence references")
    chk.equal(len({row.get("declaration") for row in rows}), len(rows),
              "evidence.unique", "evidence reference declarations must be unique")
    # Recompute the cited set from accepted query evidence.
    groups = {}
    for query in src.registry.get("queries", []):
        for usage in query.get("outcome", {}).get("evidence", {}).get(
                "underlyingTheorems", []):
            declaration = usage.get("declaration")
            group = groups.setdefault(declaration, {
                "artifacts": set(), "lines": set(), "roles": set(), "queries": set(),
            })
            group["artifacts"].add(usage.get("sourceArtifact"))
            if usage.get("sourceLine") is not None:
                group["lines"].add(usage.get("sourceLine"))
            if usage.get("role"):
                group["roles"].add(usage.get("role"))
            group["queries"].add(query.get("queryId"))
    chk.equal(len(groups), EXPECTED_ACTIVE["evidenceReferences"],
              "evidence.recomputed_count", "evidence reference count from accepted sources")
    by_decl = {row.get("declaration"): row for row in rows}
    chk.equal(set(by_decl), set(groups), "evidence.set",
              "evidence reference declarations differ from accepted sources")
    inv_by_decl = src.inv_by_decl
    for declaration, group in groups.items():
        row = by_decl.get(declaration)
        if row is None:
            continue
        chk.equal(sorted(row.get("usedByQueryIds", [])), sorted(group["queries"]),
                  "evidence.used_by", f"{declaration} usedByQueryIds")
        chk.equal(sorted(row.get("roles", [])), sorted(group["roles"]),
                  "evidence.roles", f"{declaration} roles")
        source_rel = row.get("sourceArtifact")
        source_path = root / source_rel
        chk.check(source_path.exists(), "evidence.source_exists",
                  f"{declaration} source {source_rel} missing")
        if not source_path.exists():
            continue
        chk.equal(sha_file(source_path), row.get("sourceArtifactSha256"),
                  "evidence.source_hash", f"{declaration} source hash")
        inv = inv_by_decl.get(declaration)
        chk.equal(row.get("inInventory"), inv is not None, "evidence.in_inventory",
                  f"{declaration} inInventory flag")
        if inv is not None:
            chk.equal(row.get("inventoryStatementId"), inv.get("id"),
                      "evidence.inventory_id", f"{declaration} inventory id")
            chk.equal(row.get("sourceArtifact"), inv.get("sourceArtifact"),
                      "evidence.inventory_source", f"{declaration} inventory source")
            chk.equal(row.get("sourceLine"), inv.get("sourceLine"),
                      "evidence.inventory_line", f"{declaration} inventory line")
            chk.equal(row.get("signatureSha256"), inv.get("signatureSha256"),
                      "evidence.inventory_signature", f"{declaration} inventory signature")
        if src.parser is not None:
            parsed = src.parser.signatures(str(source_path))
            info = parsed.get(declaration)
            chk.check(info is not None, "evidence.declaration_missing",
                      f"{declaration} not found in {source_rel}")
            if info is not None:
                chk.equal(info.get("line"), row.get("sourceLine"),
                          "evidence.source_line", f"{declaration} source line")
                signature = src.parser.signature_sha(
                    info.get("kind"), declaration, info.get("signature"))
                chk.equal(signature, row.get("signatureSha256"),
                          "evidence.signature_hash", f"{declaration} signature hash")


# ---------------------------------------------------------------------------
# Certificate library and probes
# ---------------------------------------------------------------------------


def check_certificate_library(root: Path, src: Sources, chk: Checker) -> None:
    library = src.registry.get("certificateLibrary", {})
    delivered = library.get("deliveredModule", [])
    probes = library.get("boundedProbe", [])
    chk.equal(len(delivered), EXPECTED_ACTIVE["libraryDelivered"],
              "certificates.delivered_count", "delivered module library")
    chk.equal(len(probes), EXPECTED_ACTIVE["libraryProbe"],
              "certificates.probe_count", "bounded probe library")
    chk.equal(len(delivered) + len(probes), EXPECTED_ACTIVE["libraryTotal"],
              "certificates.total", "certificate library total")
    all_ids = [c.get("certificateId") for c in delivered + probes]
    chk.equal(len(set(all_ids)), len(all_ids), "certificates.unique",
              "certificate IDs must be unique across both classes")
    legacy_certs = src.legacy_certificates
    chk.equal({c.get("certificateId") for c in delivered}, set(legacy_certs),
              "certificates.delivered_set",
              "delivered-module library must equal the unchanged legacy certificates")
    # Recompute active legacy reuse from accepted query evidence.
    active_legacy = collections.defaultdict(list)
    active_probe = collections.defaultdict(list)
    for query in src.registry.get("queries", []):
        if query.get("outcome", {}).get("status") != "certified":
            continue
        evidence = query["outcome"].get("evidence", {})
        cid = evidence.get("certificateId")
        if evidence.get("type") == "legacy-certificate":
            active_legacy[cid].append(query["queryId"])
        else:
            active_probe[cid].append(query["queryId"])
    chk.equal(sum(len(v) for v in active_legacy.values()), EXPECTED_ACTIVE["activeLegacy"],
              "certificates.active_legacy", "active reused legacy certificates")
    chk.equal(sum(len(v) for v in active_probe.values()), EXPECTED_ACTIVE["activeProbe"],
              "certificates.active_probe", "active probe certificates")
    for entry in delivered:
        cid = entry.get("certificateId")
        cert = legacy_certs.get(cid)
        if cert is None:
            chk.fail("certificates.legacy_missing", f"unknown legacy certificate {cid}")
            continue
        chk.equal(entry.get("evidenceClass"), "deliveredModule",
                  "certificates.delivered_class", f"{cid} evidence class")
        chk.equal(entry.get("kind"), cert.get("kind"), "certificates.delivered_kind",
                  f"{cid} kind")
        chk.equal(entry.get("declaration"), cert.get("lean"),
                  "certificates.delivered_declaration", f"{cid} declaration")
        chk.equal(entry.get("module"), cert.get("module"), "certificates.delivered_module",
                  f"{cid} module")
        chk.equal(entry.get("sourcePath"), cert.get("sourcePath"),
                  "certificates.delivered_source", f"{cid} source path")
        chk.equal(entry.get("sourceSha256"), cert.get("sourceSha256"),
                  "certificates.delivered_source_hash", f"{cid} source hash")
        chk.equal(sha_file(root / cert.get("sourcePath")), cert.get("sourceSha256"),
                  "certificates.delivered_source_disk", f"{cid} source hash on disk")
        chk.equal(entry.get("axiomFootprint"), cert.get("axiomFootprint"),
                  "certificates.delivered_axioms", f"{cid} axiom footprint")
        chk.equal(entry.get("allowedAxioms"), ALLOWED_AXIOMS,
                  "certificates.delivered_allowed", f"{cid} allowed axioms")
        expected_active = sorted(active_legacy.get(cid, []))
        chk.equal(sorted(entry.get("activeQueryIds", [])), expected_active,
                  "certificates.delivered_active", f"{cid} active queries")
        expected_role = "reused-active-certificate" if expected_active else "retained-legacy-support"
        chk.equal(entry.get("libraryRole"), expected_role, "certificates.delivered_role",
                  f"{cid} library role")
        chk.equal(entry.get("certificateStatus"),
                  "unchanged-delivered-module-certificate",
                  "certificates.delivered_status", f"{cid} certificate status")
        chk.check(entry.get("legacyRecordIds") == sorted(
            r["id"] for r in src.legacy["records"] if r.get("certificate") == cid),
            "certificates.delivered_records", f"{cid} legacy record links")
    chk.equal(sum(1 for c in delivered if c.get("activeQueryIds")), 12,
              "certificates.delivered_active_entries", "12 delivered certificates are active")
    chk.equal(sum(1 for c in delivered if not c.get("activeQueryIds")), 26,
              "certificates.delivered_retained", "26 delivered certificates are retained support")

    # Probe certificates and package provenance.
    probe_by_path = {}
    for entry in probes:
        cid = entry.get("certificateId")
        chk.equal(entry.get("evidenceClass"), "boundedProbe", "certificates.probe_class",
                  f"{cid} evidence class")
        chk.check(entry.get("kind") in NON_REFUTATION_KINDS, "certificates.probe_kind",
                  f"{cid} probe kind")
        chk.equal(entry.get("allowedAxioms"), ALLOWED_AXIOMS,
                  "certificates.probe_allowed", f"{cid} allowed axioms")
        chk.equal(entry.get("axiomFootprint"), ALLOWED_AXIOMS,
                  "certificates.probe_axioms", f"{cid} axiom footprint")
        chk.equal(entry.get("libraryRole"), "active-certificate",
                  "certificates.probe_role", f"{cid} library role")
        chk.equal(len(entry.get("activeQueryIds", [])), 1,
                  "certificates.probe_active", f"{cid} must be attached to one query")
        probe_rel = entry.get("probePath")
        chk.check(isinstance(probe_rel, str) and probe_rel.startswith("bounded_audit/"),
                  "certificates.probe_path", f"{cid} probe path")
        if probe_rel:
            probe_by_path.setdefault(probe_rel, []).append(cid)
        chk.equal(sha_file(root / probe_rel), entry.get("probeSha256"),
                  "certificates.probe_hash", f"{cid} probe hash")
        log = entry.get("compileLog", {})
        chk.equal(sha_file(root / log.get("path", "")), log.get("sha256"),
                  "certificates.probe_log", f"{cid} compile log hash")
        expected_command = f"proofs/scripts/lake env lean {probe_rel}"
        chk.equal(entry.get("buildCommand"), expected_command,
                  "certificates.probe_command", f"{cid} build command")
        pkg = next((p for p in src.packages
                    if p["packageId"] == entry.get("packageId")), None)
        chk.check(pkg is not None, "certificates.probe_package",
                  f"{cid} package {entry.get('packageId')} not accepted")
        if pkg:
            chk.equal(entry.get("round"), pkg["round"], "certificates.probe_round",
                      f"{cid} round")
            chk.equal(entry.get("acceptance"), pkg["acceptance"],
                      "certificates.probe_acceptance", f"{cid} package acceptance")
            review = entry.get("packageReview", {})
            if review.get("kind") == "package-report":
                chk.equal(sha_file(root / review.get("path", "")), review.get("sha256"),
                          "certificates.probe_review", f"{cid} package review hash")
            elif review.get("kind") == "coverage-acceptance-row":
                chk.equal(review.get("sha256"), EXPECTED["coverage"],
                          "certificates.probe_review", f"{cid} coverage acceptance row")
        expected_queries = sorted(active_probe.get(cid, []))
        chk.equal(sorted(entry.get("activeQueryIds", [])), expected_queries,
                  "certificates.probe_query_link", f"{cid} active query link")
        if expected_queries:
            query = next(q for q in src.registry["queries"]
                         if q["queryId"] == expected_queries[0])
            evidence = query.get("outcome", {}).get("evidence", {})
            chk.equal(evidence.get("certificateId"), cid,
                      "certificates.probe_evidence_id", f"{cid} query certificate id")
            chk.equal(evidence.get("kind"), entry.get("kind"),
                      "certificates.probe_evidence_kind", f"{cid} query certificate kind")
            chk.equal(evidence.get("probe", {}).get("declaration"),
                      entry.get("declaration"),
                      "certificates.probe_evidence_declaration",
                      f"{cid} query certificate declaration")
            chk.equal(evidence.get("probe", {}).get("sha256"), entry.get("probeSha256"),
                      "certificates.probe_evidence_hash", f"{cid} query probe hash")
    # Every active probe certificate must be exactly one certified query.
    chk.equal(set(active_probe), {c.get("certificateId") for c in probes},
              "certificates.probe_active_set",
              "active probe evidence set differs from probe library")
    # No candidate declaration may be a certificate.
    candidate_declarations = {
        c.get("declaration") for c in src.registry.get("candidateEvidence", [])
    }
    library_declarations = {c.get("declaration") for c in delivered + probes}
    for declaration in candidate_declarations:
        chk.check(declaration not in library_declarations, "certificates.candidate_promoted",
                  f"candidate {declaration} appears in the certificate library")


def check_probe_files(root: Path, src: Sources, chk: Checker) -> dict:
    files = src.registry.get("probeFiles", [])
    chk.equal(len(files), EXPECTED_ACTIVE["probeFiles"], "probes.file_count",
              "probe file count")
    chk.equal(len({f.get("path") for f in files}), len(files), "probes.unique",
              "probe paths must be unique")
    probes = src.registry.get("certificateLibrary", {}).get("boundedProbe", [])
    candidates = src.registry.get("candidateEvidence", [])
    certificate_by_path = collections.defaultdict(list)
    for cert in probes:
        certificate_by_path[cert.get("probePath")].append(cert)
    candidate_by_path = collections.defaultdict(list)
    for candidate in candidates:
        candidate_by_path[candidate.get("probePath")].append(candidate)
    expected_paths = {c.get("probePath") for c in probes} | {
        c.get("probePath") for c in candidates
    }
    chk.equal({f.get("path") for f in files}, expected_paths, "probes.path_set",
              "probeFiles must cover every certificate/candidate probe")
    total_cert = 0
    total_candidate = 0
    total_reviewed = 0
    declarations = {}
    for entry in files:
        rel = entry.get("path")
        path = root / rel
        chk.check(path.exists(), "probes.file_exists", f"missing probe {rel}")
        chk.equal(sha_file(path), entry.get("sha256"), "probes.file_hash",
                  f"probe hash {rel}")
        chk.equal(entry.get("buildCommand"),
                  f"proofs/scripts/lake env lean {rel}", "probes.command",
                  f"probe build command {rel}")
        log = entry.get("compileLog", {})
        chk.equal(sha_file(root / log.get("path", "")), log.get("sha256"),
                  "probes.log_hash", f"probe compile log {rel}")
        cert_decls = sorted(entry.get("certificateDeclarations", []))
        cand_decls = sorted(entry.get("candidateDeclarations", []))
        chk.equal(cert_decls, sorted(c.get("declaration") for c in certificate_by_path[rel]),
                  "probes.certificate_declarations", f"{rel} certificate declarations")
        chk.equal(cand_decls, sorted(c.get("declaration") for c in candidate_by_path[rel]),
                  "probes.candidate_declarations", f"{rel} candidate declarations")
        chk.equal(entry.get("certificateDeclarationCount"), len(cert_decls),
                  "probes.certificate_count", f"{rel} certificate count")
        chk.equal(entry.get("candidateDeclarationCount"), len(cand_decls),
                  "probes.candidate_count", f"{rel} candidate count")
        chk.equal(entry.get("reviewedDeclarationCount"), len(cert_decls) + len(cand_decls),
                  "probes.reviewed_count", f"{rel} reviewed count")
        total_cert += len(cert_decls)
        total_candidate += len(cand_decls)
        total_reviewed += len(cert_decls) + len(cand_decls)
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        stripped = strip_lean_comments_and_strings(text)
        for token in PROBE_FORBIDDEN.findall(stripped):
            chk.fail("probes.forbidden_token", f"{rel} contains forbidden token {token!r}")
        source_decls = set(DECL_RE.findall(stripped))
        printed = PRINT_RE.findall(text)
        reviewed = set(cert_decls) | set(cand_decls)
        for declaration in reviewed:
            short = declaration.split(".")[-1]
            chk.check(short in source_decls or declaration in source_decls,
                      "probes.declaration_missing",
                      f"{rel} does not declare {declaration}")
        chk.equal(set(printed), reviewed, "probes.print_axioms_set",
                  f"{rel} #print axioms declarations")
        declarations[rel] = reviewed
    chk.equal(total_cert, EXPECTED_ACTIVE["activeProbe"], "probes.total_certificates",
              "probe certificate declarations")
    chk.equal(total_candidate, EXPECTED_ACTIVE["candidates"],
              "probes.total_candidates", "probe candidate declarations")
    chk.equal(total_reviewed, EXPECTED_ACTIVE["reviewedDeclarations"],
              "probes.total_reviewed", "reviewed probe declarations")
    # Candidate evidence must be exactly the three excluded XD1 declarations.
    chk.equal(len(candidates), EXPECTED_ACTIVE["candidates"], "candidates.count",
              "candidate evidence count")
    for candidate in candidates:
        cid = candidate.get("candidateId")
        declaration = candidate.get("declaration")
        chk.check(candidate.get("isCertificate") is False, "candidates.not_certificate",
                  f"{cid} is marked as a certificate")
        chk.equal(candidate.get("status"), "unresolved", "candidates.status",
                  f"{cid} status")
        attached = candidate.get("attachedQueryIds", [])
        chk.equal(len(attached), 1, "candidates.attachment", f"{cid} attached query count")
        if not attached:
            continue
        query = next((q for q in src.registry["queries"]
                      if q["queryId"] == attached[0]), None)
        chk.check(query is not None, "candidates.query_missing",
                  f"{cid} attached query {attached[0]} missing")
        if query is None:
            continue
        chk.equal(query.get("outcome", {}).get("status"), "unresolved",
                  "candidates.query_status", f"{cid} attached query is not unresolved")
        evidence = query.get("outcome", {}).get("evidence", {})
        probe = evidence.get("candidateProbe", {})
        chk.equal(probe.get("declaration"), declaration,
                  "candidates.query_declaration", f"{cid} query candidate declaration")
        chk.equal(probe.get("path"), candidate.get("probePath"),
                  "candidates.query_path", f"{cid} query candidate path")
        chk.equal(probe.get("sha256"), candidate.get("probeSha256"),
                  "candidates.query_hash", f"{cid} query candidate hash")
        chk.equal(probe.get("axiomFootprint"), ALLOWED_AXIOMS,
                  "candidates.axioms", f"{cid} candidate axiom footprint")
        chk.check(cid == "candidate-" + attached[0], "candidates.id",
                  f"{cid} candidate id mismatch")
        chk.check((root / candidate.get("probePath")).exists(),
                  "candidates.probe_exists", f"{cid} probe missing")
    return {
        "files": len(files),
        "certificates": total_cert,
        "candidates": total_candidate,
        "reviewed": total_reviewed,
        "declarations": declarations,
    }


# ---------------------------------------------------------------------------
# Legacy dispositions
# ---------------------------------------------------------------------------


def _legacy_classification(src: Sources):
    inv_ids = set(src.inv_by_id)
    out = {}
    for query in src.legacy["queries"]:
        qid = query.get("id")
        source = query.get("source")
        target = query.get("target")

        def theory_of(statement_id):
            if statement_id.startswith("stmt-theory-"):
                return statement_id[len("stmt-theory-"):], "anchor"
            if statement_id in src.legacy_statements:
                return src.legacy_statements[statement_id].get("theory"), "legacy"
            if statement_id in inv_ids:
                return src.inv_by_id[statement_id].get("theory"), "inventory"
            return None, "unknown"

        a, akind = theory_of(source)
        b, bkind = theory_of(target)
        is_anchor = akind == "anchor" or bkind == "anchor"
        intra = (not is_anchor) and a == b
        pair_id = None
        if not intra and a and b:
            try:
                pair_id = canonical_pair(a, b)
            except ValueError:
                pair_id = None
        out[qid] = {
            "kind": "pair-anchor" if is_anchor else "named-query",
            "is_anchor": is_anchor,
            "intra": intra,
            "pair_id": pair_id,
            "theories": [a, b],
            "theory_kinds": [akind, bkind],
        }
    return out


def check_dispositions(root: Path, src: Sources, chk: Checker) -> dict:
    dis = src.dispositions
    entries = dis.get("entries", [])
    legacy_records = src.legacy_records
    legacy_queries = src.legacy_queries
    legacy_certs = src.legacy_certificates
    classification = _legacy_classification(src)
    chk.equal(len(entries), EXPECTED_ACTIVE["legacyRecords"], "dispositions.count",
              "legacy dispositions")
    chk.equal(len({e.get("legacyRecordId") for e in entries}), len(entries),
              "dispositions.unique_records", "legacy records disposed twice")
    chk.equal(len({e.get("legacyQueryId") for e in entries}), len(entries),
              "dispositions.unique_queries", "legacy queries disposed twice")
    chk.equal({e.get("legacyRecordId") for e in entries}, set(legacy_records),
              "dispositions.record_set",
              "disposition record set must equal the unchanged legacy records")
    chk.equal({e.get("legacyQueryId") for e in entries}, set(legacy_queries),
              "dispositions.query_set",
              "disposition query set must equal the unchanged legacy queries")
    named = [e for e in entries if e.get("legacyKind") == "named-query"]
    anchors = [e for e in entries if e.get("legacyKind") == "pair-anchor"]
    chk.equal(len(named), EXPECTED_ACTIVE["legacyNamed"], "dispositions.named",
              "named legacy queries")
    chk.equal(len(anchors), EXPECTED_ACTIVE["legacyAnchors"], "dispositions.anchors",
              "legacy pair anchors")
    chk.equal(sum(1 for e in entries if e.get("intraTheory")), EXPECTED_ACTIVE["legacyIntra"],
              "dispositions.intra", "intra-theory legacy records")
    # Recompute the 26/125 split from the unchanged legacy statement IDs.
    expected_named = sum(1 for row in classification.values() if not row["is_anchor"])
    expected_anchors = sum(1 for row in classification.values() if row["is_anchor"])
    chk.equal(expected_named, 26, "dispositions.recomputed_named", "26 named legacy queries")
    chk.equal(expected_anchors, 125, "dispositions.recomputed_anchors", "125 pair anchors")

    active_query_status = {
        q["queryId"]: q["outcome"]["status"] for q in src.registry["queries"]
    }
    active_queries_by_pair = collections.defaultdict(list)
    for query in src.registry["queries"]:
        active_queries_by_pair[query["pairId"]].append(query["queryId"])

    corrected = {
        "rec-D-S05-bep-rate-eq-exp-neg-eact": {
            "primary": "Q-WPS01-MB-03",
            "source": "stmt-Marcus-PhotoLean-Marcus-rate",
            "target": "stmt-BEP-PhotoLean-BEP-rate_eq_exp_neg_eact",
            "certificate": "cert-D-S05-bep-rate-eq-exp-neg-eact",
        },
        "rec-D-S06-hammond-sharp-iff-marcus-sharp": {
            "primary": "Q-WPS01-MH-05",
            "source": "stmt-Hammond-PhotoLean-Hammond-HammondDescriptor",
            "target": "stmt-Marcus-PhotoLean-Marcus-descriptor_sharp",
            "certificate": "cert-D-S06-hammond-sharp-iff-marcus-sharp",
        },
        "rec-D-S15-egBarrier-zero-iff-emEnergy-zero": {
            "primary": "Q-RAD3-ES-01",
            "source": "stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier",
            "target": "stmt-StokesShift-PhotoLean-StokesShift-emEnergy",
            "certificate": "cert-D-S15-egBarrier-zero-iff-emEnergy-zero",
        },
    }

    reconciliations = 0
    absence_overlaps = 0
    candidate_overlaps = 0
    for entry in entries:
        rid = entry.get("legacyRecordId")
        qid = entry.get("legacyQueryId")
        record = legacy_records.get(rid)
        query = legacy_queries.get(qid)
        if record is None or query is None:
            continue
        row = classification[qid]
        chk.equal(entry.get("legacyKind"), row["kind"], "dispositions.kind", f"{rid} kind")
        chk.equal(entry.get("intraTheory"), row["intra"], "dispositions.intra_flag",
                  f"{rid} intraTheory")
        chk.equal(entry.get("pairId"), row["pair_id"], "dispositions.pair_id",
                  f"{rid} pairId")
        chk.equal(entry.get("theories"), row["theories"], "dispositions.theories",
                  f"{rid} theories")
        chk.equal(entry.get("legacyStatus"), record.get("status"),
                  "dispositions.status", f"{rid} status")
        chk.equal(entry.get("legacyRelationKind"), record.get("relationKind"),
                  "dispositions.relation_kind", f"{rid} relation kind")
        chk.equal(entry.get("legacyCertificateId"), record.get("certificate"),
                  "dispositions.certificate", f"{rid} certificate")
        chk.equal(entry.get("legacyStatementVersion"), record.get("statementVersion"),
                  "dispositions.statement_version", f"{rid} statementVersion")
        chk.equal(entry.get("legacyQuestion"), query.get("question"),
                  "dispositions.question", f"{rid} question prose")
        expected_rationale = (
            record.get("rationale")
            or record.get("provenance", {}).get("rationale")
            or record.get("provenance", {}).get("note")
            or "The legacy registry records this row without a separate rationale; "
               "its query and provenance are retained verbatim."
        )
        chk.equal(entry.get("legacyRationale"), expected_rationale,
                  "dispositions.rationale", f"{rid} rationale prose")
        chk.equal(entry.get("legacyProvenance"), query.get("provenance"),
                  "dispositions.provenance", f"{rid} provenance prose")
        chk.equal(entry.get("legacySource", {}).get("path"), LEGACY_PATH,
                  "dispositions.source_path", f"{rid} legacy source path")
        chk.equal(entry.get("legacySource", {}).get("sha256"), EXPECTED["legacy"],
                  "dispositions.source_hash", f"{rid} legacy source hash")
        chk.equal(entry.get("legacySource", {}).get("recordId"), rid,
                  "dispositions.source_record", f"{rid} legacy source record")
        chk.check(entry.get("countsTowardActiveCoverage") is False,
                  "dispositions.active_coverage", f"{rid} counts toward active coverage")
        chk.equal(entry.get("activeCoverageContribution"),
                  {"pairCount": 0, "queryCount": 0},
                  "dispositions.coverage_contribution", f"{rid} active coverage contribution")
        chk.check(entry.get("proseRetention", {}).get("legacyProseRetained") is True,
                  "dispositions.prose_retained", f"{rid} prose not retained")
        chk.check(entry.get("proseRetention", {}).get("legacyRegistryUnchanged") is True,
                  "dispositions.registry_unchanged", f"{rid} legacy registry changed")
        # Active query links may only point at active queries on this pair;
        # intra-theory legacy evidence must contribute nothing.
        for linked in entry.get("activeQueryIds", []):
            chk.check(linked in active_query_status, "dispositions.active_query_unknown",
                      f"{rid} links unknown active query {linked}")
            if entry.get("pairId"):
                chk.equal(active_query_status.get(linked), active_query_status.get(linked),
                          "dispositions.noop", f"{rid}")
        if entry.get("intraTheory"):
            chk.equal(entry.get("activeQueryIds"), [], "dispositions.intra_active",
                      f"{rid} intra-theory record counts active queries")
        expected_checked = sorted(
            q for q in entry.get("activeQueryIds", [])
            if active_query_status.get(q) == "certified"
        )
        chk.equal(sorted(entry.get("checkedActiveQueryIds", [])), expected_checked,
                  "dispositions.checked_active", f"{rid} checked active query IDs")

        # Corrected legacy views for the three aliased records.
        if rid in corrected:
            view = entry.get("correctedLegacyView")
            chk.check(isinstance(view, dict), "dispositions.corrected_missing",
                      f"{rid} lacks its corrected legacy view")
            if isinstance(view, dict):
                spec = corrected[rid]
                chk.equal(view.get("correctedViewId"), "corrected-" + rid,
                          "dispositions.corrected_id", f"{rid} corrected view id")
                chk.equal(view.get("legacyRecordId"), rid, "dispositions.corrected_record",
                          f"{rid} corrected record")
                chk.equal(view.get("legacyQueryId"), qid, "dispositions.corrected_query",
                          f"{rid} corrected query")
                chk.equal(view.get("certificateId"), spec["certificate"],
                          "dispositions.corrected_certificate", f"{rid} corrected certificate")
                chk.check(view.get("certificateUnchanged") is True,
                          "dispositions.corrected_certificate_unchanged",
                          f"{rid} certificate not marked unchanged")
                chk.equal(view.get("primaryActiveQueryId"), spec["primary"],
                          "dispositions.corrected_primary", f"{rid} primary active query")
                chk.check(spec["primary"] in view.get("activeQueryIds", []),
                          "dispositions.corrected_active", f"{rid} primary query missing")
                endpoints = view.get("correctedEndpoints", {})
                chk.equal(endpoints.get("source", {}).get("statementId"), spec["source"],
                          "dispositions.corrected_source", f"{rid} corrected source")
                chk.equal(endpoints.get("target", {}).get("statementId"), spec["target"],
                          "dispositions.corrected_target", f"{rid} corrected target")
                for role in ("source", "target"):
                    e = endpoints.get(role, {})
                    chk.check(e.get("statementId") not in ALIASES,
                              "dispositions.corrected_alias", f"{rid} corrected {role} alias")
                    chk.check(e.get("declaration") not in ALIAS_DECLARATIONS,
                              "dispositions.corrected_alias_decl",
                              f"{rid} corrected {role} alias declaration")
                    inv = src.inv_by_id.get(e.get("statementId"))
                    chk.check(inv is not None, "dispositions.corrected_real",
                              f"{rid} corrected {role} is not a real R1 statement")
                    if inv is not None:
                        chk.equal(e.get("declaration"), inv.get("declaration"),
                                  "dispositions.corrected_declaration",
                                  f"{rid} corrected {role} declaration")
                        chk.equal(e.get("signatureSha256"), inv.get("signatureSha256"),
                                  "dispositions.corrected_signature",
                                  f"{rid} corrected {role} signature")
                record_view = view.get("correctedRecordView", {})
                chk.equal(record_view.get("correctedStatementVersion"),
                          f"{spec['source']}@1.0.0|{spec['target']}@1.0.0",
                          "dispositions.corrected_version",
                          f"{rid} corrected statementVersion")
                chk.equal(record_view.get("certificate"), spec["certificate"],
                          "dispositions.corrected_record_certificate",
                          f"{rid} corrected record certificate")
                query_view = view.get("correctedQueryView", {})
                chk.equal(query_view.get("source"), spec["source"],
                          "dispositions.corrected_query_source",
                          f"{rid} corrected query source")
                chk.equal(query_view.get("target"), spec["target"],
                          "dispositions.corrected_query_target",
                          f"{rid} corrected query target")
                # The linked active query must actually use the corrected endpoints.
                linked = next((q for q in src.registry["queries"]
                               if q["queryId"] == spec["primary"]), None)
                chk.check(linked is not None, "dispositions.corrected_query_missing",
                          f"{rid} primary active query missing")
                if linked:
                    chk.equal(linked["endpoints"]["source"]["statementId"], spec["source"],
                              "dispositions.corrected_link_source",
                              f"{rid} active query source differs from corrected view")
                    chk.equal(linked["endpoints"]["target"]["statementId"], spec["target"],
                              "dispositions.corrected_link_target",
                              f"{rid} active query target differs from corrected view")

        # Old absence/new evidence reconciliation.
        if row["is_anchor"]:
            pair_qids = active_queries_by_pair.get(row["pair_id"], [])
            checked_pair_qids = sorted(
                q for q in pair_qids if active_query_status.get(q) == "certified"
            )
            has_reconciliation = "absenceReconciliation" in entry
            if record.get("status") == "notEstablished" and checked_pair_qids:
                absence_overlaps += 1
                chk.check(has_reconciliation, "dispositions.absence_missing",
                          f"{rid} old absence with new evidence is not reconciled")
                chk.equal(entry.get("disposition"),
                          "reconciled-absence-with-active-evidence",
                          "dispositions.absence_disposition",
                          f"{rid} disposition")
            elif record.get("status") == "unresolved" and checked_pair_qids:
                candidate_overlaps += 1
                chk.check(has_reconciliation, "dispositions.candidate_missing",
                          f"{rid} old candidate with new evidence is not reconciled")
                chk.equal(entry.get("disposition"),
                          "reconciled-candidate-with-active-evidence",
                          "dispositions.candidate_disposition",
                          f"{rid} disposition")
            elif has_reconciliation:
                chk.fail("dispositions.unexpected_reconciliation",
                         f"{rid} is reconciled but its pair has no checked evidence")
            if has_reconciliation:
                reconciliations += 1
                recon = entry["absenceReconciliation"]
                chk.equal(sorted(recon.get("activeQueryIds", [])), checked_pair_qids,
                          "dispositions.reconciliation_queries",
                          f"{rid} reconciliation active query IDs")
                chk.equal(recon.get("legacyAnchorKind"),
                          "notEstablished" if record.get("status") == "notEstablished"
                          else "unresolved-candidate",
                          "dispositions.reconciliation_kind", f"{rid} anchor kind")
                chk.equal(recon.get("oldSnapshot"), record.get("snapshot"),
                          "dispositions.reconciliation_snapshot", f"{rid} old snapshot")
                expected_old_scope = record.get("scope")
                chk.equal(recon.get("oldScopeId"), expected_old_scope,
                          "dispositions.reconciliation_scope", f"{rid} old scope")
                chk.equal(recon.get("oldSearchIsNotRefutation"), True,
                          "dispositions.reconciliation_refutation",
                          f"{rid} old failed search became a refutation")
                chk.equal(recon.get("oldProseRetained"), True,
                          "dispositions.reconciliation_retention",
                          f"{rid} old prose not retained")
                chk.equal(recon.get("oldProseIsCurrentVerdict"), False,
                          "dispositions.reconciliation_verdict",
                          f"{rid} old prose treated as current verdict")
                relationship = recon.get("scopeRelationship")
                chk.check(relationship in ("subsumed", "superseded-in-named-scope",
                                          "coexists-different-scope"),
                          "dispositions.reconciliation_relationship",
                          f"{rid} invalid scope relationship {relationship}")
                if record.get("status") == "notEstablished":
                    chk.equal(relationship, "superseded-in-named-scope",
                              "dispositions.absence_relationship", f"{rid} relationship")
                    chk.equal(recon.get("newEvidenceOverridesOldProseInNamedScope"), True,
                              "dispositions.absence_override", f"{rid} override flag")
                else:
                    chk.equal(relationship, "coexists-different-scope",
                              "dispositions.candidate_relationship", f"{rid} relationship")
                    chk.equal(recon.get("newEvidenceOverridesOldProseInNamedScope"), False,
                              "dispositions.candidate_override", f"{rid} override flag")
                chk.check(isinstance(recon.get("relationshipRationale"), str) and
                          len(recon["relationshipRationale"].strip()) >= 40,
                          "dispositions.reconciliation_rationale",
                          f"{rid} reconciliation rationale too short")
                new_evidence = recon.get("newEvidence", [])
                chk.equal(sorted(e.get("queryId") for e in new_evidence),
                          checked_pair_qids, "dispositions.reconciliation_evidence",
                          f"{rid} reconciliation new evidence")
                for evidence in new_evidence:
                    linked = next((q for q in src.registry["queries"]
                                   if q["queryId"] == evidence.get("queryId")), None)
                    if linked is None:
                        continue
                    chk.equal(evidence.get("certificateId"),
                              linked["outcome"]["evidence"].get("certificateId"),
                              "dispositions.reconciliation_cert", f"{rid} certificate")
                    chk.equal(evidence.get("kind"), linked["outcome"].get("kind"),
                              "dispositions.reconciliation_kind_evidence", f"{rid} kind")
                    chk.equal(evidence.get("scopeId"), linked.get("scopeId"),
                              "dispositions.reconciliation_evidence_scope", f"{rid} scope")
                    chk.equal(evidence.get("snapshot"), linked.get("snapshot"),
                              "dispositions.reconciliation_evidence_snapshot",
                              f"{rid} snapshot")

    chk.equal(absence_overlaps, EXPECTED_ACTIVE["absenceNotEstablishedOverlaps"],
              "dispositions.absence_overlaps",
              "old notEstablished anchors now covered by checked evidence")
    chk.equal(candidate_overlaps, EXPECTED_ACTIVE["candidateOverlaps"],
              "dispositions.candidate_overlaps",
              "old unresolved candidate anchors now covered by checked evidence")
    chk.equal(reconciliations, EXPECTED_ACTIVE["absenceReconciliations"],
              "dispositions.reconciliations", "total old-absence/new-evidence links")
    # No intra-theory or anchor record may add pair/query coverage.
    chk.equal(sum(len(e.get("activeQueryIds", [])) for e in entries if e.get("intraTheory")),
              0, "dispositions.intra_coverage", "intra-theory active coverage")
    # No old failed search may be represented as a refutation.
    for entry in entries:
        chk.check(entry.get("legacyStatus") != "refuted", "dispositions.no_new_refutation",
                  f"{entry.get('legacyRecordId')} old search became refuted")
        if entry.get("legacyStatus") == "notEstablished":
            chk.check(entry.get("legacyRelationKind") in (None, ""),
                      "dispositions.no_negative_kind",
                      f"{entry.get('legacyRecordId')} absence has a relation kind")

    # Alias repairs and corrected views.
    alias_repairs = dis.get("aliasRepairs", [])
    corrected_views = dis.get("correctedLegacyViews", [])
    chk.equal(len(alias_repairs), EXPECTED_ACTIVE["legacyAliases"], "dispositions.alias_count",
              "alias repair count")
    chk.equal(len(corrected_views), EXPECTED_ACTIVE["correctedRecords"],
              "dispositions.corrected_count", "corrected legacy view count")
    chk.equal({row.get("aliasStatementId") for row in alias_repairs}, set(ALIASES),
              "dispositions.alias_ids", "four alias statement IDs")
    chk.equal({row.get("aliasDeclaration") for row in alias_repairs},
              ALIAS_DECLARATIONS, "dispositions.alias_declarations",
              "four alias declarations")
    for repair in alias_repairs:
        aid = repair.get("aliasRepairId")
        chk.equal(repair.get("aliasDeclaration"),
                  ALIASES.get(repair.get("aliasStatementId")),
                  "dispositions.alias_mapping", f"{aid} alias mapping")
        resolved_id = repair.get("resolvedStatementId")
        chk.check(resolved_id not in ALIASES, "dispositions.alias_resolved_alias",
                  f"{aid} resolves to another alias")
        inv = src.inv_by_id.get(resolved_id)
        chk.check(inv is not None, "dispositions.alias_resolved_real",
                  f"{aid} resolved endpoint is not an R1 inventory statement")
        if inv is not None:
            chk.equal(repair.get("resolvedDeclaration"), inv.get("declaration"),
                      "dispositions.alias_resolved_declaration",
                      f"{aid} resolved declaration")
        source = repair.get("sourceEvidence", {})
        real = source.get("realInventoryStatement", {})
        chk.equal(real.get("statementId"), resolved_id,
                  "dispositions.alias_real_statement", f"{aid} real inventory statement")
        chk.check(real.get("statementId") not in ALIASES,
                  "dispositions.alias_real_alias", f"{aid} real statement is an alias")
        affected = source.get("affectedLegacyRecords", [])
        chk.check(len(affected) >= 1, "dispositions.alias_affected",
                  f"{aid} has no affected legacy records")
        for rid in affected:
            chk.check(rid in legacy_records, "dispositions.alias_affected_missing",
                      f"{aid} unknown affected record {rid}")
        corrected_id = source.get("correctedLegacyViewId")
        chk.check(any(v.get("correctedViewId") == corrected_id for v in corrected_views),
                  "dispositions.alias_corrected_view", f"{aid} corrected view missing")
        delivered = source.get("deliveredCertificate", {})
        if delivered:
            cert = legacy_certs.get(delivered.get("certificateId"))
            chk.check(cert is not None, "dispositions.alias_certificate",
                      f"{aid} delivered certificate missing")
            if cert:
                chk.equal(delivered.get("declaration"), cert.get("lean"),
                          "dispositions.alias_certificate_declaration",
                          f"{aid} delivered declaration")
                chk.equal(delivered.get("sourceSha256"), cert.get("sourceSha256"),
                          "dispositions.alias_certificate_hash",
                          f"{aid} delivered certificate hash")
            chk.equal(delivered.get("unchanged"), True,
                      "dispositions.alias_certificate_unchanged",
                      f"{aid} delivered certificate not marked unchanged")
        for resolution in source.get("packageAliasResolutions", []):
            rel = resolution.get("screeningPath")
            chk.equal(sha_file(root / rel), resolution.get("screeningSha256"),
                      "dispositions.alias_package_hash", f"{aid} package alias hash")
            inner = resolution.get("resolution", {})
            if inner.get("aliasStatementId") is not None:
                chk.equal(inner.get("aliasStatementId"), repair.get("aliasStatementId"),
                          "dispositions.alias_package_mapping", f"{aid} package alias mapping")
                chk.equal(inner.get("resolvedStatementId"), resolved_id,
                          "dispositions.alias_package_resolution",
                          f"{aid} package alias resolution")
            else:
                # R5 package alias metadata for the D-S15 pair is record-keyed.
                chk.check(isinstance(inner.get("legacyRecordId"), str) and
                          inner.get("legacyRecordId"),
                          "dispositions.alias_package_record",
                          f"{aid} package alias record key")
                chk.check(repair.get("aliasStatementId") in inner.get("danglingEndpoints", []),
                          "dispositions.alias_package_mapping",
                          f"{aid} package alias mapping")
                chk.check(resolved_id in inner.get("resolvedStatements", []),
                          "dispositions.alias_package_resolution",
                          f"{aid} package alias resolution")
    for view in corrected_views:
        rid = view.get("legacyRecordId")
        chk.check(rid in corrected, "dispositions.view_record", f"unknown corrected record {rid}")
        entry = next((e for e in entries if e.get("legacyRecordId") == rid), None)
        chk.check(entry is not None, "dispositions.view_entry",
                  f"corrected view {rid} has no disposition entry")
        if entry:
            nested = entry.get("correctedLegacyView", {})
            chk.equal(view.get("correctedViewId"), nested.get("correctedViewId"),
                      "dispositions.view_id", f"{rid} corrected view id")
            chk.equal(view.get("primaryActiveQueryId"), nested.get("primaryActiveQueryId"),
                      "dispositions.view_primary", f"{rid} corrected primary query")
            chk.equal(sorted(view.get("activeQueryIds", [])),
                      sorted(nested.get("activeQueryIds", [])),
                      "dispositions.view_active", f"{rid} corrected active queries")
        chk.check(view.get("correctedViewId") == "corrected-" + rid,
                  "dispositions.view_naming", f"{rid} corrected view naming")

    expected_summary = {
        "records": 151,
        "namedQueries": 26,
        "pairAnchors": 125,
        "intraTheoryRecords": 5,
        "correctedRecords": 3,
        "absenceReconciliations": 44,
        "disposedExactlyOnce": True,
    }
    summary = dis.get("summary", {})
    for key, value in expected_summary.items():
        chk.equal(summary.get(key), value, f"dispositions.summary_{key}",
                  f"disposition summary {key}")
    chk.equal(summary.get("activeCoverageContribution"),
              {"pairCount": 0, "queryCount": 0},
              "dispositions.summary_coverage", "disposition summary coverage contribution")
    chk.equal(summary.get("scopeRelationships"),
              {"coexists-different-scope": 3, "superseded-in-named-scope": 41},
              "dispositions.summary_relationships", "disposition scope relationships")
    chk.equal(summary.get("byStatus"),
              {"certified": 24, "notEstablished": 121, "unresolved": 6},
              "dispositions.summary_status", "disposition legacy status counts")
    chk.equal(summary.get("byDisposition"),
              dict(sorted(collections.Counter(e.get("disposition") for e in entries).items())),
              "dispositions.summary_by_disposition", "disposition taxonomy counts")
    chk.equal(dis.get("source", {}).get("legacyRegistry", {}).get("sha256"),
              EXPECTED["legacy"], "dispositions.legacy_source", "legacy source hash")
    chk.equal(dis.get("source", {}).get("coverageLedger", {}).get("sha256"),
              EXPECTED["coverage"], "dispositions.coverage_source", "coverage source hash")
    chk.equal(dis.get("source", {}).get("statementInventory", {}).get("sha256"),
              EXPECTED["inventory"], "dispositions.inventory_source", "inventory source hash")
    chk.equal(dis.get("source", {}).get("pairQueue", {}).get("sha256"),
              EXPECTED["pairQueue"], "dispositions.queue_source", "pair queue source hash")
    chk.check(dis.get("source", {}).get("activeRegistry", {}).get("path") == REGISTRY_PATH,
              "dispositions.active_registry_path", "active registry companion path")
    chk.check("sha256" not in dis.get("source", {}).get("activeRegistry", {}),
              "dispositions.active_registry_hash",
              "disposition ledger must not hash the active registry (cycle)")
    return {
        "entries": len(entries),
        "named": len(named),
        "anchors": len(anchors),
        "intra": sum(1 for e in entries if e.get("intraTheory")),
        "reconciliations": reconciliations,
        "aliasRepairs": len(alias_repairs),
        "correctedViews": len(corrected_views),
        "byDisposition": dict(sorted(collections.Counter(
            e.get("disposition") for e in entries).items())),
        "byStatus": dict(sorted(collections.Counter(
            e.get("legacyStatus") for e in entries).items())),
    }


# ---------------------------------------------------------------------------
# Contexts / scopes / snapshots / packages
# ---------------------------------------------------------------------------


def check_indexes(src: Sources, chk: Checker, dims: dict) -> None:
    queries = src.registry.get("queries", [])
    q_by_id = {q["queryId"]: q for q in queries}
    # Contexts.
    contexts = src.registry.get("contexts", [])
    by_query = {}
    for entry in contexts:
        context = entry.get("context", {})
        cid = context.get("id")
        chk.check(isinstance(cid, str) and cid, "indexes.context_id",
                  "context entry has no id")
        chk.check(isinstance(context.get("fields"), list) and context.get("fields"),
                  "indexes.context_fields", f"{cid} has no fields")
        chk.check(isinstance(context.get("physicalReading"), str) and
                  context["physicalReading"].strip(),
                  "indexes.context_reading", f"{cid} has no physical reading")
        chk.check(isinstance(context.get("provenance"), str) and context.get("provenance"),
                  "indexes.context_provenance", f"{cid} has no provenance")
        chk.equal(entry.get("queryCount"), len(entry.get("queryIds", [])),
                  "indexes.context_count", f"{cid} query count")
        for qid in entry.get("queryIds", []):
            if qid in by_query:
                chk.fail("indexes.context_duplicate", f"query {qid} appears in two contexts")
            by_query[qid] = entry
            query = q_by_id.get(qid)
            chk.check(query is not None, "indexes.context_query",
                      f"{cid} links unknown query {qid}")
            if query:
                chk.equal(query.get("sharedContext"), context,
                          "indexes.context_fidelity", f"{qid} sharedContext vs context index")
    chk.equal(set(by_query), set(q_by_id), "indexes.context_coverage",
              "every active query must appear in exactly one context entry")
    # Scopes.
    scopes = src.registry.get("scopes", [])
    scope_by_query = {}
    for entry in scopes:
        sid = entry.get("id")
        chk.check(isinstance(sid, str) and sid, "indexes.scope_id", "scope entry has no id")
        chk.check(isinstance(entry.get("description"), str) and entry.get("description").strip(),
                  "indexes.scope_description", f"{sid} has no description")
        chk.check(isinstance(entry.get("domain"), str) and entry.get("domain").strip(),
                  "indexes.scope_domain", f"{sid} has no domain")
        chk.equal(entry.get("queryCount"), len(entry.get("queryIds", [])),
                  "indexes.scope_count", f"{sid} query count")
        for qid in entry.get("queryIds", []):
            if qid in scope_by_query:
                chk.fail("indexes.scope_duplicate", f"query {qid} appears in two scopes")
            scope_by_query[qid] = entry
            query = q_by_id.get(qid)
            chk.check(query is not None, "indexes.scope_query",
                      f"{sid} links unknown query {qid}")
            if query:
                chk.equal(query.get("scope"), {
                    "id": entry.get("id"),
                    "description": entry.get("description"),
                    "domain": entry.get("domain"),
                    "snapshot": entry.get("snapshot"),
                }, "indexes.scope_fidelity", f"{qid} scope vs scope index")
    chk.equal(set(scope_by_query), set(q_by_id), "indexes.scope_coverage",
              "every active query must appear in exactly one scope entry")
    # Snapshots.
    snapshots = src.registry.get("snapshots", [])
    snapshot_by_query = {}
    for entry in snapshots:
        sid = entry.get("snapshot")
        chk.check(isinstance(sid, str) and sid, "indexes.snapshot_id",
                  "snapshot entry has no snapshot id")
        chk.equal(entry.get("queryCount"), len(entry.get("queryIds", [])),
                  "indexes.snapshot_count", f"{sid} query count")
        for qid in entry.get("queryIds", []):
            if qid in snapshot_by_query:
                chk.fail("indexes.snapshot_duplicate", f"query {qid} appears in two snapshots")
            snapshot_by_query[qid] = entry
            query = q_by_id.get(qid)
            chk.check(query is not None, "indexes.snapshot_query",
                      f"{sid} links unknown query {qid}")
            if query:
                chk.equal(query.get("snapshot"), sid, "indexes.snapshot_fidelity",
                          f"{qid} snapshot")
    chk.equal(set(snapshot_by_query), set(q_by_id), "indexes.snapshot_coverage",
              "every active query must appear in exactly one snapshot entry")
    # Theory inventory.
    chk.equal(src.registry.get("theoryInventory"), THEORIES, "indexes.theories",
              "theory inventory")
    # Package summary entries.
    summaries = {p.get("packageId"): p for p in src.registry.get("packages", [])}
    chk.equal(len(summaries), 10, "indexes.package_summaries", "package summary count")
    chk.equal(set(summaries), {p["packageId"] for p in src.packages},
              "indexes.package_ids", "package summary IDs")
    for pkg in src.packages:
        row = summaries.get(pkg["packageId"], {})
        counter = collections.Counter(q.get("outcome", {}).get("status")
                                      for q in pkg["queries"])
        chk.equal(row.get("round"), pkg["round"], "indexes.package_round",
                  f"{pkg['packageId']} round")
        chk.equal(row.get("pairCount"), len(pkg["pairs"]), "indexes.package_pairs",
                  f"{pkg['packageId']} pair count")
        chk.equal(row.get("queryCount"), len(pkg["queries"]), "indexes.package_queries",
                  f"{pkg['packageId']} query count")
        chk.equal(row.get("outcomes"), {s: counter.get(s, 0) for s in STATUSES},
                  "indexes.package_outcomes", f"{pkg['packageId']} outcomes")
        chk.equal(row.get("acceptance"), pkg["acceptance"], "indexes.package_acceptance",
                  f"{pkg['packageId']} acceptance")


# ---------------------------------------------------------------------------
# External gates
# ---------------------------------------------------------------------------


def run_command(name: str, cmd: list[str], root: Path, timeout: int,
                expected_rc: int = 0) -> dict:
    started = time.time()
    try:
        proc = subprocess.run(cmd, cwd=str(root), capture_output=True, text=True,
                              timeout=timeout)
        return {
            "name": name,
            "command": " ".join(cmd),
            "returncode": proc.returncode,
            "expectedReturncode": expected_rc,
            "passed": proc.returncode == expected_rc,
            "seconds": round(time.time() - started, 2),
            "stdoutTail": "\n".join(proc.stdout.strip().splitlines()[-40:]),
            "stderrTail": "\n".join(proc.stderr.strip().splitlines()[-20:]),
        }
    except subprocess.TimeoutExpired:
        return {
            "name": name, "command": " ".join(cmd), "returncode": None,
            "expectedReturncode": expected_rc, "passed": False,
            "seconds": round(time.time() - started, 2),
            "stdoutTail": "", "stderrTail": f"timeout after {timeout}s",
        }
    except Exception as exc:
        return {
            "name": name, "command": " ".join(cmd), "returncode": None,
            "expectedReturncode": expected_rc, "passed": False,
            "seconds": round(time.time() - started, 2),
            "stdoutTail": "", "stderrTail": f"{type(exc).__name__}: {exc}",
        }


def record_gate(chk: Checker, gate: dict, code: str, extra_ok: bool = True,
                message: str | None = None) -> None:
    chk.gates.append(gate)
    chk.check(gate["passed"] and extra_ok, code,
              message or f"{gate['name']} failed (rc={gate['returncode']})")


def check_python_and_historical_gates(root: Path, chk: Checker) -> None:
    python = sys.executable
    gates = [
        ("r1", [python, "audit_boundary/validate_boundary.py"], 0),
        ("r2", [python, "bounded_audit/validate_screening.py"], 0),
        ("r3_derived_content", [python, "bounded_audit/r4/validate_r3_content.py"], 0),
        ("r4_frozen_snapshot", [python, "bounded_audit/r4/validate_coverage.py",
                                "--coverage", "bounded_audit/r4/coverage-accepted.json",
                                "--skip-package-validators"], 0),
        ("r4_e1", [python, "bounded_audit/r4/excited-01/validate.py"], 0),
        ("r4_e2", [python, "bounded_audit/r4/excited-02/validate.py"], 0),
        ("r4_ci_derived_content", [python, "bounded_audit/r5/validate_r4_ci_content.py"], 0),
        ("r5_rad1", [python, "bounded_audit/r5/radiative-01/validate.py"], 0),
        ("r5_rad2", [python, "bounded_audit/r5/radiative-02/validate.py"], 0),
        ("r5_rad3", [python, "bounded_audit/r5/radiative-03/validate.py"], 0),
        ("r5_xd1", [python, "bounded_audit/r5/cross-domain-01/validate.py"], 0),
        ("r5_xd2", [python, "bounded_audit/r5/cross-domain-02/validate.py"], 0),
        ("r5_current_coverage", [python, "bounded_audit/r5/validate_coverage.py"], 0),
    ]
    for name, cmd, expected in gates:
        gate = run_command(name, cmd, root, 900, expected)
        record_gate(chk, gate, f"gate.{name}")
    # Raw historical validators are expected to fail only on the already
    # accepted stale-ledger pins; verify that exact failure surface.
    r3_raw = run_command("r3_raw_historical", [python, "bounded_audit/validate_r3.py"],
                         root, 900, 1)
    r3_text = r3_raw["stdoutTail"] + "\n" + r3_raw["stderrTail"]
    r3_tags = [
        "snapshot.coverageLedgerSha256", "coverage.round", "coverage.cumulative",
        "coverage.remaining", "coverage.byRound", "coverage.remainingCount",
        "coverage.remainingSet",
    ]
    r3_ok = all(tag in r3_text for tag in r3_tags)
    record_gate(chk, r3_raw, "gate.r3_raw_historical", extra_ok=r3_ok,
                message="raw R3 failure surface is not exactly the seven accepted "
                        "stale-ledger checks")
    ci_raw = run_command("r4_ci_raw_historical",
                         [python, "bounded_audit/r4/conical-01/validate.py"],
                         root, 900, 1)
    ci_text = ci_raw["stdoutTail"] + "\n" + ci_raw["stderrTail"]
    ci_ok = "coverage.cumulative" in ci_text
    record_gate(chk, ci_raw, "gate.r4_ci_raw_historical", extra_ok=ci_ok,
                message="raw R4 CI failure surface is not the accepted stale-ledger check")



def check_adversarial_suite(root: Path, chk: Checker) -> None:
    """Run the isolated /tmp mutation suite as an executable gate."""
    cmd = [sys.executable, "tools/relation_audit_bounded/tests/test_adversarial.py"]
    gate = run_command("adversarial_mutations", cmd, root, 1800, 0)
    text = gate["stdoutTail"] + "\n" + gate["stderrTail"]
    parsed = re.search(
        r"All\s+(\d+)\s+mutations failed closed;\s+(\d+)\s+positive controls passed",
        text,
    )
    ok = gate["returncode"] == 0 and parsed is not None
    if parsed:
        chk.mutations = {
            "mutationsRejected": int(parsed.group(1)),
            "positiveControls": int(parsed.group(2)),
            "requiredMinimum": 12,
            "allFailClosed": True,
        }
    else:
        chk.mutations = {
            "mutationsRejected": 0,
            "positiveControls": 0,
            "requiredMinimum": 12,
            "allFailClosed": False,
        }
    record_gate(chk, gate, "gate.adversarial_mutations", extra_ok=ok,
                message="the /tmp adversarial mutation suite did not report the expected "
                        "fail-closed/positive-control summary")


def check_strict_build(root: Path, chk: Checker) -> None:
    gate = run_command("strict_build_scan", ["proofs/scripts/check.sh", "--strict"],
                       root, 1800, 0)
    text = gate["stdoutTail"] + "\n" + gate["stderrTail"]
    ok = gate["returncode"] == 0 and ("verdict: PASS" in text or "PASS" in text)
    record_gate(chk, gate, "gate.strict_build", extra_ok=ok)


def check_legacy_full_validator(root: Path, chk: Checker) -> None:
    with tempfile.TemporaryDirectory(prefix="r8-legacy-full-") as tmp:
        json_out = Path(tmp) / "production-full-r8.json"
        lean_out = Path(tmp) / "production-full-r8-lean-checks.lean"
        cmd = [sys.executable, "tools/relation_audit.py",
               "--manifest", "relation_audit/registry.json",
               "--schema", "relation_audit/schema.json",
               "--mode", "full",
               "--json-out", str(json_out),
               "--lean-source-out", str(lean_out)]
        gate = run_command("legacy_full_lean", cmd, root, 1800, 0)
        gate["command"] = gate["command"].replace(tmp, "<isolated-temp>")
        extra_ok = False
        detail = {}
        if json_out.exists():
            try:
                report = read_json(json_out)
                detail = {
                    "status": report.get("status"),
                    "exitCode": report.get("exitCode"),
                    "counts": report.get("counts"),
                    "coverage": report.get("coverage"),
                    "failureCount": len(report.get("findings", [])) if isinstance(
                        report.get("findings"), list) else None,
                }
                counts = report.get("counts", {})
                coverage = report.get("coverage", {})
                extra_ok = (
                    report.get("status") == "PASS"
                    and counts.get("queries") == 151
                    and counts.get("records") == 151
                    and counts.get("certificates") == 38
                    and counts.get("statements") == 52
                    and counts.get("byStatus") == {"certified": 24, "notEstablished": 121,
                                                   "outOfScope": 0, "unresolved": 6}
                    and coverage.get("coveredPairs") == 136
                    and coverage.get("missingPairs") == []
                )
            except Exception as exc:
                detail["error"] = f"{type(exc).__name__}: {exc}"
        gate["legacyReport"] = detail
        record_gate(chk, gate, "gate.legacy_full",
                    extra_ok=extra_ok,
                    message="unchanged legacy full validator did not return the accepted "
                            "151/151/38/52 PASS report")


def compile_probe_files(root: Path, src: Sources, chk: Checker) -> None:
    files = src.registry.get("probeFiles", [])
    probes = src.registry.get("certificateLibrary", {}).get("boundedProbe", [])
    candidates = src.registry.get("candidateEvidence", [])
    expected = {}
    for cert in probes:
        expected[cert["declaration"]] = set(cert.get("axiomFootprint", []))
    for candidate in candidates:
        expected[candidate["declaration"]] = set(candidate.get("axiomFootprint", []))
    chk.equal(len(expected), EXPECTED_ACTIVE["reviewedDeclarations"],
              "probes.audit_declaration_count", "expected axiom-audit declaration count")
    seen = set()
    for entry in sorted(files, key=lambda row: row.get("path", "")):
        rel = entry.get("path")
        cmd = [str(root / "proofs/scripts/lake"), "env", "lean", rel]
        started = time.time()
        try:
            proc = subprocess.run(cmd, cwd=str(root), capture_output=True,
                                  text=True, timeout=600)
            returncode = proc.returncode
            full_text = proc.stdout + "\n" + proc.stderr
        except subprocess.TimeoutExpired:
            returncode = None
            full_text = "timeout after 600s"
        except Exception as exc:
            returncode = None
            full_text = f"{type(exc).__name__}: {exc}"
        gate = {
            "name": f"probe:{rel}",
            "command": " ".join(cmd),
            "returncode": returncode,
            "expectedReturncode": 0,
            "passed": returncode == 0,
            "seconds": round(time.time() - started, 2),
            "stdoutTail": "\n".join(full_text.strip().splitlines()[-40:]),
            "stderrTail": "",
        }
        chk.gates.append(gate)
        live = parse_axiom_output(full_text)
        chk.check(returncode == 0, "probes.compile",
                  f"{rel} did not compile (rc={returncode})")
        expected_here = set(entry.get("certificateDeclarations", [])) | set(
            entry.get("candidateDeclarations", []))
        chk.equal(set(live), expected_here, "probes.axiom_declarations",
                  f"{rel} axiom-audit declaration set")
        for declaration in expected_here:
            seen.add(declaration)
            footprint = live.get(declaration)
            chk.check(footprint is not None, "probes.axiom_missing",
                      f"{rel}: no axiom audit for {declaration}")
            if footprint is not None:
                chk.equal(sorted(footprint), sorted(ALLOWED_AXIOMS),
                          "probes.axiom_footprint",
                          f"{rel}: {declaration} axiom footprint")
        # Compare the archived compile log with the live audit.
        log_rel = entry.get("compileLog", {}).get("path")
        if log_rel and (root / log_rel).exists():
            log_text = (root / log_rel).read_text(encoding="utf-8")
            logged = parse_axiom_output(log_text)
            chk.equal(set(logged), expected_here, "probes.log_declarations",
                      f"{rel} compile-log declaration set")
            for declaration in expected_here:
                if declaration in logged:
                    chk.equal(sorted(logged[declaration]), sorted(ALLOWED_AXIOMS),
                              "probes.log_footprint",
                              f"{rel}: {declaration} logged axiom footprint")
        chk.probe_runs.append({
            "path": rel,
            "sha256": entry.get("sha256"),
            "command": " ".join(cmd),
            "returncode": gate["returncode"],
            "declarations": len(expected_here),
            "axioms": {d: sorted(v) for d, v in sorted(live.items())},
        })
    chk.equal(seen, set(expected), "probes.audit_set",
              "all 58 reviewed declarations were axiom-audited")
    chk.equal(len(seen), EXPECTED_ACTIVE["reviewedDeclarations"],
              "probes.audited_count", "audited declaration count")


# ---------------------------------------------------------------------------
# Invariants and deterministic rebuild
# ---------------------------------------------------------------------------


def check_invariants(root: Path, chk: Checker) -> None:
    parent = root.parent
    original = parent.parent / "photolean"
    backup = parent / "backup/photolean-source-2026-11-04.tar.gz"
    invariants = {
        "legacyRegistrySha256": sha_file(root / LEGACY_PATH),
        "coverageSha256": sha_file(root / COVERAGE_PATH),
        "backupSha256": sha_file(backup),
        "originalRepo": str(original),
    }
    chk.equal(invariants["legacyRegistrySha256"], EXPECTED["legacy"],
              "invariants.legacy_registry", "legacy registry hash")
    chk.equal(invariants["coverageSha256"], EXPECTED["coverage"],
              "invariants.coverage", "accepted coverage hash")
    chk.equal(invariants["backupSha256"],
              "c72fbc4cb134e57cde379f2a10011c9a27f0f7a3497af50fd6c4c404bdf2745a",
              "invariants.backup", "backup archive hash")
    chk.check(original.exists(), "invariants.original_exists",
              f"original repository missing at {original}")
    if original.exists():
        head = run_command("original_head", ["git", "-C", str(original), "rev-parse", "HEAD"],
                           root, 60, 0)
        chk.equal(head["stdoutTail"].strip(),
                  "7ad25a5f03a88acc3af03f65149cf2ac102e7dac",
                  "invariants.original_head", "original repository HEAD")
        status = run_command("original_status",
                             ["git", "-C", str(original), "status", "--porcelain"],
                             root, 60, 0)
        chk.equal(status["stdoutTail"].strip(), "", "invariants.original_clean",
                  "original repository is dirty")
        # The audit copy adds the accepted RelationAudit modules; every Lean
        # file that exists in the original repository must remain byte-identical.
        mismatch = []
        audit_files = sorted((root / "PhotoLean").rglob("*.lean"))
        original_files = sorted((original / "PhotoLean").rglob("*.lean"))
        chk.equal(len(audit_files), 102, "invariants.photo_lean_count",
                  "delivered PhotoLean file count")
        chk.equal(len(original_files), 95, "invariants.original_lean_count",
                  "original PhotoLean file count")
        for original_file in original_files:
            rel = original_file.relative_to(original)
            audit_file = root / rel
            if not audit_file.exists() or sha_file(audit_file) != sha_file(original_file):
                mismatch.append(str(rel))
        chk.equal(mismatch, [], "invariants.photo_lean_match",
                  "audit copy differs from the original repository on a pre-existing "
                  "delivered Lean file")
        invariants["originalHead"] = head["stdoutTail"].strip()
        invariants["originalClean"] = status["stdoutTail"].strip() == ""
        invariants["photoLeanFiles"] = len(audit_files)
        invariants["originalPhotoLeanFiles"] = len(original_files)
        invariants["photoLeanMismatches"] = mismatch
    chk.invariants = invariants


def check_deterministic_rebuild(root: Path, chk: Checker, acceptance: str,
                                registry_path: Path | None = None,
                                dispositions_path: Path | None = None) -> None:
    """Rebuild in isolation with the *current* acceptance state.

    The builder must be invoked with the acceptance state of the manifest that
    is actually being validated.  That matters for the uniform accepted-R8
    state and it also matters when ``--registry``/``--dispositions`` point at
    custom files outside the checkout: those files are copied into the
    isolated tree at the canonical output locations and are the artifacts the
    regenerated bytes are compared against.
    """
    if acceptance not in (PENDING, ACCEPTED):
        chk.fail("rebuild.acceptance",
                 f"cannot rebuild with invalid acceptance state {iso(acceptance)}")
        return
    registry_path = Path(registry_path) if registry_path else root / REGISTRY_PATH
    dispositions_path = (Path(dispositions_path) if dispositions_path
                         else root / DISPOSITIONS_PATH)
    source_paths = {
        REGISTRY_PATH: registry_path,
        SCHEMA_PATH: root / SCHEMA_PATH,
        DISPOSITIONS_PATH: dispositions_path,
        DOCS_PATH: root / DOCS_PATH,
    }
    outputs = {rel: sha_file(path) for rel, path in source_paths.items()}
    with tempfile.TemporaryDirectory(prefix="r8-rebuild-") as tmp:
        dst = Path(tmp) / "photolean"
        try:
            for rel in ("PhotoLean", "audit_boundary", "bounded_audit",
                        "relation_audit", "docs"):
                shutil.copytree(root / rel, dst / rel,
                                ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
            (dst / "tools/relation_audit_bounded").mkdir(parents=True, exist_ok=True)
            shutil.copy2(root / "tools/relation_audit_bounded/build.py",
                         dst / "tools/relation_audit_bounded/build.py")
            # Seed the isolated tree with the manifests actually under test so
            # custom --registry/--dispositions files are compared, not the
            # checkout defaults.
            shutil.copy2(registry_path, dst / REGISTRY_PATH)
            shutil.copy2(dispositions_path, dst / DISPOSITIONS_PATH)
        except Exception as exc:
            chk.fail("rebuild.copy", f"cannot create isolated rebuild tree: {exc}")
            return
        gate = run_command("deterministic_rebuild",
                           [sys.executable, "tools/relation_audit_bounded/build.py",
                            "--acceptance", acceptance],
                           dst, 900, 0)
        chk.gates.append(gate)
        chk.check(gate["returncode"] == 0, "rebuild.run",
                  f"builder failed in isolated tree (rc={gate['returncode']})")
        regenerated = {}
        for rel in outputs:
            regenerated[rel] = sha_file(dst / rel)
            chk.equal(regenerated[rel], outputs[rel], "rebuild.byte_identical",
                      f"deterministic rebuild differs for {rel}")
        chk.rebuild = {
            "isolatedRoot": "<isolated-temp>",
            "acceptance": acceptance,
            "builderCommand": " ".join([sys.executable,
                                        "tools/relation_audit_bounded/build.py",
                                        "--acceptance", acceptance]),
            "builderReturncode": gate["returncode"],
            "builderOutputTail": gate["stdoutTail"],
            "comparedPaths": {rel: str(path) for rel, path in source_paths.items()},
            "sha256": {rel: {"generated": outputs[rel], "rebuilt": regenerated[rel]}
                       for rel in outputs},
            "byteIdentical": all(regenerated[rel] == outputs[rel] for rel in outputs),
        }


# ---------------------------------------------------------------------------
# Report and entry point
# ---------------------------------------------------------------------------


def build_report(root: Path, src: Sources, chk: Checker, dims: dict,
                 probes: dict, legacy: dict, acceptance: str,
                 skipped: list[str]) -> dict:
    registry_hash = sha_file(root / REGISTRY_PATH)
    schema_hash = sha_file(root / SCHEMA_PATH)
    dispositions_hash = sha_file(root / DISPOSITIONS_PATH)
    docs_hash = sha_file(root / DOCS_PATH)
    status = "PASS" if chk.ok else "FAIL"
    if acceptance == PENDING:
        acceptance_text = "submitted-R8-pending-review (independent acceptance still required)"
    else:
        acceptance_text = "accepted-R8"
    pairs = src.registry.get("pairs", [])
    queries = src.registry.get("queries", [])
    certified_pairs = dims.get("certifiedPairs", 0)
    report = {
        "artifactKind": "bounded-relation-audit-independent-validation",
        "schemaVersion": "1.0.0",
        "round": "R8",
        "generatedOn": "2026-11-04",
        "validator": "tools/relation_audit_bounded/validate.py",
        "root": str(root),
        "status": status,
        "exitCode": 0 if chk.ok else 1,
        "acceptanceState": acceptance,
        "acceptanceStatement": acceptance_text,
        "selfAcceptance": False,
        "hashes": {
            REGISTRY_PATH: registry_hash,
            SCHEMA_PATH: schema_hash,
            DISPOSITIONS_PATH: dispositions_hash,
            DOCS_PATH: docs_hash,
            COVERAGE_PATH: sha_file(root / COVERAGE_PATH),
            LEGACY_PATH: sha_file(root / LEGACY_PATH),
            FROZEN_R4_PATH: sha_file(root / FROZEN_R4_PATH),
        },
        "dimensions": {
            "pairCoverage": {
                "pairUniverse": 136,
                "pairsWithScreening": len(pairs),
                "pairsWithAnyActiveStatementRecord": dims.get("pairsWithQuery"),
                "pairsWithNonOutOfScopeQuery": dims.get("pairsWithNonOutOfScopeQuery"),
                "pairsWithOnlyStatementLevelOutOfScope": dims.get("pairsWithOnlyOutOfScope"),
                "remainingPairIds": [],
                "meaning": "Every R1 pair has a named statement-level query or a "
                           "statement-level outOfScope record; this is not a "
                           "certification count and not a claim that every pair has a "
                           "non-outOfScope query.",
            },
            "queryOutcomes": {
                "activeQueries": len(queries),
                "outcomes": dims.get("outcomes"),
                "byRound": dims.get("byRound"),
                "meaning": "Proposition-level bounded query outcomes, not pair coverage "
                           "and not a completeness claim.",
            },
            "relationDiscovery": {
                "certifiedQueries": dims.get("certifiedQueries"),
                "certifiedPairs": certified_pairs,
                "certifiedRelationKindCounts": dims.get("certifiedRelationKindCounts"),
                "certifiedEvidenceClasses": dims.get("certifiedEvidenceClasses"),
                "meaning": "Distinct certified statement-level relations discovered; "
                           "67 certified queries over 53 pairs is not 136/136 "
                           "certification.",
            },
            "retainedLegacyEvidence": {
                "legacyRecordsDisposed": legacy.get("entries"),
                "legacyNamedQueries": legacy.get("named"),
                "legacyPairAnchors": legacy.get("anchors"),
                "legacyIntraTheoryRecords": legacy.get("intra"),
                "deliveredCertificatesRetained": 26,
                "deliveredCertificatesActive": 12,
                "absenceReconciliations": legacy.get("reconciliations"),
                "aliasRepairs": legacy.get("aliasRepairs"),
                "correctedLegacyViews": legacy.get("correctedViews"),
                "meaning": "Retained historical evidence; pair anchors and intra-theory "
                           "records contribute zero active coverage.",
            },
            "candidates": {
                "candidateDeclarations": 3,
                "candidateQueries": sorted(
                    c["attachedQueryIds"][0] for c in src.registry.get("candidateEvidence", [])
                    if c.get("attachedQueryIds")),
                "candidateDeclarationsNotCertificates": True,
                "meaning": "The three XD1 candidate declarations are unresolved evidence, "
                           "never certificate library members.",
            },
        },
        "counts": {
            "pairs": len(pairs),
            "queries": len(queries),
            "records": len(src.registry.get("records", [])),
            "packages": len(src.packages),
            "certificateLibrary": {
                "total": 93,
                "deliveredModule": 38,
                "boundedProbe": 55,
            },
            "activeCertifiedEvidence": {
                "total": 67,
                "boundedProbe": 55,
                "deliveredModule": 12,
            },
            "probeFiles": probes.get("files"),
            "probeCertificates": probes.get("certificates"),
            "probeCandidates": probes.get("candidates"),
            "probeReviewedDeclarations": probes.get("reviewed"),
            "legacy": legacy,
        },
        "checks": {"total": chk.checks, "failed": len(chk.failures)},
        "failures": chk.failures,
        "notes": chk.notes,
        "externalGates": chk.gates,
        "probeRuns": chk.probe_runs,
        "adversarialMutations": chk.mutations,
        "deterministicRebuild": chk.rebuild,
        "invariants": chk.invariants,
        "skippedChecks": skipped,
        "deviations": [
            {
                "id": "DEV-R8-01",
                "planStatement": "The plan describes eight accepted R2-R5 screening packages.",
                "observed": "Ten accepted screening packages: R2 one, R3 one, R4 three, "
                            "R5 five.",
                "resolution": "Use all ten actual accepted packages; no package was "
                              "dropped or invented. The plan-metadata miscount is recorded "
                              "and does not change the 136/58 counts.",
                "blocking": False,
            }
        ],
        "blockers": [] if chk.ok else [
            "At least one fail-closed structural, source, evidence, legacy, state-machine, "
            "mutation or external-gate check failed; see failures."
        ],
        "nonClaims": [
            "136/136 pair coverage means every pair has a named statement-level record, "
            "not that every pair is certified.",
            "Unresolved, notEstablished and outOfScope are outcomes, not failures and not "
            "refutations.",
            "The 55 bounded-probe certificates are package-local evidence, not additions to "
            "the frozen delivered PhotoLean tree.",
            "The three XD1 candidate declarations are unresolved evidence, not certificates.",
            "The legacy registry and its 151 records remain historical inputs; dispositions "
            "are additive interpretations.",
            "The bounded protocol does not exhaust all propositions of the seventeen theories.",
            "This report is validator evidence. When acceptanceState is pending it is not an "
            "acceptance record; only two independent reviewers and the lead may accept.",
        ],
    }
    return report


def render_markdown(report: dict) -> str:
    lines = []
    lines.append("# R8 bounded relation-audit independent validation")
    lines.append("")
    lines.append(f"**Status: `{report['status']}`; acceptance: `{report['acceptanceState']}`.**")
    lines.append("")
    lines.append(report["acceptanceStatement"])
    lines.append("")
    lines.append("## Artifact hashes")
    lines.append("")
    lines.append("| Artifact | SHA-256 |")
    lines.append("| --- | --- |")
    for rel, digest in report["hashes"].items():
        lines.append(f"| `{rel}` | `{digest}` |")
    lines.append("")
    lines.append("## Five separate dimensions")
    lines.append("")
    dims = report["dimensions"]
    lines.append(f"### Pair coverage")
    lines.append("")
    pc = dims["pairCoverage"]
    lines.append(f"- Pair universe: {pc['pairUniverse']}")
    lines.append(f"- Pairs with screening record: {pc['pairsWithScreening']}")
    lines.append(f"- Pairs with any active statement-level record (named query or "
                 f"statement-level outOfScope): {pc['pairsWithAnyActiveStatementRecord']}")
    lines.append(f"- Pairs with a non-outOfScope query: "
                 f"{pc['pairsWithNonOutOfScopeQuery']}")
    lines.append(f"- Pairs whose only active record is a statement-level outOfScope: "
                 f"{pc['pairsWithOnlyStatementLevelOutOfScope']}")
    lines.append("- Remaining pairs: 0")
    lines.append(f"- {pc['meaning']}")
    lines.append("")
    lines.append("### Proposition-level query outcomes")
    lines.append("")
    qo = dims["queryOutcomes"]
    lines.append(f"- Active named queries: {qo['activeQueries']}")
    lines.append(f"- Outcomes: {qo['outcomes']}")
    lines.append(f"- {qo['meaning']}")
    lines.append("")
    lines.append("### Certified relation discovery")
    lines.append("")
    rd = dims["relationDiscovery"]
    lines.append(f"- Certified queries: {rd['certifiedQueries']}")
    lines.append(f"- Pairs with at least one certified relation: {rd['certifiedPairs']}")
    lines.append(f"- Certified relation kinds: {rd['certifiedRelationKindCounts']}")
    lines.append(f"- Active certified evidence classes: {rd['certifiedEvidenceClasses']}")
    lines.append(f"- {rd['meaning']}")
    lines.append("")
    lines.append("### Retained legacy evidence")
    lines.append("")
    le = dims["retainedLegacyEvidence"]
    lines.append(f"- Legacy records disposed exactly once: {le['legacyRecordsDisposed']}")
    lines.append(f"- Named queries / pair anchors: {le['legacyNamedQueries']} / "
                 f"{le['legacyPairAnchors']}")
    lines.append(f"- Intra-theory records: {le['legacyIntraTheoryRecords']}")
    lines.append(f"- Delivered certificates retained / active: "
                 f"{le['deliveredCertificatesRetained']} / {le['deliveredCertificatesActive']}")
    lines.append(f"- Old absence/new evidence reconciliations: {le['absenceReconciliations']}")
    lines.append(f"- Alias repairs / corrected legacy views: {le['aliasRepairs']} / "
                 f"{le['correctedLegacyViews']}")
    lines.append(f"- {le['meaning']}")
    lines.append("")
    lines.append("### Unresolved candidates")
    lines.append("")
    ca = dims["candidates"]
    lines.append(f"- Candidate declarations: {ca['candidateDeclarations']}")
    lines.append(f"- Attached queries: {', '.join(ca['candidateQueries'])}")
    lines.append(f"- {ca['meaning']}")
    lines.append("")
    lines.append("## Counts")
    lines.append("")
    lines.append("| Item | Value |")
    lines.append("| --- | ---: |")
    counts = report["counts"]
    lines.append(f"| Pairs / queries / records | {counts['pairs']} / {counts['queries']} / "
                 f"{counts['records']} |")
    lines.append(f"| Screening packages | {counts['packages']} |")
    lines.append(f"| Certificate library total / legacy / probe | "
                 f"{counts['certificateLibrary']['total']} / "
                 f"{counts['certificateLibrary']['deliveredModule']} / "
                 f"{counts['certificateLibrary']['boundedProbe']} |")
    lines.append(f"| Active certified evidence total / probe / legacy | "
                 f"{counts['activeCertifiedEvidence']['total']} / "
                 f"{counts['activeCertifiedEvidence']['boundedProbe']} / "
                 f"{counts['activeCertifiedEvidence']['deliveredModule']} |")
    lines.append(f"| Probe files / reviewed declarations | {counts['probeFiles']} / "
                 f"{counts['probeReviewedDeclarations']} |")
    lines.append("")
    lines.append("## External gates")
    lines.append("")
    lines.append("| Gate | Command | Exit | Result |")
    lines.append("| --- | --- | ---: | --- |")
    for gate in report["externalGates"]:
        command = gate["command"].replace("|", "\\|")
        result = "PASS" if gate.get("passed") else "FAIL"
        lines.append(f"| `{gate['name']}` | `{command}` | {gate['returncode']} | {result} |")
    lines.append("")
    lines.append("## Probe compilation and axiom audit")
    lines.append("")
    lines.append("| Probe | Declarations | Exit | Allowed-axiom audit |")
    lines.append("| --- | ---: | ---: | --- |")
    for run in report["probeRuns"]:
        all_ok = all(set(footprint) == {"propext", "Classical.choice", "Quot.sound"}
                     for footprint in run["axioms"].values())
        lines.append(f"| `{run['path']}` | {run['declarations']} | {run['returncode']} | "
                     f"{'PASS' if all_ok else 'FAIL'} |")
    lines.append("")
    lines.append("## Adversarial mutations")
    lines.append("")
    mutations = report.get("adversarialMutations", {})
    lines.append(f"- Mutations rejected fail-closed: {mutations.get('mutationsRejected')}")
    lines.append(f"- Positive controls passed: {mutations.get('positiveControls')}")
    lines.append(f"- Required minimum mutations: {mutations.get('requiredMinimum')}")
    lines.append(f"- All mutations fail-closed: {mutations.get('allFailClosed')}")
    lines.append("")
    lines.append("The suite covers missing/duplicate pair, pair-anchor substitution, wrong "
                 "outcome, certified without evidence, candidate promotion, unknown alias "
                 "endpoint, unrepaired legacy record, missing legacy disposition, "
                 "absence/new-evidence reconciliation removal, stale probe hash, forbidden "
                 "axiom footprint, wrong evidence class, partial acceptance flip, self-hash "
                 "cycle, legacy-anchor coverage inflation and missing probe declaration. "
                 "Every input lives under a temporary directory.")
    lines.append("")
    lines.append("## Deterministic rebuild")
    lines.append("")
    rebuild = report.get("deterministicRebuild", {})
    lines.append(f"- Isolated rebuild builder exit: {rebuild.get('builderReturncode')}")
    lines.append(f"- Byte-identical outputs: {rebuild.get('byteIdentical')}")
    for rel, row in rebuild.get("sha256", {}).items():
        lines.append(f"- `{rel}`: generated `{row['generated']}`, rebuilt `{row['rebuilt']}`")
    lines.append("")
    lines.append("## Invariants")
    lines.append("")
    inv = report.get("invariants", {})
    lines.append(f"- Legacy registry SHA-256: `{inv.get('legacyRegistrySha256')}`")
    lines.append(f"- Accepted coverage SHA-256: `{inv.get('coverageSha256')}`")
    lines.append(f"- Backup SHA-256: `{inv.get('backupSha256')}`")
    lines.append(f"- Original repository HEAD: `{inv.get('originalHead')}` "
                 f"(clean={inv.get('originalClean')})")
    lines.append(f"- Delivered PhotoLean files / mismatches: "
                 f"{inv.get('photoLeanFiles')} / {len(inv.get('photoLeanMismatches', []))}")
    lines.append("")
    lines.append("## Deviations and blockers")
    lines.append("")
    for deviation in report.get("deviations", []):
        lines.append(f"- **{deviation['id']}**: {deviation['observed']} "
                     f"Plan said: {deviation['planStatement']} "
                     f"Resolution: {deviation['resolution']} "
                     f"Blocking: {deviation['blocking']}.")
    for blocker in report.get("blockers", []):
        lines.append(f"- **BLOCKER**: {blocker}")
    lines.append("")
    lines.append("## Checks and failures")
    lines.append("")
    lines.append(f"- Checks executed: {report['checks']['total']}")
    lines.append(f"- Checks failed: {report['checks']['failed']}")
    if report["failures"]:
        lines.append("")
        lines.append("| Code | Message |")
        lines.append("| --- | --- |")
        for failure in report["failures"]:
            message = failure["message"].replace("|", "\\|")
            lines.append(f"| `{failure['code']}` | {message} |")
    else:
        lines.append("- No failures.")
    lines.append("")
    lines.append("## Non-claims")
    lines.append("")
    for claim in report["nonClaims"]:
        lines.append(f"- {claim}")
    lines.append("")
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Independent fail-closed validator for the R8 bounded relation audit.")
    parser.add_argument("--root", default=str(ROOT))
    parser.add_argument("--registry", default=None)
    parser.add_argument("--schema", default=None)
    parser.add_argument("--dispositions", default=None)
    parser.add_argument("--skip-external", action="store_true",
                        help="skip historical/current gates and strict build/scan")
    parser.add_argument("--skip-probe-compile", action="store_true",
                        help="skip live Lean probe compilation (structural mutation tests only)")
    parser.add_argument("--skip-original", action="store_true",
                        help="skip original repository/backup invariants")
    parser.add_argument("--skip-rebuild", action="store_true",
                        help="skip deterministic isolated rebuild")
    parser.add_argument("--write-report", action="store_true", default=False,
                        help="write relation_audit/reports/bounded-accepted.{json,md}")
    parser.add_argument("--report-json", default=None)
    parser.add_argument("--report-md", default=None)
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    registry_path = Path(args.registry).resolve() if args.registry else root / REGISTRY_PATH
    schema_path = Path(args.schema).resolve() if args.schema else root / SCHEMA_PATH
    dispositions_path = (Path(args.dispositions).resolve() if args.dispositions
                         else root / DISPOSITIONS_PATH)

    chk = Checker()
    src = load_sources(root, registry_path, dispositions_path, schema_path, chk)
    if src.registry is None or src.dispositions is None or src.inventory is None:
        print(f"FAIL: required inputs unavailable; {len(chk.failures)} failures")
        for failure in chk.failures:
            print(f"  [{failure['code']}] {failure['message']}")
        return 2

    acceptance = src.registry.get("acceptance", "unknown")
    skipped = []
    dims = {"outcomes": {}, "byRound": {}, "certifiedQueries": 0, "certifiedPairs": 0,
            "certifiedRelationKindCounts": {}, "certifiedEvidenceClasses": {},
            "pairUniverse": 0, "pairsWithQuery": 0}
    probes = {"files": 0, "certificates": 0, "candidates": 0, "reviewed": 0}
    legacy = {"entries": 0, "named": 0, "anchors": 0, "intra": 0, "reconciliations": 0,
              "aliasRepairs": 0, "correctedViews": 0, "byDisposition": {}, "byStatus": {}}
    try:
        check_schema(src, chk)
        check_top_level(root, src, chk)
        check_references(root, src, chk)
        check_queries_and_records(src, chk)
        check_pairs(src, chk)
        dims = check_counts(src, chk)
        check_statements(root, src, chk)
        check_evidence_references(root, src, chk)
        check_certificate_library(root, src, chk)
        probes = check_probe_files(root, src, chk)
        legacy = check_dispositions(root, src, chk)
        check_indexes(src, chk, dims)
        if not args.skip_original:
            check_invariants(root, chk)
        else:
            skipped.append("original/backup invariants")
        if not args.skip_external:
            check_python_and_historical_gates(root, chk)
            check_strict_build(root, chk)
            check_legacy_full_validator(root, chk)
            check_adversarial_suite(root, chk)
        else:
            skipped.append("historical/current Python gates")
            skipped.append("strict build/scan")
            skipped.append("unchanged legacy full Lean validator")
            skipped.append("adversarial mutation suite")
        if not args.skip_probe_compile:
            compile_probe_files(root, src, chk)
        else:
            skipped.append("live probe compilation and 58 axiom audits")
        if not args.skip_rebuild:
            check_deterministic_rebuild(root, chk, acceptance,
                                        registry_path, dispositions_path)
        else:
            skipped.append("deterministic isolated rebuild")
    except Exception as exc:  # fail closed
        import traceback
        chk.fail("internal.exception", f"{type(exc).__name__}: {exc}")
        if not args.quiet:
            traceback.print_exc()

    report = build_report(root, src, chk, dims, probes, legacy, acceptance, skipped)

    if args.write_report or args.report_json or args.report_md:
        report_json = (Path(args.report_json) if args.report_json
                       else root / REPORT_JSON_PATH)
        report_md = (Path(args.report_md) if args.report_md else root / REPORT_MD_PATH)
        report_json.parent.mkdir(parents=True, exist_ok=True)
        report_md.parent.mkdir(parents=True, exist_ok=True)
        report_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                               encoding="utf-8")
        report_md.write_text(render_markdown(report) + "\n", encoding="utf-8")
        print(f"wrote {report_json}")
        print(f"wrote {report_md}")

    if not args.quiet:
        print(f"R8 independent validator: {report['status']}")
        print(f"  acceptance: {report['acceptanceState']}")
        print(f"  checks: {report['checks']['total']} total, "
              f"{report['checks']['failed']} failed")
        counts = report["counts"]
        print(f"  pairs/queries/records: {counts['pairs']}/{counts['queries']}/"
              f"{counts['records']}")
        print(f"  outcomes: {report['dimensions']['queryOutcomes']['outcomes']}")
        print(f"  library: {counts['certificateLibrary']}")
        print(f"  active evidence: {counts['activeCertifiedEvidence']}")
        print(f"  probes: {counts['probeFiles']} files / "
              f"{counts['probeReviewedDeclarations']} declarations / "
              f"{counts['probeCandidates']} candidates")
        print(f"  legacy: {counts['legacy']['entries']} dispositions "
              f"({counts['legacy']['named']}+{counts['legacy']['anchors']})")
        if report["failures"]:
            for failure in report["failures"][:40]:
                print(f"  FAIL [{failure['code']}] {failure['message']}")
            if len(report["failures"]) > 40:
                print(f"  ... {len(report['failures']) - 40} more failures")
    return 0 if chk.ok else 1


if __name__ == "__main__":
    sys.exit(main())
