#!/usr/bin/env python3
"""Deterministic builder for the R8 bounded relation-audit snapshot.

The builder reads only frozen/accepted inputs in the isolated PhotoLean
checkout and writes four generated artifacts:

  relation_audit/registry.accepted.json
  relation_audit/schema.accepted.json
  relation_audit/legacy-dispositions.accepted.json
  docs/RELATION-AUDIT-ACCEPTED.md

It never edits the legacy registry, the accepted R1-R7 packages, the frozen
PhotoLean tree, or any backup.  The builder supports the two uniform R8
acceptance states explicitly:

  --acceptance submitted-R8-pending-review   (default; independent review pending)
  --acceptance accepted-R8                   (only after two independent reviews pass)

The registry and the disposition ledger always receive the same state, and the
generated documentation and non-claims are rendered from that state.
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
import sys
from pathlib import Path

# The builder imports the frozen R1 parser; never leave __pycache__ behind in
# the read-only accepted input tree.
sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[2]
REGISTRY_OUT = ROOT / "relation_audit/registry.accepted.json"
SCHEMA_OUT = ROOT / "relation_audit/schema.accepted.json"
DISPOSITIONS_OUT = ROOT / "relation_audit/legacy-dispositions.accepted.json"
DOC_OUT = ROOT / "docs/RELATION-AUDIT-ACCEPTED.md"

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

PENDING = "submitted-R8-pending-review"
ACCEPTED = "accepted-R8"
ACCEPTANCE_STATES = (PENDING, ACCEPTED)
ACCEPTANCE_ALIASES = {
    PENDING: PENDING,
    ACCEPTED: ACCEPTED,
    "pending": PENDING,
    "accepted": ACCEPTED,
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
THEORIES = [
    "Marcus", "Hammond", "BEP", "Kasha", "Sabatier", "Goldschmidt",
    "SymmetryFactor", "KashaVavilov", "SternVolmer", "QuantumYield",
    "FluorPhos", "EnergyGapLaw", "StokesShift", "ICvsISC", "Forster",
    "Einstein", "RACI",
]
THEORY_INDEX = {t: i for i, t in enumerate(THEORIES)}

ALIASES = [
    {
        "aliasStatementId": "stmt-BEP-PhotoLean-BEP-rateViaEact",
        "aliasDeclaration": "PhotoLean.BEP.rateViaEact",
        "resolvedStatementId": "stmt-BEP-PhotoLean-BEP-rate_eq_exp_neg_eact",
        "resolvedDeclaration": "PhotoLean.BEP.rate_eq_exp_neg_eact",
        "resolutionKind": "theorem-rhs-term",
        "legacyRecordIds": ["rec-D-S05-bep-rate-eq-exp-neg-eact"],
        "certificateId": "cert-D-S05-bep-rate-eq-exp-neg-eact",
        "primaryActiveQueryId": "Q-WPS01-MB-03",
        "packageAliasIds": ["AL-WPS01-01", "AL-R3-01"],
    },
    {
        "aliasStatementId": "stmt-Marcus-PhotoLean-Marcus-rateDescriptor",
        "aliasDeclaration": "PhotoLean.Marcus.rateDescriptor",
        "resolvedStatementId": "stmt-Marcus-PhotoLean-Marcus-descriptor_sharp",
        "resolvedDeclaration": "PhotoLean.Marcus.descriptor_sharp",
        "resolutionKind": "theorem-lhs-predicate",
        "legacyRecordIds": ["rec-D-S06-hammond-sharp-iff-marcus-sharp"],
        "certificateId": "cert-D-S06-hammond-sharp-iff-marcus-sharp",
        "primaryActiveQueryId": "Q-WPS01-MH-05",
        "packageAliasIds": ["AL-WPS01-02", "AL-R3-02"],
    },
    {
        "aliasStatementId": "stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier-eq-zero",
        "aliasDeclaration": "PhotoLean.EnergyGapLaw.nrBarrier_eq_zero",
        "resolvedStatementId": "stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier",
        "resolvedDeclaration": "PhotoLean.EnergyGapLaw.nrBarrier",
        "resolutionKind": "definition-zero-locus",
        "legacyRecordIds": ["rec-D-S15-egBarrier-zero-iff-emEnergy-zero"],
        "certificateId": "cert-D-S15-egBarrier-zero-iff-emEnergy-zero",
        "primaryActiveQueryId": "Q-RAD3-ES-01",
        "packageAliasIds": ["AL-R3-03", "AL-RAD3-S15"],
    },
    {
        "aliasStatementId": "stmt-StokesShift-PhotoLean-StokesShift-emEnergy-eq-zero",
        "aliasDeclaration": "PhotoLean.StokesShift.emEnergy_eq_zero",
        "resolvedStatementId": "stmt-StokesShift-PhotoLean-StokesShift-emEnergy",
        "resolvedDeclaration": "PhotoLean.StokesShift.emEnergy",
        "resolutionKind": "definition-zero-locus",
        "legacyRecordIds": ["rec-D-S15-egBarrier-zero-iff-emEnergy-zero"],
        "certificateId": "cert-D-S15-egBarrier-zero-iff-emEnergy-zero",
        "primaryActiveQueryId": "Q-RAD3-ES-01",
        "packageAliasIds": ["AL-R3-04", "AL-RAD3-S15"],
    },
]

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
}


def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def parse_acceptance(value: str) -> str:
    """Validate the requested uniform R8 state; never guess an invalid value."""
    state = ACCEPTANCE_ALIASES.get(value)
    if state is None:
        allowed = ", ".join(ACCEPTANCE_STATES)
        raise argparse.ArgumentTypeError(
            f"invalid acceptance {value!r}; expected one of: {allowed} "
            "(or the aliases 'pending'/'accepted')")
    return state


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha_file(path: str | Path) -> str:
    p = ROOT / path if not os.path.isabs(str(path)) else Path(path)
    return sha_bytes(p.read_bytes())


def read_json(rel_path: str):
    path = ROOT / rel_path
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:  # fail closed
        fail(f"cannot read {rel_path}: {exc}")


def canonical_pair(a: str, b: str) -> str:
    require(a in THEORY_INDEX and b in THEORY_INDEX, f"unknown theory pair {a}/{b}")
    return f"P-{a}-{b}" if THEORY_INDEX[a] <= THEORY_INDEX[b] else f"P-{b}-{a}"


def status_counts(queries) -> dict:
    c = collections.Counter(q["outcome"]["status"] for q in queries)
    return {s: c.get(s, 0) for s in STATUSES}


def load_r1_validator():
    """Reuse the frozen R1 Lean declaration parser for signature verification."""
    path = ROOT / "audit_boundary/validate_boundary.py"
    spec = importlib.util.spec_from_file_location("_r1_boundary_for_r8", path)
    require(spec is not None and spec.loader is not None, "cannot load R1 boundary parser")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def load_boundary():
    inventory = read_json(INVENTORY_PATH)
    queue = read_json(PAIR_QUEUE_PATH)
    clusters = read_json(CLUSTER_PLAN_PATH)
    coverage = read_json(COVERAGE_PATH)
    legacy = read_json(LEGACY_PATH)
    for key, rel_path in (
        ("boundary", BOUNDARY_PATH),
        ("inventory", INVENTORY_PATH),
        ("pairQueue", PAIR_QUEUE_PATH),
        ("clusterPlan", CLUSTER_PLAN_PATH),
        ("coverage", COVERAGE_PATH),
        ("legacy", LEGACY_PATH),
        ("frozenR4", FROZEN_R4_PATH),
    ):
        actual = sha_file(rel_path)
        require(actual == EXPECTED[key], f"{rel_path} hash drift: {actual} != {EXPECTED[key]}")
    require(len(queue["pairs"]) == 136, "R1 pair queue is not 136 pairs")
    require(len(inventory["statements"]) == 1154, "R1 inventory is not 1154 rows")
    require(inventory["sourceFileManifest"]["fileCount"] == 102,
            "R1 source manifest is not 102 Lean files")
    require(len(list((ROOT / "PhotoLean").rglob("*.lean"))) == 102,
            "delivered PhotoLean tree is not 102 Lean files")
    require(len(legacy["queries"]) == 151 and len(legacy["records"]) == 151,
            "legacy registry is not 151 queries/records")
    require(len(legacy["certificates"]) == 38, "legacy registry is not 38 certificates")
    require(len(legacy["statements"]) == 52, "legacy registry is not 52 statements")
    require(dict(collections.Counter(r["status"] for r in legacy["records"])) ==
            {"certified": 24, "notEstablished": 121, "unresolved": 6},
            "legacy status counts are not 24/121/6")
    cum = coverage["cumulative"]
    require(cum["screenedPairCount"] == 136 and cum["acceptedPairCount"] == 136,
            "R7 coverage is not 136/136 accepted")
    require(cum["queryCount"] == 152 and cum["queryOutcomes"] ==
            {"certified": 67, "refuted": 0, "unresolved": 39, "notEstablished": 2, "outOfScope": 44},
            "R7 coverage query outcomes mismatch")
    return inventory, queue, clusters, coverage, legacy


def coverage_package_order(coverage) -> list[dict]:
    entries = []
    for group in ("acceptedWorkPackages", "submittedWorkPackages", "r5WorkPackages"):
        for row in coverage[group]:
            entries.append(dict(row))
    require(len(entries) == 10, f"expected 10 accepted screening packages, found {len(entries)}")
    return entries


def find_first(paths):
    for p in paths:
        if p and (ROOT / p).exists():
            return p
    return None


def package_artifacts(meta: dict, screening: dict) -> dict:
    screening_path = meta["path"]
    pkg_dir = (ROOT / screening_path).parent

    search_log_path = find_first([
        meta.get("searchLogPath"),
        (pkg_dir / "search-log.json").relative_to(ROOT).as_posix(),
    ])
    require(search_log_path is not None, f"missing search-log for {screening_path}")

    probe_path = find_first([
        meta.get("probePath"),
        (screening.get("probeReference") or {}).get("path"),
        (pkg_dir / "probes/Surface-probe.lean").relative_to(ROOT).as_posix(),
        (pkg_dir / "probes/R3-probe.lean").relative_to(ROOT).as_posix(),
        (pkg_dir / "probes/R4-CI-probe.lean").relative_to(ROOT).as_posix(),
        (pkg_dir / "probes/E1-probe.lean").relative_to(ROOT).as_posix(),
        (pkg_dir / "probes/E2-probe.lean").relative_to(ROOT).as_posix(),
        (pkg_dir / "probes/RAD1-probe.lean").relative_to(ROOT).as_posix(),
        (pkg_dir / "probes/RAD2-probe.lean").relative_to(ROOT).as_posix(),
        (pkg_dir / "probes/RAD3-probe.lean").relative_to(ROOT).as_posix(),
        (pkg_dir / "probes/XD1-probe.lean").relative_to(ROOT).as_posix(),
    ])
    fragment_path = find_first([
        meta.get("fragmentPath"),
        (pkg_dir / "coverage-fragment.json").relative_to(ROOT).as_posix(),
    ])
    report_path = find_first([
        (pkg_dir / "REPORT.md").relative_to(ROOT).as_posix(),
        (pkg_dir / "README.md").relative_to(ROOT).as_posix(),
    ])
    validator_path = find_first([
        meta.get("validatePath"),
        (pkg_dir / "validate.py").relative_to(ROOT).as_posix(),
    ])

    def artifact(path):
        if path is None:
            return None
        return {"path": path, "sha256": sha_file(path)}

    search_log = read_json(search_log_path)
    art = {
        "screening": artifact(screening_path),
        "searchLog": artifact(search_log_path),
        "probe": artifact(probe_path),
        "coverageFragment": artifact(fragment_path),
        "report": artifact(report_path),
        "validator": artifact(validator_path),
    }
    # Cross-check hashes that the accepted coverage ledger pins.
    if meta.get("sha256"):
        require(art["screening"]["sha256"] == meta["sha256"],
                f"coverage ledger screening hash mismatch for {screening_path}")
    if meta.get("searchLogSha256"):
        require(art["searchLog"]["sha256"] == meta["searchLogSha256"],
                f"coverage ledger search-log hash mismatch for {screening_path}")
    if meta.get("fragmentSha256"):
        require(art["coverageFragment"]["sha256"] == meta["fragmentSha256"],
                f"coverage ledger fragment hash mismatch for {screening_path}")
    if meta.get("validateSha256"):
        require(art["validator"]["sha256"] == meta["validateSha256"],
                f"coverage ledger validator hash mismatch for {screening_path}")
    if meta.get("probeSha256"):
        require(art["probe"]["sha256"] == meta["probeSha256"],
                f"coverage ledger probe hash mismatch for {screening_path}")
    return art, search_log


def load_packages(coverage):
    packages = []
    for meta in coverage_package_order(coverage):
        screening = read_json(meta["path"])
        art, search_log = package_artifacts(meta, screening)
        pairs = screening["pairs"]
        queries = [q for p in pairs for q in p["queries"]]
        require(len(pairs) == meta["pairCount"],
                f"pair count mismatch in {meta['path']}")
        require(len(queries) == len({q['queryId'] for q in queries}),
                f"duplicate query id in {meta['path']}")
        require(meta["acceptance"].startswith("accepted-"),
                f"package {meta['path']} is not accepted")
        packages.append({
            "meta": meta,
            "screening": screening,
            "searchLog": search_log,
            "artifacts": art,
            "pairs": pairs,
            "queries": queries,
        })
    require(len({p["meta"]["path"] for p in packages}) == 10, "package paths are not unique")
    return packages


def build_indexes(inventory, legacy, packages):
    inv_by_id = {s["id"]: s for s in inventory["statements"]}
    inv_by_decl = {s["declaration"]: s for s in inventory["statements"]}
    legacy_stmt_by_id = {s["id"]: s for s in legacy["statements"]}
    legacy_query_by_id = {q["id"]: q for q in legacy["queries"]}
    legacy_record_by_id = {r["id"]: r for r in legacy["records"]}
    legacy_cert_by_id = {c["id"]: c for c in legacy["certificates"]}
    package_by_path = {p["meta"]["path"]: p for p in packages}
    query_by_id = {}
    for pkg in packages:
        for pair in pkg["pairs"]:
            for q in pair["queries"]:
                require(q["queryId"] not in query_by_id, f"duplicate global query {q['queryId']}")
                query_by_id[q["queryId"]] = q
    return {
        "inv_by_id": inv_by_id,
        "inv_by_decl": inv_by_decl,
        "legacy_stmt_by_id": legacy_stmt_by_id,
        "legacy_query_by_id": legacy_query_by_id,
        "legacy_record_by_id": legacy_record_by_id,
        "legacy_cert_by_id": legacy_cert_by_id,
        "package_by_path": package_by_path,
        "query_by_id": query_by_id,
    }


def resolve_legacy_statement(sid: str, idx) -> dict:
    if sid.startswith("stmt-theory-"):
        theory = sid[len("stmt-theory-"):]
        require(theory in THEORY_INDEX, f"unknown theory anchor {sid}")
        return {"id": sid, "theory": theory, "declaration": None, "version": None,
                "kind": "theoryAnchor"}
    if sid in idx["legacy_stmt_by_id"]:
        s = idx["legacy_stmt_by_id"][sid]
        return {"id": sid, "theory": s["theory"], "declaration": s.get("declaration"),
                "version": s.get("version"), "kind": "legacyStatement"}
    if sid in idx["inv_by_id"]:
        s = idx["inv_by_id"][sid]
        return {"id": sid, "theory": s["theory"], "declaration": s.get("declaration"),
                "version": s.get("version"), "kind": "inventoryStatement"}
    fail(f"cannot resolve legacy endpoint {sid}")


def require_real_declaration(sid: str, idx, where: str) -> dict:
    require(sid in idx["inv_by_id"], f"{where}: {sid} is not a real R1 inventory statement")
    s = idx["inv_by_id"][sid]
    require(s.get("screeningEligible") is True, f"{where}: {sid} is not screeningEligible")
    return s


def build_statements(inventory, packages, idx, parser):
    endpoint_ids = set()
    for pkg in packages:
        for pair in pkg["pairs"]:
            for q in pair["queries"]:
                for role in ("source", "target"):
                    endpoint_ids.add(q["endpoints"][role]["statementId"])
    rows = []
    for sid in sorted(endpoint_ids):
        inv = require_real_declaration(sid, idx, "active endpoint")
        source_path = inv["sourceArtifact"]
        require(sha_file(source_path) == inv["sourceArtifactSha256"],
                f"source hash drift for {source_path}")
        parsed = parser.signatures(str(ROOT / source_path))
        info = parsed.get(inv["declaration"])
        require(info is not None, f"declaration {inv['declaration']} not found in {source_path}")
        require(info["line"] == inv["sourceLine"],
                f"line drift for {inv['declaration']}: {info['line']} != {inv['sourceLine']}")
        sig_sha = parser.signature_sha(info["kind"], inv["declaration"], info["signature"])
        require(sig_sha == inv["signatureSha256"],
                f"signature hash drift for {inv['declaration']}")
        rows.append({
            "statementId": sid,
            "inventoryId": sid,
            "theory": inv["theory"],
            "declaration": inv["declaration"],
            "declarationKind": inv["declarationKind"],
            "screeningRole": inv.get("screeningRole"),
            "screeningEligible": inv["screeningEligible"],
            "sourceArtifact": source_path,
            "sourceArtifactSha256": inv["sourceArtifactSha256"],
            "sourceLine": inv["sourceLine"],
            "sourceSignature": inv["sourceSignature"],
            "signatureSha256": inv["signatureSha256"],
            "version": inv["version"],
            "versionBasis": inv.get("versionBasis"),
        })
    require(len(rows) == 92, f"expected 92 active endpoint statements, found {len(rows)}")
    return rows


def build_queries_and_records(packages, idx, legacy, search_log_index):
    queries = []
    records = []
    for pkg in packages:
        meta = pkg["meta"]
        acceptance = meta["acceptance"]
        screening_art = pkg["artifacts"]["screening"]
        for pair in pkg["pairs"]:
            for raw in pair["queries"]:
                q = copy.deepcopy(raw)
                require(q["pairId"] == pair["pairId"], "query pair mismatch")
                for role in ("source", "target"):
                    e = q["endpoints"][role]
                    inv = require_real_declaration(e["statementId"], idx, q["queryId"])
                    require(inv["declaration"] == e["declaration"],
                            f"{q['queryId']}: endpoint declaration mismatch for {role}")
                    require(inv["theory"] == e["theory"],
                            f"{q['queryId']}: endpoint theory mismatch for {role}")
                    require(inv["sourceArtifact"] == e["sourceArtifact"],
                            f"{q['queryId']}: endpoint artifact mismatch for {role}")
                    require(inv["sourceLine"] == e["sourceLine"],
                            f"{q['queryId']}: endpoint line mismatch for {role}")
                    require(inv["version"] == e["version"],
                            f"{q['queryId']}: endpoint version mismatch for {role}")
                    require(inv["signatureSha256"] == e["signatureSha256"],
                            f"{q['queryId']}: endpoint signature hash mismatch for {role}")
                    require(inv["sourceArtifactSha256"] == e["sourceArtifactSha256"],
                            f"{q['queryId']}: endpoint source hash mismatch for {role}")
                require(q["expectedKind"] in RELATION_KINDS, f"{q['queryId']}: unknown kind")
                status = q["outcome"]["status"]
                require(status in STATUSES, f"{q['queryId']}: unknown status")
                if status == "certified":
                    ev = q["outcome"]["evidence"]
                    require(ev.get("kind") in NON_REFUTATION_KINDS,
                            f"{q['queryId']}: certified evidence kind is not non-refutation")
                    require(ev.get("kind") == q["expectedKind"],
                            f"{q['queryId']}: evidence kind != expected kind")
                    q["outcome"]["kind"] = ev["kind"]
                    q["outcome"]["evidenceClass"] = (
                        "deliveredModule" if ev["type"] == "legacy-certificate" else "boundedProbe"
                    )
                else:
                    require("searchLogRef" in q["outcome"]["evidence"],
                            f"{q['queryId']}: non-certified query lacks searchLogRef")
                    entry = search_log_index.get(q["queryId"])
                    require(entry is not None, f"{q['queryId']}: no search-log entry")
                    require(entry.get("status") == status,
                            f"{q['queryId']}: search-log status mismatch")
                    q["searchLog"] = {
                        "path": pkg["artifacts"]["searchLog"]["path"],
                        "sha256": pkg["artifacts"]["searchLog"]["sha256"],
                        "searchId": entry["searchId"],
                        "status": entry.get("status"),
                        "scope": entry.get("scope"),
                    }
                q["recordId"] = "rec-bounded-" + q["queryId"]
                q["packageId"] = meta.get("packageId") or meta["id"]
                q["round"] = meta["round"]
                q["acceptance"] = acceptance
                q["sourcePackage"] = {
                    "path": screening_art["path"],
                    "sha256": screening_art["sha256"],
                }
                q["statementVersion"] = (
                    f"{q['endpoints']['source']['statementId']}@{q['endpoints']['source']['version']}"
                    f"|{q['endpoints']['target']['statementId']}@{q['endpoints']['target']['version']}"
                )
                q["scopeId"] = q["scope"]["id"]
                q["snapshot"] = q["scope"].get("snapshot")
                queries.append(q)

                rec = {
                    "recordId": q["recordId"],
                    "queryId": q["queryId"],
                    "pairId": q["pairId"],
                    "status": status,
                    "scopeId": q["scopeId"],
                    "snapshot": q["snapshot"],
                    "statementVersion": q["statementVersion"],
                    "endpoints": {
                        role: {
                            "statementId": q["endpoints"][role]["statementId"],
                            "declaration": q["endpoints"][role]["declaration"],
                            "version": q["endpoints"][role]["version"],
                        }
                        for role in ("source", "target")
                    },
                    "premises": {
                        "predicate": q["premises"]["predicate"],
                        "premiseIds": list(q["premises"].get("premiseIds", [])),
                    },
                    "contextId": q["sharedContext"]["id"],
                    "provenance": q["provenance"],
                    "activeCoverage": True,
                }
                if status == "certified":
                    rec["relationKind"] = q["outcome"]["kind"]
                    rec["certificateId"] = q["outcome"]["evidence"]["certificateId"]
                    rec["evidenceClass"] = q["outcome"]["evidenceClass"]
                elif status == "refuted":
                    rec["refutationCertificateId"] = q["outcome"].get("refutationCertificateId")
                    rec["evidenceClass"] = q["outcome"].get("evidenceClass")
                else:
                    ev = q["outcome"]["evidence"]
                    rec["searchLog"] = q["searchLog"]
                    if status == "unresolved":
                        rec["candidateSummary"] = ev.get("candidateSummary", "")
                        entry = search_log_index[q["queryId"]]
                        rec["remainingGap"] = entry.get("remainingGap", "")
                        if "candidateProbe" in ev:
                            rec["candidateEvidenceIds"] = ["candidate-" + q["queryId"]]
                    elif status == "notEstablished":
                        entry = search_log_index[q["queryId"]]
                        rec["candidateSummary"] = ev.get("candidateSummary", "")
                        rec["dependencyEvidence"] = dependency_evidence(entry, pkg)
                    elif status == "outOfScope":
                        rec["jurisdiction"] = {
                            "statementLevel": True,
                            "rationale": ev.get("jurisdictionRationale", ""),
                            "statementLevelReason": ev.get("statementLevelReason") or ev.get("jurisdictionRationale", ""),
                            "searchLogRef": ev.get("searchLogRef"),
                            "endpoints": {role: q["endpoints"][role]["statementId"]
                                          for role in ("source", "target")},
                        }
                require(rec["statementVersion"] == q["statementVersion"], "statementVersion drift")
                records.append(rec)
    require(len(queries) == 152, f"expected 152 queries, found {len(queries)}")
    require(len(records) == 152, f"expected 152 records, found {len(records)}")
    require(len({q['queryId'] for q in queries}) == 152, "query IDs are not unique")
    require(len({r['recordId'] for r in records}) == 152, "record IDs are not unique")
    return queries, records


def dependency_evidence(entry: dict, pkg: dict) -> dict:
    deps = []
    for dep in entry.get("dependenciesConsulted", []):
        row = {
            "artifact": dep.get("artifact"),
            "locator": dep.get("locator"),
            "finding": dep.get("finding"),
        }
        art = dep.get("artifact")
        if art and (ROOT / art).exists():
            row["sha256"] = sha_file(art)
        deps.append(row)
    return {
        "searchId": entry["searchId"],
        "path": pkg["artifacts"]["searchLog"]["path"],
        "sha256": pkg["artifacts"]["searchLog"]["sha256"],
        "scope": entry.get("scope"),
        "snapshot": entry.get("snapshot"),
        "searchedStatements": list(entry.get("searchedStatements", [])),
        "searchedKinds": list(entry.get("searchedKinds", [])),
        "contextsConsidered": list(entry.get("contextsConsidered", [])),
        "commands": copy.deepcopy(entry.get("commands", [])),
        "dependenciesConsulted": deps,
        "recomputeCommands": list(entry.get("recomputeCommands", [])),
    }


def build_search_log_index(packages):
    out = {}
    for pkg in packages:
        for entry in pkg["searchLog"].get("entries", []):
            qid = entry.get("queryId")
            require(qid not in out, f"duplicate search-log query id {qid}")
            out[qid] = entry
    return out


def build_certificate_library(packages, queries, legacy, idx):
    legacy_records_by_cert = collections.defaultdict(list)
    for rec in legacy["records"]:
        if rec.get("certificate"):
            legacy_records_by_cert[rec["certificate"]].append(rec)
    active_legacy_use = collections.defaultdict(list)
    for q in queries:
        if q["outcome"]["status"] == "certified" and q["outcome"]["evidence"]["type"] == "legacy-certificate":
            active_legacy_use[q["outcome"]["evidence"]["certificateId"]].append(q["queryId"])

    delivered = []
    for cert in sorted(legacy["certificates"], key=lambda c: c["id"]):
        cid = cert["id"]
        active_ids = sorted(active_legacy_use.get(cid, []))
        recs = legacy_records_by_cert.get(cid, [])
        require(sha_file(cert["sourcePath"]) == cert["sourceSha256"],
                f"legacy certificate source drift: {cid}")
        require(set(cert["axiomFootprint"]) == set(ALLOWED_AXIOMS),
                f"legacy certificate axiom footprint: {cid}")
        delivered.append({
            "certificateId": cid,
            "evidenceClass": "deliveredModule",
            "kind": cert["kind"],
            "declaration": cert["lean"],
            "module": cert["module"],
            "sourcePath": cert["sourcePath"],
            "sourceSha256": cert["sourceSha256"],
            "axiomFootprint": list(cert["axiomFootprint"]),
            "allowedAxioms": list(ALLOWED_AXIOMS),
            "libraryRole": "reused-active-certificate" if active_ids else "retained-legacy-support",
            "activeQueryIds": active_ids,
            "legacyRecordIds": sorted(r["id"] for r in recs),
            "legacyQueryIds": sorted(r["queryId"] for r in recs),
            "certificateStatus": "unchanged-delivered-module-certificate",
        })
    require(len(delivered) == 38, "delivered-module library is not 38 entries")
    require(sum(1 for c in delivered if c["activeQueryIds"]) == 12,
            "active legacy certificate count is not 12")

    probe_entries = collections.OrderedDict()
    for q in queries:
        status = q["outcome"]["status"]
        if status != "certified":
            continue
        ev = q["outcome"]["evidence"]
        if ev["type"] == "legacy-certificate":
            continue
        cid = ev["certificateId"]
        probe = ev["probe"]
        require(cid not in probe_entries, f"duplicate probe certificate id {cid}")
        require(sha_file(probe["path"]) == probe["sha256"],
                f"probe source drift for {cid}")
        require(set(ev["axiomFootprint"]) == set(ALLOWED_AXIOMS),
                f"probe axiom footprint for {cid}")
        require(ev.get("kind") in NON_REFUTATION_KINDS, f"probe kind for {cid}")
        pkg = None
        for p in packages:
            if p["screening"] is not None and p["artifacts"]["screening"]["sha256"] == q["sourcePackage"]["sha256"]:
                pkg = p
                break
        require(pkg is not None, f"cannot find package for {cid}")
        review = pkg["artifacts"]["report"]
        review_ref = (
            {"path": review["path"], "sha256": review["sha256"], "kind": "package-report"}
            if review else
            {"path": COVERAGE_PATH, "sha256": EXPECTED["coverage"], "kind": "coverage-acceptance-row",
             "locator": pkg["meta"]["id"]}
        )
        log_path = probe.get("log")
        require(log_path and (ROOT / log_path).exists(), f"missing probe compile log for {cid}")
        probe_entries[cid] = {
            "certificateId": cid,
            "evidenceClass": "boundedProbe",
            "kind": ev["kind"],
            "declaration": probe["declaration"],
            "kindCheckTheorem": probe.get("kindCheckTheorem"),
            "probePath": probe["path"],
            "probeSha256": probe["sha256"],
            "buildCommand": probe["buildCommand"],
            "compileLog": {"path": log_path, "sha256": sha_file(log_path)},
            "axiomFootprint": list(ev["axiomFootprint"]),
            "allowedAxioms": list(ev["allowedAxioms"]),
            "packageId": pkg["meta"].get("packageId") or pkg["meta"]["id"],
            "round": pkg["meta"]["round"],
            "acceptance": pkg["meta"]["acceptance"],
            "packageReview": review_ref,
            "activeQueryIds": [q["queryId"]],
            "libraryRole": "active-certificate",
        }
    require(len(probe_entries) == 55, f"probe library is not 55 entries, found {len(probe_entries)}")
    require(all(len(v["activeQueryIds"]) == 1 for v in probe_entries.values()),
            "probe certificate is not attached to exactly one active query")
    return delivered, list(probe_entries.values())


def build_candidate_evidence(queries):
    candidates = []
    for q in queries:
        if q["outcome"]["status"] != "unresolved":
            continue
        ev = q["outcome"]["evidence"]
        if "candidateProbe" not in ev:
            continue
        p = ev["candidateProbe"]
        require(sha_file(p["path"]) == p["sha256"], f"candidate probe source drift {q['queryId']}")
        candidates.append({
            "candidateId": "candidate-" + q["queryId"],
            "evidenceClass": "boundedProbe",
            "isCertificate": False,
            "status": "unresolved",
            "declaration": p["declaration"],
            "probePath": p["path"],
            "probeSha256": p["sha256"],
            "buildCommand": p["buildCommand"],
            "compileLog": {"path": p["log"], "sha256": sha_file(p["log"])},
            "axiomFootprint": list(p["axiomFootprint"]),
            "allowedAxioms": list(p["allowedAxioms"]),
            "attachedQueryIds": [q["queryId"]],
            "candidateSummary": ev.get("candidateSummary", ""),
            "packageId": q["packageId"],
            "round": q["round"],
            "missingEvidence": "Named remaining gap recorded in the attached unresolved query and its search log.",
        })
    require(len(candidates) == 3, f"expected 3 XD1 candidate declarations, found {len(candidates)}")
    return candidates


def build_probe_files(packages, certificate_library, candidates):
    probe_entries = certificate_library["boundedProbe"]
    by_path = collections.OrderedDict()
    for c in probe_entries:
        by_path.setdefault(c["probePath"], []).append(("certificate", c))
    for c in candidates:
        by_path.setdefault(c["probePath"], []).append(("candidate", c))
    files = []
    for path in sorted(by_path):
        items = by_path[path]
        pkg = next(p for p in packages
                   if any(a["path"] == path for a in p["artifacts"].values() if a))
        cert_items = [x for kind, x in items if kind == "certificate"]
        cand_items = [x for kind, x in items if kind == "candidate"]
        build = (cert_items[0]["buildCommand"] if cert_items else cand_items[0]["buildCommand"])
        log = (cert_items[0]["compileLog"] if cert_items else cand_items[0]["compileLog"])
        files.append({
            "path": path,
            "sha256": sha_file(path),
            "packageId": pkg["meta"].get("packageId") or pkg["meta"]["id"],
            "round": pkg["meta"]["round"],
            "buildCommand": build,
            "compileLog": log,
            "certificateDeclarationCount": len(cert_items),
            "candidateDeclarationCount": len(cand_items),
            "reviewedDeclarationCount": len(cert_items) + len(cand_items),
            "certificateDeclarations": sorted(c["declaration"] for c in cert_items),
            "candidateDeclarations": sorted(c["declaration"] for c in cand_items),
        })
        declared = (pkg["screening"].get("probeReference") or {}).get("declarationCount")
        if declared is not None:
            require(declared == len(cert_items) + len(cand_items),
                    f"probeReference declarationCount mismatch for {path}")
    require(len(files) == 9, f"expected 9 probe files, found {len(files)}")
    require(sum(f["reviewedDeclarationCount"] for f in files) == 58,
            "reviewed probe declarations do not sum to 58")
    require(sum(f["certificateDeclarationCount"] for f in files) == 55,
            "probe certificate declarations do not sum to 55")
    require(sum(f["candidateDeclarationCount"] for f in files) == 3,
            "probe candidate declarations do not sum to 3")
    return files


def build_pairs(queue, queries, legacy, idx, certificate_library, candidates):
    by_pair = collections.defaultdict(list)
    for q in queries:
        by_pair[q["pairId"]].append(q)
    legacy_anchor_by_pair = {}
    legacy_named_by_pair = collections.defaultdict(list)
    for rec in legacy["records"]:
        q = idx["legacy_query_by_id"][rec["queryId"]]
        if q["source"].startswith("stmt-theory-") or q["target"].startswith("stmt-theory-"):
            a = resolve_legacy_statement(q["source"], idx)["theory"]
            b = resolve_legacy_statement(q["target"], idx)["theory"]
            legacy_anchor_by_pair[canonical_pair(a, b)] = rec
        else:
            a = resolve_legacy_statement(q["source"], idx)["theory"]
            b = resolve_legacy_statement(q["target"], idx)["theory"]
            if a != b:
                legacy_named_by_pair[canonical_pair(a, b)].append(rec)
    pairs = []
    for row in queue["pairs"]:
        pid = row["pairId"]
        qs = by_pair.get(pid, [])
        require(qs, f"pair {pid} has no active query")
        counts = status_counts(qs)
        cert_qs = [q for q in qs if q["outcome"]["status"] == "certified"]
        cert_kinds = sorted({q["outcome"]["kind"] for q in cert_qs})
        has_oos = any(q["outcome"]["status"] == "outOfScope" for q in qs)
        if cert_qs:
            basis = "certified-statement-query"
        elif any(q["outcome"]["status"] in ("unresolved", "notEstablished") for q in qs):
            basis = "named-noncertified-query"
        else:
            basis = "statement-level-outOfScope"
            require(has_oos, f"pair {pid} has no statement-level outOfScope record")
        anchor = legacy_anchor_by_pair.get(pid)
        named = legacy_named_by_pair.get(pid, [])
        absence_reconciled = bool(anchor and cert_qs and anchor["status"] == "notEstablished")
        candidate_reconciled = bool(anchor and cert_qs and anchor["status"] == "unresolved")
        packages = sorted({q["round"] for q in qs})
        pairs.append({
            "pairId": pid,
            "theories": list(row["theories"]),
            "primaryCluster": row["screeningCluster"],
            "requirement": {
                "requiredOutcome": row["requirement"]["requiredOutcome"],
                "permittedAlternative": row["requirement"].get("permittedAlternative"),
                "outOfScopePermitted": row["requirement"].get("outOfScopePermitted"),
            },
            "queryIds": [q["queryId"] for q in qs],
            "queryCount": len(qs),
            "outcomes": counts,
            "certifiedQueryIds": [q["queryId"] for q in cert_qs],
            "certifiedRelationKinds": cert_kinds,
            "hasCheckedEvidence": bool(cert_qs),
            "hasStatementLevelOutOfScope": has_oos,
            "coverageBasis": basis,
            "screened": True,
            "packages": packages,
            "legacy": {
                "pairAnchorIds": [anchor["id"]] if anchor else [],
                "namedRecordIds": sorted(r["id"] for r in named),
                "hasPairAnchor": bool(anchor),
                "hasNamedQuery": bool(named),
                "absenceReconciled": absence_reconciled,
                "candidateAnchorReconciled": candidate_reconciled,
            },
        })
    require(len(pairs) == 136, "pair entries are not 136")
    require(sum(p["queryCount"] for p in pairs) == 152, "pair query counts do not sum to 152")
    require(all(p["queryCount"] > 0 for p in pairs), "a pair has no query")
    return pairs


def build_index_maps(packages, queries, legacy, idx):
    # Search-log entries keyed by query id.
    search_index = build_search_log_index(packages)
    # Active queries keyed by pair.
    by_pair = collections.defaultdict(list)
    for q in queries:
        by_pair[q["pairId"]].append(q)
    # Legacy records keyed by pair.
    anchor_by_pair = {}
    named_by_pair = collections.defaultdict(list)
    for rec in legacy["records"]:
        q = idx["legacy_query_by_id"][rec["queryId"]]
        if q["source"].startswith("stmt-theory-") or q["target"].startswith("stmt-theory-"):
            a = resolve_legacy_statement(q["source"], idx)["theory"]
            b = resolve_legacy_statement(q["target"], idx)["theory"]
            anchor_by_pair[canonical_pair(a, b)] = rec
        else:
            a = resolve_legacy_statement(q["source"], idx)["theory"]
            b = resolve_legacy_statement(q["target"], idx)["theory"]
            if a != b:
                named_by_pair[canonical_pair(a, b)].append(rec)
    return search_index, by_pair, anchor_by_pair, named_by_pair


def build_legacy_dispositions(packages, queries, legacy, idx, pairs):
    search_index, by_pair, anchor_by_pair, named_by_pair = build_index_maps(
        packages, queries, legacy, idx)
    corrected_ids = {
        "rec-D-S05-bep-rate-eq-exp-neg-eact",
        "rec-D-S06-hammond-sharp-iff-marcus-sharp",
        "rec-D-S15-egBarrier-zero-iff-emEnergy-zero",
    }
    corrected_endpoints = {
        "rec-D-S05-bep-rate-eq-exp-neg-eact": (
            "stmt-Marcus-PhotoLean-Marcus-rate",
            "stmt-BEP-PhotoLean-BEP-rate_eq_exp_neg_eact",
        ),
        "rec-D-S06-hammond-sharp-iff-marcus-sharp": (
            "stmt-Hammond-PhotoLean-Hammond-HammondDescriptor",
            "stmt-Marcus-PhotoLean-Marcus-descriptor_sharp",
        ),
        "rec-D-S15-egBarrier-zero-iff-emEnergy-zero": (
            "stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier",
            "stmt-StokesShift-PhotoLean-StokesShift-emEnergy",
        ),
    }
    # Direct provenance and explicit prose links from active queries to legacy records/queries.
    record_links = collections.defaultdict(set)
    record_related = collections.defaultdict(set)
    link_basis = collections.defaultdict(set)
    for q in queries:
        prov = q.get("provenance", {})
        rid = prov.get("legacyRecordId")
        qid = prov.get("legacyQueryId")
        if rid:
            record_links[rid].add(q["queryId"])
            link_basis[rid].add("provenance-record-id")
        if qid:
            rec = next((r for r in legacy["records"] if r["queryId"] == qid), None)
            if rec:
                record_links[rec["id"]].add(q["queryId"])
                link_basis[rec["id"]].add("provenance-query-id")
        note = prov.get("legacyDisposition", "") or ""
        for rec in legacy["records"]:
            if rec["id"] in note:
                record_related[rec["id"]].add(q["queryId"])
                link_basis[rec["id"]].add("provenance-note")
        for rec in legacy["records"]:
            if rec["queryId"] in note:
                record_related[rec["id"]].add(q["queryId"])
                link_basis[rec["id"]].add("provenance-query-note")

    # Declaration-level correspondence for named rows on the same pair.
    def decl_of(sid):
        s = idx["inv_by_id"].get(sid) or idx["legacy_stmt_by_id"].get(sid)
        return s.get("declaration") if s else None

    active_by_decl_pair = collections.defaultdict(list)
    for q in queries:
        ds = (q["endpoints"]["source"]["declaration"], q["endpoints"]["target"]["declaration"])
        active_by_decl_pair[frozenset(ds)].append(q)
    for rec in legacy["records"]:
        q = idx["legacy_query_by_id"][rec["queryId"]]
        if q["source"].startswith("stmt-theory-") or q["target"].startswith("stmt-theory-"):
            continue
        if rec["id"] in corrected_endpoints:
            a, b = corrected_endpoints[rec["id"]]
        else:
            a, b = q["source"], q["target"]
        da, db = decl_of(a), decl_of(b)
        if not da or not db:
            continue
        for cand in active_by_decl_pair.get(frozenset((da, db)), []):
            if cand["pairId"] == rec_pair_id(rec, q, idx):
                record_links[rec["id"]].add(cand["queryId"])
                link_basis[rec["id"]].add("endpoint-declaration-match")

    # Force the three repaired records onto their canonical active query.
    for rid, (a, b) in corrected_endpoints.items():
        rec = idx["legacy_record_by_id"][rid]
        candidates = [q for q in queries
                      if (q["endpoints"]["source"]["statementId"], q["endpoints"]["target"]["statementId"])
                      == (a, b)]
        require(candidates, f"no active query for corrected record {rid}")
        primary = {
            "rec-D-S05-bep-rate-eq-exp-neg-eact": "Q-WPS01-MB-03",
            "rec-D-S06-hammond-sharp-iff-marcus-sharp": "Q-WPS01-MH-05",
            "rec-D-S15-egBarrier-zero-iff-emEnergy-zero": "Q-RAD3-ES-01",
        }[rid]
        require(any(q["queryId"] == primary for q in candidates),
                f"primary active query {primary} missing for {rid}")
        record_links[rid] = {primary}
        link_basis[rid].add("alias-repair")
        for cand in candidates:
            if cand["queryId"] != primary:
                record_related[rid].add(cand["queryId"])
                link_basis[rid].add("same-endpoint-active-query")

    # Alias lookup by statement id.
    alias_by_sid = {a["aliasStatementId"]: a for a in ALIASES}

    entries = []
    corrected_views = []
    reconciliations = []
    disposition_counts = collections.Counter()
    for rec in legacy["records"]:
        q = idx["legacy_query_by_id"][rec["queryId"]]
        is_anchor = q["source"].startswith("stmt-theory-") or q["target"].startswith("stmt-theory-")
        legacy_kind = "pair-anchor" if is_anchor else "named-query"
        if is_anchor:
            a = resolve_legacy_statement(q["source"], idx)["theory"]
            b = resolve_legacy_statement(q["target"], idx)["theory"]
            pair_id = canonical_pair(a, b)
            theories = [a, b]
            intra = False
        else:
            a = resolve_legacy_statement(q["source"], idx)["theory"]
            b = resolve_legacy_statement(q["target"], idx)["theory"]
            theories = [a, b]
            intra = a == b
            pair_id = None if intra else canonical_pair(a, b)
        active_ids = set(record_links.get(rec["id"], []))
        if is_anchor:
            pair_qids = {qq["queryId"] for qq in queries if qq["pairId"] == pair_id}
            active_ids |= pair_qids
            if pair_qids:
                link_basis[rec["id"]].add("pair-active-query-set")
        active_ids = sorted(active_ids)
        related_ids = sorted(set(record_related.get(rec["id"], [])) - set(active_ids))
        checked_ids = sorted(qid for qid in active_ids
                             if idx["query_by_id"][qid]["outcome"]["status"] == "certified")
        basis = sorted(link_basis.get(rec["id"], []))
        scope_obj = next((s for s in legacy["scopes"] if s["id"] == rec["scope"]), None)
        require(scope_obj is not None, f"legacy scope missing for {rec['id']}")
        entry = {
            "dispositionId": "disp-" + rec["id"],
            "legacyQueryId": rec["queryId"],
            "legacyRecordId": rec["id"],
            "legacyKind": legacy_kind,
            "pairId": pair_id,
            "theories": theories,
            "intraTheory": intra,
            "legacyStatus": rec["status"],
            "legacyRelationKind": rec.get("relationKind"),
            "legacyCertificateId": rec.get("certificate"),
            "legacyScope": {
                "id": scope_obj["id"],
                "kind": scope_obj.get("kind"),
                "description": scope_obj.get("description"),
                "boundary": scope_obj.get("boundary"),
            },
            "legacyStatementVersion": rec["statementVersion"],
            "legacyQuestion": q["question"],
            "legacyRationale": (
                rec.get("rationale")
                or rec.get("provenance", {}).get("rationale")
                or rec.get("provenance", {}).get("note")
                or "The legacy registry records this row without a separate rationale; its query and provenance are retained verbatim."
            ),
            "legacyProvenance": copy.deepcopy(q.get("provenance", {})),
            "legacySource": {"path": LEGACY_PATH, "sha256": EXPECTED["legacy"],
                             "recordId": rec["id"]},
            "activeQueryIds": active_ids,
            "relatedActiveQueryIds": related_ids,
            "checkedActiveQueryIds": checked_ids,
            "activeQueryLinkBasis": basis,
            "countsTowardActiveCoverage": False,
            "activeCoverageContribution": {"pairCount": 0, "queryCount": 0},
            "proseRetention": {
                "legacyProseRetained": True,
                "legacyRegistryUnchanged": True,
                "note": "The legacy record and its rationale remain in relation_audit/registry.json; this disposition is an additive interpretation, not an edit.",
            },
        }
        if intra:
            disposition = "retained-intra-theory-evidence"
        elif is_anchor:
            if checked_ids:
                if rec["status"] == "notEstablished":
                    disposition = "reconciled-absence-with-active-evidence"
                elif rec["status"] == "unresolved":
                    disposition = "reconciled-candidate-with-active-evidence"
                else:
                    fail(f"unexpected legacy anchor status {rec['status']} for {rec['id']}")
            else:
                disposition = ("retained-scoped-absence" if rec["status"] == "notEstablished"
                               else "retained-unresolved-candidate")
        else:
            # Named query.
            if rec.get("relationKind") == "refutation":
                disposition = "retained-refutation-evidence"
            elif rec["id"] in corrected_ids:
                if rec["id"] == "rec-D-S15-egBarrier-zero-iff-emEnergy-zero":
                    disposition = "repaired-and-restated"
                else:
                    disposition = "repaired-and-reused"
            elif any(qid in checked_ids for qid in active_ids):
                direct_reuse = any(
                    idx["query_by_id"][qid]["outcome"]["evidence"].get("certificateId") == rec.get("certificate")
                    for qid in checked_ids
                )
                disposition = ("reused-as-active-evidence" if direct_reuse
                               else "recertified-statement-level")
            elif rec["status"] == "unresolved":
                disposition = "retained-unresolved-candidate"
            elif rec["status"] == "notEstablished":
                disposition = "retained-scoped-absence"
            else:
                disposition = "retained-legacy-support"
        entry["disposition"] = disposition
        disposition_counts[disposition] += 1

        if rec["id"] in corrected_ids:
            primary_active = (
                "Q-WPS01-MB-03" if rec["id"].startswith("rec-D-S05-bep-rate")
                else ("Q-WPS01-MH-05" if rec["id"].startswith("rec-D-S06")
                      else "Q-RAD3-ES-01")
            )
            related = sorted(related_ids)
            view = build_corrected_view(rec, q, corrected_endpoints[rec["id"]], idx,
                                        [primary_active], primary_active=primary_active,
                                        related_active_ids=related)
            entry["correctedLegacyView"] = view
            corrected_views.append({
                "correctedViewId": view["correctedViewId"],
                "legacyRecordId": rec["id"],
                "legacyQueryId": rec["queryId"],
                "activeQueryIds": view["activeQueryIds"],
                "relatedActiveQueryIds": view["relatedActiveQueryIds"],
                "primaryActiveQueryId": view["primaryActiveQueryId"],
            })
            require(rec["certificate"] == view["certificateId"],
                    f"corrected view lost certificate for {rec['id']}")

        if is_anchor and checked_ids:
            recon = build_reconciliation(rec, q, pair_id, checked_ids, scope_obj, idx)
            entry["absenceReconciliation"] = recon
            reconciliations.append({
                "legacyRecordId": rec["id"],
                "legacyAnchorKind": recon["legacyAnchorKind"],
                "scopeRelationship": recon["scopeRelationship"],
                "activeQueryIds": checked_ids,
            })

        entries.append(entry)

    require(len(entries) == 151, f"expected 151 legacy dispositions, found {len(entries)}")
    require(len({e['legacyRecordId'] for e in entries}) == 151, "duplicate legacy record disposition")
    require(len({e['legacyQueryId'] for e in entries}) == 151, "duplicate legacy query disposition")
    named = [e for e in entries if e["legacyKind"] == "named-query"]
    anchors = [e for e in entries if e["legacyKind"] == "pair-anchor"]
    require(len(named) == 26 and len(anchors) == 125, "legacy 26/125 split failed")
    require(len([e for e in entries if e["intraTheory"]]) == 5, "legacy intra-theory count failed")
    require(len(corrected_views) == 3, "corrected view count failed")
    require(len(reconciliations) == 44, f"absence reconciliation count failed: {len(reconciliations)}")
    require(sum(1 for r in reconciliations if r["legacyAnchorKind"] == "notEstablished") == 41,
            "notEstablished reconciliation count failed")
    require(sum(1 for r in reconciliations if r["legacyAnchorKind"] == "unresolved-candidate") == 3,
            "candidate reconciliation count failed")
    require(all(e["activeCoverageContribution"] == {"pairCount": 0, "queryCount": 0}
                for e in entries), "a legacy disposition contributes active coverage")

    summary = {
        "records": len(entries),
        "namedQueries": len(named),
        "pairAnchors": len(anchors),
        "intraTheoryRecords": len([e for e in entries if e["intraTheory"]]),
        "byStatus": dict(collections.Counter(e["legacyStatus"] for e in entries)),
        "byDisposition": dict(sorted(disposition_counts.items())),
        "correctedRecords": len(corrected_views),
        "absenceReconciliations": len(reconciliations),
        "scopeRelationships": dict(collections.Counter(
            r["scopeRelationship"] for r in reconciliations)),
        "disposedExactlyOnce": True,
        "activeCoverageContribution": {"pairCount": 0, "queryCount": 0},
    }
    return entries, corrected_views, reconciliations, summary


def rec_pair_id(rec, q, idx):
    a = resolve_legacy_statement(q["source"], idx)["theory"]
    b = resolve_legacy_statement(q["target"], idx)["theory"]
    if a == b:
        return None
    return canonical_pair(a, b)


def build_corrected_view(rec, q, endpoints, idx, active_ids, primary_active,
                         related_active_ids=None):
    a, b = endpoints
    sa = require_real_declaration(a, idx, rec["id"])
    sb = require_real_declaration(b, idx, rec["id"])
    corrections = []
    for role, old, new, inv in (
        ("source", q["source"], a, sa),
        ("target", q["target"], b, sb),
    ):
        if old != new:
            corrections.append({
                "field": role,
                "oldStatementId": old,
                "newStatementId": new,
                "newDeclaration": inv["declaration"],
                "newVersion": inv["version"],
                "reason": "R1 legacy dangling statement alias replaced by the real delivered inventory declaration.",
            })
    require(corrections, f"corrected view for {rec['id']} has no corrections")
    statement_version = (
        f"{a}@{sa['version']}|{b}@{sb['version']}"
    )
    original_q = idx["legacy_query_by_id"][rec["queryId"]]
    return {
        "correctedViewId": "corrected-" + rec["id"],
        "kind": "corrected-legacy-query-record-view",
        "legacyQueryId": rec["queryId"],
        "legacyRecordId": rec["id"],
        "certificateId": rec["certificate"],
        "certificateUnchanged": True,
        "activeQueryIds": sorted(set(active_ids) | {primary_active}),
        "relatedActiveQueryIds": sorted(related_active_ids or []),
        "primaryActiveQueryId": primary_active,
        "corrections": corrections,
        "correctedQueryView": {
            "id": rec["queryId"],
            "queryId": rec["queryId"],
            "context": original_q["context"],
            "question": original_q["question"],
            "source": a,
            "target": b,
            "provenance": copy.deepcopy(original_q.get("provenance", {})),
        },
        "correctedRecordView": {
            "id": rec["id"],
            "recordId": rec["id"],
            "queryId": rec["queryId"],
            "certificate": rec["certificate"],
            "relationKind": rec.get("relationKind"),
            "scope": rec["scope"],
            "snapshot": rec["snapshot"],
            "status": rec["status"],
            "premises": copy.deepcopy(rec.get("premises", [])),
            "statementVersion": statement_version,
            "correctedStatementVersion": statement_version,
            "provenance": copy.deepcopy(rec.get("provenance", {})),
        },
        "correctedEndpoints": {
            "source": statement_summary(sa),
            "target": statement_summary(sb),
        },
    }


def statement_summary(inv):
    return {
        "statementId": inv["id"],
        "theory": inv["theory"],
        "declaration": inv["declaration"],
        "declarationKind": inv["declarationKind"],
        "sourceArtifact": inv["sourceArtifact"],
        "sourceLine": inv["sourceLine"],
        "version": inv["version"],
        "signatureSha256": inv["signatureSha256"],
        "sourceArtifactSha256": inv["sourceArtifactSha256"],
    }


def build_reconciliation(rec, q, pair_id, checked_ids, scope_obj, idx):
    if rec["status"] == "notEstablished":
        anchor_kind = "notEstablished"
        relationship = "superseded-in-named-scope"
        rationale = (
            f"The legacy anchor {rec['id']} is a pair-scoped snapshot absence: scope "
            f"{scope_obj['id']} asserts only that no direct cross-theory certificate was "
            f"registered in the accepted R1/R3 evidence at snapshot {rec['snapshot']}. "
            f"The active certified query/queries {', '.join(checked_ids)} establish a checked "
            f"statement-level relation in named scope(s) "
            f"{', '.join(sorted({idx['query_by_id'][qid]['scope']['id'] for qid in checked_ids}))}. "
            "The old absence is therefore superseded within those named scopes; outside them the "
            "historical prose is retained unchanged and is not used as a current verdict or a refutation."
        )
    elif rec["status"] == "unresolved":
        anchor_kind = "unresolved-candidate"
        relationship = "coexists-different-scope"
        rationale = (
            f"The legacy anchor {rec['id']} records a specific undelivered candidate relation in "
            f"scope {scope_obj['id']}; it is explicitly not a negative result. The active certified "
            f"query/queries {', '.join(checked_ids)} certify a different statement-level relation "
            f"in named scope(s) "
            f"{', '.join(sorted({idx['query_by_id'][qid]['scope']['id'] for qid in checked_ids}))}. "
            "The old candidate prose and the new checked relation therefore coexist in different "
            "scopes: the new evidence is current for its named statement, while the old candidate "
            "is neither refuted nor silently promoted."
        )
    else:
        fail(f"cannot reconcile status {rec['status']} for {rec['id']}")
    evidence = []
    for qid in checked_ids:
        qq = idx["query_by_id"][qid]
        evidence.append({
            "queryId": qid,
            "certificateId": qq["outcome"]["evidence"]["certificateId"],
            "evidenceClass": qq["outcome"]["evidenceClass"],
            "kind": qq["outcome"]["kind"],
            "scopeId": qq["scope"]["id"],
            "snapshot": qq["scope"].get("snapshot"),
        })
    return {
        "reconciliationId": "recon-" + rec["id"],
        "legacyAnchorKind": anchor_kind,
        "oldScopeId": scope_obj["id"],
        "oldSnapshot": rec["snapshot"],
        "newEvidence": evidence,
        "activeQueryIds": list(checked_ids),
        "scopeRelationship": relationship,
        "relationshipRationale": rationale,
        "oldSearchIsNotRefutation": True,
        "oldProseRetained": True,
        "oldProseIsCurrentVerdict": False,
        "newEvidenceOverridesOldProseInNamedScope": relationship == "superseded-in-named-scope",
    }


def build_alias_repairs(packages, legacy, idx, corrected_views):
    resolution_by_id = {}
    for pkg in packages:
        for res in pkg["screening"].get("aliasResolutions", []):
            rid = res.get("id") or res.get("legacyRecordId") or ""
            if rid:
                resolution_by_id[rid] = (pkg, res)
    # RAD3's alias resolution has no id; index by legacy record id.
    for pkg in packages:
        for res in pkg["screening"].get("aliasResolutions", []):
            if "legacyRecordId" in res:
                resolution_by_id[res["legacyRecordId"]] = (pkg, res)
    repairs = []
    for idx_alias, a in enumerate(ALIASES, start=1):
        inv_alias = idx["inv_by_id"].get(a["aliasStatementId"])
        require(inv_alias is None, f"alias {a['aliasStatementId']} unexpectedly in R1 inventory")
        inv_real = require_real_declaration(a["resolvedStatementId"], idx, a["aliasDeclaration"])
        require(inv_real["declaration"] == a["resolvedDeclaration"],
                f"alias mapping declaration mismatch for {a['aliasDeclaration']}")
        require(sha_file(inv_real["sourceArtifact"]) == inv_real["sourceArtifactSha256"],
                f"real endpoint source drift for {a['aliasDeclaration']}")
        dangling = next((d for d in read_json(INVENTORY_PATH)["legacyDanglingStatements"]
                         if d["id"] == a["aliasStatementId"]), None)
        require(dangling is not None, f"missing R1 dangling statement {a['aliasStatementId']}")
        package_refs = []
        for alias_id in a["packageAliasIds"]:
            hit = None
            for pkg in packages:
                for res in pkg["screening"].get("aliasResolutions", []):
                    rid = res.get("id")
                    if rid == alias_id:
                        hit = (pkg, res)
                        break
                if hit:
                    break
            if hit is None:
                # RAD3 uses a record-keyed resolution for S15.
                for pkg in packages:
                    if pkg["meta"]["round"] != "R5":
                        continue
                    for res in pkg["screening"].get("aliasResolutions", []):
                        if res.get("legacyRecordId") in a["legacyRecordIds"]:
                            hit = (pkg, res)
                            break
                    if hit:
                        break
            require(hit is not None, f"missing package alias resolution {alias_id}")
            pkg, res = hit
            package_refs.append({
                "packageId": pkg["meta"].get("packageId") or pkg["meta"]["id"],
                "round": pkg["meta"]["round"],
                "screeningPath": pkg["artifacts"]["screening"]["path"],
                "screeningSha256": pkg["artifacts"]["screening"]["sha256"],
                "resolutionId": res.get("id") or ("record-keyed:" + res.get("legacyRecordId", "")),
                "resolution": copy.deepcopy(res),
            })
        cert = idx["legacy_cert_by_id"][a["certificateId"]]
        views = [v for v in corrected_views if v["legacyRecordId"] in a["legacyRecordIds"]]
        require(len(views) == 1, f"alias {a['aliasDeclaration']} has no unique corrected view")
        repairs.append({
            "aliasRepairId": f"AL-R8-{idx_alias:02d}",
            "aliasClass": "r1-legacy-dangling",
            "aliasStatementId": a["aliasStatementId"],
            "aliasDeclaration": a["aliasDeclaration"],
            "resolvedStatementId": a["resolvedStatementId"],
            "resolvedDeclaration": a["resolvedDeclaration"],
            "resolutionKind": a["resolutionKind"],
            "sourceEvidence": {
                "inventory": {"path": INVENTORY_PATH, "sha256": EXPECTED["inventory"]},
                "inventoryDanglingRecord": copy.deepcopy(dangling),
                "packageAliasResolutions": package_refs,
                "realInventoryStatement": statement_summary(inv_real),
                "deliveredCertificate": {
                    "certificateId": cert["id"],
                    "kind": cert["kind"],
                    "declaration": cert["lean"],
                    "sourcePath": cert["sourcePath"],
                    "sourceSha256": cert["sourceSha256"],
                    "unchanged": True,
                },
                "affectedLegacyRecords": list(a["legacyRecordIds"]),
                "correctedLegacyViewId": views[0]["correctedViewId"],
                "activeQueryIds": list(views[0]["activeQueryIds"]),
                "primaryActiveQueryId": a["primaryActiveQueryId"],
            },
        })
    require(len(repairs) == 4, "alias repair count failed")
    return repairs


def build_evidence_references(queries, idx, parser):
    """Resolve every delivered theorem cited inside accepted query evidence.

    The endpoint statements live in ``registry.statements``.  The supporting
    theorems cited by probe evidence are a separate reference set: most are R1
    inventory rows, but some live in PhotoLean/Relations.lean outside the theory
    authority.  They are recorded explicitly instead of being silently dropped.
    """
    groups = {}
    for q in queries:
        for u in q["outcome"].get("evidence", {}).get("underlyingTheorems", []):
            decl = u["declaration"]
            g = groups.setdefault(decl, {
                "declaration": decl,
                "sourceArtifacts": set(),
                "sourceLines": set(),
                "roles": set(),
                "queryIds": set(),
            })
            g["sourceArtifacts"].add(u["sourceArtifact"])
            if u.get("sourceLine") is not None:
                g["sourceLines"].add(u["sourceLine"])
            if u.get("role"):
                g["roles"].add(u["role"])
            g["queryIds"].add(q["queryId"])
    rows = []
    for decl in sorted(groups):
        g = groups[decl]
        inv = idx["inv_by_decl"].get(decl)
        artifacts = sorted(g["sourceArtifacts"])
        source_path = None
        info = None
        for art in artifacts:
            parsed = parser.signatures(str(ROOT / art))
            if decl in parsed:
                source_path = art
                info = parsed[decl]
                break
        require(source_path is not None and info is not None,
                f"evidence declaration {decl} not found in cited sources {artifacts}")
        if inv is not None:
            require(inv["sourceArtifact"] == source_path,
                    f"inventory evidence declaration source mismatch for {decl}")
            require(inv["sourceLine"] == info["line"],
                    f"inventory evidence declaration line mismatch for {decl}")
            signature = inv["sourceSignature"]
            signature_sha = inv["signatureSha256"]
            source_sha = inv["sourceArtifactSha256"]
            statement_id = inv["id"]
        else:
            signature = info["signature"]
            signature_sha = parser.signature_sha(info["kind"], decl, signature)
            source_sha = sha_file(source_path)
            statement_id = None
        require(sha_file(source_path) == source_sha,
                f"evidence source hash drift for {decl}")
        rows.append({
            "declaration": decl,
            "inventoryStatementId": statement_id,
            "inInventory": inv is not None,
            "sourceArtifact": source_path,
            "sourceArtifactSha256": source_sha,
            "sourceLine": info["line"],
            "sourceSignature": signature,
            "signatureSha256": signature_sha,
            "roles": sorted(g["roles"]),
            "usedByQueryIds": sorted(g["queryIds"]),
        })
    require(len(rows) == 77, f"expected 77 evidence references, found {len(rows)}")
    return rows


def build_registry(inventory, queue, clusters, coverage, legacy, packages, parser,
                   acceptance):
    require(acceptance in ACCEPTANCE_STATES,
            f"unsupported acceptance state {acceptance!r}")
    idx = build_indexes(inventory, legacy, packages)
    search_index = build_search_log_index(packages)
    statements = build_statements(inventory, packages, idx, parser)
    queries, records = build_queries_and_records(packages, idx, legacy, search_index)
    evidence_references = build_evidence_references(queries, idx, parser)
    queries.sort(key=lambda q: q["queryId"])
    records.sort(key=lambda r: r["recordId"])
    delivered, probe = build_certificate_library(packages, queries, legacy, idx)
    candidates = build_candidate_evidence(queries)
    certificate_library = {
        "evidenceClassVocabulary": list(EVIDENCE_CLASSES),
        "counts": {
            "total": len(delivered) + len(probe),
            "deliveredModule": len(delivered),
            "boundedProbe": len(probe),
        },
        "deliveredModule": delivered,
        "boundedProbe": probe,
    }
    probe_files = build_probe_files(packages, certificate_library, candidates)
    pairs = build_pairs(queue, queries, legacy, idx, certificate_library, candidates)

    counts = {
        "packages": len(packages),
        "pairs": len(pairs),
        "activeQueries": len(queries),
        "activeRecords": len(records),
        "queryOutcomes": status_counts(queries),
        "certifiedPairs": sum(1 for p in pairs if p["hasCheckedEvidence"]),
        "certificateLibrary": certificate_library["counts"],
        "activeCertifiedEvidence": {
            "total": sum(1 for r in records if r["status"] == "certified"),
            "boundedProbe": sum(1 for r in records if r.get("evidenceClass") == "boundedProbe"),
            "deliveredModule": sum(1 for r in records if r.get("evidenceClass") == "deliveredModule"),
        },
        "candidateDeclarations": len(candidates),
        "probeFiles": len(probe_files),
        "probeReviewedDeclarations": sum(f["reviewedDeclarationCount"] for f in probe_files),
        "evidenceReferences": len(evidence_references),
        "legacy": {
            "records": len(legacy["records"]),
            "queries": len(legacy["queries"]),
            "namedQueries": 26,
            "pairAnchors": 125,
            "intraTheoryRecords": 5,
            "aliases": 4,
            "correctedRecords": 3,
            "absenceReconciliations": 44,
        },
    }
    require(counts["pairs"] == EXPECTED_ACTIVE["pairs"], "pair count mismatch")
    require(counts["activeQueries"] == EXPECTED_ACTIVE["queries"], "query count mismatch")
    require(counts["queryOutcomes"] == EXPECTED_ACTIVE["outcomes"], "outcome counts mismatch")
    require(counts["certifiedPairs"] == EXPECTED_ACTIVE["certifiedPairs"], "certified pair count mismatch")
    require(counts["certificateLibrary"]["total"] == 93, "library total mismatch")
    require(counts["certificateLibrary"]["deliveredModule"] == 38, "library delivered mismatch")
    require(counts["certificateLibrary"]["boundedProbe"] == 55, "library probe mismatch")
    require(counts["activeCertifiedEvidence"] == {
        "total": 67, "boundedProbe": 55, "deliveredModule": 12,
    }, "active certificate evidence counts mismatch")
    require(counts["probeReviewedDeclarations"] == 58, "reviewed declaration count mismatch")

    scopes = collections.OrderedDict()
    contexts = collections.OrderedDict()
    snapshots = collections.OrderedDict()
    statement_package = {}
    for q in queries:
        sid = q["scope"]["id"]
        if sid not in scopes:
            scopes[sid] = {
                "id": sid,
                "description": q["scope"]["description"],
                "domain": q["scope"]["domain"],
                "snapshot": q["scope"].get("snapshot"),
                "queryIds": [],
            }
        scopes[sid]["queryIds"].append(q["queryId"])
        key = q["packageId"] + "::" + q["sharedContext"]["id"]
        if key not in contexts:
            ctx = copy.deepcopy(q["sharedContext"])
            contexts[key] = {
                "packageId": q["packageId"],
                "context": ctx,
                "queryIds": [],
            }
        contexts[key]["queryIds"].append(q["queryId"])
        sn = q["scope"].get("snapshot")
        if sn:
            snapshots.setdefault(sn, {"snapshot": sn, "packages": set(), "queryIds": []})
            snapshots[sn]["packages"].add(q["packageId"])
            snapshots[sn]["queryIds"].append(q["queryId"])
    scope_rows = []
    for sid in sorted(scopes):
        row = scopes[sid]
        row["queryIds"] = sorted(row["queryIds"])
        row["queryCount"] = len(row["queryIds"])
        scope_rows.append(row)
    context_rows = []
    for key in sorted(contexts):
        row = contexts[key]
        row["queryIds"] = sorted(row["queryIds"])
        row["queryCount"] = len(row["queryIds"])
        context_rows.append(row)
    snapshot_rows = []
    for sn in sorted(snapshots):
        row = snapshots[sn]
        row["packages"] = sorted(row["packages"])
        row["queryIds"] = sorted(row["queryIds"])
        row["queryCount"] = len(row["queryIds"])
        snapshot_rows.append(row)

    accepted_packages = []
    package_rows = []
    for pkg in packages:
        meta = pkg["meta"]
        post = status_counts(pkg["queries"])
        probe_count = sum(1 for q in pkg["queries"]
                          if q["outcome"]["status"] == "certified"
                          and q["outcome"]["evidence"]["type"] != "legacy-certificate")
        legacy_count = sum(1 for q in pkg["queries"]
                           if q["outcome"]["status"] == "certified"
                           and q["outcome"]["evidence"]["type"] == "legacy-certificate")
        review = pkg["artifacts"]["report"]
        accepted_packages.append({
            "round": meta["round"],
            "packageId": meta.get("packageId") or meta["id"],
            "acceptance": meta["acceptance"],
            "screening": pkg["artifacts"]["screening"],
            "searchLog": pkg["artifacts"]["searchLog"],
            "probe": pkg["artifacts"]["probe"],
            "coverageFragment": pkg["artifacts"]["coverageFragment"],
            "report": review,
            "validator": pkg["artifacts"]["validator"],
            "reviewReference": (
                {"kind": "package-report", "path": review["path"], "sha256": review["sha256"]}
                if review else
                {"kind": "coverage-acceptance-row", "path": COVERAGE_PATH,
                 "sha256": EXPECTED["coverage"], "locator": meta["id"]}
            ),
        })
        package_rows.append({
            "round": meta["round"],
            "packageId": meta.get("packageId") or meta["id"],
            "acceptance": meta["acceptance"],
            "pairCount": len(pkg["pairs"]),
            "queryCount": len(pkg["queries"]),
            "outcomes": post,
            "certifiedProbeCertificates": probe_count,
            "certifiedLegacyCertificates": legacy_count,
        })

    references = {
        "r1": {
            "boundary": {"path": BOUNDARY_PATH, "sha256": EXPECTED["boundary"]},
            "statementInventory": {"path": INVENTORY_PATH, "sha256": EXPECTED["inventory"],
                                   "statementRows": 1154, "screeningEligible": 1134},
            "pairQueue": {"path": PAIR_QUEUE_PATH, "sha256": EXPECTED["pairQueue"],
                          "pairCount": 136, "theoryCount": 17},
            "clusterPlan": {"path": CLUSTER_PLAN_PATH, "sha256": EXPECTED["clusterPlan"]},
        },
        "coverageLedger": {"path": COVERAGE_PATH, "sha256": EXPECTED["coverage"],
                           "acceptedPairCount": 136, "queryCount": 152},
        "legacyRegistry": {"path": LEGACY_PATH, "sha256": EXPECTED["legacy"],
                           "queries": 151, "records": 151, "certificates": 38,
                           "statements": 52},
        "frozenR4Coverage": {"path": FROZEN_R4_PATH, "sha256": EXPECTED["frozenR4"]},
        "acceptedPackages": accepted_packages,
    }

    relation_kind_counts = collections.Counter(
        q["outcome"]["kind"] for q in queries if q["outcome"]["status"] == "certified")
    relation_discovery = {
        "certifiedQueries": sum(1 for q in queries if q["outcome"]["status"] == "certified"),
        "pairsWithCertifiedRelation": counts["certifiedPairs"],
        "certifiedRelationKindCounts": dict(sorted(relation_kind_counts.items())),
        "note": "This is the bounded certified-relation discovery dimension; it is not pair coverage and not proposition completeness.",
    }
    query_outcomes = {
        **status_counts(queries),
        "byRound": {
            rnd: status_counts([q for q in queries if q["round"] == rnd])
            for rnd in sorted({q["round"] for q in queries})
        },
        "certifiedEvidenceClasses": {
            "boundedProbe": counts["activeCertifiedEvidence"]["boundedProbe"],
            "deliveredModule": counts["activeCertifiedEvidence"]["deliveredModule"],
        },
    }
    coverage_block = {
        "pairUniverse": 136,
        "pairsWithScreening": 136,
        "remainingPairIds": [],
        "pairsWithNamedStatementQuery": 136,
        "note": "136/136 pair coverage means every pair has a named statement-level query or statement-level outOfScope record; it does not mean every pair is certified.",
    }

    evidence_policy = {
        "evidenceClassVocabulary": list(EVIDENCE_CLASSES),
        "deliveredModule": {
            "definition": "A certificate declared in the frozen delivered PhotoLean/**/*.lean tree and accepted by the legacy full-registry validator.",
            "acceptanceRequirements": [
                "declaration exists in the delivered Lean source",
                "source path and SHA-256 match the accepted legacy registry",
                "certificate kind and axiom footprint are recorded",
                "the unchanged legacy full validator remains the evidence gate",
            ],
        },
        "boundedProbe": {
            "definition": "A package-local certificate compiled directly from an accepted bounded screening package's probe file outside the frozen default build targets.",
            "acceptanceRequirements": [
                "accepted package provenance (screening, search log, report/acceptance row)",
                "exact probe source path and SHA-256",
                "certificate declaration and kind, including the kind-check theorem",
                "direct serial compile command and compile/axiom log",
                "live allowed-axiom footprint propext, Classical.choice, Quot.sound",
                "package review reference",
            ],
            "forbiddenPatterns": ["sorry", "admit", "axiom", "native_decide", "unsafe"],
            "serialCompilation": True,
            "candidatePolicy": "Candidate declarations in a probe are not certificates; they are attached only to unresolved queries and never enter the certificate library.",
        },
        "probeCompilation": {
            "fileCount": 9,
            "reviewedDeclarationCount": 58,
            "certificateDeclarationCount": 55,
            "candidateDeclarationCount": 3,
            "commandShape": "proofs/scripts/lake env lean <probe-path>",
            "serialized": True,
            "note": "The integrated validator must serially compile all nine probe files, run the package placeholder/custom-axiom gates, audit all 58 declarations, and run the original legacy full-registry validator.",
        },
    }

    legacy_reconciliation = {
        "dispositionsPath": "relation_audit/legacy-dispositions.accepted.json",
        "legacyRegistryUnchanged": True,
        "legacyRecords": 151,
        "namedQueries": 26,
        "pairAnchors": 125,
        "intraTheoryRecords": 5,
        "aliasesRepaired": 4,
        "affectedCertifiedRecords": 3,
        "oldAbsenceNewEvidenceOverlaps": 44,
        "scopeRelationships": {
            "superseded-in-named-scope": 41,
            "coexists-different-scope": 3,
            "subsumed": 0,
        },
        "pairAnchorsCountTowardActiveCoverage": False,
        "intraTheoryRecordsCountTowardActiveCoverage": False,
        "failedSearchesBecomeRefutations": False,
        "oldProseRetained": True,
        "note": "Legacy records are disposed once in the companion ledger; they do not add active queries or pair coverage. Old absence prose is retained and reconciled by explicit scope, never silently overwritten.",
    }

    non_claims = [
        "136/136 pair coverage means every pair has a named statement-level screening record, not that every pair has a certified relation.",
        "An unresolved, notEstablished or outOfScope query is not a failure and is not a refutation.",
        "The 55 bounded-probe certificates are package-local evidence accepted under the probe policy; they are not additions to the frozen delivered PhotoLean tree.",
        "The three XD1 candidate declarations are unresolved candidate evidence, not certificates.",
        "The legacy registry and its 151 records remain historical inputs; the dispositions are additive interpretations and do not edit them.",
        "The bounded protocol does not exhaust all propositions of the seventeen theories or all relations outside the frozen statement inventory.",
    ]
    if acceptance == PENDING:
        non_claims.append(
            "This snapshot is submitted-R8-pending-review until two independent K3.1 Pro "
            "reviews pass and the lead accepts it.")
    else:
        non_claims.append(
            "This snapshot is accepted-R8: two independent K3.1 Pro reviews passed and the "
            "lead recorded the uniform registry/disposition acceptance flip. Acceptance does "
            "not turn unresolved, notEstablished or outOfScope queries into certified ones.")

    registry = {
        "$schema": "relation_audit/schema.accepted.json#/$defs/registry",
        "schemaVersion": "2.0.0",
        "artifactKind": "bounded-relation-registry",
        "mode": "bounded-full",
        "round": "R8",
        "generatedOn": "2026-11-04",
        "acceptance": acceptance,
        "description": "Deterministic R8 bounded relation registry generated from the accepted R1-R7 inputs, ten accepted R2-R5 screening packages, the unchanged legacy registry and the final R7 coverage ledger. Pair coverage, query outcomes and certified relation discovery are separate dimensions.",
        "references": references,
        "packages": package_rows,
        "theoryInventory": list(queue["theoryInventory"]),
        "counts": counts,
        "coverage": coverage_block,
        "queryOutcomes": query_outcomes,
        "relationDiscovery": relation_discovery,
        "pairs": pairs,
        "queries": queries,
        "records": records,
        "statements": statements,
        "evidenceReferences": evidence_references,
        "scopes": scope_rows,
        "contexts": context_rows,
        "snapshots": snapshot_rows,
        "certificateLibrary": certificate_library,
        "candidateEvidence": candidates,
        "probeFiles": probe_files,
        "evidencePolicy": evidence_policy,
        "legacyReconciliation": legacy_reconciliation,
        "companionArtifacts": {
            "legacyDispositions": "relation_audit/legacy-dispositions.accepted.json",
            "schema": "relation_audit/schema.accepted.json",
            "builder": "tools/relation_audit_bounded/build.py",
            "documentation": "docs/RELATION-AUDIT-ACCEPTED.md",
        },
        "planDeviations": [
            {
                "id": "DEV-R8-01",
                "planStatement": "The plan describes eight accepted R2-R5 screening packages.",
                "observed": "The actual accepted artifacts contain ten screening packages: R2 one, R3 one, R4 three, R5 five.",
                "impact": "None on the contract counts. All ten are required to reach 136 pairs and 152 queries; using only eight would leave pair or query coverage incomplete.",
                "resolution": "Use all ten actual accepted packages and report the plan-metadata miscount rather than dropping data or inventing packages.",
                "blocking": False,
            }
        ],
        "nonClaims": non_claims,
    }
    return registry


def build_dispositions_file(legacy, coverage, packages, queries, idx, pairs,
                            acceptance):
    require(acceptance in ACCEPTANCE_STATES,
            f"unsupported acceptance state {acceptance!r}")
    idx = dict(idx)
    idx["query_by_id"] = {q["queryId"]: q for q in queries}
    entries, corrected_views, reconciliations, summary = build_legacy_dispositions(
        packages, queries, legacy, idx, pairs)
    repairs = build_alias_repairs(packages, legacy, idx, corrected_views)
    source = {
        "legacyRegistry": {"path": LEGACY_PATH, "sha256": EXPECTED["legacy"],
                           "queries": 151, "records": 151, "certificates": 38,
                           "statements": 52, "unchanged": True},
        "coverageLedger": {"path": COVERAGE_PATH, "sha256": EXPECTED["coverage"]},
        "statementInventory": {"path": INVENTORY_PATH, "sha256": EXPECTED["inventory"]},
        "pairQueue": {"path": PAIR_QUEUE_PATH, "sha256": EXPECTED["pairQueue"]},
        "activeRegistry": {
            "path": "relation_audit/registry.accepted.json",
            "role": "companion output; referenced by path only to avoid a hash cycle",
        },
    }
    disposition_non_claims = [
        "This ledger does not modify relation_audit/registry.json; every legacy record and query ID remains exactly as accepted.",
        "A pair anchor is coverage history, not a named query, and contributes zero active pair or query coverage.",
        "A failed legacy search is not a refutation; no old absent edge becomes refuted by this ledger.",
        "A corrected legacy view is metadata repair for endpoint traceability, not a new certificate or a new mathematical claim.",
    ]
    if acceptance == ACCEPTED:
        disposition_non_claims.append(
            "This ledger shares the active registry's accepted-R8 state; acceptance is a "
            "state flip, not an edit to any legacy record or certificate.")
    dispositions = {
        "$schema": "relation_audit/schema.accepted.json#/$defs/legacyDispositions",
        "schemaVersion": "1.0.0",
        "artifactKind": "legacy-disposition-ledger",
        "mode": "bounded-full",
        "round": "R8",
        "generatedOn": "2026-11-04",
        "acceptance": acceptance,
        "description": "Additive R8 disposition ledger for every one of the 151 unchanged legacy records. It repairs four endpoint aliases in explicit corrected views, preserves all legacy prose, and reconciles old scoped absence with new checked evidence without counting legacy anchors or intra-theory records as active coverage.",
        "source": source,
        "dispositionVocabulary": [
            "reused-as-active-evidence",
            "repaired-and-reused",
            "repaired-and-restated",
            "recertified-statement-level",
            "retained-legacy-support",
            "retained-refutation-evidence",
            "retained-intra-theory-evidence",
            "retained-scoped-absence",
            "retained-unresolved-candidate",
            "reconciled-absence-with-active-evidence",
            "reconciled-candidate-with-active-evidence",
        ],
        "scopeRelationshipVocabulary": [
            "subsumed",
            "superseded-in-named-scope",
            "coexists-different-scope",
        ],
        "aliasRepairs": repairs,
        "correctedLegacyViews": corrected_views,
        "summary": {
            **summary,
            "aliasRepairs": len(repairs),
            "activeCoverageContribution": {"pairCount": 0, "queryCount": 0},
            "pairAnchorsCountTowardActiveCoverage": False,
            "intraTheoryRecordsCountTowardActiveCoverage": False,
        },
        "entries": entries,
        "nonClaims": disposition_non_claims,
    }
    require(len(dispositions["aliasRepairs"]) == 4, "alias repairs missing")
    require(len(dispositions["correctedLegacyViews"]) == 3, "corrected legacy views missing")
    require(dispositions["summary"]["records"] == 151, "disposition summary records mismatch")
    require(dispositions["summary"]["namedQueries"] == 26, "disposition summary named mismatch")
    require(dispositions["summary"]["pairAnchors"] == 125, "disposition summary anchors mismatch")
    return dispositions


def build_schema() -> dict:
    """Return the draft 2020-12 schema with registry and disposition definitions."""
    sha = {"type": "string", "pattern": "^[0-9a-f]{64}$"}
    path = {"type": "string", "minLength": 1}
    nonempty = {"type": "string", "minLength": 1}
    statement_ref = {
        "type": "object",
        "required": ["statementId", "declaration", "version"],
        "properties": {
            "statementId": nonempty,
            "declaration": nonempty,
            "version": nonempty,
        },
        "additionalProperties": False,
    }
    endpoint = {
        "type": "object",
        "required": ["statementId", "theory", "declaration", "declarationKind", "sourceArtifact",
                     "sourceLine", "version", "signatureSha256", "sourceArtifactSha256", "endpointForm"],
        "properties": {
            "statementId": nonempty,
            "theory": {"type": "string", "enum": THEORIES},
            "declaration": nonempty,
            "declarationKind": {"type": "string", "enum": ["def", "theorem"]},
            "sourceArtifact": path,
            "sourceLine": {"type": "integer", "minimum": 1},
            "version": nonempty,
            "signatureSha256": sha,
            "sourceArtifactSha256": sha,
            "endpointForm": nonempty,
            "endpointNote": {"type": "string"},
        },
        "additionalProperties": False,
    }
    context = {
        "type": "object",
        "required": ["id", "fields", "physicalReading", "provenance"],
        "properties": {
            "id": nonempty,
            "fields": {"type": "array", "items": {"type": "string"}},
            "physicalReading": nonempty,
            "provenance": {"type": "string"},
            "translationStatus": {"type": "string"},
        },
        "additionalProperties": False,
    }
    translation = {
        "type": "object",
        "required": ["id", "requirement"],
        "properties": {
            "id": nonempty,
            "requirement": nonempty,
            "term": {"type": ["string", "null"]},
            "reason": {"type": "string"},
        },
        "additionalProperties": False,
    }
    premises = {
        "type": "object",
        "required": ["predicate", "premiseIds", "definitions"],
        "properties": {
            "predicate": nonempty,
            "premiseIds": {"type": "array", "items": {"type": "string"}},
            "definitions": {"type": "array", "items": {"type": "object"}},
            "note": {"type": "string"},
        },
        "additionalProperties": False,
    }
    channel = {
        "type": "object",
        "required": ["id", "observedValueType", "inputDomain", "domainNonempty",
                     "leftObs", "rightObs"],
        "properties": {
            "id": nonempty,
            "name": {"type": "string"},
            "observedValueType": nonempty,
            "inputDomain": nonempty,
            "domainNonempty": {"type": "boolean"},
            "leftObs": nonempty,
            "rightObs": nonempty,
        },
        "additionalProperties": False,
    }
    scope = {
        "type": "object",
        "required": ["id", "description", "domain", "snapshot"],
        "properties": {
            "id": nonempty,
            "description": nonempty,
            "domain": nonempty,
            "snapshot": nonempty,
        },
        "additionalProperties": False,
    }
    evidence = {
        "type": "object",
        "required": ["type"],
        "properties": {"type": nonempty},
        "additionalProperties": True,
    }
    outcome = {
        "type": "object",
        "required": ["status", "rationale", "evidence"],
        "properties": {
            "status": {"$ref": "#/$defs/status"},
            "rationale": nonempty,
            "evidence": {"$ref": "#/$defs/evidence"},
            "kind": {"$ref": "#/$defs/relationKind"},
            "evidenceClass": {"$ref": "#/$defs/evidenceClass"},
            "refutationCertificateId": nonempty,
        },
        "additionalProperties": False,
        "allOf": [
            {
                "if": {"properties": {"status": {"const": "certified"}}, "required": ["status"]},
                "then": {
                    "required": ["kind", "evidenceClass"],
                    "properties": {
                        "kind": {"enum": NON_REFUTATION_KINDS},
                        "evidenceClass": {"$ref": "#/$defs/evidenceClass"},
                        "evidence": {"required": ["certificateId", "kind"]},
                    },
                },
            },
            {
                "if": {"properties": {"status": {"const": "refuted"}}, "required": ["status"]},
                "then": {
                    "required": ["refutationCertificateId", "evidenceClass"],
                    "properties": {"refutationCertificateId": nonempty},
                },
            },
            {
                "if": {"properties": {"status": {"const": "unresolved"}}, "required": ["status"]},
                "then": {"properties": {"evidence": {"required": ["candidateSummary", "searchLogRef"]}}},
            },
            {
                "if": {"properties": {"status": {"const": "notEstablished"}}, "required": ["status"]},
                "then": {"properties": {"evidence": {"required": ["candidateSummary", "searchLogRef"]}}},
            },
            {
                "if": {"properties": {"status": {"const": "outOfScope"}}, "required": ["status"]},
                "then": {"properties": {"evidence": {"required": [
                    "searchLogRef", "jurisdictionRationale"]}}},
            },
            {
                "if": {"properties": {"status": {"enum": [
                    "refuted", "unresolved", "notEstablished", "outOfScope"]}},
                    "required": ["status"]},
                "then": {"not": {"required": ["kind"]}},
            },
        ],
    }
    search_log = {
        "type": "object",
        "required": ["path", "sha256", "searchId", "status"],
        "properties": {
            "path": path,
            "sha256": sha,
            "searchId": nonempty,
            "status": {"$ref": "#/$defs/status"},
            "scope": {"type": "string"},
        },
        "additionalProperties": False,
    }
    query = {
        "type": "object",
        "required": ["queryId", "pairId", "title", "chemicalQuestion", "chemicalRationale",
                     "endpoints", "sharedContext", "translations", "premises",
                     "observationChannels", "scope", "expectedKind", "expectedKindRationale",
                     "falsificationCondition", "outcome", "provenance", "recordId",
                     "packageId", "round", "acceptance", "sourcePackage",
                     "statementVersion", "scopeId", "snapshot"],
        "properties": {
            "queryId": nonempty,
            "pairId": nonempty,
            "title": nonempty,
            "chemicalQuestion": nonempty,
            "chemicalRationale": nonempty,
            "endpoints": {
                "type": "object",
                "required": ["source", "target"],
                "properties": {"source": endpoint, "target": endpoint},
                "additionalProperties": False,
            },
            "sharedContext": context,
            "translations": {
                "type": "object",
                "required": ["left", "right"],
                "properties": {"left": translation, "right": translation},
                "additionalProperties": False,
            },
            "premises": premises,
            "observationChannels": {"type": "array", "items": channel},
            "scope": scope,
            "expectedKind": {"$ref": "#/$defs/relationKind"},
            "expectedKindRationale": nonempty,
            "falsificationCondition": nonempty,
            "outcome": outcome,
            "provenance": {"type": "object", "required": ["kind"], "additionalProperties": True},
            "recordId": nonempty,
            "packageId": nonempty,
            "round": {"type": "string", "enum": ["R2", "R3", "R4", "R5"]},
            "acceptance": {"type": "string", "pattern": "^accepted-R[2-5]$"},
            "sourcePackage": {
                "type": "object",
                "required": ["path", "sha256"],
                "properties": {"path": path, "sha256": sha},
                "additionalProperties": False,
            },
            "statementVersion": nonempty,
            "scopeId": nonempty,
            "snapshot": nonempty,
            "searchLog": search_log,
        },
        "additionalProperties": False,
    }
    dependency = {
        "type": "object",
        "required": ["searchId", "path", "sha256", "scope", "snapshot", "commands",
                     "dependenciesConsulted", "recomputeCommands"],
        "properties": {
            "searchId": nonempty,
            "path": path,
            "sha256": sha,
            "scope": {"type": "string"},
            "snapshot": {"type": "string"},
            "searchedStatements": {"type": "array", "items": {"type": "string"}},
            "searchedKinds": {"type": "array", "items": {"type": "string"}},
            "contextsConsidered": {"type": "array", "items": {"type": "string"}},
            "commands": {"type": "array", "items": {"type": "object"}},
            "dependenciesConsulted": {"type": "array", "items": {"type": "object"}},
            "recomputeCommands": {"type": "array", "items": {"type": "string"}},
        },
        "additionalProperties": False,
    }
    jurisdiction = {
        "type": "object",
        "required": ["statementLevel", "rationale", "statementLevelReason", "searchLogRef", "endpoints"],
        "properties": {
            "statementLevel": {"const": True},
            "rationale": nonempty,
            "statementLevelReason": nonempty,
            "searchLogRef": nonempty,
            "endpoints": {
                "type": "object",
                "required": ["source", "target"],
                "properties": {"source": nonempty, "target": nonempty},
                "additionalProperties": False,
            },
        },
        "additionalProperties": False,
    }
    record = {
        "type": "object",
        "required": ["recordId", "queryId", "pairId", "status", "scopeId", "snapshot",
                     "statementVersion", "endpoints", "premises", "contextId",
                     "provenance", "activeCoverage"],
        "properties": {
            "recordId": nonempty,
            "queryId": nonempty,
            "pairId": nonempty,
            "status": {"$ref": "#/$defs/status"},
            "relationKind": {"$ref": "#/$defs/relationKind"},
            "certificateId": nonempty,
            "evidenceClass": {"$ref": "#/$defs/evidenceClass"},
            "refutationCertificateId": nonempty,
            "scopeId": nonempty,
            "snapshot": nonempty,
            "statementVersion": nonempty,
            "endpoints": {
                "type": "object",
                "required": ["source", "target"],
                "properties": {"source": statement_ref, "target": statement_ref},
                "additionalProperties": False,
            },
            "premises": {
                "type": "object",
                "required": ["predicate", "premiseIds"],
                "properties": {
                    "predicate": nonempty,
                    "premiseIds": {"type": "array", "items": {"type": "string"}},
                },
                "additionalProperties": False,
            },
            "contextId": nonempty,
            "provenance": {"type": "object", "required": ["kind"], "additionalProperties": True},
            "activeCoverage": {"const": True},
            "searchLog": search_log,
            "candidateSummary": {"type": "string"},
            "remainingGap": {"type": "string"},
            "candidateEvidenceIds": {"type": "array", "items": {"type": "string"}},
            "dependencyEvidence": {"$ref": "#/$defs/dependencyEvidence"},
            "jurisdiction": {"$ref": "#/$defs/jurisdiction"},
        },
        "additionalProperties": False,
        "allOf": [
            {
                "if": {"properties": {"status": {"const": "certified"}}, "required": ["status"]},
                "then": {
                    "required": ["relationKind", "certificateId", "evidenceClass"],
                    "properties": {"relationKind": {"enum": NON_REFUTATION_KINDS}},
                },
            },
            {
                "if": {"properties": {"status": {"const": "refuted"}}, "required": ["status"]},
                "then": {"required": ["refutationCertificateId", "evidenceClass"]},
            },
            {
                "if": {"properties": {"status": {"const": "unresolved"}}, "required": ["status"]},
                "then": {"required": ["candidateSummary", "remainingGap", "searchLog"]},
            },
            {
                "if": {"properties": {"status": {"const": "notEstablished"}}, "required": ["status"]},
                "then": {"required": ["dependencyEvidence", "searchLog"]},
            },
            {
                "if": {"properties": {"status": {"const": "outOfScope"}}, "required": ["status"]},
                "then": {"required": ["jurisdiction", "searchLog"]},
            },
            {
                "if": {"properties": {"status": {"enum": [
                    "refuted", "unresolved", "notEstablished", "outOfScope"]}},
                    "required": ["status"]},
                "then": {"not": {"required": ["relationKind"]}},
            },
        ],
    }
    pair = {
        "type": "object",
        "required": ["pairId", "theories", "primaryCluster", "requirement", "queryIds",
                     "queryCount", "outcomes", "certifiedQueryIds", "certifiedRelationKinds",
                     "hasCheckedEvidence", "hasStatementLevelOutOfScope", "coverageBasis",
                     "screened", "packages", "legacy"],
        "properties": {
            "pairId": nonempty,
            "theories": {"type": "array", "minItems": 2, "maxItems": 2,
                         "items": {"type": "string", "enum": THEORIES}},
            "primaryCluster": nonempty,
            "requirement": {
                "type": "object",
                "required": ["requiredOutcome", "permittedAlternative", "outOfScopePermitted"],
                "properties": {
                    "requiredOutcome": nonempty,
                    "permittedAlternative": {"type": ["string", "null"]},
                    "outOfScopePermitted": {"type": ["boolean", "null"]},
                },
                "additionalProperties": False,
            },
            "queryIds": {"type": "array", "minItems": 1, "items": {"type": "string"}},
            "queryCount": {"type": "integer", "minimum": 1},
            "outcomes": {"$ref": "#/$defs/statusCounts"},
            "certifiedQueryIds": {"type": "array", "items": {"type": "string"}},
            "certifiedRelationKinds": {"type": "array", "items": {"$ref": "#/$defs/relationKind"}},
            "hasCheckedEvidence": {"type": "boolean"},
            "hasStatementLevelOutOfScope": {"type": "boolean"},
            "coverageBasis": {"type": "string", "enum": [
                "certified-statement-query", "named-noncertified-query", "statement-level-outOfScope"]},
            "screened": {"const": True},
            "packages": {"type": "array", "items": {"type": "string"}},
            "legacy": {
                "type": "object",
                "required": ["pairAnchorIds", "namedRecordIds", "hasPairAnchor", "hasNamedQuery",
                             "absenceReconciled", "candidateAnchorReconciled"],
                "properties": {
                    "pairAnchorIds": {"type": "array", "items": {"type": "string"}},
                    "namedRecordIds": {"type": "array", "items": {"type": "string"}},
                    "hasPairAnchor": {"type": "boolean"},
                    "hasNamedQuery": {"type": "boolean"},
                    "absenceReconciled": {"type": "boolean"},
                    "candidateAnchorReconciled": {"type": "boolean"},
                },
                "additionalProperties": False,
            },
        },
        "additionalProperties": False,
    }
    statement = {
        "type": "object",
        "required": ["statementId", "inventoryId", "theory", "declaration",
                     "declarationKind", "screeningEligible", "sourceArtifact",
                     "sourceArtifactSha256", "sourceLine", "sourceSignature",
                     "signatureSha256", "version"],
        "properties": {
            "statementId": nonempty,
            "inventoryId": nonempty,
            "theory": {"type": "string", "enum": THEORIES},
            "declaration": nonempty,
            "declarationKind": {"type": "string", "enum": ["def", "theorem"]},
            "screeningRole": {"type": "string"},
            "screeningEligible": {"const": True},
            "sourceArtifact": path,
            "sourceArtifactSha256": sha,
            "sourceLine": {"type": "integer", "minimum": 1},
            "sourceSignature": nonempty,
            "signatureSha256": sha,
            "version": nonempty,
            "versionBasis": {"type": "string"},
        },
        "additionalProperties": False,
    }
    cert_common = {
        "certificateId": nonempty,
        "kind": {"$ref": "#/$defs/relationKind"},
        "axiomFootprint": {"type": "array", "items": {"type": "string", "enum": ALLOWED_AXIOMS}},
        "allowedAxioms": {"type": "array", "items": {"type": "string", "enum": ALLOWED_AXIOMS}},
        "activeQueryIds": {"type": "array", "items": {"type": "string"}},
        "libraryRole": nonempty,
    }
    delivered_cert = {
        "type": "object",
        "required": ["certificateId", "evidenceClass", "kind", "declaration", "module",
                     "sourcePath", "sourceSha256", "axiomFootprint", "allowedAxioms",
                     "libraryRole", "activeQueryIds", "legacyRecordIds", "legacyQueryIds",
                     "certificateStatus"],
        "properties": {
            **cert_common,
            "evidenceClass": {"const": "deliveredModule"},
            "declaration": nonempty,
            "module": nonempty,
            "sourcePath": path,
            "sourceSha256": sha,
            "legacyRecordIds": {"type": "array", "items": {"type": "string"}},
            "legacyQueryIds": {"type": "array", "items": {"type": "string"}},
            "certificateStatus": nonempty,
        },
        "additionalProperties": False,
    }
    probe_cert = {
        "type": "object",
        "required": ["certificateId", "evidenceClass", "kind", "declaration",
                     "kindCheckTheorem", "probePath", "probeSha256", "buildCommand",
                     "compileLog", "axiomFootprint", "allowedAxioms", "packageId",
                     "round", "acceptance", "packageReview", "activeQueryIds", "libraryRole"],
        "properties": {
            **cert_common,
            "evidenceClass": {"const": "boundedProbe"},
            "declaration": nonempty,
            "kindCheckTheorem": nonempty,
            "probePath": path,
            "probeSha256": sha,
            "buildCommand": nonempty,
            "compileLog": {
                "type": "object",
                "required": ["path", "sha256"],
                "properties": {"path": path, "sha256": sha},
                "additionalProperties": False,
            },
            "packageId": nonempty,
            "round": {"type": "string", "enum": ["R2", "R3", "R4", "R5"]},
            "acceptance": {"type": "string", "pattern": "^accepted-R[2-5]$"},
            "packageReview": {"type": "object"},
        },
        "additionalProperties": False,
    }
    candidate = {
        "type": "object",
        "required": ["candidateId", "evidenceClass", "isCertificate", "status", "declaration",
                     "probePath", "probeSha256", "buildCommand", "compileLog",
                     "axiomFootprint", "allowedAxioms", "attachedQueryIds",
                     "candidateSummary", "packageId", "round", "missingEvidence"],
        "properties": {
            "candidateId": nonempty,
            "evidenceClass": {"const": "boundedProbe"},
            "isCertificate": {"const": False},
            "status": {"const": "unresolved"},
            "declaration": nonempty,
            "probePath": path,
            "probeSha256": sha,
            "buildCommand": nonempty,
            "compileLog": {"type": "object"},
            "axiomFootprint": {"type": "array", "items": {"type": "string", "enum": ALLOWED_AXIOMS}},
            "allowedAxioms": {"type": "array", "items": {"type": "string", "enum": ALLOWED_AXIOMS}},
            "attachedQueryIds": {"type": "array", "minItems": 1, "items": {"type": "string"}},
            "candidateSummary": {"type": "string"},
            "packageId": nonempty,
            "round": {"type": "string", "enum": ["R2", "R3", "R4", "R5"]},
            "missingEvidence": nonempty,
        },
        "additionalProperties": False,
    }
    probe_file = {
        "type": "object",
        "required": ["path", "sha256", "packageId", "round", "buildCommand", "compileLog",
                     "certificateDeclarationCount", "candidateDeclarationCount",
                     "reviewedDeclarationCount", "certificateDeclarations",
                     "candidateDeclarations"],
        "properties": {
            "path": path,
            "sha256": sha,
            "packageId": nonempty,
            "round": {"type": "string", "enum": ["R2", "R3", "R4", "R5"]},
            "buildCommand": nonempty,
            "compileLog": {"type": "object"},
            "certificateDeclarationCount": {"type": "integer", "minimum": 0},
            "candidateDeclarationCount": {"type": "integer", "minimum": 0},
            "reviewedDeclarationCount": {"type": "integer", "minimum": 1},
            "certificateDeclarations": {"type": "array", "items": {"type": "string"}},
            "candidateDeclarations": {"type": "array", "items": {"type": "string"}},
        },
        "additionalProperties": False,
    }
    status_counts = {
        "type": "object",
        "required": STATUSES,
        "properties": {s: {"type": "integer", "minimum": 0} for s in STATUSES},
        "additionalProperties": False,
    }
    registry = {
        "type": "object",
        "required": ["$schema", "schemaVersion", "artifactKind", "mode", "round",
                     "generatedOn", "acceptance", "description", "references", "packages",
                     "theoryInventory", "counts", "coverage", "queryOutcomes",
                     "relationDiscovery", "pairs", "queries", "records", "statements",
                     "evidenceReferences", "scopes", "contexts", "snapshots", "certificateLibrary",
                     "candidateEvidence", "probeFiles", "evidencePolicy",
                     "legacyReconciliation", "companionArtifacts", "planDeviations", "nonClaims"],
        "properties": {
            "$schema": nonempty,
            "schemaVersion": {"const": "2.0.0"},
            "artifactKind": {"const": "bounded-relation-registry"},
            "mode": {"const": "bounded-full"},
            "round": {"const": "R8"},
            "generatedOn": nonempty,
            "acceptance": {"type": "string", "enum": [
                "submitted-R8-pending-review", "accepted-R8"]},
            "description": nonempty,
            "references": {"type": "object"},
            "packages": {"type": "array", "minItems": 10, "maxItems": 10},
            "theoryInventory": {"type": "array", "minItems": 17, "maxItems": 17,
                                "items": {"type": "string", "enum": THEORIES}},
            "counts": {"type": "object"},
            "coverage": {"type": "object"},
            "queryOutcomes": {"type": "object"},
            "relationDiscovery": {"type": "object"},
            "pairs": {"type": "array", "minItems": 136, "maxItems": 136,
                      "items": {"$ref": "#/$defs/pair"}},
            "queries": {"type": "array", "minItems": 152, "maxItems": 152,
                        "items": {"$ref": "#/$defs/query"}},
            "records": {"type": "array", "minItems": 152, "maxItems": 152,
                        "items": {"$ref": "#/$defs/record"}},
            "statements": {"type": "array", "items": {"$ref": "#/$defs/statement"}},
            "evidenceReferences": {"type": "array", "minItems": 77, "maxItems": 77,
                                   "items": {"type": "object"}},
            "scopes": {"type": "array"},
            "contexts": {"type": "array"},
            "snapshots": {"type": "array"},
            "certificateLibrary": {
                "type": "object",
                "required": ["evidenceClassVocabulary", "counts", "deliveredModule", "boundedProbe"],
                "properties": {
                    "evidenceClassVocabulary": {"type": "array", "items": {"$ref": "#/$defs/evidenceClass"}},
                    "counts": {"type": "object"},
                    "deliveredModule": {"type": "array", "minItems": 38, "maxItems": 38,
                                        "items": {"$ref": "#/$defs/deliveredCertificate"}},
                    "boundedProbe": {"type": "array", "minItems": 55, "maxItems": 55,
                                     "items": {"$ref": "#/$defs/probeCertificate"}},
                },
                "additionalProperties": False,
            },
            "candidateEvidence": {"type": "array", "minItems": 3, "maxItems": 3,
                                  "items": {"$ref": "#/$defs/candidateEvidence"}},
            "probeFiles": {"type": "array", "minItems": 9, "maxItems": 9,
                           "items": {"$ref": "#/$defs/probeFile"}},
            "evidencePolicy": {"type": "object"},
            "legacyReconciliation": {"type": "object"},
            "companionArtifacts": {"type": "object"},
            "planDeviations": {"type": "array", "items": {"type": "object"}},
            "nonClaims": {"type": "array", "items": {"type": "string"}},
        },
        "additionalProperties": False,
    }

    corrected_view = {
        "type": "object",
        "required": ["correctedViewId", "kind", "legacyQueryId", "legacyRecordId",
                     "certificateId", "certificateUnchanged", "activeQueryIds",
                     "primaryActiveQueryId", "corrections", "correctedQueryView",
                     "correctedRecordView", "correctedEndpoints"],
        "properties": {
            "correctedViewId": nonempty,
            "kind": {"const": "corrected-legacy-query-record-view"},
            "legacyQueryId": nonempty,
            "legacyRecordId": nonempty,
            "certificateId": nonempty,
            "certificateUnchanged": {"const": True},
            "activeQueryIds": {"type": "array", "minItems": 1, "items": {"type": "string"}},
            "primaryActiveQueryId": nonempty,
            "relatedActiveQueryIds": {"type": "array", "items": {"type": "string"}},
            "corrections": {"type": "array", "minItems": 1, "items": {"type": "object"}},
            "correctedQueryView": {"type": "object"},
            "correctedRecordView": {"type": "object"},
            "correctedEndpoints": {"type": "object"},
        },
        "additionalProperties": False,
    }
    reconciliation = {
        "type": "object",
        "required": ["reconciliationId", "legacyAnchorKind", "oldScopeId", "oldSnapshot",
                     "newEvidence", "activeQueryIds", "scopeRelationship",
                     "relationshipRationale", "oldSearchIsNotRefutation",
                     "oldProseRetained", "oldProseIsCurrentVerdict",
                     "newEvidenceOverridesOldProseInNamedScope"],
        "properties": {
            "reconciliationId": nonempty,
            "legacyAnchorKind": {"type": "string", "enum": ["notEstablished", "unresolved-candidate"]},
            "oldScopeId": nonempty,
            "oldSnapshot": nonempty,
            "newEvidence": {"type": "array", "minItems": 1, "items": {"type": "object"}},
            "activeQueryIds": {"type": "array", "minItems": 1, "items": {"type": "string"}},
            "scopeRelationship": {"type": "string", "enum": [
                "subsumed", "superseded-in-named-scope", "coexists-different-scope"]},
            "relationshipRationale": nonempty,
            "oldSearchIsNotRefutation": {"const": True},
            "oldProseRetained": {"const": True},
            "oldProseIsCurrentVerdict": {"const": False},
            "newEvidenceOverridesOldProseInNamedScope": {"type": "boolean"},
        },
        "additionalProperties": False,
    }
    disposition = {
        "type": "object",
        "required": ["dispositionId", "legacyQueryId", "legacyRecordId", "legacyKind",
                     "pairId", "theories", "intraTheory", "legacyStatus",
                     "legacyRelationKind", "legacyCertificateId", "legacyScope",
                     "legacyStatementVersion", "legacyQuestion", "legacyRationale",
                     "legacyProvenance", "legacySource", "activeQueryIds",
                     "relatedActiveQueryIds", "checkedActiveQueryIds", "activeQueryLinkBasis",
                     "countsTowardActiveCoverage", "activeCoverageContribution",
                     "proseRetention", "disposition"],
        "properties": {
            "dispositionId": nonempty,
            "legacyQueryId": nonempty,
            "legacyRecordId": nonempty,
            "legacyKind": {"type": "string", "enum": ["named-query", "pair-anchor"]},
            "pairId": {"type": ["string", "null"]},
            "theories": {"type": "array", "items": {"type": "string", "enum": THEORIES}},
            "intraTheory": {"type": "boolean"},
            "legacyStatus": {"type": "string", "enum": ["certified", "unresolved", "notEstablished"]},
            "legacyRelationKind": {"type": ["string", "null"]},
            "legacyCertificateId": {"type": ["string", "null"]},
            "legacyScope": {"type": "object"},
            "legacyStatementVersion": nonempty,
            "legacyQuestion": nonempty,
            "legacyRationale": nonempty,
            "legacyProvenance": {"type": "object"},
            "legacySource": {"type": "object"},
            "activeQueryIds": {"type": "array", "items": {"type": "string"}},
            "relatedActiveQueryIds": {"type": "array", "items": {"type": "string"}},
            "checkedActiveQueryIds": {"type": "array", "items": {"type": "string"}},
            "activeQueryLinkBasis": {"type": "array", "items": {"type": "string"}},
            "countsTowardActiveCoverage": {"const": False},
            "activeCoverageContribution": {
                "type": "object",
                "required": ["pairCount", "queryCount"],
                "properties": {"pairCount": {"const": 0}, "queryCount": {"const": 0}},
                "additionalProperties": False,
            },
            "proseRetention": {"type": "object"},
            "disposition": {"type": "string", "enum": [
                "reused-as-active-evidence", "repaired-and-reused",
                "repaired-and-restated", "recertified-statement-level",
                "retained-legacy-support", "retained-refutation-evidence",
                "retained-intra-theory-evidence", "retained-scoped-absence",
                "retained-unresolved-candidate",
                "reconciled-absence-with-active-evidence",
                "reconciled-candidate-with-active-evidence",
            ]},
            "correctedLegacyView": {"$ref": "#/$defs/correctedLegacyView"},
            "absenceReconciliation": {"$ref": "#/$defs/absenceReconciliation"},
        },
        "additionalProperties": False,
        "allOf": [
            {
                "if": {"properties": {"legacyKind": {"const": "pair-anchor"}},
                       "required": ["legacyKind"]},
                "then": {
                    "properties": {
                        "activeCoverageContribution": {
                            "properties": {"pairCount": {"const": 0}, "queryCount": {"const": 0}}
                        },
                    },
                },
            },
            {
                "if": {"properties": {"intraTheory": {"const": True}}, "required": ["intraTheory"]},
                "then": {"properties": {"pairId": {"const": None}}},
            },
            {
                "if": {"properties": {"disposition": {"const": "reconciled-absence-with-active-evidence"}},
                       "required": ["disposition"]},
                "then": {"required": ["absenceReconciliation"]},
            },
            {
                "if": {"properties": {"disposition": {"const": "reconciled-candidate-with-active-evidence"}},
                       "required": ["disposition"]},
                "then": {"required": ["absenceReconciliation"]},
            },
        ],
    }
    dispositions = {
        "type": "object",
        "required": ["$schema", "schemaVersion", "artifactKind", "mode", "round",
                     "generatedOn", "acceptance", "description", "source",
                     "dispositionVocabulary", "scopeRelationshipVocabulary",
                     "aliasRepairs", "correctedLegacyViews", "summary", "entries",
                     "nonClaims"],
        "properties": {
            "$schema": nonempty,
            "schemaVersion": {"const": "1.0.0"},
            "artifactKind": {"const": "legacy-disposition-ledger"},
            "mode": {"const": "bounded-full"},
            "round": {"const": "R8"},
            "generatedOn": nonempty,
            "acceptance": {"type": "string", "enum": [
                "submitted-R8-pending-review", "accepted-R8"]},
            "description": nonempty,
            "source": {"type": "object"},
            "dispositionVocabulary": {"type": "array", "minItems": 11, "items": {"type": "string"}},
            "scopeRelationshipVocabulary": {"type": "array", "minItems": 3,
                                            "items": {"type": "string"}},
            "aliasRepairs": {"type": "array", "minItems": 4, "maxItems": 4,
                             "items": {"type": "object"}},
            "correctedLegacyViews": {"type": "array", "minItems": 3, "maxItems": 3,
                                     "items": {"type": "object"}},
            "summary": {"type": "object"},
            "entries": {"type": "array", "minItems": 151, "maxItems": 151,
                        "items": {"$ref": "#/$defs/dispositionEntry"}},
            "nonClaims": {"type": "array", "items": {"type": "string"}},
        },
        "additionalProperties": False,
    }

    schema = {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://photolean.local/relation_audit/schema.accepted.json",
        "title": "PhotoLean Bounded Relation Audit Accepted Schema v2.0 (R8)",
        "description": "Additive schema for the R8 bounded registry and its legacy disposition ledger. It supports five query outcomes, seven relation kinds and the deliveredModule/boundedProbe evidence classes. It does not modify the legacy schema.",
        "oneOf": [
            {"$ref": "#/$defs/registry"},
            {"$ref": "#/$defs/legacyDispositions"},
        ],
        "$defs": {
            "status": {"type": "string", "enum": STATUSES},
            "relationKind": {"type": "string", "enum": RELATION_KINDS},
            "evidenceClass": {"type": "string", "enum": EVIDENCE_CLASSES},
            "statusCounts": status_counts,
            "evidence": evidence,
            "endpoint": endpoint,
            "query": query,
            "record": record,
            "pair": pair,
            "statement": statement,
            "dependencyEvidence": dependency,
            "jurisdiction": jurisdiction,
            "deliveredCertificate": delivered_cert,
            "probeCertificate": probe_cert,
            "candidateEvidence": candidate,
            "probeFile": probe_file,
            "correctedLegacyView": corrected_view,
            "absenceReconciliation": reconciliation,
            "dispositionEntry": disposition,
            "registry": registry,
            "legacyDispositions": dispositions,
        },
    }
    return schema


def check_registry_semantics(registry, dispositions, legacy, idx):
    # No alias may be used as an active endpoint, declaration reference or
    # statement object.  Accepted package provenance notes may *mention* an
    # alias while explaining the repair; the repair crosswalk lives in the
    # disposition ledger.
    alias_ids = {a["aliasStatementId"] for a in ALIASES}
    alias_decls = {a["aliasDeclaration"] for a in ALIASES}
    for srow in registry["statements"]:
        require(srow["statementId"] not in alias_ids,
                f"alias used as active statement: {srow['statementId']}")
        require(srow["declaration"] not in alias_decls,
                f"alias declaration used as active statement: {srow['declaration']}")
    for q in registry["queries"]:
        for role in ("source", "target"):
            require(q["endpoints"][role]["statementId"] not in alias_ids,
                    f"{q['queryId']}: alias active endpoint {role}")
            require(q["endpoints"][role]["declaration"] not in alias_decls,
                    f"{q['queryId']}: alias active declaration {role}")
    def walk(node):
        if isinstance(node, dict):
            for key, value in node.items():
                if key in ("statementId", "inventoryId") and isinstance(value, str):
                    require(value not in alias_ids, f"alias used as {key}: {value}")
                elif key == "declaration" and isinstance(value, str):
                    require(value not in alias_decls, f"alias used as declaration: {value}")
                else:
                    walk(value)
        elif isinstance(node, list):
            for item in node:
                walk(item)
    walk(registry)
    # Every pair has a query or a statement-level outOfScope record.
    q_by_id = {q["queryId"]: q for q in registry["queries"]}
    for p in registry["pairs"]:
        require(p["queryIds"], f"pair {p['pairId']} has no query")
        require(any(q_by_id[qid]["outcome"]["status"] == "outOfScope" for qid in p["queryIds"])
                or any(q_by_id[qid]["outcome"]["status"] != "outOfScope" for qid in p["queryIds"]),
                f"pair {p['pairId']} has no statement-level record")
    # Certificate library and active record cross-references.
    lib = {c["certificateId"]: c for c in
           registry["certificateLibrary"]["deliveredModule"] +
           registry["certificateLibrary"]["boundedProbe"]}
    require(len(lib) == 93, "certificate library IDs are not unique")
    active_cert_records = [r for r in registry["records"] if r["status"] == "certified"]
    require(len(active_cert_records) == 67, "active certified records mismatch")
    require(all(r["certificateId"] in lib for r in active_cert_records),
            "active record certificate missing from library")
    used = collections.Counter(lib[r["certificateId"]]["evidenceClass"] for r in active_cert_records)
    require(used == {"boundedProbe": 55, "deliveredModule": 12},
            f"active evidence class counts mismatch: {dict(used)}")
    # Candidate declarations are not certificates.
    cert_decls = {c["declaration"] for c in
                  registry["certificateLibrary"]["deliveredModule"] +
                  registry["certificateLibrary"]["boundedProbe"]}
    for c in registry["candidateEvidence"]:
        require(c["declaration"] not in cert_decls, f"candidate promoted to certificate: {c['declaration']}")
    # Every active endpoint resolves to a real statement row.
    stmt_ids = {s["statementId"] for s in registry["statements"]}
    for q in registry["queries"]:
        for role in ("source", "target"):
            require(q["endpoints"][role]["statementId"] in stmt_ids,
                    f"{q['queryId']}: endpoint missing from statements")
    # Legacy dispositions exactly once and 26/125.
    entries = dispositions["entries"]
    require(len(entries) == 151, "disposition count mismatch")
    require(len({e["legacyRecordId"] for e in entries}) == 151, "legacy record disposed twice")
    require(len({e["legacyQueryId"] for e in entries}) == 151, "legacy query disposed twice")
    old_records = {r["id"] for r in legacy["records"]}
    require({e["legacyRecordId"] for e in entries} == old_records,
            "disposition record set does not equal legacy record set")
    named = [e for e in entries if e["legacyKind"] == "named-query"]
    anchors = [e for e in entries if e["legacyKind"] == "pair-anchor"]
    require(len(named) == 26 and len(anchors) == 125, "legacy 26/125 split mismatch")
    require(sum(1 for e in entries if e["intraTheory"]) == 5, "intra-theory disposition count mismatch")
    # Every old notEstablished anchor whose pair has checked evidence is reconciled.
    for e in anchors:
        rec = idx["legacy_record_by_id"][e["legacyRecordId"]]
        pair = next((p for p in registry["pairs"] if p["pairId"] == e["pairId"]), None)
        require(pair is not None, f"anchor pair missing: {e['pairId']}")
        if rec["status"] == "notEstablished" and pair["hasCheckedEvidence"]:
            require("absenceReconciliation" in e,
                    f"missing absence reconciliation for {e['legacyRecordId']}")
            require(e["absenceReconciliation"]["activeQueryIds"],
                    f"empty reconciliation active query ids for {e['legacyRecordId']}")
            require(e["absenceReconciliation"]["scopeRelationship"] in
                    ("subsumed", "superseded-in-named-scope", "coexists-different-scope"),
                    f"invalid scope relationship for {e['legacyRecordId']}")
            require(e["absenceReconciliation"]["oldSearchIsNotRefutation"] is True,
                    f"old failed search became refutation for {e['legacyRecordId']}")
    # Four alias repairs, three corrected views.
    require(len(dispositions["aliasRepairs"]) == 4, "alias repair count mismatch")
    require(len(dispositions["correctedLegacyViews"]) == 3, "corrected view count mismatch")
    for rep in dispositions["aliasRepairs"]:
        require(rep["sourceEvidence"]["realInventoryStatement"]["statementId"]
                in {s["statementId"] for s in registry["statements"]},
                f"alias real endpoint not in active statements: {rep['aliasRepairId']}")
    # Old anchors and intra-theory records never contribute coverage.
    for e in entries:
        require(e["countsTowardActiveCoverage"] is False, "legacy entry counts toward coverage")
        require(e["activeCoverageContribution"] == {"pairCount": 0, "queryCount": 0},
                "legacy entry contributes coverage")
    return True


def render_docs(registry, dispositions):
    c = registry["counts"]
    lines = []
    lines.append("# Accepted bounded relation-audit registry (R8 submission)")
    lines.append("")
    if registry["acceptance"] == PENDING:
        lines.append("**Acceptance state: `submitted-R8-pending-review`.** This snapshot is not accepted. "
                     "Only two independent K3.1 Pro reviews followed by the lead's acceptance flip may "
                     "change the top-level `acceptance` value to `accepted-R8`.")
    else:
        lines.append("**Acceptance state: `accepted-R8`.** Two independent K3.1 Pro reviews "
                     "passed and the lead recorded the uniform registry/disposition acceptance "
                     "flip. The registry and the disposition ledger share this state.")
    lines.append("")
    lines.append("## What this snapshot is")
    lines.append("")
    lines.append("The registry is a deterministic, machine-auditable integration of the accepted "
                 "R1 boundary, the accepted R2-R5 screening packages, the final R7 coverage ledger "
                 "and the unchanged legacy registry. It separates three dimensions that must not be "
                 "conflated:")
    lines.append("")
    lines.append("- **Pair coverage:** 136/136 pairs have a named statement-level query or a statement-level "
                 "`outOfScope` record. This is not a certification count.")
    lines.append("- **Query outcomes:** 152 active named queries: 67 certified, 0 refuted, 39 unresolved, "
                 "2 notEstablished, 44 outOfScope.")
    lines.append("- **Certified relation discovery:** 67 certified queries over 53 distinct pairs, with "
                 "7 declared relation kinds available and no `refuted` outcome in this snapshot.")
    lines.append("")
    lines.append("## Counts")
    lines.append("")
    lines.append("| Dimension | Value |")
    lines.append("| --- | ---: |")
    lines.append(f"| Accepted screening packages | {c['packages']} |")
    lines.append(f"| Pair universe / pairs with screening | 136 / {c['pairs']} |")
    lines.append(f"| Active named queries | {c['activeQueries']} |")
    lines.append(f"| Active records | {c['activeRecords']} |")
    lines.append(f"| Certified / refuted / unresolved / notEstablished / outOfScope | "
                 f"{c['queryOutcomes']['certified']} / {c['queryOutcomes']['refuted']} / "
                 f"{c['queryOutcomes']['unresolved']} / {c['queryOutcomes']['notEstablished']} / "
                 f"{c['queryOutcomes']['outOfScope']} |")
    lines.append(f"| Pairs with at least one certified relation | {c['certifiedPairs']} |")
    lines.append(f"| Certificate library (total / deliveredModule / boundedProbe) | "
                 f"{c['certificateLibrary']['total']} / {c['certificateLibrary']['deliveredModule']} / "
                 f"{c['certificateLibrary']['boundedProbe']} |")
    lines.append(f"| Active certified evidence (probe / reused legacy) | "
                 f"{c['activeCertifiedEvidence']['boundedProbe']} / "
                 f"{c['activeCertifiedEvidence']['deliveredModule']} |")
    lines.append(f"| XD1 candidate declarations (not certificates) | {c['candidateDeclarations']} |")
    lines.append(f"| Probe files / reviewed declarations | {c['probeFiles']} / {c['probeReviewedDeclarations']} |")
    lines.append(f"| Evidence references (supporting delivered theorems) | {c['evidenceReferences']} |")
    lines.append(f"| Legacy records disposed / named / pair anchors | "
                 f"{c['legacy']['records']} / {c['legacy']['namedQueries']} / {c['legacy']['pairAnchors']} |")
    lines.append(f"| Legacy alias repairs / corrected certified records | "
                 f"{c['legacy']['aliases']} / {c['legacy']['correctedRecords']} |")
    lines.append(f"| Old absence/new evidence reconciliations | {c['legacy']['absenceReconciliations']} |")
    lines.append("")
    lines.append("Note on the package count: the plan's prose says \"eight accepted R2-R5 screening "
                 "packages\". The actual accepted artifacts contain **ten** packages (R2 one, R3 one, "
                 "R4 three, R5 five), and all ten are required to reach the contract's 136 pairs / 152 "
                 "queries. No package was dropped or invented; this is a reported plan-metadata "
                 "deviation, not a data substitution.")
    lines.append("")
    lines.append("## Five outcomes and seven kinds")
    lines.append("")
    lines.append("The schema and records implement the five outcomes `certified`, `refuted`, `unresolved`, "
                 "`notEstablished`, `outOfScope` and the seven relation kinds "
                 "`definitionalIdentity`, `implication`, `equivalence`, `conditionalComposition`, "
                 "`observationalEquivalence`, `distinguishability`, `refutation`.")
    lines.append("")
    lines.append("- `certified` requires a library certificate and a non-refutation relation kind.")
    lines.append("- `refuted` requires a refutation certificate and is an outcome; it is not an eighth kind. "
                 "No active query is refuted in this snapshot.")
    lines.append("- `unresolved` requires a named remaining candidate/gap and a search-log entry.")
    lines.append("- `notEstablished` requires machine-recomputable scoped dependency evidence.")
    lines.append("- `outOfScope` requires a statement-level jurisdiction finding and provenance.")
    lines.append("")
    lines.append("Contexts, translations, premise predicates and IDs, versions, scopes and snapshots, "
                 "observation channels/domains, falsification conditions and provenance are preserved "
                 "from the accepted query objects.")
    lines.append("")
    lines.append("The 77 unique supporting theorems cited inside accepted evidence are resolved in "
                 "`evidenceReferences`: 54 are R1 inventory rows and 23 are delivered "
                 "`PhotoLean/Relations.lean` theorems outside the seventeen-theory statement authority. "
                 "They are supporting evidence, not active statement endpoints; every active endpoint "
                 "still resolves to an R1 inventory declaration.")
    lines.append("")
    lines.append("## Evidence classes")
    lines.append("")
    lines.append("### deliveredModule")
    lines.append("")
    lines.append("A certificate declared in the frozen `PhotoLean/**/*.lean` tree. The legacy full-registry "
                 "validator remains the evidence gate. All 38 legacy certificates are retained in the "
                 "library; 12 are directly reused by active certified queries and 26 remain explicit "
                 "retained legacy/support evidence without creating fake active pair queries.")
    lines.append("")
    lines.append("### boundedProbe")
    lines.append("")
    lines.append("A package-local certificate compiled directly from an accepted probe file under "
                 "`bounded_audit/`, outside the frozen default build targets. Each entry carries its "
                 "accepted package provenance, exact probe path and SHA-256, certificate declaration "
                 "and kind-check theorem, direct serial compile command, compile/axiom log, live "
                 "allowed-axiom footprint (`propext`, `Classical.choice`, `Quot.sound`) and package "
                 "review reference.")
    lines.append("")
    lines.append("The nine probe files contain 58 reviewed declarations: 55 certificate declarations "
                 "and 3 XD1 candidate declarations. The candidates are attached only to unresolved "
                 "queries and are excluded from the certificate library by construction. The integrated "
                 "validator must serially compile all nine probes, audit all 58 declarations, run the "
                 "package placeholder/custom-axiom gates and the original legacy full validator.")
    lines.append("")
    lines.append("| Probe file | Certificates | Candidates | Reviewed |")
    lines.append("| --- | ---: | ---: | ---: |")
    for f in registry["probeFiles"]:
        lines.append(f"| `{f['path']}` | {f['certificateDeclarationCount']} | "
                     f"{f['candidateDeclarationCount']} | {f['reviewedDeclarationCount']} |")
    lines.append("")
    lines.append("## Legacy reconciliation")
    lines.append("")
    lines.append("The companion `relation_audit/legacy-dispositions.accepted.json` disposes every one "
                 "of the 151 unchanged legacy records exactly once: 26 named queries and 125 pair "
                 "anchors. Legacy prose is retained verbatim in the ledger; no old record is deleted "
                 "or rewritten.")
    lines.append("")
    lines.append("Four R1 legacy statement IDs are metadata aliases, not delivered declarations: "
                 "`PhotoLean.BEP.rateViaEact`, `PhotoLean.Marcus.rateDescriptor`, "
                 "`PhotoLean.EnergyGapLaw.nrBarrier_eq_zero` and "
                 "`PhotoLean.StokesShift.emEnergy_eq_zero`. They affect three certified legacy records "
                 "(`rec-D-S05-bep-rate-eq-exp-neg-eact`, "
                 "`rec-D-S06-hammond-sharp-iff-marcus-sharp`, "
                 "`rec-D-S15-egBarrier-zero-iff-emEnergy-zero`). The disposition ledger records all four "
                 "alias-to-real mappings with inventory and package source evidence, and gives each "
                 "affected record an explicit corrected query/record view with real endpoint statement "
                 "IDs and corrected `statementVersion`, linked to the unchanged legacy certificate and "
                 "to the corresponding active bounded query.")
    lines.append("")
    lines.append("For the 41 old `notEstablished` pair anchors whose pair now has checked evidence, the "
                 "ledger records the active query IDs and the precise relationship "
                 "`superseded-in-named-scope`: the old statement was only a snapshot absence and is "
                 "superseded within the named statement scope, while the old prose remains a historical "
                 "record outside it. For the three legacy undelivered-candidate anchors that now have "
                 "checked evidence, the relationship is `coexists-different-scope`: the old candidate "
                 "and the new statement-level relation are different scopes, so neither silently "
                 "overwrites the other. No failed search is converted into a refutation.")
    lines.append("")
    lines.append("The 125 legacy pair anchors and the five intra-theory legacy records contribute "
                 "**zero** active pair or query coverage. Pair anchors are coverage history; intra-theory "
                 "records are retained support evidence.")
    lines.append("")
    lines.append("## Deterministic generation")
    lines.append("")
    lines.append("Run from the isolated PhotoLean repository root:")
    lines.append("")
    lines.append("```bash")
    if registry["acceptance"] == PENDING:
        lines.append("python3 tools/relation_audit_bounded/build.py")
    else:
        lines.append("python3 tools/relation_audit_bounded/build.py --acceptance accepted-R8")
    lines.append("```")
    lines.append("")
    if registry["acceptance"] == ACCEPTED:
        lines.append("The default acceptance state remains `submitted-R8-pending-review`; the "
                     "accepted artifact is regenerated only with the explicit "
                     "`--acceptance accepted-R8` state.")
        lines.append("")
    lines.append("The builder reads only frozen/accepted inputs, sorts every collection deterministically, "
                 "uses no wall clock or random state, and writes with `sort_keys=True`, two-space "
                 "indentation, UTF-8 and a final newline. It contains no output self-hash and creates no "
                 "hash cycle. It never edits the legacy registry, accepted packages, frozen PhotoLean "
                 "tree or backup.")
    lines.append("")
    lines.append("## Input references")
    lines.append("")
    lines.append("| Input | SHA-256 |")
    lines.append("| --- | --- |")
    for label, ref in (
        ("R1 boundary", registry["references"]["r1"]["boundary"]),
        ("R1 statement inventory", registry["references"]["r1"]["statementInventory"]),
        ("R1 pair queue", registry["references"]["r1"]["pairQueue"]),
        ("R1 cluster plan", registry["references"]["r1"]["clusterPlan"]),
        ("R7 coverage ledger", registry["references"]["coverageLedger"]),
        ("Legacy registry", registry["references"]["legacyRegistry"]),
        ("R4 frozen coverage", registry["references"]["frozenR4Coverage"]),
    ):
        lines.append(f"| {label} (`{ref['path']}`) | `{ref['sha256']}` |")
    for pkg in registry["references"]["acceptedPackages"]:
        lines.append(f"| {pkg['round']} {pkg['packageId']} screening (`{pkg['screening']['path']}`) | "
                     f"`{pkg['screening']['sha256']}` |")
    lines.append("")
    lines.append("## Non-claims")
    lines.append("")
    for n in registry["nonClaims"]:
        lines.append(f"- {n}")
    lines.append("")
    if registry["acceptance"] == PENDING:
        lines.append("Independent validation is intentionally out of scope for this builder. The next "
                     "agent must write the fail-closed validator and report; this document must not be "
                     "read as an acceptance record.")
    else:
        lines.append("Independent validation is recorded by the fail-closed validator and its report; "
                     "the acceptance state was set only after two independent K3.1 Pro reviews passed "
                     "and the lead recorded the acceptance flip. This document is the accepted "
                     "snapshot's documentation, not additional evidence.")
    lines.append("")
    return "\n".join(lines)


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8", newline="\n")
    os.replace(tmp, path)


def write_json(path: Path, obj) -> None:
    text = json.dumps(obj, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    write_text(path, text)


def validate_schema(registry, dispositions, schema) -> None:
    try:
        import jsonschema
    except ImportError:
        print("NOTE: jsonschema not installed; skipped draft 2020-12 self-validation")
        return
    jsonschema.Draft202012Validator.check_schema(schema)
    validator = jsonschema.Draft202012Validator(schema)
    for name, instance, ref in (
        ("registry", registry, "#/$defs/registry"),
        ("legacyDispositions", dispositions, "#/$defs/legacyDispositions"),
    ):
        sub = validator.evolve(schema={"$ref": ref})
        errors = sorted(sub.iter_errors(instance), key=lambda e: list(e.path))
        if errors:
            msg = "\n".join(f"  {list(e.path)}: {e.message}" for e in errors[:20])
            fail(f"schema validation failed for {name}:\n{msg}")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Deterministic builder for the R8 bounded relation-audit snapshot.")
    parser.add_argument(
        "--acceptance", type=parse_acceptance, default=PENDING,
        metavar="{submitted-R8-pending-review,accepted-R8}",
        help="uniform acceptance state for the registry and disposition ledger "
             "(default: submitted-R8-pending-review)")
    args = parser.parse_args(argv)
    acceptance = args.acceptance

    inventory, queue, clusters, coverage, legacy = load_boundary()
    r1_parser = load_r1_validator()
    packages = load_packages(coverage)
    idx = build_indexes(inventory, legacy, packages)

    registry = build_registry(inventory, queue, clusters, coverage, legacy, packages,
                              r1_parser, acceptance)
    dispositions = build_dispositions_file(legacy, coverage, packages,
                                           registry["queries"], idx,
                                           registry["pairs"], acceptance)
    schema = build_schema()

    validate_schema(registry, dispositions, schema)
    check_registry_semantics(registry, dispositions, legacy, idx)

    # The state is uniform by construction; assert it before writing anything.
    require(registry["acceptance"] == acceptance, "registry acceptance state drifted")
    require(dispositions["acceptance"] == acceptance,
            "disposition acceptance state drifted")
    require(acceptance in ACCEPTANCE_STATES, "invalid final acceptance state")

    # Recompute the core counts one final time from the generated objects.
    require(len(registry["pairs"]) == 136, "final pair count")
    require(len(registry["queries"]) == 152, "final query count")
    require(len(registry["records"]) == 152, "final record count")
    require(status_counts(registry["queries"]) == EXPECTED_ACTIVE["outcomes"], "final outcomes")
    require(len(registry["certificateLibrary"]["deliveredModule"]) == 38, "final library delivered")
    require(len(registry["certificateLibrary"]["boundedProbe"]) == 55, "final library probe")
    require(len(dispositions["entries"]) == 151, "final dispositions")

    write_json(REGISTRY_OUT, registry)
    write_json(SCHEMA_OUT, schema)
    write_json(DISPOSITIONS_OUT, dispositions)
    write_text(DOC_OUT, render_docs(registry, dispositions))

    print("R8 builder: PASS")
    print(f"  acceptance: {acceptance} (registry and dispositions)")
    print(f"  packages: {len(packages)}")
    print(f"  pairs: {len(registry['pairs'])} (screened {registry['coverage']['pairsWithScreening']})")
    print(f"  queries: {len(registry['queries'])} {registry['counts']['queryOutcomes']}")
    print(f"  certified pairs: {registry['counts']['certifiedPairs']}")
    print(f"  certificate library: {registry['counts']['certificateLibrary']}")
    print(f"  active certified evidence: {registry['counts']['activeCertifiedEvidence']}")
    print(f"  probe files / declarations: {registry['counts']['probeFiles']} / "
          f"{registry['counts']['probeReviewedDeclarations']}")
    print(f"  legacy dispositions: {dispositions['summary']['records']} "
          f"({dispositions['summary']['namedQueries']} named + "
          f"{dispositions['summary']['pairAnchors']} anchors)")
    print(f"  alias repairs / corrected records: "
          f"{dispositions['summary']['aliasRepairs']} / "
          f"{dispositions['summary']['correctedRecords']}")
    print(f"  absence reconciliations: {dispositions['summary']['absenceReconciliations']} "
          f"{dispositions['summary']['scopeRelationships']}")
    print(f"  registry: {REGISTRY_OUT.relative_to(ROOT)}")
    print(f"  schema: {SCHEMA_OUT.relative_to(ROOT)}")
    print(f"  dispositions: {DISPOSITIONS_OUT.relative_to(ROOT)}")
    print(f"  docs: {DOC_OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except SystemExit:
        raise
    except Exception as exc:  # fail closed
        print(f"FAIL: internal error: {type(exc).__name__}: {exc}")
        raise
