#!/usr/bin/env python3
"""R8 adversarial mutation suite for the independent bounded-registry validator.

Every mutation is applied to a deep copy written under a temporary directory;
no repository file is modified.  Each mutation must make the validator exit
non-zero (fail closed).  The unmutated pending snapshot and a uniformly
accepted copy of it must both pass the same structural checks.  Deterministic
rebuild is exercised for the pending state and, separately, for a fully
accepted artifact set with rebuild enabled (default paths and custom
``--registry``/``--dispositions`` paths).  An invalid builder ``--acceptance``
value must be rejected before any output is written.

Run from the PhotoLean checkout root:

    python3 tools/relation_audit_bounded/tests/test_adversarial.py

Exit 0 means every positive control passed and all mutations were rejected.
"""

from __future__ import annotations

import copy
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
VALIDATOR = ROOT / "tools/relation_audit_bounded/validate.py"
BUILD = ROOT / "tools/relation_audit_bounded/build.py"
REGISTRY = ROOT / "relation_audit/registry.accepted.json"
DISPOSITIONS = ROOT / "relation_audit/legacy-dispositions.accepted.json"
SCHEMA = ROOT / "relation_audit/schema.accepted.json"
DOCS = ROOT / "docs/RELATION-AUDIT-ACCEPTED.md"

SKIP_FLAGS = [
    "--skip-external",
    "--skip-probe-compile",
    "--skip-rebuild",
    "--skip-original",
]

REBUILD_FLAGS = [
    "--skip-external",
    "--skip-probe-compile",
    "--skip-original",
]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_validator(registry: Path, dispositions: Path) -> subprocess.CompletedProcess:
    command = [
        sys.executable, str(VALIDATOR),
        "--root", str(ROOT),
        "--registry", str(registry),
        "--dispositions", str(dispositions),
        "--schema", str(SCHEMA),
        *SKIP_FLAGS,
    ]
    return subprocess.run(command, cwd=str(ROOT), capture_output=True, text=True,
                          timeout=600)


def prepare_isolated_root(parent: Path, acceptance: str) -> Path:
    """Copy the checker inputs to /tmp and generate a complete artifact set."""
    dst = parent / "photolean"
    for rel in ("PhotoLean", "audit_boundary", "bounded_audit",
                "relation_audit", "docs"):
        shutil.copytree(ROOT / rel, dst / rel,
                        ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    (dst / "tools/relation_audit_bounded").mkdir(parents=True, exist_ok=True)
    shutil.copy2(BUILD, dst / "tools/relation_audit_bounded/build.py")
    proc = subprocess.run(
        [sys.executable, "tools/relation_audit_bounded/build.py",
         "--acceptance", acceptance],
        cwd=str(dst), capture_output=True, text=True, timeout=600,
    )
    if proc.returncode != 0:
        raise AssertionError(
            f"isolated builder failed for {acceptance!r}: "
            f"{proc.stdout[-2000:]}\n{proc.stderr[-2000:]}")
    return dst


def run_rebuild_validator(root: Path, registry: Path | None = None,
                          dispositions: Path | None = None) -> subprocess.CompletedProcess:
    command = [
        sys.executable, str(VALIDATOR),
        "--root", str(root),
        *REBUILD_FLAGS,
        "--quiet",
    ]
    if registry is not None:
        command += ["--registry", str(registry)]
    if dispositions is not None:
        command += ["--dispositions", str(dispositions)]
    return subprocess.run(command, cwd=str(root), capture_output=True, text=True,
                          timeout=900)


def first_query(registry: dict, status: str | None = None) -> dict:
    for query in registry["queries"]:
        if status is None or query["outcome"]["status"] == status:
            return query
    raise AssertionError(f"no query with status {status}")


def first_certificate(registry: dict) -> dict:
    return registry["certificateLibrary"]["boundedProbe"][0]


def first_reconciled(dispositions: dict) -> dict:
    for entry in dispositions["entries"]:
        if "absenceReconciliation" in entry:
            return entry
    raise AssertionError("no reconciled disposition")


def mutate_missing_pair(registry, dispositions):
    registry["pairs"].pop(0)


def mutate_duplicate_pair(registry, dispositions):
    registry["pairs"].append(copy.deepcopy(registry["pairs"][0]))


def mutate_pair_anchor_substitution(registry, dispositions):
    pair = registry["pairs"][0]
    pair["queryIds"] = []
    pair["queryCount"] = 0
    pair["outcomes"] = {status: 0 for status in (
        "certified", "refuted", "unresolved", "notEstablished", "outOfScope")}
    pair["coverageBasis"] = "legacy-pair-anchor"
    pair["hasCheckedEvidence"] = False


def mutate_wrong_outcome(registry, dispositions):
    query = first_query(registry, "certified")
    query["outcome"]["status"] = "unresolved"


def mutate_certified_without_evidence(registry, dispositions):
    query = first_query(registry, "certified")
    query["outcome"]["evidence"].pop("certificateId", None)


def mutate_candidate_promoted(registry, dispositions):
    candidate = copy.deepcopy(registry["candidateEvidence"][0])
    candidate["evidenceClass"] = "boundedProbe"
    candidate["libraryRole"] = "active-certificate"
    registry["certificateLibrary"]["boundedProbe"].append(candidate)


def mutate_unknown_alias_endpoint(registry, dispositions):
    query = first_query(registry)
    query["endpoints"]["source"]["statementId"] = (
        "stmt-BEP-PhotoLean-BEP-rateViaEact")
    query["endpoints"]["source"]["declaration"] = "PhotoLean.BEP.rateViaEact"


def mutate_unrepaired_legacy_record(registry, dispositions):
    for entry in dispositions["entries"]:
        if entry["legacyRecordId"] == "rec-D-S05-bep-rate-eq-exp-neg-eact":
            entry.pop("correctedLegacyView", None)
            break
    else:
        raise AssertionError("corrected record not found")


def mutate_missing_legacy_disposition(registry, dispositions):
    dispositions["entries"].pop(0)


def mutate_absence_reconciliation_removed(registry, dispositions):
    first_reconciled(dispositions).pop("absenceReconciliation", None)


def mutate_stale_probe_hash(registry, dispositions):
    registry["probeFiles"][0]["sha256"] = "0" * 64


def mutate_forbidden_axiom_footprint(registry, dispositions):
    entry = first_certificate(registry)
    entry["axiomFootprint"] = ["sorryAx"]
    for query in registry["queries"]:
        evidence = query.get("outcome", {}).get("evidence", {})
        if evidence.get("certificateId") == entry["certificateId"]:
            evidence["axiomFootprint"] = ["sorryAx"]
            break


def mutate_wrong_evidence_class(registry, dispositions):
    first_certificate(registry)["evidenceClass"] = "deliveredModule"


def mutate_partial_acceptance_flip(registry, dispositions):
    registry["acceptance"] = "accepted-R8"


def mutate_self_hash_cycle(registry, dispositions):
    registry["description"] = sha(REGISTRY)


def mutate_legacy_anchor_counts(registry, dispositions):
    dispositions["entries"][0]["countsTowardActiveCoverage"] = True


def mutate_probe_declaration_missing(registry, dispositions):
    registry["probeFiles"][0]["certificateDeclarations"].pop()


MUTATIONS = [
    ("missing_pair", mutate_missing_pair, "pairs.count"),
    ("duplicate_pair", mutate_duplicate_pair, "pairs.unique"),
    ("pair_anchor_substitution", mutate_pair_anchor_substitution, "pairs.query_ids"),
    ("wrong_outcome", mutate_wrong_outcome, "records.status"),
    ("certified_without_evidence", mutate_certified_without_evidence,
     "queries.certified_evidence"),
    ("candidate_promoted", mutate_candidate_promoted, "certificates.probe_count"),
    ("unknown_alias_endpoint", mutate_unknown_alias_endpoint, "queries.alias_endpoint"),
    ("unrepaired_legacy_record", mutate_unrepaired_legacy_record,
     "dispositions.corrected_missing"),
    ("missing_legacy_disposition", mutate_missing_legacy_disposition,
     "dispositions.count"),
    ("absence_reconciliation_removed", mutate_absence_reconciliation_removed,
     "dispositions.absence_missing"),
    ("stale_probe_hash", mutate_stale_probe_hash, "probes.file_hash"),
    ("forbidden_axiom_footprint", mutate_forbidden_axiom_footprint,
     "certificates.probe_axioms"),
    ("wrong_evidence_class", mutate_wrong_evidence_class,
     "certificates.probe_class"),
    ("partial_acceptance_flip", mutate_partial_acceptance_flip,
     "state.acceptance_uniform"),
    ("self_hash_cycle", mutate_self_hash_cycle, "hash.self_reference"),
    ("legacy_anchor_counts", mutate_legacy_anchor_counts,
     "dispositions.active_coverage"),
    ("probe_declaration_missing", mutate_probe_declaration_missing,
     "probes.certificate_declarations"),
]


def main() -> int:
    base_registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    base_dispositions = json.loads(DISPOSITIONS.read_text(encoding="utf-8"))
    # The mutation baseline is always the pending state, so the suite gives the
    # same result when the checkout under test is pending or accepted.  The
    # accepted state is exercised separately by the rebuild-enabled controls.
    base_registry["acceptance"] = "submitted-R8-pending-review"
    base_dispositions["acceptance"] = "submitted-R8-pending-review"
    failures: list[str] = []
    positives = 0

    with tempfile.TemporaryDirectory(prefix="r8-adversarial-") as tmp:
        tmpdir = Path(tmp)

        # Positive control 1: unmutated pending snapshot.
        reg_path = tmpdir / "pending-registry.json"
        dis_path = tmpdir / "pending-dispositions.json"
        reg_path.write_text(json.dumps(base_registry), encoding="utf-8")
        dis_path.write_text(json.dumps(base_dispositions), encoding="utf-8")
        proc = run_validator(reg_path, dis_path)
        if proc.returncode != 0:
            failures.append(f"pending control unexpectedly failed: {proc.stdout[-2000:]}")
        else:
            positives += 1

        # Positive control 2: uniform accepted snapshot.
        accepted_registry = copy.deepcopy(base_registry)
        accepted_dispositions = copy.deepcopy(base_dispositions)
        accepted_registry["acceptance"] = "accepted-R8"
        accepted_dispositions["acceptance"] = "accepted-R8"
        reg_path.write_text(json.dumps(accepted_registry), encoding="utf-8")
        dis_path.write_text(json.dumps(accepted_dispositions), encoding="utf-8")
        proc = run_validator(reg_path, dis_path)
        if proc.returncode != 0:
            failures.append(f"accepted control unexpectedly failed: {proc.stdout[-2000:]}")
        else:
            positives += 1

        for name, mutate, expected_code in MUTATIONS:
            registry = copy.deepcopy(base_registry)
            dispositions = copy.deepcopy(base_dispositions)
            mutate(registry, dispositions)
            reg_path = tmpdir / f"{name}-registry.json"
            dis_path = tmpdir / f"{name}-dispositions.json"
            reg_path.write_text(json.dumps(registry), encoding="utf-8")
            dis_path.write_text(json.dumps(dispositions), encoding="utf-8")
            proc = run_validator(reg_path, dis_path)
            output = proc.stdout + "\n" + proc.stderr
            if proc.returncode == 0:
                failures.append(f"{name}: mutation was accepted (exit 0)")
            elif expected_code not in output:
                failures.append(
                    f"{name}: rejected but expected code {expected_code!r} was absent; "
                    f"tail={output[-1200:]!r}")
            else:
                print(f"PASS {name}: fail-closed with {expected_code}")

        # Positive control 3: deterministic isolated rebuild.
        command = [
            sys.executable, str(VALIDATOR), "--root", str(ROOT),
            "--schema", str(SCHEMA),
            "--skip-external", "--skip-probe-compile", "--skip-original",
            "--quiet",
        ]
        proc = subprocess.run(command, cwd=str(ROOT), capture_output=True, text=True,
                              timeout=900)
        if proc.returncode != 0:
            failures.append(f"deterministic rebuild control failed: {proc.stdout[-2000:]}")
        else:
            positives += 1

        # Positive control 4: a complete accepted-R8 artifact set with rebuild
        # enabled.  This is the state machine that previously failed because
        # the builder hardcoded the pending state.
        try:
            accepted_root = prepare_isolated_root(tmpdir / "accepted", "accepted-R8")
            generated_registry = json.loads(
                (accepted_root / "relation_audit/registry.accepted.json")
                .read_text(encoding="utf-8"))
            generated_dispositions = json.loads(
                (accepted_root / "relation_audit/legacy-dispositions.accepted.json")
                .read_text(encoding="utf-8"))
            generated_docs = (accepted_root / "docs/RELATION-AUDIT-ACCEPTED.md").read_text(
                encoding="utf-8")
            if generated_registry["acceptance"] != "accepted-R8":
                failures.append("accepted builder control: registry acceptance is not accepted-R8")
            elif generated_dispositions["acceptance"] != "accepted-R8":
                failures.append("accepted builder control: dispositions acceptance is not accepted-R8")
            elif "`accepted-R8`" not in generated_docs:
                failures.append("accepted builder control: generated docs do not state accepted-R8")
            else:
                proc = run_rebuild_validator(accepted_root)
                if proc.returncode != 0:
                    failures.append(
                        "accepted+rebuild control failed: "
                        f"{proc.stdout[-3000:]}\n{proc.stderr[-1000:]}")
                else:
                    positives += 1
        except Exception as exc:
            failures.append(f"accepted+rebuild control error: {type(exc).__name__}: {exc}")

        # Positive control 5: the same uniform accepted state, but fed through
        # custom --registry/--dispositions paths with rebuild enabled.  The
        # rebuild must follow the current manifest's acceptance and compare
        # the custom artifacts, not only the checkout defaults.
        try:
            custom_reg = tmpdir / "custom-accepted-registry.json"
            custom_dis = tmpdir / "custom-accepted-dispositions.json"
            shutil.copy2(accepted_root / "relation_audit/registry.accepted.json", custom_reg)
            shutil.copy2(accepted_root / "relation_audit/legacy-dispositions.accepted.json",
                         custom_dis)
            proc = run_rebuild_validator(accepted_root, custom_reg, custom_dis)
            if proc.returncode != 0:
                failures.append(
                    "accepted custom-path+rebuild control failed: "
                    f"{proc.stdout[-3000:]}\n{proc.stderr[-1000:]}")
            else:
                positives += 1
        except Exception as exc:
            failures.append(f"accepted custom-path+rebuild control error: "
                            f"{type(exc).__name__}: {exc}")

        # Invalid acceptance states must be rejected before any write.  This
        # runs from a scratch copy of the builder so a parsing bug cannot touch
        # the checkout, and an unexpected path falls through to a failed load.
        try:
            scratch = tmpdir / "invalid-acceptance"
            (scratch / "tools/relation_audit_bounded").mkdir(parents=True)
            shutil.copy2(BUILD, scratch / "tools/relation_audit_bounded/build.py")
            proc = subprocess.run(
                [sys.executable, "tools/relation_audit_bounded/build.py",
                 "--acceptance", "bogus-state"],
                cwd=str(scratch), capture_output=True, text=True, timeout=120)
            if proc.returncode == 0:
                failures.append("invalid acceptance control: builder accepted an invalid state")
        except Exception as exc:
            failures.append(f"invalid acceptance control error: {type(exc).__name__}: {exc}")

    print()
    if failures:
        for failure in failures:
            print(f"FAIL {failure}")
        print(f"{len(failures)} failure(s); "
              f"{len(MUTATIONS) - len(failures)}/{len(MUTATIONS)} mutations rejected")
        return 1
    print(f"All {len(MUTATIONS)} mutations failed closed; "
          f"{positives} positive controls passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
