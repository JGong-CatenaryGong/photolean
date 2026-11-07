"""Tests for the R4 production full-registry generator and checker.

The production registry must be derived from the accepted R1/R2/R3 inputs, not
from a hand-maintained certificate list.  These tests exercise the derivation,
the status/coverage invariants, and the drift/mutation controls that make a
stale or edited registry fail closed.
"""

from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), "tools"))

from harness import REPO_ROOT  # noqa: E402
from relation_audit import registry  # noqa: E402


TOOL = os.path.join(REPO_ROOT, "tools", "relation_audit_registry.py")

BASE_INPUTS = registry.load_inputs(REPO_ROOT)
BASE_MANIFEST, BASE_REPORT = registry.build_registry(copy.deepcopy(BASE_INPUTS))


def build(inputs=None):
    return registry.build_registry(copy.deepcopy(inputs or BASE_INPUTS))


def findings_for(inputs=None):
    try:
        build(inputs)
    except registry.RegistryError as exc:
        return {finding.code for finding in exc.findings}
    except Exception as exc:  # pragma: no cover - a crash is a test failure, not a pass
        raise AssertionError(f"unexpected generator exception: {exc!r}") from exc
    return set()


def record_status(manifest, record_id):
    for record in manifest["records"]:
        if record["id"] == record_id:
            return record["status"]
    raise AssertionError(f"record {record_id!r} not found")


class RegistryBuildTests(unittest.TestCase):
    def test_accepted_inputs_are_clean(self):
        self.assertEqual(registry.validate_accepted_inputs(copy.deepcopy(BASE_INPUTS)), [])

    def test_generation_is_deterministic(self):
        first, first_report = build()
        second, second_report = build()
        self.assertEqual(registry.canonical_json(first), registry.canonical_json(second))
        self.assertEqual(registry.canonical_json(first_report),
                         registry.canonical_json(second_report))

    def test_all_136_pairs_are_covered(self):
        coverage = BASE_REPORT["coverage"]
        self.assertEqual(coverage["coveredPairs"], 136)
        self.assertEqual(coverage["missingPairs"], [])
        self.assertEqual(len(BASE_MANIFEST["records"]) >= 136, True)

    def test_resolved_coverage_is_nine_pairs_not_complete(self):
        coverage = BASE_REPORT["coverage"]
        self.assertEqual(coverage["resolvedPairs"], 9)
        self.assertFalse(coverage["resolvedCoverageComplete"])
        self.assertEqual(coverage["unresolvedRecords"], 6)

    def test_status_and_kind_counts(self):
        counts = BASE_REPORT["counts"]
        self.assertEqual(counts["records"], 151)
        self.assertEqual(counts["byStatus"]["certified"], 24)
        self.assertEqual(counts["byStatus"]["unresolved"], 6)
        self.assertEqual(counts["byStatus"]["notEstablished"], 121)
        self.assertEqual(counts["byStatus"]["outOfScope"], 0)
        self.assertEqual(counts["certifiedByKind"], {
            "conditionalComposition": 1,
            "definitionalIdentity": 7,
            "distinguishability": 2,
            "equivalence": 8,
            "implication": 2,
            "observationalEquivalence": 3,
            "refutation": 1,
        })

    def test_every_accepted_certificate_is_registered(self):
        accepted = {item["lean"] for item in BASE_INPUTS["pilot"]["certificates"]}
        for fragment in BASE_INPUTS["fragments"]:
            accepted |= {
                item["certificate"] for item in fragment["entries"]
                if item.get("outcome") == "certified"
            }
        registered = {item["lean"] for item in BASE_MANIFEST["certificates"]}
        self.assertEqual(registered, accepted)
        self.assertEqual(len(accepted), 38)

    def test_certificate_mapping_is_one_to_one(self):
        mapping = BASE_REPORT["certificateMapping"]
        self.assertEqual(len(mapping), 38)
        self.assertEqual(len({item["registryCertificate"] for item in mapping}), 38)
        for item in mapping:
            if item["outcome"] == "pair-record":
                self.assertTrue(item["recordIds"])
                self.assertTrue(item["pairIds"])
            elif item["outcome"] in ("non-pair-evidence", "composition-parent"):
                self.assertFalse(item["recordIds"])
            else:
                self.assertEqual(item["outcome"], "intra-theory-record")
                self.assertTrue(item["recordIds"])
                self.assertEqual(item["pairIds"], [])

    def test_kernel_only_pins_do_not_manufacture_pair_records(self):
        cert_by_id = {item["id"]: item for item in BASE_MANIFEST["certificates"]}
        cert_by_lean = {item["lean"]: item for item in BASE_MANIFEST["certificates"]}
        for item in BASE_REPORT["certificateMapping"]:
            if item["outcome"] != "pair-record":
                continue
            cert = cert_by_id.get(item["certificate"]) or cert_by_lean[item["certificate"]]
            pair_ids = [pair["pairId"] for pair in BASE_INPUTS["pair_inventory"]["pairs"]
                        if pair["pairId"] in item["pairIds"]]
            self.assertEqual(len(pair_ids), 1)
            pair = pair_ids[0]
            pair_theories = next(
                pair_item["theories"] for pair_item in BASE_INPUTS["pair_inventory"]["pairs"]
                if pair_item["pairId"] == pair
            )
            statement_map = {s["id"]: s for s in BASE_MANIFEST["statements"]}
            query_map = {q["id"]: q for q in BASE_MANIFEST["queries"]}
            for record_id in item["recordIds"]:
                record = next(r for r in BASE_MANIFEST["records"] if r["id"] == record_id)
                query = query_map[record["queryId"]]
                endpoints = {
                    statement_map[query["source"]]["theory"],
                    statement_map[query["target"]]["theory"],
                }
                self.assertEqual(endpoints, set(pair_theories))
        # The concrete R3 kernel pin whose declared pair does not match its endpoints.
        mapping = {item["declarationId"]: item for item in BASE_REPORT["certificateMapping"]}
        kernel_pin = mapping["D-S07-kernel_marcusIC"]
        self.assertEqual(kernel_pin["outcome"], "non-pair-evidence")
        self.assertEqual(kernel_pin["recordIds"], [])
        self.assertIn("do not match the declared pair", kernel_pin["reason"])

    def test_six_candidates_remain_unresolved(self):
        candidates = {
            pair["pairId"] for pair in BASE_INPUTS["pair_inventory"]["pairs"]
            if pair.get("candidate")
        }
        self.assertEqual(len(candidates), 6)
        for pair_id in candidates:
            decision = next(item for item in BASE_REPORT["pairDecisions"]
                            if item["pairId"] == pair_id)
            self.assertEqual(decision["status"], "unresolved")
            for record_id in decision["recordIds"]:
                record = next(item for item in BASE_MANIFEST["records"]
                              if item["id"] == record_id)
                self.assertEqual(record["status"], "unresolved")
                self.assertNotIn("dependencies", record)
                self.assertIn(record["candidate"], registry.CERTIFIED_KINDS)

    def test_not_established_records_are_conservative(self):
        for record in BASE_MANIFEST["records"]:
            if record["status"] != "notEstablished":
                continue
            self.assertTrue(any(
                phrase in record["rationale"]
                for phrase in registry.CONSERVATIVE_ABSENCE_PHRASES
            ))
            self.assertTrue(record["dependencies"])
            for dependency in record["dependencies"]:
                self.assertIn(dependency["kind"], ("sourceScan", "census", "search"))
                self.assertTrue(dependency["recompute"])
                self.assertTrue(dependency["reference"])
            self.assertIn("rationale", record["provenance"])

    def test_reused_pilot_absence_is_not_duplicated(self):
        decisions = [item for item in BASE_REPORT["pairDecisions"]
                     if item["pairId"] == "P-Marcus-Goldschmidt"]
        self.assertEqual(len(decisions), 1)
        self.assertEqual(decisions[0]["status"], "notEstablished")
        self.assertEqual(decisions[0]["recordIds"], ["rec-goldschmidt-marcus-noedge"])

    def test_multiple_relations_are_preserved(self):
        pair_records = {}
        statement_map = {s["id"]: s for s in BASE_MANIFEST["statements"]}
        query_map = {q["id"]: q for q in BASE_MANIFEST["queries"]}
        for record in BASE_MANIFEST["records"]:
            if record["status"] != "certified":
                continue
            query = query_map[record["queryId"]]
            left = statement_map[query["source"]]["theory"]
            right = statement_map[query["target"]]["theory"]
            if left == right:
                continue
            pair_records.setdefault(frozenset((left, right)), []).append(record)
        self.assertGreaterEqual(len(pair_records[frozenset(("Marcus", "Hammond"))]), 5)
        self.assertGreaterEqual(len(pair_records[frozenset(("Marcus", "BEP"))]), 3)
        self.assertGreaterEqual(len(pair_records[frozenset(("Hammond", "BEP"))]), 4)
        kinds = {record["relationKind"]
                 for record in pair_records[frozenset(("Marcus", "BEP"))]}
        self.assertIn("conditionalComposition", kinds)
        self.assertIn("definitionalIdentity", kinds)

    def test_conflict_keys_have_one_status(self):
        groups = {}
        for record in BASE_MANIFEST["records"]:
            key = (record["queryId"], record["statementVersion"], record["scope"])
            groups.setdefault(key, set()).add(record["status"])
        self.assertTrue(all(len(statuses) == 1 for statuses in groups.values()))
        # The accepted pilot keeps three distinct Stern-Volmer certified
        # relations at the same statement version and scope; the conflict key
        # also includes the query id, so they remain three independent groups.
        sv = [record for record in BASE_MANIFEST["records"]
              if record["queryId"] in ("q-sv-intensity", "q-sv-joint", "q-sv-decoder")]
        self.assertEqual(len(sv), 3)
        self.assertTrue(all(record["status"] == "certified" for record in sv))

    def test_legacy_labels_are_not_promoted(self):
        for decision in BASE_REPORT["pairDecisions"]:
            if decision["legacyLabel"] == "edge" and decision["status"] == "certified":
                # Only accept a legacy edge becoming certified when an accepted
                # certificate actually maps to the pair.
                self.assertTrue(decision["certifiedRecordIds"])
            if decision["legacyLabel"] == "absence":
                self.assertNotEqual(decision["status"], "certified")

    def test_exceptional_decisions_are_recorded(self):
        kinds = {item["kind"] for item in BASE_REPORT["exceptionalDecisions"]}
        self.assertIn("census-ambiguity", kinds)
        self.assertIn("non-pair-certificate", kinds)
        self.assertIn("undelivered-candidate", kinds)
        self.assertIn("reclassified-non-certificate", kinds)
        self.assertIn("reused-pilot-absence", kinds)


class RegistryCheckTests(unittest.TestCase):
    def test_check_accepts_generated_registry(self):
        findings = registry.check_registry(
            copy.deepcopy(BASE_INPUTS), BASE_MANIFEST, BASE_REPORT)
        self.assertEqual(findings, [])

    def test_check_detects_hand_added_certificate(self):
        manifest = copy.deepcopy(BASE_MANIFEST)
        manifest["certificates"].append({
            "id": "cert-hand-added",
            "kind": "implication",
            "module": "PhotoLean.RelationAudit.Pilot",
            "lean": "PhotoLean.RelationAudit.handAdded",
            "kindFunction": "PhotoLean.RelationAudit.certificateKind",
            "constructor": "PhotoLean.RelationAudit.RelationKind.implication",
            "premises": [],
            "semantics": {
                "context": "x",
                "translations": {"left": "id", "right": "id"},
                "premisePredicate": "fun _ => True",
            },
            "axiomFootprint": [],
        })
        codes = {finding.code for finding in registry.check_registry(
            copy.deepcopy(BASE_INPUTS), manifest, BASE_REPORT)}
        self.assertIn("registry.drift", codes)

    def test_check_detects_status_mutation(self):
        manifest = copy.deepcopy(BASE_MANIFEST)
        target = next(record for record in manifest["records"]
                      if record["id"] == "rec-notestablished-P-Marcus-RACI")
        target["status"] = "certified"
        codes = {finding.code for finding in registry.check_registry(
            copy.deepcopy(BASE_INPUTS), manifest, BASE_REPORT)}
        self.assertIn("registry.drift", codes)

    def test_check_detects_input_hash_drift(self):
        report = copy.deepcopy(BASE_REPORT)
        report["inputs"][registry.PILOT_PATH] = "0" * 64
        codes = {finding.code for finding in registry.check_registry(
            copy.deepcopy(BASE_INPUTS), BASE_MANIFEST, report)}
        self.assertIn("input.drift", codes)

    def test_check_detects_report_drift(self):
        report = copy.deepcopy(BASE_REPORT)
        report["counts"]["byStatus"]["unresolved"] = 0
        codes = {finding.code for finding in registry.check_registry(
            copy.deepcopy(BASE_INPUTS), BASE_MANIFEST, report)}
        self.assertIn("registry.reportDrift", codes)


class RegistryMutationTests(unittest.TestCase):
    def test_unknown_pair_association_fails(self):
        inputs = copy.deepcopy(BASE_INPUTS)
        entry = next(item for fragment in inputs["fragments"] for item in fragment["entries"]
                     if item["declarationId"] == "D-S02-tsCoord_lt_zero_iff_inverted")
        entry["pairIds"] = ["P-No-Such-Pair"]
        self.assertIn("registry.pairUnknown", findings_for(inputs))

    def test_multiple_pair_associations_fail(self):
        inputs = copy.deepcopy(BASE_INPUTS)
        entry = next(item for fragment in inputs["fragments"] for item in fragment["entries"]
                     if item["declarationId"] == "D-S02-tsCoord_lt_zero_iff_inverted")
        entry["pairIds"] = ["P-Marcus-Hammond", "P-Marcus-BEP"]
        self.assertIn("registry.pairAssociation", findings_for(inputs))

    def test_removing_a_queue_row_fails(self):
        inputs = copy.deepcopy(BASE_INPUTS)
        inputs["fragments"][0]["entries"] = [
            item for item in inputs["fragments"][0]["entries"]
            if item["declarationId"] != "D-S01-kernel_barrier_eq_hammond"
        ]
        self.assertIn("fragment.queue", findings_for(inputs))

    def test_duplicate_fragment_certificate_fails(self):
        inputs = copy.deepcopy(BASE_INPUTS)
        entries = [item for fragment in inputs["fragments"] for item in fragment["entries"]]
        first = next(item for item in entries if item.get("outcome") == "certified")
        second = next(item for item in entries
                      if item.get("outcome") == "certified" and item is not first)
        second["certificate"] = first["certificate"]
        self.assertIn("fragment.certificateDuplicate", findings_for(inputs))

    def test_stale_statement_hash_fails(self):
        inputs = copy.deepcopy(BASE_INPUTS)
        inputs["pilot"]["statements"][0]["sha256"] = "0" * 64
        self.assertIn("pilot.statementHash", findings_for(inputs))

    def test_stale_snapshot_hash_fails(self):
        inputs = copy.deepcopy(BASE_INPUTS)
        snapshot = inputs["pilot"]["snapshots"][0]
        key = next(iter(snapshot["artifacts"]))
        snapshot["artifacts"][key] = "0" * 64
        self.assertIn("pilot.snapshotHash", findings_for(inputs))

    def test_not_established_lean_probe_is_rejected(self):
        inputs = copy.deepcopy(BASE_INPUTS)
        # Build once, inject a Lean-probe dependency into a generated absence
        # record, and re-run the post-build conservative check by rebuilding a
        # registry whose notEstablished record is hand-mutated.
        manifest, _report = build(inputs)
        target = next(record for record in manifest["records"]
                      if record["id"] == "rec-notestablished-P-Marcus-RACI")
        target["dependencies"] = [{
            "kind": "leanProbe",
            "reference": "PhotoLean.RelationAudit.someTheorem",
            "recompute": "lake env lean #check PhotoLean.RelationAudit.someTheorem",
        }]
        with self.assertRaises(registry.RegistryError) as ctx:
            registry._assert_conservative_absence(target)
        self.assertIn("registry.dependencyKind",
                      {finding.code for finding in ctx.exception.findings})

class RegistryCliTests(unittest.TestCase):
    def test_cli_check_passes(self):
        completed = subprocess.run(
            [sys.executable, TOOL, "--check", "--quiet"],
            cwd=REPO_ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=120,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(completed.stdout.strip(), "")

    def test_cli_explain_pair_passes(self):
        completed = subprocess.run(
            [sys.executable, TOOL, "--explain-pair", "P-Marcus-Hammond"],
            cwd=REPO_ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=120,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("pair: P-Marcus-Hammond", completed.stdout)
        self.assertIn("registry records:", completed.stdout)

    def test_cli_explain_unknown_pair_fails(self):
        completed = subprocess.run(
            [sys.executable, TOOL, "--explain-pair", "P-No-Such-Pair"],
            cwd=REPO_ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=120,
        )
        self.assertEqual(completed.returncode, 1)
        self.assertIn("unknown pair", completed.stderr)

    def test_cli_render_validator_report(self):
        source = os.path.join(REPO_ROOT, "relation_audit", "reports",
                              "production-full.json")
        if not os.path.isfile(source):
            self.skipTest("production full report has not been generated yet")
        with open(source, encoding="utf-8") as handle:
            data = json.load(handle)
        rendered = registry.render_validator_report(data)
        self.assertIn("Production Full Validator Report", rendered)
        self.assertIn("registry: 136/136 pairs", rendered)


if __name__ == "__main__":
    unittest.main()
