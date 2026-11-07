"""End-to-end tests for the valid pilot and full-registry fixtures."""

from __future__ import annotations

import hashlib
import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from harness import (  # noqa: E402
    FULL, PILOT, REPO_ROOT, SCHEMA, load_json, mock_lean_root,
    report_from, run_cli, write_mutant,
)


class ValidFixtureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lean_root, reason = mock_lean_root()
        if not cls.lean_root:
            raise unittest.SkipTest(reason)

    def test_pilot_passes_with_all_gates(self):
        handle = tempfile.NamedTemporaryFile(suffix=".json", delete=False)
        handle.close()
        try:
            completed = run_cli(PILOT, mode="pilot", lean_root=self.lean_root,
                                json_out=handle.name)
            report = report_from(handle.name)
        finally:
            os.unlink(handle.name)
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(report["exitCode"], 0)
        self.assertEqual(report["coverage"]["theoryCount"], 17)
        self.assertEqual(report["coverage"]["expectedPairUniverse"], 136)
        self.assertGreaterEqual(report["coverage"]["coveredPairs"], 9)
        self.assertEqual(report["counts"]["byStatus"], {
            "certified": 7, "unresolved": 1, "notEstablished": 1, "outOfScope": 1})
        self.assertEqual(report["counts"]["certifiedByKind"], {
            "definitionalIdentity": 1, "implication": 1, "equivalence": 1,
            "conditionalComposition": 1, "observationalEquivalence": 1,
            "distinguishability": 1, "refutation": 1})
        for gate in ("structure", "references", "semantics", "provenance",
                     "snapshot", "coverage", "lean"):
            self.assertEqual(report["gates"][gate]["status"], "PASS", gate)
        self.assertEqual(report["metadata"]["lean"]["status"], "PASS")
        self.assertGreater(report["metadata"]["lean"]["checks"], 0)
        self.assertEqual(len(report["unresolved"]), 1)

    def test_mode_defaults_to_the_manifest_field(self):
        completed = run_cli(PILOT, mode=None, lean_root=self.lean_root)
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        self.assertIn("(pilot mode)", completed.stdout)

    def test_full_registry_fixture_covers_136_pairs(self):
        completed = run_cli(FULL, mode="full")
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        self.assertIn("registry          136/136 pairs", completed.stdout)
        self.assertIn("overall: PASS", completed.stdout)

    def test_full_registry_report_does_not_claim_resolved_coverage(self):
        handle = tempfile.NamedTemporaryFile(suffix=".json", delete=False)
        handle.close()
        try:
            completed = run_cli(FULL, mode="full", json_out=handle.name)
            report = report_from(handle.name)
        finally:
            os.unlink(handle.name)
        self.assertEqual(completed.returncode, 0)
        self.assertEqual(report["coverage"]["coveredPairs"], 136)
        self.assertEqual(report["coverage"]["missingPairs"], [])
        self.assertEqual(report["coverage"]["resolvedPairs"], 0)
        self.assertFalse(report["coverage"]["resolvedCoverageComplete"])
        self.assertEqual(report["coverage"]["unresolvedRecords"], 136)
        self.assertEqual(len(report["unresolved"]), 136)

    def test_no_lean_is_incomplete_not_pass(self):
        completed = run_cli(PILOT, mode="pilot", no_lean=True)
        self.assertEqual(completed.returncode, 2, completed.stdout + completed.stderr)
        self.assertIn("lean.notRequested", completed.stdout)
        self.assertIn("overall: INCOMPLETE", completed.stdout)

    def test_missing_schema_exits_2(self):
        completed = run_cli(PILOT, mode="pilot",
                            schema=os.path.join(REPO_ROOT, "does", "not", "exist.json"))
        self.assertEqual(completed.returncode, 2)
        self.assertIn("ERROR:", completed.stderr)

    def test_missing_manifest_exits_2(self):
        completed = run_cli(os.path.join(REPO_ROOT, "missing-manifest.json"),
                            mode="pilot")
        self.assertEqual(completed.returncode, 2)
        self.assertIn("ERROR:", completed.stderr)

    def test_fixture_pilot_passes_against_the_production_schema(self):
        production = os.path.join(REPO_ROOT, "relation_audit", "schema.json")
        if not os.path.isfile(production):
            self.skipTest("production relation_audit/schema.json not present")
        # Contract section 4 allows an empty bridge list, so the pilot fixture
        # carries `bridges: []`.  The lead-owned production schema still
        # requires at least one bridge at the time of this change; that schema
        # file is outside this worker's write scope.  Once it is updated this
        # test exercises the full production-schema path again instead of
        # skipping.
        with open(production, encoding="utf-8") as handle:
            production_schema = json.load(handle)
        bridge = (production_schema.get("$defs", {})
                  .get("composition", {})
                  .get("properties", {})
                  .get("bridges", {}))
        if isinstance(bridge, dict) and bridge.get("minItems", 0) >= 1:
            self.skipTest(
                "relation_audit/schema.json still requires a non-empty "
                "composition.bridges list, but docs/RELATION-AUDIT-CONTRACT.md "
                "section 4 permits an empty list; the lead-owned schema update "
                "is pending")
        with open(production, "rb") as handle:
            schema_hash = hashlib.sha256(handle.read()).hexdigest()
        data = load_json(PILOT)
        data["snapshots"][0]["schemaSha256"] = schema_hash
        mutant = write_mutant(data)
        handle = tempfile.NamedTemporaryFile(suffix=".json", delete=False)
        handle.close()
        try:
            completed = run_cli(mutant, mode="pilot", schema=production,
                                lean_root=self.lean_root, json_out=handle.name)
            report = report_from(handle.name)
        finally:
            os.unlink(mutant)
            os.unlink(handle.name)
        self.assertEqual(completed.returncode, 0,
                         completed.stdout + completed.stderr)
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(report["gates"]["lean"]["status"], "PASS")

    def test_full_registry_passes_against_the_production_schema(self):
        production = os.path.join(REPO_ROOT, "relation_audit", "schema.json")
        if not os.path.isfile(production):
            self.skipTest("production relation_audit/schema.json not present")
        with open(production, "rb") as handle:
            schema_hash = hashlib.sha256(handle.read()).hexdigest()
        data = load_json(FULL)
        data["snapshots"][0]["schemaSha256"] = schema_hash
        mutant = write_mutant(data)
        try:
            completed = run_cli(mutant, mode="full", schema=production)
        finally:
            os.unlink(mutant)
        self.assertEqual(completed.returncode, 0,
                         completed.stdout + completed.stderr)
        self.assertIn("136/136", completed.stdout)

    def test_report_json_is_stable_and_complete(self):
        handle = tempfile.NamedTemporaryFile(suffix=".json", delete=False)
        handle.close()
        try:
            run_cli(PILOT, mode="pilot", lean_root=self.lean_root, json_out=handle.name)
            with open(handle.name, encoding="utf-8") as stream:
                first = stream.read()
            run_cli(PILOT, mode="pilot", lean_root=self.lean_root, json_out=handle.name)
            with open(handle.name, encoding="utf-8") as stream:
                second = stream.read()
        finally:
            os.unlink(handle.name)
        self.assertEqual(first, second)
        report = json.loads(first)
        for key in ("status", "exitCode", "coverage", "counts", "unresolved",
                    "gates", "failureCount", "skipCount", "metadata"):
            self.assertIn(key, report)


class FixtureIntegrityTests(unittest.TestCase):
    def test_invalid_fixtures_exist_for_every_named_mutation(self):
        expected = {
            "mislabelled_kind.json",
            "mislabelled_kind_lean.json",
            "composition_wrong_parent_order.json",
            "composition_parent_premise_drift.json",
            "composition_wrong_mediator.json",
            "missing_premise.json",
            "incomplete_bridge.json",
            "bridge_unrelated_witness.json",
            "discharge_unrelated_witness.json",
            "badge_nonvacuous_unrelated.json",
            "badge_nonredundant_unrelated.json",
            "badge_weakest_unrelated.json",
            "stale_snapshot.json",
            "conflicting_statuses.json",
            "missing_pair.json",
            "missing_provenance.json",
        }
        from harness import INVALID_DIR
        present = set(os.listdir(INVALID_DIR))
        self.assertTrue(expected <= present, expected - present)

    def test_obsolete_conflict_kinds_and_missing_bridge_fixtures_are_gone(self):
        # R4 removed kind-level conflict detection and section 4 allows empty
        # bridges, so these fixtures must not quietly reappear as expectations.
        from harness import INVALID_DIR
        present = set(os.listdir(INVALID_DIR))
        self.assertNotIn("conflicting_kinds.json", present)
        self.assertNotIn("missing_bridge.json", present)

    def test_pilot_composition_uses_an_empty_bridge_list(self):
        pilot = load_json(PILOT)
        comp = next(r for r in pilot["records"] if r["id"] == "rec-comp")
        self.assertEqual(comp["composition"]["bridges"], [])
        self.assertEqual([item["id"] for item in comp["premises"]],
                         ["p-adj", "p-pos"])
        self.assertEqual(comp["badges"], {})

    def test_pilot_fixture_declares_all_seven_kinds(self):
        pilot = load_json(PILOT)
        kinds = {r.get("relationKind") for r in pilot["records"]
                 if r["status"] == "certified"}
        self.assertEqual(kinds, {
            "definitionalIdentity", "implication", "equivalence",
            "conditionalComposition", "observationalEquivalence",
            "distinguishability", "refutation"})

    def test_full_fixture_has_136_records_and_unique_query_versions(self):
        full = load_json(FULL)
        self.assertEqual(len(full["records"]), 136)
        self.assertEqual(len(full["queries"]), 136)
        triples = {(r["queryId"], r["statementVersion"], r["scope"])
                   for r in full["records"]}
        self.assertEqual(len(triples), 136)

    def test_fixture_schema_is_not_the_production_schema(self):
        # The fixture schema must not silently shadow or rewrite the contract
        # schema the lead owns.
        production = os.path.join(REPO_ROOT, "relation_audit", "schema.json")
        self.assertNotEqual(os.path.realpath(SCHEMA), os.path.realpath(production))


if __name__ == "__main__":
    unittest.main()
