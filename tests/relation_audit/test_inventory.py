"""Drift and mutation tests for the R2 migration inventory.

The inventory is single-source: every declaration and pair must come from
``tools/counts.py``.  These tests therefore mutate the scanner results, the
generated artifacts, and the disposition ledger, and assert that the checker
fails closed with a specific code.  They do not need the Lean toolchain.
"""

from __future__ import annotations

import contextlib
import copy
import io
import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), "tools"))

from harness import REPO_ROOT  # noqa: E402
from relation_audit import inventory, json_schema  # noqa: E402


AUDIT_STATUS_WORDS = {"certified", "unresolved", "notEstablished", "outOfScope"}
AUDIT_KINDS = {
    "definitionalIdentity", "implication", "equivalence", "conditionalComposition",
    "observationalEquivalence", "distinguishability", "refutation",
}


def codes(findings) -> set[str]:
    return {finding.code for finding in findings}


def load_ledger() -> dict:
    return inventory.load_json(os.path.join(REPO_ROOT, inventory.DISPOSITIONS))


class DeclarationInventoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.artifact = inventory.build_declaration_inventory(REPO_ROOT)

    def test_counts_match_the_round_contract(self):
        self.assertEqual(self.artifact["counts"]["declarations"], 78)
        self.assertEqual(self.artifact["counts"]["sections"], 17)
        self.assertEqual(self.artifact["counts"]["sectionsWithDeclarations"], 15)
        self.assertEqual(self.artifact["counts"]["documentationOnlySections"], [10, 16])
        self.assertEqual(len(self.artifact["declarations"]), 78)

    def test_every_declaration_has_a_stable_id_and_locator(self):
        ids = [row["declarationId"] for row in self.artifact["declarations"]]
        self.assertEqual(len(ids), len(set(ids)))
        for row in self.artifact["declarations"]:
            self.assertTrue(row["declarationId"].startswith("D-S"))
            self.assertNotIn(str(row["sourceLocator"]["line"]), row["declarationId"])
            self.assertEqual(row["sourceLocator"]["artifact"], "PhotoLean/Relations.lean")
            self.assertGreaterEqual(row["sourceLocator"]["line"], 1)
            self.assertTrue(row["sectionTitle"])

    def test_section_rows_reconcile_with_declarations(self):
        total = sum(section["declarationCount"] for section in self.artifact["sections"])
        self.assertEqual(total, 78)
        for section in self.artifact["sections"]:
            self.assertEqual(section["declarationCount"], len(section["declarationIds"]))
            if section["documentationOnly"]:
                self.assertEqual(section["declarationCount"], 0)

    def test_legacy_classes_are_namespaced(self):
        for row in self.artifact["declarations"]:
            self.assertIs(row["legacy"]["nonAuditMetadata"], True)
            self.assertNotIn(row["legacy"]["class"], AUDIT_STATUS_WORDS | AUDIT_KINDS)


class PairInventoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.artifact = inventory.build_pair_inventory(REPO_ROOT)

    def test_pair_universe_and_legacy_counts(self):
        counts = self.artifact["counts"]
        self.assertEqual(counts["pairs"], 136)
        self.assertEqual(counts["legacyEdges"], 26)
        self.assertEqual(counts["legacyUniqueAbsences"], 110)
        self.assertEqual(counts["legacyCoveredPairs"], 136)
        self.assertEqual(counts["legacyRawAbsenceRegistryRows"], 114)
        self.assertEqual(counts["unaccountedPairs"], 0)
        self.assertEqual(counts["bothEdgeAndAbsencePairs"], 0)
        self.assertEqual(len(self.artifact["pairs"]), 136)

    def test_pair_ids_and_theory_order_are_canonical(self):
        order = {theory: index for index, theory in enumerate(self.artifact["source"]["theories"])}
        self.assertEqual(len(order), 17)
        for row in self.artifact["pairs"]:
            first, second = row["theories"]
            self.assertLess(order[first], order[second])
            self.assertEqual(row["pairId"], f"P-{first}-{second}")

    def test_legacy_labels_are_not_audit_judgments(self):
        for row in self.artifact["pairs"]:
            self.assertIn(row["legacy"]["label"], {"edge", "absence"})
            self.assertIs(row["legacy"]["nonAuditMetadata"], True)
            self.assertIsNone(row["auditJudgment"])
            self.assertEqual(row["migration"]["status"], "not-audited")
            self.assertNotIn(row["legacy"]["label"], AUDIT_STATUS_WORDS | AUDIT_KINDS)
            self.assertNotIn(row["legacy"]["subtype"], AUDIT_STATUS_WORDS | AUDIT_KINDS)

    def test_undelivered_candidates_are_explicit(self):
        candidates = [row for row in self.artifact["pairs"] if row.get("candidate")]
        self.assertEqual(len(candidates), 6)
        for row in candidates:
            self.assertEqual(row["legacy"]["label"], "absence")
            self.assertEqual(row["legacy"]["subtype"], "undelivered-candidate")
            self.assertEqual(row["candidate"]["kind"], "unresolved-candidate")
            self.assertNotIn(row["candidate"]["kind"], AUDIT_STATUS_WORDS)

    def test_ambiguous_and_duplicate_registry_rows_are_reported(self):
        self.assertEqual(self.artifact["counts"]["ambiguousPairs"], 1)
        self.assertEqual(self.artifact["counts"]["duplicateRegistryRows"], 4)
        ambiguous = [row for row in self.artifact["pairs"] if row.get("ambiguous")]
        self.assertEqual(len(ambiguous), 1)
        self.assertEqual(ambiguous[0]["pairId"], "P-Marcus-RACI")
        duplicates = [row for row in self.artifact["pairs"] if row["legacy"]["duplicateRegistryRow"]]
        self.assertEqual(len(duplicates), 4)


class DispositionLedgerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.declarations = inventory.build_declaration_inventory(REPO_ROOT)
        cls.pairs = inventory.build_pair_inventory(REPO_ROOT)
        cls.ledger = load_ledger()
        cls.pilot = inventory.load_json(os.path.join(REPO_ROOT, inventory.PILOT))

    def findings(self, ledger):
        return inventory.validate_disposition_ledger(
            ledger, self.declarations, self.pairs, self.pilot, REPO_ROOT
        )

    def test_current_ledger_is_clean(self):
        self.assertEqual(self.findings(self.ledger), [])

    def test_schema_accepts_current_ledger(self):
        schema = json_schema.Schema.from_path(os.path.join(REPO_ROOT, inventory.DISPOSITIONS_SCHEMA))
        self.assertEqual(schema.validate(self.ledger), [])

    def test_every_declaration_is_covered_exactly_once(self):
        names = [entry["name"] for entry in self.ledger["entries"]]
        scanned = [row["name"] for row in self.declarations["declarations"]]
        self.assertEqual(len(names), 78)
        self.assertEqual(sorted(names), sorted(scanned))
        self.assertEqual(len(names), len(set(names)))

    def test_every_entry_has_rationale_action_and_provenance(self):
        for entry in self.ledger["entries"]:
            self.assertGreaterEqual(len(entry["rationale"].strip()), 40)
            self.assertGreaterEqual(len(entry["migrationAction"].strip()), 10)
            self.assertIs(entry["nonAuditMetadata"], True)
            self.assertIn(entry["provenance"]["kind"], {"source", "manual", "computed", "imported"})
            self.assertTrue(entry["provenance"]["references"])
            self.assertIn(entry["pairAssociation"], {"direct", "supporting", "look-alike", "intra-theory", "transitive", "none"})
            if entry["intraTheory"]:
                self.assertEqual(entry["pairAssociation"], "intra-theory")
            if entry["pairAssociation"] in {"direct", "look-alike", "transitive", "supporting"}:
                self.assertTrue(entry["pairIds"] or entry["relatedPairIds"])
            for ref in entry["provenance"]["references"]:
                self.assertTrue(ref["artifact"])
                self.assertTrue(ref["locator"])

    def test_exceptional_rows_are_distinguishable(self):
        by_name = {entry["name"]: entry for entry in self.ledger["entries"]}
        self.assertEqual(by_name["symmetryFactor_tsCoordZero_eq_kernel"]["relationRole"], "transitive-tie-back")
        self.assertEqual(by_name["kashaWithin_one_marcus"]["relationRole"], "conditional-equivalence")
        self.assertEqual(by_name["hammond_trend_exact_bep_law_inexact"]["disposition"], "look-alike-non-relation")
        self.assertIs(by_name["symmetryFactor_betaHalf_iff"]["intraTheory"], True)
        self.assertEqual(by_name["eg_boundary_eq_tsCoord_zero"]["disposition"], "scoped-relation-documentation")
        self.assertEqual(by_name["marcusIC_strictAnti_on_inverted_gaps"]["relationRole"], "composition-component")

    def test_missing_declaration_is_rejected(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["entries"] = ledger["entries"][:-1]
        self.assertIn("disposition.missing", codes(self.findings(ledger)))
        self.assertIn("disposition.count", codes(self.findings(ledger)))

    def test_duplicate_declaration_is_rejected(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["entries"].append(copy.deepcopy(ledger["entries"][0]))
        self.assertIn("disposition.duplicate", codes(self.findings(ledger)))

    def test_unknown_or_stale_declaration_is_rejected(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["entries"][0]["name"] = "not_a_relations_declaration"
        self.assertIn("disposition.unknown", codes(self.findings(ledger)))
        # The real declaration is now missing as well.
        self.assertIn("disposition.missing", codes(self.findings(ledger)))

    def test_section_and_id_drift_are_rejected(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["entries"][0]["section"] = 2
        ledger["entries"][1]["declarationId"] = "D-S99-wrong"
        found = codes(self.findings(ledger))
        self.assertIn("disposition.sectionMismatch", found)
        self.assertIn("disposition.idMismatch", found)

    def test_invalid_disposition_and_short_rationale_are_rejected(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["entries"][0]["disposition"] = "certified"
        ledger["entries"][1]["rationale"] = "too short"
        found = codes(self.findings(ledger))
        self.assertIn("disposition.schema", found)
        self.assertIn("disposition.rationale", found)

    def test_missing_provenance_is_rejected(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["entries"][0]["provenance"]["references"] = []
        self.assertIn("disposition.schema", codes(self.findings(ledger)))
        self.assertIn("disposition.provenance", codes(self.findings(ledger)))

    def test_unknown_pair_and_pilot_references_are_rejected(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["entries"][0]["pairIds"] = ["P-Nope-Nope"]
        ledger["entries"][0]["pilotRecordIds"] = ["rec-nope"]
        ledger["entries"][0]["pilotQueryIds"] = ["q-nope"]
        found = codes(self.findings(ledger))
        self.assertIn("disposition.pairUnknown", found)
        self.assertIn("disposition.pilotRecordUnknown", found)
        self.assertIn("disposition.pilotQueryUnknown", found)

    def test_pilot_certificate_needs_pilot_evidence(self):
        ledger = copy.deepcopy(self.ledger)
        entry = next(row for row in ledger["entries"] if row["disposition"] == "pilot-certificate")
        entry["pilotRecordIds"] = []
        entry["pilotQueryIds"] = []
        self.assertIn("disposition.pilotEvidence", codes(self.findings(ledger)))

    def test_intra_theory_entry_cannot_claim_a_pair(self):
        ledger = copy.deepcopy(self.ledger)
        entry = next(row for row in ledger["entries"] if row["intraTheory"])
        entry["pairIds"] = ["P-Marcus-BEP"]
        self.assertIn("disposition.intraTheoryPair", codes(self.findings(ledger)))

    def test_pair_association_must_match_the_reference(self):
        ledger = copy.deepcopy(self.ledger)
        direct = next(row for row in ledger["entries"] if row["pairAssociation"] == "direct")
        direct["pairAssociation"] = "none"
        found = codes(self.findings(ledger))
        self.assertIn("disposition.pairAssociationNone", found)
        ledger = copy.deepcopy(self.ledger)
        entry = next(row for row in ledger["entries"] if row["pairAssociation"] == "none")
        entry["pairAssociation"] = "direct"
        self.assertIn("disposition.pairAssociationEvidence", codes(self.findings(ledger)))


class DriftTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.declarations, cls.pairs, cls.ledger, cls.report, cls.pilot = inventory.build_all(REPO_ROOT)

    def test_check_mode_is_clean(self):
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(inventory.check(REPO_ROOT), 0)

    def test_generation_is_deterministic(self):
        first = inventory.build_all(REPO_ROOT)
        second = inventory.build_all(REPO_ROOT)
        for index in range(3):
            self.assertEqual(inventory.json_text(first[index]), inventory.json_text(second[index]))

    def test_any_production_registry_is_the_r4_generated_artifact(self):
        # R2 itself creates no registry.  R4 deliberately adds one, and when it
        # is present it must be the deterministic R4 generation with the
        # generation report; an unpaired or hand-written registry is not legal.
        registry_path = os.path.join(REPO_ROOT, "relation_audit", "registry.json")
        if not os.path.exists(registry_path):
            return
        report_path = os.path.join(
            REPO_ROOT, "relation_audit", "reports", "registry-report.json")
        self.assertTrue(os.path.exists(report_path))
        with open(report_path, encoding="utf-8") as handle:
            report = json.load(handle)
        self.assertEqual(report.get("artifactKind"), "relation-full-registry-generation")
        self.assertEqual(report["coverage"]["coveredPairs"], 136)
        self.assertIs(report["coverage"]["resolvedCoverageComplete"], False)

    def test_report_makes_no_registry_or_coverage_claim(self):
        self.assertEqual(self.report["status"], "INVENTORY_ONLY")
        self.assertIs(self.report["coverage"]["fullRegistryCreated"], False)
        self.assertIs(self.report["coverage"]["resolvedCoverageClaimed"], False)
        self.assertIs(self.report["coverage"]["fullRegistryPassClaimed"], False)
        self.assertEqual(self.report["counts"]["declarations"], 78)
        self.assertEqual(self.report["counts"]["pairs"], 136)
        self.assertEqual(self.report["counts"]["legacyEdges"], 26)
        self.assertEqual(self.report["counts"]["legacyUniqueAbsences"], 110)
        self.assertGreaterEqual(len(self.report["nonClaims"]), 6)
        self.assertEqual(self.report["counts"]["unresolvedCandidateDeclarations"], 0)
        self.assertEqual(len(self.report["undeliveredCandidates"]), 6)
        self.assertEqual(self.report["pairAssociationCounts"]["intra-theory"], 7)
        self.assertEqual(self.report["pairAssociationCounts"]["transitive"], 2)

    def test_declaration_count_drift_is_rejected(self):
        mutated = copy.deepcopy(self.declarations)
        mutated["counts"]["declarations"] = 77
        self.assertIn("inventory.count.declarations", codes(inventory.validate_declaration_inventory(mutated)))

    def test_section_count_drift_is_rejected(self):
        mutated = copy.deepcopy(self.declarations)
        mutated["counts"]["sections"] = 16
        self.assertIn("inventory.count.sections", codes(inventory.validate_declaration_inventory(mutated)))

    def test_pair_count_drift_is_rejected(self):
        mutated = copy.deepcopy(self.pairs)
        mutated["counts"]["legacyEdges"] = 25
        self.assertIn("inventory.count.legacyEdges", codes(inventory.validate_pair_inventory(mutated)))

    def test_stale_pair_annotation_is_rejected(self):
        key = frozenset(("Nope", "AlsoNope"))
        inventory.PAIR_ANNOTATIONS[key] = {"subtype": "shape", "note": "stale"}
        try:
            found = codes(inventory.validate_pair_inventory(self.pairs))
        finally:
            del inventory.PAIR_ANNOTATIONS[key]
        self.assertIn("inventory.annotationUnknown", found)

    def test_pair_audit_label_mutation_is_rejected(self):
        mutated = copy.deepcopy(self.pairs)
        mutated["pairs"][0]["legacy"]["label"] = "certified"
        found = codes(inventory.validate_pair_inventory(mutated))
        self.assertIn("inventory.pair.legacyLabel", found)

    def test_stale_checked_in_file_is_rejected(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            path = os.path.join(directory, inventory.GENERATED_DECLARATIONS)
            os.makedirs(os.path.dirname(path))
            with open(path, "w", encoding="utf-8") as handle:
                handle.write("{}\n")
            found = codes(inventory._compare_file(directory, inventory.GENERATED_DECLARATIONS, "{}\n"))
            self.assertEqual(found, set())
            stale = codes(inventory._compare_file(directory, inventory.GENERATED_DECLARATIONS, "different\n"))
            self.assertIn("drift.mismatch", stale)

    def test_missing_checked_in_file_is_rejected(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            found = codes(inventory._compare_file(directory, inventory.GENERATED_PAIRS, "{}\n"))
            self.assertIn("drift.missing", found)

    def test_scanner_mutation_changes_the_inventory(self):
        counts = inventory.load_counts_module(REPO_ROOT)
        real_scan = counts.scan_file

        def dropping_scan(relative):
            rows = real_scan(relative)
            if relative == counts.RELATIONS:
                return rows[1:]
            return rows

        counts.scan_file = dropping_scan
        try:
            artifact = inventory.build_declaration_inventory(REPO_ROOT, counts)
        finally:
            counts.scan_file = real_scan
        self.assertEqual(len(artifact["declarations"]), 77)
        self.assertEqual(artifact["counts"]["declarations"], 77)

    def test_pair_census_mutation_changes_the_inventory(self):
        counts = inventory.load_counts_module(REPO_ROOT)
        real_census = counts.pair_census

        def shifted_census():
            census = real_census()
            edge = census["edges"].pop(0)
            census["absences"].append({
                "pair": edge["pair"],
                "cite": "synthetic mutation",
                "registry": "synthetic registry",
            })
            return census

        counts.pair_census = shifted_census
        try:
            artifact = inventory.build_pair_inventory(REPO_ROOT, counts)
        finally:
            counts.pair_census = real_census
        self.assertEqual(artifact["counts"]["legacyEdges"], 25)
        self.assertEqual(artifact["counts"]["legacyUniqueAbsences"], 111)
        self.assertEqual(artifact["counts"]["legacyCoveredPairs"], 136)

    def test_schema_rejects_wrong_entry_count(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["entries"] = ledger["entries"][:-1]
        schema = json_schema.Schema.from_path(os.path.join(REPO_ROOT, inventory.DISPOSITIONS_SCHEMA))
        self.assertTrue(schema.validate(ledger))


if __name__ == "__main__":
    unittest.main()
