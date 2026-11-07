"""Tests for the R3 migration-fragment integration checker and generator.

The migration fragments are the single source of truth: the checker must cover
exactly the 41 R2 certificate-required declarations, and the generated Lean
file must be derived from the fragments rather than from a second list.  These
tests mutate the fragments in memory and assert the fail-closed codes.
"""

from __future__ import annotations

import copy
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), "tools"))

from harness import REPO_ROOT, toolchain_available  # noqa: E402
from relation_audit import migration  # noqa: E402


TOOL = os.path.join(REPO_ROOT, "tools", "relation_audit_migration.py")


def codes(findings) -> set[str]:
    return {finding.code for finding in findings}


def load_base():
    fragments = migration.load_fragments(REPO_ROOT)
    dispositions = migration.load_dispositions(REPO_ROOT)
    relations = os.path.join(REPO_ROOT, migration.RELATIONS)
    with open(relations, encoding="utf-8") as handle:
        source = handle.read()
    return fragments, dispositions, source


BASE_FRAGMENTS, DISPOSITIONS, RELATIONS_SOURCE = load_base()


def validate(fragments, *, dispositions=None, relations_source=RELATIONS_SOURCE):
    return migration.validate_fragments(
        fragments,
        dispositions or DISPOSITIONS,
        relations_source=relations_source,
    )


def mutate(mutator):
    fragments = copy.deepcopy(BASE_FRAGMENTS)
    mutator(fragments)
    return validate(fragments)


def _sync_queue(fragment):
    entries = fragment.get("entries", [])
    queue = fragment.setdefault("queue", {})
    queue["declarationIds"] = [entry["declarationId"] for entry in entries]
    queue["expectedCount"] = len(entries)
    queue["coveredCount"] = len(entries)
    outcomes = {"certified": 0, "reclassified": 0}
    for entry in entries:
        outcome = entry.get("outcome")
        if outcome in outcomes:
            outcomes[outcome] += 1
    queue["outcomeCounts"] = outcomes


def _first_certified(fragments):
    for fragment in fragments:
        for entry in fragment["entries"]:
            if entry.get("outcome") == "certified":
                return fragment, entry
    raise AssertionError("no certified row in fixtures")


def _first_reclassified(fragments):
    for fragment in fragments:
        for entry in fragment["entries"]:
            if entry.get("outcome") == "reclassified":
                return fragment, entry
    raise AssertionError("no reclassified row in fixtures")


def _valid_composition_metadata() -> dict:
    return {
        "parentIDs": ["Test.ParentLeft", "Test.ParentRight"],
        "parentKinds": ["implication", "equivalence"],
        "parentPremiseIDs": [["test.leftPremise"], ["test.rightPremise"]],
        "bridgeIDs": ["test.bridge"],
        "dischargeIDs": [],
        "mediatingStatementID": "Test.Middle",
        "form": "implication",
    }


def _make_composition(fragments, *, metadata=None):
    fragment, entry = _first_certified(fragments)
    entry["relationKind"] = "conditionalComposition"
    entry["certificateConstructor"] = (
        "PhotoLean.RelationAudit.RelationKind.conditionalComposition"
    )
    entry["statement"]["form"] = "conditionalComposition"
    entry["composition"] = metadata or _valid_composition_metadata()
    _sync_queue(fragment)
    return fragment, entry


class FragmentValidationTests(unittest.TestCase):
    def test_actual_fragments_are_clean(self):
        findings = validate(copy.deepcopy(BASE_FRAGMENTS))
        self.assertEqual(findings, [], "\n".join(str(item) for item in findings))

    def test_queue_is_exactly_41_unique_ids(self):
        queue = migration.queue_entries(DISPOSITIONS)
        self.assertEqual(len(queue), 41)
        ids = [entry["declarationId"] for entry in queue]
        self.assertEqual(len(set(ids)), 41)
        entries = migration._entries(BASE_FRAGMENTS)
        self.assertEqual(len(entries), 41)
        self.assertEqual({entry["declarationId"] for _f, entry in entries}, set(ids))

    def test_counts_match_the_section_reports(self):
        entries = migration._entries(BASE_FRAGMENTS)
        certified = [entry for _f, entry in entries if entry["outcome"] == "certified"]
        reclassified = [entry for _f, entry in entries if entry["outcome"] == "reclassified"]
        self.assertEqual((len(certified), len(reclassified)), (27, 14))
        kinds = {}
        for entry in certified:
            kinds[entry["relationKind"]] = kinds.get(entry["relationKind"], 0) + 1
        self.assertEqual(
            kinds,
            {
                "definitionalIdentity": 18,
                "equivalence": 6,
                "observationalEquivalence": 2,
                "implication": 1,
            },
        )

    def test_duplicate_id_rejected(self):
        def mutate_fragment(fragments):
            duplicate = copy.deepcopy(fragments[0]["entries"][0])
            fragments[1]["entries"].append(duplicate)
            _sync_queue(fragments[1])

        findings = mutate(mutate_fragment)
        self.assertIn("migration.duplicateDeclarationId", codes(findings))

    def test_omission_rejected(self):
        def mutate_fragment(fragments):
            removed = fragments[2]["entries"].pop()
            _sync_queue(fragments[2])
            return removed

        findings = mutate(mutate_fragment)
        self.assertIn("migration.omittedDeclarationId", codes(findings))

    def test_unknown_id_rejected(self):
        def mutate_fragment(fragments):
            fragments[0]["entries"][0]["declarationId"] = "D-S99-not-a-real-row"
            _sync_queue(fragments[0])

        findings = mutate(mutate_fragment)
        self.assertIn("migration.unknownDeclarationId", codes(findings))

    def test_wrong_r2_disposition_rejected(self):
        def mutate_fragment(fragments):
            fragments[0]["entries"][0]["r2Ledger"]["disposition"] = "support-lemma"

        findings = mutate(mutate_fragment)
        self.assertIn("migration.r2Ledger", codes(findings))

    def test_section_mismatch_rejected(self):
        def mutate_fragment(fragments):
            fragments[0]["entries"][0]["section"] = 99

        findings = mutate(mutate_fragment)
        self.assertIn("migration.sectionMismatch", codes(findings))

    def test_original_declaration_must_match_the_r2_ledger_name(self):
        def mutate_fragment(fragments):
            fragments[0]["entries"][0]["originalDeclaration"] = (
                "PhotoLean.Relations.some_other_row"
            )

        findings = mutate(mutate_fragment)
        self.assertIn("migration.originalDeclarationMismatch", codes(findings))

    def test_unknown_original_declaration_rejected(self):
        def mutate_fragment(fragments):
            fragments[0]["entries"][0]["originalDeclaration"] = "PhotoLean.Relations.not_delivered"

        findings = mutate(mutate_fragment)
        self.assertIn("migration.originalDeclarationMissing", codes(findings))

    def test_queue_order_mismatch_rejected(self):
        def mutate_fragment(fragments):
            fragments[0]["queue"]["declarationIds"] = list(
                reversed(fragments[0]["queue"]["declarationIds"])
            )

        findings = mutate(mutate_fragment)
        self.assertIn("migration.fragmentQueue", codes(findings))


class CertifiedValidationTests(unittest.TestCase):
    def test_missing_certificate_rejected(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_certified(fragments)
            entry["certificate"] = None

        findings = mutate(mutate_fragment)
        self.assertIn("migration.missingCertificate", codes(findings))

    def test_unknown_relation_kind_rejected(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_certified(fragments)
            entry["relationKind"] = "approximatelyEquivalent"

        findings = mutate(mutate_fragment)
        self.assertIn("migration.relationKind", codes(findings))

    def test_constructor_mismatch_rejected(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_certified(fragments)
            entry["certificateConstructor"] = (
                "PhotoLean.RelationAudit.RelationKind.implication"
            )

        findings = mutate(mutate_fragment)
        self.assertIn("migration.certificateConstructor", codes(findings))

    def test_disallowed_axiom_footprint_rejected(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_certified(fragments)
            entry["axiomFootprint"] = ["propext", "sorryAx"]

        findings = mutate(mutate_fragment)
        self.assertIn("migration.axiomFootprint", codes(findings))

    def test_duplicate_premise_id_rejected(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_certified(fragments)
            entry["premises"] = [
                {"id": "test.same", "predicate": "True"},
                {"id": "test.same", "predicate": "True"},
            ]

        findings = mutate(mutate_fragment)
        self.assertIn("migration.duplicatePremiseId", codes(findings))

    def test_definitional_without_fresh_defeq_rejected(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_certified(fragments)
            entry["statement"]["definitionalWitness"]["kind"] = "propositional-equality"

        findings = mutate(mutate_fragment)
        self.assertIn("migration.definitionalWitness", codes(findings))

    def test_non_certifiable_r2_role_rejected(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_certified(fragments)
            entry["r2Ledger"]["relationRole"] = "transitive-tie-back"

        findings = mutate(mutate_fragment)
        self.assertIn("migration.nonDirectRoleCertified", codes(findings))

    def test_composition_form_must_match_parent_kinds(self):
        def mutate_fragment(fragments):
            metadata = _valid_composition_metadata()
            metadata["form"] = "equivalence"  # one implication parent => implication
            _make_composition(fragments, metadata=metadata)

        findings = mutate(mutate_fragment)
        self.assertIn("migration.compositionForm", codes(findings))

    def test_composition_requires_projections(self):
        def mutate_fragment(fragments):
            _fragment, entry = _make_composition(fragments)
            del entry["composition"]

        findings = mutate(mutate_fragment)
        self.assertIn("migration.compositionMetadata", codes(findings))

    def test_composition_provenance_true_without_composition_rejected(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_certified(fragments)
            entry["compositionProvenance"] = {"typedParentComposition": True}

        findings = mutate(mutate_fragment)
        self.assertIn("migration.compositionMetadata", codes(findings))


class ReclassificationValidationTests(unittest.TestCase):
    def test_missing_target_category_rejected(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_reclassified(fragments)
            entry["targetCategory"] = None

        findings = mutate(mutate_fragment)
        self.assertIn("migration.reclassificationCategory", codes(findings))

    def test_short_rationale_rejected(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_reclassified(fragments)
            entry["rationale"] = "Not a certificate."

        findings = mutate(mutate_fragment)
        self.assertIn("migration.reclassificationRationale", codes(findings))

    def test_duplicate_rationale_rejected(self):
        def mutate_fragment(fragments):
            rows = [
                entry
                for fragment in fragments
                for entry in fragment["entries"]
                if entry.get("outcome") == "reclassified"
            ]
            rows[1]["rationale"] = rows[0]["rationale"]

        findings = mutate(mutate_fragment)
        self.assertIn("migration.reclassificationRationale", codes(findings))

    def test_missing_blockers_rejected(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_reclassified(fragments)
            entry["certificationBlockers"] = []

        findings = mutate(mutate_fragment)
        self.assertIn("migration.reclassificationBlockers", codes(findings))

    def test_reclassified_with_certificate_rejected(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_reclassified(fragments)
            entry["certificate"] = "PhotoLean.RelationAudit.Full.Sections11_17.fake"

        findings = mutate(mutate_fragment)
        self.assertIn("migration.reclassifiedCertificate", codes(findings))

    def test_missing_evidence_rejected(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_reclassified(fragments)
            entry["evidence"] = {}

        findings = mutate(mutate_fragment)
        self.assertIn("migration.reclassificationEvidence", codes(findings))

    def test_certificate_kind_is_not_a_target_category(self):
        def mutate_fragment(fragments):
            _fragment, entry = _first_reclassified(fragments)
            entry["targetCategory"] = "equivalence"

        findings = mutate(mutate_fragment)
        self.assertIn("migration.reclassificationCategory", codes(findings))


class SourceHashTests(unittest.TestCase):
    def test_actual_declared_hashes_match(self):
        findings = migration._validate_lean_hashes(
            REPO_ROOT, copy.deepcopy(BASE_FRAGMENTS)
        )
        self.assertEqual(findings, [])

    def test_stale_declared_hash_rejected(self):
        fragments = copy.deepcopy(BASE_FRAGMENTS)
        fragments[0]["leanSourceSha256"] = "0" * 64
        findings = migration._validate_lean_hashes(REPO_ROOT, fragments)
        self.assertIn("migration.leanSourceHash", codes(findings))


class GeneratorTests(unittest.TestCase):
    def test_every_fragment_certificate_and_evidence_is_generated_once(self):
        source, specs = migration.generate_lean_checks(copy.deepcopy(BASE_FRAGMENTS))
        entries = migration._entries(BASE_FRAGMENTS)
        certificates = [
            entry["certificate"]
            for _fragment, entry in entries
            if entry["outcome"] == "certified"
        ]
        evidence = [
            entry["evidence"]["leanName"]
            for _fragment, entry in entries
            if entry["outcome"] == "reclassified"
        ]
        for name in certificates + evidence:
            self.assertEqual(source.count(f"#check {name}\n"), 1, name)
        self.assertEqual(len(certificates), 27)
        self.assertEqual(len(evidence), 14)
        self.assertEqual(
            len([spec for spec in specs if spec["role"] == "kind"]), 27
        )
        self.assertEqual(
            len([spec for spec in specs if spec["role"] == "premises"]), 27
        )
        self.assertEqual(
            len([spec for spec in specs if spec["role"] == "axioms"]), 27
        )

    def test_generator_is_derived_from_fragments(self):
        fragments = copy.deepcopy(BASE_FRAGMENTS)
        _fragment, entry = _first_certified(fragments)
        source, _specs = migration.generate_lean_checks(fragments)
        self.assertIn(f"#check {entry['certificate']}", source)
        fragments[0]["entries"] = [
            row
            for row in fragments[0]["entries"]
            if row["declarationId"] != entry["declarationId"]
        ]
        _sync_queue(fragments[0])
        reduced, _specs = migration.generate_lean_checks(fragments)
        self.assertNotIn(f"#check {entry['certificate']}", reduced)

    def test_generation_is_deterministic(self):
        first, first_specs = migration.generate_lean_checks(copy.deepcopy(BASE_FRAGMENTS))
        second, second_specs = migration.generate_lean_checks(copy.deepcopy(BASE_FRAGMENTS))
        self.assertEqual(first, second)
        self.assertEqual(first_specs, second_specs)

    def test_composition_projection_generation(self):
        fragments = copy.deepcopy(BASE_FRAGMENTS)
        _fragment, entry = _make_composition(fragments)
        source, specs = migration.generate_lean_checks(fragments)
        certificate = entry["certificate"]
        self.assertIn(
            f"PhotoLean.RelationAudit.certificateParentIDs {certificate}", source
        )
        self.assertIn(
            f"PhotoLean.RelationAudit.certificateParentKinds {certificate}", source
        )
        self.assertIn(
            f"PhotoLean.RelationAudit.certificateParentPremiseIDs {certificate}", source
        )
        self.assertIn(
            f"PhotoLean.RelationAudit.certificateBridgeIDs {certificate}", source
        )
        self.assertIn(
            f"PhotoLean.RelationAudit.certificateDischargeIDs {certificate}", source
        )
        self.assertIn("certificateMediating?", source)
        self.assertIn("certificateCompositionForm?", source)
        roles = {spec["role"] for spec in specs}
        self.assertIn("composition_parents", roles)
        self.assertIn("composition_mediating", roles)

    def test_report_has_every_reclassification(self):
        source, specs = migration.generate_lean_checks(copy.deepcopy(BASE_FRAGMENTS))
        report = migration.build_report(
            copy.deepcopy(BASE_FRAGMENTS), DISPOSITIONS, REPO_ROOT, source, specs
        )
        self.assertEqual(report["queue"]["expectedCount"], 41)
        self.assertEqual(report["queue"]["coveredCount"], 41)
        self.assertEqual(report["counts"]["certified"], 27)
        self.assertEqual(report["counts"]["reclassified"], 14)
        self.assertEqual(report["counts"]["conditionalCompositionCertificates"], 0)
        self.assertEqual(len(report["reclassifications"]), 14)
        for row in report["reclassifications"]:
            self.assertGreaterEqual(len(row["rationale"]), migration.MIN_RATIONALE_CHARS)
            self.assertTrue(row["evidenceLeanName"])
            self.assertTrue(row["certificationBlockers"])


class AxiomParsingTests(unittest.TestCase):
    def test_footprints_are_parsed_across_line_wrapping(self):
        output = (
            "'PhotoLean.A' depends on axioms: [propext,\n"
            " Classical.choice, Quot.sound]\n"
            "'PhotoLean.B' does not depend on any axioms\n"
        )
        parsed = migration.parse_axiom_footprints(output)
        self.assertEqual(
            parsed["PhotoLean.A"], {"propext", "Classical.choice", "Quot.sound"}
        )
        self.assertEqual(parsed["PhotoLean.B"], set())


class CliAndLeanTests(unittest.TestCase):
    def test_check_cli_passes_on_checked_in_artifacts(self):
        completed = subprocess.run(
            [sys.executable, TOOL, "--check"],
            cwd=REPO_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=120,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        self.assertIn("migration check: OK", completed.stdout)

    @unittest.skipUnless(toolchain_available(), "Lean toolchain not available")
    def test_generated_checks_elaborate_and_axioms_match(self):
        completed = subprocess.run(
            [sys.executable, TOOL, "--check", "--lean"],
            cwd=REPO_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=900,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        self.assertIn("lean checks: OK", completed.stdout)


if __name__ == "__main__":
    unittest.main()
