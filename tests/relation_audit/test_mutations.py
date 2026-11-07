"""Mutation tests: every invalid fixture (and every in-memory mutation) must be rejected.

The validator must exit non-zero and emit the specific failure code for the
mutation.  Structural mutations run with ``--no-lean`` so the tests stay fast;
the Lean-relabelling mutation runs the real generated certificateKind check.
"""

from __future__ import annotations

import copy
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from harness import (  # noqa: E402
    FULL, PILOT, failure_codes, invalid_fixture, load_json,
    mock_lean_root, run_cli, write_mutant,
)


# fixture file -> (mode, expected failure code, requires Lean)
FIXTURE_MUTATIONS = {
    "mislabelled_kind.json": ("pilot", "status.certificateMismatch", False),
    "mislabelled_kind_lean.json": ("pilot", "lean.certificateKind", True),
    "composition_wrong_parent_order.json": ("pilot", "lean.compositionParentIDs", True),
    "composition_parent_premise_drift.json": ("pilot", "lean.compositionParentPremiseIDs", True),
    "composition_wrong_mediator.json": ("pilot", "lean.compositionMediating", True),
    "missing_premise.json": ("pilot", "premise.closure", False),
    "incomplete_bridge.json": ("pilot", "composition.bridge", False),
    "bridge_unrelated_witness.json": ("pilot", "composition.bridgeUnsupported", False),
    "discharge_unrelated_witness.json": ("pilot", "composition.dischargeUnsupported", False),
    "badge_nonvacuous_unrelated.json": ("pilot", "badge.nonvacuousUnsupported", False),
    "badge_nonredundant_unrelated.json": ("pilot", "badge.nonredundantUnsupported", False),
    "badge_weakest_unrelated.json": ("pilot", "badge.weakestUnsupported", False),
    "stale_snapshot.json": ("pilot", "snapshot.unknownCommit", False),
    "stale_artifact.json": ("pilot", "snapshot.staleArtifact", False),
    "conflicting_statuses.json": ("pilot", "conflict.statuses", False),
    "missing_pair.json": ("full", "coverage.missingPair", False),
    "missing_provenance.json": ("pilot", "provenance.missing", False),
    "missing_certificate.json": ("pilot", "ref.certificate", False),
    "adjudication_kind.json": ("pilot", "kind.adjudication", False),
    "missing_dependencies.json": ("pilot", "status.dependencies", False),
    "missing_badge_evidence.json": ("pilot", "badge.nonvacuousUnsupported", False),
    "duplicate_id.json": ("pilot", "id.duplicate", False),
    "unknown_premise.json": ("pilot", "premise.unknown", False),
    "scope_jurisdiction.json": ("pilot", "scope.jurisdiction", False),
}


class InvalidFixtureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lean_root, cls.lean_reason = mock_lean_root()

    def _run(self, path: str, mode: str, needs_lean: bool):
        lean_root = None
        if needs_lean:
            if not self.lean_root:
                self.skipTest(self.lean_reason)
            lean_root = self.lean_root
        completed = run_cli(path, mode=mode, no_lean=not needs_lean,
                            lean_root=lean_root)
        return completed, failure_codes(completed.stdout)

    def test_every_invalid_fixture_is_rejected_with_its_code(self):
        for name, (mode, code, needs_lean) in FIXTURE_MUTATIONS.items():
            with self.subTest(fixture=name):
                path = invalid_fixture(name)
                self.assertTrue(os.path.isfile(path), path)
                completed, codes = self._run(path, mode, needs_lean)
                self.assertEqual(completed.returncode, 1,
                                 f"{name} must be a real rejection (FAIL), not a skipped "
                                 f"run:\n{completed.stdout}")
                self.assertIn(code, codes,
                              f"{name}: expected {code}, got {sorted(codes)}")
                self.assertNotIn("overall: PASS", completed.stdout)

    def test_lean_relabelling_is_caught_by_certificate_kind_check(self):
        if not self.lean_root:
            self.skipTest(self.lean_reason)
        completed = run_cli(invalid_fixture("mislabelled_kind_lean.json"),
                            mode="pilot", lean_root=self.lean_root)
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("lean.certificateKind", completed.stdout)
        self.assertIn("rfl", completed.stdout)


class InMemoryMutationTests(unittest.TestCase):
    """Mutate the valid fixture in memory; each mutant must be rejected."""

    @classmethod
    def setUpClass(cls):
        cls.lean_root, cls.lean_reason = mock_lean_root()

    def _reject(self, data: dict, expected: str, mode: str = "pilot"):
        path = write_mutant(data)
        try:
            completed = run_cli(path, mode=mode, no_lean=True)
        finally:
            os.unlink(path)
        self.assertNotEqual(completed.returncode, 0, completed.stdout)
        self.assertIn(expected, failure_codes(completed.stdout),
                      f"expected {expected}, got {sorted(failure_codes(completed.stdout))}")

    def test_mislabelled_kind(self):
        data = copy.deepcopy(load_json(PILOT))
        for record in data["records"]:
            if record["id"] == "rec-equiv":
                record["relationKind"] = "definitionalIdentity"
        self._reject(data, "status.certificateMismatch")

    def test_missing_premise(self):
        data = copy.deepcopy(load_json(PILOT))
        for record in data["records"]:
            if record["id"] == "rec-comp":
                record["premises"] = [p for p in record["premises"]
                                      if p["id"] != "p-adj"]
        self._reject(data, "premise.closure")

    def test_declared_bridge_is_rejected_even_with_a_complete_shape(self):
        data = copy.deepcopy(load_json(PILOT))
        for record in data["records"]:
            if record["id"] == "rec-comp":
                record["premises"].append({
                    "id": "p-bridge",
                    "statement": "A declared bridge premise.",
                })
                record["composition"]["bridges"] = [{
                    "premiseId": "p-bridge",
                    "statement": "A declared bridge premise.",
                    "expectedType": "True",
                    "witness": "RelationAuditFixture.bridgeWitness",
                }]
        self._reject(data, "composition.bridgeUnsupported")

    def test_stale_snapshot(self):
        data = copy.deepcopy(load_json(PILOT))
        data["snapshots"][0]["treeSha"] = "f" * 40
        self._reject(data, "snapshot.unknownCommit")

    def test_conflicting_statuses(self):
        data = copy.deepcopy(load_json(PILOT))
        source = next(r for r in data["records"] if r["id"] == "rec-equiv")
        conflict = copy.deepcopy(source)
        conflict["id"] = "rec-mutant-conflict"
        conflict["status"] = "unresolved"
        conflict["candidate"] = "implication"
        for key in ("relationKind", "certificate", "premises", "badges"):
            conflict.pop(key, None)
        conflict["rationale"] = "mutant conflict"
        conflict["provenance"]["rationale"] = "mutant conflict"
        data["records"].append(conflict)
        self._reject(data, "conflict.statuses")

    def test_missing_provenance(self):
        data = copy.deepcopy(load_json(PILOT))
        for record in data["records"]:
            if record["id"] == "rec-def":
                record.pop("provenance")
        self._reject(data, "provenance.missing")

    def test_missing_pair(self):
        data = copy.deepcopy(load_json(FULL))
        data["records"] = [r for r in data["records"] if r["id"] != "rec-full-15-16"]
        data["queries"] = [q for q in data["queries"] if q["id"] != "q-full-15-16"]
        self._reject(data, "coverage.missingPair", mode="full")

    def test_duplicate_id(self):
        data = copy.deepcopy(load_json(PILOT))
        duplicate = copy.deepcopy(next(r for r in data["records"]
                                       if r["id"] == "rec-def"))
        data["records"].append(duplicate)
        self._reject(data, "id.duplicate")

    def test_unknown_premise(self):
        data = copy.deepcopy(load_json(PILOT))
        for record in data["records"]:
            if record["id"] == "rec-impl":
                record["premises"].append({
                    "id": "p-extra", "statement": "unregistered premise"})
        self._reject(data, "premise.unknown")

    def test_constructor_does_not_match_declared_kind(self):
        data = copy.deepcopy(load_json(PILOT))
        for certificate in data["certificates"]:
            if certificate["id"] == "cert-equiv":
                certificate["constructor"] = \
                    "RelationAuditFixture.CertificateKind.definitionalIdentity"
        self._reject(data, "certificate.kindConstructorMismatch")

    def test_mode_mismatch(self):
        data = copy.deepcopy(load_json(PILOT))
        data["mode"] = "full"
        self._reject(data, "mode.mismatch")

    def test_pair_count_mismatch(self):
        data = copy.deepcopy(load_json(PILOT))
        data["pairCount"] = 135
        self._reject(data, "coverage.pairCount")

    def test_scope_does_not_cover_endpoints(self):
        data = copy.deepcopy(load_json(PILOT))
        for record in data["records"]:
            if record["id"] == "rec-def":
                record["scope"] = "bep-kasha"
        self._reject(data, "scope.jurisdiction")

    def test_explicit_badge_premise_ids_must_match_the_record(self):
        data = copy.deepcopy(load_json(PILOT))
        for record in data["records"]:
            if record["id"] == "rec-impl":
                record["badges"]["explicit"]["premiseIds"] = ["p-pos"]
        self._reject(data, "badge.explicitPremiseIds")

    def test_declared_axiom_footprint_drift_is_rejected(self):
        if not self.lean_root:
            self.skipTest(self.lean_reason)
        data = copy.deepcopy(load_json(PILOT))
        for certificate in data["certificates"]:
            if certificate["id"] == "cert-def":
                certificate["axiomFootprint"] = ["propext"]
        path = write_mutant(data)
        try:
            completed = run_cli(path, mode="pilot", lean_root=self.lean_root)
        finally:
            os.unlink(path)
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("lean.axiomFootprint", completed.stdout)

    def test_certificate_premise_projection_is_checked(self):
        # The certificate's canonical premise IDs must equal the manifest's
        # declared certificate premises; a manifest cannot attribute an extra
        # premise to a certificate value.
        if not self.lean_root:
            self.skipTest(self.lean_reason)
        data = copy.deepcopy(load_json(PILOT))
        for certificate in data["certificates"]:
            if certificate["id"] == "cert-impl":
                certificate["premises"].append({
                    "id": "p-extra", "statement": "An extra premise."})
        path = write_mutant(data)
        try:
            completed = run_cli(path, mode="pilot", lean_root=self.lean_root)
        finally:
            os.unlink(path)
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("lean.certificatePremiseIDs", completed.stdout)

    def test_old_composition_duplication_is_schema_rejected(self):
        # The schema no longer accepts a second combinator/application or a
        # parentEvidence array: the Lean ConditionalComposition constructor is
        # authoritative and the canonical projections are checked instead.
        data = copy.deepcopy(load_json(PILOT))
        for record in data["records"]:
            if record["id"] == "rec-comp":
                record["composition"]["combinator"] = "RelationAuditFixture.composeMock"
        path = write_mutant(data)
        try:
            completed = run_cli(path, mode="pilot", no_lean=True)
        finally:
            os.unlink(path)
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("schema.invalid", completed.stdout)

    def test_definitional_rfl_check_is_generated_and_enforced(self):
        if not self.lean_root:
            self.skipTest(self.lean_reason)
        data = copy.deepcopy(load_json(PILOT))
        for certificate in data["certificates"]:
            if certificate["id"] == "cert-def":
                certificate["semantics"]["rflCheck"]["rhs"] = \
                    "RelationAuditFixture.certEquiv"
        path = write_mutant(data)
        try:
            completed = run_cli(path, mode="pilot", lean_root=self.lean_root)
        finally:
            os.unlink(path)
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("lean.rflCheck", completed.stdout)


class ContractAlignmentTests(unittest.TestCase):
    """Lead-mandated contract corrections R2-R4 exercised end to end."""

    @classmethod
    def setUpClass(cls):
        cls.lean_root, cls.lean_reason = mock_lean_root()

    def setUp(self):
        if not self.lean_root:
            self.skipTest(self.lean_reason)

    def _run_with_lean(self, data: dict, mode: str = "pilot"):
        path = write_mutant(data)
        try:
            completed = run_cli(path, mode=mode, lean_root=self.lean_root)
        finally:
            os.unlink(path)
        return completed

    def test_empty_bridges_are_allowed(self):
        # The pilot composition record uses `bridges: []` because the parent
        # contexts already align (contract section 4).  A full pass proves the
        # validator does not require a non-empty bridge list.
        complete = run_cli(PILOT, mode="pilot", lean_root=self.lean_root)
        self.assertEqual(complete.returncode, 0, complete.stdout + complete.stderr)
        self.assertNotIn("composition.bridges", complete.stdout)
        self.assertNotIn("composition.bridgeUnsupported", complete.stdout)

    def test_different_certified_kinds_coexist(self):
        # Contract sections 7 and 8: multiple certified relations may share
        # (queryId, statementVersion, scope); different certified kinds are not
        # inherently contradictory.
        data = copy.deepcopy(load_json(PILOT))
        extra = copy.deepcopy(next(r for r in data["records"]
                                   if r["id"] == "rec-impl"))
        extra["id"] = "rec-impl-equivalence"
        extra["relationKind"] = "equivalence"
        extra["certificate"] = "cert-equiv"
        extra["premises"] = [{
            "id": "p-pos",
            "statement": "The reorganization energy is positive.",
        }]
        extra["badges"] = {}
        data["records"].append(extra)
        completed = self._run_with_lean(data)
        self.assertEqual(completed.returncode, 0,
                         completed.stdout + completed.stderr)
        self.assertNotIn("conflict.kinds", completed.stdout)
        self.assertNotIn("conflict.statuses", completed.stdout)

    def test_definitional_witness_may_use_allowed_axioms(self):
        # R2: a definitional witness legitimately using Classical.choice must
        # pass the standard whitelist; the fresh rfl check is still generated.
        data = copy.deepcopy(load_json(PILOT))
        for certificate in data["certificates"]:
            if certificate["id"] == "cert-def":
                certificate["semantics"]["rflWitness"] = \
                    "RelationAuditFixture.rflWitnessClassical"
                certificate["semantics"]["rflWitnessAxiomFootprint"] = \
                    ["Classical.choice"]
        completed = self._run_with_lean(data)
        self.assertEqual(completed.returncode, 0,
                         completed.stdout + completed.stderr)
        self.assertNotIn("lean.rflAxioms", completed.stdout)
        self.assertNotIn("lean.axioms", completed.stdout)

    def test_declared_bridge_fails_the_canonical_bridge_id_projection(self):
        # A declared bridge is rejected as unsupported evidence, and the
        # canonical certificateBridgeIDs projection also rejects the non-empty
        # manifest list because the Lean child carries no bridge.
        data = copy.deepcopy(load_json(PILOT))
        rec = next(r for r in data["records"] if r["id"] == "rec-comp")
        rec["composition"]["bridges"] = [{
            "premiseId": "p-bridge",
            "statement": "A declared bridge premise.",
            "expectedType": "True",
            "witness": "RelationAuditFixture.bridgeWitness",
        }]
        rec["premises"].append({
            "id": "p-bridge",
            "statement": "A declared bridge premise.",
        })
        completed = self._run_with_lean(data)
        self.assertEqual(completed.returncode, 1, completed.stdout)
        codes = failure_codes(completed.stdout)
        self.assertIn("composition.bridgeUnsupported", codes)
        self.assertIn("lean.compositionBridgeIDs", codes)

    def test_declared_discharge_fails_the_canonical_discharge_id_projection(self):
        # A declared discharge is rejected as unsupported evidence, and the
        # canonical certificateDischargeIDs projection also rejects the
        # non-empty manifest list because the Lean child carries no discharge.
        data = copy.deepcopy(load_json(PILOT))
        rec = next(r for r in data["records"] if r["id"] == "rec-comp")
        rec["premises"] = [p for p in rec["premises"] if p["id"] != "p-pos"]
        rec["composition"]["discharges"] = [{
            "premiseId": "p-pos",
            "retainedPremiseIds": ["p-adj"],
            "expectedType": "True",
            "witness": "RelationAuditFixture.rflWitness",
        }]
        completed = self._run_with_lean(data)
        self.assertEqual(completed.returncode, 1, completed.stdout)
        codes = failure_codes(completed.stdout)
        self.assertIn("composition.dischargeUnsupported", codes)
        self.assertIn("lean.compositionDischargeIDs", codes)

    def test_definitional_witness_footprint_drift_is_rejected(self):
        # R2: the standard whitelist applies, but a declared footprint that
        # differs from Lean's actual #print axioms is drift, not evidence.
        data = copy.deepcopy(load_json(PILOT))
        for certificate in data["certificates"]:
            if certificate["id"] == "cert-def":
                certificate["semantics"]["rflWitnessAxiomFootprint"] = ["propext"]
        completed = self._run_with_lean(data)
        self.assertEqual(completed.returncode, 1, completed.stdout)
        self.assertIn("lean.axiomFootprint", failure_codes(completed.stdout))

    def test_unrelated_declarations_cannot_earn_badges(self):
        # R3: each of these declarations exists and has an allowed footprint,
        # but none is typed evidence for the claimed badge.
        data = copy.deepcopy(load_json(PILOT))
        rec = next(r for r in data["records"] if r["id"] == "rec-impl")
        rec["badges"].update({
            "nonvacuous": {
                "lean": "RelationAuditFixture.rflWitness",
                "expectedType": "True",
                "premiseIds": ["p-adj"],
            },
            "nonredundant": {
                "premiseIds": ["p-adj"],
                "byPremise": {
                    "p-adj": {
                        "lean": "RelationAuditFixture.rflWitness",
                        "expectedType": "True",
                    },
                },
            },
            "weakest": {
                "premiseIds": ["p-adj"],
                "preorder": "premise-strength",
                "alternatives": ["p-adj"],
                "expectedType": "True",
                "minimality": "RelationAuditFixture.rflWitness",
            },
        })
        completed = self._run_with_lean(data)
        self.assertEqual(completed.returncode, 1, completed.stdout)
        codes = failure_codes(completed.stdout)
        for code in ("badge.nonvacuousUnsupported",
                     "badge.nonredundantUnsupported",
                     "badge.weakestUnsupported"):
            self.assertIn(code, codes)
        for stale in ("badge.nonvacuous", "badge.nonredundant",
                      "badge.nonredundantCoverage", "badge.weakestEvidence"):
            self.assertNotIn(stale, codes)


class DirtySnapshotTests(unittest.TestCase):
    def test_dirty_snapshot_passes_with_working_tree_hashes(self):
        import json
        import tempfile
        data = copy.deepcopy(load_json(PILOT))
        data["snapshots"][0]["dirty"] = True
        path = write_mutant(data)
        handle = tempfile.NamedTemporaryFile(suffix=".json", delete=False)
        handle.close()
        try:
            completed = run_cli(path, mode="pilot", no_lean=True,
                                extra=["--verbose"], json_out=handle.name)
            with open(handle.name, encoding="utf-8") as stream:
                report = json.load(stream)
        finally:
            os.unlink(path)
            os.unlink(handle.name)
        # The only skip is the requested Lean gate; dirty hashes match the tree.
        self.assertEqual(completed.returncode, 2, completed.stdout)
        self.assertIn("snapshot.dirty", completed.stdout)
        self.assertNotIn("snapshot.staleArtifact", completed.stdout)
        self.assertEqual(report["caveats"][0]["code"], "snapshotDirty")
        self.assertTrue(report["metadata"]["snapshotDirty"])

    def test_dirty_snapshot_hash_mismatch_is_rejected(self):
        data = copy.deepcopy(load_json(PILOT))
        data["snapshots"][0]["dirty"] = True
        data["snapshots"][0]["artifacts"]["PhotoLean/Marcus/Barrier.lean"] = "0" * 64
        path = write_mutant(data)
        try:
            completed = run_cli(path, mode="pilot", no_lean=True)
        finally:
            os.unlink(path)
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("snapshot.staleArtifact", completed.stdout)


class FailClosedTests(unittest.TestCase):
    def test_skipped_lean_is_never_pass(self):
        completed = run_cli(PILOT, mode="pilot", no_lean=True)
        self.assertEqual(completed.returncode, 2)
        self.assertIn("lean.notRequested", completed.stdout)
        self.assertIn("overall: INCOMPLETE", completed.stdout)

    def test_no_certificates_means_lean_is_not_applicable(self):
        completed = run_cli(FULL, mode="full")
        self.assertEqual(completed.returncode, 0)
        self.assertIn("lean         NOT_APPLICABLE", completed.stdout)


if __name__ == "__main__":
    unittest.main()
