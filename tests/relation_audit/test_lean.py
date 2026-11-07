"""Tests for the generated Lean certificate checks.

These tests use an inline mock prelude, so they exercise the real Lean
toolchain without depending on PhotoLean/RelationAudit being delivered yet.
"""

from __future__ import annotations

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), "tools"))

from harness import REPO_ROOT, toolchain_available  # noqa: E402
from relation_audit.lean import ALLOWED_AXIOMS, LeanHarness, SourceBuilder  # noqa: E402


PRELUDE = """\
inductive Kind where
  | implication
  | equivalence

def certificateKind : Kind -> Kind := fun k => k

def certImp : Kind := Kind.implication
def certEq : Kind := Kind.equivalence
def certAxiomFree : Kind := Kind.equivalence
theorem evidence : True := True.intro
theorem evidenceBad : True := evidence
noncomputable def pick (a : Type) [Nonempty a] : a := Classical.choice (inferInstance)
"""


def cert_spec(name: str = "certImp", expected: str = "Kind.implication") -> dict:
    return {
        "shape": "certificate",
        "check_id": "test.certificate",
        "location": "test",
        "certificate": name,
        "kind_function": "certificateKind",
        "expected_constructor": expected,
    }


def decl_spec(name: str, **kwargs) -> dict:
    spec = {
        "shape": "declaration",
        "check_id": f"test.{name}",
        "location": "test",
        "declaration": name,
    }
    spec.update(kwargs)
    return spec


@unittest.skipUnless(toolchain_available(), "Lean toolchain not available")
class LeanHarnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.harness = LeanHarness(REPO_ROOT, timeout=120)

    def test_generated_source_contains_all_required_checks(self):
        spec = cert_spec()
        source, checks = self.harness.build_source(
            [spec], imports=["Foo.Bar"], prelude=PRELUDE)
        lines = source.splitlines()
        rendered = [lines[check.line - 1] for check in checks]
        self.assertIn("import Foo.Bar", lines)
        self.assertTrue(any(item == "#check certImp" for item in rendered))
        self.assertTrue(any(
            item == "example : certificateKind certImp = Kind.implication := rfl"
            for item in rendered))
        self.assertTrue(any(item == "#print axioms certImp" for item in rendered))

    def test_valid_certificate_and_evidence_pass(self):
        outcome = self.harness.run(
            [cert_spec(), decl_spec("evidence")], prelude=PRELUDE)
        self.assertEqual(outcome.status, "PASS", outcome.findings)
        self.assertFalse([f for f in outcome.findings if f.status == "FAIL"])

    def test_mislabelled_kind_is_rejected_by_the_rfl_check(self):
        outcome = self.harness.run(
            [cert_spec(expected="Kind.equivalence")], prelude=PRELUDE)
        self.assertEqual(outcome.status, "FAIL")
        self.assertIn("lean.certificateKind", {f.code for f in outcome.findings})

    def test_missing_declaration_is_rejected(self):
        outcome = self.harness.run(
            [cert_spec("Does.not.exist", "Kind.implication")], prelude=PRELUDE)
        self.assertEqual(outcome.status, "FAIL")
        self.assertIn("lean.existence", {f.code for f in outcome.findings})

    def test_disallowed_axiom_footprint_is_rejected(self):
        prelude = PRELUDE + "\naxiom customAxiom : True\n"
        spec = decl_spec("customAxiom")
        outcome = self.harness.run([spec], prelude=prelude)
        self.assertEqual(outcome.status, "FAIL")
        self.assertIn("lean.axioms", {f.code for f in outcome.findings})

    def test_allowed_axiom_is_reported_as_pass(self):
        outcome = self.harness.run([decl_spec("pick")], prelude=PRELUDE)
        self.assertEqual(outcome.status, "PASS", outcome.findings)
        self.assertIn("Classical.choice", ALLOWED_AXIOMS)
        messages = [f.message for f in outcome.findings if f.code == "lean.axioms"]
        self.assertTrue(any("Classical.choice" in message for message in messages))

    def test_there_is_no_empty_footprint_requirement(self):
        # Contract section 5: definitional witnesses use the standard allowed
        # axiom whitelist; only the fresh rfl check establishes definitional
        # identity.  The harness must expose no "must be axiom-free" path.
        spec = decl_spec("pick")
        self.assertNotIn("allow_empty_axioms", spec)
        outcome = self.harness.run([spec], prelude=PRELUDE)
        codes = {finding.code for finding in outcome.findings}
        self.assertEqual(outcome.status, "PASS", outcome.findings)
        self.assertNotIn("lean.rflAxioms", codes)

    def test_timeout_is_a_failure_not_a_skip(self):
        harness = LeanHarness(REPO_ROOT, timeout=0.001)
        outcome = harness.run([cert_spec()], prelude=PRELUDE)
        self.assertEqual(outcome.status, "FAIL")
        self.assertIn("lean.timeout", {f.code for f in outcome.findings})

    def test_missing_toolchain_is_skipped_not_passed(self):
        harness = LeanHarness("/nonexistent-relation-audit-root")
        outcome = harness.run([cert_spec()], prelude=PRELUDE)
        self.assertEqual(outcome.status, "SKIP")
        self.assertIn("lean.unavailable", {f.code for f in outcome.findings})


REAL_OLEAN = os.path.join(
    REPO_ROOT, ".lake", "build", "lib", "PhotoLean", "RelationAudit.olean")

REAL_CERTIFICATES = [
    ("kernelBarrierPin", "definitionalIdentity"),
    ("epBoundsImplication", "implication"),
    ("betaHalfEquivalence", "equivalence"),
    # The Kasha–Marcus row is a conditional equivalence carrying the `hic`
    # premise; the genuine proof-relevant composition is the Marcus
    # normal-direction chain through EPBounds, with both of its typed parents.
    ("kashaMarcusEquivalence", "equivalence"),
    ("marcusNormalImplication", "implication"),
    ("epBoundsNoInvertedEquivalence", "equivalence"),
    ("marcusNormalNoInvertedComposition", "conditionalComposition"),
    ("svIntensityObservationalEquivalence", "observationalEquivalence"),
    ("svJointDistinguishability", "distinguishability"),
    ("svJointIdentifiability", "distinguishability"),
    ("kvRefutation", "refutation"),
]


@unittest.skipUnless(toolchain_available() and os.path.isfile(REAL_OLEAN),
                     "PhotoLean.RelationAudit is not built in this checkout")
class DeliveredCertificateIntegrationTests(unittest.TestCase):
    """Run the generated checks against the real delivered certificate values."""

    def test_delivered_pilot_certificates_elaborate_and_match_their_kinds(self):
        harness = LeanHarness(REPO_ROOT, timeout=300)
        all_axioms = frozenset({"propext", "Classical.choice", "Quot.sound"})
        specs = []
        for index, (name, kind) in enumerate(REAL_CERTIFICATES):
            specs.append({
                "shape": "certificate",
                "check_id": f"real.{index}",
                "location": name,
                "certificate": f"PhotoLean.RelationAudit.{name}",
                "kind_function": "PhotoLean.RelationAudit.certificateKind",
                "expected_constructor": f"PhotoLean.RelationAudit.RelationKind.{kind}",
                "expected_axioms": all_axioms,
            })
        outcome = harness.run(specs, imports=["PhotoLean.RelationAudit"])
        self.assertEqual(outcome.status, "PASS", outcome.findings)


class SourceBuilderTests(unittest.TestCase):
    def test_line_numbers_account_for_header_imports_and_prelude(self):
        builder = SourceBuilder(imports=["Foo.Bar"], prelude="def z := 1")
        builder.add_certificate(
            "c", "here", "cert", "kindFn", "Kind.impl")
        source = builder.build()
        lines = source.splitlines()
        for check in builder.checks:
            rendered = lines[check.line - 1]
            self.assertIn(check.role == "kind" and "example" or "#", rendered)


if __name__ == "__main__":
    unittest.main()
