# WP-SURFACE-01 — bounded screening package (R2)

This directory contains the R2 statement-level screening package for the ten
pairs named in `loop/计划.md` step 1. The package is deliberately narrow: it
records what the frozen R1 inventory, the accepted legacy registry, and the
delivered Lean sources actually support, and it does not claim completeness for
any pair.

## Work-package membership

The approved R2 plan names these ten pairs:

```
P-Marcus-Hammond          P-Marcus-BEP
P-Marcus-Sabatier         P-Hammond-BEP
P-Hammond-Sabatier        P-Hammond-SymmetryFactor
P-BEP-Sabatier            P-BEP-SymmetryFactor
P-Kasha-Sabatier          P-Sabatier-SymmetryFactor
```

The R1 cluster plan's `WP-surface-free-energy-01` has a different membership:
it contains `P-Marcus-SymmetryFactor` and omits `P-Kasha-Sabatier`. This
package follows the approved R2 plan and records the mismatch in
`screening.json.workPackage.r1ClusterPlanWorkPackage`. No R1 artifact is edited.

## Artifacts

- `screening.json` — ten pairs, nineteen named queries, complete endpoint /
  context / translation / premise / scope / provenance records, and one outcome
  per query.
- `search-log.json` — bounded searches for the three unresolved queries.
- `probes/Surface-probe.lean` — the four R2 probe certificates. The probe is
  compiled with `lake env lean` and carries `#print axioms` print-outs.
- `evidence/legacy-axioms.log` — per-declaration axiom audits for the twelve
  reused legacy certificates.
- `evidence/surface-probe.log` — compile and axiom output for the four probe
  certificates.
- `evidence/explain-pairs.log` — machine-recomputable legacy dispositions for
  the three unresolved pairs.
- `evidence/probe-scan.log` — forbidden-token scan and compile exit for the probe.
- `evidence/mutation-tests.log` — fail-closed mutation tests of the validator.
- `build_screening.py` — deterministic builder kept for reproducibility; the
  acceptance gate is `../validate_screening.py`.

## Outcome summary

| status | queries |
|---|---:|
| certified | 16 |
| unresolved | 3 |
| refuted | 0 |
| notEstablished | 0 |
| outOfScope | 0 |
| **total** | **19** |

Certified kinds: definitionalIdentity 4, equivalence 4, conditionalComposition
1, implication 2, observationalEquivalence 5. The three unresolved queries are
the descriptor-level comparisons for `P-Hammond-Sabatier`, `P-Kasha-Sabatier`
and `P-Sabatier-SymmetryFactor`; their term-level candidates are recorded but
not certified.

## Why a probe instead of `PhotoLean/BoundedAudit/Surface.lean`

The R1 contract freezes the complete `PhotoLean/**/*.lean` file set to 102
files; `audit_boundary/validate_boundary.py` fails with
`FAIL [inventory.manifestSet] source manifest file set differs from the
delivered Lean tree` when a new module is added there. The R2 plan also
requires the same R1 validator to exit 0 and forbids editing R1 artifacts.
The four new certificates are therefore checked as a compiled probe under
`bounded_audit/`, not delivered as a `PhotoLean` module. Each probe certificate
wraps a delivered theorem and carries a fresh `def` with a `Certificate` type
and a `_kind` theorem; `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound`.

This is a recorded deviation from the plan's suggested path, not a silent
change. The probe hash is pinned in each `r2-probe-certificate` evidence row.

## Reproduction

From the repository root (`photolean/`):

```bash
python3 audit_boundary/validate_boundary.py
python3 bounded_audit/validate_screening.py bounded_audit/wp-surface-01/screening.json
sha256sum relation_audit/registry.json
proofs/scripts/lake env lean bounded_audit/wp-surface-01/probes/Surface-probe.lean
proofs/scripts/check.sh --strict
```

The last command builds the delivered tree and scans it for unproved
placeholders and custom axioms. The probe is outside the `PhotoLean` scan root,
so `validate_screening.py` also scans the probe for the same forbidden tokens.

## Non-claims

- The package is not a completeness claim about any pair.
- A certified row is a checked relation under its declared context, premises
  and snapshot; it is not a claim of physical universality.
- An unresolved row is not a negative claim and is not a refutation.
- No pair was forced into a relation to increase edge count.
