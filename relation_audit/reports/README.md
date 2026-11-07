# Production pilot reports

This directory contains the machine-readable evidence of the production pilot
run of the certified relation audit in the isolated checkout.

## Run

```bash
cd relation-genealogy/photolean

# production pilot, Lean checks enabled, report + generated Lean checks archived
python3 tools/relation_audit.py \
    --manifest relation_audit/pilot.json \
    --schema relation_audit/schema.json \
    --mode pilot \
    --keep-temps \
    --lean-source-out relation_audit/reports/production-pilot-lean-checks.lean \
    --json-out relation_audit/reports/production-pilot.json

# all fixtures and mutation tests
python3 tests/relation_audit/run_tests.py
```

Exit code of the pilot run: `0` (`PASS`). No gate is `NOT_APPLICABLE` in this
run, and `skipCount` is `0`: every requested check ran.

## Files

| file | contents |
|---|---|
| `production-pilot.json` | full machine-readable report: gates, findings, coverage, counts, unresolved set, caveats, Lean metadata |
| `production-pilot-lean-checks.lean` | the exact generated Lean check file from the run (34 specs / 61 generated commands) |

The report records `metadata.lean.sourceOutSha256`, which must equal the
SHA-256 of `production-pilot-lean-checks.lean`.

## Result summary

| item | value |
|---|---|
| overall | `PASS`, exit `0`, `failureCount = 0`, `skipCount = 0` |
| gates | structure, references, semantics, provenance, snapshot, coverage, lean all `PASS` |
| theories | `17/17` |
| pair universe | `136` |
| registry coverage | `6/136` pairs |
| resolved coverage | `4/136` pairs (`resolvedCoverageComplete = false`) |
| unresolved records | `1` |
| records | `11`: certified `9`, unresolved `1`, notEstablished `1`, outOfScope `0` |
| certified by kind | definitionalIdentity `1`, implication `1`, equivalence `2`, conditionalComposition `1`, observationalEquivalence `1`, distinguishability `2`, refutation `1` |
| Lean specs / generated commands | `34` / `61` |
| snapshot | `snap-relation-audit-2026-10-31` at `7ad25a5f...`, `dirty: true` |

The `dirty: true` snapshot is deliberate: the relation-audit layer is
uncommitted in the isolated checkout, so artifact hashes are matched against
the working tree at the recorded commit. The report carries a `snapshotDirty`
caveat. A full-registry `PASS` is **not** claimed; the pilot covers only six
cross-theory pairs.

## Composition evidence

The single composition record `rec-composition` uses the delivered
`PhotoLean.RelationAudit.marcusNormalNoInvertedComposition` certificate with
the parents `marcusNormalImplication` and `epBoundsNoInvertedEquivalence`. The
generated Lean file contains the canonical projection checks:

```lean
example : certificateParentIDs ... = ["...marcusNormalImplication", "...epBoundsNoInvertedEquivalence"] := rfl
example : certificateParentKinds ... = [RelationKind.implication, RelationKind.equivalence] := rfl
example : certificateParentPremiseIDs ... = [["barrier.positiveCurvature", "marcus.reverseNotInverted"], ["barrier.positiveCurvature"]] := rfl
example : certificateBridgeIDs ... = [] := rfl
example : certificateDischargeIDs ... = [] := rfl
example : (certificateMediating? ...).map (fun s => s.statementId) = some "PhotoLean.BEP.EPBounds" := rfl
example : certificateCompositionForm? ... = some CompositionForm.implication := rfl
```

No `combinator`, `application`, `childConclusion` or `parentEvidence` field is
present or accepted; the Lean `ConditionalComposition` constructor is
authoritative.

## Remaining limitations

* The snapshot is dirty; a clean full-registry run is still outstanding.
* The pilot does not claim 136-pair coverage (`registryCoverage = 6/136`).
* `nonvacuous`, `nonredundant`, `weakest`, bridge and discharge typed
  evidence checks are not implemented. Those claims are rejected fail-closed
  (`badge.*Unsupported`, `composition.bridgeUnsupported`,
  `composition.dischargeUnsupported`); the pilot leaves every badge unclaimed.
* `certificateMediating?` is pinned through its `statementId` projection; the
  remaining `StatementRef` fields are Lean-side metadata.
* Independent verification remains outstanding.

## R2 migration inventory

The R2 artifacts are separate from the pilot acceptance evidence. They inventory
all 78 `PhotoLean/Relations.lean` declarations and all 136 unordered theory
pairs, assign each declaration exactly one migration disposition, and keep the
legacy `edge` / `absence` labels namespaced as non-audit metadata. They do not
create a production registry and they make no resolved-coverage claim.

```bash
# derive both inventories and the report from tools/counts.py
python3 tools/relation_audit_inventory.py --generate

# fail closed on scanner drift, stale artifacts, or an incomplete ledger
python3 tools/relation_audit_inventory.py --check
```

| file | contents |
|---|---|
| `relation_audit/dispositions.json` | authored 78-entry migration ledger (disposition, role, pair association, rationale, provenance) |
| `relation_audit/dispositions.schema.json` | structural contract for the ledger |
| `relation_audit/generated/relations_inventory.json` | 78 declarations in 17 sections with stable IDs and source locators |
| `relation_audit/generated/pair_inventory.json` | 136 pairs with legacy edge/absence metadata and migration candidates |
| `relation_audit/reports/inventory-report.json` | machine-readable counts, dispositions, exceptional classifications, non-claims |
| `relation_audit/reports/inventory-report.md` | human-readable summary of the same report |

The inventory check is not an audit gate. A green `--check` means the artifacts
are consistent with `tools/counts.py` and the ledger covers every scanned
declaration exactly once; it does not certify any relation.

## R3 migration fragments

The R3 section workers authored three disjoint Lean fragments and three JSON
fragments. The integration checker treats the JSON fragments as the single
source of truth: every generated Lean command is derived from them, and there
is no second certificate list.

```bash
# fail closed on missing/duplicate/unknown queue IDs, missing certificates,
# stale source hashes, malformed reclassification evidence, or artifact drift
python3 tools/relation_audit_migration.py --check

# regenerate the report and generated Lean checks after an intended change
python3 tools/relation_audit_migration.py --generate

# additionally build PhotoLean.RelationAudit.Full, elaborate the generated
# checks, and compare every #print axioms footprint with the fragments
python3 tools/relation_audit_migration.py --check --lean
```

| file | contents |
|---|---|
| `relation_audit/reports/migration-report.json` | machine-readable integration report: 41-ID queue coverage, 27 certified / 14 reclassified counts, every certificate and reclassification row, generated-check metadata, non-claims |
| `relation_audit/reports/migration-report.md` | human-readable summary of the same report |
| `relation_audit/reports/migration-lean-checks.lean` | generated Lean checks: kind pins, premise-ID pins, `#print axioms` probes, definitional witnesses, reclassification evidence, and composition projections when a fragment row uses `conditionalComposition` |

The report and generated file are integration evidence for the R3 fragments,
not a production registry. They do not claim 136/136 or resolved coverage; in
this round all 41 queue rows are accounted for as 27 certified and 14
reclassified, and no `conditionalComposition` certificate exists.

## R4 production full registry

The R4 generator derives `relation_audit/registry.json` from the accepted R1
pilot, R2 inventory/dispositions, and R3 fragments. It has no second
certificate list: every certificate row is read from `pilot.json` or a
`sections*.json` fragment, and every pair record is derived from the pair
inventory plus the accepted certificate/fragment mapping.

```bash
# derive the production registry, generation report and markdown summary
python3 tools/relation_audit_registry.py --generate

# fail on stale input hashes, missing/hand-added certificates, invalid pair
# associations, coverage changes, or non-byte-identical regeneration
python3 tools/relation_audit_registry.py --check

# print the accepted inputs and registry decision for one pair
python3 tools/relation_audit_registry.py --explain-pair P-Marcus-Hammond

# the real fail-closed validator; Lean must run (a skip is exit 2, never PASS)
python3 tools/relation_audit.py --manifest relation_audit/registry.json \
    --schema relation_audit/schema.json --mode full \
    --json-out relation_audit/reports/production-full.json \
    --lean-source-out relation_audit/reports/production-full-lean-checks.lean
```

| file | contents |
|---|---|
| `relation_audit/registry.json` | production full manifest: 136/136 pairs covered, 24 certified / 6 unresolved / 121 notEstablished records, 38 certificates |
| `relation_audit/reports/registry-report.json` | deterministic mapping report: input hash pins, certificate mapping, pair decisions, exceptional decisions, non-claims |
| `relation_audit/reports/registry-report.md` | human-readable summary of the generation report |
| `relation_audit/reports/production-full.json` | real full-validator report (all gates PASS, zero skips, Lean enabled) |
| `relation_audit/reports/production-full.md` | human-readable summary of the full-validator report |
| `relation_audit/reports/production-full-lean-checks.lean` | generated Lean checks archived from the full run |

Registry coverage is not resolved coverage: 136/136 pairs have an audit record,
but only 9/136 pairs have an accepted certificate and six undelivered candidates
remain unresolved. The snapshot is dirty by construction, so the full-mode
result carries the documented `snapshotDirty` caveat and requires independent
review.
