# Relation-audit fixtures

These fixtures let the validator and its tests run before the production
`relation_audit/schema.json` and `relation_audit/pilot.json` land.  They are
test data, not the contract and not the pilot.

## Files

| path | purpose |
|---|---|
| `schema.json` | fixture copy of the v1.2.0 manifest schema; the production schema stays at `relation_audit/schema.json` |
| `manifest_pilot.json` | valid pilot: all seven certified kinds plus `unresolved`, `notEstablished` and `outOfScope`; carries `mode` and `pairCount: 136`. Its composition record names two parent IDs and one mediator and uses the contract-permitted empty bridge list; the mock Lean module exposes the canonical projections that the validator pins |
| `manifest_full.json` | valid full registry: 136 unordered theory pairs, one unresolved record per pair |
| `invalid/*.json` | one-defect manifests used by the mutation tests |
| `lean/RelationAuditFixture.lean` | mock certificate module compiled by the test harness |
| `generate.py` | deterministic regenerator for every JSON file above |

## Source snapshot

The fixtures pin `7ad25a5f03a88acc3af03f65149cf2ac102e7dac`
(`relation-genealogy/WORKSPACE.md`).  Artifact hashes are computed with
`git show 7ad25a5:<path>`, so the fixtures remain valid when the working tree
advances.  A shallow clone that lacks this commit cannot run them.

## Regenerating

```bash
python3 tests/relation_audit/fixtures/generate.py
```

The script recomputes the schema hash, the toolchain string and every artifact
hash.  Re-run it after changing `schema.json` or intentionally changing the
pinned snapshot; do not hand-edit the generated JSON.

## Mock Lean module

The fixture certificates live in `RelationAuditFixture`, not in
`PhotoLean/RelationAudit`.  The test harness compiles the module to an `.olean`
under `.lake/tmp/relation-audit-tests/` and passes that directory as
`--lean-root`.  The module mirrors the contract's certificate sum type:

* seven `CertificateKind` constructors;
* a computable `certificateKind` function;
* one certificate value per kind;
* premise signatures with named binders (`hAdj`, `hPos`);
* rfl declarations, including one that legitimately depends on
  `Classical.choice` to exercise the standard allowed-axiom whitelist;
* an `aliasDef` used by the definitional `rflCheck` example;
* canonical projections mirroring the real certificate layer
  (`certificatePremiseIDs`, `certificateParentIDs`, `certificateParentKinds`,
  `certificateParentPremiseIDs`, `certificateBridgeIDs`,
  `certificateDischargeIDs`, `certificateMediating?`,
  `certificateCompositionForm?`) plus a minimal `CompositionForm` and
  `StatementRef`. The production module `PhotoLean.RelationAudit` exposes the
  same shape over the real `ConditionalComposition`; the mock keeps the test
  suite independent of whether that module is built.

The invalid fixture `mislabelled_kind_lean.json` relabels the implication
certificate as `definitionalIdentity` in both the record and the certificate
row.  Only the generated `certificateKind ... = ... := rfl` check rejects it;
no structural check can.

## Invalid fixture map

| fixture | expected failure |
|---|---|
| `mislabelled_kind.json` | `status.certificateMismatch` |
| `mislabelled_kind_lean.json` | `lean.certificateKind` |
| `composition_wrong_parent_order.json` | `lean.compositionParentIDs` |
| `composition_parent_premise_drift.json` | `lean.compositionParentPremiseIDs` |
| `composition_wrong_mediator.json` | `lean.compositionMediating` |
| `missing_premise.json` | `premise.closure` |
| `incomplete_bridge.json` | `composition.bridge` |
| `bridge_unrelated_witness.json` | `composition.bridgeUnsupported` |
| `discharge_unrelated_witness.json` | `composition.dischargeUnsupported` |
| `badge_nonvacuous_unrelated.json` | `badge.nonvacuousUnsupported` |
| `badge_nonredundant_unrelated.json` | `badge.nonredundantUnsupported` |
| `badge_weakest_unrelated.json` | `badge.weakestUnsupported` |
| `stale_snapshot.json` | `snapshot.unknownCommit` |
| `stale_artifact.json` | `snapshot.staleArtifact` |
| `conflicting_statuses.json` | `conflict.statuses` |
| `missing_pair.json` | `coverage.missingPair` |
| `missing_provenance.json` | `provenance.missing` |
| `missing_certificate.json` | `ref.certificate` |
| `adjudication_kind.json` | `kind.adjudication` |
| `missing_dependencies.json` | `status.dependencies` |
| `missing_badge_evidence.json` | `badge.nonvacuousUnsupported` |
| `duplicate_id.json` | `id.duplicate` |
| `unknown_premise.json` | `premise.unknown` |
| `scope_jurisdiction.json` | `scope.jurisdiction` |

There is deliberately no `conflicting_kinds.json`: contract section 7 says
different certified relation kinds are not inherently contradictory.  The
compatible-kinds case is a valid manifest and is exercised in
`test_mutations.py` instead.

## Tests

```bash
python3 tests/relation_audit/run_tests.py
```

The suite compiles the mock module and runs the real Lean toolchain.  If the
toolchain is absent, the Lean-dependent tests are reported as skipped, never as
passed.

One integration test copies `manifest_pilot.json`, replaces the snapshot's
`schemaSha256` with the hash of the production `relation_audit/schema.json`, and
runs the validator against that schema with the mock certificates. The fixture
follows schema v1.2.0, so the test runs the full production-schema path. A
defensive skip remains in case the production schema regresses to requiring a
non-empty `composition.bridges` list (contract section 4 permits an empty list).
If the production schema changes shape, this test is the early warning.

When `PhotoLean.RelationAudit` is built, another test runs the generated
`#check` / `certificateKind ... := rfl` / `#print axioms` checks against the
real delivered pilot certificates (`kernelBarrierPin`, `betaHalfEquivalence`,
...), with no mock module involved.
