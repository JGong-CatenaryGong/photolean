# theories/EnergyGapLaw/TASKS.md — PhotoLean task board: EnergyGapLaw (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/EnergyGapLaw/plan.md`.
- Status of this theory: **Phase 1 (statement formalization) in progress** — batch:
  photophysics subgraph (groups A–D), dispatched 2026-09-22.

## Sprint 0 — environment, statements, plan

- [ ] Statement skeleton `theories/EnergyGapLaw/probes/EnergyGapLaw-statement-skeleton.lean` compiles at 0 errors
      (`proofs/scripts/lake env lean`) — placeholder theorem bodies on purpose
- [ ] Plan landed: `theories/EnergyGapLaw/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates)
- [ ] Literature leaf: `theories/EnergyGapLaw/LITERATURE.md` (sources with formalizable implications)

### Sprint-0 declaration board (26 declarations: 9 definitions incl. 1 inductive, 17 theorems)

- Skeleton: `theories/EnergyGapLaw/probes/EnergyGapLaw-statement-skeleton.lean`,
  sha256 `2294c38f6040337ba9ef172b00ce6ffa7a78f1f36547234778690871b1480a64`
  (measured after the last edit; every row below is a declaration of this exact file).
- Compile command (gate: exit 0, exactly 17 `declaration uses 'sorry'` warnings, no other output):
  `proofs/scripts/lake env lean theories/EnergyGapLaw/probes/EnergyGapLaw-statement-skeleton.lean`
- API probe: `theories/EnergyGapLaw/probes/EnergyGapLaw-api-probe.lean` (exit 0, no `sorry`),
  sha256 `52e843a4eaa61ef128c4d69fd8553e5b6094bbd428d31f0f2167bec9cf2d1b90`;
  compile: `proofs/scripts/lake env lean theories/EnergyGapLaw/probes/EnergyGapLaw-api-probe.lean`

| # | Plan row | Declaration | Kind | Status |
|---|----------|-------------|------|--------|
| 1 | EG-B1 | `nrBarrier` | def | `stmt` |
| 2 | EG-B1 | `cert_nrBarrier` | theorem | `stmt` |
| 3 | EG-B2 | `nrRate` | def | `stmt` |
| 4 | EG-B2 | `cert_nrRate` | theorem | `stmt` |
| 5 | EG-B3 | `InvertedGap` | def | `stmt` |
| 6 | EG-B3 | `cert_invertedGap` | theorem | `stmt` |
| 7 | EG-B4 | `lnRate` | def | `stmt` |
| 8 | EG-C1 | `lnRate_eq` | theorem | `stmt` |
| 9 | EG-C2 | `lnRate_strictAnti_on_inverted` | theorem | `stmt` |
| 10 | EG-C3 | `lnRate_strictMono_on_normal` | theorem | `stmt` |
| 11 | EG-C4 | `secant_slope_exact` | theorem | `stmt` |
| 12 | EG-C4 (corollary) | `secant_slope_neg_iff` | theorem | `stmt` |
| 13 | EG-S1 | `eglTangent` | def | `stmt` |
| 14 | EG-S2 | `eglTangent_overestimates` | theorem | `stmt` |
| 15 | EG-S2a | `eglTangent_defect` | theorem | `stmt` |
| 16 | EG-S3 | `not_affine_on_window` | theorem | `stmt` |
| 17 | EG-S4 | `eglTangent_slope_strictAnti` | theorem | `stmt` |
| 18 | EG-R1 | `Rat.nrBarrier` | def | `stmt` |
| 19 | EG-R1 (cast row; name assigned in Sprint 0) | `Rat.nrBarrier_cast` | theorem | `stmt` |
| 20 | EG-R2 | `EGZone` | inductive | `stmt` |
| 21 | EG-R2 | `egZoneQ` | def | `stmt` |
| 22 | EG-R2 (correctness row) | `egZoneQ_eq_inverted_iff` | theorem | `stmt` |
| 23 | EG-R3 | `nrRate_decidable_order` | def | `stmt` |
| 24 | EG-I1 | `aromaticSeries` | theorem | `stmt` |
| 25 | EG-I2 | `normalRegionCounter` | theorem | `stmt` |
| 26 | EG-I3 | `tangentWitness` | theorem | `stmt` |
