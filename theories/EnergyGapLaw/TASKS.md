# theories/EnergyGapLaw/TASKS.md — PhotoLean task board: EnergyGapLaw (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/EnergyGapLaw/plan.md`.
- Status of this theory: **Phase 2 (proof layer) delivered** — all 26 Sprint-0 declarations proved,
  every row moved `stmt` -> `review` (verifier adjudication pending, so no box is ticked);
  batch: photophysics subgraph (groups A–D), dispatched 2026-09-22.

### Sprint-0/Phase-2 delivery record (prover_a)

- Delivered modules (owner prover_a; one commit per module, the batch-registered deviation from
  one-commit-per-lemma):
  `PhotoLean/EnergyGapLaw/{Basic,Criterion,Sharp,RatModel,Instances}.lean`.
- Build evidence (exit 0 each): `proofs/scripts/lake build PhotoLean.EnergyGapLaw.<Module>` for
  all five modules; `proofs/scripts/check.sh --strict` with the five modules as targets = PASS
  (scan `clean`), and the whole-tree `proofs/scripts/check.sh --strict` = PASS.
- Axiom evidence: `proofs/scripts/axioms.sh <Module> <qualified name>` = PASS for all **17**
  authority theorems plus the one auxiliary row `lnRate_second_difference` (18/18); every one
  depends on at most `propext, Classical.choice, Quot.sound`.
- Fidelity: `python3 theories/BEP/probes/bep-fidelity.py --theory EnergyGapLaw` reports
  `skeleton declarations 26`, `delivered, word-for-word 26`, `not delivered yet 0`,
  `signature differences 0`; the single "not in authority" entry is the auxiliary row.
- Statement discipline: all 26 signatures are transcribed verbatim from the authority, including
  the three §3.1 corrections (EG-I3 defect magnitude `-5`, EG-S4 without the unconsumable
  `0 < A`, EG-C4 corollary as the iff). No statement was changed and no statement incident arose;
  the `Rat.nrBarrier_cast` row was checked against the SV-R1 shadowing pitfall with a scratch
  `#print` and is a real (non-vacuous) bridge.
- Premise note for the verifier: EG-C4's `secant_slope_neg_iff` carries the authority's premise
  `x₁ ≠ x₂`, which is decorative — the proof does not consume it, and the sign equivalence is
  independent of it (at `x₁ = x₂` both sides are false under `0 < lam`). Kept for signature
  fidelity, with the unused-variable linter disabled locally (the BEP `Sharp.lean` precedent).

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
| 1 | EG-B1 | `nrBarrier` | def | `review` |
| 2 | EG-B1 | `cert_nrBarrier` | theorem | `review` |
| 3 | EG-B2 | `nrRate` | def | `review` |
| 4 | EG-B2 | `cert_nrRate` | theorem | `review` |
| 5 | EG-B3 | `InvertedGap` | def | `review` |
| 6 | EG-B3 | `cert_invertedGap` | theorem | `review` |
| 7 | EG-B4 | `lnRate` | def | `review` |
| 8 | EG-C1 | `lnRate_eq` | theorem | `review` |
| 9 | EG-C2 | `lnRate_strictAnti_on_inverted` | theorem | `review` |
| 10 | EG-C3 | `lnRate_strictMono_on_normal` | theorem | `review` |
| 11 | EG-C4 | `secant_slope_exact` | theorem | `review` |
| 12 | EG-C4 (corollary) | `secant_slope_neg_iff` | theorem | `review` |
| 13 | EG-S1 | `eglTangent` | def | `review` |
| 14 | EG-S2 | `eglTangent_overestimates` | theorem | `review` |
| 15 | EG-S2a | `eglTangent_defect` | theorem | `review` |
| 16 | EG-S3 | `not_affine_on_window` | theorem | `review` |
| 17 | EG-S4 | `eglTangent_slope_strictAnti` | theorem | `review` |
| 18 | EG-R1 | `Rat.nrBarrier` | def | `review` |
| 19 | EG-R1 (cast row; name assigned in Sprint 0) | `Rat.nrBarrier_cast` | theorem | `review` |
| 20 | EG-R2 | `EGZone` | inductive | `review` |
| 21 | EG-R2 | `egZoneQ` | def | `review` |
| 22 | EG-R2 (correctness row) | `egZoneQ_eq_inverted_iff` | theorem | `review` |
| 23 | EG-R3 | `nrRate_decidable_order` | def | `review` |
| 24 | EG-I1 | `aromaticSeries` | theorem | `review` |
| 25 | EG-I2 | `normalRegionCounter` | theorem | `review` |
| 26 | EG-I3 | `tangentWitness` | theorem | `review` |
