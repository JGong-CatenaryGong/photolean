# theories/kasha/TASKS.md — PhotoLean task board: Kasha's rule (single source of truth for status)

- Status vocabulary: `todo` (not started) → `stmt` (statements calibrated and compiling) →
  `proving` (proof in progress) → `review` (handed to the verifier) → `done` (verifier PASS,
  recorded on this board).
- Row format: `- [ ] <declaration> — <file> — <owner> — <status> — <note>`.
- **Ticking (`[x]`) happens only after a verifier PASS and is done by the lead**; workers never
  tick their own rows.
- The owner column holds engine role names (`prover_a`…`prover_d`); one file has at most one
  concurrent owner.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/kasha/plan.md`.
- **Statement authority**: `theories/kasha/probes/kasha-statement-skeleton.lean`
  (compiles at 0 error with `proofs/scripts/lake env lean`, Sprint-0 gate; sha256
  `e3ddc2d01317ec6bc46957cae7763034a23df691bffc480a08c9a23d9fe6412b`), **144 declarations** (104 theorems + 37 definitions + 3 structures/inductives).
- Theory direction: **Kasha's rule in a finite excited-state cascade model**, human request of
  2026-09-20 (three parts: formal description / proof and validity conditions / instance verdicts).
- Deliverable module prefix: `PhotoLean.Kasha`; sources under `PhotoLean/Kasha/`
  (`SOURCE_DIRS` is global and covers them — `theories/kasha/` is outside the strict scan range).
- Status of this theory: **Sprint 0 closed, Sprint 1 open** — skeleton compiled, plan landed,
  literature round 1 and API calibration running; K1 (the critical path) dispatched.
- Literature rows I10–I12 are **not yet in the skeleton**: their Lean literals must be transcribed
  from `theories/kasha/LITERATURE.md` (never guessed) and the append is recorded in
  `proofs/API-NOTES.md`.

---

## Sprint 0 — environment, statements, plan (closed except the probes)

- [x] Theory directory `theories/kasha/` created; contract extended with the multi-theory data
      plane (`THEORIES="Marcus hammond BEP kasha"` + `PLAN_kasha` / `TASKS_kasha` /
      `LITERATURE_kasha` / `PROBES_kasha` / `RESULT_kasha`) — additive; the other theories' leaves
      and the gate behaviour are unchanged
- [x] Plan landed: `theories/kasha/plan.md` (K1–K5, statement inventory, sprint order, risk
      register, honesty table, scope limits)
- [x] **Statement skeleton compiles**: `theories/kasha/probes/kasha-statement-skeleton.lean` —
      144 declarations with placeholder theorem bodies, `lake env lean` exit 0, sha256 `e3ddc2d01317ec6bc46957cae7763034a23df691bffc480a08c9a23d9fe6412b`
- [ ] API calibration: `proofs/API-NOTES.md` §kasha + `theories/kasha/probes/kasha-api-*.lean` —
      owner `api_researcher` (dispatched)
- [ ] Sprint-0 risk probe: `theories/kasha/probes/kasha-risk-probe.lean` — the riskiest statement
      forms proved verbatim before their milestones are dispatched — owner `prover_b` (dispatched)
- [ ] Literature round 1: `theories/kasha/LITERATURE.md` §R1 — owner `literature_researcher`
      (dispatched)
- [ ] Human confirmation of the plan

---

## Board rows (one row per declaration of the statement authority)

### K1 — `PhotoLean/Kasha/Basic.lean` (owner prover_a)

- [ ] `decay` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `radBranch` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `icBranch` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `cascade` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `emitYield` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `fluoYield` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `upperYield` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `specFrac` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `kashaMargin` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `funnelRatio` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `ladderRatio` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `KashaRule` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `KashaWithin` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `VavilovAt` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `VavilovUpTo` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `KashaDescriptor` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `RateData` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `KashaZone` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `kashaZone` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `decay_eq_rad_add_ic` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `radBranch_add_icBranch` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `radBranch_nonneg` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `icBranch_nonneg` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `radBranch_le_one` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `icBranch_le_one` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `cascade_self` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `cascade_nonneg` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `cascade_le_one` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `emitYield_self` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `emitYield_nonneg` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `emitYield_le_radBranch` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `fluoYield_eq_low_add_upper` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `fluoYield_zero` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `upperYield_zero` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `fluoYield_nonneg` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `upperYield_nonneg` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `upperYield_le_fluoYield` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `kashaRule_iff_upperYield_zero` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `specFrac_sum` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithin_iff_specFrac` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `kashaZone_eq_pure_iff` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `kashaZone_eq_withinTol_iff` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `kashaZone_eq_violating_iff` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `kashaRule_of_rad_zero` — Basic.lean — prover_a — todo — skeleton `e3ddc2d0`

### K2 — `PhotoLean/Kasha/Criterion.lean` (owner prover_a)

- [ ] `cascade_succ` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `emitYield_succ` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `emitYield_succ_self` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `fluoYield_succ` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `upperYield_succ` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `cascade_add_upperYield` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `fluoYield_eq_one_sub_loss` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `fluoYield_le_one` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `fluoYield_mono_succ` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `fluoYield_lt_succ_of_rad_pos` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `fluoYield_eq_iff_rad_zero` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `fluoYield_lt_one_iff_loss` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `upperYield_eq_zero_iff` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `kashaRule_iff_rad_zero` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `not_kashaRule_of_rad_pos` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `vavilovAt_iff_rad_zero` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `vavilovUpTo_iff_rad_zero` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `kashaRule_iff_vavilovUpTo` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `not_kasha_universal` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `kashaDescriptor_nonvacuous` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithin_of_kashaRule` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`
- [ ] `upperYield_le_sum_radBranch` — Criterion.lean — prover_a — todo — skeleton `e3ddc2d0`

### K3 — `PhotoLean/Kasha/Sharp.lean` (owner prover_b)

- [ ] `kashaWithin_one_iff_rates` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithin_one_iff_ratio` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithin_one_iff_ic_ratio` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `funnelRatio_eq_ladderRatio_one` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithin_iff_margin` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithin_mono_tol` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithin_zero_iff` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithin_one_mono_ic` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `not_kashaWithin_one_of_ratio_lt` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `kashaThreshold_attained` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `perLevel_criterion_insufficient` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `vavilov_premise_necessary` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithin_one_sharp_boundary` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `leak_le_of_radBranch_le` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithin_of_uniform_branch` — Sharp.lean — prover_b — todo — skeleton `e3ddc2d0`

### K4 — `PhotoLean/Kasha/Compose.lean` (owner prover_d)

- [ ] `effRad` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `effIc` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `marcusIC` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `kashaGapThreshold` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `cascade_compose` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `emitYield_compose` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `effDecay_zero` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `effDecay_one` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `effUpperYield_one` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `effEmitYield_zero_one` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `kashaMargin_effective` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithin_iff_effective` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithin_iff_ladderRatio` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `ladderRatio_one` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `not_kashaWithin_of_ladderRatio_lt` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithin_one_marcus` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `not_kashaWithin_of_gap_far` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `kashaWindow_halfWidth` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `kashaGapThreshold_pos` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`
- [ ] `marcusIC_pos` — Compose.lean — prover_d — todo — skeleton `e3ddc2d0`

### K5a — `PhotoLean/Kasha/RatModel.lean` (owner prover_c)

- [ ] `decayQ` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `radBranchQ` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `icBranchQ` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `cascadeQ` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `emitYieldQ` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `fluoYieldQ` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `upperYieldQ` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `funnelRatioQ` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `ladderRatioQ` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `KashaWithinQ` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `QRateData` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `KashaQVerdict` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `kashaQVerdict` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `twoRad` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `twoIc` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `threeRad` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `threeIc` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `decayQ_cast` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `radBranchQ_cast` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `icBranchQ_cast` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `cascadeQ_cast` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `emitYieldQ_cast` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `fluoYieldQ_cast` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `upperYieldQ_cast` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithinQ_iff_cast` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `kashaWithinQ_iff_funnelRatioQ` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `kashaQVerdict_eq_pure_iff` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `kashaQVerdict_eq_withinTol_iff` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `kashaQVerdict_eq_violating_iff` — RatModel.lean — prover_c — todo — skeleton `e3ddc2d0`

### K5b — `PhotoLean/Kasha/Instances.lean` (owner prover_c)

- [ ] `I1_conforming_control` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `I2_antiKasha_control` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `I3_threshold_boundary` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `I3b_threshold_below` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `I4_fluoYield_one` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `I5_upperYield_one` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `I6_fluoYield_two` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `I7_equalRates_leak_two` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `I7b_equalRates_violating` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `I8_noLoss_vavilov` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `I8b_noLoss_not_kasha` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `I9_verdict_violating` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `I13_row_inventory` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`
- [ ] `I14_not_one_sided` — Instances.lean — prover_c — todo — skeleton `e3ddc2d0`

---

## Acceptance records

<!-- One block per verifier run: date, frozen tree hash, milestone batch, verdict, evidence, and the
     findings verbatim. A verdict is recorded here only from an audit report that already exists. -->

_None yet._
