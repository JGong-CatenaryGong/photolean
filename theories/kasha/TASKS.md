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
  `4cf2b1055f1aee41463e7f5ad9bb6913c2c82600a0c4aa064cb58210fc68c0fb`), **144 declarations** (104 theorems + 37 definitions + 3 structures/inductives).
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
      144 declarations with placeholder theorem bodies, `lake env lean` exit 0, sha256 `4cf2b1055f1aee41463e7f5ad9bb6913c2c82600a0c4aa064cb58210fc68c0fb`
- [x] **Fidelity-checker coverage gap found and fixed** (lead, 2026-09-20): the theory-generic
      checker `theories/BEP/probes/bep-fidelity.py` matched only `theorem|def|inductive` and
      silently skipped `structure` declarations, so it reported **143** of kasha's 144 declarations.
      The regular expression now includes `structure` (kasha 144/144); the other three theories were
      re-run and report exactly as before (BEP 191/191, hammond 102/102, Marcus 51/51 + 31 aux),
      because none of them declares a top-level `structure`. This is the engine lesson "a checker's
      coverage must itself be verified" — the same family as the `theories/*/` directory sweep that
      caught silently-skipped theories.
- [x] Non-Lean cross-check: `theories/kasha/probes/kasha-instance-check.py` (exact rational
      arithmetic, a second implementation) — every instance row's number, the three threshold forms,
      probability conservation and the two recursions over 193 admissible random ladders, the
      effective two-level reduction over 825 (ladder, tolerance) pairs, the levelwise counterexample
      (`leak fraction = 6/7`), and the Marcus-bridge algebra over 400 parameter sets: **all pass**
      (`exit 0`). Committed before the provers finished, i.e. as pre-registered kernel-independent
      evidence rather than a post-hoc retelling.
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

- [ ] `decay` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `radBranch` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `icBranch` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `cascade` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `emitYield` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `fluoYield` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `upperYield` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `specFrac` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `kashaMargin` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `funnelRatio` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `ladderRatio` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `KashaRule` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `KashaWithin` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `VavilovAt` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `VavilovUpTo` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `KashaDescriptor` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `RateData` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `KashaZone` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `kashaZone` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `decay_eq_rad_add_ic` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `radBranch_add_icBranch` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `radBranch_nonneg` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `icBranch_nonneg` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `radBranch_le_one` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `icBranch_le_one` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `cascade_self` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `cascade_nonneg` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `cascade_le_one` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `emitYield_self` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `emitYield_nonneg` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `emitYield_le_radBranch` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `fluoYield_eq_low_add_upper` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `fluoYield_zero` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `upperYield_zero` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `fluoYield_nonneg` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `upperYield_nonneg` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `upperYield_le_fluoYield` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `kashaRule_iff_upperYield_zero` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `specFrac_sum` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `kashaWithin_iff_specFrac` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `kashaZone_eq_pure_iff` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `kashaZone_eq_withinTol_iff` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `kashaZone_eq_violating_iff` — Basic.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `kashaRule_of_rad_zero` — Basic.lean — prover_a — todo — skeleton `4cf2b105`

### K2 — `PhotoLean/Kasha/Criterion.lean` (owner prover_a)

- [ ] `cascade_succ` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `emitYield_succ` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `emitYield_succ_self` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `fluoYield_succ` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `upperYield_succ` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `cascade_add_upperYield` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `fluoYield_eq_one_sub_loss` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `fluoYield_le_one` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `fluoYield_mono_succ` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `fluoYield_lt_succ_of_rad_pos` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `fluoYield_eq_iff_rad_zero` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `fluoYield_lt_one_iff_loss` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `upperYield_eq_zero_iff` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `kashaRule_iff_rad_zero` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `not_kashaRule_of_rad_pos` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `vavilovAt_iff_rad_zero` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `vavilovUpTo_iff_rad_zero` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `kashaRule_iff_vavilovUpTo` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `not_kasha_universal` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `kashaDescriptor_nonvacuous` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `kashaWithin_of_kashaRule` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`
- [ ] `upperYield_le_sum_radBranch` — Criterion.lean — prover_a — todo — skeleton `4cf2b105`

### K3 — `PhotoLean/Kasha/Sharp.lean` (owner prover_b)

- [ ] `kashaWithin_one_iff_rates` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `kashaWithin_one_iff_ratio` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `kashaWithin_one_iff_ic_ratio` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `funnelRatio_eq_ladderRatio_one` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `kashaWithin_iff_margin` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `kashaWithin_mono_tol` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `kashaWithin_zero_iff` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `kashaWithin_one_mono_ic` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `not_kashaWithin_one_of_ratio_lt` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `kashaThreshold_attained` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `perLevel_criterion_insufficient` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `vavilov_premise_necessary` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `kashaWithin_one_sharp_boundary` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `leak_le_of_radBranch_le` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`
- [ ] `kashaWithin_of_uniform_branch` — Sharp.lean — prover_b — todo — skeleton `4cf2b105`

### K4 — `PhotoLean/Kasha/Compose.lean` (owner prover_d)

- [ ] `effRad` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `effIc` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `marcusIC` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `kashaGapThreshold` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `cascade_compose` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `emitYield_compose` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `effDecay_zero` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `effDecay_one` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `effUpperYield_one` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `effEmitYield_zero_one` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `kashaMargin_effective` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `kashaWithin_iff_effective` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `kashaWithin_iff_ladderRatio` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `ladderRatio_one` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `not_kashaWithin_of_ladderRatio_lt` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `kashaWithin_one_marcus` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `not_kashaWithin_of_gap_far` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `kashaWindow_halfWidth` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `kashaGapThreshold_pos` — Compose.lean — prover_d — todo — skeleton `4cf2b105`
- [ ] `marcusIC_pos` — Compose.lean — prover_d — todo — skeleton `4cf2b105`

### K5a — `PhotoLean/Kasha/RatModel.lean` (owner prover_c)

- [ ] `decayQ` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `radBranchQ` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `icBranchQ` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `cascadeQ` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `emitYieldQ` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `fluoYieldQ` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `upperYieldQ` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `funnelRatioQ` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `ladderRatioQ` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `KashaWithinQ` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `QRateData` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `KashaQVerdict` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `kashaQVerdict` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `twoRad` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `twoIc` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `threeRad` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `threeIc` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `decayQ_cast` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `radBranchQ_cast` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `icBranchQ_cast` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `cascadeQ_cast` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `emitYieldQ_cast` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `fluoYieldQ_cast` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `upperYieldQ_cast` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `kashaWithinQ_iff_cast` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `kashaWithinQ_iff_funnelRatioQ` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `kashaQVerdict_eq_pure_iff` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `kashaQVerdict_eq_withinTol_iff` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `kashaQVerdict_eq_violating_iff` — RatModel.lean — prover_c — todo — skeleton `4cf2b105`

### K5b — `PhotoLean/Kasha/Instances.lean` (owner prover_c)

- [ ] `I1_conforming_control` — Instances.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `I2_antiKasha_control` — Instances.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `I3_threshold_boundary` — Instances.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `I3b_threshold_below` — Instances.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `I4_fluoYield_one` — Instances.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `I5_upperYield_one` — Instances.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `I6_fluoYield_two` — Instances.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `I7_equalRates_leak_two` — Instances.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `I7b_equalRates_violating` — Instances.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `I8_noLoss_vavilov` — Instances.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `I8b_noLoss_not_kasha` — Instances.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `I9_verdict_violating` — Instances.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `I13_row_inventory` — Instances.lean — prover_c — todo — skeleton `4cf2b105`
- [ ] `I14_not_one_sided` — Instances.lean — prover_c — todo — skeleton `4cf2b105`

---

## Acceptance records

<!-- One block per verifier run: date, frozen tree hash, milestone batch, verdict, evidence, and the
     findings verbatim. A verdict is recorded here only from an audit report that already exists. -->

_None yet._
