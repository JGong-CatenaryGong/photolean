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
  `8c5ed93b14d96c2d08e4c6e59da587972841373d65d3d2db4f7d85dea9232853` since the 2026-09-21
  review-fix round), **151 declarations** (111 theorems + 37 definitions + 3 structures/inductives).
  Acceptance runs 1–9 below were gated against the pre-revision authority
  `b645cbfbf61ecf08a7c5dbe3a5e5f8f8874e50cbc806e994ea53823dbf63aa17` (150 declarations); the two
  revised rows (plan §3.1, external-review findings M1/M3) were independently verified **PASS**
  (2026-09-21, recorded in `theories/SymmetryFactor/TASKS.md` run 1 batch C) and are ticked.
- Theory direction: **Kasha's rule in a finite excited-state cascade model**, human request of
  2026-09-20 (three parts: formal description / proof and validity conditions / instance verdicts).
- Deliverable module prefix: `PhotoLean.Kasha`; sources under `PhotoLean/Kasha/`
  (`SOURCE_DIRS` is global and covers them — `theories/kasha/` is outside the strict scan range).
- Status of this theory: **delivered and verified** (runs 1–9, against the pre-revision authority
  `b645cbfb…`, 150 declarations) — six modules, every delivery-phase row on
  this board ticked; the verifier's runs are recorded below (three for the mathematics — K1+probes,
  K2/K4/K5a, K3/K5b+whole tree — followed by the documentation re-audits). **2026-09-21 review-fix
  round** (external review `review/FULL-REVIEW-2026-09-21.md`, findings M1/M3, plan §3.1): one
  statement strengthened (`kashaDescriptor_nonvacuous` — the delivered form was trivially true of
  every ladder), one row added (`perLevel_ic_ge_rad_insufficient` — the literal per-level reading);
  the authority is revised to
  `8c5ed93b14d96c2d08e4c6e59da587972841373d65d3d2db4f7d85dea9232853` (151 declarations); both rows
  were author-gated and have now been **independently verified PASS** (verdict: SymmetryFactor run 1,
  batch C — the trivial universal behind M1 was positively refuted in-probe, and M3's literal
  condition confirmed); the two board rows are ticked on that verdict and the theory is re-closed.
- Literature rows: **in the skeleton** (I10, I11, I11-alt, I11-alt2, I11t, I15 — appended 2026-09-20,
  literals transcribed from `theories/kasha/LITERATURE.md` §R1.6, never guessed); sketched row I12 is
  **absent by decision** (the literature round found no second anti-Kasha molecule with first-hand
  numbers, §R1.6).

---

## Sprint 0 — environment, statements, plan (closed except the probes)

- [x] Theory directory `theories/kasha/` created; contract extended with the multi-theory data
      plane (`THEORIES="Marcus hammond BEP kasha"` + `PLAN_kasha` / `TASKS_kasha` /
      `LITERATURE_kasha` / `PROBES_kasha` / `RESULT_kasha`) — additive; the other theories' leaves
      and the gate behaviour are unchanged
- [x] Plan landed: `theories/kasha/plan.md` (K1–K5, statement inventory, sprint order, risk
      register, honesty table, scope limits)
- [x] **Statement skeleton compiles** (the Sprint-0 gate): `theories/kasha/probes/kasha-statement-skeleton.lean`
      — **144 declarations** with placeholder theorem bodies, `lake env lean` exit 0, sha256
      `e3ddc2d01317ec6bc46957cae7763034a23df691bffc480a08c9a23d9fe6412b` **at that gate**. The authority
      then grew, and the hash history is part of the record (verifier finding MEDIUM-5 was that this
      row had been rewritten to a later hash, which would have made no hash identify the Sprint-0
      artifact): `4cf2b105…` — the three statement corrections of §3.1; `8508e1df…` — the six K5b
      literature rows appended (whose raw line count read 151 because a docstring line happened to
      begin with a declaration keyword); `b645cbfb…` — that line reflowed, **150 declarations**
      measured comment-stripped (110 theorems + 37 definitions + 3 structures/inductives), which is
      the state this board's header names
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
- [x] API calibration: `proofs/API-NOTES.md` §kasha + `theories/kasha/probes/kasha-api-*.lean` —
      owner `api_researcher` — **done and verified**: the five probes are tracked (`8d96538`) and
      compile with 0 diagnostics; the recipes were used verbatim by K1/K2/K4/K5a with zero rework;
      the refuted two-warning claim and the stale hash citations were corrected in the log, and the
      exponential-race item is closed as a declared modelling premise (plan §13)
- [x] Sprint-0 risk probe: `theories/kasha/probes/kasha-risk-probe.lean` — owner `prover_b` —
      **done and verified** (verifier batch B: 11/12 rows PASS, the twelfth kernel-refuted, all
      probe files compile output-clean, 33 theorems with the single allowed footprint)
- [x] Literature round 1: `theories/kasha/LITERATURE.md` §R1 (§R1.0–§R1.9, 787 lines, commit
      `7fc2efd`) — owner `literature_researcher`; the round's three binding consequences are folded
      into plan §1.1 (scope qualifiers; `tol` is a model choice, not a literature number; rates are
      measurements identified with model scalars) and §13 (the attribution requirement for the Marcus bridge — plan §7.2 item K4c — the ban on
      a global gap-monotonicity claim)
- [x] Human confirmation of the plan (2026-09-20: layout + K1–K5 approved; the three-part request
      mapped to §2/§3/§4 of `RESULTS.md`)
- **Registered deviation (commit granularity)**: one commit per lemma holds literally for K1 (28
  `feat` commits), K2 (22), K3 (15) and K4 (20); K5a (29 declarations, 4 `feat` commits) and K5b (20
  rows, 3 `feat` commits touching `Instances.lean`, plus one authority-append commit touching no
  source file) batch their declarations into `feat(K5a|K5b)` commits.
  Recorded here because plan §11 states the rule without qualification, and because the closing audit
  found the delivered tree contradicting the unqualified sentence.

---

## Board rows (one row per declaration of the statement authority)

### K1 — `PhotoLean/Kasha/Basic.lean` (owner prover_a)

- [x] `decay` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `radBranch` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `icBranch` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `cascade` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `emitYield` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `fluoYield` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `upperYield` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `specFrac` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `kashaMargin` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `funnelRatio` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `ladderRatio` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `KashaRule` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `KashaWithin` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `VavilovAt` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `VavilovUpTo` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `KashaDescriptor` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `RateData` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `KashaZone` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `kashaZone` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `decay_eq_rad_add_ic` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `radBranch_add_icBranch` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `radBranch_nonneg` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `icBranch_nonneg` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `radBranch_le_one` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `icBranch_le_one` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `cascade_self` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `cascade_nonneg` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `cascade_le_one` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `emitYield_self` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `emitYield_nonneg` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `emitYield_le_radBranch` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `fluoYield_eq_low_add_upper` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `fluoYield_zero` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `upperYield_zero` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `fluoYield_nonneg` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `upperYield_nonneg` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `upperYield_le_fluoYield` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `kashaRule_iff_upperYield_zero` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `specFrac_sum` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `kashaWithin_iff_specFrac` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `kashaZone_eq_pure_iff` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `kashaZone_eq_withinTol_iff` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `kashaZone_eq_violating_iff` — Basic.lean — prover_a — done — skeleton `b645cbfb`
- [x] `kashaRule_of_rad_zero` — Basic.lean — prover_a — done — skeleton `b645cbfb`

### K2 — `PhotoLean/Kasha/Criterion.lean` (owner prover_a)

- [x] `cascade_succ` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `emitYield_succ` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `emitYield_succ_self` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `fluoYield_succ` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `upperYield_succ` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `cascade_add_upperYield` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `fluoYield_eq_one_sub_loss` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `fluoYield_le_one` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `fluoYield_mono_succ` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `fluoYield_lt_succ_of_rad_pos` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `fluoYield_eq_iff_rad_zero` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `fluoYield_lt_one_iff_loss` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `upperYield_eq_zero_iff` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `kashaRule_iff_rad_zero` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `not_kashaRule_of_rad_pos` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `vavilovAt_iff_rad_zero` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `vavilovUpTo_iff_rad_zero` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `kashaRule_iff_vavilovUpTo` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `not_kasha_universal` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `kashaDescriptor_nonvacuous` — Criterion.lean — prover_a — done — skeleton `b645cbfb` (original statement `∃ rad ic, KashaDescriptor rad ic`, verified in the delivery runs)
- [x] `kashaDescriptor_nonvacuous` (**strengthened statement** `∃ rad ic, RateData rad ic 1 ∧ KashaRule rad ic 1`) — Criterion.lean — review-fix — done — 2026-09-21 plan §3.1 / review M1: the original form was trivially true of every ladder (`KashaRule · · 0` via `upperYield_zero`); author-gated (build OK, strict `clean`, `axioms.sh` `[propext, Classical.choice, Quot.sound]`, fidelity 151/151); **verifier re-check PASS 2026-09-21** (SymmetryFactor run 1 batch C: the trivial universal was positively refuted in-probe; delivered type confirmed strengthened)
- [x] `kashaWithin_of_kashaRule` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
- [x] `upperYield_le_sum_radBranch` — Criterion.lean — prover_a — done — skeleton `b645cbfb`

### K3 — `PhotoLean/Kasha/Sharp.lean` (owner prover_b)

- [x] `kashaWithin_one_iff_rates` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `kashaWithin_one_iff_ratio` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `kashaWithin_one_iff_ic_ratio` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `funnelRatio_eq_ladderRatio_one` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `kashaWithin_iff_margin` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `kashaWithin_mono_tol` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `kashaWithin_zero_iff` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `kashaWithin_one_mono_ic` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `not_kashaWithin_one_of_ratio_lt` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `kashaThreshold_attained` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `perLevel_criterion_insufficient` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `perLevel_ic_ge_rad_insufficient` — Sharp.lean — review-fix — done — added 2026-09-21 (plan §6.2 #13b, §3.1 / review M3): the *literal* per-level reading `rad i ≤ ic i`, which #13's branch-weighted hybrid does not formalize; same witness `rad ≡ ic ≡ 1`; author-gated (build OK, strict `clean`, `axioms.sh` clean, fidelity 151/151, milestone K3 16/16); **verifier re-check PASS 2026-09-21** (SymmetryFactor run 1 batch C: the trivial universal was positively refuted in-probe; delivered type confirmed strengthened)
- [x] `vavilov_premise_necessary` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `kashaWithin_one_sharp_boundary` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `leak_le_of_radBranch_le` — Sharp.lean — prover_b — done — skeleton `b645cbfb`
- [x] `kashaWithin_of_uniform_branch` — Sharp.lean — prover_b — done — skeleton `b645cbfb`

### K4 — `PhotoLean/Kasha/Compose.lean` (owner prover_d)

- [x] `effRad` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `effIc` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `marcusIC` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `kashaGapThreshold` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `cascade_compose` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `emitYield_compose` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `effDecay_zero` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `effDecay_one` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `effUpperYield_one` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `effEmitYield_zero_one` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `kashaMargin_effective` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `kashaWithin_iff_effective` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `kashaWithin_iff_ladderRatio` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `ladderRatio_one` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `not_kashaWithin_of_ladderRatio_lt` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `kashaWithin_one_marcus` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `not_kashaWithin_of_gap_far` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `kashaWindow_halfWidth` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `kashaGapThreshold_pos` — Compose.lean — prover_d — done — skeleton `b645cbfb`
- [x] `marcusIC_pos` — Compose.lean — prover_d — done — skeleton `b645cbfb`

### K5a — `PhotoLean/Kasha/RatModel.lean` (owner prover_c)

- [x] `decayQ` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `radBranchQ` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `icBranchQ` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `cascadeQ` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `emitYieldQ` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `fluoYieldQ` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `upperYieldQ` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `funnelRatioQ` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `ladderRatioQ` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `KashaWithinQ` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `QRateData` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `KashaQVerdict` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `kashaQVerdict` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `twoRad` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `twoIc` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `threeRad` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `threeIc` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `decayQ_cast` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `radBranchQ_cast` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `icBranchQ_cast` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `cascadeQ_cast` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `emitYieldQ_cast` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `fluoYieldQ_cast` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `upperYieldQ_cast` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `kashaWithinQ_iff_cast` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `kashaWithinQ_iff_funnelRatioQ` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `kashaQVerdict_eq_pure_iff` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `kashaQVerdict_eq_withinTol_iff` — RatModel.lean — prover_c — done — skeleton `b645cbfb`
- [x] `kashaQVerdict_eq_violating_iff` — RatModel.lean — prover_c — done — skeleton `b645cbfb`

### K5b — `PhotoLean/Kasha/Instances.lean` (owner prover_c)

- [x] `I1_conforming_control` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I2_antiKasha_control` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I3_threshold_boundary` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I3b_threshold_below` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I4_fluoYield_one` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I5_upperYield_one` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I6_fluoYield_two` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I7_equalRates_leak_two` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I7b_equalRates_violating` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I8_noLoss_vavilov` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I8b_noLoss_not_kasha` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I9_verdict_violating` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I13_row_inventory` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I14_not_one_sided` — Instances.lean — prover_c — done — skeleton `b645cbfb`
- [x] `I10_trimethylazulene_conforming` — Instances.lean — prover_c — done — literature row (thesis 1995 Table 3.3, `rad 1 = 33`, `ic 1 = 67000` in 10⁶ s⁻¹; LITERATURE §R1.6)
- [x] `I11_azulene_violating` — Instances.lean — prover_c — done — literature row (thesis 1995 Table 3.1, `35` / `720`; LITERATURE §R1.6)
- [x] `I11alt_azulene2026_violating` — Instances.lean — prover_c — done — literature row (Chem. Sci. 2026, printed `Φ_Fl = 2.42 %` ⇒ `242` / `9758`; LITERATURE §R1.4/§R1.6)
- [x] `I11alt2_azulene2020_violating` — Instances.lean — prover_c — done — literature row (Veys & Escudero JPCA 124, 7228 (2020) Table 2, `2.3×10⁷` / `5.3×10⁸` s⁻¹ ⇒ `23` / `530`)
- [x] `I11t_azulene_tolerance_dependence` — Instances.lean — prover_c — done — literature row, two tolerances on the same data (`¬ 1/100`, `1/10`)
- [x] `I15_familyContrast` — Instances.lean — prover_c — done — literature summary (I10 vs I11 at one tolerance)

---

## Acceptance records

<!-- One block per verifier run: date, frozen tree hash, milestone batch, verdict, evidence, and the
     findings verbatim. A verdict is recorded here only from an audit report that already exists. -->

### Run 1 — 2026-09-20 — K1 batch + Sprint-0 probe batch — verdict **PASS on the mathematics, with evidence-chain findings**

Verifier: independent read-only role (engine role `verifier`), report reproduced in the session log;
the tree was **not frozen** during this run (`HEAD` moved 5×: `0b87f93 → 849b0cf → a5942c6 →
58cf9a8 → 3c54536`), so this is a *snapshot* PASS, and a frozen-state re-run is required at closeout.

| batch | item | verdict | evidence |
|---|---|---|---|
| A | `PhotoLean.Kasha.Basic` (K1) | **PASS** | build OK; `check.sh --strict` `clean`/`PASS`; **25/25** theorems `axioms.sh` clean, one distinct footprint `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; K1 fidelity **44/44, 0 signature differences** (scoped recount) |
| A | the one corrected row | **PASS** | the counterexample file refutes *literally* the pre-correction signature; the witness satisfies `RateData`; the corrected row adds exactly `0 < tol` |
| B | 9 probe files | **PASS** | all `lake env lean` exit 0, **0 warnings repo-wide**; risk probe 33 theorems, one footprint, 14 re-verified by name; both negative results (ℝ and ℚ) target the pre-correction authorities exactly; `kasha-instance-check.py` exit 0 (193 ladders / 825 pairs / 400 parameter sets) |
| C | independent kernel re-derivation | **PASS** | the verifier re-derived `upperYield = 3/4`, `fluoYield = 7/8`, leak `6/7 > 1/2`, and the levelwise-satisfied-yet-violating row *in its own probe*, not by trusting the file |
| D | commit discipline | **PASS with deviations** | 30 commits on `Basic.lean` = 28 `feat(K1): <name>` + 2 `docs(K1)`, each touching exactly **one** file; no `git add -A` swallow; board rows unticked by the workers |

**Findings of run 1 and their disposition**

| # | sev | finding | disposition |
|---|---|---|---|
| 1 | HIGH | the tree was not frozen during the run, so no *stable* verdict exists | accepted: a frozen-state re-run of the whole theory is scheduled at closeout (this record says so) |
| 2 | HIGH | the five `api_researcher` probes were untracked (absent from HEAD), so the API log's evidence was unreproducible | fix dispatched to the owner (commit the probes + the log); tracked here until the commit lands |
| 3 | MED | `PhotoLean/Kasha/Basic.lean` and `API-NOTES.md` cite an authority hash that later moved | the log's citation is being rewritten as a *hash history*; the delivered module headers are updated once, at the freeze, to the frozen authority hash (a citation must name the state it was checked against) |
| 4 | MED | `API-NOTES.md` claimed two deprecation warnings in `kasha-api-risk.lean`; measured: **0 warnings** (and `EXPERIENCE.md` already said 0) | accepted — the API log is the single source of truth for calibrated names and must not carry a refuted warning claim; fix dispatched to the owner |
| 5 | MED | `TASKS.md` had rewritten the Sprint-0 gate row's hash to a value that only exists *after* the later corrections | accepted. The hash history is: Sprint-0 gate at `e3ddc2d0…` (144 declarations) → correction round `4cf2b105…` (K1 #24, K3 #2/#9, K5a criterion) → literature rows `b645cbfb…` (**150 declarations**). Quoting the current hash as "the artifact that passed the Sprint-0 gate" is a stale-number defect |
| 6 | MED | the fidelity checker had no milestone granularity, so a milestone's acceptance number was inexpressible | **fixed**: `bep-fidelity.py --milestone <K1…K5b>` scopes the report to the authority's `## <milestone>` block; regression re-run on BEP/hammond/Marcus (unchanged) |
| 7 | LOW | `KashaWithin` is defined for every real `tol`; `kashaMargin` is `0/0`-degenerate exactly on the branch it names | recorded in plan §12 (honesty table): the tolerance premise is explicit in every criterion row, and `kashaMargin` is only consumed under `0 < upperYield` |
| 8 | LOW | the `lakefile.toml` target for a module lands in a separate (lead) commit, while plan §11 says "same commit" | recorded as a **registered deviation**: `lakefile.toml` is lead-owned (workers are forbidden to edit it), so "same commit" is unachievable as written; the rule's purpose — no delivered module outside the build — is enforced by the lead immediately after each module lands |

### Run 2 — 2026-09-20 — K2/K4/K5a batch — verdict **PASS**

Verifier: independent read-only role. The tree again moved during the run (`0fd0a6a → 446cdad`,
23 commits: 16 `feat` + 7 `docs`), so every artifact is pinned by blob hash (`Criterion.lean` `9c7a8c37…`, `Compose.lean`
`b86f63c5…`, `RatModel.lean` `a3dd1856…`, authority `ee5fa48f` = sha256 `b645cbfb…`), and the
verifier additionally **rebuilt the three modules from a `git archive` copy with its own lake**
(defeating stale oleans).

| batch | item | verdict | evidence |
|---|---|---|---|
| A | K2 `Criterion` (22 theorems) | **PASS** | build OK; `--strict` `clean`/`PASS`; **22/22** `axioms.sh` clean; fidelity 22/22, 0 differences; independent `git archive` rebuild success |
| B | K4 `Compose` (4 defs + 16 theorems) | **PASS** | build OK; `--strict` PASS; **16/16** axioms clean; fidelity 20/20; imports only `Basic` + `Marcus.Basic` (no `Sharp`), and `Marcus.Basic` is really used (`barrier`) |
| C | K5a `RatModel` (29 declarations) | **PASS** | build OK; `--strict` PASS; **12/12** axioms clean; fidelity 29/29 |
| — | bare `check.sh --strict` | **PASS** | leaf plane 5/5; build all; scan `clean`; all six `PhotoLean.Kasha.*` targets present in `defaultTargets` |
| — | independent mathematics | **PASS** | 36 kernel-closed `example`s in the verifier's own probe: the effective-reduction equivalence on six self-chosen ladders (`N = 1, 2, 3`, two tolerances), the N-level threshold and `kashaMargin` values, three Marcus parameter settings (including one where no gap can conform), the K5a verdicts and the `6/7` leak fraction |
| — | adversarial positivity sweep (K2/K4/K5a, line by line) | **no latent false statement** | the one suspect row (K2 #18, needing `cascade 0 i > 0` without hypothesising it) was re-derived as true by the verifier via a minimal-index argument |

Findings (all evidence-chain/documentation, disposition): (1) MEDIUM stale authority citations in
module headers → fixed at the freeze (all six now cite `b645cbfb…`); (2) LOW/MED seven plan sketches
disagreeing with the delivered signatures → reconciled in plan §3.1 (the closing audit corrected the
count to eight: seven strengthened, one unneeded premise dropped); (3) LOW the "151 declarations"
figure was stale → corrected to 150 everywhere; (4) LOW K5a's four `feat` commits carry 29
declarations → **registered as a deviation** in the Sprint-0 notes above; (5) LOW no linter
suppression beyond declaration-scoped `unusedVariables` (checked, no defect).

### Run 3 — 2026-09-20 — K3 + K5b + whole-tree acceptance + documentation — verdict **A PASS / B PASS / C FAIL / D PASS with one HIGH finding**

Verifier: same independent role. Frozen state: `HEAD` `0ad8d01` at start, `86aef04` at report time
(one **docs-only** commit in between: `RESULTS.md +10`, `plan.md +1`); `git status --porcelain` empty
at both ends, **no source file was ever dirty**; all artifacts pinned by blob hash (Sharp `2fcfb801`,
Instances `d0371fe8`, authority `ee5fa48f` = `b645cbfb…`, 150 declarations).

| batch | item | verdict | evidence |
|---|---|---|---|
| A | K3 `Sharp` (15) + K5b `Instances` (20) | **PASS** | build OK both; `--strict` `clean`/`PASS` both; **35/35** theorems `axioms.sh` clean, **one** distinct footprint; fidelity 15/15 and 20/20, 0 differences |
| A | independent mathematics | **PASS** | the verifier's own probe (56 `example`s): every K5b row recomputed from `RatModel`, including the four literature verdicts and the two-tolerance row, plus the reduced criterion `KashaWithinQ (twoRad 1 r) (twoIc 0 i) (1/100) 1 ↔ 99 ≤ i/r` proved symbolically; four K3 rows re-derived from the definitions (`kashaWithin_one_iff_rates` re-proved without any delivered lemma, the attainment witness checked at `tol = 1/4`, the `perLevel` witness's `RateData`/levelwise/leak `6/7` all verified) |
| A | adversarial positivity sweep (K3, K5b) | **no latent false statement** | every division guarded by an explicit premise; the two junk-value cases (`funnelRatio_eq_ladderRatio_one` at `rad 1 = 0`, `kashaWithin_one_mono_ic`'s unsatisfiable `tol · rad 0 < 0` branch) are documented in the docstrings/header rather than hidden |
| B | whole-theory frozen acceptance | **PASS** | leaf plane 5/5; bare `check.sh --strict` `verdict: PASS`; `defaultTargets` = every delivered module (29 modules), proven by moving `Instances.olean` away and watching the bare run rebuild it; unscoped fidelity **150/150**, 0 differences |
| C | documentation audit of `RESULTS.md` (both halves), board and plan | **FAIL — 11 findings, all documentation** | see below |
| D | board discipline | **PASS with one HIGH finding** | K1's 44 rows were ticked from a run-1 PASS; the other 106 rows were unticked at audit time (correct — the lead ticks after a PASS); run-1's record reproducible to the commit |

Run 3 findings and their disposition (the audit's own numbering):

| # | sev | finding | disposition |
|---|---|---|---|
| 1 | HIGH | plan and `RESULTS.md` claimed a *run-2 acceptance record on the board*, which did not exist (the board held run 1 only) | **fixed**: this record and the run-2 record above are now on the board; the claim is no longer false |
| 2 | MED | `RESULTS.md` line count stale (2,354 → measured **2,358**) | fixed |
| 3 | MED | stale commit count (96 = 92 `feat` + 4 `docs` → measured **97 = 92 `feat` + 5 `docs`**) | fixed, with the K5a/K5b commit-granularity deviation registered |
| 4 | MED | the reconciliation count disagreed with itself and with the diff (`seven`/`six` vs the measured **eight = seven strengthened + one dropped**, six of them K4) | fixed in plan §3.1, `RESULTS.md` and the `Compose.lean` header |
| 5 | MED | two headline biconditionals were displayed **without their premises**, and the kernel refutes the unpremised form (`rad = (1,0,…)`, `ic ≡ 1`, `N = 1`, `tol = 1/100` is a witness: tolerance form true, `ladderRatio` degenerate `0`) | fixed: the display now carries the delivered premises, with the witness named |
| 6 | LOW | the azulene conformance boundary was given as `1/21.6 ≈ 4.6 %`; the exact value is `7/151 = 4.6358 %` | fixed |
| 7 | LOW | "three of the four corrections" mis-counted the log (five rows, three distinct defects) | fixed |
| 8 | LOW | the commit-granularity deviation was not registered while `RESULTS.md` asserted "one commit per lemma" unqualified | fixed (deviation registered in the Sprint-0 notes; `RESULTS.md` qualified) |
| 9 | LOW | three plan §6.2 sketch rows have no counterpart in the authority (§3.1 claims row-by-row agreement), plus a `---## 6.` formatting typo | fixed: the three rows are marked as carried by K5b I1/I2 or dropped, and the typo is repaired |
| 10 | LOW | bilingual drift: `RESULTS.md` §5's English half reported runs 1–2 while the Chinese half reported run 1 | fixed |
| 11 | LOW | the API-calibration board row still read "fix dispatched" after the fix landed | fixed (row ticked) |

### Run 4 — 2026-09-20 — documentation re-audit after the run-3 corrections — verdict **C-plane FAIL (7 of 11 fixed, 4 residual + 9 smaller)**

Verifier: same role, focused on the C-plane. Frozen state: `HEAD` `baa5c1e` → `b6ccf1d` (one
docs-only plan commit mid-audit); `git status --porcelain` empty at both ends; source blobs compared
against run 3's pins — **Compose differs in the header comment only** (the `five`→`six` fix), the
comment-stripped code plane is byte-identical (295/295 lines), so no mathematics re-verification was
triggered. Gates re-run on the tree: bare `check.sh --strict` `verdict: PASS`; four `axioms.sh` rows
clean; fidelity 44/22/15/20/29/20, unscoped **150/150**, 0 differences.

| # | run-3 finding | run-4 verdict |
|---|---|---|
| 1 | missing run-2 board record (HIGH) | **fixed** — the record exists, its numbers match the verifier's own, all cited commits exist |
| 2 | stale line count | **still wrong** — the Chinese half kept `2,354` while the English half was corrected |
| 3 | stale commit count | **still wrong** — measured 98 = 92 `feat` + 6 `docs`; the English half read 97 (invalidated by the correcting commit itself), the Chinese half 96 |
| 4 | reconciliation count | **fixed** (eight = seven strengthened + one dropped, six K4) |
| 5 | unpremised headline biconditionals | **fixed** — premise lists match the authority verbatim; the refuting witness was re-verified |
| 6 | azulene boundary | **fixed** — `7/151 = 4.6358 %` recomputed |
| 7 | correction-log count | **fixed** |
| 8 | commit-granularity deviation | **still wrong** — the deviation is registered, but the Chinese half still asserted the unqualified rule |
| 9 | plan sketch rows / typo | **fixed**; row-by-row spot-checks against the authority exact |
| 10 | bilingual drift in §5 | **partial → still wrong** — the Chinese half reported runs 1–3 but attributed 36 examples to all three rounds (English: 36 for runs 1–2; board: 56 for run 3) |
| 11 | API-calibration row | **fixed** |

Nine further (smaller) findings: the self-invalidating commit count (N1), the untouched Chinese half
(N2), the example-count attribution (N3), the run-2 commit-range arithmetic (N4, 23 not 19), the
`Compose.lean` header still saying "nothing added" (N5), the stale plan status header (N6, "Sprint 1
open … K1 dispatched"), a `§13.5` cross-reference that should be §12/§13-item-5 (N7), the Marcus
display's missing premise list (N8), and a duplicated item number in plan §13 (N9).

Most of these were corrected in the follow-up commits of this round (the counts are re-measured after
the last commit that touches `PhotoLean/`); run 5 checked each one and its record is below.

### Run 5 — 2026-09-20 — re-check of the run-4 corrections — verdict **C-plane FAIL (11 of 13 items fixed)**

Verifier: same role, C-plane only. Baseline: the comment-stripped code plane of all 29
`PhotoLean/**/*.lean` files hashes `21f46569e1d09a428ad652a5d1ed111d` at every revision from
`baa5c1e` to `HEAD` — **only comments moved**, so no mathematics re-verification was triggered; gates
re-run on the tree (`build` OK, `--strict` PASS/clean, two `axioms.sh` rows clean, fidelity
44/22/15/20/29/20 and unscoped 150/150 with 0 differences).

Fixed and confirmed: the Chinese half's line count (**2,360**, both halves), the commit count
(**99 = 92 `feat` + 7 `docs`**, quoted value = `git log --oneline -- PhotoLean/Kasha | wc -l`), the
per-lemma sentence qualified with the K5a/K5b deviation, the example-count attribution (36 for runs
1–2, 56 for run 3, consistently in both halves and on this board), N1 (the counting commit touches no
`PhotoLean/` file, so the count does not invalidate itself), N2, N3, N4 (the run-2 range really holds
23 commits: 16 `feat` + 7 `docs`), N5 (`Compose.lean`'s header and plan §3.1 now agree and both are
literally true), N8 (the Marcus display lists exactly the authority's hypotheses), N9 (plan §13 items
1–8, no duplicate).

Standing after run 5 (both corrected afterwards): **N6-board** — the *status header of this board*
still read "Sprint 0 closed, Sprint 1 open … K1 dispatched" and claimed the literature rows were not
in the skeleton, contradicting the delivered state — and **N7** — `plan.md` §1.2 still cross-referred
to "§13.5" (which is the time-integrated-yields item) and named the exponential-race probe "K4c"
(it is K4b; K4c is bridge bookkeeping). Four smaller drifts were also reported and corrected: the
past-tense claim on this board that "run 5 re-audited the corrections" (a record for a run that had
not happened), the Chinese half of `RESULTS.md` §5 attributing the positivity sweep to five
milestones instead of run 2's three, the window corollary's omission of its extra premise `h0`, and
the status of the 36/56 example counts (they are the verifier's own reported probe counts; its probes
live outside the repository, so the counts are cited as reported, not as tree-measurable).

### Run 6 — 2026-09-20 — full documentation-plane sweep — verdict **C-plane FAIL (six run-5 items all fixed; five new drifts)**

Verifier: same role. Baseline: the comment-stripped code plane of `PhotoLean/**/*.lean` is unchanged
since `baa5c1e` (only `Compose.lean`'s header comment moved); gates re-run on the tree: `lake build`
OK, `--strict` `verdict: PASS`, two `axioms.sh` rows clean, unscoped fidelity 150/150 with 0
differences. All six run-5 items were confirmed fixed (board status header; `plan.md`'s
`§13.5`/`K4c` cross-references in §1.2; the board's past-tense run-5 claim; the Chinese half's sweep
scope; the window corollary's `h0`; the example-count provenance). Five new drifts were found and
corrected in `7cc7059`: **F1** `plan.md` §1.5 still called the exponential-race probe "K4c" and
phrased it as a live stretch item while probe K4b is closed; **F2** the plan's "row by row" claim was
false for five rows (§4.2 #20 `specFrac_sum`, #21 `kashaWithin_iff_specFrac`, §6.2 #14
`vavilov_premise_necessary`, #17 `leak_le_of_radBranch_le`, #18 `kashaWithin_of_uniform_branch`);
**F3** run counts ("four verifier runs", "all four runs", "四轮") that re-stale as records
accumulate; **F4** the K5b `feat`-commit count read 4 on the board and 3 in `RESULTS.md` (a
scope-convention difference); **F5** `RESULTS.md`'s header claimed every number is tree-measured,
contradicted by its own note about the verifier's reported probe counts. Also reported: run 5's
digest `21f46569…` is not reproducible under any of ~3,300 stripping conventions tried (the claim it
supports was verified directly instead) — recorded here as the reason this board cites the
*comparison*, not that digest.

### Run 7 — 2026-09-20 — delta check of the run-6 fixes — verdict **C-plane FAIL (F1–F4 fixed; F5 residual + cross-reference labels)**

Verifier: same role, delta scope. Source plane unchanged (`372a384` is the last commit touching
`PhotoLean/`); gates re-run: `lake build` OK, `--strict` `verdict: PASS`, two `axioms.sh` rows clean,
fidelity 150/150 with 0 differences. **F1–F4 confirmed fixed** (the five corrected plan rows are
literal substrings of the authority's declarations; five further rows spot-checked also match; the
file-scoped commit convention is identical in both files; no run-count sentence remains that will
stale). **Still wrong**: F5 — the *Chinese* header of `RESULTS.md` still said every number is
tree-measured; plus cross-reference labels — `LITERATURE.md` (§R1.1, §R1.7 twice) and the board's
Sprint-0 note called the *Marcus bridge* "K4b" (it is K4c; K4b is the exponential-race probe), the
probe `kasha-api-race.lean` called the exponential-race premise "K4c" (the inverse), and two more
plan rows (§6.1 #6 `kashaWithin_mono_tol`, §7.2 #15 `kashaGapThreshold_pos`) were still not literal,
which made the "row by row" claim over-broad. All corrected in `92fad2f`, except the probe's
line 22, whose single-label inversion survived that commit and was corrected in `0e3acbe`
(reported by run 8).

### Run 8 — 2026-09-20 — final delta check of the run-7 fixes — verdict **C-plane FAIL (one surviving single-label inversion)**

Verifier: same role, tight delta scope. Five of the six items confirmed fixed: the source plane is
still frozen at `372a384` (no `.lean` code-plane change), the Chinese header of `RESULTS.md` now
states the same provenance rule as the English half, the two plan rows are literal against the
authority, the board's run-6/run-7 records are accurate summaries, and the re-sweep found no stale
count (2,360 lines; 99 = 92 + 7; 150 = 110 + 37 + 3; fidelity 44/22/15/20/29/20; the instance ratios
and boundaries; 193/825/400). All gates green. **One factual defect stood**: `probes/kasha-api-race.lean`
line 22 still called the exponential-race premise "K4c", contradicting line 7 of the same file and
plan §7.2 (K4b = the race probe, K4c = the Marcus-bridge bookkeeping). Three cosmetic/provenance
items were also reported: the plan's unreproducible "all 75 table rows" figure, this board's run-7
closure not naming the follow-up commit, and an "anti-Kashi" typo. All four were corrected in
`0e3acbe`.

### Run 9 — 2026-09-20 — minimal confirmation of the run-8 fixes — verdict **C-plane PASS / contract gates PASS**

Verifier: same role, four-item scope. (1) The probe's lines 7 and 22 now both read K4b and the file
compiles exit 0 with no single-label inversion anywhere in the leaves (the paired `plan K4b/K4c`
mentions are header/loci lines, not assertions about one premise); the API log, literature record and
`RESULTS.md` reference the two items correctly. (2) The plan's "75 table rows" figure is replaced by
a description of the comparison. (3) The board's run-7 closure now names `0e3acbe`, and the
`anti-Kashi` typo is gone (repo-wide grep: 0 hits). (4) No new drift: the last commit touching
`PhotoLean/` is still `372a384`, the worktree is clean, the commit counts are unchanged, and the
gates re-run verbatim: `lake build` → `Build completed successfully.` (exit 0); `check.sh --strict` →
scan `clean` / `build: OK` / `verdict: PASS` (exit 0); `axioms.sh … I11t_azulene_tolerance_dependence`
→ `[propext, Classical.choice, Quot.sound]` / `PASS` (exit 0); unscoped fidelity →
`delivered, word-for-word: 150`, `signature differences: 0` (exit 0).** Cosmetic remarks noted (not
verdict-flipping): this record supersedes the "Run 8 — pending" placeholder, and run 7's closure
could cite the hash directly (done above).**
**The documentation plane now matches the tree: the theory is closed.**

### Review-fix round — 2026-09-21 — external review M1/M3 statement fixes — author-gated, then **independently verified PASS** (verdict recorded in `theories/SymmetryFactor/TASKS.md` run 1, batch C, 2026-09-21)

Actor: the second external full-repository review (`review/FULL-REVIEW-2026-09-21.md`, findings M1–M12;
the two Kasha items are M1 and M3), executed under direct human instruction. This block is an
**author-side gate record**, not a verifier verdict — per iron rule 6 the writer of a fix does not
adjudicate it; the two open board rows above stay unticked until an independent verifier re-runs the
gates.

| item | change | gates re-run by the author (raw results) |
|---|---|---|
| M1 | `kashaDescriptor_nonvacuous` statement **strengthened** to `∃ rad ic, RateData rad ic 1 ∧ KashaRule rad ic 1` (delivered form was trivially true of every ladder: `KashaRule · · 0` holds via `upperYield_zero`; kernel probe `∀ rad ic, KashaDescriptor rad ic` compiled during the review). Witness unchanged; skeleton authority synced word-for-word; plan §3.1 + §5.2 #20 updated | `lake build PhotoLean.Kasha.Criterion` → `Build completed successfully.`; `axioms.sh` → `[propext, Classical.choice, Quot.sound]` / `verdict: PASS` |
| M3 | `perLevel_ic_ge_rad_insufficient` **added** (plan §6.2 #13b; the literal `rad i ≤ ic i` reading that the paper outline's headline quotes; same witness `rad ≡ ic ≡ 1`, leak `3/4` vs `(1/2)·(7/8)`) | `lake build PhotoLean.Kasha.Sharp` → OK; `axioms.sh` → `[propext, Classical.choice, Quot.sound]` / `verdict: PASS` |
| M2 | `I7_equalRates_leak_two` docstring scoped to its statement (the `6/7` fraction is I6+I7 composed; the per-level facts are the Sharp rows) — comment-only | strict scan `clean` (the scan reads comments; no forbidden keyword introduced) |
| — | whole-tree re-gate after all Kasha edits | `lake build` → exit 0; `check.sh --strict` → `clean` / `verdict: PASS`; fidelity unscoped **151/151**, `signature differences: 0`; milestone scope **44/22/16/20/29/20**; skeleton compiles at 0 error; new authority sha256 `8c5ed93b…` |

Counts after the round: **151 declarations** (111 theorems + 37 definitions + 3
structures/inductives), 2,430 lines. Runs 1–9 above stand as recorded against `b645cbfb…` (150);
no delivered theorem was refuted — one statement was strengthened, one row added.
