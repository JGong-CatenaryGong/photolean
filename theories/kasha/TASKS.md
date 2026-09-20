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
  `b645cbfbf61ecf08a7c5dbe3a5e5f8f8874e50cbc806e994ea53823dbf63aa17`), **150 declarations** (110 theorems + 37 definitions + 3 structures/inductives).
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
      measurements identified with model scalars) and §13 (the K4b attribution requirement; the ban on
      a global gap-monotonicity claim)
- [x] Human confirmation of the plan (2026-09-20: layout + K1–K5 approved; the three-part request
      mapped to §2/§3/§4 of `RESULTS.md`)
- **Registered deviation (commit granularity)**: one commit per lemma holds literally for K1 (28
  `feat` commits), K2 (22), K3 (15) and K4 (20); K5a (29 declarations, 4 `feat` commits) and K5b (20
  rows, 4 `feat` commits under the K5b area) batch their declarations into `feat(K5a|K5b)` commits.
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
- [x] `kashaDescriptor_nonvacuous` — Criterion.lean — prover_a — done — skeleton `b645cbfb`
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
+19 commits), so every artifact is pinned by blob hash (`Criterion.lean` `9c7a8c37…`, `Compose.lean`
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

### Run 4 — pending — documentation re-audit after the run-3 corrections

The run-3 findings are documentation-plane fixes; a focused re-audit (C-plane and the new
acceptance records only) is scheduled before the theory is declared closed. No verdict is recorded
here until that report exists.
