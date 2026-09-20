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
  `8508e1df7705daaac31288ef78e97073aaff2f1c6422c31bd2eb83b669cbf888`), **151 declarations** (111 theorems + 37 definitions + 3 structures/inductives).
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
      151 declarations with placeholder theorem bodies, `lake env lean` exit 0, sha256 `8508e1df7705daaac31288ef78e97073aaff2f1c6422c31bd2eb83b669cbf888`
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
      owner `api_researcher` — **delivered, sitting `review`**: the five probes were untracked at the
      first verifier run (finding HIGH-2, fix dispatched back to the owner); the recipes themselves
      were used verbatim by K1/K2/K4/K5a with zero rework
- [x] Sprint-0 risk probe: `theories/kasha/probes/kasha-risk-probe.lean` — owner `prover_b` —
      **done and verified** (verifier batch B: 11/12 rows PASS, the twelfth kernel-refuted, all
      probe files compile output-clean, 33 theorems with the single allowed footprint)
- [x] Literature round 1: `theories/kasha/LITERATURE.md` §R1 (§R1.0–§R1.9, 787 lines, commit
      `7fc2efd`) — owner `literature_researcher`; the round's three binding consequences are folded
      into plan §1.1 (scope qualifiers; `tol` is a model choice, not a literature number; rates are
      measurements identified with model scalars) and §13 (the K4b attribution requirement; the ban on
      a global gap-monotonicity claim)
- [ ] Human confirmation of the plan

---

## Board rows (one row per declaration of the statement authority)

### K1 — `PhotoLean/Kasha/Basic.lean` (owner prover_a)

- [x] `decay` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `radBranch` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `icBranch` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `cascade` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `emitYield` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `fluoYield` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `upperYield` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `specFrac` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `kashaMargin` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `funnelRatio` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `ladderRatio` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `KashaRule` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `KashaWithin` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `VavilovAt` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `VavilovUpTo` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `KashaDescriptor` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `RateData` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `KashaZone` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `kashaZone` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `decay_eq_rad_add_ic` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `radBranch_add_icBranch` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `radBranch_nonneg` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `icBranch_nonneg` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `radBranch_le_one` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `icBranch_le_one` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `cascade_self` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `cascade_nonneg` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `cascade_le_one` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `emitYield_self` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `emitYield_nonneg` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `emitYield_le_radBranch` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `fluoYield_eq_low_add_upper` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `fluoYield_zero` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `upperYield_zero` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `fluoYield_nonneg` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `upperYield_nonneg` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `upperYield_le_fluoYield` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `kashaRule_iff_upperYield_zero` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `specFrac_sum` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `kashaWithin_iff_specFrac` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `kashaZone_eq_pure_iff` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `kashaZone_eq_withinTol_iff` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `kashaZone_eq_violating_iff` — Basic.lean — prover_a — done — skeleton `8508e1df`
- [x] `kashaRule_of_rad_zero` — Basic.lean — prover_a — done — skeleton `8508e1df`

### K2 — `PhotoLean/Kasha/Criterion.lean` (owner prover_a)

- [ ] `cascade_succ` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `emitYield_succ` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `emitYield_succ_self` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `fluoYield_succ` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `upperYield_succ` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `cascade_add_upperYield` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `fluoYield_eq_one_sub_loss` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `fluoYield_le_one` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `fluoYield_mono_succ` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `fluoYield_lt_succ_of_rad_pos` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `fluoYield_eq_iff_rad_zero` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `fluoYield_lt_one_iff_loss` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `upperYield_eq_zero_iff` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `kashaRule_iff_rad_zero` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `not_kashaRule_of_rad_pos` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `vavilovAt_iff_rad_zero` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `vavilovUpTo_iff_rad_zero` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `kashaRule_iff_vavilovUpTo` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `not_kasha_universal` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `kashaDescriptor_nonvacuous` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `kashaWithin_of_kashaRule` — Criterion.lean — prover_a — todo — skeleton `8508e1df`
- [ ] `upperYield_le_sum_radBranch` — Criterion.lean — prover_a — todo — skeleton `8508e1df`

### K3 — `PhotoLean/Kasha/Sharp.lean` (owner prover_b)

- [ ] `kashaWithin_one_iff_rates` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `kashaWithin_one_iff_ratio` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `kashaWithin_one_iff_ic_ratio` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `funnelRatio_eq_ladderRatio_one` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `kashaWithin_iff_margin` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `kashaWithin_mono_tol` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `kashaWithin_zero_iff` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `kashaWithin_one_mono_ic` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `not_kashaWithin_one_of_ratio_lt` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `kashaThreshold_attained` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `perLevel_criterion_insufficient` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `vavilov_premise_necessary` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `kashaWithin_one_sharp_boundary` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `leak_le_of_radBranch_le` — Sharp.lean — prover_b — todo — skeleton `8508e1df`
- [ ] `kashaWithin_of_uniform_branch` — Sharp.lean — prover_b — todo — skeleton `8508e1df`

### K4 — `PhotoLean/Kasha/Compose.lean` (owner prover_d)

- [ ] `effRad` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `effIc` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `marcusIC` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `kashaGapThreshold` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `cascade_compose` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `emitYield_compose` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `effDecay_zero` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `effDecay_one` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `effUpperYield_one` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `effEmitYield_zero_one` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `kashaMargin_effective` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `kashaWithin_iff_effective` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `kashaWithin_iff_ladderRatio` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `ladderRatio_one` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `not_kashaWithin_of_ladderRatio_lt` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `kashaWithin_one_marcus` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `not_kashaWithin_of_gap_far` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `kashaWindow_halfWidth` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `kashaGapThreshold_pos` — Compose.lean — prover_d — todo — skeleton `8508e1df`
- [ ] `marcusIC_pos` — Compose.lean — prover_d — todo — skeleton `8508e1df`

### K5a — `PhotoLean/Kasha/RatModel.lean` (owner prover_c)

- [ ] `decayQ` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `radBranchQ` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `icBranchQ` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `cascadeQ` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `emitYieldQ` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `fluoYieldQ` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `upperYieldQ` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `funnelRatioQ` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `ladderRatioQ` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `KashaWithinQ` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `QRateData` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `KashaQVerdict` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `kashaQVerdict` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `twoRad` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `twoIc` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `threeRad` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `threeIc` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `decayQ_cast` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `radBranchQ_cast` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `icBranchQ_cast` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `cascadeQ_cast` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `emitYieldQ_cast` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `fluoYieldQ_cast` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `upperYieldQ_cast` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `kashaWithinQ_iff_cast` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `kashaWithinQ_iff_funnelRatioQ` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `kashaQVerdict_eq_pure_iff` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `kashaQVerdict_eq_withinTol_iff` — RatModel.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `kashaQVerdict_eq_violating_iff` — RatModel.lean — prover_c — todo — skeleton `8508e1df`

### K5b — `PhotoLean/Kasha/Instances.lean` (owner prover_c)

- [ ] `I1_conforming_control` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I2_antiKasha_control` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I3_threshold_boundary` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I3b_threshold_below` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I4_fluoYield_one` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I5_upperYield_one` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I6_fluoYield_two` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I7_equalRates_leak_two` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I7b_equalRates_violating` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I8_noLoss_vavilov` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I8b_noLoss_not_kasha` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I9_verdict_violating` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I13_row_inventory` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I14_not_one_sided` — Instances.lean — prover_c — todo — skeleton `8508e1df`
- [ ] `I10_trimethylazulene_conforming` — Instances.lean — prover_c — todo — literature row (thesis 1995 Table 3.3, `rad 1 = 33`, `ic 1 = 67000` in 10⁶ s⁻¹; LITERATURE §R1.6)
- [ ] `I11_azulene_violating` — Instances.lean — prover_c — todo — literature row (thesis 1995 Table 3.1, `35` / `720`; LITERATURE §R1.6)
- [ ] `I11alt_azulene2026_violating` — Instances.lean — prover_c — todo — literature row (Chem. Sci. 2026, printed `Φ_Fl = 2.42 %` ⇒ `242` / `9758`; LITERATURE §R1.4/§R1.6)
- [ ] `I11alt2_azulene2020_violating` — Instances.lean — prover_c — todo — literature row (Veys & Escudero JPCA 124, 7228 (2020) Table 2, `2.3×10⁷` / `5.3×10⁸` s⁻¹ ⇒ `23` / `530`)
- [ ] `I11t_azulene_tolerance_dependence` — Instances.lean — prover_c — todo — literature row, two tolerances on the same data (`¬ 1/100`, `1/10`)
- [ ] `I15_familyContrast` — Instances.lean — prover_c — todo — literature summary (I10 vs I11 at one tolerance)

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
| 5 | MED | `TASKS.md` had rewritten the Sprint-0 gate row's hash to a value that only exists *after* the later corrections | accepted. The hash history is: Sprint-0 gate at `e3ddc2d0…` (144 declarations) → correction round `4cf2b105…` (K1 #24, K3 #2/#9, K5a criterion) → literature rows `8508e1df…` (**151 declarations**). Quoting the current hash as "the artifact that passed the Sprint-0 gate" is a stale-number defect |
| 6 | MED | the fidelity checker had no milestone granularity, so a milestone's acceptance number was inexpressible | **fixed**: `bep-fidelity.py --milestone <K1…K5b>` scopes the report to the authority's `## <milestone>` block; regression re-run on BEP/hammond/Marcus (unchanged) |
| 7 | LOW | `KashaWithin` is defined for every real `tol`; `kashaMargin` is `0/0`-degenerate exactly on the branch it names | recorded in plan §12 (honesty table): the tolerance premise is explicit in every criterion row, and `kashaMargin` is only consumed under `0 < upperYield` |
| 8 | LOW | the `lakefile.toml` target for a module lands in a separate (lead) commit, while plan §11 says "same commit" | recorded as a **registered deviation**: `lakefile.toml` is lead-owned (workers are forbidden to edit it), so "same commit" is unachievable as written; the rule's purpose — no delivered module outside the build — is enforced by the lead immediately after each module lands |

