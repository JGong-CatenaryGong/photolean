# theories/Sabatier/TASKS.md — PhotoLean task board: the Sabatier principle (single source of truth for status)

- Status vocabulary: `todo` (not started) → `stmt` (statements calibrated and compiling) →
  `proving` (proof in progress) → `review` (handed to the verifier) → `done` (verifier PASS,
  recorded on this board).
- Row format: `- [x] <theorem> — <file> — <owner> — <status> — <note>`.
- **Ticking (`[x]`) happens only after a verifier PASS and is done by the lead**; workers never
  tick their own rows.
- The owner column holds engine role names (`prover_a`…`prover_d`, `lead`); one file has at most one
  concurrent owner.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/Sabatier/plan.md`.
- **Statement authority**: `theories/Sabatier/probes/sabatier-statement-skeleton.lean`
  (15 definitions/inductives + 91 theorems; fidelity check `python3 theories/BEP/probes/bep-fidelity.py
  --theory Sabatier [--milestone S<k>]`).
- **Sprint-0 kernel evidence**: `theories/Sabatier/probes/sabatier-risk-probe.lean` (0 error).
- Theory direction: **the Sabatier principle / volcano plot**, human request of 2026-09-21
  (three parts: formal description / proof and exact conditions / instance verdicts).
- Deliverable module prefix: `PhotoLean.Sabatier`; sources under `PhotoLean/Sabatier/`
  (`SOURCE_DIRS` is global and covers them).

---

## Sprint 0 — environment, statements, plan (closed)

- [x] Theory directory `theories/Sabatier/` created with the five required items; contract
      `proofs/ENGINE.yml` extended (`THEORIES="Marcus hammond BEP kasha Sabatier"` + `PLAN_Sabatier` /
      `TASKS_Sabatier` / `LITERATURE_Sabatier` / `PROBES_Sabatier` / `RESULT_Sabatier`)
- [x] **Statement skeleton compiles**: `theories/Sabatier/probes/sabatier-statement-skeleton.lean`
      (15 definitions/inductives + 91 theorems; 0 error, placeholder-only bodies)
- [x] **Lead risk probe**: `theories/Sabatier/probes/sabatier-risk-probe.lean` — 0 error; proves the
      critical-path statement forms *before* planning (the sharp `iff`, the min/uniqueness pair, both
      legs, the tolerance bound, the activity layer, the three failure witnesses, the ℚ-free S4
      tangent/bridge rows, and the instance spot checks). **It caught two false skeleton rows**
      (`apex_comm`/`volcanoBarrier_comm`, `activity_descriptor_iff`) → corrected, correction log in
      `plan.md` §3.1
- [x] API calibration (`api_researcher`) → `proofs/API-NOTES.md` § "Sabatier theory (2026-09-21)" +
      `theories/Sabatier/probes/sabatier-api-{max-abs,monotone,explog-sqrt,cast-ite}.lean`
      (4 probes, all exit 0 / 0 error / 0 warning)
- [x] Literature survey (`literature_researcher`) → `theories/Sabatier/LITERATURE.md` (30 sources,
      each with the formalizable-implication column) + `theories/Sabatier/literature/INSTANCE-DATA.md`
      (printed tables, with the clean negatives: no IUPAC entry, `0 < alphaA*alphaB` absent from the
      literature, the `max`-form is not a kinetic law, three DOI corrections)
- [x] Plan landed: `theories/Sabatier/plan.md` §1–§14 (model, conventions, correction log, milestones,
      sprint order, risks, acceptance criteria, honesty table, scope limits, leaves)
- [x] `lakefile.toml` `defaultTargets` extended with `PhotoLean.Sabatier.Basic` (one line per module,
      in the same commit as the module)
- [x] Human confirmation of the design (2026-09-21: layout + the S1–S5 model approved)

## S1 — description layer (`PhotoLean/Sabatier/Basic.lean`; owner lead; Sprint 0)

- [ ] definitions `branchUp` / `branchDown` / `volcanoBarrier` / `apex` / `apexBarrier` /
      `VolcanoDescriptor` / `AntiVolcanoDescriptor` / `activity` / `SabatierConforms` / `TooStrong` /
      `Optimal` / `TooWeak` / `NearOptimal` / `SZone` / `sabatierZone` — Basic.lean — lead — review —
      plan §4.1
- [ ] `branch_gap` — Basic.lean — lead — review — plan §4.2
- [ ] `apex_crossing` — Basic.lean — lead — review — plan §4.2
- [ ] `apex_unique_crossing` — Basic.lean — lead — review — plan §4.2
- [ ] `apex_eq_zero_iff` — Basic.lean — lead — review — plan §4.2
- [ ] `apex_relabel` — Basic.lean — lead — review — plan §4.2 (replaces the FALSE `apex_comm`, §3.1)
- [ ] `volcanoBarrier_relabel` — Basic.lean — lead — review — plan §4.2 (replaces the FALSE
      `volcanoBarrier_comm`, §3.1)
- [ ] `volcanoBarrier_at_apex` — Basic.lean — lead — review — plan §4.2
- [ ] `branchUp_lt_branchDown_of_lt_apex` — Basic.lean — lead — review — plan §4.2
- [ ] `branchDown_lt_branchUp_of_apex_lt` — Basic.lean — lead — review — plan §4.2
- [ ] `volcanoBarrier_eq_branchUp_of_apex_le` — Basic.lean — lead — review — plan §4.2
- [ ] `volcanoBarrier_eq_branchDown_of_le_apex` — Basic.lean — lead — review — plan §4.2
- [ ] `sabatierZone_eq_optimal_iff` — Basic.lean — lead — review — plan §4.3
- [ ] `sabatierZone_eq_tooStrong_iff` — Basic.lean — lead — review — plan §4.3
- [ ] `sabatierZone_eq_tooWeak_iff` — Basic.lean — lead — review — plan §4.3
- [ ] `nearOptimal_iff_band` — Basic.lean — lead — review — plan §4.3
- [ ] auxiliary declarations `branchDown_le_branchUp_of_apex_le` / `branchUp_le_branchDown_of_le_apex`
      — Basic.lean — lead — review — implemented auxiliaries (not authority rows; reported by the
      fidelity checker as "not in authority")

## S2 — law layer (`PhotoLean/Sabatier/Criterion.lean`; owner prover_b; Sprint 1)

- [ ] `volcanoBarrier_apex_le` / `volcanoBarrier_eq_apex_iff` — Criterion.lean — prover_b — proving — plan §5
- [ ] `volcanoBarrier_strictMono_of_apex_le` / `volcanoBarrier_strictAnti_of_le_apex` — Criterion.lean — prover_b — proving — plan §5
- [ ] `volcanoBarrier_le_apex_add` — Criterion.lean — prover_b — proving — plan §5 (tolerance bound)
- [ ] `volcanoBarrier_apex_form` — Criterion.lean — prover_b — proving — plan §5
- [ ] `volcanoBarrier_secSlope_of_apex_le` / `volcanoBarrier_secSlope_of_le_apex` — Criterion.lean — prover_b — proving — plan §5
- [ ] `apexBarrier_eq` — Criterion.lean — prover_b — proving — plan §5
- [ ] `volcano_descriptor_of_physical` — Criterion.lean — prover_b — proving — plan §5 (main positive statement)
- [ ] `activity_pos` / `activity_le_apex` / `activity_eq_apex_iff` / `antiDescriptor_activity_iff` / `activity_ratio` — Criterion.lean — prover_b — proving — plan §5
- [ ] `exists_optimal` / `exists_tooWeak` / `exists_tooStrong` / `exists_nearOptimal` — Criterion.lean — prover_b — proving — plan §5 (non-vacuity)

## S3 — sharp conditions (`PhotoLean/Sabatier/Sharp.lean`; owner prover_d; Sprint 1)

- [ ] `volcano_descriptor_iff` — Sharp.lean — prover_d — proving — plan §6 (**headline**: `⟺ 0 < alphaA * alphaB`)
- [ ] `descriptor_fails_of_nonpos_product` — Sharp.lean — prover_d — proving — plan §6
- [ ] `volcano_descriptor_iff_labels` — Sharp.lean — prover_d — proving — plan §6
- [ ] `volcano_descriptor_of_neg` — Sharp.lean — prover_d — proving — plan §6 (label invariance)
- [ ] `volcanoActivity_peak_iff` — Sharp.lean — prover_d — proving — plan §6 (the volcano plot)
- [ ] `flat_witness` / `not_descriptor_flat` — Sharp.lean — prover_d — proving — plan §6
- [ ] `plateau_witness` / `not_descriptor_plateau` — Sharp.lean — prover_d — proving — plan §6
- [ ] `antiVolcano_monotone` / `not_descriptor_mixedSign` — Sharp.lean — prover_d — proving — plan §6

## S4 — cross-theory form (`PhotoLean/Sabatier/Compose.lean`; owner prover_a; Sprint 1)

- [ ] definitions `parabolaUp` / `parabolaDown` / `parabolicBarrier` / `apexPar` — Compose.lean — prover_a — proving — plan §7
- [ ] `linearVolcano_eq_bepTangent` — Compose.lean — prover_a — proving — plan §7
- [ ] `bepLine_le_eact` — Compose.lean — prover_a — proving — plan §7
- [ ] `linearVolcano_le_parabolic` — Compose.lean — prover_a — proving — plan §7 (lower-bound bridge)
- [ ] `parabolicBarrier_crossing` — Compose.lean — prover_a — proving — plan §7 (sqrt algebra, main S4 risk)
- [ ] `parabolicBarrier_apex_le` / `parabolicBarrier_eq_apex_iff` / `parabolic_descriptor` — Compose.lean — prover_a — proving — plan §7
- [ ] `apexPar_self` — Compose.lean — prover_a — proving — plan §7
- [ ] `linearVolcano_apex_exact` — Compose.lean — prover_a — proving — plan §7

## S5a — rational decision layer (`PhotoLean/Sabatier/RatModel.lean`; owner prover_c; Sprint 1)

- [ ] definitions `branchUpQ` / `branchDownQ` / `volcanoBarrierQ` / `apexQ` / `apexBarrierQ` /
      `sabatierZoneQ` / `SabatierConformsQ` / `NearOptimalQ` — RatModel.lean — prover_c — proving — plan §8.1
- [ ] cast transfers `branchUpQ_cast` / `branchDownQ_cast` / `volcanoBarrierQ_cast` / `apexQ_cast` /
      `apexBarrierQ_cast` — RatModel.lean — prover_c — proving — plan §8.1
- [ ] `sabatierZoneQ_eq_sabatierZone` — RatModel.lean — prover_c — proving — plan §8.1 (classifier transfer)
- [ ] `sabatierZoneQ_eq_optimal_iff` / `…_tooStrong_iff` / `…_tooWeak_iff` — RatModel.lean — prover_c — proving — plan §8.1
- [ ] `sabatierConformsQ_iff` / `nearOptimalQ_iff` — RatModel.lean — prover_c — proving — plan §8.1
- [ ] `volcanoBarrierQ_apex_le` / `volcanoBarrierQ_eq_apex_iff` — RatModel.lean — prover_c — proving — plan §8.1

## S5b — instance verdicts (`PhotoLean/Sabatier/Instances.lean`; owner prover_c; Sprint 2)

- [ ] model rows I1–I3 (symmetric cycle, asymmetric series on both sides of its apex) — Instances.lean — prover_c — todo — plan §8.2
- [ ] non-conforming rows I4–I5 (zero-slope plateau, mixed-sign anti-volcano) — Instances.lean — prover_c — todo — plan §8.2
- [ ] tolerance / penalty rows I6 — Instances.lean — prover_c — todo — plan §8.2
- [ ] two-parabola cross-check row I7 (`apexPar 1 4 = 2/3`, crossing, pass height, linear-below) — Instances.lean — prover_c — todo — plan §8.2
- [ ] non-vacuity row I8 — Instances.lean — prover_c — todo — plan §8.2
- [ ] literature rows I9–I11 (HER `ΔG_H*` per metal: near-optimal / too weak / too strong; axis stated
      in the docstring, numbers from LITERATURE.md §R4) — Instances.lean — prover_c — todo — plan §8.2
- [ ] derivable literature row I12 (OER apex `1.60 eV = 3.20/2` on stated premises) — Instances.lean — prover_c — todo — plan §8.2

---

## Acceptance records (independent verifier runs; the lead ticks from these)

| Batch | Scope | Verdict | Key evidence | Notes |
|---|---|---|---|---|
| — | — | — | (the first independent run is dispatched after Sprint 1 lands) | — |

**Our own pre-verification evidence (for cross-checking, not a substitute for the verifier)**
| Check | Artifact | Result |
|---|---|---|
| Sprint-0 risk probe (statement forms) | `probes/sabatier-risk-probe.lean` | 0 error; **two false skeleton rows caught** |
| API calibration | `probes/sabatier-api-*.lean` (4 files) | exit 0 / 0 error / 0 warning each |
| Statement fidelity | `python3 theories/BEP/probes/bep-fidelity.py --theory Sabatier --milestone S1` | 30/30 word-for-word, 0 differences, 0 missing, 2 auxiliaries |
| S1 gate | `check.sh --strict PhotoLean.Sabatier.Basic` | PASS; `#print axioms` = `[propext, Classical.choice, Quot.sound]` |

## Notes and conflict log

- **Layout decision (reported to the human)**: the theory's artifacts live under `theories/Sabatier/`
  as requested; the Lean sources live under `PhotoLean/Sabatier/` because the contract's
  `SOURCE_DIRS` (the acceptance gate's scan and build range) is global and the module prefix must
  match the directory — the same layout as the four earlier theories (`PhotoLean/Hammond`,
  `PhotoLean/BEP`, `PhotoLean/Kasha`). Plan §14 records the leaves.
- **Contract/gate change (lead, Sprint 0)**: `proofs/ENGINE.yml` gained `Sabatier` in `THEORIES` and
  the five `*_Sabatier` leaf variables (the variable pass of `check.sh` had silently skipped the new
  theory directory before that). Both passes (variable pass + directory sweep) now cover it.
- **Statement corrections (lead, Sprint 0)**: see `plan.md` §3.1 — two false authority rows
  (`apex_comm`/`volcanoBarrier_comm`, `activity_descriptor_iff`) were caught by the risk probe and
  replaced by kernel-correct forms before any delivered file cited them.
- **Deviations from "one commit per lemma"**: none so far in S1 (delivered as one `feat(S0)` commit
  for the module plus the S0 artifacts). If a milestone groups commits, the grouping is recorded here.
- **Known-weak statements**: the four non-vacuity `exists_*` rows carry little information (they are
  witness exhibitors); do not overstate them in `RESULTS.md` (the same warning the Hammond board
  carries for its trichotomy lemma).
