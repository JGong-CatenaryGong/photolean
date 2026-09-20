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
  (**132 declarations: 105 theorems + 26 definitions + 1 inductive**; of which the `## S1` section is
  30 = 15 definitions/inductives + 15 theorems, delivered; fidelity check `python3 theories/BEP/probes/bep-fidelity.py
  --theory Sabatier [--milestone S<k>]`).
- **Sprint-0 kernel evidence**: `theories/Sabatier/probes/sabatier-risk-probe.lean` (0 error).
- Theory direction: **the Sabatier principle / volcano plot**, human request of 2026-09-21
  (three parts: formal description / proof and exact conditions / instance verdicts).
- Deliverable module prefix: `PhotoLean.Sabatier`; sources under `PhotoLean/Sabatier/`
  (`SOURCE_DIRS` is global and covers them).

---

## Sprint 0 — environment, statements, plan (closed)

> Note: the eight rows below are **process rows** (environment, probe, contract, plan) — verified by
> the lead where they are reproducible (skeleton and probe compile, API probes compile, plan/board
> exist, `defaultTargets` parsed) and covered by verifier run 1's scope cell; several are not
> per-row checkable by a verifier (e.g. "human confirmation").

- [x] Theory directory `theories/Sabatier/` created with the five required items; contract
      `proofs/ENGINE.yml` extended (`THEORIES="Marcus hammond BEP kasha Sabatier"` + `PLAN_Sabatier` /
      `TASKS_Sabatier` / `LITERATURE_Sabatier` / `PROBES_Sabatier` / `RESULT_Sabatier`)
- [x] **Statement skeleton compiles**: `theories/Sabatier/probes/sabatier-statement-skeleton.lean`
      (132 declarations: 105 theorems + 26 definitions + 1 inductive; 0 error, placeholder-only bodies)
- [x] **Lead risk probe**: `theories/Sabatier/probes/sabatier-risk-probe.lean` — 0 error; proves the
      critical-path statement forms *before* planning (the sharp `iff`, the min/uniqueness pair, both
      legs, the tolerance bound, the activity layer, the three failure witnesses, the ℚ-free S4
      tangent/bridge rows, and the instance spot checks). **It caught two false skeleton rows**
      (`apex_comm`/`volcanoBarrier_comm`, `activity_descriptor_iff`) → corrected, correction log in
      `plan.md` §3.1
- [x] API calibration (`api_researcher`) → `proofs/API-NOTES.md` § "Sabatier theory (2026-09-21)" +
      `theories/Sabatier/probes/sabatier-api-{max-abs,monotone,explog-sqrt,cast-ite}.lean`
      (4 probes, all exit 0 / 0 error / 0 warning)
- [x] Literature survey (`literature_researcher`) → `theories/Sabatier/LITERATURE.md` (30 sources;
      most sections carry a `Formalizable implication.` block, the rest an `**Impact:**` note — the
      record is checkable per source either way) + `theories/Sabatier/literature/INSTANCE-DATA.md`
      (printed tables, with the clean negatives: no IUPAC entry, `0 < alphaA*alphaB` absent from the
      literature, the `max`-form is not a kinetic law, three DOI corrections)
- [x] Plan landed: `theories/Sabatier/plan.md` §1–§14 (model, conventions, correction log, milestones,
      sprint order, risks, acceptance criteria, honesty table, scope limits, leaves)
- [x] `lakefile.toml` `defaultTargets` extended with `PhotoLean.Sabatier.Basic` (one line per module,
      in the same commit as the module)
- [x] Human confirmation of the design (2026-09-21: layout + the S1–S5 model approved)

## S1 — description layer (`PhotoLean/Sabatier/Basic.lean`; owner lead; Sprint 0)

- [x] definitions `branchUp` / `branchDown` / `volcanoBarrier` / `apex` / `apexBarrier` /
      `VolcanoDescriptor` / `AntiVolcanoDescriptor` / `activity` / `SabatierConforms` / `TooStrong` /
      `Optimal` / `TooWeak` / `NearOptimal` / `SZone` / `sabatierZone` — Basic.lean — lead — done — (verifier run 1 PASS) —
      plan §4.1
- [x] `branch_gap` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.2
- [x] `apex_crossing` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.2
- [x] `apex_unique_crossing` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.2
- [x] `apex_eq_zero_iff` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.2
- [x] `apex_relabel` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.2 (replaces the FALSE `apex_comm`, §3.1)
- [x] `volcanoBarrier_relabel` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.2 (replaces the FALSE
      `volcanoBarrier_comm`, §3.1)
- [x] `volcanoBarrier_at_apex` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.2
- [x] `branchUp_lt_branchDown_of_lt_apex` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.2
- [x] `branchDown_lt_branchUp_of_apex_lt` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.2
- [x] `volcanoBarrier_eq_branchUp_of_apex_le` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.2
- [x] `volcanoBarrier_eq_branchDown_of_le_apex` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.2
- [x] `sabatierZone_eq_optimal_iff` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.3
- [x] `sabatierZone_eq_tooStrong_iff` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.3
- [x] `sabatierZone_eq_tooWeak_iff` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.3
- [x] `nearOptimal_iff_band` — Basic.lean — lead — done — (verifier run 1 PASS) — plan §4.3
- [x] auxiliary declarations `branchDown_le_branchUp_of_apex_le` / `branchUp_le_branchDown_of_le_apex`
      — Basic.lean — lead — done — (verifier run 1 PASS) — implemented auxiliaries (not authority rows; reported by the
      fidelity checker as "not in authority")

## S2 — law layer (`PhotoLean/Sabatier/Criterion.lean`; owner prover_b; Sprint 1)

- [x] `volcanoBarrier_apex_le` / `volcanoBarrier_eq_apex_iff` — Criterion.lean — prover_b — done — (verifier run 2 PASS) — plan §5
- [x] `volcanoBarrier_strictMono_of_apex_le` / `volcanoBarrier_strictAnti_of_le_apex` — Criterion.lean — prover_b — done — (verifier run 2 PASS) — plan §5
- [x] `volcanoBarrier_le_apex_add` — Criterion.lean — prover_b — done — (verifier run 2 PASS) — plan §5 (tolerance bound)
- [x] `volcanoBarrier_apex_form` — Criterion.lean — prover_b — done — (verifier run 2 PASS) — plan §5
- [x] `volcanoBarrier_secSlope_of_apex_le` / `volcanoBarrier_secSlope_of_le_apex` — Criterion.lean — prover_b — done — (verifier run 2 PASS) — plan §5
- [x] `apexBarrier_eq` — Criterion.lean — prover_b — done — (verifier run 2 PASS) — plan §5
- [x] `volcano_descriptor_of_physical` — Criterion.lean — prover_b — done — (verifier run 2 PASS) — plan §5 (main positive statement)
- [x] `activity_pos` / `activity_le_apex` / `activity_eq_apex_iff` / `antiDescriptor_activity_iff` / `activity_ratio` — Criterion.lean — prover_b — done — (verifier run 2 PASS) — plan §5
- [x] `exists_optimal` / `exists_tooWeak` / `exists_tooStrong` / `exists_nearOptimal` — Criterion.lean — prover_b — done — (verifier run 2 PASS) — plan §5 (non-vacuity)

## S3 — sharp conditions (`PhotoLean/Sabatier/Sharp.lean`; owner prover_d; Sprint 1)

- [x] `volcano_descriptor_iff` — Sharp.lean — prover_d — done — (verifier run 2 PASS) — plan §6 (**headline**: `⟺ 0 < alphaA * alphaB`)
- [x] `descriptor_fails_of_nonpos_product` — Sharp.lean — prover_d — done — (verifier run 2 PASS) — plan §6
- [x] `volcano_descriptor_iff_labels` — Sharp.lean — prover_d — done — (verifier run 2 PASS) — plan §6
- [x] `volcano_descriptor_of_neg` — Sharp.lean — prover_d — done — (verifier run 2 PASS) — plan §6 (label invariance)
- [x] `volcanoActivity_peak_iff` — Sharp.lean — prover_d — done — (verifier run 2 PASS) — plan §6 (the volcano plot)
- [x] `flat_witness` / `not_descriptor_flat` — Sharp.lean — prover_d — done — (verifier run 2 PASS) — plan §6
- [x] `plateau_witness` / `not_descriptor_plateau` — Sharp.lean — prover_d — done — (verifier run 2 PASS) — plan §6
- [x] `antiVolcano_monotone` / `not_descriptor_mixedSign` — Sharp.lean — prover_d — done — (verifier run 2 PASS) — plan §6

## S4 — cross-theory form (`PhotoLean/Sabatier/Compose.lean`; owner prover_a; Sprint 1)

- [x] definitions `parabolaUp` / `parabolaDown` / `parabolicBarrier` / `apexPar` — Compose.lean — prover_a — done — (verifier run 2 PASS) — plan §7
- [x] `linearVolcano_eq_bepTangent` — Compose.lean — prover_a — done — (verifier run 2 PASS) — plan §7
- [x] `bepLine_le_eact` — Compose.lean — prover_a — done — (verifier run 2 PASS) — plan §7
- [x] `linearVolcano_le_parabolic` — Compose.lean — prover_a — done — (verifier run 2 PASS) — plan §7 (lower-bound bridge)
- [x] `parabolicBarrier_crossing` — Compose.lean — prover_a — done — (verifier run 2 PASS) — plan §7 (sqrt algebra, main S4 risk)
- [x] `parabolicBarrier_apex_le` / `parabolicBarrier_eq_apex_iff` / `parabolic_descriptor` — Compose.lean — prover_a — done — (verifier run 2 PASS) — plan §7
- [x] `apexPar_self` — Compose.lean — prover_a — done — (verifier run 2 PASS) — plan §7
- [x] `linearVolcano_apex_exact` — Compose.lean — prover_a — done — (verifier run 2 PASS) — plan §7

## S5a — rational decision layer (`PhotoLean/Sabatier/RatModel.lean`; owner prover_c; Sprint 1)

- [x] definitions `branchUpQ` / `branchDownQ` / `volcanoBarrierQ` / `apexQ` / `apexBarrierQ` /
      `sabatierZoneQ` / `SabatierConformsQ` / `NearOptimalQ` — RatModel.lean — prover_c — done — (verifier run 2 PASS) — plan §8.1
- [x] cast transfers `branchUpQ_cast` / `branchDownQ_cast` / `volcanoBarrierQ_cast` / `apexQ_cast` /
      `apexBarrierQ_cast` — RatModel.lean — prover_c — done — (verifier run 2 PASS) — plan §8.1
- [x] `sabatierZoneQ_eq_sabatierZone` — RatModel.lean — prover_c — done — (verifier run 2 PASS) — plan §8.1 (classifier transfer)
- [x] `sabatierZoneQ_eq_optimal_iff` / `…_tooStrong_iff` / `…_tooWeak_iff` — RatModel.lean — prover_c — done — (verifier run 2 PASS) — plan §8.1
- [x] `sabatierConformsQ_iff` / `nearOptimalQ_iff` — RatModel.lean — prover_c — done — (verifier run 2 PASS) — plan §8.1
- [x] `volcanoBarrierQ_apex_le` / `volcanoBarrierQ_eq_apex_iff` — RatModel.lean — prover_c — done — (verifier run 2 PASS) — plan §8.1

## S5b — instance verdicts (`PhotoLean/Sabatier/Instances.lean`; owner prover_c; Sprint 2)

- [x] model rows I1–I3 (symmetric cycle, asymmetric series on both sides of its apex) — Instances.lean — prover_c — done — (verifier run 3 PASS; runs 4/5 re-check) — plan §8.2
- [x] non-conforming rows I4–I5 (zero-slope plateau, mixed-sign anti-volcano) — Instances.lean — prover_c — done — (verifier run 3 PASS; runs 4/5 re-check) — plan §8.2
- [x] tolerance / penalty rows I6 — Instances.lean — prover_c — done — (verifier run 3 PASS; runs 4/5 re-check) — plan §8.2
- [x] two-parabola cross-check row I7 (`apexPar 1 4 = 2/3`, crossing, pass height, linear-below) — Instances.lean — prover_c — done — (verifier run 3 PASS; runs 4/5 re-check) — plan §8.2
- [x] non-vacuity row I8 — Instances.lean — prover_c — done — (verifier run 3 PASS; runs 4/5 re-check) — plan §8.2
- [x] literature rows I9–I11 (HER `ΔG_H*` per metal: near-optimal / too weak / too strong; the axis
      is stated in the docstring and the values are DERIVED from the printed `ΔE_H` by the source's
      Eq. [8], record-marked `[arith]`, LITERATURE.md §R2.1) — Instances.lean — prover_c — done — (verifier run 3 PASS; runs 4/5 re-check) —
      plan §8.2
- [x] derivable literature row I12 (OER apex `1.60 eV = 3.20/2` on stated premises) — Instances.lean — prover_c — done — (verifier run 3 PASS; runs 4/5 re-check) — plan §8.2

---

## Acceptance records (independent verifier runs; the lead ticks from these)

| Batch | Scope | Verdict | Key evidence | Notes |
|---|---|---|---|---|
| Run 1 (independent verifier; batch: S1) | `PhotoLean/Sabatier/Basic.lean` (15 defs/inductives + 17 theorems) + the S1-relevant Sprint-0 artifacts (statement skeleton, risk probe, 4 API probes), verified on the working tree AND on a clean `git archive` copy of `00c5f69` | **PASS** | build OK / scan `clean` / 17/17 `#print axioms` = `[propext, Classical.choice, Quot.sound]`; verifier's own semantic probe (REPORTED by the verifier; the probe file was not committed — treat
these counts as testimony, `EXPERIENCE.md`'s "an unreproducible digest" rule: 82 `example` +
25 `#eval` grid rows + 14 hypothesis-necessity counterexamples, 0 error); own coverage audit of the fidelity checker (32/32 public declarations of `Basic.lean` captured; the two `private theorem`s are its only blind spot); bare-tree `check.sh --strict` PASS; clean-archive rebuild PASS (6308-job fresh build); artifact sha256 `a9f282bf…` byte-identical to commit `00c5f69` | findings F1–F12, **no HIGH**: F1 the plan cited kernel evidence the probe did not contain → three witnesses appended to the probe (`apex_naive_swap_values`, `apex_naive_swap_ne`, `activity_zero_kT_witness`); F2 stale authority counts → corrected to 132; F3 the statement corrections were not logged in the API log → logged; F4 this row; F5 "no deviations" wording → corrected; F6 the fidelity checker cannot see `private` declarations → the dead private helper deleted and the blind spot documented (the shared checker is used by four closed theories, so its regex is deliberately left unchanged); F7/F8/F9 `Basic.lean` docstring wording, including one literally false unconditional equivalence → qualified with `0 < kB*T`, declaration plane verified token-identical after comment stripping; F10/F11/F12 wording and API-log staleness notes |
| Run 2 (independent verifier; batch: S2/S3/S4/S5a) | `Criterion.lean` (19) + `Sharp.lean` (11) + `Compose.lean` (13) + `RatModel.lean` (21), verified on the working tree and on a clean `git archive` copy of `1796bf4` | **PASS** | build OK ×4 / `check.sh --strict` `verdict: PASS` ×4 / **64/64** authority rows `#print axioms` in `ALLOWED_AXIOMS` (58 × `[propext, Classical.choice, Quot.sound]` + 6 × `[propext]`); fidelity 19/19, 11/11, 13/13, 21/21, `signature differences: 0`; verifier's own adversarial probe: 52 kernel `example`s + a **425 250-point** rational brute force of `volcano_descriptor_iff` with **0 counterexamples** + hypothesis-necessity witnesses for every load-bearing premise + proof-term anti-circularity dumps (no self-reference) + ℚ↔ℝ cross-evaluation + gate-sensitivity controls (`sorryAx`/custom `axiom` are actually caught); clean-archive rebuild PASS | findings F1–F4 (one MEDIUM, three LOW), **no HIGH**: F1 `Compose.lean` `apexPar` docstring called the apex "the lower of the two crossings" (false on the descriptor axis; it is the one inside `-lam1 < dE < lam2`) → fixed; F2 `Criterion.lean` `antiDescriptor_activity_iff` docstring did not restate `0 < kB*T` → fixed; F3 `Compose.lean` header omitted the ∓`dE` driving-force identification → added; F4 four non-load-bearing hypotheses (retained; authority frozen) recorded as information |
| Run 3 (independent verifier; batch: S5b + frozen whole tree + documentation plane) | `Instances.lean` (38 rows), the whole tree at `1796bf4`, the documentation plane | **mathematics PASS / documentation FAIL** | S5b: build OK / `check.sh --strict` PASS / **38/38** axiom rows clean / fidelity 38/38 `signature differences: 0`; the verifier's own exact-rational script + kernel `#eval` probe reproduced **every** asserted number (48 checks, 0 mismatches), including the corrected I2 rows; whole tree: bare gate PASS, `defaultTargets` 35/35 coverage, one-shot axioms over **107 theorems + 27 definitions** all within the allowed set, `git status` clean, artifact hashes pinned; clean-archive rebuild (6342 jobs) PASS | **documentation findings V1–V14** (delivered declarations all valid): V1 false arithmetic in two `Instances.lean` docstrings → corrected; V2/V3/V4 three unreproducible counts in `RESULTS.md` (lines/commits/private helpers) → re-measured at the frozen revision; V5 a `LITERATURE.md` citation pointer → corrected; V6 stale plan status → refreshed; V7 a forward-looking claim about the acceptance records → rewritten; V8 two Chinese experience-bank entries (language policy) → translated in place; V9 the `ΔG_H*` values were labelled "transcribed" while the record derives them from the printed `ΔE_H` by Eq. [8] → labels aligned; V10–V13 wording/testimony notes → applied; V14 the strict scan did not match `constant` declarations → `check.sh` extended (additive; no line-start occurrence in `SOURCE_DIRS`, bare gate re-run PASS) || Run 4 (independent verifier; targeted re-audit of the V1–V14 disposals) | the disposal commits at `db8270e` + the re-measured counts; re-derived the comment-only claim on all four edited files | **PASS after the residual items were disposed** | item-by-item confirmation of the nine disposals with the verifier's own measurements: `Instances.lean` docstring arithmetic all true (9/9), counts re-measured (lines 2134, commits 70, private 36), the Sabatier section of `EXPERIENCE.md` carries 0 CJK lines, the `DERIVED` labels agree with `LITERATURE.md:657-658`, the reworded literature/source claims hold (16/17 sections with a `Formalizable implication.` block, the rest an `**Impact**` note, none lacking both), the new scan alternation `(axiom\|constant)` finds 0 line-start hits, bare gate `clean`/`PASS`, fidelity 30/19/11/13/21/38 with `signature differences: 0`, one-shot axioms over 107 theorems + 27 definitions identical to run 3; **declaration planes of the four edited files token-identical to `1796bf4`** (49/32/30/33 chunks, 0 differing) | residuals R1–R7 (one HIGH = the English half of the bilingual file still read "37 private helper lemmas"; R3/R4/R5 citation, label and anticipatory-verdict drift; R2/R6/R7 duplicated clause, `check.sh` comment wording, the missing experience-bank write-back) — **all disposed in the closeout commits**; the verdict converts to PASS and no delivered declaration was invalidated at any point of runs 3–4 |
| Run 5 (independent verifier; final confirmation) | the R1–R7 disposal at `f2b45b1` + the re-pinned counts + the bare gate and the unscoped fidelity | **PASS — ticks supported** | each R item confirmed by the verifier's own read/measurement (both halves of `RESULTS.md` read 36; §R1.2.2 citation correct; DERIVED labels everywhere with the intended `transcribed` occurrences only; no anticipatory verdict sentence anywhere in the theory; the four declaration planes token-identical to `1796bf4`; the `check.sh` comment now records its own false positive); counts reproduced (2 133 lines / 71 commits / 36 private helpers); bare `check.sh --strict` → `clean` / `verdict: PASS`; unscoped fidelity 132/132, per milestone 30/19/11/13/21/38, `not delivered yet: 0`, `signature differences: 0`; a fresh one-shot axioms run over the 107 theorems reproduced run 3's footprints exactly | residual **R8** (LOW, attribution): the seven ticked S5b rows cited "runs 2/3" while run 2's scope was S2–S5a — corrected in the same commit (S2–S5a cite run 2, S5b cites run 3 with runs 4/5 re-check); **no mathematical re-verification was needed**: the only source-plane change since `1796bf4` is one deleted comment line |

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
- **Deviations from "one commit per lemma"**: S1 was delivered as ONE grouped per-module commit
  (`00c5f69`, the module plus the Sprint-0 artifacts) — recorded here as a deviation from the
  contract's `COMMIT_TEMPLATE`, since the `<lemma>` slot holds a batch description. S2, S3, S4, S5a
  and S5b commit one lemma (or one row group) per commit; S5b's twelve row-group commits are the
  registered grouping for the instance layer. Commit counts are quoted **revision-pinned** (70 at
  `b57c8d1`); a count that is not pinned to a revision goes stale silently (verifier run 3, V3).
- **Known-weak statements**: the four non-vacuity `exists_*` rows carry little information (they are
  witness exhibitors); do not overstate them in `RESULTS.md` (the same warning the Hammond board
  carries for its trichotomy lemma).
