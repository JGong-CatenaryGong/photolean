# theories/SymmetryFactor/TASKS.md — PhotoLean task board: the symmetry-factor adjudication (single source of truth for status)

- Status vocabulary: `todo` → `stmt` (calibrated and compiling) → `proving` → `review` (handed to
  the verifier) → `done` (verifier PASS, recorded on this board).
- Row format: `- [ ] <declaration> — <file> — <owner> — <status> — <note>`.
- **Ticking (`[x]`) happens only after a verifier PASS and is done by the lead**; workers never
  tick their own rows. The 2026-09-21 delivery was author-gated first, then **independently
  verified PASS** (read-only verifier, all 35 rows + the 4 Relations §11 rows: build / strict /
  fidelity 35-0-0 and 15-10-5-5 / 28+4 axioms clean, plus adversarial probes B1–B5 confirming the
  verdict is non-vacuous, two-sided, and independently recomputed; 2 LOW findings, both
  environmental/cosmetic, neither blocking). The rows below are ticked on that verdict.
- **Statement authority**: `theories/SymmetryFactor/probes/SymmetryFactor-statement-skeleton.lean`
  (compiles at 0 error with `proofs/scripts/lake env lean`; sha256 `3653beb67c34d4701401bb06a2ba4ee1ad9654d09815cbb9f74ae3882aa7543d`,
  **35 declarations** = 28 theorems + 7 definitions). Two Sprint-0 statement corrections are
  logged in `plan.md` §3.1 (both premise-drops under the weakest-premise standard).
- Theory direction: **the β = 1/2 symmetry-factor reading vs the structural transfer coefficient of
  the unequal-curvature two-parabola model**, human request of 2026-09-21 (execute
- Deliverable module prefix: `PhotoLean.SymmetryFactor`; sources under `PhotoLean/SymmetryFactor/`
  (`SOURCE_DIRS` is global and covers them).
- Literature: S1 (practice locus, arXiv 2104.05424 §2.1, **first-hand read**), S2 (IUPAC TR 2014
  warning, first-hand record reused from BEP §R1.17), S3 (Shinagawa 2015, first-hand record
  reused), S4 (Marcus's symmetrization approximation, hammond S34 reused) — see `LITERATURE.md`.

---

## F0 — Sprint 0 (contract, literature, API, authority)

- [x] literature round L1/L2 — LITERATURE.md — lead — done — S1 found and read first-hand (the
      pre-registered decision rule's success branch); L2 (Fletcher 2009 first-hand upgrade)
      **not done**, registered as delegated/out-of-budget — the verdict does not depend on it
- [x] API probe (`probes/SymmetryFactor-api-probe.lean` + rounds 2–6) — probes — lead — done —
      four guessed names refuted at probe stage; all proof routes kernel-verified before dispatch;
      recorded in `proofs/API-NOTES.md` §symmetryFactor
- [x] statement authority (35 rows) — probes — lead — done — compiles 0 error with placeholders
- [x] risk instantiation of the headline rows at exact rationals (`(1,4) ↦ 2/3 ≠ 1/2`, `(4,1) ↦ 1/3`,
      `(1,1) ↦ 1/2`; crossing equation at `q = 2` outside the interval) — probes — lead — done —
      folded into the API probe rounds (examples C/D in `SymmetryFactor-api-probe.lean` and the
      build-verified deliverables)

## F1 — description + law layers (`Basic.lean`, `Criterion.lean`; owner lead-as-prover)

- [x] `asymReactantSurface` — Basic.lean — prover — done — definition; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `asymProductSurface` — Basic.lean — prover — done — definition; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `CrossesAtThermoneutral` — Basic.lean — prover — done — definition (consumes both surfaces); author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZero` — Basic.lean — prover — done — definition; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `BetaHalfReading` — Basic.lean — prover — done — definition; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `crosses_eq_algebra` — Basic.lean — prover — done — definitional-unfolding row (labelled); author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZero_nonneg` — Criterion.lean — prover — done — **premise-free** (§3.1 item 1); author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZero_le_one` — Criterion.lean — prover — done — **premise-free** (§3.1 item 2); author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZero_pos` — Criterion.lean — prover — done — weakest premise `0 < kp` only; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZero_lt_one` — Criterion.lean — prover — done — weakest premise `0 < kr` only; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZero_crosses` — Criterion.lean — prover — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `crossing_unique_in_unit_interval` — Criterion.lean — prover — done — calculus-free; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `crossing_witness_outside_interval` — Criterion.lean — prover — done — necessity witness `q = 2`; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZero_strictMono_kp` — Criterion.lean — prover — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZero_strictAnti_kr` — Criterion.lean — prover — done — author-gated, verifier run 1 PASS (2026-09-21)

## F2 — sharp conditions and verdicts (`Sharp.lean`)

- [x] `betaHalf_iff_equalForceConstants` — Sharp.lean — prover — done — **the headline verdict**; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZero_one_four` — Sharp.lean — prover — done — witness 2/3; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZero_four_one` — Sharp.lean — prover — done — witness 1/3; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `betaHalf_falsified_by_unequal` — Sharp.lean — prover — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `not_betaHalf_universal` — Sharp.lean — prover — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZero_gt_half_iff_stiffProduct` — Sharp.lean — prover — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZero_lt_half_iff_stiffReactant` — Sharp.lean — prover — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZero_eq_kernel_thermoneutral` — Sharp.lean — prover — done — kernel tie-back certificate; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `betaHalf_holds_in_kernel` — Sharp.lean — prover — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `betaHalf_eq_transfer_thermoneutral` — Sharp.lean — prover — done — BEP tie-back certificate; author-gated, verifier run 1 PASS (2026-09-21)

## F3 — rational decision layer (`RatModel.lean`)

- [x] `tsCoordZeroQ` — RatModel.lean — prover — done — definition; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `BetaHalfQ` — RatModel.lean — prover — done — definition; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `tsCoordZeroQ_cast` — RatModel.lean — prover — done — cast bridge; author-gated, verifier run 1 PASS (2026-09-21)
- [x] `betaHalfQ_iff` — RatModel.lean — prover — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `betaHalfQ_cast` — RatModel.lean — prover — done — cast bridge (norm_cast route rejected, measured — plan §4); author-gated, verifier run 1 PASS (2026-09-21)

## F4 — instances and verdicts (`Instances.lean`)

- [x] `inst_stiffProduct_lateTS` — Instances.lean — prover — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `inst_stiffReactant_earlyTS` — Instances.lean — prover — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `inst_symmetric_half` — Instances.lean — prover — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `inst_conflation_falsified` — Instances.lean — prover — done — **the H1 row** (both layers); author-gated, verifier run 1 PASS (2026-09-21)
- [x] `inst_nonvacuous_both_readings` — Instances.lean — prover — done — M1-lesson non-vacuity (pinned at concrete curvatures); author-gated, verifier run 1 PASS (2026-09-21)

## F5 — relation-graph integration and closeout

- [x] `Relations.lean` §11 (class A1: adjudicated conflation) + header edge-type list + theory count — Relations.lean — lead — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `theories/RELATIONS.md` new bilingual section + §2.5 registry rows for the seventh node (21 pairs) — RELATIONS.md — lead — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `README.md` 现状 (seven theories, module/declaration counts, fidelity list) — README.md — lead — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `proofs/API-NOTES.md` §symmetryFactor — API-NOTES.md — lead — done — author-gated, verifier run 1 PASS (2026-09-21)
- [x] `proofs/EXPERIENCE.md` round write-back — EXPERIENCE.md — lead — done — author-gated, verifier run 1 PASS (2026-09-21)

---

## Acceptance records

### Author-side gate record — 2026-09-21 — delivery of F1–F4 (+F5 rows above) — author-gated (superseded by run 1 below)

Actor: the review-fix session under direct human instruction (iron rule 6 bound at the time: these
rows stayed unticked until the independent read-only verifier returned PASS — run 1 below — on
whose verdict the lead then ticked every row).

| gate | raw result |
|---|---|
| `lake build` (five modules, then full tree) | `Build completed successfully.` (exit 0), **0 warnings** |
| `check.sh --strict` | leaf plane 7/7 theories OK; scan `clean`; `verdict: PASS` |
| authority compile | `lake env lean …SymmetryFactor-statement-skeleton.lean` → exit 0, placeholder warnings only, 0 errors |
| fidelity (unscoped) | `delivered, word-for-word: 35`, `not delivered yet: 0`, `signature differences: 0` |
| fidelity (milestone F1/F2/F3/F4) | 15/10/5/5 word-for-word |
| `axioms.sh` on all 28 theorems | each `[propext, Classical.choice, Quot.sound]` → `verdict: PASS` (sweep output on file in the round's shell history; spot rows: `betaHalf_iff_equalForceConstants`, `inst_conflation_falsified`) |
| vacuity self-check (M1 lesson, applied prospectively) | the only `∃`-free verdict rows are iff/witness forms; `inst_nonvacuous_both_readings` pins both readings at concrete positive curvatures; `BetaHalfReading 0 0` is FALSE under the totalized convention (0 ≠ 1/2), so no degenerate free pass exists — recorded for the verifier's vacuity pass |
| scan hygiene | no forbidden keyword in any delivered file (comments included); `set_option autoImplicit false` in all five modules; no `maxHeartbeats`/linter relaxations |

### Run 1 — 2026-09-21 — independent verification of the whole delivery (F1–F4 + Relations §11 + the Kasha M1/M3 re-check) — verdict **PASS** (2 LOW findings, none repo-blocking)

Verifier: independent read-only agent (separate session; repository untouched — `git status
--porcelain` clean at report time; probes only under `/tmp`, kernel-checked with `proofs/scripts/
lake env lean`). Brief was bounded and report-first per the lost-report lesson.

| batch | item | verdict | evidence (raw, from the verifier's report) |
|---|---|---|---|
| A | gates re-run | **PASS** | build exit 0 no warnings; `check.sh --strict` `verdict: PASS`, leaf plane `OK theories/SymmetryFactor (5/5)`, scan `clean`; authority compiles exit 0 (placeholder warnings only); fidelity unscoped **35/0/0**; milestones **15/10/5/5**; axioms **28/28** `[propext, Classical.choice, Quot.sound]`; Relations §11 rows **4/4** same footprint |
| B1 | vacuity pass (the M1 lesson, adversarial) | **as expected** | `BetaHalfReading 1 1` proved; `¬ BetaHalfReading 1 4` proved; the universal `∀ kr kp, 0<kr → 0<kp → BetaHalfReading kr kp` **failed to compile for the right reason** (rfl cannot prove `kr = kp`); `not_betaHalf_universal` is a proved `¬∀`; `inst_nonvacuous_both_readings` is a genuine conjunction, not a free `∃`-row |
| B2 | two-sidedness of the headline | **as expected** | both `.mp` (`BetaHalfReading 2 2 ⊢ (2:ℝ) = 2`) and `.mpr` (`(3:ℝ) = 3 ⊢ BetaHalfReading 3 3`) compile; `#check` shows the delivered `0 < kr → 0 < kp → (BetaHalfReading kr kp ↔ kr = kp)` |
| B3 | independent recomputation | **as expected** | both layers recomputed from definitions: `tsCoordZero 1 4 = 2/3` and `tsCoordZeroQ 1 2 = 2/3`, with `(tsCoordZeroQ 1 2 : ℝ) = tsCoordZero 1 4` proved and `2/3 ≠ 1/2` in ℝ and ℚ — the ℚ shadow and the ℝ closed form **agree** (the verifier's first probe attempt failed on its own cast typo, re-run clean — not a repo defect) |
| B4 | premise-drop audit (plan §3.1 items 1–2) | **sound** | `tsCoordZero_nonneg`/`tsCoordZero_le_one` instantiate and typecheck at `(-1,-1)` and `(-12345, 6789)` — the dropped premises were genuinely non-load-bearing under totalized `Real.sqrt`, and the rows are non-vacuous (real `∀`-statements; `0 < tsCoordZero 1 4` confirmed) |
| B5 | interval premise load-bearing | **as expected** | `q = 2` re-verified by definitional unfolding as a second real root at `(1,4)`, distinct from `2/3` — `q ∈ Icc 0 1` in the uniqueness row is load-bearing |
| C | Kasha M1/M3 re-check (the two rows left open by the review-fix round) | **PASS — both genuinely fixed** | M1: axioms clean; the trivial universal `∀ rad ic, RateData rad ic 1 → KashaRule rad ic 1` not only failed to prove but was **positively refuted** in a probe (equal-rates ladder: `RateData` re-proved from scratch, `not_kashaRule_of_rad_pos` gives `¬ KashaRule · · 1`); delivered type confirmed strengthened. M3: statement confirmed to carry the **literal** `rad i ≤ ic i` in source (Sharp.lean:397) and `#check`. Kasha fidelity re-run **151/151**, 0 differences |

Findings and disposition: **LOW-1** (verifier-environment: `/tmp` does not persist across its shell
invocations — the already-banked harness lesson; gates unaffected since `axioms.sh` uses unique
names under `.lake/tmp`) — no repo action. **LOW-2** (cosmetic: `#print axioms` Format line-wrap
double-spaces in 3 outputs; axiom set identical; `axioms.sh` already normalizes) — no repo action.

**Consequence**: the board rows F0–F5 were ticked by the lead on this verdict (iron rule 7); the
two open Kasha review-fix rows were ticked on batch C (its board carries the pointer). Iron rule 8
registrations were completed in the delivery commits (README 现状 seven theories; Relations §11 +
RELATIONS.md §3bis/§2.5/§5(x)/§7; AGENTS.md 当前状态) and their PENDING qualifiers are flipped by
this record. **The theory is closed.**
