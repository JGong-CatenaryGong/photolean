# theories/SymmetryFactor/TASKS.md — PhotoLean task board: the symmetry-factor adjudication (single source of truth for status)

- Status vocabulary: `todo` → `stmt` (calibrated and compiling) → `proving` → `review` (handed to
  the verifier) → `done` (verifier PASS, recorded on this board).
- Row format: `- [ ] <declaration> — <file> — <owner> — <status> — <note>`.
- **Ticking (`[x]`) happens only after a verifier PASS and is done by the lead**; workers never
  tick their own rows. The 2026-09-21 delivery below is **author-gated**; every row stands at
  `review` with the author-side gate evidence in the acceptance record, until the independent
  verifier returns.
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

- [ ] `asymReactantSurface` — Basic.lean — prover — review — definition; author-gated
- [ ] `asymProductSurface` — Basic.lean — prover — review — definition; author-gated
- [ ] `CrossesAtThermoneutral` — Basic.lean — prover — review — definition (consumes both surfaces); author-gated
- [ ] `tsCoordZero` — Basic.lean — prover — review — definition; author-gated
- [ ] `BetaHalfReading` — Basic.lean — prover — review — definition; author-gated
- [ ] `crosses_eq_algebra` — Basic.lean — prover — review — definitional-unfolding row (labelled); author-gated
- [ ] `tsCoordZero_nonneg` — Criterion.lean — prover — review — **premise-free** (§3.1 item 1); author-gated
- [ ] `tsCoordZero_le_one` — Criterion.lean — prover — review — **premise-free** (§3.1 item 2); author-gated
- [ ] `tsCoordZero_pos` — Criterion.lean — prover — review — weakest premise `0 < kp` only; author-gated
- [ ] `tsCoordZero_lt_one` — Criterion.lean — prover — review — weakest premise `0 < kr` only; author-gated
- [ ] `tsCoordZero_crosses` — Criterion.lean — prover — review — author-gated
- [ ] `crossing_unique_in_unit_interval` — Criterion.lean — prover — review — calculus-free; author-gated
- [ ] `crossing_witness_outside_interval` — Criterion.lean — prover — review — necessity witness `q = 2`; author-gated
- [ ] `tsCoordZero_strictMono_kp` — Criterion.lean — prover — review — author-gated
- [ ] `tsCoordZero_strictAnti_kr` — Criterion.lean — prover — review — author-gated

## F2 — sharp conditions and verdicts (`Sharp.lean`)

- [ ] `betaHalf_iff_equalForceConstants` — Sharp.lean — prover — review — **the headline verdict**; author-gated
- [ ] `tsCoordZero_one_four` — Sharp.lean — prover — review — witness 2/3; author-gated
- [ ] `tsCoordZero_four_one` — Sharp.lean — prover — review — witness 1/3; author-gated
- [ ] `betaHalf_falsified_by_unequal` — Sharp.lean — prover — review — author-gated
- [ ] `not_betaHalf_universal` — Sharp.lean — prover — review — author-gated
- [ ] `tsCoordZero_gt_half_iff_stiffProduct` — Sharp.lean — prover — review — author-gated
- [ ] `tsCoordZero_lt_half_iff_stiffReactant` — Sharp.lean — prover — review — author-gated
- [ ] `tsCoordZero_eq_kernel_thermoneutral` — Sharp.lean — prover — review — kernel tie-back certificate; author-gated
- [ ] `betaHalf_holds_in_kernel` — Sharp.lean — prover — review — author-gated
- [ ] `betaHalf_eq_transfer_thermoneutral` — Sharp.lean — prover — review — BEP tie-back certificate; author-gated

## F3 — rational decision layer (`RatModel.lean`)

- [ ] `tsCoordZeroQ` — RatModel.lean — prover — review — definition; author-gated
- [ ] `BetaHalfQ` — RatModel.lean — prover — review — definition; author-gated
- [ ] `tsCoordZeroQ_cast` — RatModel.lean — prover — review — cast bridge; author-gated
- [ ] `betaHalfQ_iff` — RatModel.lean — prover — review — author-gated
- [ ] `betaHalfQ_cast` — RatModel.lean — prover — review — cast bridge (norm_cast route rejected, measured — plan §4); author-gated

## F4 — instances and verdicts (`Instances.lean`)

- [ ] `inst_stiffProduct_lateTS` — Instances.lean — prover — review — author-gated
- [ ] `inst_stiffReactant_earlyTS` — Instances.lean — prover — review — author-gated
- [ ] `inst_symmetric_half` — Instances.lean — prover — review — author-gated
- [ ] `inst_conflation_falsified` — Instances.lean — prover — review — **the H1 row** (both layers); author-gated
- [ ] `inst_nonvacuous_both_readings` — Instances.lean — prover — review — M1-lesson non-vacuity (pinned at concrete curvatures); author-gated

## F5 — relation-graph integration and closeout

- [ ] `Relations.lean` §11 (class A1: adjudicated conflation) + header edge-type list + theory count — Relations.lean — lead — review — author-gated
- [ ] `theories/RELATIONS.md` new bilingual section + §2.5 registry rows for the seventh node (21 pairs) — RELATIONS.md — lead — review — author-gated
- [ ] `README.md` 现状 (seven theories, module/declaration counts, fidelity list) — README.md — lead — review — author-gated
- [ ] `proofs/API-NOTES.md` §symmetryFactor — API-NOTES.md — lead — review — author-gated
- [ ] `proofs/EXPERIENCE.md` round write-back — EXPERIENCE.md — lead — review — author-gated

---

## Acceptance records

### Author-side gate record — 2026-09-21 — delivery of F1–F4 (+F5 rows above) — **author-gated; independent verifier PENDING** (NOT a verifier verdict)

Actor: the review-fix session under direct human instruction (iron rule 6 binds: these rows stay
unticked until an independent read-only verifier returns PASS).

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
