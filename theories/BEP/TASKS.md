# theories/BEP/TASKS.md — PhotoLean task board: the Bell–Evans–Polanyi principle (single source of truth for status)

- Status vocabulary: `todo` (not started) → `stmt` (statements calibrated and compiling) →
  `proving` (proof in progress) → `review` (handed to the verifier) → `done` (verifier PASS,
  recorded on this board).
- Row format: `- [x] <theorem> — <file> — <owner> — <status> — <note>`.
- **Ticking (`[x]`) happens only after a verifier PASS and is done by the lead**; workers never
  tick their own rows.
- The owner column holds engine role names (`prover_a`…`prover_d`); one file has at most one
  concurrent owner.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/BEP/plan.md`.
- **Statement authority**: `theories/BEP/probes/bep-statement-skeleton.lean`
  (must compile with 0 error before any proof work).
- Theory direction: **the Bell–Evans–Polanyi principle in the two-parabola (Marcus-type) model**,
  human request of 2026-09-20 (three parts: formal description / proof and validity conditions /
  instance verdicts).
- Deliverable module prefix: `PhotoLean.BEP`; sources under `PhotoLean/BEP/`
  (`SOURCE_DIRS` is global and covers them — `theories/BEP/` is outside the strict scan range).
- Status of this theory: **Sprint 0 (plan + contract + statements)**.

---

## Sprint 0 — environment, statements, plan (open)

- [x] Theory directory `theories/BEP/` created; contract extended with the multi-theory data plane
      (`THEORIES="Marcus hammond BEP"` + `PLAN_BEP` / `TASKS_BEP` / `LITERATURE_BEP` / `PROBES_BEP`
      / `RESULT_BEP`) — additive; the canonical Marcus leaves and the gate behaviour are unchanged
- [x] Plan landed: `theories/BEP/plan.md` (B1–B5, statement inventory, sprint order, risk register,
      honesty table, non-goals)
- [x] **Statement skeleton compiles**: `theories/BEP/probes/bep-statement-skeleton.lean` —
      owner `api_researcher`; **137 declarations**, `lake env lean` exit 0 / 0 errors (lead-verified),
      105 placeholder declarations of which 32 are already delivered word-for-word
- [x] Lead risk probe: `theories/BEP/probes/bep-risk-probe.lean` — owner `prover_d`; seven riskiest
      B3/Sprint-0 forms, **six PASS** (including the `Real.sqrt` tolerance radius by two independent
      routes and the equioscillation minimax lower bound in its original `∀ c a, ∃ x` form) and
      **one handed statement kernel-refuted** (the two-point solver: numerator sign + missing
      `lam ≠ 0`), which triggered three plan corrections; commits `135af1e`, `626d47a`
- [ ] API calibration: `proofs/API-NOTES.md` BEP section + `theories/BEP/probes/bep-api-*.lean`
      — owner `api_researcher` (final report pending)
- [ ] Literature round 1: `theories/BEP/LITERATURE.md` — owner `literature_researcher`; IUPAC
      verbatim entries, complementarity, limitations and the fidelity check landed; **the B5b data
      table is explicitly outstanding and flagged "must not be filled from memory"** (round 2 needed)
- [x] Human confirmation of the plan (2026-09-20: layout + B1–B5 approved, full scope; instance
      provenance = literature families + model-constructed families, each row labelled)
---

## B1 — description layer (`PhotoLean/BEP/Basic.lean`; owner prover_a; Sprint 1)

- [ ] definitions `eact` / `bepLine` / `bepDefect` / `transfer` / `reverseTransfer` / `secSlope`
      / `bepRadius` / `bepBestLine` / `EPBounds` / `EPLinearOn` / `EPExact` / `EPConformsOnWindow`
      / `EPBestOnWindow` / `EPZone` / `epZone` / `EPRegime` / `EPConforms` / `EPDescriptor`
      — Basic.lean — prover_a — todo — plan §4.1
- [ ] `eact_at_zero` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `eact_at_lam` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `eact_zero_lam` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `transfer_zero_lam` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `bepLine_at_zero` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `secSlope_zero_h` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `epZone_eq_degenerate_iff` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `epZone_eq_unphysical_iff` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `epZone_eq_thermoneutral_iff` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `epZone_eq_exergonic_iff` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `epZone_eq_endergonic_iff` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `epZone_eq_atForwardLimit_iff` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `epZone_eq_atReverseLimit_iff` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `epZone_eq_beyondForward_iff` — Basic.lean — prover_a — todo — plan §4.2
- [ ] `epZone_eq_beyondReverse_iff` — Basic.lean — prover_a — todo — plan §4.2

## B2 — law layer (`PhotoLean/BEP/Criterion.lean`; owner prover_a; Sprint 2)

- [ ] `eact_expansion` — Criterion.lean — prover_a — todo — plan §5
- [ ] `bepDefect_eq` — Criterion.lean — prover_a — todo — plan §5 (central identity)
- [ ] `bepLine_exact_at_thermoneutrality` — Criterion.lean — prover_a — todo — plan §5
- [ ] `bepDefect_at_thermoneutrality` — Criterion.lean — prover_a — todo — plan §5
- [ ] `transfer_eq_tsCoord` — Criterion.lean — prover_a — todo — plan §5 (Leffler/Brønsted bridge)
- [ ] `transfer_thermoneutral` — Criterion.lean — prover_a — todo — plan §5
- [ ] `reverseTransfer_thermoneutral` — Criterion.lean — prover_a — todo — plan §5
- [ ] `transfer_add_reverse` — Criterion.lean — prover_a — todo — plan §5 (Bronsted complementarity)
- [ ] `reverseTransfer_eq_transfer_neg` — Criterion.lean — prover_a — todo — plan §5
- [ ] `secSlope_eq_transfer_mid` — Criterion.lean — prover_a — todo — plan §5 (mean-value identity)
- [ ] `secSlope_midpoint_invariant` — Criterion.lean — prover_a — todo — plan §5
- [ ] `eact_neg_eq_add` — Criterion.lean — prover_a — todo — plan §5 (barrier reversal)
- [ ] `eact_antitone` — Criterion.lean — prover_a — todo — plan §5
- [ ] `bepDefect_nonneg` — Criterion.lean — prover_a — todo — plan §5
- [ ] `bepDefect_pos_iff` — Criterion.lean — prover_a — todo — plan §5
- [ ] `epDescriptor_holds` — Criterion.lean — prover_a — todo — plan §5
- [ ] `epDescriptor_conforms` — Criterion.lean — prover_a — todo — plan §5
- [ ] `epConforms_iff_bounds` — Criterion.lean — prover_a — todo — plan §5
- [ ] `exists_epDescriptor` / non-vacuity suite (`exists_thermoneutral` … `exists_degenerate`)
      — Criterion.lean — prover_a — todo — plan §5

## B3 — sharp conditions (`PhotoLean/BEP/Sharp.lean`; owner prover_d; Sprint 3)

- [ ] `epBounds_iff_region` — Sharp.lean — prover_d — todo — plan §6.1 (critical path)
- [ ] `epRegime_iff_strict` — Sharp.lean — prover_d — todo — plan §6.1
- [ ] `transfer_at_lam` — Sharp.lean — prover_d — todo — plan §6.1
- [ ] `transfer_at_neg_lam` — Sharp.lean — prover_d — todo — plan §6.1
- [ ] `not_epBounds_of_lt_neg` — Sharp.lean — prover_d — todo — plan §6.1
- [ ] `not_epBounds_of_gt` — Sharp.lean — prover_d — todo — plan §6.1
- [ ] `epExact_iff_degenerate` — Sharp.lean — prover_d — todo — plan §6.1
- [ ] `not_epLinearOn_of_ne_zero` — Sharp.lean — prover_d — todo — plan §6.1
- [ ] `exists_conforms_fails` — Sharp.lean — prover_d — todo — plan §6.1
- [ ] `bepDefect_abs_eq` — Sharp.lean — prover_d — todo — plan §6.2
- [ ] `epConformsOnWindow_iff_radius` — Sharp.lean — prover_d — todo — plan §6.2 (risk: `Real.sqrt`)
- [ ] `epConformsOnWindow_at_radius` — Sharp.lean — prover_d — todo — plan §6.2
- [ ] `epConformsOnWindow_mono` — Sharp.lean — prover_d — todo — plan §6.2
- [ ] `epConformsOnWindow_symm` — Sharp.lean — prover_d — todo — plan §6.2
- [ ] `bepDefect_antitone_lam` — Sharp.lean — prover_d — todo — plan §6.3
- [ ] `bepRadius_mono` — Sharp.lean — prover_d — todo — plan §6.3
- [ ] `epConformsOnWindow_mono_lam` — Sharp.lean — prover_d — todo — plan §6.3
- [ ] `bepBestLine_error` — Sharp.lean — prover_d — todo — plan §6.4
- [ ] `epBestOnWindow_holds` — Sharp.lean — prover_d — todo — plan §6.4 (risk: equioscillation)
- [ ] `bepLine_worst_case` — Sharp.lean — prover_d — todo — plan §6.4
- [ ] `bepBestLine_halves` — Sharp.lean — prover_d — todo — plan §6.4
- [ ] `bepDefect_zero_lam_witness` — Sharp.lean — prover_d — todo — plan §6.5
- [ ] `bepDefect_neg_lam_witness` — Sharp.lean — prover_d — todo — plan §6.5
- [ ] `bepDefect_sign_flips` — Sharp.lean — prover_d — todo — plan §6.5
- [ ] `secSlope_needs_h_ne_zero` — Sharp.lean — prover_d — todo — plan §6.5

## B4 — microscopic and cross-module layer (`PhotoLean/BEP/Compose.lean`; owner prover_b; Sprint 3)

- [ ] `eact_eq_barrier` — Compose.lean — prover_b — todo — plan §7
- [ ] `rate_eq_exp_neg_eact` — Compose.lean — prover_b — todo — plan §7
- [ ] `transfer_eq_tsCoord_bridge` — Compose.lean — prover_b — todo — plan §7
- [ ] `epBounds_iff_no_inverted_direction` — Compose.lean — prover_b — todo — plan §7 (Marcus bridge)
- [ ] `epBounds_of_reactionRegion` — Compose.lean — prover_b — todo — plan §7 (Hammond bridge)
- [ ] `epBounds_of_marcus_normal` — Compose.lean — prover_b — todo — plan §7
- [ ] `epDescriptor_of_microscopic` — Compose.lean — prover_b — todo — plan §7
- [ ] `bepDefect_le_of_microscopic` — Compose.lean — prover_b — todo — plan §7
- [ ] `bepRadius_add` — Compose.lean — prover_b — todo — plan §7
- [ ] `epConformsOnWindow_of_microscopic` — Compose.lean — prover_b — todo — plan §7
- [ ] `epConformsOnWindow_shrinks_with_inner` — Compose.lean — prover_b — todo — plan §7
- [ ] `transfer_complementary_microscopic` — Compose.lean — prover_b — todo — plan §7

## B5a — rational decision layer (`PhotoLean/BEP/RatModel.lean`; owner prover_c; Sprint 2)

- [ ] definitions `qEact` / `qBepLine` / `qBepDefect` / `qTransfer` / `qReverseTransfer` / `qSecSlope`
      / `qAlphaObs` / `qLamOfPair` / `qConformsWindow` / `EPQVerdict` / `epQVerdict`
      — RatModel.lean — prover_c — todo — plan §8.1
- [ ] `qEact_cast` — RatModel.lean — prover_c — todo — plan §8.1
- [ ] `qBepDefect_cast` — RatModel.lean — prover_c — todo — plan §8.1
- [ ] `qTransfer_cast` — RatModel.lean — prover_c — todo — plan §8.1
- [ ] `qSecSlope_cast` — RatModel.lean — prover_c — todo — plan §8.1
- [ ] `qAlphaObs_cast` — RatModel.lean — prover_c — todo — plan §8.1
- [ ] `qLamOfPair_cast` — RatModel.lean — prover_c — todo — plan §8.1
- [ ] `qSecSlope_eq_qTransfer_mid` — RatModel.lean — prover_c — todo — plan §8.1
- [ ] `qAlphaObs_eq_qTransfer_mid` — RatModel.lean — prover_c — todo — plan §8.1 (data → structure)
- [ ] `qLamOfPair_reconstructs` — RatModel.lean — prover_c — todo — plan §8.1 (λ̂ from two points)
- [ ] `epQVerdict_conforming_iff` — RatModel.lean — prover_c — todo — plan §8.1
- [ ] `epQVerdict_boundary_iff` — RatModel.lean — prover_c — todo — plan §8.1
- [ ] `epQVerdict_superLinear_iff` — RatModel.lean — prover_c — todo — plan §8.1
- [ ] `epQVerdict_subLinear_iff` — RatModel.lean — prover_c — todo — plan §8.1
- [ ] `qConformsWindow_iff_radius_sq` — RatModel.lean — prover_c — todo — plan §8.1

## B5b — instance verdicts (`PhotoLean/BEP/Instances.lean`; owner prover_c; Sprint 4)

- [ ] I1 thermoneutral family (`λ=2, x=0`) — Instances.lean — prover_c — todo — plan §8.2
- [ ] I2 mildly exergonic (`λ=2, x=1/2`) — Instances.lean — prover_c — todo — plan §8.2
- [ ] I3 mildly endergonic (`λ=2, x=-1/2`) — Instances.lean — prover_c — todo — plan §8.2
- [ ] I4 forward barrierless limit (`λ=2, x=2`) — Instances.lean — prover_c — todo — plan §8.2
- [ ] I5 reverse barrierless limit (`λ=2, x=-2`) — Instances.lean — prover_c — todo — plan §8.2
- [ ] I6 forward inverted regime (`λ=2, x=3`, α<0) — Instances.lean — prover_c — todo — plan §8.2
- [ ] I7 reverse inverted regime (`λ=2, x=-3`, α>1) — Instances.lean — prover_c — todo — plan §8.2
- [ ] I8 degenerate family (`λ=0`) — Instances.lean — prover_c — todo — plan §8.2
- [ ] I9 unphysical curvature (`λ=-2`) — Instances.lean — prover_c — todo — plan §8.2
- [ ] I10 tolerance threshold (`λ=2, w=1`) — Instances.lean — prover_c — todo — plan §8.2
- [ ] I11 literature families from `LITERATURE.md` — Instances.lean — prover_c — todo — plan §8.2
- [ ] `inst_nonvacuous` — Instances.lean — prover_c — todo — plan §8.2

---

## Acceptance records (independent verifier runs; the lead ticks from these)

| Batch | Scope | Verdict | Key evidence | Notes |
|---|---|---|---|---|
| B1 + B5a (independent verifier #1) | `Basic.lean` + `RatModel.lean` | — | — | not yet dispatched |
| B2 + B3 (independent verifier #2) | `Criterion.lean` + `Sharp.lean` | — | — | not yet dispatched |
| B4 + B5b (independent verifier #3) | `Compose.lean` + `Instances.lean` | — | — | not yet dispatched |
| Frozen-state closeout | whole tree | — | — | not yet dispatched |

## Notes and conflict log

- **Statement corrections from the Sprint-0 probes (2026-09-20, three kernel counterexamples)**:
  (a) plan §4.2 row 4 `transfer_zero_lam` — the linear-response body gives `transfer 0 x = 1/2`, not
  `0` (found by `prover_a`; the old row belonged to the discarded TS-coordinate body); (b) the
  two-point solver `qLamOfPair` had the numerator sign flipped — with denominator
  `2*(x₂-x₁) - 4*(ea₁-ea₂)` the numerator must be `x₂² - x₁²`, not `x₁² - x₂²` (found by `prover_d`
  via the literal form returning `-λ`); (c) the same solver's reconstruction theorem needs the
  explicit premise `lam ≠ 0` (`λ = 0` with totalised division is a genuine counterexample). All three
  statements were fixed in `theories/BEP/plan.md` (§4.2, §8.1, §11) **before** the affected
  milestones were dispatched, and the corrections were pushed to `api_researcher` so the statement
  authority carries the corrected signatures. Lesson (recorded for the experience bank): a
  statement-first probe is worth exactly the counterexamples it produces — two of these three
  statements would have failed *after* proof work had started.
- **Layout decision (must be reported to the human)**: theory artifacts live under `theories/BEP/`
  as requested; the Lean sources live under `PhotoLean/BEP/` because the contract's `SOURCE_DIRS`
  (the acceptance gate's scan/build range) is global, so a source outside it would be invisible to
  `check.sh --strict`. Same decision as `hammond`; changing it would require a contract +
  `lakefile.toml` redesign.
- **Multi-theory naming**: the theory key is `BEP` (capitalized) although `proofs/ENGINE.md`
  describes `<theory>` as lowercase — the contract's entries are declaration-based
  (`PLAN_BEP`, …) and `check.sh` resolves them verbatim, so the uppercase key is honoured; the
  `hammond` key stays lowercase and untouched.
- **Lesson inherited from `hammond`**: zone "trichotomy"-style lemmas carry little information —
  the semantic content is in the `..._iff` lemmas; `RESULTS.md` must not overstate them.
- **Model assumption pointer**: every BEP theorem is conditional on the equal-curvature
  two-parabola model and on `λ` being fixed across the compared family; the honesty table is
  `theories/BEP/plan.md` §13.
