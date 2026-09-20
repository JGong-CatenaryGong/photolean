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
- Status of this theory: **delivered** — six modules, 191 declarations (32 defs + 2 inductives + 157
  theorems), all six milestone batches independently verified **PASS**. The closeout rows of the
  acceptance table below record every frozen-state audit whose report exists (three runs so far, each
  reporting documentation-only findings after independently re-verifying the mathematics; no
  mathematical defect has been found in any run). A verdict is only ever recorded from an audit
  report that already exists.

---

## Sprint 0 — environment, statements, plan (closed)

- [x] Theory directory `theories/BEP/` created; contract extended with the multi-theory data plane
      (`THEORIES="Marcus hammond BEP"` + `PLAN_BEP` / `TASKS_BEP` / `LITERATURE_BEP` / `PROBES_BEP`
      / `RESULT_BEP`) — additive; the canonical Marcus leaves and the gate behaviour are unchanged
- [x] Plan landed: `theories/BEP/plan.md` (B1–B5, statement inventory, sprint order, risk register,
      honesty table, non-goals)
- [x] **Statement skeleton compiles**: `theories/BEP/probes/bep-statement-skeleton.lean` —
      owner `api_researcher`; committed authority, **191 declarations** (32 defs + 2 inductives +
      157 theorems) with 157 placeholder declarations, `lake env lean` exit 0 / 0 other warnings,
      `sha256 c9aa2cb1…` (recorded in plan §3); the delivered set replaces every placeholder
      word-for-word (191/191, 0 differences)
- [x] Lead risk probe: `theories/BEP/probes/bep-risk-probe.lean` — owner `prover_d`; seven riskiest
      B3/Sprint-0 forms, **six PASS** (including the `Real.sqrt` tolerance radius by two independent
      routes and the equioscillation minimax lower bound in its original `∀ c a, ∃ x` form) and
      **one handed statement kernel-refuted** (the two-point solver: numerator sign + missing
      `lam ≠ 0`), which triggered three plan corrections; commits `135af1e`, `626d47a`
- [x] API calibration: `proofs/API-NOTES.md` BEP section + `theories/BEP/probes/bep-api-*.lean`
      — owner `api_researcher` (delivered; the failures list is the asset: `Real.sq_le_sq`,
      `Real.sqrt_lt_iff_lt_sq`, `Set.mem_Icc_iff`, bare `le_sqrt'`, four deprecated division lemmas,
      `by decide` unusable on `/`-bearing ℚ goals, `native_decide` banned for `Lean.ofReduceBool`)
- [x] Literature rounds 1–1j: `theories/BEP/LITERATURE.md` — owner `literature_researcher`;
      **1587 lines** (measured at the fourth closeout audit), §R1–§R1.19, five `first-hand` families with per-point data (the fifth column is
      aggregate-only and marked `UNSUPPORTED`), the attribution correction (the quadratic law is
      **Marcus 1968 Eq. (2) p. 891**, not 1956), Cohen & Marcus 1968 eqs. (5a)–(5c) as the printed
      regime structure, the naming caveats, and four classical sources kept `not-accessed`
- [x] Human confirmation of the plan (2026-09-20: layout + B1–B5 approved, full scope; instance
      provenance = literature families + model-constructed families, each row labelled)
---

## B1 — description layer (`PhotoLean/BEP/Basic.lean`; owner prover_a; Sprint 1)

- [x] definitions `eact` / `bepLine` / `bepDefect` / `transfer` / `reverseTransfer` / `secSlope`
      / `bepRadius` / `bepBestLine` / `EPBounds` / `EPLinearOn` / `EPExact` / `EPConformsOnWindow`
      / `EPBestOnWindow` / `EPZone` / `epZone` / `EPRegime` / `EPConforms` / `EPDescriptor`
      — Basic.lean — prover_a — done — plan §4.1
- [x] `eact_at_zero` — Basic.lean — prover_a — done — plan §4.2
- [x] `eact_at_lam` — Basic.lean — prover_a — done — plan §4.2
- [x] `eact_zero_lam` — Basic.lean — prover_a — done — plan §4.2
- [x] `transfer_zero_lam` — Basic.lean — prover_a — done — plan §4.2
- [x] `bepLine_at_zero` — Basic.lean — prover_a — done — plan §4.2
- [x] `secSlope_zero_h` — Basic.lean — prover_a — done — plan §4.2
- [x] `epZone_eq_degenerate_iff` — Basic.lean — prover_a — done — plan §4.2
- [x] `epZone_eq_unphysical_iff` — Basic.lean — prover_a — done — plan §4.2
- [x] `epZone_eq_thermoneutral_iff` — Basic.lean — prover_a — done — plan §4.2
- [x] `epZone_eq_exergonic_iff` — Basic.lean — prover_a — done — plan §4.2
- [x] `epZone_eq_endergonic_iff` — Basic.lean — prover_a — done — plan §4.2
- [x] `epZone_eq_atForwardLimit_iff` — Basic.lean — prover_a — done — plan §4.2
- [x] `epZone_eq_atReverseLimit_iff` — Basic.lean — prover_a — done — plan §4.2
- [x] `epZone_eq_beyondForward_iff` — Basic.lean — prover_a — done — plan §4.2
- [x] `epZone_eq_beyondReverse_iff` — Basic.lean — prover_a — done — plan §4.2

## B2 — law layer (`PhotoLean/BEP/Criterion.lean`; owner prover_a; Sprint 2)

- [x] `eact_expansion` — Criterion.lean — prover_a — done — plan §5
- [x] `bepDefect_eq` — Criterion.lean — prover_a — done — plan §5 (central identity)
- [x] `bepLine_exact_at_thermoneutrality` — Criterion.lean — prover_a — done — plan §5
- [x] `bepDefect_at_thermoneutrality` — Criterion.lean — prover_a — done — plan §5
- [x] `transfer_eq_tsCoord` — Criterion.lean — prover_a — done — plan §5 (Leffler/Brønsted bridge)
- [x] `transfer_thermoneutral` — Criterion.lean — prover_a — done — plan §5
- [x] `reverseTransfer_thermoneutral` — Criterion.lean — prover_a — done — plan §5
- [x] `transfer_add_reverse` — Criterion.lean — prover_a — done — plan §5 (Bronsted complementarity)
- [x] `reverseTransfer_eq_transfer_neg` — Criterion.lean — prover_a — done — plan §5
- [x] `secSlope_eq_transfer_mid` — Criterion.lean — prover_a — done — plan §5 (mean-value identity)
- [x] `secSlope_midpoint_invariant` — Criterion.lean — prover_a — done — plan §5
- [x] `eact_neg_eq_add` — Criterion.lean — prover_a — done — plan §5 (barrier reversal)
- [x] `eact_antitone` — Criterion.lean — prover_a — done — plan §5
- [x] `bepDefect_nonneg` — Criterion.lean — prover_a — done — plan §5
- [x] `bepDefect_pos_iff` — Criterion.lean — prover_a — done — plan §5
- [x] `epDescriptor_holds` — Criterion.lean — prover_a — done — plan §5
- [x] `epDescriptor_conforms` — Criterion.lean — prover_a — done — plan §5
- [x] `epConforms_iff_bounds` — Criterion.lean — prover_a — done — plan §5
- [x] `exists_epDescriptor` / non-vacuity suite (`exists_thermoneutral` … `exists_degenerate`)
      — Criterion.lean — prover_a — done — plan §5

## B3 — sharp conditions (`PhotoLean/BEP/Sharp.lean`; owner prover_d; Sprint 3)

- [x] `epBounds_iff_region` — Sharp.lean — prover_d — done — plan §6.1 (critical path)
- [x] `epRegime_iff_strict` — Sharp.lean — prover_d — done — plan §6.1
- [x] `transfer_at_lam` — Sharp.lean — prover_d — done — plan §6.1
- [x] `transfer_at_neg_lam` — Sharp.lean — prover_d — done — plan §6.1
- [x] `not_epBounds_of_lt_neg` — Sharp.lean — prover_d — done — plan §6.1
- [x] `not_epBounds_of_gt` — Sharp.lean — prover_d — done — plan §6.1
- [x] `epExact_iff_degenerate` — Sharp.lean — prover_d — done — plan §6.1
- [x] `not_epLinearOn_of_ne_zero` — Sharp.lean — prover_d — done — plan §6.1
- [x] `exists_conforms_fails` — Sharp.lean — prover_d — done — plan §6.1
- [x] `bepDefect_abs_eq` — Sharp.lean — prover_d — done — plan §6.2
- [x] `epConformsOnWindow_iff_radius` — Sharp.lean — prover_d — done — plan §6.2 (risk: `Real.sqrt`)
- [x] `epConformsOnWindow_at_radius` — Sharp.lean — prover_d — done — plan §6.2
- [x] `epConformsOnWindow_mono` — Sharp.lean — prover_d — done — plan §6.2
- [x] `epConformsOnWindow_symm` — Sharp.lean — prover_d — done — plan §6.2
- [x] `bepDefect_antitone_lam` — Sharp.lean — prover_d — done — plan §6.3
- [x] `bepRadius_mono` — Sharp.lean — prover_d — done — plan §6.3
- [x] `epConformsOnWindow_mono_lam` — Sharp.lean — prover_d — done — plan §6.3
- [x] `bepBestLine_error` — Sharp.lean — prover_d — done — plan §6.4
- [x] `epBestOnWindow_holds` — Sharp.lean — prover_d — done — plan §6.4 (risk: equioscillation)
- [x] `bepLine_worst_case` — Sharp.lean — prover_d — done — plan §6.4
- [x] `bepBestLine_halves` — Sharp.lean — prover_d — done — plan §6.4
- [x] `bepDefect_zero_lam_witness` — Sharp.lean — prover_d — done — plan §6.5
- [x] `bepDefect_neg_lam_witness` — Sharp.lean — prover_d — done — plan §6.5
- [x] `bepDefect_sign_flips` — Sharp.lean — prover_d — done — plan §6.5
- [x] `secSlope_needs_h_ne_zero` — Sharp.lean — prover_d — done — plan §6.5
- [x] AUX minimax block (7 declarations: `epSupError`, `sSup_eq_of_le_of_mem`, `bep_error_three_point`,
      `eact_second_difference`, `epSupError_bddAbove`, `epSupError_bestLine`, `epSupError_sharp`) —
      Sharp.lean — prover_d — done — plan §6.4 + skeleton AUX section

## B4 — microscopic and cross-module layer (`PhotoLean/BEP/Compose.lean`; owner prover_b; Sprint 3)

- [x] `eact_eq_barrier` — Compose.lean — prover_b — done — plan §7
- [x] `rate_eq_exp_neg_eact` — Compose.lean — prover_b — done — plan §7
- [x] `transfer_eq_tsCoord_bridge` — Compose.lean — prover_b — done — plan §7
- [x] `epBounds_iff_no_inverted_direction` — Compose.lean — prover_b — done — plan §7 (Marcus bridge)
- [x] `epBounds_of_reactionRegion` — Compose.lean — prover_b — done — plan §7 (Hammond bridge)
- [x] `epBounds_of_marcus_normal` — Compose.lean — prover_b — done — plan §7
- [x] `epDescriptor_of_microscopic` — Compose.lean — prover_b — done — plan §7
- [x] `bepDefect_le_of_microscopic` — Compose.lean — prover_b — done — plan §7
- [x] `bepRadius_add` — Compose.lean — prover_b — done — plan §7
- [x] `epConformsOnWindow_of_microscopic` — Compose.lean — prover_b — done — plan §7
- [x] `epConformsOnWindow_shrinks_with_inner` — Compose.lean — prover_b — done — plan §7
- [x] `transfer_complementary_microscopic` — Compose.lean — prover_b — done — plan §7
- [x] `secSlope_eq_lefflerSecant` — Compose.lean — prover_b — done — plan §7 post-verification
      addition (verifier M2: the skeleton's 13th B4 declaration had no owner; delivered as a pure
      insertion, `0c86c32`, all twelve verified declarations byte-identical)

## B5a — rational decision layer (`PhotoLean/BEP/RatModel.lean`; owner prover_c; Sprint 2)

- [x] definitions `qEact` / `qBepLine` / `qBepDefect` / `qTransfer` / `qReverseTransfer` / `qSecSlope`
      / `qAlphaObs` / `qLamOfPair` / `qConformsWindow` / `Rat.EPQVerdict` / `Rat.epQVerdict`
      — RatModel.lean — prover_c — done — plan §8.1
- [x] `qEact_cast` — RatModel.lean — prover_c — done — plan §8.1
- [x] `qBepDefect_cast` — RatModel.lean — prover_c — done — plan §8.1
- [x] `qTransfer_cast` — RatModel.lean — prover_c — done — plan §8.1
- [x] `qSecSlope_cast` — RatModel.lean — prover_c — done — plan §8.1
- [x] `qAlphaObs_cast` — RatModel.lean — prover_c — done — plan §8.1
- [x] `qLamOfPair_cast` — RatModel.lean — prover_c — done — plan §8.1
- [x] `qSecSlope_eq_qTransfer_mid` — RatModel.lean — prover_c — done — plan §8.1
- [x] `qAlphaObs_eq_qTransfer_mid` — RatModel.lean — prover_c — done — plan §8.1 (data → structure)
- [x] `qLamOfPair_reconstructs` — RatModel.lean — prover_c — done — plan §8.1 (λ̂ from two points)
- [x] `epQVerdict_conforming_iff` — RatModel.lean — prover_c — done — plan §8.1
- [x] `epQVerdict_boundary_iff` — RatModel.lean — prover_c — done — plan §8.1
- [x] `epQVerdict_superLinear_iff` — RatModel.lean — prover_c — done — plan §8.1
- [x] `epQVerdict_subLinear_iff` — RatModel.lean — prover_c — done — plan §8.1
- [x] `qConformsWindow_iff_radius_sq` — RatModel.lean — prover_c — done — plan §8.1
- [x] `qSecondDividedDiff` / `qModelConsistent3` definitions — RatModel.lean — prover_c — done —
      plan §8.1 (added 2026-09-20 from literature round 1c)
- [x] `qSecondDividedDiff_model` — RatModel.lean — prover_c — done — plan §8.1
- [x] `qModelConsistent3_curvature_pos` — RatModel.lean — prover_c — done — plan §8.1
- [x] `qModelConsistent3_lam_eq` — RatModel.lean — prover_c — done — plan §8.1
- [x] AUX ℝ observation twins `alphaObs` / `lamOfPair` — RatModel.lean — prover_c — done —
      lead decision: they live here and nowhere else
- [x] `qBepLine_cast` — RatModel.lean — prover_c — done — skeleton B5a block (7th cast lemma)
- [x] `qReverseTransfer_cast` — RatModel.lean — lead follow-up (`2556edc`) — done — the only ℚ
      definition left unconstrained by the first delivery; mirrored in the skeleton
- [x] `lamOfPair_reconstructs` — RatModel.lean — prover_c — done — the ℝ counterpart of the ℚ
      reconstruction (skeleton B5a block)
- [x] `qConformsWindow_witness` / `qConformsWindow_negativeControl` — RatModel.lean — prover_c —
      done — the skeleton AUX decision witnesses (positive + negative control)

## B5b — instance verdicts (`PhotoLean/BEP/Instances.lean`; owner prover_c; Sprint 4)

- [x] I1 thermoneutral family (`λ=2, x=0`) — Instances.lean — prover_c — done — plan §8.2
- [x] I2 mildly exergonic (`λ=2, x=1/2`) — Instances.lean — prover_c — done — plan §8.2
- [x] I3 mildly endergonic (`λ=2, x=-1/2`) — Instances.lean — prover_c — done — plan §8.2
- [x] I4 forward barrierless limit (`λ=2, x=2`) — Instances.lean — prover_c — done — plan §8.2
- [x] I5 reverse barrierless limit (`λ=2, x=-2`) — Instances.lean — prover_c — done — plan §8.2
- [x] I6 forward inverted regime (`λ=2, x=3`, α<0) — Instances.lean — prover_c — done — plan §8.2
- [x] I7 reverse inverted regime (`λ=2, x=-3`, α>1) — Instances.lean — prover_c — done — plan §8.2
- [x] I8 degenerate family (`λ=0`) — Instances.lean — prover_c — done — plan §8.2
- [x] I9 unphysical curvature (`λ=-2`) — Instances.lean — prover_c — done — plan §8.2
- [x] I10 tolerance threshold (`λ=2, w=1`) — Instances.lean — prover_c — done — plan §8.2
- [x] I11 four first-hand literature families with per-point data (`LITERATURE.md` §R1.10): per family
      `alphaObs`, `lamHat`, `curvature_negative`, `not_model_consistent` — Instances.lean — prover_c — done —
      plan §8.2 (the fifth family is aggregate-only and deliberately unformalized)
- [x] I12 affine-conforms / model-refuted summary — Instances.lean — prover_c — done — plan §8.2
- [x] `inst_nonvacuous` — Instances.lean — prover_c — done — plan §8.2

---

## Acceptance records (independent verifier runs; the lead ticks from these)

| Batch | Scope | Verdict | Key evidence | Notes |
|---|---|---|---|---|
| B1 (independent verifier #1) | `Basic.lean` (33 declarations) | **PASS** | 33/33 `axioms.sh` clean (raw `depends on axioms: [propext, Classical.choice, Quot.sound]` lines quoted); verifier's own fidelity parser: 33/33 MATCH including the `EPZone` constructors **and** `deriving DecidableEq, Repr`; all nine zone branch boundaries + cascade exhaustiveness kernel-checked; hypothesis necessity over the eight zone-iff premises: **5 load-bearing / 3 decorative** (over *all eleven* premises of this module the verifier proved premise-free strengthened forms of **five**, i.e. 6 load-bearing / 5 decorative — the scope is now stated) (kernel-proved strengthened forms for `epZone_eq_unphysical_iff`, `epZone_eq_exergonic_iff`, `epZone_eq_endergonic_iff`); non-vacuity witnesses for all nine constructors; `#print` bodies == plan §4.1; six falsification attempts all failed; 18/18 commits touch only `Basic.lean` | graded on `sha256 5a366027…`; observations: **O1 HIGH** — the statement authority was untracked and rewritten twice during the run (`f261a131…` → `28300289…`); B1's block was verified identical in both snapshots and against the committed plan §4.1, and the skeleton is now committed by the lead with its hash recorded (plan §3) so the claim is auditable; **O2/O3 MEDIUM** — two self-description wordings ("every physical premise is an hypothesis of the statement that needs it"; `eact_at_zero` "(needs `lam ≠ 0`)") are refuted by the kernel: these hypotheses are kept for signature fidelity, not needed by the statement — comment-only fix **landed** (`90e7f15` / `02a5a54`, the comment-stripped token streams were proven identical **per declaration** by the frozen-state closeout audit itself, both modules re-gated PASS) — the closeout re-check range includes these two commits; **O4–O8 LOW** — five comments describe B2/B3 facts as if proved in this file (reworded with the same batch), the `deriving` clause change was not logged in `API-NOTES.md` (being logged), plan §4.1's `EPBounds` doc block is shorter than the delivered docstring, `bepRadius` is silently `0` for `lam*tol < 0` (unconstrained domain, documented), skeleton layout puts the AUX twins inside the B1 block |
| B5a (independent verifier #4) | `RatModel.lean` (37 = 14 defs + 1 inductive + 22 theorems) | **PASS** | judged on `sha256 75040761…` (skeleton `c9aa2cb1…`); independent fidelity parser 37/37 word-for-word, 0 extras; 22/22 `axioms.sh` clean; the three kernel-counterexample-driven corrections *reproduced* by the verifier (it proved the negations of the premise-dropped forms: `¬` for the `hlam`-free reconstruction, `¬` for the `h₂₃`-free and `h₁₂`-free model-consistency statements); all eight cast lemmas `#print`-checked as genuine ℝ transfers and *used* (not decorative); model-consistency block instantiated with concrete rationals; `qConformsWindow_iff_radius_sq` both directions + negative control (`tol = 1/16`); unconstrained-definition audit: **zero** in the settled state (`qReverseTransfer` was the only one at delivery, fixed by `qReverseTransfer_cast`); all 25 commits touching the file are single-file (24 by `prover_c` plus the lead's follow-up) | observations: **HIGH** — the acceptance anchor must be the hash pair, not a branch name (the window moved under the verifier); **HIGH→closed** — plan→skeleton→delivery were briefly out of sync on `qReverseTransfer_cast`; **MEDIUM** — five premises are decorative (`hh`/`h` on three cast lemmas, `hx` on the two reconstructions) and must not be described as physical guards in `RESULTS.md`; **MEDIUM** — the B5a round's own experience entry is missing (being added); **LOW** — file header says "two corrections" where three are carried; board counts updated to the measured `14 defs + 1 inductive + 22 theorems`; the factor-2 naming difference between `qModelConsistent3_curvature_pos` and `LITERATURE.md` §R1.10.1's `d²Ea/dx² = 1/(2λ)` is now labelled in the record |
| B2 + B4 (independent verifier #2) | `Criterion.lean` (28) + `Compose.lean` (12) | **PASS / PASS** | 40/40 `axioms.sh` clean (raw lines quoted); verifier's own parser: B2 28/28 word-for-word, B4 12/12; 40/40 proof terms screened for circularity (**only two `rfl`s, both documented as definitional**: `eact_eq_barrier`, `rate_eq_exp_neg_eact`); 20 hypothesis-necessity counterexamples (load-bearing vs decorative split reported); `secSlope_eq_transfer_mid` hand-recomputed at three rational parameter sets (mean-value convention confirmed); B4 row 4 non-vacuous with same-true/same-false witnesses for both directions; a ~7 200-instance rational grid falsification of 31 statements found **0 counterexamples**; 28/28 + 12/12 commits touch only the owner's file | graded on `sha256 b3ef9225…` / `b68e948c…`; observations: **M1** skeleton untracked and rewritten mid-run (fixed: authority now committed), **M2** the skeleton's B4 AUX `secSlope_eq_lefflerSecant` was not delivered anywhere (fixed: `prover_b` is adding it, post-verification addition marked in the header), **M3** EXPERIENCE.md lacked the B2/B4 proof-round entries at verification time (fixed: committed), **M4** λ-additivity is an unregistered physical premise (registered in plan §13), **M5** positivity sits in the conformance predicates by design (registered in plan §13; wording fixed with the comment-only batch); **LOW 1–6** wording/registration items (comment-only fixes queued; junk files in the repo root removed by the lead) |
| B3 (independent verifier #3) | `Sharp.lean` (32 = 25 + 7 AUX) | **PASS** | graded on `sha256 b9b3b568…` (skeleton `c9aa2cb1…`, `Basic.lean` `19133be2…`); 32/32 `axioms.sh` clean; verifier's own parser: set equality 32/32, 0 mismatches, plus the `epSupError` *body* compared; the minimax lower bound **is** the original `∀ c a, ∃ x ∈ Set.Icc (-w) w` form — `#print` of `EPBestOnWindow` confirms the pre-registered disjunctive fallback was not used — and is non-vacuous at two affine functions; the radius theorem checked in both directions with a strict-interior case, a failing-window case and the attained radius; `a < b` shown load-bearing (a single point *is* trivially affine); 11 hypothesis-necessity counterexamples; the four sharpness witnesses are the totalised-division values and `secSlope_needs_h_ne_zero` genuinely kills the B2 mean-value identity; anti-circularity: every load-bearing proof is a real derivation (no `rfl`), `Sharp.lean` imports only `Basic.lean` and re-derives the B2 identity locally (duplication, not circularity); edge-value falsification (w=0, tol=0, x=±λ, w<0, tol<0, lam<0, empty window) left every statement standing | observations: **HIGH-1** the acceptance window moved under the verifier (a concurrent comment-only `Basic.lean` commit; token streams proven identical and all gates re-run) — the anchor is the hash triple recorded here; **MEDIUM-1** one further decorative premise (`hw : 0 ≤ w` of `epConformsOnWindow_iff_radius`, kernel-strengthened by the verifier) to be disclosed in the file header — comment-only fix queued; **MEDIUM-2** plan §3 now carries the authority hash (it was claimed but missing); **LOW-1…5** the §6.5 header claim is wider than the four delivered witnesses, the board "(8 declarations)" typo corrected to 7, the B3 experience entry is being written, and the model assumptions are restated as *model* premises (not theorem premises) in `RESULTS.md` |
| B5b (independent verifier #5) | `Instances.lean` (48) | **PASS** | graded on `sha256 99161212…` (unchanged start→end; `RatModel.lean` `75040761…` = the B5a anchor); 48/48 `axioms.sh` clean; verifier's own parser: 48/48 word-for-word, order identical, 0 missing/extras; **all verdicts independently recomputed**: I1–I10 coefficients, the six-branch cascade and the I10 threshold (`tol = 1/8` conforms at the boundary, `1/16` fails, `w* = 1`); the 12 I11 literals recomputed from §R1.10's printed kcal/mol rows (four negative curvatures); the refutation rows' derivation checked non-circular; `#print` shows real `norm_num` terms and a real existential refutation; `inst_nonvacuous` exhibits two distinct verdicts; F4 absent with no invented numbers; a ±half-unit perturbation grid over every printed value flips **no** verdict (no knife-edge rows); 48/48 commits touch only the owner's file | observations: **MEDIUM-1** 12 of the 16 I11 docstrings do not repeat source/locus/status per theorem (they are contiguous under fully-provenanced family headings) — comment-only fix queued; **MEDIUM-2** the plan's "at least one conforming literature family" cannot be met with §R1.10 as printed (all four formalized families are model-refuted) — plan and `RESULTS.md` now state the affine-vs-model split instead of pretending the requirement was met; **MEDIUM-3** the pair/triple selection and the pair-dependence of `λ̂` are disclosed in plan §8.2 and are being added to the file; **LOW-4…8** I1–I9 header shorthand, one stale docstring claim about the plan's I8 cell (the plan is correct), the I9 strictness remark kept as prose, plan prose reconciled to "five families, four formalized" |
| Frozen-state closeout, first run | whole tree | **FAIL (documentation only)** | gate PASS twice, 191/191 `axioms.sh` clean, statement fidelity 191/191, comment-only deltas confirmed per declaration, kernel spot-checks clean — but eight documentation findings (I9 `α` conflated with the two-point slope; `276` vs the checker's `280`; `167` vs `164` lemma commits; the plan's `R² ≈ 0.93–0.95` against the record's own F2 = `0.548`; a reproduction command naming the wrong module; `24/24` vs `25`; plan text claiming a closeout record that did not exist; stale board status/counts) | the FAIL is preserved on purpose; corrections in commits `ff62528`, `159644c`, `0c74c71` |
| Frozen-state closeout, second run | whole tree | **FAIL (documentation only)** | mathematics re-verified independently (191/191 axioms, 191/191 fidelity, 34/34 definition bodies, comment-only deltas per declaration, `checked 280`, all kernel probes and falsification controls as expected, anchors identical start→end) — but residual documentation findings: this table still carried the three draft rows below and this row; the string `rate_exp` named a theorem that never existed; `EXPERIENCE.md` said `R² = 0.93–0.95 in four of five` where the record gives `0.934 / 0.548 / 0.934 / 0.952` (F2 the printed exception, F5 not reported); `RESULTS.md` §5 claimed `re-checked → PASS` before the re-check existed; two unit/wording LOW items | the FAIL is preserved on purpose; corrections recorded in this file, `theories/BEP/RESULTS.md` §5 and `proofs/EXPERIENCE.md` |
| Frozen-state closeout, third run | whole tree | **FAIL (documentation only)** | mathematics re-verified independently (from-source re-elaboration of all six modules 0 error/0 warning; 191/191 `axioms.sh`; 191/191 fidelity with 34/34 definition bodies; per-declaration comment-stripped token identity against every graded blob plus Compose's single added declaration; `checked 280`; 11 fresh kernel probes; an independent 608 266-point rational grid with 0 counterexamples; anchors identical start→end, `git status` clean) — but five documentation findings: (1) this file's status line and (2) the plan header claimed a closeout **PASS** that does not exist (only FAIL rows do), (3) the plan header recorded only the first run and omitted the second, (4) `LITERATURE.md` §R1.10.6 still said "in four of five families … R² = 0.93–0.95" where the record's own sections give `0.934 / 0.548 / 0.934 / 0.952` (three families, one printed exception, F5 unreported), (5) `RESULTS.md` §4's `13/16` was labelled "the two-point observable slope at the sample points" without naming the pair | the FAIL is preserved on purpose; all five corrected in this file, `theories/BEP/plan.md`, `theories/BEP/RESULTS.md` and `theories/BEP/LITERATURE.md` (lead correction note) |

## Notes and conflict log

- **Observation queue closed (2026-09-20)**: all verifier observations that named a file were fixed by
  the file's owner with comment-only edits and a token-stream gate — `Sharp.lean` (`bff7cfa`: the
  fourth decorative premise `hw : 0 ≤ w` disclosed, §6.5 header claim tightened; new raw hash
  `a874ce82…`, stripped token stream unchanged `815e9a36…`), `Instances.lean` (`a6f5402`, `16e3ae3`,
  `b4107ec`, `eae9bb8`: per-row provenance, selection disclosure, the stale I8 docstring corrected,
  header/wording fixes; new raw hash `029b02a3…`, stripped token stream unchanged `b68b010f…`),
  `Basic.lean`/`Criterion.lean` (`90e7f15`, `02a5a54`, stripped hashes unchanged `d2898dc4…` /
  `4a4eacda…`), plus the B3 experience entry (`8773775`) and the B5b one (`f4676c0`). One factual
  wording error of the lead's was caught in the process and corrected: `λ̂` is **pair-dependent**
  (negative on many documented pairs, but **positive** on the F5 abscissa-widest pair), not
  "negative on the widest pairs" — plan §8.2 and `RESULTS.md` §4 now carry the reproducible values.
- **Statement authority is now under version control (verifier O1, lead action 2026-09-20)**: the
  whole `theories/BEP/probes/` directory (skeleton, API probes, risk probe, fidelity and
  instance-cross-check scripts, prover scratch calibrations) is committed; the skeleton's hash is
  recorded in `theories/BEP/plan.md` §3. A future "matched the frozen authority" claim is
  therefore auditable, which it was not while the file was untracked.

- **Plan addition from literature round 1c (2026-09-20, lead)**: the five first-hand families in
  `LITERATURE.md` §R1.10 have good affine BEP fits but a **negative** second divided difference in
  every family, while the model with `λ > 0` forces `1/(4λ) > 0`. Plan §8.1 gained
  `qSecondDividedDiff` / `qModelConsistent3` / `qSecondDividedDiff_model` /
  `qModelConsistent3_curvature_pos` / `qModelConsistent3_lam_eq`, and §8.2 gained the I11/I12 rows
  that turn this into a theorem: the affine description survives, the equal-curvature two-parabola
  model is refuted as a family-level description of those data.

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
