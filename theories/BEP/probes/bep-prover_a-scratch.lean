/-
BEP milestone B2 — prover_a scratch calibration probe (NOT a delivered artifact).

Purpose: statement-first calibration for `PhotoLean/BEP/Criterion.lean`. The statements below are
copied verbatim from `theories/BEP/probes/bep-statement-skeleton.lean` (B2 block, = plan §5 rows
1–20 + the non-vacuity suite) and their proofs are developed here before delivery. This directory
is outside the strict scan range (`SOURCE_DIRS="PhotoLean"`).

B1 (`PhotoLean/BEP/Basic.lean`) is delivered and gates-clean; the local copies of the B1
definitions that the previous revision of this file carried are gone — it now imports them.

Running:  proofs/scripts/lake env lean theories/BEP/probes/bep-prover_a-scratch.lean
-/
import Mathlib
import PhotoLean.BEP.Basic

namespace PhotoLean.BEP

/-! ## Recorded B1 counterexample (kept as evidence for the corrected plan §4.2 row 4) -/

/-- The old row-4 statement `transfer 0 x = 0` is false for the delivered linear-response body. -/
theorem transfer_zero_lam_old_form_is_false (x : ℝ) : transfer 0 x ≠ 0 := by
  unfold transfer
  norm_num

/-! ## API probes for the B2 recipes (names taken from `proofs/API-NOTES.md`) -/

#check @div_lt_div_iff_of_pos_right
#check @sq_lt_sq₀
#check @sq_pos_of_ne_zero
#check @pow_lt_pow_left₀
#check @div_pos
#check @div_nonneg

/-! ## B2 — the law layer (plan §5) -/

/-- Plan §5 #1. -/
theorem eact_expansion {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    eact lam x = lam / 4 - x / 2 + x ^ 2 / (4 * lam) := by
  unfold eact
  field_simp
  ring

/-- Plan §5 #2. -/
theorem bepDefect_eq {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    bepDefect lam x = x ^ 2 / (4 * lam) := by
  unfold bepDefect bepLine eact
  field_simp
  ring

/-- Plan §5 #3. -/
theorem bepLine_exact_at_thermoneutrality {lam : ℝ} (hlam : lam ≠ 0) :
    bepLine lam 0 = eact lam 0 := by
  rw [eact_at_zero hlam]
  unfold bepLine
  ring

/-- Plan §5 #4. -/
theorem bepDefect_at_thermoneutrality {lam : ℝ} (hlam : lam ≠ 0) : bepDefect lam 0 = 0 := by
  rw [bepDefect_eq hlam]
  ring

/-- Plan §5 #5: the Leffler/Brønsted identification (the linear-response body equals the
transition-state coordinate). -/
theorem transfer_eq_tsCoord {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    transfer lam x = (lam - x) / (2 * lam) := by
  unfold transfer
  field_simp

/-- Plan §5 #6. -/
theorem transfer_thermoneutral (lam : ℝ) : transfer lam 0 = 1 / 2 := by
  unfold transfer
  norm_num

/-- Plan §5 #7. -/
theorem reverseTransfer_thermoneutral (lam : ℝ) : reverseTransfer lam 0 = 1 / 2 := by
  unfold reverseTransfer
  norm_num

/-- Plan §5 #8: Brønsted complementarity. -/
theorem transfer_add_reverse {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    transfer lam x + reverseTransfer lam x = 1 := by
  unfold transfer reverseTransfer
  field_simp
  ring

/-- Plan §5 #9. -/
theorem reverseTransfer_eq_transfer_neg (lam x : ℝ) : reverseTransfer lam x = transfer lam (-x) := by
  unfold reverseTransfer transfer
  ring

/-- Plan §5 #10: the mean-value identity of the parabola. -/
theorem secSlope_eq_transfer_mid {lam : ℝ} (hlam : lam ≠ 0) {x h : ℝ} (hh : h ≠ 0) :
    secSlope lam x h = transfer lam (x + h / 2) := by
  unfold secSlope transfer eact
  field_simp
  ring

/-- Plan §5 #11: the observed slope depends only on the midpoint of the observed window. -/
theorem secSlope_midpoint_invariant {lam x y h k : ℝ} (hlam : lam ≠ 0) (hh : h ≠ 0) (hk : k ≠ 0)
    (hmid : x + h / 2 = y + k / 2) : secSlope lam x h = secSlope lam y k := by
  rw [secSlope_eq_transfer_mid hlam hh, secSlope_eq_transfer_mid hlam hk, hmid]

/-- Plan §5 #12: barrier-reversal identity. -/
theorem eact_neg_eq_add {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) : eact lam (-x) = eact lam x + x := by
  unfold eact
  field_simp
  ring

/-- Plan §5 #13: monotonicity on the normal-region side of the parabola. -/
theorem eact_antitone {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h₁ : x₁ < x₂) (h₂ : x₂ ≤ lam) :
    eact lam x₂ < eact lam x₁ := by
  have h4 : (0 : ℝ) < 4 * lam := by linarith
  have h0 : 0 ≤ lam - x₂ := by linarith
  have h01 : 0 ≤ lam - x₁ := by linarith
  have hlt : lam - x₂ < lam - x₁ := by linarith
  unfold eact
  rw [div_lt_div_iff_of_pos_right h4]
  exact (sq_lt_sq₀ h0 h01).2 hlt

/-- Plan §5 #14. -/
theorem bepDefect_nonneg {lam x : ℝ} (hlam : 0 < lam) : 0 ≤ bepDefect lam x := by
  rw [bepDefect_eq (ne_of_gt hlam)]
  exact div_nonneg (sq_nonneg x) (by positivity)

/-- Plan §5 #15. -/
theorem bepDefect_pos_iff {lam x : ℝ} (hlam : 0 < lam) : 0 < bepDefect lam x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    rw [hx, bepDefect_at_thermoneutrality (ne_of_gt hlam)] at h
    exact lt_irrefl 0 h
  · intro hx
    rw [bepDefect_eq (ne_of_gt hlam)]
    exact div_pos (sq_pos_of_ne_zero hx) (by positivity)

/-- Plan §5 #16. -/
theorem epDescriptor_holds {lam : ℝ} (hlam : 0 < lam) : EPDescriptor lam := by
  exact ⟨hlam, fun x => bepDefect_eq (ne_of_gt hlam) x⟩

/-- Plan §5 #17. -/
theorem epDescriptor_conforms {lam x : ℝ} (h : EPDescriptor lam) (hx : x ≠ 0) :
    0 < bepDefect lam x := by
  obtain ⟨hpos, hdef⟩ := h
  rw [hdef x]
  exact div_pos (sq_pos_of_ne_zero hx) (by positivity)

/-- Plan §5 #18. -/
theorem epConforms_iff_bounds {lam x : ℝ} (hlam : 0 < lam) :
    EPConforms lam x ↔ EPBounds lam x := by
  unfold EPConforms
  exact ⟨fun h => h.2, fun h => ⟨hlam, h⟩⟩

/-- Plan §5 #19. -/
theorem exists_epDescriptor : ∃ lam : ℝ, EPDescriptor lam := by
  exact ⟨1, epDescriptor_holds (by norm_num)⟩

/-! ## Plan §5 #20–26 — non-vacuity of the nine regimes -/

/-- The thermoneutral regime is inhabited. -/
theorem exists_thermoneutral : ∃ lam x : ℝ, epZone lam x = EPZone.thermoneutral := by
  refine ⟨1, 0, ?_⟩
  unfold epZone
  norm_num

/-- The exergonic regime is inhabited. -/
theorem exists_exergonic : ∃ lam x : ℝ, epZone lam x = EPZone.exergonic := by
  refine ⟨1, 1 / 2, ?_⟩
  unfold epZone
  norm_num

/-- The endergonic regime is inhabited. -/
theorem exists_endergonic : ∃ lam x : ℝ, epZone lam x = EPZone.endergonic := by
  refine ⟨1, -(1 / 2), ?_⟩
  unfold epZone
  norm_num

/-- The forward barrierless limit is inhabited. -/
theorem exists_atForwardLimit : ∃ lam x : ℝ, epZone lam x = EPZone.atForwardLimit := by
  refine ⟨1, 1, ?_⟩
  unfold epZone
  norm_num

/-- The reverse barrierless limit is inhabited. -/
theorem exists_atReverseLimit : ∃ lam x : ℝ, epZone lam x = EPZone.atReverseLimit := by
  refine ⟨1, -1, ?_⟩
  unfold epZone
  norm_num

/-- The inverted forward region is inhabited. -/
theorem exists_beyondForward : ∃ lam x : ℝ, epZone lam x = EPZone.beyondForward := by
  refine ⟨1, 2, ?_⟩
  unfold epZone
  norm_num

/-- The inverted reverse region is inhabited. -/
theorem exists_beyondReverse : ∃ lam x : ℝ, epZone lam x = EPZone.beyondReverse := by
  refine ⟨1, -2, ?_⟩
  unfold epZone
  norm_num

/-- The unphysical-curvature regime is inhabited. -/
theorem exists_unphysical : ∃ lam x : ℝ, epZone lam x = EPZone.unphysical := by
  refine ⟨-1, 0, ?_⟩
  unfold epZone
  norm_num

/-- The degenerate regime is inhabited. -/
theorem exists_degenerate : ∃ lam x : ℝ, epZone lam x = EPZone.degenerate := by
  refine ⟨0, 0, ?_⟩
  unfold epZone
  norm_num

/-! ## Measured failures of this milestone (kept as evidence; do not retry)

The failing attempts below were compiled as `example`s in a separate throwaway probe (run with
`proofs/scripts/lake env lean`), not in this file: a calibration artifact that does not compile
cannot be the statement-first evidence. Exact outcomes:

* `eact_antitone` (plan §5 #13) — the plan's sketch is `nlinarith`. Measured:
  - `unfold eact; nlinarith` → `error: linarith failed to find a contradiction`, stuck at
    `(lam - x₂) ^ 2 / (4 * lam) ≥ (lam - x₁) ^ 2 / (4 * lam) ⊢ False`;
  - the same with explicit hints `nlinarith [hlam, h₁, h₂, sq_nonneg (lam - x₂),
    sq_nonneg (lam - x₁)]` → identical failure: the division by `4 * lam` is opaque to the
    lineariser and the goal is a genuine product comparison.
  Recipe that works (two lines): `rw [div_lt_div_iff_of_pos_right (by linarith : (0:ℝ) < 4*lam)]`
  then `exact (sq_lt_sq₀ h0 h01).2 hlt` (names archived in `proofs/API-NOTES.md`, C group).
* Non-vacuity suite — `decide` is not available on the ℝ-side classifier:
  - `example : epZone 1 0 = EPZone.thermoneutral := by decide` → `tactic 'decide' failed for
    proposition … since its 'Decidable' instance … did not reduce to 'isTrue' or 'isFalse'`
    (reduction gets stuck at `Real.decidableEq`);
  - `unfold epZone; decide` → the same failure on the unfolded cascade.
  Recipe that works for all nine witnesses: `refine ⟨…, …, ?_⟩; unfold epZone; norm_num`.
* `transfer_eq_tsCoord` — `unfold transfer; field_simp; ring` → `error: no goals to be solved`:
  after clearing the denominator `2 * lam`, `field_simp` closes the polynomial identity itself.
  Stop after `field_simp` (same shape as `eact_at_lam` in B1).
-/

end PhotoLean.BEP
