/-
theories/BEP/probes/bep-prover_b-scratch.lean

Scratch calibration + proof-development file for milestone B4 (`PhotoLean/BEP/Compose.lean`,
owner `prover_b`). Lives outside `SOURCE_DIRS` (the strict scan range), so it is a probe and not a
deliverable: it exists to (a) `#check` every cross-module and mathlib name before it is used in the
deliverable, and (b) develop the twelve B4 proofs before transcribing them one lemma per commit.

Statement authority: `theories/BEP/probes/bep-statement-skeleton.lean`, B4 block (plan §7); the
statements below are copied from it verbatim so that a disagreement shows up as an elaboration
error rather than as a silent re-formulation.
-/
import Mathlib
import PhotoLean.BEP.Basic
import PhotoLean.Marcus.Basic
import PhotoLean.Hammond.Basic

/-! ## 1. Cross-module and mathlib API calibration (`#check` before use) -/

-- cross-module names required by plan §7 (Marcus / Hammond bridges)
#check @PhotoLean.Marcus.barrier
#check @PhotoLean.Marcus.rate
#check @PhotoLean.Marcus.InvertedRegion
#check @PhotoLean.Marcus.NormalRegion
#check @PhotoLean.Hammond.tsCoord
#check @PhotoLean.Hammond.ReactionRegion

-- mathlib names planned for rows 4-11
#check @sq_le_sq
#check @abs_le
#check @div_le_iff₀
#check @le_div_iff₀
#check @div_le_div_of_nonneg_left
#check @div_le_div_of_nonneg_right
#check @mul_le_mul_of_nonneg_right
#check @Real.sq_sqrt
#check @Real.sqrt_le_sqrt
#check @Real.sqrt_nonneg
#check @Real.le_sqrt
#check @sq_pos_of_ne_zero
#check @Set.right_mem_Icc
#check @Set.mem_Icc

namespace PhotoLean.BEP.Scratch

open PhotoLean.BEP

noncomputable section

/-! ## 2. B4 rows 1-2: definitional bridges -/

/-- Plan §7 #1. -/
theorem eact_eq_barrier (lam x : ℝ) : eact lam x = Marcus.barrier lam x := rfl

/-- Plan §7 #2. -/
theorem rate_eq_exp_neg_eact (A lam kB T x : ℝ) :
    Marcus.rate A lam kB T x = A * Real.exp (-(eact lam x) / (kB * T)) := rfl

/-! ## 3. B4 row 3: the Brønsted/Leffler bridge -/

/-- Plan §7 #3. -/
theorem transfer_eq_tsCoord_bridge {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    transfer lam x = Hammond.tsCoord lam x := by
  unfold transfer Hammond.tsCoord
  field_simp

/-! ## 4. B4 rows 4-6: the inverted-region / region bridges -/

/-- Plan §7 #4 (headline). -/
theorem epBounds_iff_no_inverted_direction {lam x : ℝ} (hlam : 0 < lam) :
    EPBounds lam x ↔ ¬ (Marcus.InvertedRegion lam x ∨ Marcus.InvertedRegion lam (-x)) := by
  have h2 : 0 < 2 * lam := by linarith
  unfold EPBounds transfer Marcus.InvertedRegion
  constructor
  · rintro ⟨h1, h3⟩
    simp only [not_or, not_lt]
    constructor
    · have := (div_le_iff₀ h2).mp (show x / (2 * lam) ≤ 1 / 2 by linarith)
      linarith
    · have := (le_div_iff₀ h2).mp (show -(1 / 2) ≤ x / (2 * lam) by linarith)
      linarith
  · intro h
    simp only [not_or, not_lt] at h
    obtain ⟨h1, h3⟩ := h
    constructor
    · have : x / (2 * lam) ≤ 1 / 2 := (div_le_iff₀ h2).mpr (by linarith)
      linarith
    · have : -(1 / 2) ≤ x / (2 * lam) := (le_div_iff₀ h2).mpr (by linarith)
      linarith

/-- Plan §7 #5. -/
theorem epBounds_of_reactionRegion {lam x : ℝ} (hlam : 0 < lam)
    (h : Hammond.ReactionRegion lam x) : EPBounds lam x := by
  rw [epBounds_iff_no_inverted_direction hlam]
  simp only [Marcus.InvertedRegion, Hammond.ReactionRegion, not_or, not_lt] at h ⊢
  exact ⟨le_of_lt h.2, by linarith⟩

/-- Plan §7 #6. -/
theorem epBounds_of_marcus_normal {lam x : ℝ} (hlam : 0 < lam) (h : Marcus.NormalRegion lam x)
    (hx : -lam ≤ x) : EPBounds lam x := by
  rw [epBounds_iff_no_inverted_direction hlam]
  simp only [Marcus.InvertedRegion, Marcus.NormalRegion, not_or, not_lt] at h ⊢
  exact ⟨le_of_lt h, by linarith⟩

/-! ## 5. B4 rows 7-12: microscopic composition (local algebra; `Sharp.lean` not imported) -/

/-- Plan §7 #7. -/
theorem epDescriptor_of_microscopic {lamInner lamOuter : ℝ} (hli : 0 < lamInner)
    (hlo : 0 < lamOuter) : EPDescriptor (lamInner + lamOuter) := by
  have hL : 0 < lamInner + lamOuter := by linarith
  refine ⟨hL, ?_⟩
  intro x
  unfold bepDefect eact bepLine
  field_simp
  ring

/-- Plan §7 #8. -/
theorem bepDefect_le_of_microscopic {lamInner lamOuter x : ℝ} (hli : 0 < lamInner)
    (hlo : 0 < lamOuter) (hx : x ≠ 0) :
    bepDefect (lamInner + lamOuter) x ≤ bepDefect lamInner x := by
  have hL : 0 < lamInner + lamOuter := by linarith
  have key : ∀ L : ℝ, L ≠ 0 → bepDefect L x = x ^ 2 / (4 * L) := by
    intro L hL0
    unfold bepDefect eact bepLine
    field_simp
    ring
  rw [key (lamInner + lamOuter) (ne_of_gt hL), key lamInner (ne_of_gt hli)]
  exact div_le_div_of_nonneg_left (le_of_lt (sq_pos_of_ne_zero hx)) (by linarith) (by linarith)

set_option linter.unusedVariables false in
/-- Plan §7 #9. -/
theorem bepRadius_add {lamInner lamOuter tol : ℝ} (hli : 0 ≤ lamInner) (hlo : 0 ≤ lamOuter)
    (htol : 0 ≤ tol) : bepRadius lamInner tol ≤ bepRadius (lamInner + lamOuter) tol := by
  unfold bepRadius
  have hmul : lamInner * tol ≤ (lamInner + lamOuter) * tol :=
    mul_le_mul_of_nonneg_right (by linarith) htol
  have hsqrt := Real.sqrt_le_sqrt hmul
  linarith

/-- Plan §7 #10. -/
theorem epConformsOnWindow_of_microscopic {lamInner lamOuter tol w : ℝ} (hli : 0 < lamInner)
    (hlo : 0 < lamOuter) (htol : 0 < tol) (hw : w ≤ bepRadius (lamInner + lamOuter) tol) :
    EPConformsOnWindow (lamInner + lamOuter) tol (-w) w := by
  have hL : 0 < lamInner + lamOuter := by linarith
  have h4 : (0 : ℝ) < 4 * (lamInner + lamOuter) := by linarith
  have hprod : 0 ≤ (lamInner + lamOuter) * tol := mul_nonneg (le_of_lt hL) (le_of_lt htol)
  have htwo : 0 ≤ 2 * Real.sqrt ((lamInner + lamOuter) * tol) := by positivity
  have hsq : (2 * Real.sqrt ((lamInner + lamOuter) * tol)) ^ 2
      = 4 * ((lamInner + lamOuter) * tol) := by
    rw [mul_pow, Real.sq_sqrt hprod]
    norm_num
  have key : ∀ L x : ℝ, L ≠ 0 → bepDefect L x = x ^ 2 / (4 * L) := by
    intro L x hL0
    unfold bepDefect eact bepLine
    field_simp
    ring
  refine ⟨hL, htol, ?_⟩
  intro x hx
  rcases le_or_lt 0 w with hw0 | hwn
  · have hrad : w ^ 2 / (4 * (lamInner + lamOuter)) ≤ tol := by
      rw [bepRadius] at hw
      rw [div_le_iff₀ h4]
      calc w ^ 2 ≤ (2 * Real.sqrt ((lamInner + lamOuter) * tol)) ^ 2 := by
            rw [sq_le_sq, abs_of_nonneg hw0, abs_of_nonneg htwo]
            exact hw
        _ = tol * (4 * (lamInner + lamOuter)) := by rw [hsq]; ring
    have hx2 : x ^ 2 ≤ w ^ 2 := by
      rw [Set.mem_Icc] at hx
      have habs : |x| ≤ w := abs_le.mpr hx
      rw [sq_le_sq, abs_of_nonneg hw0]
      exact habs
    rw [key (lamInner + lamOuter) x (ne_of_gt hL), abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ h4]
    rw [div_le_iff₀ h4] at hrad
    linarith
  · exfalso
    rw [Set.mem_Icc] at hx
    linarith [hx.1, hx.2]

/-- Plan §7 #11. -/
theorem epConformsOnWindow_shrinks_with_inner {lamInner lamOuter tol w : ℝ} (hli : 0 < lamInner)
    (hlo : 0 < lamOuter) (htol : 0 < tol) :
    EPConformsOnWindow lamInner tol (-w) w → EPConformsOnWindow (lamInner + lamOuter) tol (-w) w := by
  intro h
  have hL : 0 < lamInner + lamOuter := by linarith
  have key : ∀ L x : ℝ, L ≠ 0 → bepDefect L x = x ^ 2 / (4 * L) := by
    intro L x hL0
    unfold bepDefect eact bepLine
    field_simp
    ring
  refine ⟨hL, htol, ?_⟩
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [key (lamInner + lamOuter) 0 (ne_of_gt hL)]
    simpa using le_of_lt htol
  · have hmono : |bepDefect (lamInner + lamOuter) x| ≤ |bepDefect lamInner x| := by
      rw [key (lamInner + lamOuter) x (ne_of_gt hL), key lamInner x (ne_of_gt hli),
        abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_left (le_of_lt (sq_pos_of_ne_zero hx0)) (by linarith) (by linarith)
    exact le_trans hmono (h.2.2 x hx)

set_option linter.unusedVariables false in
/-- Plan §7 #12. -/
theorem transfer_complementary_microscopic {lamInner lamOuter x : ℝ}
    (hlam : lamInner + lamOuter ≠ 0) :
    transfer (lamInner + lamOuter) x + reverseTransfer (lamInner + lamOuter) x = 1 := by
  unfold transfer reverseTransfer
  ring

end

end PhotoLean.BEP.Scratch
