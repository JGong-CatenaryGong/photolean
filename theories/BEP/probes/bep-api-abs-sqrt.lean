/-
BEP milestone — API probe (topic B): absolute value, intervals, square roots, order.

Scope. The tolerance window of the BEP law (plan §6.2 #11) is the statement
`EPConformsOnWindow lam tol (-w) w ↔ w ≤ bepRadius lam tol`; this probe calibrates (i) `abs_le` /
`abs_of_nonneg` and the interval membership API, (ii) the `Real.sqrt_*` family that turns
`w^2 ≤ 4*lam*tol` into `w ≤ 2*√(lam*tol)`, (iii) the division/order lemmas behind
`epBounds_iff_region` and `epRegime_iff_strict` with the **linear-response** body of `transfer`
(plan §4.1), (iv) the λ-monotonicity rows of plan §6.3. Every item carries a kernel-checked proof.

Running:  proofs/scripts/lake env lean theories/BEP/probes/bep-api-abs-sqrt.lean
Status:   0 errors / 0 warnings.
-/
import Mathlib

namespace PhotoLean.BEP.ProbeAbsSqrt

/-! ## Local copies of the B1 definitions (plan §4.1 / statement skeleton) -/

noncomputable def eact (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)
noncomputable def bepLine (lam x : ℝ) : ℝ := lam / 4 - x / 2
noncomputable def bepDefect (lam x : ℝ) : ℝ := eact lam x - bepLine lam x
noncomputable def transfer (lam x : ℝ) : ℝ := 1 / 2 - x / (2 * lam)
noncomputable def bepRadius (lam tol : ℝ) : ℝ := 2 * Real.sqrt (lam * tol)

def EPBounds (lam x : ℝ) : Prop := 0 ≤ transfer lam x ∧ transfer lam x ≤ 1
def EPRegime (lam x : ℝ) : Prop := -lam < x ∧ x < lam
def EPConformsOnWindow (lam tol a b : ℝ) : Prop :=
  0 < lam ∧ 0 < tol ∧ ∀ x ∈ Set.Icc a b, |bepDefect lam x| ≤ tol

/-! ## `#check` — absolute value and intervals -/

#check @abs_le
#check @abs_le'
#check @abs_of_nonneg
#check @abs_of_pos
#check @abs_of_neg
#check @abs_add
#check @abs_neg
#check @abs_nonneg
#check @le_abs_self
#check @neg_le_abs
#check @abs_sub_comm
#check @abs_mul
#check @abs_div
#check @abs_sq
#check @sq_abs
#check @Set.mem_Icc
#check @Set.left_mem_Icc
#check @Set.right_mem_Icc
#check @Set.Icc
#check @Set.Icc_subset_Icc_iff
#check @neg_le
#check @le_neg
#check @sq_le_sq
#check @sq_le_sq'
#check @sq_nonneg
#check @add_le_add
#check @pow_le_pow_left₀
#check @not_or
#check @not_le

/-! ## `#check` — square roots -/

#check @Real.sqrt_sq_eq_abs
#check @Real.sqrt_sq
#check @Real.sq_sqrt
#check @Real.sqrt_mul_self
#check @Real.mul_self_sqrt
#check @Real.sqrt_nonneg
#check @Real.sqrt_pos
#check @Real.sqrt_le_iff
#check @Real.le_sqrt
#check @Real.le_sqrt'
#check @Real.sqrt_le_sqrt
#check @Real.sqrt_lt_sqrt
#check @Real.lt_sqrt
#check @Real.sqrt_le_sqrt_iff
#check @Real.sqrt_mul
#check @Real.sqrt_zero
#check @Real.sqrt_one
#check @Real.sqrt_eq_zero_of_nonpos

/-! ## `#check` — division and order -/

#check @div_nonneg
#check @div_pos
#check @div_nonneg_iff
#check @div_pos_iff_of_pos_right
#check @div_le_div_of_nonneg_right
#check @div_le_div_of_nonneg_left
#check @div_le_div_iff₀
#check @div_lt_div_iff₀
#check @div_le_div_iff_of_pos_right
#check @div_le_iff₀
#check @le_div_iff₀
#check @div_le_one
#check @div_lt_one
#check @one_le_div
#check @mul_le_mul_of_nonneg_left
#check @mul_le_mul_of_nonneg_right
#check @div_ne_zero

/-! ## A worked sqrt computation (the shape the radius theorem needs) -/

/-- `√(4 * (lam * tol)) = 2 * √(lam * tol)`; the recipe is `Real.sqrt_mul` (nonnegative factor
first) and then `Real.sqrt_sq` on `√4 = 2` (`Real.sqrt_four` does **not** exist). -/
example (lam tol : ℝ) : Real.sqrt (4 * (lam * tol)) = 2 * Real.sqrt (lam * tol) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]

/-- The `√x ≤ y ↔ x ≤ y^2` route of `Real.sqrt_le_iff` (no side conditions). -/
example (t : ℝ) : Real.sqrt t ≤ 4 ↔ t ≤ 16 := by
  rw [Real.sqrt_le_iff]
  constructor
  · rintro ⟨-, h⟩
    linarith
  · intro h
    exact ⟨by norm_num, by nlinarith⟩

/-- The reverse route `Real.le_sqrt` needs **both** nonnegativity premises. -/
example {t : ℝ} (ht : 0 ≤ t) : t ≤ Real.sqrt (t ^ 2 + t) := by
  rw [Real.le_sqrt ht (by nlinarith)]
  nlinarith

/-! ## Local lemma: the defect in its quadratic normal form (plan §5 #2) -/

theorem bepDefect_eq {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    bepDefect lam x = x ^ 2 / (4 * lam) := by
  unfold bepDefect bepLine eact
  field_simp
  ring

/-- `bepDefect` is even in the driving force (used by `epConformsOnWindow_symm`).

**The `lam ≠ 0` premise cannot be dropped**: at `lam = 0` the two sides are `-x/2` and `x/2`
(kernel fact — measured as an unsolved goal when the premise is omitted, and `bepDefect 0 1 ≠
bepDefect 0 (-1)`). The evenness is exactly the barrier-reversal identity `eact lam (-x) = eact lam x
+ x` combined with `bepLine lam (-x) = bepLine lam x + x`, and both need `lam ≠ 0` for the
`(4*lam)*(4*lam)⁻¹ = 1` cancellation. -/
theorem bepDefect_even {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    bepDefect lam (-x) = bepDefect lam x := by
  unfold bepDefect bepLine eact
  field_simp
  ring

/-! ## Plan §5 #14/#15 and §6.2 #10 -/

/-- Plan §5 #14. -/
theorem bepDefect_nonneg {lam x : ℝ} (hlam : 0 < lam) : 0 ≤ bepDefect lam x := by
  rw [bepDefect_eq (ne_of_gt hlam)]
  exact div_nonneg (sq_nonneg x) (by positivity)

/-- Plan §5 #15. -/
theorem bepDefect_pos_iff {lam x : ℝ} (hlam : 0 < lam) : 0 < bepDefect lam x ↔ x ≠ 0 := by
  rw [bepDefect_eq (ne_of_gt hlam), div_pos_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  exact sq_pos_iff

/-- Plan §6.2 #10: the absolute defect, with the sign of λ kept explicit. -/
theorem bepDefect_abs_eq {lam x : ℝ} (hlam : lam ≠ 0) :
    |bepDefect lam x| = x ^ 2 / (4 * |lam|) := by
  rw [bepDefect_eq hlam, abs_div, abs_of_nonneg (sq_nonneg x), abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]

/-- Plan §5 #14 corollary: on the nonnegative side no `abs` is needed. -/
theorem abs_bepDefect {lam x : ℝ} (hlam : 0 < lam) : |bepDefect lam x| = bepDefect lam x :=
  abs_of_nonneg (bepDefect_nonneg hlam)

/-! ## Plan §6.2 #11 — the sharp window theorem -/

/-- The `∀`-form engine of plan §6.2 #11: the defect stays within `tol` on the whole window
`[-w, w]` iff the half-width is at most `bepRadius lam tol`.

`(→)` evaluate at `x = -w` (`-w ∈ Set.Icc (-w) w` because `0 ≤ w`), get
`w^2/(4*lam) ≤ tol`, multiply by `4*lam > 0`, then `√(w^2) ≤ √(4*lam*tol)` with `Real.sqrt_sq hw`
and `Real.sqrt_mul`.
`(←)` from `x ∈ Set.Icc (-w) w` get `|x| ≤ w` (`abs_le`), hence `x^2 ≤ w^2`
(`pow_le_pow_left₀` + `sq_abs`), then `w^2 ≤ (2*√(lam*tol))^2 = 4*lam*tol` (`Real.sq_sqrt`). -/
theorem bepDefect_window_iff {lam tol w : ℝ} (hlam : 0 < lam) (htol : 0 < tol) (hw : 0 ≤ w) :
    (∀ x ∈ Set.Icc (-w) w, |bepDefect lam x| ≤ tol) ↔ w ≤ bepRadius lam tol := by
  have h4 : (0 : ℝ) < 4 * lam := by linarith
  have hdef : ∀ y : ℝ, |bepDefect lam y| = y ^ 2 / (4 * lam) := by
    intro y
    rw [bepDefect_eq (ne_of_gt hlam), abs_of_nonneg (by positivity)]
  unfold bepRadius
  constructor
  · intro h
    have hmem : (-w) ∈ Set.Icc (-w) w := ⟨le_rfl, by linarith⟩
    have h1 : w ^ 2 / (4 * lam) ≤ tol := by
      have := h (-w) hmem
      rwa [hdef (-w), neg_sq] at this
    have h2 : w ^ 2 ≤ 4 * lam * tol := by
      rw [div_le_iff₀ h4] at h1
      linarith
    calc w = Real.sqrt (w ^ 2) := (Real.sqrt_sq hw).symm
      _ ≤ Real.sqrt (4 * lam * tol) := Real.sqrt_le_sqrt h2
      _ = 2 * Real.sqrt (lam * tol) := by
            rw [show (4 : ℝ) * lam * tol = 4 * (lam * tol) by ring,
              Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
              show Real.sqrt 4 = 2 by
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
  · intro h x hx
    have hxabs : |x| ≤ w := abs_le.mpr hx
    have hxsq : x ^ 2 ≤ w ^ 2 := by
      calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
        _ ≤ w ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hxabs 2
    have hwsq : w ^ 2 ≤ 4 * lam * tol := by
      have h' : w ^ 2 ≤ (2 * Real.sqrt (lam * tol)) ^ 2 := pow_le_pow_left₀ hw h 2
      have h'' : (2 * Real.sqrt (lam * tol)) ^ 2 = 4 * lam * tol := by
        rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ lam * tol)]
        ring
      linarith
    rw [hdef x, div_le_iff₀ h4]
    linarith

/-- Plan §6.2 #11 in the plan's spelling. -/
theorem epConformsOnWindow_iff_radius {lam tol w : ℝ} (hlam : 0 < lam) (htol : 0 < tol)
    (hw : 0 ≤ w) : EPConformsOnWindow lam tol (-w) w ↔ w ≤ bepRadius lam tol := by
  unfold EPConformsOnWindow
  exact ⟨fun h => (bepDefect_window_iff hlam htol hw).mp h.2.2, fun h =>
    ⟨hlam, htol, (bepDefect_window_iff hlam htol hw).mpr h⟩⟩

/-- Plan §6.2 #12: the radius is attained, not an estimate. -/
theorem epConformsOnWindow_at_radius {lam tol : ℝ} (hlam : 0 < lam) (htol : 0 < tol) :
    EPConformsOnWindow lam tol (-(bepRadius lam tol)) (bepRadius lam tol) :=
  (epConformsOnWindow_iff_radius hlam htol (by unfold bepRadius; positivity)).mpr le_rfl

/-- Plan §6.2 #13: shrinking the window preserves conformance. -/
theorem epConformsOnWindow_mono {lam tol a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    EPConformsOnWindow lam tol a b → EPConformsOnWindow lam tol a' b' := by
  rintro ⟨h1, h2, h⟩
  exact ⟨h1, h2, fun x hx => h x ⟨le_trans ha hx.1, le_trans hx.2 hb⟩⟩

/-- Plan §6.2 #14: mirroring the window does not change conformance (`bepDefect` is even). -/
theorem epConformsOnWindow_symm {lam tol a b : ℝ} :
    EPConformsOnWindow lam tol a b ↔ EPConformsOnWindow lam tol (-b) (-a) := by
  unfold EPConformsOnWindow
  constructor
  · rintro ⟨h1, h2, h⟩
    refine ⟨h1, h2, fun x hx => ?_⟩
    have hmem : -x ∈ Set.Icc a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    simpa [bepDefect_even (ne_of_gt h1) x] using h (-x) hmem
  · rintro ⟨h1, h2, h⟩
    refine ⟨h1, h2, fun x hx => ?_⟩
    have hmem : -x ∈ Set.Icc (-b) (-a) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    simpa [bepDefect_even (ne_of_gt h1) x] using h (-x) hmem

/-! ## Plan §6.3 #15/#16 — monotonicity in the reorganization energy -/

set_option linter.unusedVariables false in
/-- Plan §6.3 #16. `Real.sqrt_le_sqrt` is unconditional, so `h0 : 0 ≤ lam₁` is not consumed (the
essential premise is `0 ≤ tol`: with `tol < 0` the statement is false, e.g. `tol = -1`,
`lam₁ = -2`, `lam₂ = -1`). -/
theorem bepRadius_mono {lam₁ lam₂ tol : ℝ} (h0 : 0 ≤ lam₁) (hle : lam₁ ≤ lam₂) (htol : 0 ≤ tol) :
    bepRadius lam₁ tol ≤ bepRadius lam₂ tol := by
  unfold bepRadius
  have hprod : lam₁ * tol ≤ lam₂ * tol := mul_le_mul_of_nonneg_right hle htol
  linarith [Real.sqrt_le_sqrt hprod]

set_option linter.unusedVariables false in
/-- Plan §6.3 #15. The premise `x ≠ 0` is the plan's strictness convention and is **not consumed**
(at `x = 0` both sides are `0`); the linter is off locally. -/
theorem bepDefect_antitone_lam {lam₁ lam₂ x : ℝ} (h0 : 0 < lam₁) (hle : lam₁ ≤ lam₂)
    (hx : x ≠ 0) : bepDefect lam₂ x ≤ bepDefect lam₁ x := by
  have h₂ : 0 < lam₂ := lt_of_lt_of_le h0 hle
  rw [bepDefect_eq (ne_of_gt h₂), bepDefect_eq (ne_of_gt h0)]
  have h4₁ : (0 : ℝ) < 4 * lam₁ := by linarith
  have h4₂ : (0 : ℝ) < 4 * lam₂ := by linarith
  rw [div_le_div_iff₀ h4₂ h4₁]
  exact mul_le_mul_of_nonneg_left (by linarith : 4 * lam₁ ≤ 4 * lam₂) (sq_nonneg x)

/-! ## Plan §6.1 #1–#6 — the transfer-coefficient bounds -/

/-- Plan §6.1 #1. `div_nonneg_iff_of_pos_right` does **not** exist; the shortest route is
`le_div_iff₀` (with `0` rewritten by `zero_mul`) and `div_le_one`, after moving the
linear-response body to the transition-state form with `transfer_eq_tsCoord`. -/
theorem epBounds_iff_region {lam x : ℝ} (hlam : 0 < lam) :
    EPBounds lam x ↔ -lam ≤ x ∧ x ≤ lam := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  have hts : transfer lam x = (lam - x) / (2 * lam) := by
    unfold transfer
    field_simp
  have hlow : (0 : ℝ) ≤ (lam - x) / (2 * lam) ↔ 0 ≤ lam - x := by
    rw [le_div_iff₀ h2, zero_mul]
  have hhigh : (lam - x) / (2 * lam) ≤ 1 ↔ lam - x ≤ 2 * lam := div_le_one h2
  unfold EPBounds
  rw [hts, hlow, hhigh]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Plan §6.1 #2 (the same computation with strict inequalities). -/
theorem epRegime_iff_strict {lam x : ℝ} (hlam : 0 < lam) :
    EPRegime lam x ↔ 0 < transfer lam x ∧ transfer lam x < 1 := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  have hts : transfer lam x = (lam - x) / (2 * lam) := by
    unfold transfer
    field_simp
  have hlow : (0 : ℝ) < (lam - x) / (2 * lam) ↔ 0 < lam - x :=
    div_pos_iff_of_pos_right h2
  have hhigh : (lam - x) / (2 * lam) < 1 ↔ lam - x < 2 * lam := div_lt_one h2
  unfold EPRegime
  rw [hts, hlow, hhigh]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Plan §6.1 #5: α > 1 — the **reverse** direction is in the inverted region. -/
theorem not_epBounds_of_lt_neg {lam x : ℝ} (hlam : 0 < lam) (hx : x < -lam) :
    ¬ EPBounds lam x := by
  intro h
  have := (epBounds_iff_region hlam).mp h
  linarith

/-- Plan §6.1 #6: α < 0 — the **forward** direction is in the inverted region. -/
theorem not_epBounds_of_gt {lam x : ℝ} (hlam : 0 < lam) (hx : lam < x) : ¬ EPBounds lam x := by
  intro h
  have := (epBounds_iff_region hlam).mp h
  linarith

/-! ## Measured failures of this topic (verbatim, do not retry)

* `div_nonneg_iff_of_pos_right` — `error: unknown identifier 'div_nonneg_iff_of_pos_right'`
  (the strict sibling `div_pos_iff_of_pos_right` *does* exist; the `≤` version does not, and
  `div_nonneg_iff` is the general four-way disjunction). Use `le_div_iff₀` + `zero_mul`.
* `pow_le_pow_left` — deprecated, `warning: 'pow_le_pow_left' has been deprecated: use
  'pow_le_pow_left₀' instead`; use `pow_le_pow_left₀`.
* `Real.sqrt_four` — `error: unknown constant 'Real.sqrt_four'`; get `√4 = 2` from `Real.sqrt_sq`
  after `show (4 : ℝ) = 2 ^ 2`.
* `Real.sqrt_lt_iff_lt_sq` and `Real.sq_le_sq` — `error: unknown constant ...`; the root-level
  `sq_le_sq` is the one that exists, and the sqrt comparison routes are `Real.lt_sqrt` /
  `Real.le_sqrt` / `Real.sqrt_le_iff`.
* `le_sqrt'` written bare — `error: unknown identifier`; it is `Real.le_sqrt'` and needs `0 < x`.
* `Set.mem_Icc_iff` — `error: unknown constant 'Set.mem_Icc_iff'`; the usable names are
  `Set.mem_Icc`, `Set.left_mem_Icc`, `Set.right_mem_Icc`, `Set.Icc_subset_Icc_iff`.
* deprecations (warning only): `div_le_div_iff` → `div_le_div_iff₀`, `div_le_div_right` →
  `div_le_div_iff_of_pos_right`, `div_le_div_left` → `div_le_div_iff_of_pos_left`.
-/

end PhotoLean.BEP.ProbeAbsSqrt
