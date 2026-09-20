/-
Hammond milestone — API probe (topic A): signs of a quotient with a known-sign denominator.

Context: the Hammond layer classifies a reaction by the sign/position of the transition-state
coordinate `tsCoord lam x = (lam - x) / (2 * lam)`.  Every such step is a "divide by a positive
denominator and read off the numerator" step.  The calibration question is which of the
division/order lemmas exist in mathlib v4.17.0, and what the shortest working recipe is.

Running:  proofs/scripts/lake env lean theories/hammond/probes/hammond-api-sign-div.lean
Status:   0 errors / 0 warnings.

Verdict (details in proofs/API-NOTES.md, "Hammond milestone API calibration"):
* `div_neg_iff_of_pos_right` (and its `_left`, `nonpos`, `le`, `div_lt_zero_iff`,
  `div_le_zero_iff` cousins) DO NOT EXIST — `unknown identifier`.
* The working route for `a / c < 0 ↔ ...` with `0 < c` is `div_lt_iff₀ hc` (or, for `≤`,
  `div_le_iff₀ hc`), followed by `linarith`.
  With `c < 0` the existing names are `div_lt_iff_of_neg` / `lt_div_iff_of_neg`
  (`LinearOrderedField` only, so they do not apply to a general semifield).
-/
import Mathlib

namespace PhotoLean.Hammond.ProbeSignDiv

/-- Transition-state coordinate (same as the planned `PhotoLean.Hammond.tsCoord`). -/
noncomputable def tsCoord (lam x : ℝ) : ℝ := (lam - x) / (2 * lam)

/-! ## The calibrated division/order names -/

#check @div_pos_iff_of_pos_right
#check @div_pos_iff_of_pos_left
#check @div_lt_one
#check @one_lt_div
#check @div_le_one
#check @one_le_div
#check @div_lt_iff₀
#check @lt_div_iff₀
#check @div_le_iff₀
#check @le_div_iff₀
#check @div_lt_div_iff_of_pos_right
#check @div_le_div_iff_of_pos_right
#check @div_lt_div_right_of_neg
#check @div_le_div_right_of_neg
#check @div_lt_iff_of_neg
#check @lt_div_iff_of_neg
#check @div_eq_iff
#check @eq_div_iff
#check @div_neg_iff
#check @div_nonpos_iff
#check @div_neg_of_neg_of_pos
#check @sub_ne_zero
#check @two_ne_zero
#check @zero_div
#check @zero_mul

-- Measured (scratch probe, 2026-09-21): the following names do NOT exist.
--   #check div_neg_iff_of_pos_right      -- error: unknown identifier 'div_neg_iff_of_pos_right'
--   #check div_neg_iff_of_pos_left       -- error: unknown identifier 'div_neg_iff_of_pos_left'
--   #check div_nonpos_iff_of_pos_right   -- error: unknown identifier 'div_nonpos_iff_of_pos_right'
--   #check div_le_iff_of_pos_right       -- error: unknown identifier 'div_le_iff_of_pos_right'
--   #check div_lt_zero_iff               -- error: unknown identifier 'div_lt_zero_iff'
--   #check div_le_zero_iff               -- error: unknown identifier 'div_le_zero_iff'

/-! ## The gap: sign of `tsCoord` with a positive denominator

`div_neg_iff_of_pos_right` does not exist.  Two working routes, both verified below:
`div_lt_iff₀` (cross-multiply; shortest) and the general `div_neg_iff` (case split on the
disjunction).  The `≤ 0` version is the same with `div_le_iff₀` / `div_nonpos_iff`.
-/

/-- Route 1 for `< 0` (recommended): `div_lt_iff₀` + `linarith`. -/
theorem probe_div_neg_iff_of_pos_right {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x < 0 ↔ lam < x := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_lt_iff₀ h2, zero_mul]
  constructor <;> intro h <;> linarith

/-- The same `< 0` goal without the `zero_mul` cleanup step (also compiles). -/
theorem probe_div_neg_iff_of_pos_right' {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x < 0 ↔ lam < x := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_lt_iff₀ h2]
  constructor <;> intro h <;> linarith

/-- Route 2 for `< 0`: the general `div_neg_iff`, then kill the impossible branch. -/
theorem probe_div_neg_iff_via_general {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x < 0 ↔ lam < x := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_neg_iff]
  constructor
  · rintro (⟨h, hc⟩ | ⟨h, hc⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, h2⟩

/-- Route 3 for `< 0`: rewrite the right-hand `0` as `0 / (2 * lam)` and compare the two
divisions with `div_lt_div_iff_of_pos_right`. -/
theorem probe_div_neg_iff_via_two_divisions {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x < 0 ↔ lam < x := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [show (0 : ℝ) = 0 / (2 * lam) by rw [zero_div]]
  rw [div_lt_div_iff_of_pos_right h2]
  constructor <;> intro h <;> linarith

/-- `≤ 0` version (recommended route): `div_le_iff₀` + `linarith`. -/
theorem probe_div_nonpos_iff_of_pos_right {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x ≤ 0 ↔ lam ≤ x := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_le_iff₀ h2, zero_mul]
  constructor <;> intro h <;> linarith

/-- `≤ 0` version via the general `div_nonpos_iff`. -/
theorem probe_div_nonpos_iff_via_general {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x ≤ 0 ↔ lam ≤ x := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_nonpos_iff]
  constructor
  · rintro (⟨h, hc⟩ | ⟨h, hc⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, le_of_lt h2⟩

/-! ## The full `tsCoord` threshold table (all of it is needed by the zone lemmas) -/

/-- `tsCoord > 0` on a positive-curvature surface. -/
theorem probe_tsCoord_pos_iff {lam x : ℝ} (hlam : 0 < lam) :
    0 < tsCoord lam x ↔ x < lam := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_pos_iff_of_pos_right h2]
  constructor <;> intro h <;> linarith

/-- `tsCoord < 1/2` is exactly "reactant-like" in the driving-force coordinate. -/
theorem probe_tsCoord_lt_half_iff {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x < 1 / 2 ↔ 0 < x := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_lt_iff₀ h2]
  constructor <;> intro h <;> linarith

/-- `1/2 < tsCoord` is exactly "product-like". -/
theorem probe_half_lt_tsCoord_iff {lam x : ℝ} (hlam : 0 < lam) :
    1 / 2 < tsCoord lam x ↔ x < 0 := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [lt_div_iff₀ h2]
  constructor <;> intro h <;> linarith

/-- Non-strict reactant-like threshold. -/
theorem probe_tsCoord_le_half_iff {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x ≤ 1 / 2 ↔ 0 ≤ x := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_le_iff₀ h2]
  constructor <;> intro h <;> linarith

/-- Non-strict product-like threshold. -/
theorem probe_half_le_tsCoord_iff {lam x : ℝ} (hlam : 0 < lam) :
    1 / 2 ≤ tsCoord lam x ↔ x ≤ 0 := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [le_div_iff₀ h2]
  constructor <;> intro h <;> linarith

/-- The `1` threshold: `div_lt_one` (i.e. `tsCoord < 1 ↔ -lam < x`). -/
theorem probe_tsCoord_lt_one_iff {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x < 1 ↔ -lam < x := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_lt_one h2]
  constructor <;> intro h <;> linarith

/-- The `1` threshold, other side: `one_lt_div`. -/
theorem probe_one_lt_tsCoord_iff {lam x : ℝ} (hlam : 0 < lam) :
    1 < tsCoord lam x ↔ x < -lam := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [one_lt_div h2]
  constructor <;> intro h <;> linarith

/-- The thermoneutral point, via `div_eq_iff` (the matched denominator is the *divisor*). -/
theorem probe_tsCoord_eq_half_iff {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x = 1 / 2 ↔ x = 0 := by
  unfold tsCoord
  rw [div_eq_iff (mul_ne_zero two_ne_zero (ne_of_gt hlam))]
  constructor <;> intro h <;> linarith

/-! ## Negative denominator (the sharpness branch, `lam < 0`) -/

/-- With `lam < 0` the sign of `tsCoord` flips: use `div_lt_iff_of_neg`. -/
theorem probe_tsCoord_neg_iff_of_neg {lam x : ℝ} (hlam : lam < 0) :
    tsCoord lam x < 0 ↔ x < lam := by
  unfold tsCoord
  have h2 : (2 : ℝ) * lam < 0 := by linarith
  rw [div_lt_iff_of_neg h2]
  constructor <;> intro h <;> linarith

/-! ## Two-division monotonicity (the Hammond descriptor and its sharpness) -/

/-- `lam > 0`: larger driving force gives an *earlier* (smaller) coordinate. -/
theorem probe_tsCoord_antitone_iff {lam x₁ x₂ : ℝ} (hlam : 0 < lam) :
    tsCoord lam x₂ < tsCoord lam x₁ ↔ x₁ < x₂ := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_lt_div_iff_of_pos_right h2]
  constructor <;> intro h <;> linarith

/-- `lam > 0`, non-strict version. -/
theorem probe_tsCoord_antitone_le_iff {lam x₁ x₂ : ℝ} (hlam : 0 < lam) :
    tsCoord lam x₂ ≤ tsCoord lam x₁ ↔ x₁ ≤ x₂ := by
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_le_div_iff_of_pos_right h2]
  constructor <;> intro h <;> linarith

/-- The shape the Hammond descriptor is stated in (no `↔`): direct `rw` + `linarith`. -/
theorem probe_tsCoord_antitone {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ} (h : x₁ < x₂) :
    tsCoord lam x₂ < tsCoord lam x₁ := by
  unfold tsCoord
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 2 * lam)]
  linarith

/-- `lam < 0` (sharpness): the direction reverses.  Note `div_lt_div_right_of_neg` is
an `↔` whose right-hand side is `x₂ < x₁`, i.e. the arguments swap. -/
theorem probe_tsCoord_monotone_of_neg {lam x₁ x₂ : ℝ} (hlam : lam < 0) :
    tsCoord lam x₁ < tsCoord lam x₂ ↔ x₁ < x₂ := by
  unfold tsCoord
  have h2 : (2 : ℝ) * lam < 0 := by linarith
  rw [div_lt_div_right_of_neg h2]
  constructor <;> intro h <;> linarith

/-- `lam < 0`, non-strict version (`div_le_div_right_of_neg`). -/
theorem probe_tsCoord_monotone_le_of_neg {lam x₁ x₂ : ℝ} (hlam : lam < 0) :
    tsCoord lam x₂ ≤ tsCoord lam x₁ ↔ x₂ ≤ x₁ := by
  unfold tsCoord
  have h2 : (2 : ℝ) * lam < 0 := by linarith
  rw [div_le_div_right_of_neg h2]
  constructor <;> intro h <;> linarith

end PhotoLean.Hammond.ProbeSignDiv
