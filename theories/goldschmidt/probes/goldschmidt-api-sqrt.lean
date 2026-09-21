/-
  PhotoLean — theories/goldschmidt/probes/goldschmidt-api-sqrt.lean

  mathlib API calibration for the Goldschmidt theory (plan §2 symbol table, §4 G1 / §6 G3):
  `Real.sqrt` bookkeeping around `t = (rA + rO) / (√2 * (rB + rO))`.

  Run from the repository root:

      proofs/scripts/lake env lean theories/goldschmidt/probes/goldschmidt-api-sqrt.lean

  Calibrated against the pinned toolchain (Lean 4.17.0 + mathlib v4.17.0). Every `#check` below
  is verbatim output; every `example` is kernel-checked (no placeholder). Status: 0 error /
  0 warning.
-/
import Mathlib

noncomputable section

/-! ## (a) `Real.sqrt` — confirmed signatures (verbatim `#check @`, wraps joined) -/

#check @Real.sqrt_pos_of_pos
#check @Real.sqrt_ne_zero'
#check @Real.sq_sqrt
#check @Real.sqrt_sq_eq_abs
#check @Real.sqrt_mul
#check @Real.sqrt_mul_self
#check @Real.sqrt_mul_self_eq_abs
#check @Real.sqrt_div
#check @Real.div_sqrt
#check @Real.mul_self_sqrt
#check @Real.sqrt_inv
#check @Real.sqrt_div_self'
#check @Real.sqrt_pos
#check @Real.sqrt_nonneg
#check @Real.sqrt_le_sqrt
#check @Real.sqrt_lt_sqrt
#check @Real.sqrt_le_sqrt_iff
#check @Real.sqrt_lt_sqrt_iff
#check @Real.sqrt_eq_zero_of_nonpos

/-
  Measured drift (see the API-NOTES entry): `Real.sqrt_ne_zero_of_pos` and `Real.sqrt_two_pos`
  do **not** exist in v4.17.0.
-/

/-! ## The three bookkeeping identities of the tolerance factor -/

/-- `2 / √2 = √2` — one step, no tactic: `Real.div_sqrt` is *unconditional*
(`∀ {x : ℝ}, x / √x = √x`, and it also covers `x = 0` because `0 / 0 = 0 = √0`). -/
theorem two_div_sqrt_two : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := Real.div_sqrt

/-- The same identity in the theory's own denominator shape. -/
theorem two_mul_div_sqrt_two (x : ℝ) : 2 * x / Real.sqrt 2 = Real.sqrt 2 * x := by
  rw [show 2 * x / Real.sqrt 2 = (2 / Real.sqrt 2) * x by ring, Real.div_sqrt]

/-- `√2 * √2 = 2` — `Real.mul_self_sqrt` is the `*` version; `Real.sq_sqrt` is the `^` version. -/
theorem sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- `√2 ^ 2 = 2` — the power version (needs the explicit nonnegativity input). -/
theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- `√2 * (1 / √2) = 1` — the exact tactic line:
`rw [one_div, mul_inv_cancel₀ ((Real.sqrt_ne_zero').mpr (by norm_num))]`. -/
theorem sqrt_two_mul_one_div_sqrt_two : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := by
  rw [one_div, mul_inv_cancel₀ ((Real.sqrt_ne_zero').mpr (by norm_num))]

/-- The mirror order `(1 / √2) * √2 = 1` — `inv_mul_cancel₀` (note the reversed factor order). -/
theorem one_div_sqrt_two_mul_sqrt_two : (1 / Real.sqrt 2) * Real.sqrt 2 = 1 := by
  rw [one_div, inv_mul_cancel₀ ((Real.sqrt_ne_zero').mpr (by norm_num))]

/-- `√2 * (√2)⁻¹ = 1` — the `⁻¹` form, without passing through `one_div`. -/
theorem sqrt_two_mul_inv_sqrt_two : Real.sqrt 2 * (Real.sqrt 2)⁻¹ = 1 :=
  mul_inv_cancel₀ ((Real.sqrt_ne_zero').mpr (by norm_num))

/-- Positivity and non-vanishing of `√2` — the two facts every `field_simp`/cancel step needs. -/
theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)

theorem sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := (Real.sqrt_ne_zero').mpr (by norm_num)

/-- `Real.div_sqrt` also has the `√x`-shaped statement; useful when a denominator is not literal. -/
theorem div_sqrt_general {x : ℝ} : x / Real.sqrt x = Real.sqrt x := Real.div_sqrt

/-! ## The two G1 rows that consume the recipes (`latticeOf`, `idealAO`, `tolFac` mirror the plan
§2 symbol table; the probe is self-contained by design) -/

/-- Mirror of plan §2: `latticeOf rB rO = 2 * (rB + rO)`. -/
def latticeOf (rB rO : ℝ) : ℝ := 2 * (rB + rO)

/-- Mirror of plan §2: `idealAO rB rO = √2 * (rB + rO)`. -/
def idealAO (rB rO : ℝ) : ℝ := Real.sqrt 2 * (rB + rO)

/-- Mirror of plan §2: `tolFac rA rB rO = (rA + rO) / (√2 * (rB + rO))`. -/
def tolFac (rA rB rO : ℝ) : ℝ := (rA + rO) / (Real.sqrt 2 * (rB + rO))

/-- Row `tolFac_eq_distRatio`, first half: `latticeOf rB rO / √2 = idealAO rB rO`.
Recipe: pull the `√2` out with a `ring`-proved rearrangement, then `Real.div_sqrt`. -/
theorem latticeOf_div_sqrt_eq_idealAO (rB rO : ℝ) :
    latticeOf rB rO / Real.sqrt 2 = idealAO rB rO := by
  have h : latticeOf rB rO / Real.sqrt 2 = (2 / Real.sqrt 2) * (rB + rO) := by
    unfold latticeOf; ring
  rw [h]
  unfold idealAO
  rw [Real.div_sqrt]

/-- Row `tolFac_eq_distRatio`, second half: `tolFac rA rB rO = (rA + rO) / idealAO rB rO`. -/
theorem tolFac_eq_div_idealAO (rA rB rO : ℝ) :
    tolFac rA rB rO = (rA + rO) / idealAO rB rO := rfl

/-- Row `contact_iff_tolFac_one` shape: the cancellation that turns `t = 1` into the contact
equation. `div_eq_one_iff_eq` is the tool; the two side conditions are `√2 ≠ 0` and `rB + rO ≠ 0`. -/
theorem contact_iff_tolFac_one (rA rB rO : ℝ) (hB : rB + rO ≠ 0) :
    rA + rO = idealAO rB rO ↔ tolFac rA rB rO = 1 := by
  unfold tolFac idealAO
  rw [div_eq_one_iff_eq (mul_ne_zero sqrt_two_ne_zero hB)]

/-- The geometric rearrangement behind `tolFac (idealA rB rO) rB rO = 1`: the A radius that makes
the two contact distances agree, `idealA rB rO = √2 * (rB + rO) - rO`. -/
theorem idealA_contact (rB rO : ℝ) :
    (Real.sqrt 2 * (rB + rO) - rO) + rO = idealAO rB rO := by
  unfold idealAO; ring

/-! ## Every `#check` above is present; the two absent names are recorded in `proofs/API-NOTES.md`
under "failures and drift". This probe imports `Mathlib` only and touches no `PhotoLean` source. -/
