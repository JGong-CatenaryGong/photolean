/-
PhotoLean.SymmetryFactor.Criterion — milestone F1, the law layer.

The mathematics of the thermoneutral crossing of two parabolas with **unequal** curvatures:
the closed form `tsCoordZero kr kp = √kp / (√kr + √kp)` is a coordinate (bounded in `[0,1]`,
with the weakest one-sided positivity premises), it **is** the crossing of the two surfaces, and
inside the reaction interval `[0,1]` it is the **only** crossing — proved without calculus: the
quantities `√kr·q` and `√kp·(1-q)` are nonnegative on `[0,1]` and have equal squares exactly at a
crossing, hence are equal, and the rest is a linear solve. The interval restriction is
load-bearing and its necessity is a delivered witness (`crossing_witness_outside_interval`: the
second real root `q = 2` at `(kr,kp) = (1,4)`). The two monotonicity rows carry the chemical
reading: a stiffer product well pushes the thermoneutral crossing **later**, a stiffer reactant
well pushes it **earlier** — a Hammond-style structural verdict at ZERO driving force.

Measured proof boundaries (API round, `theories/SymmetryFactor/probes/SymmetryFactor-api-probe.lean`
and the round log in `proofs/API-NOTES.md` §symmetryFactor): `norm_num` does NOT evaluate
`Real.sqrt` of perfect-square numerals in this toolchain (the `Real.sqrt_sq` route is used
instead); `Real.sqrt_four` does not exist; `div_lt_div_iff` takes the LEFT denominator first.

Statement authority: `theories/SymmetryFactor/probes/SymmetryFactor-statement-skeleton.lean` § F1
(law-layer rows). There is no unproved placeholder and no custom axiomatic declaration anywhere
in this file. The `#print axioms` gate of every theorem below lists at most `propext`,
`Classical.choice`, `Quot.sound`.
-/
import PhotoLean.SymmetryFactor.Basic

set_option autoImplicit false

namespace PhotoLean

namespace SymmetryFactor

/-! ## F1 — law layer -/

/-- The closed form is a coordinate: nonnegative **unconditionally**. `Real.sqrt` is totalized
(`0 ≤ √·` for every input, including negatives where `√ = 0`) and totalized division gives
`0/0 = 0`, so no curvature premise is load-bearing (weakest-premise standard, iron rule 3: the
first draft's `0 ≤ kr, 0 ≤ kp` premises were dropped rather than suppressed — plan §3.1). -/
theorem tsCoordZero_nonneg {kr kp : ℝ} : 0 ≤ tsCoordZero kr kp := by
  unfold tsCoordZero
  exact div_nonneg (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- The closed form never exceeds `1`, unconditionally (same totalization note; the first draft's
nonnegativity premises were dropped — plan §3.1). -/
theorem tsCoordZero_le_one {kr kp : ℝ} : tsCoordZero kr kp ≤ 1 := by
  unfold tsCoordZero
  have hden : 0 ≤ Real.sqrt kr + Real.sqrt kp :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  by_cases hd : Real.sqrt kr + Real.sqrt kp = 0
  · rw [hd, div_zero]
    exact zero_le_one
  · have hpos : 0 < Real.sqrt kr + Real.sqrt kp := lt_of_le_of_ne hden (Ne.symm hd)
    rw [div_le_one hpos]
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)

/-- Positivity needs exactly one premise: a positive product curvature makes the numerator
positive and the denominator at least the numerator (weakest-premise standard: no premise on
`kr` is consumed — at `kr < 0` the totalized `Real.sqrt kr = 0` and the row still holds). -/
theorem tsCoordZero_pos {kr kp : ℝ} (hkp : 0 < kp) : 0 < tsCoordZero kr kp := by
  unfold tsCoordZero
  exact div_pos (Real.sqrt_pos.mpr hkp)
    (lt_of_lt_of_le (Real.sqrt_pos.mpr hkp) (le_add_of_nonneg_left (Real.sqrt_nonneg _)))

/-- Staying below `1` needs exactly one premise: a positive reactant curvature. -/
theorem tsCoordZero_lt_one {kr kp : ℝ} (hkr : 0 < kr) : tsCoordZero kr kp < 1 := by
  unfold tsCoordZero
  rw [div_lt_one (lt_of_lt_of_le (Real.sqrt_pos.mpr hkr)
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)))]
  exact lt_add_of_pos_left _ (Real.sqrt_pos.mpr hkr)

/-- The closed form IS the thermoneutral crossing of the two surfaces. -/
theorem tsCoordZero_crosses {kr kp : ℝ} (hkr : 0 < kr) (hkp : 0 < kp) :
    CrossesAtThermoneutral kr kp (tsCoordZero kr kp) := by
  rw [crosses_eq_algebra]
  unfold tsCoordZero
  have hd : Real.sqrt kr + Real.sqrt kp ≠ 0 :=
    ne_of_gt (add_pos (Real.sqrt_pos.mpr hkr) (Real.sqrt_pos.mpr hkp))
  have h1 : Real.sqrt kp / (Real.sqrt kr + Real.sqrt kp) - 1
      = -(Real.sqrt kr) / (Real.sqrt kr + Real.sqrt kp) := by
    field_simp
  rw [h1, ← Real.sq_sqrt (le_of_lt hkr), ← Real.sq_sqrt (le_of_lt hkp)]
  field_simp
  ring

/-- Uniqueness on the reaction interval: inside `[0,1]` the crossing point is exactly the closed
form. Proof route (calculus-free): both `√kr·q` and `√kp·(1-q)` are nonnegative with equal
squares, hence equal; then a linear solve. -/
theorem crossing_unique_in_unit_interval {kr kp q : ℝ} (hkr : 0 < kr) (hkp : 0 < kp)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hc : CrossesAtThermoneutral kr kp q) :
    q = tsCoordZero kr kp := by
  rw [crosses_eq_algebra] at hc
  have h1 : (Real.sqrt kr * q) ^ 2 = (Real.sqrt kp * (1 - q)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hkr), Real.sq_sqrt (le_of_lt hkp),
      show (1 - q) ^ 2 = (q - 1) ^ 2 by ring]
    exact hc
  have h2 : 0 ≤ Real.sqrt kr * q := mul_nonneg (Real.sqrt_nonneg _) hq.1
  have h3 : 0 ≤ Real.sqrt kp * (1 - q) := mul_nonneg (Real.sqrt_nonneg _) (by linarith [hq.2])
  rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg h2, abs_of_nonneg h3] at h1
  unfold tsCoordZero
  have hne : Real.sqrt kr + Real.sqrt kp ≠ 0 :=
    ne_of_gt (add_pos (Real.sqrt_pos.mpr hkr) (Real.sqrt_pos.mpr hkp))
  rw [eq_div_iff hne]
  have hkey : q * (Real.sqrt kr + Real.sqrt kp) = Real.sqrt kp * (1 - q) + Real.sqrt kp * q := by
    calc q * (Real.sqrt kr + Real.sqrt kp) = Real.sqrt kr * q + Real.sqrt kp * q := by ring
      _ = Real.sqrt kp * (1 - q) + Real.sqrt kp * q := by rw [h1]
  rw [hkey]
  ring

/-- The interval restriction is load-bearing: outside `[0,1]` the crossing equation has a second
real root. Kernel-checked witness at `(kr, kp) = (1, 4)`: `q = 2` satisfies `1·q² = 4·(q-1)²`
and `2 ∉ [0,1]`, while the delivered crossing coordinate is `2/3` (F2). -/
theorem crossing_witness_outside_interval :
    CrossesAtThermoneutral 1 4 2 ∧ (2 : ℝ) ∉ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [crosses_eq_algebra]
    norm_num
  · intro h
    exact absurd h.2 (by norm_num)

/-- A stiffer product well pushes the thermoneutral crossing later (strictly monotone in `kp`). -/
theorem tsCoordZero_strictMono_kp {kr kp kp' : ℝ} (hkr : 0 < kr) (hkp : 0 ≤ kp) (h : kp < kp') :
    tsCoordZero kr kp < tsCoordZero kr kp' := by
  have hsr : Real.sqrt kp < Real.sqrt kp' := Real.sqrt_lt_sqrt hkp h
  have hd : 0 < Real.sqrt kr + Real.sqrt kp :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr hkr) (Real.sqrt_nonneg _)
  have hd' : 0 < Real.sqrt kr + Real.sqrt kp' :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr hkr) (Real.sqrt_nonneg _)
  unfold tsCoordZero
  rw [div_lt_div_iff₀ hd hd', mul_add, mul_add]
  have hlt : Real.sqrt kp * Real.sqrt kr < Real.sqrt kp' * Real.sqrt kr :=
    mul_lt_mul_of_pos_right hsr (Real.sqrt_pos.mpr hkr)
  have hcomm : Real.sqrt kp * Real.sqrt kp' = Real.sqrt kp' * Real.sqrt kp := mul_comm _ _
  linarith

/-- A stiffer reactant well pushes the thermoneutral crossing earlier (strictly antitone in
`kr`). -/
theorem tsCoordZero_strictAnti_kr {kr kr' kp : ℝ} (hkp : 0 < kp) (hkr : 0 ≤ kr) (h : kr < kr') :
    tsCoordZero kr' kp < tsCoordZero kr kp := by
  have hsr : Real.sqrt kr < Real.sqrt kr' := Real.sqrt_lt_sqrt hkr h
  have hd : 0 < Real.sqrt kr + Real.sqrt kp :=
    by linarith [Real.sqrt_nonneg kr, Real.sqrt_pos.mpr hkp]
  have hd' : 0 < Real.sqrt kr' + Real.sqrt kp :=
    by linarith [Real.sqrt_nonneg kr', Real.sqrt_pos.mpr hkp]
  unfold tsCoordZero
  rw [div_lt_div_iff₀ hd' hd, mul_add, mul_add]
  have hlt : Real.sqrt kp * Real.sqrt kr < Real.sqrt kp * Real.sqrt kr' :=
    mul_lt_mul_of_pos_left hsr (Real.sqrt_pos.mpr hkp)
  linarith

end SymmetryFactor

end PhotoLean
