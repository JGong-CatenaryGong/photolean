/-
  PhotoLean — theories/goldschmidt/probes/goldschmidt-api-sqrt2-irrational.lean

  mathlib API calibration for the Goldschmidt theory, dispatch item (d): the irrationality of the
  tolerance factor at rational radii (plan §7 G4 row `tolFac_irrational`).

  Run from the repository root:

      proofs/scripts/lake env lean theories/goldschmidt/probes/goldschmidt-api-sqrt2-irrational.lean

  Lean 4.17.0 + mathlib v4.17.0. The last theorem in this file is a **complete** kernel-checked
  proof of the delivered row (no placeholder). Status: 0 error / 0 warning.
-/
import Mathlib

noncomputable section

/-! ## The `Irrational` API that exists in v4.17.0 (verbatim `#check @`, wraps joined)

  **Name drift measured in this round:** the dispatch's candidate family
  `Irrational.mul_ratCast` / `div_ratCast` / `add_ratCast` / `ratCast_mul` / `ratCast_div` /
  `of_ratCast_mul` / `of_ratCast_add` / `of_ratCast_div` / `ratCast_sub` / `ratCast_add` /
  `Irrational.sub_ratCast` / `of_ratCast_sub` / `of_ratCast_inv` does **not** exist. In v4.17.0 the
  whole closure family is spelled with a bare `rat` / `int` / `nat`, not `ratCast`; the ones this
  row needs are `Irrational.rat_mul`, `Irrational.mul_rat`, `Irrational.inv`,
  `Irrational.rat_div`, `Irrational.div_rat`. -/

#check @Irrational
#check @irrational_sqrt_two
#check @Irrational.inv
#check @Irrational.ne_rat
#check @Irrational.ne_zero
#check @Irrational.rat_mul
#check @Irrational.mul_rat
#check @Irrational.of_mul_rat
#check @Irrational.rat_add
#check @Irrational.add_rat
#check @Irrational.of_rat_add
#check @Irrational.rat_sub
#check @Irrational.sub_rat
#check @Irrational.rat_div
#check @Irrational.div_rat
#check @Irrational.of_div_rat
#check @Irrational.of_rat_div
#check @Irrational.mul_int
#check @Irrational.of_mul_self
#check @Irrational.of_one_div
#check @Rat.not_irrational
#check @irrational_sqrt_natCast_iff
#check @Nat.Prime.irrational_sqrt

/-! ## The delivered statement of `tolFac_irrational` — settled form

  Plan §2 fixes `tolFac rA rB rO = (rA + rO) / (√2 * (rB + rO))` on `ℝ`, while the row's hypotheses
  are about *rational* radii. The form that compiles (and that keeps the plan's `tolFac` shape
  verbatim, so no definition is specialized) is: input **rationals** `rA rB rO : ℚ`, with the two
  non-degeneracy hypotheses stated in `ℚ` and carried by `ℚ → ℝ` casts inside the conclusion.

  The two hypotheses are both **necessary**, not cosmetic:
  * `rB + rO ≠ 0` — otherwise the denominator is `0` and `tolFac = 0`, rational;
  * `rA + rO ≠ 0` — otherwise the numerator is `0` and again `tolFac = 0`, rational.
-/

/-- Plan §2 mirror (self-contained probe). -/
def tolFac (rA rB rO : ℝ) : ℝ := (rA + rO) / (Real.sqrt 2 * (rB + rO))

/-- The reusable core: a nonzero rational divided by `√2` is irrational.
Recipe: `Irrational.inv` on `irrational_sqrt_two`, then `Irrational.rat_mul`;
`√2 / √2` is *not* involved, so no `Real.sqrt` algebra is needed at all. -/
theorem irrational_ratCast_div_sqrt_two (q : ℚ) (hq : q ≠ 0) :
    Irrational ((q : ℝ) / Real.sqrt 2) := by
  have h : Irrational ((q : ℝ) * (Real.sqrt 2)⁻¹) :=
    (irrational_sqrt_two.inv).rat_mul hq
  simpa only [div_eq_mul_inv] using h

/-- The `(√2)⁻¹ * ↑q` orientation named in the dispatch — same proof, one `mul_comm`. -/
theorem irrational_inv_sqrt_two_mul_ratCast (q : ℚ) (hq : q ≠ 0) :
    Irrational ((Real.sqrt 2)⁻¹ * (q : ℝ)) := by
  simpa only [mul_comm] using irrational_ratCast_div_sqrt_two q hq

/-- And the still more primitive orientation, straight out of `Irrational.rat_mul`. -/
theorem irrational_ratCast_mul_inv_sqrt_two (q : ℚ) (hq : q ≠ 0) :
    Irrational ((q : ℝ) * (Real.sqrt 2)⁻¹) := (irrational_sqrt_two.inv).rat_mul hq

/-- **`tolFac_irrational`** (plan §7 G4) — the delivered row, kernel-checked end to end.

  Statement (settled): for `rA rB rO : ℚ`, if `rA + rO ≠ 0` and `rB + rO ≠ 0`, then
  `Irrational (tolFac ↑rA ↑rB ↑rO)`.

  Proof recipe (3 steps):
  1. the algebraic identity `tolFac ↑rA ↑rB ↑rO = ↑((rA+rO)/(rB+rO)) / √2`
     by `unfold tolFac; push_cast; field_simp; ring` (the `field_simp` needs `√2 ≠ 0` and
     `↑(rB+rO) ≠ 0` as explicit context hypotheses; `ring_nf` **fails** here — see API-NOTES);
  2. `div_ne_zero hA hB : (rA+rO)/(rB+rO) ≠ 0`;
  3. `irrational_ratCast_div_sqrt_two`. -/
theorem tolFac_irrational (rA rB rO : ℚ) (hA : rA + rO ≠ 0) (hB : rB + rO ≠ 0) :
    Irrational (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)) := by
  have hq : (rA + rO) / (rB + rO) ≠ 0 := div_ne_zero hA hB
  have key : tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)
      = ((rA + rO) / (rB + rO) : ℚ) / Real.sqrt 2 := by
    have h2 : (Real.sqrt 2 : ℝ) ≠ 0 := (Real.sqrt_ne_zero').mpr (by norm_num)
    have hb : ((rB + rO : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hB
    unfold tolFac
    push_cast
    field_simp
    ring
  rw [key]
  exact irrational_ratCast_div_sqrt_two _ hq

/-- A concrete instance of the row, to make the `Rat.cast` layer visible: `rA = rB = 1/2`,
`rO = 3/2` gives `tolFac = 2 / (√2 * 2) = 1/√2`, and `2 / (√2 * 2) = 1/√2` is irrational. -/
theorem tolFac_irrational_instance :
    Irrational (tolFac ((1 / 2 : ℚ) : ℝ) ((1 / 2 : ℚ) : ℝ) ((3 / 2 : ℚ) : ℝ)) :=
  tolFac_irrational (1 / 2) (1 / 2) (3 / 2) (by norm_num) (by norm_num)

/-- The closure access form of `Irrational.ne_rat` (used whenever a prover must *contradict* a
rational value): `h.ne_rat q : x ≠ ↑q`. -/
example (q : ℚ) (h : Irrational (Real.sqrt 2)) : Real.sqrt 2 ≠ (q : ℝ) := h.ne_rat q

/-- `Rat.not_irrational` is the `simp`-friendly negative fact on `ℚ → ℝ` casts. -/
example (q : ℚ) : ¬ Irrational ((q : ℝ)) := Rat.not_irrational q

end
