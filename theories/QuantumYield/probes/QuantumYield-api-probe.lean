/-
QuantumYield-api-probe.lean — API calibration probe for the QuantumYield theory (Phase 1).

Run: proofs/scripts/lake env lean theories/QuantumYield/probes/QuantumYield-api-probe.lean
Expected: exit 0, no placeholder proofs in this file (probes are calibration tools and may
carry proved examples). Every `#check` confirms a name the statement skeleton uses in a proof
route; the findings are appended to proofs/API-NOTES.md at delivery.

Coverage: the `Fin.cons` surface (the risk surface of this theory), the Finset sum lemmas, the
matrix-literal numerals `![…]`, the cast-coherence names, and the instance arithmetic of QY-I
(the measured boundary: `decide` does not reduce ℚ division — use `norm_num`, cf.
`PhotoLean.Marcus.RatModel`).
-/
import Mathlib

-- Fin.cons / sum API (QY-C6 risk surface)
-- `Fin.sum_univ_cons` does NOT exist in this mathlib (drift catch); the cons-sum route is
-- `Fin.sum_univ_succ` + `Fin.cons_zero` (+ definitional `Fin.cons_succ`):
#check @Fin.sum_univ_succ
#check @Fin.cons_zero
#check @Fin.cons_succ
#check @Fin.sum_univ_zero
#check @Finset.sum_div
#check @Finset.single_le_sum
#check @Finset.sum_nonneg
#check @Finset.sum_pos
#check @div_self
#check @div_lt_one
#check @map_sum
#check @Rat.cast_div
#check @Rat.cast_sum

set_option autoImplicit false

namespace PhotoLean.QuantumYield

/-- The QY-C6 route dry run: the total rate under `Fin.cons`. The rewrite closes the goal
definitionally after the two named steps (the tail sum's `Fin.cons_succ` equality is
definitional, so `rw`'s closing `rfl` finishes it). -/
example (c : ℝ) (k : Fin 3 → ℝ) :
    ∑ i : Fin 4, (Fin.cons c k : Fin 4 → ℝ) i = c + ∑ i : Fin 3, k i := by
  rw [Fin.sum_univ_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]

/-- The QY-C9 witness arithmetic: total `6`, yields `1/6, 1/3, 1/2`. -/
example : ∑ i : Fin 3, (![1, 2, 3] : Fin 3 → ℝ) i = 6 := by
  norm_num [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
/-- Matrix-literal evaluation needs the `Matrix.cons_val_zero/one/two` simp set (measured:
without them `norm_num` leaves the numeral-indexed applications unevaluated). -/
example : (![1, 2, 3] : Fin 3 → ℝ) 0 / (∑ i : Fin 3, (![1, 2, 3] : Fin 3 → ℝ) i) = 1 / 6 := by
  norm_num [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- The QY-I instance verdicts at ℚ (kernel computation by `norm_num`). -/
example : (18 : ℚ) / (18 + 1 + 1) = 9 / 10 := by norm_num
example : (11 : ℚ) / (11 + 5 + 4) = 11 / 20 := by norm_num
/-- The quench-dilution instance: adding a channel of rate `9` rescales the yield to `18/29`
and the Stern–Volmer ratio is `29/20` (the A2 edge rehearsal at ℚ). -/
example : (18 : ℚ) / (9 + (18 + 1 + 1)) = 18 / 29 ∧
    (9 + (18 + 1 + 1) : ℚ) / (18 + 1 + 1) = 29 / 20 := by norm_num

end PhotoLean.QuantumYield
