/-
Einstein-api-probe.lean — API calibration probe for the Einstein theory (Phase 1).

Run: proofs/scripts/lake env lean theories/Einstein/probes/Einstein-api-probe.lean
Expected: exit 0, no `sorry` anywhere in this file (probes are calibration tools and may carry
proved examples). Every `#check` output is recorded against proofs/API-NOTES.md §Einstein
(appended at delivery).

The probe covers: (i) the π-positivity route of `radFactor_pos`; (ii) the field-algebra routes
of the round-trip legs; (iii) the ℚ-layer arithmetic of the named instances (the measured
boundary: `decide` does not reduce ℚ division — use `norm_num`, cf. `PhotoLean.Marcus.RatModel`);
(iv) the irrationality-of-π name used by `radFactor_not_rational`.
-/
import Mathlib

-- π positivity and its irrationality (EB-C1 route and the EB-R2 honesty row)
#check @Real.pi_pos
#check @irrational_pi

-- positivity / field-algebra names used across EB-C rows
#check @mul_pos
#check @div_pos
#check @div_mul_cancel₀
#check @mul_div_cancel_left₀
#check @mul_one_div
#check @one_div_pos
#check @mul_pos_iff
#check @div_eq_iff
#check @Rat.cast_mul
#check @Rat.cast_div
#check @Rat.cast_one
#check @Rat.cast_ofNat

set_option autoImplicit false

namespace PhotoLean.Einstein

/-- The EB-C1 route dry run: the radiation factor is positive from the premises. -/
example {h c ν : ℝ} (hh : 0 < h) (hc : 0 < c) (hν : 0 < ν) :
    0 < 8 * Real.pi * h * ν ^ 3 / c ^ 3 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h3 : (0 : ℝ) < ν ^ 3 := pow_pos hν 3
  have hc3 : (0 : ℝ) < c ^ 3 := pow_pos hc 3
  positivity

/-- The EB-C2 route dry run: the A↔B round trip at a symbolic factor. -/
example {K B21 : ℝ} (hK : K ≠ 0) : K * B21 / K = B21 := mul_div_cancel_left₀ B21 hK
example {K A : ℝ} (hK : K ≠ 0) : K * (A / K) = A := mul_div_cancel₀ A hK

/-- The EB-R2 instance arithmetic at ℚ surrogate constants: `norm_num`, never `decide`
(ℚ division defeats `decide` — measured boundary). -/
example : (3 : ℚ) * 2 = 6 ∧ (3 : ℚ) * 2 / 3 = 2 := by norm_num
example : (5 : ℚ) * (3 / 1) * 6 = 90 ∧ (5 : ℚ) * (3 / 1) * 6 / (5 * (3 / 1)) = 6 := by norm_num
/-- The degeneracy swap both ways (EB-I2 arithmetic). -/
example : (3 / 1 : ℚ) * 2 = 6 ∧ (1 / 3 : ℚ) * 6 = 2 := by norm_num

end PhotoLean.Einstein
