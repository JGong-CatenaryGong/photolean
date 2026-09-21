/-
symmetryFactor API-calibration probe (F0-b, iron rule 4: no guessed names).
Run: proofs/scripts/lake env lean theories/SymmetryFactor/probes/SymmetryFactor-api-probe.lean
Expected: exit 0. Every `#check` output is recorded in proofs/API-NOTES.md §symmetryFactor.
-/
import Mathlib
import PhotoLean.Kernel
import PhotoLean.BEP.Basic

open Real Set

-- sqrt numeral and order API
#check @Real.sqrt_one
#check @Real.sqrt_four
#check @Real.sqrt_sq
#check @Real.sq_sqrt
#check @Real.sqrt_inj
#check @Real.sqrt_lt_sqrt
#check @Real.sqrt_lt_sqrt_iff
#check @Real.sqrt_pos
#check @Real.sqrt_nonneg
#check @Real.sqrt_mul_self

-- square-equality routes for the crossing uniqueness
#check @sq_eq_sq_iff_eq_or_eq
#check @sq_eq_sq_iff_abs_eq_abs
#check @abs_of_nonneg

-- division order API
#check @div_lt_one
#check @div_lt_one_iff
#check @eq_div_iff
#check @div_eq_div_iff
#check @lt_div_iff₀

-- numeral computations the instances will need
example : Real.sqrt 4 / (Real.sqrt 1 + Real.sqrt 4) = (2 : ℝ) / 3 := by
  rw [Real.sqrt_one, Real.sqrt_four]; norm_num
example : Real.sqrt 1 / (Real.sqrt 4 + Real.sqrt 1) = (1 : ℝ) / 3 := by
  rw [Real.sqrt_one, Real.sqrt_four]; norm_num

-- kernel / BEP tie-back targets
#check @PhotoLean.Kernel.tsCoord
#check @PhotoLean.BEP.transfer
#check @PhotoLean.BEP.transfer_thermoneutral
example {lam : ℝ} (hlam : lam ≠ 0) : PhotoLean.Kernel.tsCoord lam 0 = 1 / 2 := by
  unfold PhotoLean.Kernel.tsCoord; field_simp
example {lam : ℝ} (hlam : 0 < lam) : PhotoLean.BEP.transfer lam 0 = 1 / 2 := by
  unfold PhotoLean.BEP.transfer; field_simp

-- the crossing-uniqueness proof route, dry-run at (kr, kp) = (1, 4):
-- q² = 4(q-1)² has the two real roots 2/3 and 2; only 2/3 lies in [0,1].
example : (1 : ℝ) * (2/3) ^ 2 = 4 * ((2/3) - 1) ^ 2 := by norm_num
example : (1 : ℝ) * (2) ^ 2 = 4 * ((2) - 1) ^ 2 := by norm_num
example : (2 : ℝ) ∉ Set.Icc 0 1 := by norm_num [Set.mem_Icc]

-- the algebraic key step for uniqueness on [0,1]: from kr q² = kp (q-1)² with 0 ≤ q ≤ 1,
-- √kr·q and √kp·(1-q) are both nonnegative with equal squares.
example (kr kp q : ℝ) (hkr : 0 < kr) (hkp : 0 < kp) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hc : kr * q ^ 2 = kp * (q - 1) ^ 2) :
    Real.sqrt kr * q = Real.sqrt kp * (1 - q) := by
  have h1 : (Real.sqrt kr * q) ^ 2 = (Real.sqrt kp * (1 - q)) ^ 2 := by
    calc (Real.sqrt kr * q) ^ 2 = kr * q ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hkr)]
    _ = kp * (q - 1) ^ 2 := hc
    _ = kp * (1 - q) ^ 2 := by ring
    _ = (Real.sqrt kp * (1 - q)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hkp)]
  rw [sq_eq_sq_iff_eq_or_eq] at h1
  rcases h1 with h1 | h1
  · exact h1
  · have h2 : 0 ≤ Real.sqrt kr * q := mul_nonneg Real.sqrt_nonneg _ hq0
    have h3 : 0 ≤ Real.sqrt kp * (1 - q) :=
      mul_nonneg Real.sqrt_nonneg _ (by linarith)
    linarith

-- then the linear solve: q (√kr + √kp) = √kp.
example (kr kp q : ℝ) (hkr : 0 < kr) (hkp : 0 < kp)
    (hlin : Real.sqrt kr * q = Real.sqrt kp * (1 - q)) :
    q = Real.sqrt kp / (Real.sqrt kr + Real.sqrt kp) := by
  have hpos : 0 < Real.sqrt kr + Real.sqrt kp :=
    add_pos (Real.sqrt_pos.mpr hkr) (Real.sqrt_pos.mpr hkp)
  field_simp
  linarith [hlin]
