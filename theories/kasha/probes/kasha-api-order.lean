/-
Kasha milestone — API probe (topic B + D): division/order on ℝ, and the `Real.sqrt` window recipe.

Scope (B). The K3 sharp criteria are cross-multiplications with explicit positivity, and K4's
Marcus bridge inverts a `kashaGapThreshold`.  This probe calibrates `div_le_div_iff₀`,
`div_lt_div_iff₀`, `le_div_iff₀`/`div_le_iff₀`/`lt_div_iff₀`/`div_lt_iff₀`, `div_pos`,
`div_nonneg`, `div_le_div_of_nonneg_left/right`, `mul_le_mul_of_nonneg_left/right`,
`lt_of_mul_lt_mul_right` and the `one_div`/`inv_le_inv₀` pair, and kernel-checks one worked
recipe per row shape: the K3 #1 ⟺ K3 #2 cross-multiplication, the K3 #9 strict side, the K3 #3
cancellation, the reciprocal of `kashaGapThreshold` (K4 #12/#15), and the strict threshold step of
K3 #10.

Scope (D). The K4 #14 window `(lam - x)^2 ≤ R` with `0 ≤ R` ⟺ `|lam - x| ≤ Real.sqrt R` is
re-verified in the K4 shape, both as a one-`rw` recipe and as the two `calc` halves (the route of
`theories/BEP/probes/bep-api-abs-sqrt.lean`).

Deprecated names must NOT appear in a 0-warning probe: `div_le_div_iff`, `div_le_div_right`,
`div_le_div_left`, `inv_le_inv`, `le_div_iff`, `div_le_iff`, `lt_div_iff`, `div_lt_iff` were
measured in a temporary scratch file (verbatim warnings in `proofs/API-NOTES.md` §kasha);
`div_le_div_iff_of_pos` does not exist (`unknown identifier`).

Plan loci served: §6.1 #1–#9 (K3), §6.2 #9/#10/#16 (K3), §7.2 #12/#15 (K4), §8.1 (K5a).

Running:  proofs/scripts/lake env lean theories/kasha/probes/kasha-api-order.lean
Status:   0 errors / 0 warnings.
-/
import Mathlib

open scoped BigOperators

set_option autoImplicit false

namespace PhotoLean.Kasha.ProbeOrder

/-! ## Local copies of the definitions the recipes are stated against -/

noncomputable def decay (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := rad n + ic n

noncomputable def kashaGapThreshold (A rad0 dec0 rad1 tol : ℝ) : ℝ :=
  A * rad0 * tol / (rad1 * dec0 * (1 - tol))

/-! ## `#check` — division / order (the names K3 and K4 need) -/

#check @div_le_div_iff₀
#check @div_lt_div_iff₀
#check @div_le_div_iff_of_pos_right
#check @div_le_div_iff_of_pos_left
#check @le_div_iff₀
#check @div_le_iff₀
#check @lt_div_iff₀
#check @div_lt_iff₀
#check @div_pos
#check @div_nonneg
#check @div_nonneg_iff
#check @div_pos_iff_of_pos_right
#check @div_le_div_of_nonneg_left
#check @div_le_div_of_nonneg_right
#check @mul_le_mul_of_nonneg_left
#check @mul_le_mul_of_nonneg_right
#check @lt_of_mul_lt_mul_right
#check @le_of_mul_le_mul_right
#check @one_div
#check @inv_le_inv₀
#check @inv_lt_inv₀
#check @inv_anti₀
#check @inv_pos
#check @inv_nonneg
#check @one_div_le_one_div_of_le
#check @div_self
#check @div_le_one
#check @one_le_div
#check @div_lt_one
#check @inv_div
#check @one_div_one_div

/-! ## `#check` — the `abs`/`sqrt` window (K4 #14) -/

#check @sq_le_sq
#check @sq_le_sq'
#check @abs_le
#check @abs_of_nonneg
#check @abs_abs
#check @abs_nonneg
#check @sq_abs
#check @pow_le_pow_left₀
#check @Real.sqrt_sq_eq_abs
#check @Real.sqrt_le_sqrt
#check @Real.sqrt_lt_sqrt
#check @Real.sqrt_le_iff
#check @Real.le_sqrt
#check @Real.le_sqrt'
#check @Real.lt_sqrt
#check @Real.sq_sqrt
#check @Real.mul_self_sqrt
#check @Real.sqrt_nonneg
#check @Real.sqrt_pos

/-! ## K3 #1 ⟺ K3 #2 — the cross-multiplication (`div_le_div_iff₀`) -/

/-- The arithmetic core of `kashaWithin_one_iff_rates` ⟺ `kashaWithin_one_iff_ratio`: the rate form
and the funnel-ratio form are the same inequality after multiplying by the positive
`tol * (rad 1 * decay 0)`.  `div_le_div_iff₀` is stated with the *denominators* as its positivity
hypotheses (`0 < b`, `0 < d`), and the `↔` has `a * d ≤ c * b` on the right. -/
theorem kashaWithin_one_iff_ratio_step {rad ic : ℕ → ℝ} {tol : ℝ}
    (h0 : 0 < decay rad ic 0) (htol : 0 < tol) (hr : 0 < rad 1) :
    (rad 1 * decay rad ic 0 * (1 - tol) ≤ tol * (rad 0 * ic 1)) ↔
      (1 - tol) / tol ≤ rad 0 * ic 1 / (rad 1 * decay rad ic 0) := by
  have hden : 0 < rad 1 * decay rad ic 0 := mul_pos hr h0
  rw [div_le_div_iff₀ htol hden]
  constructor <;> intro h <;> nlinarith [h]

/-! ## K3 #2 ⟺ K3 #3 — cancelling the lowest level's own rate -/

/-- The cancellation step of `kashaWithin_one_iff_ic_ratio` (K3 #3): the cross-multiplied rate form
contains the common positive factor `rad 0`; `lt_of_mul_lt_mul_right` removes it **after the two
sides are reassociated so that `rad 0` is the right factor** — its positivity hypothesis is the
`0 ≤ ·` of that *cancelled* factor, not of the result. -/
theorem ic_ratio_cancel_step {rad ic : ℕ → ℝ} {tol : ℝ} (hr0 : 0 < rad 0)
    (h : rad 1 * rad 0 * (1 - tol) < tol * (rad 0 * ic 1)) :
    rad 1 * (1 - tol) < tol * ic 1 := by
  have h' : rad 1 * (1 - tol) * rad 0 < tol * ic 1 * rad 0 := by linarith [h]
  exact lt_of_mul_lt_mul_right h' hr0.le

/-- K3 #3's own shape: `ic 1 / rad 1` below the boundary contradicts the cross-multiplied rate form
(the negative control behind K3 #9). -/
theorem not_rate_form_of_ic_ratio_lt {rad ic : ℕ → ℝ} {tol : ℝ}
    (hic0 : ic 0 = 0) (hr0 : 0 < rad 0) (htol : 0 < tol) (hr : 0 < rad 1)
    (h : ic 1 / rad 1 < (1 - tol) / tol) :
    ¬ (rad 1 * decay rad ic 0 * (1 - tol) ≤ tol * (rad 0 * ic 1)) := by
  intro hc
  have hdec : decay rad ic 0 = rad 0 := by rw [decay, hic0, add_zero]
  rw [hdec] at hc
  have h' : ic 1 * tol < (1 - tol) * rad 1 := (div_lt_div_iff₀ hr htol).mp h
  nlinarith [h', hc]

/-! ## K4 #12/#15 — the reciprocal of the gap threshold -/

/-- The reciprocal identity behind K4 #12: `1 / kashaGapThreshold = rad1·dec0·(1-tol) / (A·rad0·tol)`
(the form in which the Marcus bridge needs `1/K`). -/
theorem one_div_kashaGapThreshold {A rad0 dec0 rad1 tol : ℝ} :
    1 / kashaGapThreshold A rad0 dec0 rad1 tol
      = rad1 * dec0 * (1 - tol) / (A * rad0 * tol) := by
  unfold kashaGapThreshold
  rw [one_div, inv_div]

/-- The same reciprocal written with `inv_le_inv₀`: turning `(1-tol)/tol ≤ F` around by taking
inverses needs *both* sides positive, and `inv_le_inv₀` returns the **reversed** order. -/
theorem inv_le_inv_step {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x ≤ y) : 1 / y ≤ 1 / x := by
  rw [one_div, one_div]
  exact (inv_le_inv₀ hy hx).mpr h

/-! ## K3 #10 — the strict threshold step (`div_lt_div_iff₀`) -/

set_option linter.unusedVariables false in
/-- `kashaThreshold_attained` (K3 #10) needs `tol' < tol ⇒ (1-tol)/tol < (1-tol')/tol'`; with
`div_lt_div_iff₀` this is a two-line `nlinarith`.  (`h2 : tol < 1` is part of the plan's premise set
but is *not consumed* by this step: `tol' < tol` alone forces it; the linter is off locally.)
Note the required order: `set_option … in` must NOT follow the doc comment — block comment →
`set_option … in` → doc comment + theorem (the BEP-round lesson). -/
theorem threshold_strict_step {tol tol' : ℝ} (h0 : 0 < tol') (h1 : tol' < tol) (h2 : tol < 1) :
    (1 - tol) / tol < (1 - tol') / tol' := by
  have h0' : 0 < tol := lt_trans h0 h1
  rw [div_lt_div_iff₀ h0' h0]
  nlinarith

/-! ## K4 #14 — the sqrt window, both routes -/

/-- Route 1 (four lines): the window is a `sq_le_sq` after writing both sides as squares.  The
right-hand `R` must be rewritten **under `conv_rhs`** — a plain `rw [← Real.sq_sqrt hR]` also hits
the `R` inside `Real.sqrt R` and produces the unsolved goal `|x| ≤ √(√R ^ 2)`. -/
theorem sq_le_iff_abs_le_sqrt {R x : ℝ} (hR : 0 ≤ R) :
    x ^ 2 ≤ R ↔ |x| ≤ Real.sqrt R := by
  nth_rewrite 1 [← Real.sq_sqrt hR]
  rw [← sq_abs x, sq_le_sq, abs_abs, abs_of_nonneg (Real.sqrt_nonneg R)]

/-- Route 2a (the BEP `calc` route, forward): `|x| = √(x²) ≤ √R`. -/
theorem abs_le_sqrt_of_sq_le {R x : ℝ} (h : x ^ 2 ≤ R) : |x| ≤ Real.sqrt R :=
  calc |x| = Real.sqrt (x ^ 2) := (Real.sqrt_sq_eq_abs x).symm
    _ ≤ Real.sqrt R := Real.sqrt_le_sqrt h

/-- Route 2b (the BEP `calc` route, backward): square both sides and use `Real.sq_sqrt`. -/
theorem sq_le_of_abs_le_sqrt {R x : ℝ} (hR : 0 ≤ R) (h : |x| ≤ Real.sqrt R) : x ^ 2 ≤ R := by
  have h1 : x ^ 2 ≤ (Real.sqrt R) ^ 2 :=
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ (Real.sqrt R) ^ 2 := pow_le_pow_left₀ (abs_nonneg x) h 2
  rwa [Real.sq_sqrt hR] at h1

/-- The K4 #14 shape verbatim: with `R = 4·lam·(kB·T)·log K` and `0 ≤ R`, the squared-gap form
(K4 #12) and the half-width form are the same statement. -/
theorem kashaWindow_halfWidth_step {R lam x : ℝ} (hR : 0 ≤ R) :
    (lam - x) ^ 2 ≤ R ↔ |lam - x| ≤ Real.sqrt R :=
  sq_le_iff_abs_le_sqrt hR

end PhotoLean.Kasha.ProbeOrder
