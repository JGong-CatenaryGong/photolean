/-
Kasha milestone — API probe (topic C): `Real.exp` / `Real.log`, and the K4 #12 Marcus bridge.

Scope. `kashaWithin_one_marcus` (K4 #12) is the composition of
  (i) the K3 #1 rate criterion,
  (ii) `ic 1 = marcusIC A lam kB T x = A · exp (-(barrier lam x) / (kB·T))`,
  (iii) the `exp`/`log` inversion with the explicit positive-side hypotheses,
  (iv) the reciprocal of `kashaGapThreshold` (K4 #15 positivity),
and this probe kernel-checks each step plus the *whole* arithmetic content of the bridge
(`marcus_gap_window_step`, the rate form ⟺ the squared-gap form of the skeleton's K4 #12).

Plan loci served: §7.2 #12/#13/#15/#16 (K4), §6.1 #1 (K3, the rate form it starts from).

Running:  proofs/scripts/lake env lean theories/kasha/probes/kasha-api-logexp.lean
Status:   0 errors / 0 warnings.
-/
import Mathlib
import PhotoLean.Marcus.Basic

open scoped BigOperators

set_option autoImplicit false

namespace PhotoLean.Kasha.ProbeLogExp

/-! ## Cross-module names the K4 bridge consumes (`PhotoLean.Marcus`, delivered) -/

#check PhotoLean.Marcus.barrier
#check PhotoLean.Marcus.rate

/-! ## `#check` — `Real.exp` / `Real.log` -/

#check @Real.exp_pos
#check @Real.exp_ne_zero
#check @Real.exp_le_exp
#check @Real.exp_lt_exp
#check @Real.exp_add
#check @Real.exp_sub
#check @Real.exp_neg
#check @Real.exp_le_one_iff
#check @Real.exp_lt_one_iff
#check @Real.one_lt_exp_iff
#check @Real.log_pos
#check @Real.log_nonneg
#check @Real.log_nonpos
#check @Real.log_neg
#check @Real.log_one
#check @Real.log_zero
#check @Real.log_exp
#check @Real.exp_log
#check @Real.log_le_log
#check @Real.log_lt_log
#check @Real.log_le_log_iff
#check @Real.log_lt_log_iff
#check @Real.le_log_iff_exp_le
#check @Real.log_le_iff_le_exp
#check @Real.log_div
#check @Real.log_inv
#check @Real.log_mul
#check @Real.log_pow
#check @Real.log_le_sub_one_of_pos
#check @Real.exp_injective
#check @Real.log_injOn_pos

/-! ## The requested chain: `c ≤ A · exp (-b/k)` ⟺ `b ≤ k · log (A/c)` -/

/-- The K4 #12 engine, in the requested form.  Positivity is explicit on all three constants
(`0 < c`, `0 < A`, `0 < k`); the route is
`div_le_iff₀` → `Real.log_le_iff_le_exp` → `Real.log_div` → `le_div_iff₀` → `linarith`, and back
`div_le_iff₀` → `Real.log_div` → `Real.log_le_iff_le_exp` → `div_le_iff₀`. -/
theorem exp_neg_div_iff_log {A b c k : ℝ} (hc : 0 < c) (hA : 0 < A) (hk : 0 < k) :
    c ≤ A * Real.exp (-b / k) ↔ b ≤ k * Real.log (A / c) := by
  have hcA : 0 < c / A := div_pos hc hA
  constructor
  · intro h
    have h1 : c / A ≤ Real.exp (-b / k) := by
      rw [div_le_iff₀ hA]
      linarith [h]
    have h2 : Real.log (c / A) ≤ -b / k := (Real.log_le_iff_le_exp hcA).mpr h1
    have h3 : Real.log (c / A) * k ≤ -b := (le_div_iff₀ hk).mp h2
    rw [Real.log_div (ne_of_gt hc) (ne_of_gt hA)] at h3
    rw [Real.log_div (ne_of_gt hA) (ne_of_gt hc)]
    linarith [h3]
  · intro h
    rw [Real.log_div (ne_of_gt hA) (ne_of_gt hc)] at h
    have h1 : b / k ≤ Real.log A - Real.log c := by
      rw [div_le_iff₀ hk]
      linarith [h]
    have h2 : Real.log (c / A) ≤ -b / k := by
      rw [Real.log_div (ne_of_gt hc) (ne_of_gt hA), neg_div]
      linarith [h1]
    have h3 : c / A ≤ Real.exp (-b / k) := (Real.log_le_iff_le_exp hcA).mp h2
    rw [div_le_iff₀ hA] at h3
    linarith [h3]

/-- The bridge's actual shape (`A` has been absorbed into the threshold): with `0 < K`, `0 < k`,
`1/K ≤ exp (-B/k) ⟺ B ≤ k·log K`.  This is what `kashaGapThreshold` feeds. -/
theorem one_div_le_exp_iff {B K k : ℝ} (hK : 0 < K) (hk : 0 < k) :
    1 / K ≤ Real.exp (-B / k) ↔ B ≤ k * Real.log K := by
  have h := exp_neg_div_iff_log (A := 1) (b := B) (c := 1 / K) (k := k)
    (by positivity) (by norm_num) hk
  simpa only [one_div_one_div, one_mul] using h

/-! ## K4 #15 — positivity of the gap threshold, and K4 #16 -/

noncomputable def kashaGapThreshold (A rad0 dec0 rad1 tol : ℝ) : ℝ :=
  A * rad0 * tol / (rad1 * dec0 * (1 - tol))

theorem kashaGapThreshold_pos {A rad0 dec0 rad1 tol : ℝ} (hA : 0 < A) (hr0 : 0 < rad0)
    (hdec0 : 0 < dec0) (hr1 : 0 < rad1) (htol0 : 0 < tol) (htol1 : tol < 1) :
    0 < kashaGapThreshold A rad0 dec0 rad1 tol := by
  -- `positivity` does not discharge `0 < 1 - tol` from `tol < 1` here; `nlinarith` does.
  unfold kashaGapThreshold
  apply div_pos
  · positivity
  · have h1 : (0 : ℝ) < 1 - tol := by linarith
    positivity

noncomputable def marcusIC (A lam kB T x : ℝ) : ℝ :=
  A * Real.exp (-(PhotoLean.Marcus.barrier lam x) / (kB * T))

theorem marcusIC_pos {A lam kB T x : ℝ} (hA : 0 < A) : 0 < marcusIC A lam kB T x := by
  unfold marcusIC
  positivity

/-! ## The whole arithmetic content of K4 #12 — the rate form ⟺ the squared-gap form -/

/-- **K4 #12's arithmetic core, kernel-checked.**  The K3 #1 rate criterion with
`ic 1 = marcusIC A lam kB T x` is *equivalent* to the squared-gap criterion of the skeleton:

`rad1 · dec0 · (1-tol) ≤ tol · rad0 · A · exp (-(barrier lam x)/(kB·T))`
  ⟺ `(lam - x)^2 ≤ 4 · lam · (kB·T) · log (kashaGapThreshold A rad0 dec0 rad1 tol)`.

Recipe: (1) divide by `tol·rad0·A > 0` (`div_le_iff₀`), (2) rewrite the quotient into
`1/kashaGapThreshold` (`one_div` + `inv_div` + `ring_nf`), (3) `one_div_le_exp_iff` (needs
`0 < kashaGapThreshold` — K4 #15), (4) `unfold barrier` and `div_le_iff₀ (0 < 4·lam)`, then
`linarith`.  `hbar : barrier lam x = (lam-x)^2/(4·lam)` is the delivered body, no hypothesis. -/
theorem marcus_gap_window_step {rad0 dec0 rad1 A lam kB T x tol : ℝ}
    (hA : 0 < A) (hr0 : 0 < rad0) (hdec0 : 0 < dec0) (hr1 : 0 < rad1)
    (htol0 : 0 < tol) (htol1 : tol < 1) (hkT : 0 < kB * T) (hlam : 0 < lam) :
    rad1 * dec0 * (1 - tol)
        ≤ tol * rad0 * (A * Real.exp (-(PhotoLean.Marcus.barrier lam x) / (kB * T))) ↔
      (lam - x) ^ 2 ≤ 4 * lam * (kB * T) * Real.log (kashaGapThreshold A rad0 dec0 rad1 tol) := by
  have hK : 0 < kashaGapThreshold A rad0 dec0 rad1 tol :=
    kashaGapThreshold_pos hA hr0 hdec0 hr1 htol0 htol1
  have hden : 0 < tol * rad0 * A := by positivity
  have hkey : rad1 * dec0 * (1 - tol)
        ≤ tol * rad0 * (A * Real.exp (-(PhotoLean.Marcus.barrier lam x) / (kB * T))) ↔
      rad1 * dec0 * (1 - tol) / (tol * rad0 * A)
        ≤ Real.exp (-(PhotoLean.Marcus.barrier lam x) / (kB * T)) := by
    rw [div_le_iff₀ hden]
    constructor <;> intro h <;> linarith [h]
  have hquot : rad1 * dec0 * (1 - tol) / (tol * rad0 * A)
      = 1 / kashaGapThreshold A rad0 dec0 rad1 tol := by
    unfold kashaGapThreshold
    rw [one_div, inv_div]
    ring_nf
  rw [hkey, hquot, one_div_le_exp_iff hK hkT]
  unfold PhotoLean.Marcus.barrier
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * lam)]
  constructor <;> intro h <;> linarith [h]

end PhotoLean.Kasha.ProbeLogExp
