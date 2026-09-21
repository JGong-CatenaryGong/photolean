/-
  PhotoLean — PhotoLean/Goldschmidt/Criterion.lean

  The Goldschmidt theory, milestone G3 (the **law layer**): how the tolerance factor
  `tolFac rA rB rO = (rA + rO) / (√2 * (rB + rO))` depends on its three radii, and the exact
  condition under which a triple conforms to a band `[lo, hi]`.

  Design of record: `theories/goldschmidt/plan.md` §1.3 (milestone G3), §6 (the row table) and §12
  (honesty table).  Statement authority:
  `theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean` § `## G3`, which every signature
  below matches word for word (checked by
  `python3 theories/BEP/probes/bep-fidelity.py --theory goldschmidt --milestone G3`).

  Content.  Monotonicity in `rA` (strictly increasing) and in `rB` (strictly decreasing); the `rO`
  trichotomy — strictly increasing for `rA < rB`, strictly decreasing for `rB < rA`, and constant
  exactly at `rA = rB`, where the value is `1/√2`; scale invariance and the ratio form; the exact and
  unconditional affine shift
  law `t(rA + d) - t(rA) = d / (√2 (rB + rO))` and its absolute value; the ideal-packing
  identification at the point band; the **radius-window equivalence**
  `GoldschmidtConforms lo hi rA rB rO ↔ rAMin lo rB rO ≤ rA ∧ rA ≤ rAMax hi rB rO` (exact for every
  band, including inverted ones, because it is the result of dividing by the positive denominator
  `√2 (rB + rO)`); its `√2`-free **squared** form (the decision form of the rational layer G5); the
  symmetric band `1 ± δ` as an absolute-value bound, with **no** hypothesis on `δ` (at `δ > 1` the
  band is empty and both sides of the equivalence are false); the classic `4/5`–`1` band; band
  monotonicity; the bridge to the G1 classifier; and band-level non-vacuity.

  Physical premises are explicit hypotheses (engine iron rule 3): `0 < rB + rO` wherever the
  denominator is divided by (including both trichotomy branches, where it is what makes the pole
  `rO = -rB` unreachable), `0 ≤ lo` / `0 ≤ hi` and `0 ≤ rA + rO` in the squared rows, `0 < rA + rO`
  for the strict anti-monotonicity in `rB`, and `0 ≤ rB` in the constant row.  Nothing is hidden in a
  definition.

  Authority defect found in the kernel on 2026-09-21 (before delivery) and corrected in the authority
  by the lead — plan §3.1 items 6–7.  Three G3 drafts were FALSE as written, because `0 < rO` does
  **not** keep the pole `rO = -rB` of `rO ↦ t` out of the quantifier's range, and the factor is
  monotone in `rO` only on each side of that pole:

  1. `tolFac_mono_rO_of_lt` with `(hrO : 0 < rO)`: kernel witness `rA = -2, rB = -1, rO = 1/2,
     rO' = 2`, all three premises true and `tolFac (-2) (-1) (1/2) = 3/√2 > 0 = tolFac (-2) (-1) 2`.
  2. `tolFac_anti_rO_of_lt` with `(hrO : 0 < rO)`: kernel witness `rA = -1, rB = -2, rO = 1/2,
     rO' = 3`, where the factor *increases* from `1/(3√2)` to `√2`.
  3. `tolFac_rO_const_iff` with `(hrO : 0 < rO)`: FALSE in the backward direction — at
     `rA = rB = -1, rO = 1` the right side holds while the quantified left side fails at `rO' = 2`
     (`1/√2` versus `0/0 = 0`).  Replacing `0 < rO` by `0 < rB + rO` does not repair it either (the
     quantifier still reaches the pole), so the delivered row takes `(hrB : 0 ≤ rB) (hrO : 0 < rO)`.

  The three rows below are the **corrected** authority rows: `0 < rO` replaced by the premise the two
  denominators actually need (`0 < rB + rO`) in the first two, and `0 ≤ rB` added in the third.  No
  signature here is the prover's own invention — each matches the corrected authority word for word.

  The risk-probe lesson behind this finding: the Sprint-0 probe that was supposed to catch these rows
  before dispatch did not compile at the time (67 errors, concentrated in exactly these rows), so its
  "0 error" claim was never evidence; see `proofs/EXPERIENCE.md`.
-/
import PhotoLean.Goldschmidt.Basic

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Goldschmidt

/-! ## Private helpers for the G3 rows

  Not declarations of the theory: `denom_pos` is the positivity of the tolerance-factor denominator
  under the physical premise `0 < rB + rO`, and the rest are the algebraic normal forms used by the
  window and squared rows. -/

private theorem sqrtTwo_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)

private theorem sqrtTwo_ne : (Real.sqrt 2 : ℝ) ≠ 0 := (Real.sqrt_ne_zero').mpr (by norm_num)

private theorem sqrtTwo_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- The tolerance-factor denominator is positive under the explicit physical premise
`0 < rB + rO`. -/
private theorem denom_pos {rB rO : ℝ} (h : 0 < rB + rO) : 0 < Real.sqrt 2 * (rB + rO) :=
  mul_pos sqrtTwo_pos h

/-- `rAMin lo rB rO` in the factored shape the window row divides by. -/
private theorem rAMin_eq (lo rB rO : ℝ) :
    rAMin lo rB rO = lo * (Real.sqrt 2 * (rB + rO)) - rO := by
  unfold rAMin
  ring

/-- `rAMax hi rB rO` in the factored shape the window row divides by. -/
private theorem rAMax_eq (hi rB rO : ℝ) :
    rAMax hi rB rO = hi * (Real.sqrt 2 * (rB + rO)) - rO := by
  unfold rAMax
  ring

/-- The square of the tolerance-factor denominator is `√2`-free: `(√2 (rB + rO))^2 = 2 (rB + rO)^2`.
This is the identity that turns the radius window into the squared criterion of G5. -/
private theorem denom_sq (rB rO : ℝ) :
    (Real.sqrt 2 * (rB + rO)) ^ 2 = 2 * (rB + rO) ^ 2 := by
  rw [mul_pow, sqrtTwo_sq]

/-- The factor at `rA = rB` is `1/√2` whenever the denominator does not vanish. -/
private theorem tolFac_self {rB rO : ℝ} (h : rB + rO ≠ 0) : tolFac rB rB rO = 1 / Real.sqrt 2 := by
  unfold tolFac
  rw [div_eq_div_iff (mul_ne_zero sqrtTwo_ne h) sqrtTwo_ne]
  ring

/-! ## G3 — law layer (`PhotoLean/Goldschmidt/Criterion.lean`) -/

/-- Strict monotonicity in `rA`: the A cation never loses contact by growing.  The denominator
`√2 (rB + rO)` is positive by the explicit physical premise, so `div_lt_div_of_pos_right` applies
(plan §6). -/
theorem tolFac_strictMono_rA {rA rA' rB rO : ℝ} (h : 0 < rB + rO) (hlt : rA < rA') :
    tolFac rA rB rO < tolFac rA' rB rO := by
  unfold tolFac
  exact div_lt_div_of_pos_right (by linarith) (denom_pos h)

/-- Strict anti-monotonicity in `rB`: the larger B cation stretches the octahedral contact and lowers
the factor.  `0 < rA + rO` is the positivity of the numerator and `0 < rB + rO` that of the smaller
denominator; `div_lt_div_of_pos_left` reduces the row to the strict monotonicity of
`rB ↦ √2 (rB + rO)` (plan §6). -/
theorem tolFac_strictAnti_rB {rA rB rB' rO : ℝ} (h : 0 < rB + rO) (hA : 0 < rA + rO)
    (hlt : rB < rB') : tolFac rA rB' rO < tolFac rA rB rO := by
  unfold tolFac
  refine div_lt_div_of_pos_left hA (denom_pos h) ?_
  nlinarith [sqrtTwo_pos]

/-- The `rO` trichotomy, increasing branch: for `rA < rB` the factor is strictly increasing in `rO`.
The premise `0 < rB + rO` is what makes the trichotomy true — it keeps the pole `rO = -rB` of
`rO ↦ t` out of the interval, so both denominators are positive and `div_lt_div_iff₀` cross-multiplies
into the residual `√2 (rA - rB) (rO' - rO) < 0`.

Authority history (plan §3.1 item 6): the first draft carried `(hrO : 0 < rO)` instead, which does
**not** imply `0 < rB + rO`; the draft is FALSE, with the kernel witness `rA = -2, rB = -1,
rO = 1/2, rO' = 2` satisfying all its premises and giving `t(rO') = 0 < 3/√2 = t(rO)`. `0 < rO` was
then dropped as non-load-bearing rather than kept beside the premise that carries the row. -/
theorem tolFac_mono_rO_of_lt {rA rB rO rO' : ℝ} (hB : 0 < rB + rO) (h : rA < rB)
    (hlt : rO < rO') : tolFac rA rB rO < tolFac rA rB rO' := by
  unfold tolFac
  rw [div_lt_div_iff₀ (denom_pos hB) (denom_pos (by linarith)), ← sub_pos]
  rw [show (rA + rO') * (Real.sqrt 2 * (rB + rO)) - (rA + rO) * (Real.sqrt 2 * (rB + rO'))
      = Real.sqrt 2 * ((rB - rA) * (rO' - rO)) by ring]
  exact mul_pos sqrtTwo_pos (mul_pos (by linarith) (by linarith))

/-- The `rO` trichotomy, decreasing branch: for `rB < rA` the factor is strictly decreasing in `rO`
— the mirror image of `tolFac_mono_rO_of_lt`, with the same premise `0 < rB + rO` and the same
cross-multiplication (the residual only changes sign).  Authority history (plan §3.1 item 6): the
draft's `(hrO : 0 < rO)` is FALSE here too, refuted by `rA = -1, rB = -2, rO = 1/2, rO' = 3`, where
the factor *increases* from `1/(3√2)` to `√2`. -/
theorem tolFac_anti_rO_of_lt {rA rB rO rO' : ℝ} (hB : 0 < rB + rO) (h : rB < rA)
    (hlt : rO < rO') : tolFac rA rB rO' < tolFac rA rB rO := by
  unfold tolFac
  rw [div_lt_div_iff₀ (denom_pos (by linarith)) (denom_pos hB), ← sub_pos]
  rw [show (rA + rO) * (Real.sqrt 2 * (rB + rO')) - (rA + rO') * (Real.sqrt 2 * (rB + rO))
      = Real.sqrt 2 * ((rA - rB) * (rO' - rO)) by ring]
  exact mul_pos sqrtTwo_pos (mul_pos (by linarith) (by linarith))

/-- The constant branch of the `rO` trichotomy: the factor is independent of `rO` exactly at
`rA = rB` (where it is `1/√2`).

The hypotheses are load-bearing and are *not* the naive `0 < rO` (plan §3.1 item 7): the quantified
left-hand side ranges over every positive `rO'`, and the pole `rO' = -rB` must be unreachable for it —
which is exactly what `0 ≤ rB` gives, since then `rB + rO' ≥ rO' > 0`.  With `rA = rB = -1, rO = 1`
the right-hand side holds while the left fails at `rO' = 2` (`1/√2` versus `0/0 = 0`), and replacing
`0 < rO` by `0 < rB + rO` does not repair the row either (at `rO = 2` the factor is `1/√2`, while
`rO' = 1` lands on the pole and gives `0`).

Forward direction: instantiate the hypothesis at `rO + 1` and `rO + 2` (both positive, both with
positive denominator by `hrB`), equate the two values and cross-multiply with `div_eq_div_iff`; the
residual collapses to `(rB + rO) = (rA + rO)`.  Backward direction: at `rA = rB` both sides are the
`rA = rB` value `1/√2` of `tolFac_self`. -/
theorem tolFac_rO_const_iff {rA rB rO : ℝ} (hrB : 0 ≤ rB) (hrO : 0 < rO) :
    (∀ rO' : ℝ, 0 < rO' → tolFac rA rB rO' = tolFac rA rB rO) ↔ rA = rB := by
  constructor
  · intro hh
    have h1 := hh (rO + 1) (by linarith)
    have h2 := hh (rO + 2) (by linarith)
    have hp1 : (0 : ℝ) < Real.sqrt 2 * (rB + (rO + 1)) := denom_pos (by linarith)
    have hp2 : (0 : ℝ) < Real.sqrt 2 * (rB + (rO + 2)) := denom_pos (by linarith)
    have h3 : (rA + (rO + 2)) * (Real.sqrt 2 * (rB + (rO + 1))) =
        (rA + (rO + 1)) * (Real.sqrt 2 * (rB + (rO + 2))) := by
      have heq : tolFac rA rB (rO + 2) = tolFac rA rB (rO + 1) := by rw [h2, h1]
      unfold tolFac at heq
      exact (div_eq_div_iff hp2.ne' hp1.ne').mp heq
    nlinarith [sqrtTwo_pos]
  · intro hEq rO' hrO'
    rw [hEq,
      tolFac_self (ne_of_gt (by linarith : (0 : ℝ) < rB + rO')),
      tolFac_self (ne_of_gt (by linarith : (0 : ℝ) < rB + rO))]

/-- The factor is `1/√2` exactly when `rA = rB`.  Forward: cross-multiply the equality
`(rA + rO)/(√2 (rB + rO)) = 1/√2` with `div_eq_div_iff`, cancel `√2` and cancel `rO`.  Backward: at
`rA = rB` the numerator and the outer `√2 (rB + rO)` cancel, leaving `1/√2` (plan §6). -/
theorem tolFac_eq_invSqrtTwo_iff {rA rB rO : ℝ} (h : 0 < rB + rO) :
    tolFac rA rB rO = 1 / Real.sqrt 2 ↔ rA = rB := by
  have hD : (0 : ℝ) < Real.sqrt 2 * (rB + rO) := denom_pos h
  constructor
  · intro ht
    have h2 : (rA + rO) * Real.sqrt 2 = 1 * (Real.sqrt 2 * (rB + rO)) :=
      (div_eq_div_iff hD.ne' sqrtTwo_ne).mp ht
    have h3 : Real.sqrt 2 * (rA + rO) = Real.sqrt 2 * (rB + rO) := by
      rw [mul_comm (Real.sqrt 2) (rA + rO), h2, one_mul]
    have h4 : rA + rO = rB + rO := mul_left_cancel₀ sqrtTwo_ne h3
    linarith
  · intro hEq
    rw [hEq]
    exact tolFac_self h.ne'

/-- Scale invariance: the factor depends only on the two ratios of the radii, so common scaling of
all three radii leaves it unchanged.  The proof factors `c` out of both sums and cancels it with
`mul_div_mul_left`; no positivity of `c` is needed, only `c ≠ 0` — at a vanishing sum both sides are
`0` because division is totalized (`x / 0 = 0`), so there is no hidden case distinction (plan §6). -/
theorem tolFac_scale_invariance {c rA rB rO : ℝ} (hc : c ≠ 0) :
    tolFac (c * rA) (c * rB) (c * rO) = tolFac rA rB rO := by
  unfold tolFac
  rw [show c * rA + c * rO = c * (rA + rO) by ring,
    show c * rB + c * rO = c * (rB + rO) by ring,
    show Real.sqrt 2 * (c * (rB + rO)) = c * (Real.sqrt 2 * (rB + rO)) by ring]
  exact mul_div_mul_left (rA + rO) (Real.sqrt 2 * (rB + rO)) hc

/-- The ratio form of the factor: writing `rA/rO + 1 = (rA + rO)/rO` and likewise for `rB` turns
`t` into a function of the two dimensionless ratios alone.  Only `rO ≠ 0` is needed; the vanishing of
`rB + rO` is handled by `field_simp` on both sides (plan §6). -/
theorem tolFac_ratio_form {rA rB rO : ℝ} (hrO : rO ≠ 0) :
    tolFac rA rB rO = (rA / rO + 1) / (Real.sqrt 2 * (rB / rO + 1)) := by
  have hA : rA / rO + 1 = (rA + rO) / rO := by
    field_simp
  have hB : rB / rO + 1 = (rB + rO) / rO := by
    field_simp
  rw [hA, hB, ← mul_div_assoc]
  unfold tolFac
  by_cases hB0 : rB + rO = 0
  · simp [hB0]
  · field_simp [mul_ne_zero sqrtTwo_ne hB0]

/-- The **exact affine shift law**, unconditional: adding `d` to `rA` shifts the factor by exactly
`d` over the denominator.  `add_div` splits the shifted quotient into the old one plus
`d / (√2 (rB + rO))`, and the old quotient cancels; the identity holds even at a vanishing
denominator, where both sides are `0` (plan §6). -/
theorem tolFac_shift (rA rB rO d : ℝ) :
    tolFac (rA + d) rB rO - tolFac rA rB rO = d / (Real.sqrt 2 * (rB + rO)) := by
  unfold tolFac
  rw [show rA + d + rO = (rA + rO) + d by ring, add_div]
  ring

/-- Absolute form of the shift law: the sensitivity of the factor to an `rA` shift is `|d|` over the
positive denominator.  Immediate from `tolFac_shift` by `abs_div` and the positivity of the
denominator (plan §6). -/
theorem tolFac_abs_shift_eq {rA rB rO d : ℝ} (h : 0 < rB + rO) :
    |tolFac (rA + d) rB rO - tolFac rA rB rO| = |d| / (Real.sqrt 2 * (rB + rO)) := by
  rw [tolFac_shift, abs_div, abs_of_pos (denom_pos h)]

/-- The ideal A radius conforms to a band exactly when the band contains `1` (plan §6). -/
theorem conforms_at_idealA_iff {lo hi rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms lo hi (idealA rB rO) rB rO ↔ lo ≤ 1 ∧ 1 ≤ hi := by
  unfold GoldschmidtConforms InBand
  rw [idealA_tolFac h]

/-- The **point band** `1`–`1` is exactly the ideal packing `rA + rO = idealAO rB rO` (plan §6): the
band predicate on a singleton band is `t = 1`, and `contact_iff_tolFac_one` identifies that with the
A–O contact equation. -/
theorem conforms_iff_ideal_packing {rA rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms 1 1 rA rB rO ↔ rA + rO = idealAO rB rO := by
  unfold GoldschmidtConforms InBand
  rw [contact_iff_tolFac_one h]
  exact ⟨fun hk => le_antisymm hk.2 hk.1, fun hk => ⟨hk.ge, hk.le⟩⟩

/-- **The radius-window equivalence** (the headline row of G3).  A triple conforms to the band
`[lo, hi]` exactly when its A radius lies in the window cut out by the two band edges:
`rAMin lo rB rO ≤ rA ≤ rAMax hi rB rO`, where the edges are the closed forms `lo √2 (rB + rO) - rO`
and `hi √2 (rB + rO) - rO`.

Proof (no squaring anywhere): unfold the verdict and the two edges, then divide each side by the
denominator `√2 (rB + rO)`, which is positive by the explicit premise, using `le_div_iff₀` /
`div_le_iff₀`; the residual claims are affine.  Because the equivalence is *exact* and carries no
band-non-emptiness premise, it is valid for every band — including inverted ones (`hi < lo`), where
both sides are false (plan §6, and the same design as the corrected
`goldschmidtZone_eq_tooLarge_iff` of G1, plan §3.1 item 4). -/
theorem conforms_iff_radius_window {lo hi rA rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms lo hi rA rB rO ↔ rAMin lo rB rO ≤ rA ∧ rA ≤ rAMax hi rB rO := by
  have hD : 0 < Real.sqrt 2 * (rB + rO) := denom_pos h
  unfold GoldschmidtConforms InBand tolFac
  rw [rAMin_eq, rAMax_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [le_div_iff₀ hD] at h1; linarith,
      by rw [div_le_iff₀ hD] at h2; linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [le_div_iff₀ hD]; linarith, by rw [div_le_iff₀ hD]; linarith⟩

/-- Lower edge, squared form: for `0 ≤ lo` and non-negative numerator, the window's lower bound is
equivalent to the `√2`-free inequality `2 lo² (rB + rO)² ≤ (rA + rO)²`.  Both sides of the affine
form `lo √2 (rB + rO) ≤ rA + rO` are non-negative — the left one because `lo ≥ 0` and the
denominator is positive — so `mul_self_le_mul_self_iff` applies, and `(√2 (rB + rO))² = 2 (rB + rO)²`
is `Real.sq_sqrt` plus distribution (plan §6). -/
theorem rAMin_le_iff_sq {lo rA rB rO : ℝ} (hlo : 0 ≤ lo) (h : 0 < rB + rO) (hA : 0 ≤ rA + rO) :
    rAMin lo rB rO ≤ rA ↔ 2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 := by
  have hD : 0 < Real.sqrt 2 * (rB + rO) := denom_pos h
  have hnn : 0 ≤ lo * (Real.sqrt 2 * (rB + rO)) := mul_nonneg hlo hD.le
  have hiff : lo * (Real.sqrt 2 * (rB + rO)) ≤ rA + rO ↔
      (lo * (Real.sqrt 2 * (rB + rO))) ^ 2 ≤ (rA + rO) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self_iff hnn hA
  have hsq : (lo * (Real.sqrt 2 * (rB + rO))) ^ 2 = 2 * lo ^ 2 * (rB + rO) ^ 2 := by
    rw [mul_pow, denom_sq]
    ring
  rw [rAMin_eq, ← hsq, sub_le_iff_le_add]
  exact hiff

/-- Upper edge, squared form: the mirror of `rAMin_le_iff_sq` for the upper band edge — for `0 ≤ hi`
and non-negative numerator, `rA ≤ rAMax hi rB rO` is equivalent to
`(rA + rO)² ≤ 2 hi² (rB + rO)²` (plan §6). -/
theorem le_rAMax_iff_sq {hi rA rB rO : ℝ} (hhi : 0 ≤ hi) (h : 0 < rB + rO) (hA : 0 ≤ rA + rO) :
    rA ≤ rAMax hi rB rO ↔ (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2 := by
  have hD : 0 < Real.sqrt 2 * (rB + rO) := denom_pos h
  have hnn : 0 ≤ hi * (Real.sqrt 2 * (rB + rO)) := mul_nonneg hhi hD.le
  have hiff : rA + rO ≤ hi * (Real.sqrt 2 * (rB + rO)) ↔
      (rA + rO) ^ 2 ≤ (hi * (Real.sqrt 2 * (rB + rO))) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self_iff hA hnn
  have hsq : (hi * (Real.sqrt 2 * (rB + rO))) ^ 2 = 2 * hi ^ 2 * (rB + rO) ^ 2 := by
    rw [mul_pow, denom_sq]
    ring
  rw [rAMax_eq, ← hsq, le_sub_iff_add_le]
  exact hiff

/-- **The `√2`-free form of the band verdict** (the row the rational decision layer G5 is built on):
under the explicit premises `0 ≤ lo`, `0 ≤ hi`, `0 < rB + rO` and `0 ≤ rA + rO`, conformance is the
pair of squared inequalities `2 lo² (rB + rO)² ≤ (rA + rO)² ≤ 2 hi² (rB + rO)²`.

Proof: the window equivalence composed with the two per-edge squared equivalences — which is exactly
why those two rows sit immediately above this one, and why the law layer precedes the rational layer
(plan §6, §3.1 item 3). -/
theorem conforms_iff_sq {lo hi rA rB rO : ℝ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (h : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) : GoldschmidtConforms lo hi rA rB rO ↔
      2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 ∧
        (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2 := by
  rw [conforms_iff_radius_window h, rAMin_le_iff_sq hlo h hA, le_rAMax_iff_sq hhi h hA]

/-- The **symmetric band** `1 ± δ`: conformance is exactly `|rA - idealA rB rO| ≤ δ * idealAO rB rO`,
i.e. the A radius is within the fraction `δ` of the ideal A–O distance of the ideal value.

The equivalence carries **no hypothesis on `δ`** — in particular not `0 ≤ δ < 1`.  That is not an
oversight but the exact statement: the window row gives `idealA - δ * idealAO ≤ rA ≤ idealA +
δ * idealAO`, and `abs_le` turns that into the absolute-value bound for *every* `δ`; at `δ > 1` the
band is empty and the two sides of the equivalence are both false (plan §3.1 item 2, where the
non-load-bearing `0 ≤ δ` draft hypothesis was removed). -/
theorem conforms_symmetric_band_iff {delta rA rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms (1 - delta) (1 + delta) rA rB rO ↔
      |rA - idealA rB rO| ≤ delta * idealAO rB rO := by
  rw [conforms_iff_radius_window h,
    show rAMin (1 - delta) rB rO = idealA rB rO - delta * idealAO rB rO by
      unfold rAMin idealA idealAO; ring,
    show rAMax (1 + delta) rB rO = idealA rB rO + delta * idealAO rB rO by
      unfold rAMax idealA idealAO; ring,
    abs_le]
  exact ⟨fun hk => ⟨by linarith, by linarith⟩, fun hk => ⟨by linarith, by linarith⟩⟩

/-- The literature's **classic band** `[4/5, 1]` as an explicit radius window:
`classicLo * idealAO rB rO - rO ≤ rA ≤ idealA rB rO`.  This is the window row with `lo = 4/5`,
`hi = 1` unfolded (`rAMax 1 rB rO = idealA rB rO` is G1's `rAMax_one` in closed form).  The band
constants remain *instances* of the band parameter — this is the only place they enter G3, via the
window they instantiate (plan §2, §6). -/
theorem conforms_classic_band_iff {rA rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms classicLo classicHi rA rB rO ↔
      classicLo * idealAO rB rO - rO ≤ rA ∧ rA ≤ idealA rB rO := by
  rw [conforms_iff_radius_window h,
    show rAMin classicLo rB rO = classicLo * idealAO rB rO - rO by
      unfold rAMin idealAO; ring,
    show rAMax classicHi rB rO = idealA rB rO by
      unfold rAMax classicHi idealA idealAO; ring]

/-- **Band monotonicity**: widening a band never loses a conforming candidate.  This is the theorem
that makes the band convention a *changeable parameter* rather than a hidden constant: any verdict
established for a narrow band transfers to every band that contains it.  No physical premise is
needed — the row is a purely order-theoretic transfer through `le_trans` (plan §6). -/
theorem conforms_of_conforms_window_le {lo lo' hi hi' rA rB rO : ℝ} (h1 : lo' ≤ lo)
    (h2 : hi ≤ hi') : GoldschmidtConforms lo hi rA rB rO →
      GoldschmidtConforms lo' hi' rA rB rO := by
  unfold GoldschmidtConforms InBand
  rintro ⟨ha, hb⟩
  exact ⟨le_trans h1 ha, le_trans hb h2⟩

/-- Bridge to the G1 classifier: the zone `ideal` is taken exactly on the band verdict.  This is the
goodschmidt `ideal` characterization of G1 (`goldschmidtZone_eq_ideal_iff`, unconditional — the
classifier's first test `t < lo` is irrelevant to the middle branch) read against the G3 definition of
conformance, so the classifier and the verdict are the same predicate (plan §6). -/
theorem goldschmidtZone_ideal_iff_conforms {lo hi rA rB rO : ℝ} :
    goldschmidtZone lo hi (tolFac rA rB rO) = GoldschmidtZone.ideal ↔
      GoldschmidtConforms lo hi rA rB rO := by
  unfold GoldschmidtConforms InBand
  exact goldschmidtZone_eq_ideal_iff lo hi (tolFac rA rB rO)

/-- Band-level non-vacuity: every non-empty band has a conforming triple among the normalized
(`rB = rO = 1`) ones.  The witness `rA = lo * √8 - 1` makes the factor exactly `lo` — not merely
inside the band — so this row is a *tightness* statement about the window's lower edge as well as a
non-vacuity statement (plan §6). -/
theorem exists_conforming {lo hi : ℝ} (h : lo ≤ hi) :
    ∃ rA : ℝ, GoldschmidtConforms lo hi rA 1 1 := by
  refine ⟨lo * (2 * Real.sqrt 2) - 1, ?_⟩
  rw [conforms_iff_radius_window (by norm_num : (0 : ℝ) < 1 + 1)]
  constructor
  · rw [show rAMin lo 1 1 = lo * (2 * Real.sqrt 2) - 1 by unfold rAMin; ring]
  · rw [show rAMax hi 1 1 = hi * (2 * Real.sqrt 2) - 1 by unfold rAMax; ring]
    nlinarith [sqrtTwo_pos, h]

/-- Every band has a triple *below* it (in particular an empty band has no conforming triple at all,
which is the sharpness companion of this row in G4).  The witness `rA = (lo - 1) * √8 - 1` gives
`t = lo - 1 < lo`, so the lower edge is violated; the row is stated for an arbitrary band and needs
no premise (plan §6). -/
theorem exists_tooSmall (lo hi : ℝ) : ∃ rA : ℝ, ¬ GoldschmidtConforms lo hi rA 1 1 := by
  refine ⟨(lo - 1) * (2 * Real.sqrt 2) - 1, ?_⟩
  rw [conforms_iff_radius_window (by norm_num : (0 : ℝ) < 1 + 1)]
  rintro ⟨h1, -⟩
  rw [show rAMin lo 1 1 = lo * (2 * Real.sqrt 2) - 1 by unfold rAMin; ring] at h1
  nlinarith [sqrtTwo_pos]

/-- Every band has a triple *above* it, the mirror of `exists_tooSmall`.  The witness
`rA = (hi + 1) * √8 - 1` gives `t = hi + 1 > hi` (plan §6). -/
theorem exists_tooLarge (lo hi : ℝ) : ∃ rA : ℝ, ¬ GoldschmidtConforms lo hi rA 1 1 := by
  refine ⟨(hi + 1) * (2 * Real.sqrt 2) - 1, ?_⟩
  rw [conforms_iff_radius_window (by norm_num : (0 : ℝ) < 1 + 1)]
  rintro ⟨-, h2⟩
  rw [show rAMax hi 1 1 = hi * (2 * Real.sqrt 2) - 1 by unfold rAMax; ring] at h2
  nlinarith [sqrtTwo_pos]

/-- The model's positive headline row: the ideal A radius conforms to the classic band `[4/5, 1]`,
because it puts the factor at exactly `1`, the band's upper edge (plan §6, §9 family I1). -/
theorem conforms_at_idealA_classic {rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms classicLo classicHi (idealA rB rO) rB rO := by
  rw [conforms_at_idealA_iff h]
  exact ⟨by unfold classicLo; norm_num, by unfold classicHi; norm_num⟩

end Goldschmidt

end PhotoLean
