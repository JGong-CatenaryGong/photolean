/-
Sabatier API calibration — probe (d)+(e): `Real.exp` / `Real.log` and `Real.sqrt`.

Owner: api_researcher. Evidence behind the `## Sabatier theory (2026-09-21)` section of
`proofs/API-NOTES.md`. Run from the repository root with

  proofs/scripts/lake env lean theories/Sabatier/probes/sabatier-api-explog-sqrt.lean

Highest-risk item for the volcano layer: turning the *dimensionless* exponential comparison
`Real.exp (-(a) / (kB * T)) ≤ Real.exp (-(b) / (kB * T))` (with `0 < kB`, `0 < T`) into the
*energy* statement `b ≤ a`. The three-line recipe is in §2 below and is kernel-checked; the
`rate`-shaped version in §3 uses the delivered `PhotoLean.Marcus.rate` / `barrier`.
-/
import Mathlib
import PhotoLean.Marcus.Basic

namespace PhotoLean
namespace Sabatier
namespace ApiProbeExpLogSqrt

/-! ## 1. `Real.exp` / `Real.log` — confirmed signatures -/

#check @Real.exp_pos
#check @Real.exp_ne_zero
#check @Real.exp_nonneg
#check @Real.exp_le_exp
#check @Real.exp_lt_exp
#check @Real.exp_monotone
#check @Real.exp_strictMono
#check @Real.exp_injective
#check Real.exp_zero
#check @Real.exp_le_one_iff
#check @Real.exp_lt_one_iff
#check @Real.one_lt_exp_iff
#check @Real.exp_add
#check @Real.exp_sub
#check @Real.exp_neg
#check Real.log_exp
#check @Real.exp_log
#check @Real.log_le_log
#check @Real.log_lt_log
#check @Real.log_le_log_iff
#check @Real.log_lt_log_iff
#check @Real.log_pos
#check @Real.log_nonneg
#check @Real.log_nonpos
#check @Real.log_le_sub_one_of_pos
#check @Real.log_le_iff_le_exp
#check @Real.le_log_iff_exp_le
#check @Real.log_injOn_pos

/-! ## 2. The key recipe: exp-monotonicity with positive `kB * T`

`Real.exp_le_exp` **is already the `iff`** on `ℝ` (`Real.exp x ≤ Real.exp y ↔ x ≤ y`). The whole
content is therefore: drop `exp`, cancel the *positive* denominator with
`div_le_div_iff_of_pos_right`, and flip the negations with `neg_le_neg_iff`. -/

/-- The recipe in its cleanest form: one `k > 0` (the physically combined `kB * T`), no
hypotheses on the signs of `a`, `b`. This is the form the Sabatier layer should state. -/
theorem exp_neg_div_le_iff_of_pos {a b k : ℝ} (hk : 0 < k) :
    Real.exp (-a / k) ≤ Real.exp (-b / k) ↔ b ≤ a := by
  rw [Real.exp_le_exp, div_le_div_iff_of_pos_right hk, neg_le_neg_iff]

/-- The same recipe with the two physical premises kept separate, i.e. exactly the hypothesis
shape of the plan (`0 < kB`, `0 < T`). The only extra step is `mul_pos`. -/
theorem exp_neg_div_le_iff {a b kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) :
    Real.exp (-a / (kB * T)) ≤ Real.exp (-b / (kB * T)) ↔ b ≤ a :=
  exp_neg_div_le_iff_of_pos (mul_pos hkB hT)

/-- The forward half, for a `have`/`exact` site: from the energy comparison to the exponential
comparison (this is the direction a monotone-descriptor proof needs). -/
theorem exp_neg_div_mono {a b kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (h : b ≤ a) :
    Real.exp (-a / (kB * T)) ≤ Real.exp (-b / (kB * T)) := by
  rw [Real.exp_le_exp, div_le_div_iff_of_pos_right (mul_pos hkB hT)]
  linarith

/-- The backward half as a standalone implication, for the sharpness/necessity direction. -/
theorem le_of_exp_neg_div_le {a b kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T)
    (h : Real.exp (-a / (kB * T)) ≤ Real.exp (-b / (kB * T))) : b ≤ a :=
  (exp_neg_div_le_iff hkB hT).mp h

/-- Recipe: the same comparison once `kB * T` has already been combined into a hypothesis — the
house style of `PhotoLean.Marcus.Rate` (`hkT : 0 < kB * T`). -/
example {a b kB T : ℝ} (hkT : 0 < kB * T)
    (h : Real.exp (-a / (kB * T)) ≤ Real.exp (-b / (kB * T))) : b ≤ a := by
  rw [Real.exp_le_exp, div_le_div_iff_of_pos_right hkT, neg_le_neg_iff] at h
  exact h

/-- Recipe: **the `linarith` route** (no `neg_le_neg_iff`): after cancelling the denominator the
goal is a linear inequality in the two negated atoms, which `linarith` closes. Kept because it
also survives when the two sides are not syntactically `-(·)/k`. -/
example {a b k : ℝ} (hk : 0 < k) (h : Real.exp (-a / k) ≤ Real.exp (-b / k)) : b ≤ a := by
  rw [Real.exp_le_exp] at h
  rw [div_le_div_iff_of_pos_right hk] at h
  linarith

/-- Recipe: `Real.exp_monotone` / `Real.exp_strictMono` as `Monotone`/`StrictMono` objects, for
the `StrictMonoOn` toolkit of probe (b). -/
example : StrictMono Real.exp := Real.exp_strictMono

/-- Recipe: injectivity of `Real.exp`, the alternative to `Real.exp_le_exp.mp` when only an
equality of exponentials is known. -/
example {x y : ℝ} (h : Real.exp x = Real.exp y) : x = y := Real.exp_injective h

/-! ## 3. The `rate`-shaped version (delivered `PhotoLean.Marcus` vocabulary)

`PhotoLean.Marcus.rate A lam kB T x = A * Real.exp (-(barrier lam x) / (kB * T))`. The delivered
`PhotoLean.Marcus.Rate.rate_gt_of_barrier_lt` covers `barrier <` ⟹ `rate >`. The volcano layer
needs the *reverse* reading (a rate comparison ⟹ a barrier comparison), which is what the two
theorems below add. -/

/-- From a rate comparison to a barrier comparison, in the direction the volcano needs: the
exponential is strictly increasing, the prefactor `A > 0` can be cancelled, and the denominator
`kB * T > 0` is positive. -/
theorem barrier_le_of_rate_le {A lam kB T x₁ x₂ : ℝ} (hA : 0 < A) (hkB : 0 < kB) (hT : 0 < T)
    (h : Marcus.rate A lam kB T x₁ ≤ Marcus.rate A lam kB T x₂) :
    Marcus.barrier lam x₂ ≤ Marcus.barrier lam x₁ := by
  have hkT : 0 < kB * T := mul_pos hkB hT
  unfold Marcus.rate at h
  rw [mul_le_mul_left hA, Real.exp_le_exp, div_le_div_iff_of_pos_right hkT, neg_le_neg_iff] at h
  exact h

/-- The strict twin. -/
theorem barrier_lt_of_rate_lt {A lam kB T x₁ x₂ : ℝ} (hA : 0 < A) (hkB : 0 < kB) (hT : 0 < T)
    (h : Marcus.rate A lam kB T x₁ < Marcus.rate A lam kB T x₂) :
    Marcus.barrier lam x₂ < Marcus.barrier lam x₁ := by
  have hkT : 0 < kB * T := mul_pos hkB hT
  unfold Marcus.rate at h
  rw [mul_lt_mul_left hA, Real.exp_lt_exp, div_lt_div_iff_of_pos_right hkT, neg_lt_neg_iff] at h
  exact h

/-! ## 4. `Real.log` — the recipe that pairs with the exponential layer

Needed when a criterion is stated as a threshold in the barrier: the exponential comparison is
turned into a *linear* one via `Real.log_le_iff_le_exp` / `Real.le_log_iff_exp_le` (the
directions are opposite — see the trap note in `proofs/API-NOTES.md`). -/

/-- Recipe: divide by the positive prefactor `A`, then take `log`. Note the direction of
`Real.log_le_iff_le_exp` (`0 < x → (Real.log x ≤ y ↔ x ≤ Real.exp y)`): here it rewrites the
`Real.log`-side into the `exp`-side, which is what closes the `↔`. -/
theorem log_threshold {c A b k : ℝ} (hA : 0 < A) (hc : 0 < c) :
    c ≤ A * Real.exp (-b / k) ↔ Real.log (c / A) ≤ -b / k := by
  rw [Real.log_le_iff_le_exp (div_pos hc hA), mul_comm A, ← div_le_iff₀ hA]

/-- Recipe: clearing the `k > 0` denominator at the end (`le_div_iff₀`), so the criterion comes
out in energy units — this is the shape a volcano threshold row lands in. -/
theorem log_threshold_energy {c A k b : ℝ} (hA : 0 < A) (hk : 0 < k) (hc : 0 < c) :
    c ≤ A * Real.exp (-b / k) ↔ Real.log (c / A) * k ≤ -b := by
  rw [← le_div_iff₀ hk, mul_comm A, ← div_le_iff₀ hA, Real.log_le_iff_le_exp (div_pos hc hA)]

/-! ## 5. `Real.sqrt` — confirmed signatures (the "parabola volcano" apex)

The exact hypotheses matter here (they are *not* symmetric between the four order lemmas), so
they are quoted verbatim below. -/

#check @Real.sq_sqrt
#check @Real.sqrt_sq_eq_abs
#check @Real.sqrt_mul_self
#check @Real.sqrt_mul
#check @Real.sqrt_div
#check @Real.sqrt_pos
#check @Real.sqrt_pos_of_pos
#check @Real.sqrt_nonneg
#check @Real.sqrt_lt_sqrt
#check @Real.sqrt_lt_sqrt_iff
#check @Real.sqrt_le_sqrt
#check @Real.sqrt_le_sqrt_iff
#check @Real.sqrt_inj
#check @Real.sqrt_eq_zero_of_nonpos

/-- Recipe: the apex position `√lam` is positive as soon as `lam` is. -/
example {lam : ℝ} (hlam : 0 < lam) : 0 < Real.sqrt lam := Real.sqrt_pos_of_pos hlam

/-- Recipe: eliminating the root at an apex `x = √lam` (the `"parabola volcano"` step). -/
example {lam x : ℝ} (hlam : 0 ≤ lam) (h : x = Real.sqrt lam) : x ^ 2 = lam := by
  rw [h, Real.sq_sqrt hlam]

/-- Recipe: the same without the `have`, at a `√`-valued apex. -/
example {lam : ℝ} (hlam : 0 ≤ lam) : (Real.sqrt lam) ^ 2 = lam := Real.sq_sqrt hlam

/-- Recipe: `√` is strictly monotone on the nonnegative half-line; note the hypothesis is on the
**left** argument (`Real.sqrt_lt_sqrt (hx : 0 ≤ x) (h : x < y)`). -/
example {lam₁ lam₂ : ℝ} (h₁ : 0 ≤ lam₁) (h : lam₁ < lam₂) :
    Real.sqrt lam₁ < Real.sqrt lam₂ := Real.sqrt_lt_sqrt h₁ h

/-- Recipe: **the hypothesis trap.** `Real.sqrt_le_sqrt_iff` carries `0 ≤ y` (the *right*
argument) while `Real.sqrt_lt_sqrt_iff` carries `0 ≤ x` (the *left* argument). Both are quoted
verbatim in §5 above; a caller that passes the wrong one gets a unification failure, not a
silently wrong statement. -/
example {x y : ℝ} (hy : 0 ≤ y) : Real.sqrt x ≤ Real.sqrt y ↔ x ≤ y := Real.sqrt_le_sqrt_iff hy

/-- Recipe: the `√`-window that a volcano apex comparison produces, in the `nth_rewrite` form
recorded in `proofs/API-NOTES.md` §kasha §4.4 (`rw` alone rewrites too deep into `√R`). -/
example {R x : ℝ} (hR : 0 ≤ R) : x ^ 2 ≤ R ↔ |x| ≤ Real.sqrt R := by
  nth_rewrite 1 [← Real.sq_sqrt hR]
  rw [sq_le_sq, abs_of_nonneg (Real.sqrt_nonneg R)]

/-- Recipe: the same window with `calc`-free steps (no `nth_rewrite`), for when the goal's
left-hand side also mentions `√`. -/
example {R x : ℝ} (hR : 0 ≤ R) : |x| ≤ Real.sqrt R ↔ x ^ 2 ≤ R := by
  constructor
  · intro h
    have h' : (|x|) ^ 2 ≤ (Real.sqrt R) ^ 2 := by
      rw [sq_le_sq, abs_abs, abs_of_nonneg (Real.sqrt_nonneg R)]
      exact h
    rwa [sq_abs, Real.sq_sqrt hR] at h'
  · intro h
    have h' : (|x|) ^ 2 ≤ (Real.sqrt R) ^ 2 := by rwa [sq_abs, Real.sq_sqrt hR]
    rwa [sq_le_sq, abs_abs, abs_of_nonneg (Real.sqrt_nonneg R)] at h'

/-- Recipe: `√` of a product, when only one factor is known nonnegative
(`Real.sqrt_mul (hx : 0 ≤ x) (y : ℝ)`). -/
example {x y : ℝ} (hx : 0 ≤ x) : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y :=
  Real.sqrt_mul hx y

/-- Recipe: `√` of a quotient with the numerator's sign hypothesis. -/
example {x y : ℝ} (hx : 0 ≤ x) : Real.sqrt (x / y) = Real.sqrt x / Real.sqrt y :=
  Real.sqrt_div hx y

/-- Recipe: injectivity of `√` on the nonnegative half-line (both hypotheses required). -/
example {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : Real.sqrt x = Real.sqrt y ↔ x = y :=
  Real.sqrt_inj hx hy

/-- Recipe: the degenerate collapse `√x = 0` for `x ≤ 0` (the non-physical-branch tool, parallel
to `Marcus.barrier_zero_lam` in the sharpness arguments). -/
example {x : ℝ} (hx : x ≤ 0) : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos hx

/-- Recipe: `√(x²) = |x|`, the bridge from a square back to an absolute value. -/
example (x : ℝ) : Real.sqrt (x ^ 2) = |x| := Real.sqrt_sq_eq_abs x

/-- Recipe: `√` is nonnegative everywhere (no hypothesis), which is what discharges the
sign side condition of `sq_le_sq`-style steps. -/
example (x : ℝ) : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x

/-- Recipe: `Real.sqrt_pos` is already an `iff`. -/
example {x : ℝ} : 0 < Real.sqrt x ↔ 0 < x := Real.sqrt_pos

/-- Recipe: `√(x * x) = x` on the nonnegative half-line. -/
example {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (x * x) = x := Real.sqrt_mul_self hx

/-!
## 6. `NOT FOUND` in mathlib v4.17.0 (measured with this same probe; kept as comments so the
delivered file stays at 0 error — the verbatim lines are quoted in `proofs/API-NOTES.md`)

```
error: unknown constant 'Real.exp_le_exp_iff'      -- `Real.exp_le_exp` *is* the iff on ℝ
error: unknown constant 'Real.exp_lt_exp_iff'      -- `Real.exp_lt_exp` *is* the iff on ℝ
error: unknown identifier 'strictMonoOn_const'     -- use `monotoneOn_const` (strict is false)
error: unknown identifier 'strictMonoOn_iff_forall_lt'
error: unknown identifier 'abs_le_iff'             -- use `abs_le` (or the primitive `abs_le'`)
error: unknown identifier 'map_max'                -- use `Rat.cast_max`, or `max_def`+case split
```
-/

end ApiProbeExpLogSqrt
end Sabatier
end PhotoLean
