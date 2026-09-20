/-
Kasha milestone — API probe (topic F): feasibility of the exponential-race derivation (plan K4b/K4c).

Scope.  The plan's §1.2 branching probabilities `ic n / decay n` are the embedded-jump-chain
probabilities of two competing exponential clocks.  This probe answers the bounded feasibility
question *with kernel evidence*:  can mathlib v4.17.0 state and prove "two independent exponential
clocks of rates `a`, `b`: the probability that the first fires first is `a / (a + b)`", or must K4b
stay a declared modelling premise?

Findings (details in `proofs/API-NOTES.md` §kasha, prose section (f)):

* the exponential distribution **does** exist: `ProbabilityTheory.expMeasure r` (with
  `isProbabilityMeasureExponential`, `exponentialPDF`, `exponentialCDFReal_eq`), and the tail
  formula is kernel-checked below;
* the two ingredients that *do not* exist under the dispatched names:
  `MeasureTheory.integral_exp_neg_mul_Ioi` and `MeasureTheory.measure_lt` (`unknown identifier`),
  `MeasureTheory.Measure.withDensity_apply` (root name `MeasureTheory.withDensity_apply`), bare
  `IsProbabilityMeasure` (`MeasureTheory.IsProbabilityMeasure`), bare `MeasureTheory.measure_Ioi`
  (the usable one is `StieltjesFunction.measure_Ioi`);
* a full proof of the race is **not** a one-lemma job (product law for the pair, density change of
  measure on `Ioi 0`, `ℝ≥0∞ → ℝ` conversion, a.e. split at `0`); the race statement is therefore
  `#check`ed here as a proposition, not proved, and K4b stays a declared modelling premise.

Plan loci served: §1.2 (the model's branching probabilities), §13 scope limit 5, plan K4b/K4c.

Running:  proofs/scripts/lake env lean theories/kasha/probes/kasha-api-race.lean
Status:   0 errors / 0 warnings.
-/
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

set_option autoImplicit false

namespace PhotoLean.Kasha.ProbeRace

/-! ## `#check` — the candidate infrastructure (what exists in mathlib v4.17.0) -/

#check @ProbabilityTheory.expMeasure
#check @ProbabilityTheory.isProbabilityMeasureExponential
#check @ProbabilityTheory.exponentialPDF
#check @ProbabilityTheory.exponentialPDF_eq
#check @ProbabilityTheory.exponentialPDF_of_nonneg
#check @ProbabilityTheory.lintegral_exponentialPDF_eq_one
#check @ProbabilityTheory.exponentialCDFReal
#check @ProbabilityTheory.exponentialCDFReal_eq
#check @ProbabilityTheory.cdf
#check @ProbabilityTheory.cdf_eq_toReal
#check @ProbabilityTheory.tendsto_cdf_atTop
#check @ProbabilityTheory.measure_cdf
#check @ProbabilityTheory.iIndepFun
#check @ProbabilityTheory.IndepFun
#check @MeasureTheory.Measure.withDensity
#check @MeasureTheory.withDensity_apply
#check @MeasureTheory.lintegral_withDensity_eq_lintegral_mul
#check @MeasureTheory.Measure.restrict
#check @MeasureTheory.IsProbabilityMeasure
#check @MeasureTheory.measure_univ
#check @MeasureTheory.measure_compl
#check @MeasureTheory.lintegral_indicator
#check @MeasureTheory.lintegral_const_mul
#check @MeasureTheory.Measure.map
#check @MeasureTheory.Measure.prod
#check @MeasureTheory.Measure.prod_apply
#check @MeasureTheory.Measure.prod_apply_symm
#check @MeasureTheory.lintegral_prod
#check @MeasureTheory.lintegral_lintegral_swap
#check @MeasureTheory.ofReal_integral_eq_lintegral_ofReal
#check @MeasureTheory.integral_eq_lintegral_of_nonneg_ae
#check @MeasureTheory.integral_comp_mul_left_Ioi
#check @exp_neg_integrableOn_Ioi
#check @integral_exp_neg_Ioi
#check @integral_exp_neg_Ioi_zero
#check @StieltjesFunction.measure_Ioi
#check @ENNReal.ofReal
#check @ENNReal.toReal_ofReal
#check @ENNReal.ofReal_le_ofReal_iff

-- NOT in mathlib v4.17.0 (verbatim errors quoted in `proofs/API-NOTES.md` §kasha):
--   `MeasureTheory.integral_exp_neg_mul_Ioi`, `MeasureTheory.measure_lt`,
--   `MeasureTheory.measure_Ioi`, `MeasureTheory.Measure.withDensity_apply`, bare
--   `IsProbabilityMeasure`, `Real.integral_exp_neg_Ioi` — all `unknown identifier`/`unknown
--   constant`.  Replacements are in the `#check` block above.

/-! ## Kernel-checked step 1 — the exponential law is the density `a·exp(-a·x)` on `[0,∞)` -/

/-- `expMeasure r` is `volume.withDensity (exponentialPDF r)` by `rfl` (both are
`gammaMeasure 1 r = volume.withDensity (gammaPDF 1 r)` with `gammaPDF 1 r = exponentialPDF r`). -/
theorem expMeasure_eq_withDensity (r : ℝ) :
    ProbabilityTheory.expMeasure r = volume.withDensity (ProbabilityTheory.exponentialPDF r) := rfl

theorem hasDensity (r : ℝ) : ProbabilityTheory.exponentialPDF r
    = fun x => ENNReal.ofReal (if 0 ≤ x then r * Real.exp (-(r * x)) else 0) :=
  funext fun x => ProbabilityTheory.exponentialPDF_eq r x

theorem isProbabilityMeasure_expMeasure {r : ℝ} (hr : 0 < r) :
    MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
  ProbabilityTheory.isProbabilityMeasureExponential hr

theorem lintegral_exponentialPDF_eq_one {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ProbabilityTheory.exponentialPDF r x = 1 :=
  ProbabilityTheory.lintegral_exponentialPDF_eq_one hr

/-! ## Kernel-checked step 2 — the survival function `P(T_r > x) = exp (-(r x))` -/

/-- The tail of the exponential law, the quantity the race integrand is built from.
Route: `StieltjesFunction.measure_Ioi` applied to `cdf (expMeasure r)` (`tendsto_cdf_atTop` gives
the limit `1`) + `ProbabilityTheory.measure_cdf` + `exponentialCDFReal_eq`. -/
theorem expMeasure_Ioi {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    ProbabilityTheory.expMeasure r (Set.Ioi x) = ENNReal.ofReal (Real.exp (-(r * x))) := by
  haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
    ProbabilityTheory.isProbabilityMeasureExponential hr
  have h1 : ProbabilityTheory.expMeasure r (Set.Ioi x)
      = ENNReal.ofReal (1 - (ProbabilityTheory.exponentialCDFReal r) x) := by
    have h := StieltjesFunction.measure_Ioi (ProbabilityTheory.exponentialCDFReal r)
      (ProbabilityTheory.tendsto_cdf_atTop (ProbabilityTheory.expMeasure r)) x
    unfold ProbabilityTheory.exponentialCDFReal at h
    rwa [ProbabilityTheory.measure_cdf] at h
  rw [h1, ProbabilityTheory.exponentialCDFReal_eq hr x, if_pos hx]
  congr 1
  ring

/-! ## Kernel-checked step 3 — the Laplace integral `∫_{0}^{∞} exp (-(c x)) dx = 1/c` -/

/-- The integral of the survival function against a rate: the substitution is
`MeasureTheory.integral_comp_mul_left_Ioi` (`∫ x in Ioi a, g (b·x) = b⁻¹ • ∫ x in Ioi (b·a), g x`),
the base case is `integral_exp_neg_Ioi_zero` (root namespace, *not* `Real.…`). -/
theorem integral_exp_neg_mul_Ioi_zero {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ in Set.Ioi 0, Real.exp (-(c * x))) = 1 / c := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi (fun y : ℝ => Real.exp (-y)) (0 : ℝ) hc
  simp only [mul_zero] at h
  rw [h, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one, one_div]

/-! ## The race statement itself — stated (kernel-elaborated), NOT proved -/

/- The two-clock race as a proposition (type-checked by `#check`, no proof attempted): the product
of two exponential laws on `ℝ × ℝ` gives the lower coordinate the mass `a / (a + b)`.
A proof needs the three kernel-checked steps above **plus** four things mathlib does not hand over:
(i) an identification of `(expMeasure a).prod (expMeasure b)` with two independent clocks
(`iIndepFun` is a statement about a single probability space `Ω`, not about `Measure.prod`), (ii) the
density change of measure applied *inside* the restriction to `Ioi 0` (indicator/`restrict`
bookkeeping), (iii) `ofReal_integral_eq_lintegral_ofReal`'s side conditions (`Integrable`,
`0 ≤ᵐ`), and (iv) the a.e. split of `s ↦ expMeasure b (Ioi s)` at `s = 0` (where the tail is `1`,
not `exp (-(b s))`).  Order of magnitude: a dedicated sprint, not a probe. -/
#check (fun (a b : ℝ) (_ : 0 < a) (_ : 0 < b) =>
  ((ProbabilityTheory.expMeasure a).prod (ProbabilityTheory.expMeasure b))
      {p : ℝ × ℝ | p.1 < p.2} = ENNReal.ofReal (a / (a + b)))

end PhotoLean.Kasha.ProbeRace
