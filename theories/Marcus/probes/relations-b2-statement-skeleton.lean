/-
relations-b2-statement-skeleton — statement calibration probe for the second batch of
cross-theory relations (`PhotoLean/Relations.lean` §9, Sabatier ↔ Marcus).

This file is NOT delivered source: it lives under `theories/Marcus/probes/`, outside
`SOURCE_DIRS`, and carries placeholder proofs on purpose — exactly as the per-theory
statement authorities do. Its only job is to pin the *statements* of the new relations
before any proof work (statement-first). Candidates that turn out to be infeasible are
demoted to prose in `theories/RELATIONS.md` rather than restated to fit a proof.

Run with:
    proofs/scripts/lake env lean theories/Marcus/probes/relations-b2-statement-skeleton.lean

The subject is the "look-alike but different" pair: the Sabatier volcano predicate
(`Sabatier.AntiVolcanoDescriptor`, the activity peak of the volcano plot) and the Marcus
rate of the two-parabola model. Both have a unique interior optimum; the candidates below
are (C1) the shared functional form, (C2) the same predicate instantiated at the Marcus
rate, and (C3–C5) three checkable facets on which the two optima come apart.
-/
import PhotoLean.Kernel
import PhotoLean.Marcus.Rate
import PhotoLean.Sabatier.Criterion
import PhotoLean.Kasha.Compose

namespace PhotoLean

namespace Relations

/-! ## API calibration (contract rule 4: never guess a mathlib name) -/

#check @Real.exp_injective
#check @Real.exp_eq_exp
#check @mul_left_cancel₀
#check @div_mul_cancel₀
#check @sq_eq_zero_iff
#check @pow_eq_zero

/-! ## C1 — the shared functional form (certificate) -/

/-- C1: the Marcus rate is the Sabatier activity functional applied to the kernel barrier,
scaled by the pre-exponential factor `A`. This is what turns "same shape" from an analogy
into a shared definition pattern: both theories' observable is `A' * exp (-Ea / (kB*T))`
on the same kernel barrier. -/
theorem marcus_rate_eq_activity (A lam kB T x : ℝ) :
    Marcus.rate A lam kB T x =
      A * Sabatier.activity (fun y => Kernel.barrier lam y) kB T x := by
  sorry

/-! ## C2 — the same predicate, instantiated at the Marcus rate -/

/-- C2: the Marcus rate takes the *Sabatier* volcano shape in the very same predicate
`Sabatier.AntiVolcanoDescriptor`: `lam` is its unique global maximizer. -/
theorem marcusRate_antiVolcanoDescriptor {A lam kB T : ℝ}
    (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T) :
    Sabatier.AntiVolcanoDescriptor (Marcus.rate A lam kB T) lam := by
  sorry

/-! ## C3 — non-relation 1: the barrier height at the optimum -/

/-- C3a: the reference volcano's optimal pass height is nonzero (`1/2`). -/
theorem apexBarrier_reference_nonzero :
    Sabatier.apexBarrier (1 / 2) (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  sorry

/-- C3b: the contrast, side by side — the Marcus optimal barrier is identically zero
(the optimum is a barrierless point) while the Sabatier reference pass is nonzero. -/
theorem optimal_barrier_height_contrast :
    (∀ lam : ℝ, Kernel.barrier lam lam = 0) ∧
      Sabatier.apexBarrier (1 / 2) (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  sorry

/-! ## C4 — non-relation 2: the one-sided secant at the optimum (no calculus) -/

/-- C4: at the Marcus optimum the one-sided secant of the barrier vanishes with the step
(it is exactly `h / (4 * lam)`), whereas the Sabatier volcano legs have secant slopes that
do not depend on the step at all (`Sabatier.volcanoBarrier_secSlope_of_apex_le` gives
`alphaA`, `..._of_le_apex` gives `-alphaB`). -/
theorem marcus_secant_at_optimum {lam h : ℝ} (hlam : lam ≠ 0) (hh : h ≠ 0) :
    (Kernel.barrier lam (lam + h) - Kernel.barrier lam lam) / h = h / (4 * lam) := by
  sorry

/-! ## C5 — non-relation 3: the parameter dependence of the optimal position -/

/-- C5a: the Sabatier apex moves when only the offsets change, the two slopes being held
fixed: `apex (1/2) 0 (1/2) 1 = 1` while `apex (1/2) 0 (1/2) 0 = 0`. -/
theorem sabatier_apex_moves_with_offsets :
    Sabatier.apex (1 / 2) 0 (1 / 2) 1 = 1 ∧ Sabatier.apex (1 / 2) 0 (1 / 2) 0 = 0 := by
  sorry

/-- C5b: the Marcus optimal position is fixed by the curvature alone — the same descriptor
`lam` is optimal for every admissible pre-exponential factor and thermal energy. -/
theorem marcus_optimum_fixed_by_curvature {lam : ℝ} (hlam : 0 < lam) :
    ∀ (A kB T : ℝ), 0 < A → 0 < kB * T →
      Sabatier.AntiVolcanoDescriptor (Marcus.rate A lam kB T) lam := by
  sorry

end Relations

end PhotoLean
