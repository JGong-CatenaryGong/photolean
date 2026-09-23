/-
PhotoLean.RACI.Instances — named admissible and refuting models of the RACI theory
(integration addition, plan §4.7).

The admissible model is the delivered linearized torsion Hamiltonian with its conical point at
`θ = 0`; the free/blocked phase pair at `δ = 1/2` realizes the enhancement theorem at concrete
parameters. The named non-model is a constant diagonal Hamiltonian with no conical point
anywhere — the RACI mechanism has no accessible crossing to block, and its M2/M3 premise chain
is uninstantiable there (registered, with kernel-checked verdicts).
-/
import Mathlib
import PhotoLean.RACI.Torsion
import PhotoLean.RACI.Main
import PhotoLean.RACI.RatModel

namespace PhotoLean

namespace RACI

/-! ### The named admissible model -/

/-- The named admissible RACI model at concrete parameters (`A = β = kr = 1`, `δ = 1/2`): the
free/blocked phase pair realizes the enhancement theorem — the blocked phase's quantum yield
strictly exceeds the free phase's. Verdict: admissible, enhancement holds. -/
theorem admissibleModel_enhancement_holds :
    quantumYield 1 (barrierRate 1 1 (accessGap (Allowed (1 / 2 : ℝ)))) >
      quantumYield 1 (barrierRate 1 1 (accessGap Set.univ)) :=
  torsion_raci_emission_enhancement (A := 1) (β := 1) (δ := 1 / 2) (kr := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The admissible model's conical point: `0` belongs to the delivered torsion model's conical
set (its conical set is exactly `{0}`). -/
theorem admissibleModel_conical_point :
    (0 : ℝ) ∈ TwoState.conicalSet (⟨torsionH, torsionH_symm, torsionH_cont⟩ : TwoState ℝ) := by
  rw [torsionH_conicalSet]
  exact Set.mem_singleton 0

/-! ### The named non-model (refuting instance) -/

/-- The named non-model: a constant diagonal Hamiltonian with `a = 1 ≠ 2 = d` — the conical set
is empty everywhere, so the RACI mechanism has no accessible crossing to block. -/
def nonModelNoCI : TwoState ℝ where
  H := fun _ => !![(1 : ℝ), 0; 0, 2]
  h_symm := by
    intro x
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose]
  h_cont := continuous_const

/-- Verdict (discriminant form): the non-model's discriminant is strictly positive everywhere —
there is no degeneracy to reach. -/
theorem nonModelNoCI_gapped_everywhere (x : ℝ) : 0 < TwoState.discr nonModelNoCI x := by
  unfold TwoState.discr TwoState.a TwoState.d TwoState.b nonModelNoCI
  norm_num

/-- Verdict (set form): the non-model's conical set is empty. -/
theorem nonModelNoCI_conicalSet_empty :
    TwoState.conicalSet nonModelNoCI = ∅ := by
  ext x
  simp [TwoState.conicalSet, TwoState.a, TwoState.d, TwoState.b, nonModelNoCI,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Verdict (existence form): the non-model has no conical point — the RACI premise chain (a
reachable CI to block) is uninstantiable here. This is the registered shape of the mechanism's
failure, not a defect: the theorem is conditional. -/
theorem nonModelNoCI_no_conical_point : ¬ ∃ x : ℝ, x ∈ TwoState.conicalSet nonModelNoCI := by
  rw [nonModelNoCI_conicalSet_empty]
  simp

/-- The ℚ decision layer agrees with the ℝ verdicts: the admissible entry is `conical`, the
non-model entry is `gapped` (no runtime evaluation — kernel decisions on rationals). -/
theorem instance_verdicts_agree :
    Rat.ciZoneQ 0 0 0 = .conical ∧ Rat.ciZoneQ 1 0 2 = .gapped :=
  ⟨Rat.ciZoneQ_conical_entry_verdict, Rat.ciZoneQ_nonModel_gapped_verdict⟩

end RACI

end PhotoLean
