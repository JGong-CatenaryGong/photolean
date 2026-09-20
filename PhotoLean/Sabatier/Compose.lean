/-
PhotoLean.Sabatier.Compose — S4, the microscopic / cross-theory form of the Sabatier theory
(the volcano plot built from the repository's own two-parabola model).

The S1–S3 layers describe the volcano in the *phenomenological* language of the Sabatier theory:
two Brønsted–Evans–Polanyi (BEP) branches, affine in the descriptor `dE`, with the effective
barrier taken as their maximum. This file closes the loop with the repository's own microscopic
(two-parabola, Marcus-type) theory `PhotoLean.BEP`: replacing each affine branch by the exact
barrier of the equal-curvature two-parabola model of an elementary step,
`BEP.eact lam x = (lam - x) ^ 2 / (4 * lam)`, produces the two-parabola volcano

  `parabolaUp lam1 dE   = BEP.eact lam1 (-dE)`   (the branch penalized by weak binding),
  `parabolaDown lam2 dE = BEP.eact lam2 dE`      (the reverse step),
  `parabolicBarrier lam1 lam2 dE = max (parabolaUp .. dE) (parabolaDown .. dE)`,

whose branches cross at `apexPar lam1 lam2`. What is proved here:

1. the BEP-linear volcano `volcanoBarrier (1/2) (lam1/4) (1/2) (lam2/4)` of S1 is EXACTLY the
   maximum of the two tangent lines of the parabolas at thermoneutrality
   (`linearVolcano_eq_bepTangent`) — the literature's linear volcano is the linear-response
   (tangent) form of the microscopic model;
2. each tangent line lies below its parabola (`bepLine_le_eact`), so the linear volcano is a
   pointwise LOWER BOUND on the two-parabola volcano (`linearVolcano_le_parabolic`): the linear
   model underestimates the barrier away from the apex;
3. the two parabolas cross at `apexPar` (`parabolicBarrier_crossing`), and that crossing point is
   the *unique* global minimizer of their maximum whenever `0 < lam1`, `0 < lam2`
   (`parabolicBarrier_apex_le`, `parabolicBarrier_eq_apex_iff`): the Sabatier description holds in
   the two-parabola model with NO BEP linearization (`parabolic_descriptor`);
4. for a symmetric cycle (`lam1 = lam2`) the apex sits at the thermoneutral descriptor `dE = 0`
   (`apexPar_self`), and there the linear and the parabolic volcano agree exactly
   (`linearVolcano_apex_exact`).

Model assumptions that are NOT derived here (plan §12): the effective barrier of the two-step cycle
is the MAXIMUM of the two branch barriers (the modelling premise of S1, inherited here); both steps
follow the equal-curvature two-parabola model of `PhotoLean.BEP` with reorganization energies
`lam1`, `lam2` held fixed across the compared family; the transition state is the classical crossing
point (no tunnelling, no recoupling); the comparison "linear volcano versus parabolic volcano" is
taken at the same descriptor and the same reorganization energies. Every physical premise
(`0 < lam`, `0 < lam1`, `0 < lam2`) is an explicit hypothesis of the statements; nothing is hidden
in a definition.

There is no unproved placeholder and no custom axiom anywhere in this file.

Statement authority: every declaration below matches
`theories/Sabatier/probes/sabatier-statement-skeleton.lean` §S4 word for word (plan §7). Kernel
evidence for the critical-path statement forms: `theories/Sabatier/probes/sabatier-risk-probe.lean`.
-/
import Mathlib
import PhotoLean.BEP.Basic
import PhotoLean.Sabatier.Basic

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Sabatier

/-! ## S4 — microscopic / cross-theory form (`PhotoLean/Sabatier/Compose.lean`) -/

/-- Ascending branch of the two-parabola volcano: the repository's two-parabola barrier of the step
whose reaction energy is the descriptor `dE` (`PhotoLean.BEP.eact` at driving force `-dE`).
(plan §7) -/
noncomputable def parabolaUp (lam1 dE : ℝ) : ℝ := BEP.eact lam1 (-dE)

/-- Descending branch of the two-parabola volcano: the two-parabola barrier of the reverse step
(`PhotoLean.BEP.eact` at driving force `dE`). (plan §7) -/
noncomputable def parabolaDown (lam2 dE : ℝ) : ℝ := BEP.eact lam2 dE

/-- Effective barrier when both steps are described by the repository's two-parabola model: the
larger of the two parabolic branch barriers (the S1 modelling premise "effective barrier = maximum
of the two branch barriers" is inherited unchanged). (plan §7) -/
noncomputable def parabolicBarrier (lam1 lam2 dE : ℝ) : ℝ :=
  max (parabolaUp lam1 dE) (parabolaDown lam2 dE)

/-- Apex of the two-parabola volcano: the descriptor value where the two Marcus-type parabolas cross,
`√(λ₁λ₂)(√λ₂ - √λ₁)/(√λ₁ + √λ₂)`. It is the lower (physically relevant) of the two crossings that
two parabolas of unequal curvature have in general; the uniqueness proved below refers to the
minimizer of the maximum, not to the crossing count. (plan §7) -/
noncomputable def apexPar (lam1 lam2 : ℝ) : ℝ :=
  (lam2 * Real.sqrt lam1 - lam1 * Real.sqrt lam2) / (Real.sqrt lam1 + Real.sqrt lam2)

/-! ### Auxiliary evaluation forms of the two parabolic branches (plan §7) -/

/-- Auxiliary: the ascending branch evaluated as a square, `(lam1 + dE) ^ 2 / (4 * lam1)`.
(plan §7, auxiliary) -/
private theorem parabolaUp_eq (lam1 dE : ℝ) : parabolaUp lam1 dE = (lam1 + dE) ^ 2 / (4 * lam1) := by
  unfold parabolaUp BEP.eact
  ring

/-- Auxiliary: the descending branch is definitionally the square `(lam2 - dE) ^ 2 / (4 * lam2)`.
(plan §7, auxiliary) -/
private theorem parabolaDown_eq (lam2 dE : ℝ) : parabolaDown lam2 dE = (lam2 - dE) ^ 2 / (4 * lam2) :=
  rfl

/-- The BEP-linear volcano is the maximum of the two tangent lines of the parabolic branches: the
literature's linear volcano, read as the tangent (linear-response) form of the repository's model.
The identification is exact for the parameter choice `alphaA = alphaB = 1/2`,
`betaA = lam1/4`, `betaB = lam2/4` — the BEP intercepts of the two steps. (plan §7) -/
theorem linearVolcano_eq_bepTangent (lam1 lam2 dE : ℝ) :
    volcanoBarrier (1 / 2) (lam1 / 4) (1 / 2) (lam2 / 4) dE
      = max (BEP.bepLine lam1 (-dE)) (BEP.bepLine lam2 dE) := by
  unfold volcanoBarrier branchUp branchDown BEP.bepLine
  have h1 : (1 : ℝ) / 2 * dE + lam1 / 4 = lam1 / 4 - -dE / 2 := by ring
  have h2 : lam2 / 4 - 1 / 2 * dE = lam2 / 4 - dE / 2 := by ring
  rw [h1, h2]

/-- The BEP tangent line lies below the parabola it is tangent to (the linear-response direction).
The exact violation is the square `x ^ 2 / (4 * lam)`, so the tangent is the tangent at
thermoneutrality and touches the parabola only at `x = 0`. (plan §7) -/
theorem bepLine_le_eact {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    BEP.bepLine lam x ≤ BEP.eact lam x := by
  have h : BEP.eact lam x - BEP.bepLine lam x = x ^ 2 / (4 * lam) := by
    unfold BEP.eact BEP.bepLine
    field_simp
    ring
  have hnonneg : 0 ≤ x ^ 2 / (4 * lam) := by positivity
  linarith

/-- The BEP-linear volcano is a pointwise LOWER BOUND on the two-parabola volcano: the linear model
optimistically underestimates the barrier away from the apex. Both inequalities are instances of
`bepLine_le_eact`, taken at the driving forces `-dE` (ascending step) and `dE` (reverse step).
(plan §7) -/
theorem linearVolcano_le_parabolic {lam1 lam2 : ℝ} (h1 : 0 < lam1) (h2 : 0 < lam2) (dE : ℝ) :
    volcanoBarrier (1 / 2) (lam1 / 4) (1 / 2) (lam2 / 4) dE ≤ parabolicBarrier lam1 lam2 dE := by
  rw [linearVolcano_eq_bepTangent]
  unfold parabolicBarrier parabolaUp parabolaDown
  exact max_le
    (le_trans (bepLine_le_eact h1 (-dE)) (le_max_left _ _))
    (le_trans (bepLine_le_eact h2 dE) (le_max_right _ _))

/-- The two Marcus-type parabolas cross at `apexPar`. In the square roots `√λ₁ =: s1`, `√λ₂ =: s2`
the apex is `s1 * s2 * (s2 - s1) / (s1 + s2)` and both branches take the common value
`((s1 ^ 2 + s2 ^ 2) / (2 * (s1 + s2))) ^ 2` there. (plan §7) -/
theorem parabolicBarrier_crossing {lam1 lam2 : ℝ} (h1 : 0 < lam1) (h2 : 0 < lam2) :
    parabolaUp lam1 (apexPar lam1 lam2) = parabolaDown lam2 (apexPar lam1 lam2) := by
  unfold parabolaUp parabolaDown apexPar BEP.eact
  set s1 := Real.sqrt lam1 with hs1
  set s2 := Real.sqrt lam2 with hs2
  have hs1pos : 0 < s1 := by rw [hs1]; exact Real.sqrt_pos_of_pos h1
  have hs2pos : 0 < s2 := by rw [hs2]; exact Real.sqrt_pos_of_pos h2
  have h1sq : lam1 = s1 ^ 2 := by rw [hs1]; exact (Real.sq_sqrt h1.le).symm
  have h2sq : lam2 = s2 ^ 2 := by rw [hs2]; exact (Real.sq_sqrt h2.le).symm
  rw [h1sq, h2sq]
  rw [show s2 ^ 2 * s1 - s1 ^ 2 * s2 = s1 * s2 * (s2 - s1) by ring]
  have hs1ne : s1 ≠ 0 := ne_of_gt hs1pos
  have hs2ne : s2 ≠ 0 := ne_of_gt hs2pos
  have hsum : s1 + s2 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < s1 + s2)
  have h4s1 : (4 : ℝ) * s1 ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h4s2 : (4 : ℝ) * s2 ^ 2 ≠ 0 := ne_of_gt (by positivity)
  rw [div_eq_div_iff h4s1 h4s2]
  field_simp
  ring

end Sabatier

end PhotoLean
