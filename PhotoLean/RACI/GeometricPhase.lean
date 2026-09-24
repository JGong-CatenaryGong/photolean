import Mathlib
import PhotoLean.RACI.Branching

namespace PhotoLean


/-!
# RACI M6 — the Longuet–Higgins sign theorem and the geometric phase (first version: the canonical loop)

Upstream provenance: the ChemLean RACI plan §11 (M6 preview, depending on the M1.4 linearized splitting; integration record: theories/RACI/plan.md §3.1).
Status: added after M1–M4 and M1*.
Contents: for the linearized model (M1.4) along the unit-circle loop `H(t) = [[cos t, sin t], [sin t, −cos t]]`:
1. `loopLowerVec`, `v(t) = (sin(t/2), −cos(t/2))`, is an eigenvector of `H(t)` (eigenvalue −1) and a unit vector;
2. after one circuit around the CI (`t ↦ t + 2π`) the eigenvector changes sign — the Longuet–Higgins sign theorem (monodromy = −1);
3. the gap on the loop is constantly 2 (from `linearized_gap` of M1.4), so adiabatic transport is well defined everywhere.

Upstream owner: prover_m1 (M6 belongs to the M1.4 line).
-/

namespace RACI

/-- The linearized Hamiltonian on the canonical loop: `H(t) = [[cos t, sin t], [sin t, −cos t]]` (M6). -/
noncomputable def loopH (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  linearized (Real.cos t) (Real.sin t) 1

/-- The lower eigenvector `v(t) = (sin(t/2), −cos(t/2))` (M6). -/
noncomputable def loopLowerVec (t : ℝ) : Fin 2 → ℝ :=
  ![Real.sin (t / 2), -Real.cos (t / 2)]

/-- M6.1: `v(t)` is an eigenvector of `H(t)` with eigenvalue −1. -/
theorem loopLowerVec_eigen (t : ℝ) :
    (loopH t).mulVec (loopLowerVec t) = (-1 : ℝ) • loopLowerVec t := by
  ext i
  fin_cases i
  · simp [loopH, loopLowerVec, linearized, Matrix.mulVec]
    have h : Real.sin (t / 2) = Real.sin t * Real.cos (t / 2) - Real.cos t * Real.sin (t / 2) := by
      have h1 := Real.sin_sub t (t / 2)
      rw [show t - t / 2 = t / 2 by ring] at h1
      exact h1
    linarith
  · simp [loopH, loopLowerVec, linearized, Matrix.mulVec]
    have h : Real.cos (t / 2) = Real.cos t * Real.cos (t / 2) + Real.sin t * Real.sin (t / 2) := by
      have h1 := Real.cos_sub t (t / 2)
      rw [show t - t / 2 = t / 2 by ring] at h1
      exact h1
    linarith

/-- M6.2: `v(t)` is a unit vector (the squared entries sum to 1). -/
theorem loopLowerVec_sq_sum (t : ℝ) :
    loopLowerVec t 0 ^ 2 + loopLowerVec t 1 ^ 2 = 1 := by
  simp [loopLowerVec]

/-- M6.3: after one circuit around the CI the eigenvector changes sign (the Longuet–Higgins sign theorem: monodromy = −1). -/
theorem loop_monodromy (t : ℝ) :
    loopLowerVec (t + 2 * Real.pi) = -loopLowerVec t := by
  ext i
  fin_cases i
  · simp [loopLowerVec]
    rw [show (t + 2 * Real.pi) / 2 = t / 2 + Real.pi by ring]
    exact Real.sin_add_pi (t / 2)
  · simp [loopLowerVec]
    rw [show (t + 2 * Real.pi) / 2 = t / 2 + Real.pi by ring]
    rw [Real.cos_add_pi (t / 2)]
    simp

/-- M6.4: the gap on the loop is constantly 2 (an instantiation of `linearized_gap` of M1.4; adiabatic transport is well defined). -/
theorem loop_gap (t : ℝ) :
    let e := eigenRootsMat (loopH t)
    e.1 - e.2 = 2 := by
  change (eigenRootsMat (loopH t)).1 - (eigenRootsMat (loopH t)).2 = 2
  have hgap := linearized_gap (Real.cos t) (Real.sin t) 1
  simpa [loopH] using hgap

end RACI


end PhotoLean