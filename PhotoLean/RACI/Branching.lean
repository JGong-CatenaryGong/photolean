import Mathlib
import PhotoLean.RACI.TwoState

namespace PhotoLean


/-!
# RACI M1 — Branching: the branching space, codimension 2 (linear layer), the linearized splitting

Upstream provenance: the ChemLean RACI plan §4.3, §4.4 (integration record: theories/RACI/plan.md §3.1).
Status note (upstream header, preserved): the statements were transcribed from the upstream plan; two deliberate deviations from the draft:
1. In `finrank_branching_eq_two`, `F` follows the upstream §4.5 risk fallback "state it first as an arbitrary continuous linear map" (the fderiv version is kept too).
2. The upstream §4.4 draft used `eigenRoots` directly on matrices; this file introduces `eigenRootsMat` (the matrix-level counterpart),
   semantically equivalent (`TwoState.eigenRoots` is its special case on `H x`).
Upstream owner: prover_m1 (exclusive file).
-/

open TwoState
open Module

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The fderiv of the degeneracy-condition map `F(x) = (a(x) - d(x), b(x))`. -/
noncomputable def F (M : TwoState X) (x : X) : X →L[ℝ] (ℝ × ℝ) :=
  fderiv ℝ (fun y => (TwoState.a M y - TwoState.d M y, TwoState.b M y)) x

/-- M1.3: the branching space (the orthogonal complement of `ker F`) has dimension 2 (codimension 2
    of the linear layer; upstream plan §4.3). Upstream §4.5 risk fallback: `F` is stated as an
    arbitrary continuous linear map (`F' : Y →L[ℝ] (ℝ × ℝ)`); the orthogonal complement `ᗮ`
    requires `[InnerProductSpace ℝ Y]`, so the norm structure on `Y` is provided through
    `InnerProductSpace`, avoiding the instance diamond with `[NormedSpace ℝ Y]`. The fderiv
    version (the `F` above) is kept; the identification `F = fderiv ...` belongs to the upstream
    Sprint 5. -/
theorem finrank_branching_eq_two
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F' : Y →L[ℝ] (ℝ × ℝ)) (hreg : Function.Surjective F') :
    finrank ℝ (LinearMap.ker F')ᗮ = 2 := by
  let f : Y →ₗ[ℝ] (ℝ × ℝ) := F'.toLinearMap
  change finrank ℝ (LinearMap.ker f)ᗮ = 2
  have hsurj : Function.Surjective f := by
    simpa [f] using hreg
  have hrange : LinearMap.range f = ⊤ := (LinearMap.range_eq_top).mpr hsurj
  have hfin1 : finrank ℝ (LinearMap.range f) = finrank ℝ (ℝ × ℝ) := by
    rw [hrange]
    exact finrank_top ℝ (ℝ × ℝ)
  have hfin2 : finrank ℝ (ℝ × ℝ) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self ℝ]
  have hrn : finrank ℝ (LinearMap.range f) + finrank ℝ (LinearMap.ker f) = finrank ℝ Y :=
    LinearMap.finrank_range_add_finrank_ker f
  have horth : finrank ℝ (LinearMap.ker f) + finrank ℝ (LinearMap.ker f)ᗮ = finrank ℝ Y :=
    Submodule.finrank_add_finrank_orthogonal (LinearMap.ker f)
  have hmain : finrank ℝ (LinearMap.ker f)ᗮ = finrank ℝ (LinearMap.range f) := by omega
  calc
    finrank ℝ (LinearMap.ker f)ᗮ = finrank ℝ (LinearMap.range f) := hmain
    _ = finrank ℝ (ℝ × ℝ) := hfin1
    _ = 2 := hfin2

/-- M1.3 explicit two-dimensional instance: the degeneracy map of the linearized model
    (`t = 1`), `v ↦ (2·v 0, v 1)`. The domain is `EuclideanSpace ℝ (Fin 2)` (≃ ℝ²), whose norm
    structure is uniquely derived from `InnerProductSpace`, avoiding the
    `NormedSpace`/`InnerProductSpace` instance diamond of ℝ×ℝ (upstream §4.3 acceptance). -/
noncomputable def Fex : (EuclideanSpace ℝ (Fin 2)) →L[ℝ] (ℝ × ℝ) where
  toFun := fun v => (2 * v 0, v 1)
  map_add' := by
    intro v w
    ext <;> simp [mul_add, Pi.add_apply]
  map_smul' := by
    intro c v
    ext <;> simp [mul_assoc, mul_left_comm, mul_comm, Pi.smul_apply]
  cont := by fun_prop

/-- M1.3: `Fex` is surjective (the `hreg` of the upstream §4.3 acceptance). -/
theorem Fex_surjective : Function.Surjective Fex := by
  intro q
  refine ⟨![q.1 / 2, q.2], ?_⟩
  ext <;> simp [Fex]
  field_simp

/-- M1.3 explicit instance: codimension 2 of the branching space holds on the two-dimensional Euclidean space (upstream §4.3 acceptance). -/
theorem finrank_branching_eq_two_explicit :
    finrank ℝ (LinearMap.ker Fex)ᗮ = 2 := by
  exact finrank_branching_eq_two Fex Fex_surjective

/-- The linearized two-state matrix: diagonal difference along the g direction, coupling along h (upstream plan §4.4). -/
def linearized (gv hv t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![t * gv, t * hv; t * hv, -(t * gv)]

/-- The matrix-level discriminant eigenvalue pair (the upstream §4.4 draft applied `eigenRoots` to matrices; see header note 2). -/
noncomputable def eigenRootsMat (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ × ℝ :=
  (((M 0 0 + M 1 1) + Real.sqrt ((M 0 0 - M 1 1) ^ 2 + 4 * (M 0 1) ^ 2)) / 2,
   ((M 0 0 + M 1 1) - Real.sqrt ((M 0 0 - M 1 1) ^ 2 + 4 * (M 0 1) ^ 2)) / 2)

/-- M1.4: the discriminant identity of the linearized matrix (a pure polynomial; closed by `ring_nf`; upstream plan §4.4). -/
theorem linearized_discr (gv hv t : ℝ) :
    (linearized gv hv t 0 0 - linearized gv hv t 1 1) ^ 2
      + 4 * (linearized gv hv t 0 1) ^ 2
      = 4 * t ^ 2 * (gv ^ 2 + hv ^ 2) := by
  simp [linearized]
  ring

/-- M1.4: the level splitting along the branching direction (upstream plan §4.4; `sqrt (t^2) = |t|`). -/
theorem linearized_gap (gv hv t : ℝ) :
    let e := eigenRootsMat (linearized gv hv t)
    e.1 - e.2 = 2 * |t| * Real.sqrt (gv ^ 2 + hv ^ 2) := by
  dsimp [eigenRootsMat]
  have hsq : Real.sqrt (4 * t ^ 2 * (gv ^ 2 + hv ^ 2)) =
      2 * |t| * Real.sqrt (gv ^ 2 + hv ^ 2) := by
    rw [show 4 * t ^ 2 * (gv ^ 2 + hv ^ 2) = (2 * t) ^ 2 * (gv ^ 2 + hv ^ 2) by ring]
    rw [Real.sqrt_mul (sq_nonneg (2 * t)) (gv ^ 2 + hv ^ 2)]
    rw [Real.sqrt_sq_eq_abs, abs_mul]
    norm_num
  have hdiscr : (linearized gv hv t 0 0 - linearized gv hv t 1 1) ^ 2
      + 4 * (linearized gv hv t 0 1) ^ 2
      = 4 * t ^ 2 * (gv ^ 2 + hv ^ 2) := linearized_discr gv hv t
  rw [hdiscr, hsq]
  ring

/-- M1.4 corollary: at nonzero `t` and a nonzero splitting direction the gap is positive (the prerequisite of the M6 geometric-phase work; upstream plan §4.4). -/
theorem linearized_gap_pos (gv hv t : ℝ) (ht : t ≠ 0) (hgh : gv ^ 2 + hv ^ 2 ≠ 0) :
    0 < 2 * |t| * Real.sqrt (gv ^ 2 + hv ^ 2) := by
  have ht' : 0 < |t| := abs_pos.mpr ht
  have hX : 0 ≤ gv ^ 2 + hv ^ 2 := add_nonneg (sq_nonneg gv) (sq_nonneg hv)
  have hXpos : 0 < gv ^ 2 + hv ^ 2 := lt_of_le_of_ne hX (Ne.symm hgh)
  have hsqrt : 0 < Real.sqrt (gv ^ 2 + hv ^ 2) := Real.sqrt_pos.mpr hXpos
  exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) ht') hsqrt


end PhotoLean