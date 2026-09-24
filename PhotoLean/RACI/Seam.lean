import Mathlib
import PhotoLean.RACI.TwoState
import PhotoLean.RACI.Branching

namespace PhotoLean


/-!
# RACI M1* — the global CI seam as a codimension-2 submanifold (the inverse-function-theorem layer)

Upstream provenance: the ChemLean RACI plan §11 (M1* preview) and §4.5 risk fallback (integration record: theories/RACI/plan.md §3.1).
Status: added after M1–M4. It upgrades the linear-layer result of M1.3 to a local geometric statement:
near a non-degenerate conical intersection, `conicalSet` corresponds, through a local homeomorphism, to the `ker F × {0}` slice
(mathlib's implicit function theorem `ImplicitFunctionData`) — locally a codimension-2 submanifold.

Contents:
1. `TwoState.degeneracyMap`: the degeneracy-condition map (definitionally equal to the fderiv definition of `Branching.F`).
2. `degeneracyMap_hasStrictFDerivAt_of_contDiffAt`: `H` of class C¹ at `x` ⇒ `G` is strictly differentiable at `x` with derivative `F`.
3. `conicalSet_locally_slice`: the main theorem (local rectification).
4. `conicalSet_local_codim_two`: combined with `finrank_branching_eq_two` of M1.3, this gives codimension 2.

Upstream owner: prover_m1 (M1* belongs to the M1 line).
-/

open Module

namespace TwoState

/-- The degeneracy-condition map `G(y) = (a(y) - d(y), b(y))` (definitionally equal to the fderiv definition of `Branching.F`). -/
def degeneracyMap {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (M : TwoState X) (y : X) : ℝ × ℝ :=
  (a M y - d M y, b M y)

end TwoState

namespace RACI

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

open TwoState

/-- M1*.1: the three independent matrix entries of class C¹ at `x` ⇒ the degeneracy map `G` is
    strictly differentiable at `x` with derivative `F` (the fderiv link of upstream §4.5; matrices
    themselves carry no canonical norm instance in mathlib, so the premise is taken on the entry
    tuple). -/
theorem degeneracyMap_hasStrictFDerivAt_of_contDiffAt
    (M : TwoState X) {x : X}
    (hH : ContDiffAt ℝ 1 (fun y : X => (M.H y 0 0, M.H y 0 1, M.H y 1 1)) x) :
    HasStrictFDerivAt (TwoState.degeneracyMap M) (F M x) x := by
  let T : X → ℝ × ℝ × ℝ := fun y => (M.H y 0 0, M.H y 0 1, M.H y 1 1)
  let L : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    { toFun := fun t => (t.1 - t.2.2, t.2.1)
      map_add' := by
        intro a b
        ext <;> simp [add_sub_add_comm]
      map_smul' := by
        intro c a
        ext <;> simp [mul_sub]
      cont := by
        fun_prop }
  have hT : HasStrictFDerivAt T (fderiv ℝ T x) x := by
    simpa [T] using hH.hasStrictFDerivAt (by simp : (1 : WithTop ℕ∞) ≤ 1)
  have hL : HasStrictFDerivAt L L (T x) := L.hasStrictFDerivAt
  have hG' : HasStrictFDerivAt (TwoState.degeneracyMap M) (L.comp (fderiv ℝ T x)) x := by
    simpa [TwoState.degeneracyMap, TwoState.a, TwoState.d, TwoState.b, T]
      using hL.comp x hT
  have hF_eq : F M x = L.comp (fderiv ℝ T x) := by
    change fderiv ℝ (TwoState.degeneracyMap M) x = L.comp (fderiv ℝ T x)
    exact (hG'.hasFDerivAt.differentiableAt.hasFDerivAt).unique hG'.hasFDerivAt
  simpa [hF_eq] using hG'

/-- M1*.2 main theorem: near a non-degenerate CI, `conicalSet` is locally homeomorphic to the
    `{0} × ker F` slice of `(ℝ × ℝ) × ker F` (the parametrizing directions of `ker F` are the
    seam; via mathlib's implicit function theorem `ImplicitFunctionData`). -/
theorem conicalSet_locally_slice
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (M : TwoState X) {x : X}
    (hG : HasStrictFDerivAt (TwoState.degeneracyMap M) (F M x) x)
    (hreg : Function.Surjective (F M x)) :
    ∃ Φ : PartialHomeomorph X ((ℝ × ℝ) × (LinearMap.ker (F M x))),
      x ∈ Φ.source ∧
        ∀ y ∈ Φ.source, y ∈ TwoState.conicalSet M ↔ (Φ y).1 = 0 := by
  have hsurj : LinearMap.range (F M x) = ⊤ := (LinearMap.range_eq_top).mpr hreg
  rcases ContinuousLinearMap.exists_right_inverse_of_surjective (F M x) hsurj with ⟨s, hs⟩
  have hsv : ∀ v : ℝ × ℝ, (F M x) (s v) = v := by
    intro v
    have := congrArg (fun (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) => L v) hs
    simpa using this
  let P : X →L[ℝ] X := ContinuousLinearMap.id ℝ X - s.comp (F M x)
  have hPmem : ∀ y, P y ∈ LinearMap.ker (F M x) := by
    intro y
    rw [LinearMap.mem_ker]
    simp only [P, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply]
    rw [ContinuousLinearMap.map_sub, hsv (F M x y), sub_self]
  have hPidem : ∀ y, P (P y) = P y := by
    intro y
    have hF : (F M x) (P y) = 0 := (LinearMap.mem_ker.mp (hPmem y))
    change P y - s ((F M x) (P y)) = P y
    rw [hF, ContinuousLinearMap.map_zero, sub_zero]
  let Pcod : X →L[ℝ] (LinearMap.ker (F M x)) :=
    P.codRestrict (LinearMap.ker (F M x)) hPmem
  have hisCompl : IsCompl (LinearMap.ker (F M x)) (LinearMap.ker Pcod) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro y hyF hyP
      rw [LinearMap.mem_ker] at hyF hyP
      have hyP' : P y = 0 := by
        simpa [Pcod] using (Subtype.ext_iff.mp hyP)
      have hdecomp : y = P y + s ((F M x) y) := by
        simp [P]
      rw [hdecomp, hyP', hyF]
      simp
    · intro y hyF hyP
      intro z hz
      have hz1 : P z ∈ y := hyF (hPmem z)
      have hz2 : s ((F M x) z) ∈ y := by
        apply hyP
        rw [LinearMap.mem_ker]
        refine Subtype.ext ?_
        change P (s ((F M x) z)) = 0
        simp only [P, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply]
        rw [hsv (F M x z), sub_self]
      have hdecomp : z = P z + s ((F M x) z) := by
        simp [P]
      rw [hdecomp]
      exact add_mem hz1 hz2
  have hright_range : LinearMap.range Pcod = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro k
    refine ⟨k, ?_⟩
    ext
    change P k = (k : X)
    have hFk : (F M x) k = 0 := (LinearMap.mem_ker.mp k.property)
    simp [P, hFk]
  let φ : ImplicitFunctionData ℝ X (ℝ × ℝ) (LinearMap.ker (F M x)) :=
    { leftFun := TwoState.degeneracyMap M
      leftDeriv := F M x
      rightFun := fun y => Pcod y
      rightDeriv := Pcod
      pt := x
      left_has_deriv := hG
      right_has_deriv := Pcod.hasStrictFDerivAt
      left_range := hsurj
      right_range := hright_range
      isCompl_ker := hisCompl }
  refine ⟨φ.toPartialHomeomorph, ?_, ?_⟩
  · exact φ.pt_mem_toPartialHomeomorph_source
  · intro y hy
    rw [φ.toPartialHomeomorph_apply]
    simp [φ, TwoState.conicalSet, TwoState.degeneracyMap, sub_eq_zero]

/-- M1*.3 corollary: the seam slice near a non-degenerate CI has codimension 2 (combined with `finrank_branching_eq_two` of M1.3). -/
theorem conicalSet_local_codim_two
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [CompleteSpace X]
    (M : TwoState X) {x : X}
    (hG : HasStrictFDerivAt (TwoState.degeneracyMap M) (F M x) x)
    (hreg : Function.Surjective (F M x)) :
    finrank ℝ (LinearMap.ker (F M x))ᗮ = 2 ∧
      ∃ Φ : PartialHomeomorph X ((ℝ × ℝ) × (LinearMap.ker (F M x))),
        x ∈ Φ.source ∧
          ∀ y ∈ Φ.source, y ∈ TwoState.conicalSet M ↔ (Φ y).1 = 0 := by
  constructor
  · exact finrank_branching_eq_two (F M x) hreg
  · exact conicalSet_locally_slice M hG hreg

end RACI


end PhotoLean