import Mathlib

namespace PhotoLean


/-!
# RACI M1 — TwoState: the CI algebra of the 2×2 real symmetric Hamiltonian

Upstream provenance: the ChemLean RACI plan §2.2, §4.1, §4.2 (integration record: theories/RACI/plan.md §3.1).
Status: **DONE** — the four M1.1/M1.2 theorems are proved (upstream Sprint 2): no placeholder proof, no custom axiom.
Upstream owner: prover_m1 (exclusive file).
Discipline: the delivered theorems of this file carry no placeholder proof and no custom `axiom`;
API names are never guessed — they are calibrated by api_researcher (recorded in the upstream proofs/API-NOTES.md).
-/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Two-state adiabatic Hamiltonian (a 2×2 real symmetric matrix family over the nuclear configuration space `X`). -/
structure TwoState (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  H : X → Matrix (Fin 2) (Fin 2) ℝ
  h_symm : ∀ x, Matrix.IsSymm (H x)
  h_cont : Continuous H

namespace TwoState

/-- Matrix-entry notation: `a = H00`, `b = H01`, `d = H11`. -/
def a (M : TwoState X) (x : X) : ℝ := M.H x 0 0

/-- Matrix-entry notation: `b = H01` (the coupling). -/
def b (M : TwoState X) (x : X) : ℝ := M.H x 0 1

/-- Matrix-entry notation: `d = H11`. -/
def d (M : TwoState X) (x : X) : ℝ := M.H x 1 1

/-- The degeneracy discriminant: `(a - d) ^ 2 + 4 * b ^ 2`. -/
def discr (M : TwoState X) (x : X) : ℝ :=
  (a M x - d M x) ^ 2 + 4 * (b M x) ^ 2

/-- The conical-intersection set (the two equivalent degeneracy conditions of a 2×2 real symmetric matrix). -/
def conicalSet (M : TwoState X) : Set X :=
  {x | a M x = d M x ∧ b M x = 0}

/-- The conical-intersection set in discriminant form (equivalent to `conicalSet`, see `discr_eq_zero_iff_ci`). -/
def conicalSet' (M : TwoState X) : Set X :=
  {x | discr M x = 0}

/-- The two eigenvalues of a 2×2 real symmetric matrix (discriminant form). -/
noncomputable def eigenRoots (M : TwoState X) (x : X) : ℝ × ℝ :=
  (((a M x + d M x) + Real.sqrt (discr M x)) / 2,
   ((a M x + d M x) - Real.sqrt (discr M x)) / 2)

/-- M1.1: vanishing discriminant ⇔ the CI condition (upstream plan §4.1; acceptance item 1 of upstream §4.5). -/
theorem discr_eq_zero_iff_ci (M : TwoState X) (x : X) :
    discr M x = 0 ↔ a M x = d M x ∧ b M x = 0 := by
  unfold discr
  constructor
  · intro h
    have h1 : 0 ≤ (a M x - d M x) ^ 2 := sq_nonneg (a M x - d M x)
    have h2 : 0 ≤ 4 * (b M x) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg (b M x))
    have hsq1 : (a M x - d M x) ^ 2 = 0 := by nlinarith
    have hsq2 : 4 * (b M x) ^ 2 = 0 := by nlinarith
    have had : a M x = d M x := sub_eq_zero.mp (sq_eq_zero_iff.mp hsq1)
    have hb : b M x = 0 := by
      rcases mul_eq_zero.mp hsq2 with h4 | hb2
      · norm_num at h4
      · exact sq_eq_zero_iff.mp hb2
    exact ⟨had, hb⟩
  · rintro ⟨had, hb⟩
    simp [had, hb]

/-- M1.2: the discriminant is nonnegative (upstream plan §4.2). -/
theorem discr_nonneg (M : TwoState X) (x : X) : 0 ≤ discr M x := by
  unfold discr
  exact add_nonneg (sq_nonneg (a M x - d M x))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg (b M x)))

/-- M1.2: eigenvalue degeneracy ⇔ vanishing discriminant (upstream plan §4.2). -/
theorem degenerate_iff_discr_zero (M : TwoState X) (x : X) :
    (eigenRoots M x).1 = (eigenRoots M x).2 ↔ discr M x = 0 := by
  unfold eigenRoots
  have hd : 0 ≤ discr M x := discr_nonneg M x
  constructor
  · intro h
    have hmul := congrArg (fun t : ℝ => 2 * t) h
    field_simp at hmul
    have hs : Real.sqrt (discr M x) = 0 := by nlinarith
    exact (Real.sqrt_eq_zero hd).mp hs
  · intro h
    have hs : Real.sqrt (discr M x) = 0 := (Real.sqrt_eq_zero hd).mpr h
    rw [hs]
    ring

/-- M1.2: CI ⇔ eigenvalue degeneracy (upstream plan §4.2). -/
theorem ci_iff_degenerate (M : TwoState X) (x : X) :
    x ∈ conicalSet M ↔ (eigenRoots M x).1 = (eigenRoots M x).2 := by
  rw [degenerate_iff_discr_zero, discr_eq_zero_iff_ci]
  rfl

end TwoState


end PhotoLean