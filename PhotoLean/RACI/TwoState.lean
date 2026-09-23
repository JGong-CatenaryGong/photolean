import Mathlib

namespace PhotoLean


/-!
# RACI M1 — TwoState：2×2 实对称 Hamiltonian 的 CI 代数

来源：plan.md §2.2、§4.1、§4.2。
状态：**DONE** —— M1.1/M1.2 四条定理已证明（Sprint 2），无占位证明、无自定义 axiom。
属主：prover_m1（独占文件）。
纪律：本文件交付的定理不得含占位证明 / 自定义 `axiom`；
API 名漂移不猜测，交给 api_researcher 校准（记录于 proofs/API-NOTES.md）。
-/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- 两态绝热 Hamiltonian（核构型空间 X 上的 2×2 实对称矩阵族） -/
structure TwoState (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  H : X → Matrix (Fin 2) (Fin 2) ℝ
  h_symm : ∀ x, Matrix.IsSymm (H x)
  h_cont : Continuous H

namespace TwoState

/-- 矩阵元记号：a = H00, b = H01, d = H11 -/
def a (M : TwoState X) (x : X) : ℝ := M.H x 0 0

/-- 矩阵元记号：b = H01（耦合） -/
def b (M : TwoState X) (x : X) : ℝ := M.H x 0 1

/-- 矩阵元记号：d = H11 -/
def d (M : TwoState X) (x : X) : ℝ := M.H x 1 1

/-- 简并判别式：(a-d)^2 + 4 b^2 -/
def discr (M : TwoState X) (x : X) : ℝ :=
  (a M x - d M x) ^ 2 + 4 * (b M x) ^ 2

/-- 锥形交叉集合（2×2 实对称矩阵的两个等价简并条件） -/
def conicalSet (M : TwoState X) : Set X :=
  {x | a M x = d M x ∧ b M x = 0}

/-- 判别式形式的锥形交叉集合（与 conicalSet 等价，见 discr_eq_zero_iff_ci） -/
def conicalSet' (M : TwoState X) : Set X :=
  {x | discr M x = 0}

/-- 2×2 实对称矩阵的两个本征值（判别式形式） -/
noncomputable def eigenRoots (M : TwoState X) (x : X) : ℝ × ℝ :=
  (((a M x + d M x) + Real.sqrt (discr M x)) / 2,
   ((a M x + d M x) - Real.sqrt (discr M x)) / 2)

/-- M1.1：判别式零 ⇔ CI 条件（plan §4.1，验收清单 §4.5 第 1 项） -/
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

/-- M1.2：判别式非负（plan §4.2） -/
theorem discr_nonneg (M : TwoState X) (x : X) : 0 ≤ discr M x := by
  unfold discr
  exact add_nonneg (sq_nonneg (a M x - d M x))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg (b M x)))

/-- M1.2：本征值简并 ⇔ 判别式为零（plan §4.2） -/
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

/-- M1.2：CI ⇔ 本征值简并（plan §4.2） -/
theorem ci_iff_degenerate (M : TwoState X) (x : X) :
    x ∈ conicalSet M ↔ (eigenRoots M x).1 = (eigenRoots M x).2 := by
  rw [degenerate_iff_discr_zero, discr_eq_zero_iff_ci]
  rfl

end TwoState


end PhotoLean