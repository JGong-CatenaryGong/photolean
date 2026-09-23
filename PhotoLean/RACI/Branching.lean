import Mathlib
import PhotoLean.RACI.TwoState

namespace PhotoLean


/-!
# RACI M1 — Branching：branching space、余维 2（线性层）、线性劈裂

来源：plan.md §4.3、§4.4。
状态：**SKELETON** —— 语句从 plan.md 转写；两处与草稿的有意差异：
1. `finrank_branching_eq_two` 中 `F` 按 plan §4.5 风险回退"先作为任意连续线性映射陈述"（fderiv 版保留）。
2. plan §4.4 草稿把 `eigenRoots` 直接用于矩阵；骨架引入 `eigenRootsMat`（矩阵级对应），
   语义等价（TwoState.eigenRoots 是其在 (H x) 上的特例）。
属主：prover_m1（独占文件）。
-/

open TwoState
open Module

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- 简并条件映射 F(x) = (a(x) - d(x), b(x)) 的 fderiv -/
noncomputable def F (M : TwoState X) (x : X) : X →L[ℝ] (ℝ × ℝ) :=
  fderiv ℝ (fun y => (TwoState.a M y - TwoState.d M y, TwoState.b M y)) x

/-- M1.3：branching space（ker F 的正交补）维数为 2（线性层的余维 2；plan §4.3）
    plan §4.5 风险回退：把 F 作为任意连续线性映射陈述（`F' : Y →L[ℝ] (ℝ × ℝ)`）；
    `ᗮ` 正交补需要 `[InnerProductSpace ℝ Y]`，故在 Y 上以 `InnerProductSpace` 提供范数结构，
    避免与 `[NormedSpace ℝ Y]` 的实例菱形。fderiv 版（上方 `F`）保留，Sprint 5 单独证 `F = fderiv ...`。 -/
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

/-- M1.3 显式二维实例：线性化模型（t=1）的简并映射 `v ↦ (2·v 0, v 1)`。
    定义域用 `EuclideanSpace ℝ (Fin 2)`（≃ ℝ²），其范数结构由 `InnerProductSpace` 唯一派生，
    避免 ℝ×ℝ 的 `NormedSpace`/`InnerProductSpace` 实例菱形（plan §4.3 验收） -/
noncomputable def Fex : (EuclideanSpace ℝ (Fin 2)) →L[ℝ] (ℝ × ℝ) where
  toFun := fun v => (2 * v 0, v 1)
  map_add' := by
    intro v w
    ext <;> simp [mul_add, Pi.add_apply]
  map_smul' := by
    intro c v
    ext <;> simp [mul_assoc, mul_left_comm, mul_comm, Pi.smul_apply]
  cont := by fun_prop

/-- M1.3：Fex 满射（plan §4.3 验收的 hreg） -/
theorem Fex_surjective : Function.Surjective Fex := by
  intro q
  refine ⟨![q.1 / 2, q.2], ?_⟩
  ext <;> simp [Fex]
  field_simp

/-- M1.3 显式实例：branching space 余维 2 在二维 Euclidean 空间上成立（plan §4.3 验收） -/
theorem finrank_branching_eq_two_explicit :
    finrank ℝ (LinearMap.ker Fex)ᗮ = 2 := by
  exact finrank_branching_eq_two Fex Fex_surjective

/-- 线性化两态矩阵：g 方向对角差，h 方向耦合（plan §4.4） -/
def linearized (gv hv t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![t * gv, t * hv; t * hv, -(t * gv)]

/-- 矩阵版本的判别式本征值对（plan §4.4 草稿将 eigenRoots 用于矩阵；见文件头注 2） -/
noncomputable def eigenRootsMat (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ × ℝ :=
  (((M 0 0 + M 1 1) + Real.sqrt ((M 0 0 - M 1 1) ^ 2 + 4 * (M 0 1) ^ 2)) / 2,
   ((M 0 0 + M 1 1) - Real.sqrt ((M 0 0 - M 1 1) ^ 2 + 4 * (M 0 1) ^ 2)) / 2)

/-- M1.4：线性化矩阵的判别式恒等式（纯多项式，ring_nf；plan §4.4） -/
theorem linearized_discr (gv hv t : ℝ) :
    (linearized gv hv t 0 0 - linearized gv hv t 1 1) ^ 2
      + 4 * (linearized gv hv t 0 1) ^ 2
      = 4 * t ^ 2 * (gv ^ 2 + hv ^ 2) := by
  simp [linearized]
  ring

/-- M1.4：沿 branching 方向的能级劈裂（plan §4.4；sqrt (t^2) = |t|） -/
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

/-- M1.4 推论：非零 t 与非零劈裂方向下能隙为正（M6 几何相位前置；plan §4.4） -/
theorem linearized_gap_pos (gv hv t : ℝ) (ht : t ≠ 0) (hgh : gv ^ 2 + hv ^ 2 ≠ 0) :
    0 < 2 * |t| * Real.sqrt (gv ^ 2 + hv ^ 2) := by
  have ht' : 0 < |t| := abs_pos.mpr ht
  have hX : 0 ≤ gv ^ 2 + hv ^ 2 := add_nonneg (sq_nonneg gv) (sq_nonneg hv)
  have hXpos : 0 < gv ^ 2 + hv ^ 2 := lt_of_le_of_ne hX (Ne.symm hgh)
  have hsqrt : 0 < Real.sqrt (gv ^ 2 + hv ^ 2) := Real.sqrt_pos.mpr hXpos
  exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) ht') hsqrt


end PhotoLean