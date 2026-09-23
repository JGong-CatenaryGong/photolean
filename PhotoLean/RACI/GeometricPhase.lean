import Mathlib
import PhotoLean.RACI.Branching

namespace PhotoLean


/-!
# RACI M6 — Longuet-Higgins 符号定理与几何相位（首版：规范回路）

来源：plan.md §11（M6 预览，依赖 M1.4 的线性劈裂）。
状态：M1–M4 与 M1* 完成后新增。
内容：对线性化模型（M1.4）沿单位圆回路 `H(t) = [[cos t, sin t], [sin t, −cos t]]`：
1. `loopLowerVec v(t) = (sin(t/2), −cos(t/2))` 是 H(t) 的本征矢（本征值 −1），且为单位矢量；
2. 绕 CI 一圈（t ↦ t + 2π）本征矢反号 —— Longuet-Higgins 符号定理（monodromy = −1）；
3. 回路上的能隙恒为 2（由 M1.4 的 `linearized_gap`），故绝热输运处处良定义。

属主：prover_m1（M6 依赖 M1.4 线）。
-/

namespace RACI

/-- 规范回路上的线性化 Hamiltonian：H(t) = [[cos t, sin t], [sin t, −cos t]]（M6） -/
noncomputable def loopH (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  linearized (Real.cos t) (Real.sin t) 1

/-- 低能本征矢 v(t) = (sin(t/2), −cos(t/2))（M6） -/
noncomputable def loopLowerVec (t : ℝ) : Fin 2 → ℝ :=
  ![Real.sin (t / 2), -Real.cos (t / 2)]

/-- M6.1：v(t) 是 H(t) 的本征矢，本征值 −1 -/
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

/-- M6.2：v(t) 为单位矢量（分量平方和为 1） -/
theorem loopLowerVec_sq_sum (t : ℝ) :
    loopLowerVec t 0 ^ 2 + loopLowerVec t 1 ^ 2 = 1 := by
  simp [loopLowerVec]

/-- M6.3：绕 CI 一圈本征矢反号（Longuet-Higgins 符号定理：monodromy = −1） -/
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

/-- M6.4：回路上的能隙恒为 2（M1.4 的 linearized_gap 实例化；绝热输运良定义） -/
theorem loop_gap (t : ℝ) :
    let e := eigenRootsMat (loopH t)
    e.1 - e.2 = 2 := by
  change (eigenRootsMat (loopH t)).1 - (eigenRootsMat (loopH t)).2 = 2
  have hgap := linearized_gap (Real.cos t) (Real.sin t) 1
  simpa [loopH] using hgap

end RACI


end PhotoLean