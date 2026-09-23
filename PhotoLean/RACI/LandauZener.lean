import Mathlib

namespace PhotoLean


/-!
# RACI M3 — LandauZener：LZ 概率单调性

来源：plan.md §6.1、§6.2、§6.4。
状态：**SKELETON** —— 语句从 plan.md 转写；与草稿的差异：
§6.2 按 plan 证明步骤的要求把 `0 < c0` 写成显式前提（骨架已加入 `(hc0 : 0 < c0)`）。
属主：prover_m3（独占文件）。
-/

namespace RACI

/-- Landau-Zener 型概率：P = exp(-(c * a))（常数已吸收进 c；plan §6.1） -/
noncomputable def lzProbability (c a : ℝ) : ℝ :=
  Real.exp (-(c * a))

/-- M3.1：抽象指数函数反单调（`Real.exp_strictMono`；plan §6.1，API-NOTES 记录 8） -/
theorem lz_antitone (hc : 0 < c) {a b : ℝ} (hab : a < b) :
    lzProbability c b < lzProbability c a := by
  have h1 : c * a < c * b := mul_lt_mul_of_pos_left hab hc
  have h2 : -(c * b) < -(c * a) := neg_lt_neg h1
  have h3 := Real.exp_strictMono h2
  simpa [lzProbability] using h3

/-- M3.2：LZ 概率关于能隙平方反单调（plan §6.2；`0 < c0` 为显式前提） -/
theorem lz_probability_antitone_in_gap
    {Δ1 Δ2 v F c0 : ℝ}
    (hv : 0 < v) (hF : 0 < F) (hc0 : 0 < c0)
    (hΔ0 : 0 ≤ Δ1) (hΔ : Δ1 < Δ2) :
    lzProbability (c0 / (v * F)) (Δ2 ^ 2) <
      lzProbability (c0 / (v * F)) (Δ1 ^ 2) := by
  have hsq : Δ1 ^ 2 < Δ2 ^ 2 := by
    rw [sq_lt_sq]
    simpa [abs_of_nonneg hΔ0, abs_of_pos (lt_of_le_of_lt hΔ0 hΔ)] using hΔ
  exact lz_antitone (div_pos hc0 (mul_pos hv hF)) hsq

/-- M3.4（可选）：FGR 洛伦兹线型关于能隙的反单调（plan §6.4） -/
noncomputable def lorentzian (σ x : ℝ) : ℝ :=
  1 / (1 + (x / σ) ^ 2)

theorem lorentzian_antitone_on_norm
    (hσ : 0 < σ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    lorentzian σ y < lorentzian σ x := by
  have h1 : x / σ < y / σ := div_lt_div_of_pos_right hxy hσ
  have hx' : 0 ≤ x / σ := div_nonneg hx hσ.le
  have h2 : (x / σ) ^ 2 < (y / σ) ^ 2 := by
    rw [sq_lt_sq]
    simpa [abs_of_nonneg hx', abs_of_pos (lt_of_le_of_lt hx' h1)] using h1
  have h3 : 1 + (x / σ) ^ 2 < 1 + (y / σ) ^ 2 := by linarith
  have h4 : 0 < 1 + (x / σ) ^ 2 := by
    have : 0 ≤ (x / σ) ^ 2 := sq_nonneg (x / σ)
    linarith
  have h5 : 1 / (1 + (y / σ) ^ 2) < 1 / (1 + (x / σ) ^ 2) :=
    one_div_lt_one_div_of_lt h4 h3
  simpa [lorentzian] using h5

end RACI


end PhotoLean