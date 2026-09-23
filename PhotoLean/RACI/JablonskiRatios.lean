import Mathlib
import PhotoLean.RACI.Jablonski

namespace PhotoLean


/-!
# RACI M4+ — 广义发射增强判据

AIE 只需要证明 `Φ_agg > Φ_sol`，不必强加 `kr_agg = kr_free`。
本文件把 M4 的等 kr 版本推广为 **knr/kr 比值判据**：
`Φ_agg > Φ_sol ⟺ knr_agg/kr_agg < knr_sol/kr_sol`。
-/

namespace RACI

/-- 量子产率差值恒等式（分母正时） -/
theorem quantumYield_sub_eq
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 ≤ knr1) (hknr2 : 0 ≤ knr2) :
    quantumYield kr2 knr2 - quantumYield kr1 knr1
      = (kr2 * knr1 - kr1 * knr2) / ((kr2 + knr2) * (kr1 + knr1)) := by
  unfold quantumYield
  have hd1 : kr1 + knr1 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hkr1 hknr1)
  have hd2 : kr2 + knr2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hkr2 hknr2)
  field_simp [hd1, hd2]
  ring

/-- 广义主判据：Φ_agg > Φ_sol ⟺ knr_agg/kr_agg < knr_sol/kr_sol -/
theorem quantumYield_gt_iff_ratio_lt
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 ≤ knr1) (hknr2 : 0 ≤ knr2) :
    quantumYield kr2 knr2 > quantumYield kr1 knr1 ↔
      knr2 / kr2 < knr1 / kr1 := by
  have hden : 0 < (kr2 + knr2) * (kr1 + knr1) :=
    mul_pos (add_pos_of_pos_of_nonneg hkr2 hknr2) (add_pos_of_pos_of_nonneg hkr1 hknr1)
  have hsub := quantumYield_sub_eq hkr1 hkr2 hknr1 hknr2
  constructor
  · intro h
    have hq : 0 < quantumYield kr2 knr2 - quantumYield kr1 knr1 := sub_pos.mpr h
    rw [hsub] at hq
    have hnum : 0 < kr2 * knr1 - kr1 * knr2 := (div_pos_iff_of_pos_right hden).mp hq
    have hlt : knr2 * kr1 < knr1 * kr2 := by linarith
    exact (div_lt_div_iff₀ hkr2 hkr1).mpr hlt
  · intro h
    have hlt : knr2 * kr1 < knr1 * kr2 := (div_lt_div_iff₀ hkr2 hkr1).mp h
    have hnum : 0 < kr2 * knr1 - kr1 * knr2 := by linarith
    have hq : 0 < quantumYield kr2 knr2 - quantumYield kr1 knr1 := by
      rw [hsub]
      exact (div_pos_iff_of_pos_right hden).mpr hnum
    exact sub_pos.mp hq

/-- 单向版本：knr/kr 下降 ⇒ Φ 上升 -/
theorem quantumYield_gt_of_ratio_lt
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 ≤ knr1) (hknr2 : 0 ≤ knr2)
    (h : knr2 / kr2 < knr1 / kr1) :
    quantumYield kr2 knr2 > quantumYield kr1 knr1 :=
  (quantumYield_gt_iff_ratio_lt hkr1 hkr2 hknr1 hknr2).mpr h

/-- 充分条件：辐射速率不降（kr_agg ≥ kr_sol）且无辐射速率下降 ⇒ Φ_agg > Φ_sol -/
theorem quantumYield_gt_of_knr_lt_of_kr_le
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 ≤ knr1) (hknr2 : 0 ≤ knr2)
    (hkr_le : kr1 ≤ kr2) (hknr : knr2 < knr1) :
    quantumYield kr2 knr2 > quantumYield kr1 knr1 := by
  apply quantumYield_gt_of_ratio_lt hkr1 hkr2 hknr1 hknr2
  have h1 : knr2 / kr2 < knr1 / kr2 := div_lt_div_of_pos_right hknr hkr2
  have h2 : knr1 / kr2 ≤ knr1 / kr1 := div_le_div_of_nonneg_left hknr1 hkr1 hkr_le
  exact lt_of_lt_of_le h1 h2

/-- 广义 RACI 模板：只要求 knr/kr 比值下降，不要求 kr 相等 -/
theorem raci_emission_enhancement_general
    {kr_free kr_agg knr_free knr_agg : ℝ}
    (hkr_free : 0 < kr_free) (hkr_agg : 0 < kr_agg)
    (hknr_free : 0 ≤ knr_free) (hknr_agg : 0 ≤ knr_agg)
    (hratio : knr_agg / kr_agg < knr_free / kr_free) :
    quantumYield kr_agg knr_agg > quantumYield kr_free knr_free :=
  quantumYield_gt_of_ratio_lt hkr_free hkr_agg hknr_free hknr_agg hratio


/-- 竞争比：无辐射/辐射速率比，决定发光分支比 -/
noncomputable def competitionRatio (kr knr : ℝ) : ℝ := knr / kr

/-- Φ = 1 / (1 + competitionRatio)（kr ≠ 0 时） -/
theorem quantumYield_eq_inv_one_add_competitionRatio {kr knr : ℝ} (hkr : kr ≠ 0) :
    quantumYield kr knr = 1 / (1 + competitionRatio kr knr) := by
  unfold quantumYield competitionRatio
  field_simp [hkr]

/-- knr/kr 下降 ⟺ Φ 上升（与 quantumYield_gt_iff_ratio_lt 同义） -/
theorem quantumYield_gt_iff_competitionRatio_lt
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 ≤ knr1) (hknr2 : 0 ≤ knr2) :
    quantumYield kr2 knr2 > quantumYield kr1 knr1 ↔
      competitionRatio kr2 knr2 < competitionRatio kr1 knr1 := by
  simpa [competitionRatio] using quantumYield_gt_iff_ratio_lt hkr1 hkr2 hknr1 hknr2

/-- 无辐射通道分解：knr = kCI + kOther -/
theorem competitionRatio_add {kr kCI kOther : ℝ} (hkr : kr ≠ 0) :
    competitionRatio kr (kCI + kOther) = kCI / kr + kOther / kr := by
  unfold competitionRatio
  field_simp [hkr]

/-- 通道竞争形式：即使 kr_agg < kr_sol，只要 CI 通道比值下降得足够多、
    其他无辐射通道比值不升高，则发光仍增强。
    这里没有任何 kr_agg/kr_sol > 1 的假设。 -/
theorem quantumYield_gt_of_channel_ratios
    {kr1 kr2 kCI1 kCI2 kOther1 kOther2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hkCI1 : 0 ≤ kCI1) (hkCI2 : 0 ≤ kCI2)
    (hkOther1 : 0 ≤ kOther1) (hkOther2 : 0 ≤ kOther2)
    (hOther_le : competitionRatio kr2 kOther2 ≤ competitionRatio kr1 kOther1)
    (hCI_lt : competitionRatio kr2 kCI2 < competitionRatio kr1 kCI1) :
    quantumYield kr2 (kCI2 + kOther2) > quantumYield kr1 (kCI1 + kOther1) := by
  have htotal :
      competitionRatio kr2 (kCI2 + kOther2) < competitionRatio kr1 (kCI1 + kOther1) := by
    rw [competitionRatio_add hkr2.ne', competitionRatio_add hkr1.ne']
    exact add_lt_add_of_lt_of_le hCI_lt hOther_le
  exact quantumYield_gt_of_ratio_lt hkr1 hkr2
    (add_nonneg hkCI1 hkOther1) (add_nonneg hkCI2 hkOther2)
    (by simpa [competitionRatio] using htotal)


/-- 先验 AIE 判据（乘法形式，不含任何统计/实验项）：
    Φ_agg > Φ_sol ⟺ knr_agg * kr_sol < knr_sol * kr_agg。
    这是二态 Jablonski 模型内的**充要条件**。 -/
theorem aie_iff_mul
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 ≤ knr1) (hknr2 : 0 ≤ knr2) :
    quantumYield kr2 knr2 > quantumYield kr1 knr1 ↔
      knr2 * kr1 < knr1 * kr2 := by
  have hden : 0 < (kr2 + knr2) * (kr1 + knr1) :=
    mul_pos (add_pos_of_pos_of_nonneg hkr2 hknr2) (add_pos_of_pos_of_nonneg hkr1 hknr1)
  have hsub := quantumYield_sub_eq hkr1 hkr2 hknr1 hknr2
  constructor
  · intro h
    have hq : 0 < quantumYield kr2 knr2 - quantumYield kr1 knr1 := sub_pos.mpr h
    rw [hsub] at hq
    have hnum : 0 < kr2 * knr1 - kr1 * knr2 := (div_pos_iff_of_pos_right hden).mp hq
    linarith
  · intro h
    have hnum : 0 < kr2 * knr1 - kr1 * knr2 := by linarith
    have hq : 0 < quantumYield kr2 knr2 - quantumYield kr1 knr1 := by
      rw [hsub]
      exact (div_pos_iff_of_pos_right hden).mpr hnum
    exact sub_pos.mp hq

/-- 抑制因子形式：设 c = knr_agg/knr_sol，d = kr_agg/kr_sol。
    AIE 成立 ⟺ 无辐射抑制因子小于辐射抑制因子：c < d。
    注意：**不要求 kr_agg ≥ kr_sol**。 -/
theorem aie_iff_knr_suppression_lt_kr_suppression
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 < knr1) (hknr2 : 0 ≤ knr2) :
    quantumYield kr2 knr2 > quantumYield kr1 knr1 ↔
      knr2 / knr1 < kr2 / kr1 := by
  have h := aie_iff_mul hkr1 hkr2 hknr1.le hknr2
  constructor
  · intro hΦ
    have hmul : knr2 * kr1 < knr1 * kr2 := h.mp hΦ
    exact (div_lt_div_iff₀ hknr1 hkr1).mpr (by simpa [mul_comm] using hmul)
  · intro hratio
    have hmul' : knr2 * kr1 < knr1 * kr2 := by
      have := (div_lt_div_iff₀ hknr1 hkr1).mp hratio
      simpa [mul_comm] using this
    exact h.mpr hmul'

end RACI


end PhotoLean