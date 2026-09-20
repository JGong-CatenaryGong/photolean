/-
marcus-lead-crosscheck.lean — lead 的**独立交叉验证**（非交付文件）。

目的：不调用任何**交付的实例定理**（`inst_I4_mcc_rate_drop` 等），
直接在**定义层**重新推导同一条结论，用来交叉验证实例层没有"循环论证/顺序依赖"式的错误。
运行：proofs/scripts/lake env lean proofs/probes/marcus-lead-crosscheck.lean
-/
import PhotoLean.Marcus.Basic

set_option linter.unusedVariables false

namespace LeadCrossCheck

open PhotoLean.Marcus

/-- 文献参数下的两个势垒值（定义层直接算，不经任何实例定理）。--/
example : barrier (1.20 : ℝ) 1.23 = 0.0001875 := by norm_num [barrier]
example : barrier (1.20 : ℝ) 2.40 = 0.3 := by norm_num [barrier]
example : barrier (1.20 : ℝ) 2.00 = 2 / 15 := by norm_num [barrier]

/-- 反转区判定的定义层重推（`lam < x`）。--/
example : (1.20 : ℝ) < 2.40 := by norm_num
example : ¬ ((2.40 : ℝ) < 1.20) := by norm_num
example : (0.60 : ℝ) < 1.20 := by norm_num

/-- **核心交叉验证**：不调用交付的 `inverted_rate_decreases`，直接用
    `Real.exp_lt_exp` + 势垒值重推 `rate(2.40) < rate(1.23)`（对任意 `kBT > 0`）。--/
example {kBT : ℝ} (hkBT : 0 < kBT) :
    Real.exp (-(barrier (1.20 : ℝ) 2.40) / kBT) < Real.exp (-(barrier (1.20 : ℝ) 1.23) / kBT) := by
  apply Real.exp_lt_exp.mpr
  have h1 : barrier (1.20 : ℝ) 1.23 = 0.0001875 := by norm_num [barrier]
  have h2 : barrier (1.20 : ℝ) 2.40 = 0.3 := by norm_num [barrier]
  rw [h1, h2]
  rw [div_lt_div_iff_of_pos_right hkBT]
  norm_num

/-- 同上，完整 `rate` 形式（前置因子 A=1）。--/
example {kBT : ℝ} (hkBT : 0 < kBT) :
    rate (1 : ℝ) (1.20 : ℝ) kBT 1 2.40 < rate (1 : ℝ) (1.20 : ℝ) kBT 1 1.23 := by
  unfold rate
  apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 1)
  apply Real.exp_lt_exp.mpr
  have h1 : barrier (1.20 : ℝ) 1.23 = 0.0001875 := by norm_num [barrier]
  have h2 : barrier (1.20 : ℝ) 2.40 = 0.3 := by norm_num [barrier]
  rw [h1, h2]
  simp only [mul_one]
  rw [div_lt_div_iff_of_pos_right hkBT]
  norm_num

/-- 正常区反向：`rate(0.60) < rate(1.20)`（定义层重推）。--/
example {kBT : ℝ} (hkBT : 0 < kBT) :
    rate (1 : ℝ) (1.20 : ℝ) kBT 1 0.60 < rate (1 : ℝ) (1.20 : ℝ) kBT 1 1.20 := by
  unfold rate
  apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 1)
  apply Real.exp_lt_exp.mpr
  have h1 : barrier (1.20 : ℝ) 1.20 = 0 := by norm_num [barrier]
  have h2 : barrier (1.20 : ℝ) 0.60 = 0.075 := by norm_num [barrier]
  rw [h1, h2]
  simp only [mul_one]
  rw [div_lt_div_iff_of_pos_right hkBT]
  norm_num

end LeadCrossCheck
