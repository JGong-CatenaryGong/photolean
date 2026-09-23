import Mathlib

namespace PhotoLean


/-!
# RACI M3 — Barrier：势垒型无辐射速率单调性

来源：plan.md §6.3。
状态：**SKELETON** —— 语句从 plan.md 转写。
属主：prover_m3（独占文件）。
-/

namespace RACI

/-- 势垒型无辐射速率：k_nr = A exp(-β B)（plan §6.3） -/
noncomputable def barrierRate (A β B : ℝ) : ℝ :=
  A * Real.exp (-(β * B))

/-- M3.3：势垒型无辐射速率反单调（plan §6.3；复刻 M3.1 的指数步骤后乘正数 A） -/
theorem barrierRate_antitone
    (hA : 0 < A) (hβ : 0 < β) {B1 B2 : ℝ}
    (hB : B1 < B2) :
    barrierRate A β B2 < barrierRate A β B1 := by
  have h1 : β * B1 < β * B2 := mul_lt_mul_of_pos_left hB hβ
  have h2 : -(β * B2) < -(β * B1) := neg_lt_neg h1
  have h3 := Real.exp_strictMono h2
  have h4 := mul_lt_mul_of_pos_left h3 hA
  simpa [barrierRate] using h4

end RACI


end PhotoLean