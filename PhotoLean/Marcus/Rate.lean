/-
PhotoLean.Marcus.Rate — M3 速率层（Marcus 反转区）。

**语句权威**：`proofs/probes/marcus-statement-skeleton.lean` 的 M3 段
（Sprint 0 已编译通过）。本文件 3 条定理的签名与它**逐字一致**；
定理体已全部补齐（零占位证明、无自定义公理声明）。

**依赖**：`PhotoLean.Marcus.Basic`（M1 已过独立验收，提供 `barrier` / `rate`，
不重新定义）与 `PhotoLean.Marcus.Barrier`（M2 势垒代数，已过独立验收）。
第一批三条定理（`rate_pos` / `rate_gt_of_barrier_lt` / `rate_ratio`）只需 M1；
本批（Sprint 3）三条速率单调性定理复用 M2 的 `barrier_mono_of_pos` /
`barrier_antitone_of_pos` / `barrier_min_at_lam`，故追加 import `Barrier` ——
两条组合定理是"势垒代数 → 速率层"的纯复合，不引入新的实分析风险。

**风险隔离**：`rate_gt_of_barrier_lt` 是全项目**唯一**使用 `Real.exp` 单调性的
地方，其余全是代数 —— 因此 M3 的全部实分析风险集中在这一条。
已实测的 mathlib 事实（mathlib v4.17.0）：`Real.exp_lt_exp` 本身就是 `↔`
（`Real.exp a < Real.exp b ↔ a < b`），**不存在** `Real.exp_lt_exp_iff`。

**注**：本文件头刻意不写出被 `check.sh --strict` 扫描的关键字字面量
（块注释同样在扫描范围内，写了会造成误报 FAIL）。

验收（契约 `proofs/ENGINE.yml`）：
  proofs/scripts/lake build PhotoLean.Marcus.Rate
  proofs/scripts/check.sh --strict PhotoLean.Marcus.Rate
  proofs/scripts/axioms.sh PhotoLean.Marcus.Rate PhotoLean.Marcus.<theorem>
-/
import PhotoLean.Marcus.Basic
import PhotoLean.Marcus.Barrier

namespace PhotoLean.Marcus

/-! ## 正性（M3 §6） -/

/-- 前置因子正 ⇒ 速率正（M4 锐利性的显式前提之一就是它）。

证明：`k = A · exp(-ΔG‡/(k_B T))`，`positivity` 用 `hA : 0 < A` 与
`Real.exp_pos` 直接闭合乘积的正性，**不需要** `kB*T` 的符号假设。 -/
theorem rate_pos {A lam kB T : ℝ} (hA : 0 < A) (x : ℝ) : 0 < rate A lam kB T x := by
  unfold rate; positivity

/-! ## 核心转移引理（M3 §6） -/

/-- **核心转移引理**：势垒更小 ⇒ 速率更大。整个项目唯一的 exp 单调性使用点。

证明：`h : Φx < Φy` → 取负 `-(Φy)/(kBT) < -(Φx)/(kBT)`（`linarith` +
`div_lt_div_of_pos_right` 用 `hkT`）→ `Real.exp_lt_exp.mpr` 吃掉 exp
→ `mul_lt_mul_of_pos_left _ hA` 乘回前置因子 `A > 0`。

物理含义：这是"势垒越低速率越大"这条唯象直觉在速率层的唯一入口；
后续所有速率单调性定理（M3 剩余三条、M4a 描述子）都由它 + 势垒代数复合得到。 -/
theorem rate_gt_of_barrier_lt {A lam kB T : ℝ} (hA : 0 < A) (hkT : 0 < kB * T) {x y : ℝ}
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  have hu : -(barrier lam y) / (kB * T) < -(barrier lam x) / (kB * T) :=
    div_lt_div_of_pos_right (by linarith) hkT
  have hexp := Real.exp_lt_exp.mpr hu
  unfold rate
  exact mul_lt_mul_of_pos_left hexp hA

/-! ## 定量形式（M3 §6，拉伸目标） -/

/-- 定量形式：反转区抑制因子的指数形式。

`rate y / rate x = exp ((Φx - Φy)/(kBT))` —— 即速率比只依赖势垒差，
与前置因子 `A` 无关（`A ≠ 0` 正是为了约掉它）。

证明：`unfold rate` → `mul_div_mul_left _ _ hA` 约掉 `A`
→ `← Real.exp_sub` 合并两个 exp → `congr 1` 归结为纯代数
→ `field_simp`（用 `hkT : kB*T ≠ 0` 清分母）+ `ring`。

注：本条的假设是 `A ≠ 0` 与 `kB*T ≠ 0`（比 `rate_pos` / 核心引理的
`0 < A` / `0 < kB*T` 弱），与 statement skeleton 逐字一致。 -/
theorem rate_ratio {A lam kB T : ℝ} (hA : A ≠ 0) (hkT : kB * T ≠ 0) (x y : ℝ) :
    rate A lam kB T y / rate A lam kB T x
      = Real.exp ((barrier lam x - barrier lam y) / (kB * T)) := by
  unfold rate
  rw [mul_div_mul_left _ _ hA, ← Real.exp_sub]
  congr 1
  field_simp
  ring

/-! ## 速率单调性与峰位（M3 §6，Sprint 3；依赖 M2 势垒代数）

三条定理都是"势垒单调性 + 核心引理"的两行复合，无新的实分析风险。
注意 `rate_gt_of_barrier_lt` 的方向：`h : Φx < Φy ⇒ rate y < rate x`，
因此"正常区 Φ 递减 ⇒ 速率递增"这一支要把 `x₂` 当作**更小的势垒**喂进去
（即取核心引理的 `y := x₁`），"反转区 Φ 递增 ⇒ 速率递减"则取 `y := x₂`。 -/

/-- 正常区：驱动力越大速率越大（`0 ≤ x₁ < x₂ ≤ lam`，`lam > 0`）。

证明：M2 的 `barrier_antitone_of_pos` 给出 `Φ x₂ < Φ x₁`，
把 `x₂` 当更小势垒喂给核心引理 `rate_gt_of_barrier_lt`（`y := x₁`），
即得 `rate x₁ < rate x₂`。物理含义：正常区里驱动力越接近重组能，
势垒越低、反应越快。 -/
theorem normal_rate_increases {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    {x₁ x₂ : ℝ} (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) :
    rate A lam kB T x₁ < rate A lam kB T x₂ :=
  rate_gt_of_barrier_lt hA hkT (barrier_antitone_of_pos hlam h₁ h₂ h₃)

/-- 反转区：驱动力越大速率越小 —— **马库斯反转区**（`lam < x₁ < x₂`，`lam > 0`）。

证明：M2 的 `barrier_mono_of_pos` 给出 `Φ x₁ < Φ x₂`（把 `h₁ : lam < x₁`
弱化为它需要的 `lam ≤ x₁`），把 `x₂` 当更大势垒喂给核心引理（`y := x₂`），
即得 `rate x₂ < rate x₁`。物理含义：这是"马库斯反转"的核心 ——
驱动力超过重组能后，继续增大驱动力反而使势垒升高、反应变慢。 -/
theorem inverted_rate_decreases {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    {x₁ x₂ : ℝ} (h₁ : lam < x₁) (h₂ : x₁ < x₂) :
    rate A lam kB T x₂ < rate A lam kB T x₁ :=
  rate_gt_of_barrier_lt hA hkT (barrier_mono_of_pos hlam (le_of_lt h₁) h₂)

/-- 峰值：`x = lam` 处速率**最大**（最快反应的驱动力恰等于重组能）。

这是本批唯一用到**非严格** `exp` 单调性（`Real.exp_le_exp`，同样是 `↔`）的定理，
结构比前两条多一层：M2 的 `barrier_min_at_lam` 给出 `Φ lam ≤ Φ x`
→ 取负并按 `kB*T ≥ 0` 除（`div_le_div_of_nonneg_right`，用 `le_of_lt hkT`）
→ `Real.exp_le_exp.mpr` → 乘前置因子 `A ≥ 0`（`mul_le_mul_of_nonneg_left`）。
物理含义：`x = lam` 是势垒为零的无势垒点，故它同时是正常区（递增）与
反转区（递减）两支的公共端点，峰位与 M1 分类器的 `Zone.barrierless` 一致。 -/
theorem rate_peak_at_lam {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    (x : ℝ) : rate A lam kB T x ≤ rate A lam kB T lam := by
  have hb : barrier lam lam ≤ barrier lam x := barrier_min_at_lam hlam x
  have hu : -(barrier lam x) / (kB * T) ≤ -(barrier lam lam) / (kB * T) :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hkT)
  have hexp := Real.exp_le_exp.mpr hu
  unfold rate
  exact mul_le_mul_of_nonneg_left hexp (le_of_lt hA)

end PhotoLean.Marcus
