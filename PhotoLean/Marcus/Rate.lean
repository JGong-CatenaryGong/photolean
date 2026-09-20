/-
PhotoLean.Marcus.Rate — M3 速率层（Marcus 反转区）。

**语句权威**：`proofs/probes/marcus-statement-skeleton.lean` 的 M3 段
（Sprint 0 已编译通过）。本文件 3 条定理的签名与它**逐字一致**；
定理体已全部补齐（零占位证明、无自定义公理声明）。

**依赖**：只 import `PhotoLean.Marcus.Basic`（M1 已过独立验收），复用其中的
`barrier` / `rate`，不重新定义。本批三条定理**不需要势垒代数**，故刻意
不 import `PhotoLean.Marcus.Barrier`（`normal_rate_increases` /
`inverted_rate_decreases` / `rate_peak_at_lam` 属于 Sprint 3，届时再加）。

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

end PhotoLean.Marcus
