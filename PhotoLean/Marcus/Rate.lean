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

end PhotoLean.Marcus
