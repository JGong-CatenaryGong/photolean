/-
PhotoLean.Marcus.RatModel — M5a：ℚ 上的判定层（可分派的分类器）。

**语句权威**：`proofs/probes/marcus-statement-skeleton.lean` 的 M5a 段（Sprint 0 已编译通过）。
本文件的 2 个定义与 2 条定理的签名与它**逐字一致**。

**为什么要 ℚ 副本**：`ℝ` 上的序经 `Classical`，**不可计算**，因此"某实例属于哪个区"
在 ℝ 上无法由内核算出。`ℚ` 上 `Rat` 的序与相等都可判定，于是判定层的证据链是：
内核计算（`by decide` / `norm_num`）→ 转移引理 `zoneQ_eq_zone` → ℝ 侧 `zone_eq_inverted_iff`。
转移引理就是"ℚ 上的判定对 ℝ 理论有约束力"的依据（plan §2.3）。

**实测边界**（prover_c 探针 `proofs/probes/marcus-prover_c-scratch.lean`）：
`by decide` 只对**整数**字面量可算（如 `zoneQ 1 3`）；对**含除法**的有理字面量
（如 `zoneQ 1 (3/4)`）会卡在 `Rat` 的 gcd/除法归约上，必须改用 `norm_num [zoneQ]`。

**命名约定（工具链硬约束）**：Lean 4 中 `λ` 是 lambda 关键字，不可作标识符，
故物理记号一律 ASCII 化：重组能 `lam`、驱动力 `x`。

验收（契约 `proofs/ENGINE.yml`）：
  proofs/scripts/lake build PhotoLean.Marcus.RatModel
  proofs/scripts/check.sh --strict PhotoLean.Marcus.RatModel
  proofs/scripts/axioms.sh PhotoLean.Marcus.RatModel PhotoLean.Marcus.Rat.<theorem>
-/
import PhotoLean.Marcus.Basic

namespace PhotoLean.Marcus.Rat

/-! ## 定义（plan §2.3 / §8.1） -/

/-- ℚ 上的分类器（可计算：`Rat` 的序与相等都可判定）。--/
def zoneQ (lam x : ℚ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

/-- ℚ 上的马库斯势垒：`(lam - x)^2 / (4 lam)`（与 ℝ 版 `barrier` 同式，供数值判定用）。--/
def barrierQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

end PhotoLean.Marcus.Rat
