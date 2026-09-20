/-
  marcus-api-cast-normnum.lean — API-NOTES 收尾追加（cast 家族 + norm_num 边界 + 倒数/交叉相乘）

  目的（三批，逐条**独立复核**，非照抄交付者结论）
    ⑴ ℚ→ℝ `Rat.cast_*` 家族的名字与签名，以及两条**"尾巴规则相反"**的坑；
    ⑵ `norm_num` 的**可靠域边界**：不认识 `Real.exp` 的正性；
    ⑶ `one_div_le_one_div_of_le`（取倒数翻转方向）、`div_lt_div_iff₀` / `div_lt_iff₀`
       （多分母不等式的交叉相乘），以及 `field_simp` 对**不等式**的失败路径。

  运行命令（在仓库根目录执行）
    proofs/scripts/lake env lean proofs/probes/marcus-api-cast-normnum.lean

  本文件为 **正向探针**：必须 0 error / 0 warning。
  **失败**路径（"expect FAIL"）只出现在注释里，附原始报错。

  校准基准：mathlib v4.17.0（lean-toolchain = leanprover/lean4:v4.17.0）
  校准日期：2026-09-20 — api_researcher

  English:
  marcus-api-cast-normnum.lean — closing addendum to API-NOTES (the cast family + the `norm_num` boundary + reciprocals / cross-multiplication)

  Purpose (three batches, each **independently re-checked**, rather than merely copying the deliverer's conclusions)
    ⑴ the names and signatures of the ℚ→ℝ `Rat.cast_*` family, plus two traps where **the "tail rules" disagree**;
    ⑵ the **trustworthy-domain boundary** of `norm_num`: it does not know positivity of `Real.exp`;
    ⑶ `one_div_le_one_div_of_le` (taking reciprocals flips the direction), `div_lt_div_iff₀` / `div_lt_iff₀`
       (cross-multiplication for inequalities with several denominators), and the failure path of `field_simp` on **inequalities**.

  Run command (executed from the repository root)
    proofs/scripts/lake env lean proofs/probes/marcus-api-cast-normnum.lean

  This file is a **positive probe**: it must give 0 error / 0 warning.
  **Failure** paths ("expect FAIL") occur only inside comments, together with the original error message.

  Calibration baseline: mathlib v4.17.0 (lean-toolchain = leanprover/lean4:v4.17.0)
  Calibration date: 2026-09-20 — api_researcher
-/

import Mathlib

set_option linter.unusedVariables false

namespace MarcusApiCast

/-! ## ⑴ ℚ→ℝ cast 家族

  `#check` 原始输出（完整，`@` 形式以暴露隐式参数）：

  ```
  @Rat.cast_pow {α} [DivisionRing α] (p : ℚ) (n : ℕ) : ↑(p ^ n) = ↑p ^ n
  @Rat.cast_mul {α} [DivisionRing α] [CharZero α] (p q : ℚ) : ↑(p * q) = ↑p * ↑q
  @Rat.cast_sub {α} [DivisionRing α] [CharZero α] (p q : ℚ) : ↑(p - q) = ↑p - ↑q
  @Rat.cast_div {α} [DivisionRing α] [CharZero α] (p q : ℚ) : ↑(p / q) = ↑p / ↑q
  @Rat.cast_add {α} [DivisionRing α] [CharZero α] (p q : ℚ) : ↑(p + q) = ↑p + ↑q
  @Rat.cast_ofNat {α} [DivisionRing α] (n : ℕ) [n.AtLeastTwo] :
      ↑(OfNat.ofNat n) = OfNat.ofNat n          ← ⚠️ 需要 [n.AtLeastTwo]
  @Rat.cast_natCast {α} [DivisionRing α] (n : ℕ) : ↑↑n = ↑n
  @Rat.cast_inv {α} [DivisionRing α] [CharZero α] (p : ℚ) : ↑p⁻¹ = (↑p)⁻¹
  @Rat.cast_zero {α} [DivisionRing α] : ↑0 = 0
  @Rat.cast_inj {α} [DivisionRing α] [CharZero α] {p q : ℚ} : ↑p = ↑q ↔ p = q
  ```

  要点：
  - `cast_pow` / `cast_ofNat` / `cast_natCast` / `cast_zero` **不需要** `[CharZero α]`；
    其余（`mul` / `sub` / `div` / `add` / `inv` / `inj`）**需要**。
  - `cast_ofNat` 带 `[n.AtLeastTwo]`，故 `↑(2 : ℚ)` 这类字面量能转，`↑(1 : ℚ)` 走 `cast_one`。
  - `cast_div` 的 `[CharZero α]` 是**数学上必需**的（`p/q` 的分母约定要 `q ≠ 0` 侧无零因子）。

  English:
  Section ⑴ — the ℚ→ℝ cast family.

  The raw `#check` output is quoted in full above (the `@` form exposes the implicit arguments).
  Inside that quoted output, the annotation after the arrow glosses as "requires `[n.AtLeastTwo]`".

  Key points:
  - `cast_pow` / `cast_ofNat` / `cast_natCast` / `cast_zero` do **not** need `[CharZero α]`;
    the others (`mul` / `sub` / `div` / `add` / `inv` / `inj`) **do**.
  - `cast_ofNat` carries `[n.AtLeastTwo]`, so literals such as `↑(2 : ℚ)` can be cast, whereas `↑(1 : ℚ)` goes through `cast_one`.
  - The `[CharZero α]` of `cast_div` is **mathematically necessary** (the denominator convention for `p/q` requires no zero divisor on the `q ≠ 0` side).
-/

#check @Rat.cast_pow
#check @Rat.cast_mul
#check @Rat.cast_sub
#check @Rat.cast_div
#check @Rat.cast_add
#check @Rat.cast_ofNat
#check @Rat.cast_natCast
#check @Rat.cast_inv
#check @Rat.cast_zero
#check @Rat.cast_inj

noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

noncomputable def rate (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(barrier lam x) / (kB * T))

def barrierQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- 主目标：ℚ 侧势垒经 cast 与 ℝ 侧一致（M5a `barrierQ_cast`）。**不需要任何前提**。

English: Main goal: the ℚ-side barrier agrees with the ℝ-side one after casting (M5a `barrierQ_cast`). **No hypotheses are needed.** -/
theorem barrierQ_cast (lam x : ℚ) : ((barrierQ lam x : ℚ) : ℝ) = barrier (lam : ℝ) (x : ℝ) := by
  unfold barrierQ barrier
  push_cast
  ring

/-- **尾巴规则相反（路线 1）**：`push_cast` **单独不够** —— 它归一到 `X = X` 后**不**自动收尾，
    必须补 `ring`（或 `rfl`）。实测去掉 `ring` 报：
    `error: unsolved goals / ⊢ (↑lam - ↑x)^2/(4*↑lam) = (↑lam - ↑x)^2/(4*↑lam)`。

English: **The "tail rules" disagree (route 1)**: `push_cast` **is not enough on its own** — after normalising to `X = X` it does **not** close the goal automatically,
    so `ring` (or `rfl`) must be added. Measured: dropping `ring` reports:
    `error: unsolved goals / ⊢ (↑lam - ↑x)^2/(4*↑lam) = (↑lam - ↑x)^2/(4*↑lam)`. -/
theorem barrierQ_cast_pushcast (lam x : ℚ) :
    ((barrierQ lam x : ℚ) : ℝ) = barrier (lam : ℝ) (x : ℝ) := by
  unfold barrierQ barrier
  push_cast
  ring

/-- **尾巴规则相反（路线 2）**：显式 `rw` 一串 cast 引理**自带 `rfl` 收尾**，
    后面再写 `ring` 报 `error: no goals to be solved`。故这条路线**不能有尾巴战术**。

English: **The "tail rules" disagree (route 2)**: an explicit `rw` chain of cast lemmas **closes the goal by `rfl` on its own**,
    so writing `ring` afterwards reports `error: no goals to be solved`. Hence this route **must not carry a tail tactic**. -/
theorem barrierQ_cast_rw (lam x : ℚ) :
    ((barrierQ lam x : ℚ) : ℝ) = barrier (lam : ℝ) (x : ℝ) := by
  unfold barrierQ barrier
  rw [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]

/-- **`Rat.cast_inj` 的 `α` 在 `apply` 下会卡住**（`CharZero ?m` 无法求解）。
    ❌ 写法：`apply Rat.cast_inj.mp` → `typeclass instance problem is stuck … CharZero ?m.41`
    ✅ 写法：**显式给出目标域** `apply (Rat.cast_inj (α := ℝ)).mp`。

English: **The `α` of `Rat.cast_inj` gets stuck under `apply`** (`CharZero ?m` cannot be solved).
    ❌ Form: `apply Rat.cast_inj.mp` → `typeclass instance problem is stuck … CharZero ?m.41`
    ✅ Form: **give the target field explicitly**, `apply (Rat.cast_inj (α := ℝ)).mp`. -/
theorem barrierQ_zero_lam (x : ℚ) : barrierQ 0 x = 0 := by
  apply (Rat.cast_inj (α := ℝ)).mp
  rw [barrierQ_cast]
  norm_num [barrier]

/-! ## ⑵ `norm_num` 的可靠域边界：不认识 `Real.exp` 的正性

  **实测偏差**（M5b / `inst_I7_unphysical_rate_not_pos`）：
  派发提示里的写法 `intro h; have := h 0; norm_num [rate, barrier] at this`
  **不足以收尾** —— 它把假设化为 `Real.exp (1/4) < 0`（或 `0 < -exp(1/4)`），
  但 `norm_num` **不认识 `Real.exp` 的正性**，留下未解目标 `⊢ False`。

  ✅ 奏效写法：`norm_num [barrier]` 算出势垒值 → `rw [rate, hb] at h0`
  → `norm_num at h0` → **`linarith [Real.exp_pos (1/4)]`**。

  与已有的两条可靠域条目并列：
  | 工具 | 可靠域 | 不可靠域 | 出路 |
  |---|---|---|---|
  | `decide` | ℚ 整数/无除法字面量 | 含除法/十进制的 ℚ | `norm_num [zoneQ]` |
  | `norm_num` | 多项式/字面量的算术归约、`barrier` 求值 | `Real.exp` 的**正性/单调性** | `linarith [Real.exp_pos c]` |
  | `field_simp` | **等式**（+ 显式非零前提） | **不等式** | `div_lt_div_iff₀` 交叉相乘 |

  English:
  **Measured deviation** (M5b / `inst_I7_unphysical_rate_not_pos`):
  the form used in the dispatch note, `intro h; have := h 0; norm_num [rate, barrier] at this`,
  **is not enough to close the goal** — it reduces the hypothesis to `Real.exp (1/4) < 0` (or `0 < -exp(1/4)`),
  but `norm_num` **does not know positivity of `Real.exp`**, leaving the unsolved goal `⊢ False`.

  ✅ Form that works: `norm_num [barrier]` computes the barrier value → `rw [rate, hb] at h0`
  → `norm_num at h0` → **`linarith [Real.exp_pos (1/4)]`**.

  Listed next to the two existing trustworthy-domain entries:
  | tool | trustworthy domain | unreliable domain | way out |
  |---|---|---|---|
  | `decide` | ℚ integer / division-free literals | ℚ with division or decimals | `norm_num [zoneQ]` |
  | `norm_num` | arithmetic normalisation of polynomials and literals; evaluation of `barrier` | **positivity / monotonicity** of `Real.exp` | `linarith [Real.exp_pos c]` |
  | `field_simp` | **equalities** (+ explicit nonzero hypotheses) | **inequalities** | cross-multiplication via `div_lt_div_iff₀` |
-/

/-- 见上：`Real.exp_pos` 给出正性，`norm_num [barrier]` 给出势垒值，两者缺一不可。

English: See above: `Real.exp_pos` supplies positivity and `norm_num [barrier]` supplies the barrier value; neither may be omitted. -/
theorem inst_I7_unphysical_rate_not_pos : ¬ (∀ x : ℝ, 0 < rate (-1) (-1) 1 1 x) := by
  intro h
  have h0 := h 0
  -- ❌ 不足以收尾：`norm_num [rate, barrier] at h0` → 留下 `⊢ False` 未解
  -- English: ❌ Not enough to close the goal: `norm_num [rate, barrier] at h0` leaves `⊢ False` unsolved
  have hb : barrier (-1) 0 = -(1 / 4) := by norm_num [barrier]
  rw [rate, hb] at h0
  norm_num at h0
  linarith [Real.exp_pos (1 / 4)]

-- `Real.exp_pos` 已在 A 组登记（`(x : ℝ) : 0 < Real.exp x`），此处确认仍是同一签名
-- English: `Real.exp_pos` is already registered in group A (`(x : ℝ) : 0 < Real.exp x`); here we confirm that it still has the same signature
#check Real.exp_pos

-- 同一证明链上的备用工具：`mul_neg_of_neg_of_pos`（负数 × 正数 = 负数）
-- English: Spare tool on the same proof chain: `mul_neg_of_neg_of_pos` (negative × positive = negative)
#check mul_neg_of_neg_of_pos
example (x : ℝ) : rate (-1) (-1) 1 1 x < 0 := by
  unfold rate
  have hb : barrier (-1) x = -((x + 1) ^ 2) / 4 := by unfold barrier; ring
  rw [hb]
  apply mul_neg_of_neg_of_pos (by norm_num)
  exact Real.exp_pos _

/-! ## ⑶ 倒数 / 交叉相乘 / `field_simp` 边界

  `#check` 原始输出：

  ```
  one_div_le_one_div_of_le {α} [LinearOrderedSemifield α] {a b : α} (ha : 0 < a) (h : a ≤ b) :
    1 / b ≤ 1 / a                                   ← **取倒数翻转方向**（a ≤ b ↦ 1/b ≤ 1/a）
  div_lt_div_iff₀ {G₀} [CommGroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀]
    [PosMulReflectLT G₀] [PosMulStrictMono G₀] {a b c d : G₀} (hb : 0 < b) (hd : 0 < d) :
    a / b < c / d ↔ a * d < c * b                   ← **两个分母都要正性**
  div_lt_iff₀ {G₀} … (hc : 0 < c) : b / c < a ↔ b < a * c
  ```

  用途：`PhotoLean/Marcus/Reorg.lean` 的 `hgeom_of_nonoverlap`（Pekar 几何项）。

  **`field_simp` 的失败路径**（prover_d 实测，我已复现）：
  对**不等式**用 `field_simp` 报 `error: simp made no progress`（它只对**等式**可靠）。
  多分母不等式的**通用三步**：
  ⑴ 需要通分时先对**等式**用 `field_simp`；
  ⑵ 用 `div_lt_div_iff₀ hb hd`（或 `div_lt_iff₀ hc`）**交叉相乘**去掉分母；
  ⑶ `nlinarith` 收尾。
  未通分前 `nlinarith` / `gcongr` 都看不到分母符号，**目标不动**。

  English:
  Section ⑶ — reciprocals / cross-multiplication / the `field_simp` boundary.

  The raw `#check` output is quoted above; inside it, the two annotations gloss as
  "**taking reciprocals flips the direction** (a ≤ b ↦ 1/b ≤ 1/a)" and "**both denominators must be positive**".

  Use: for `hgeom_of_nonoverlap` in `PhotoLean/Marcus/Reorg.lean` (the Pekar geometric term).

  **The failure path of `field_simp`** (measured by prover_d, reproduced by me):
  applying `field_simp` to an **inequality** reports `error: simp made no progress` (it is reliable only for **equalities**).
  The **general three steps** for an inequality with several denominators:
  ⑴ when a common denominator is needed, first apply `field_simp` to an **equality**;
  ⑵ use `div_lt_div_iff₀ hb hd` (or `div_lt_iff₀ hc`) to **cross-multiply** the denominators away;
  ⑶ finish with `nlinarith`.
  Before the common denominator is cleared, neither `nlinarith` nor `gcongr` can see the signs of the denominators, so **the goal does not move**.
-/

#check one_div_le_one_div_of_le
#check div_lt_div_iff₀
#check div_lt_iff₀

-- 倒数翻转方向
-- English: Reciprocals flip the direction
example {a b : ℝ} (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha h
-- 两个分母都正时交叉相乘
-- English: Cross-multiply when both denominators are positive
example {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) : a / b < c / d ↔ a * d < c * b :=
  div_lt_div_iff₀ hb hd
-- 单分母
-- English: Single denominator
example {a b c : ℝ} (hc : 0 < c) : b / c < a ↔ b < a * c := div_lt_iff₀ hc
-- 三步法实测：交叉相乘后 nlinarith 收尾
-- English: The three-step method, measured: cross-multiply first, then finish with `nlinarith`
example {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) (h : a * d < c * b) : a / b < c / d := by
  rw [div_lt_div_iff₀ hb hd]; exact h
-- `field_simp` 对**等式**可靠（对不等式不可靠，见上）
-- English: `field_simp` is reliable on **equalities** (and unreliable on inequalities, see above)
example {p q : ℝ} (hq : q ≠ 0) (h : p / q = 3) : p = 3 * q := by
  field_simp at h
  linarith

end MarcusApiCast
