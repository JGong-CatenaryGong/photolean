/-
  marcus-api-closeout.lean — API-NOTES 收尾追加的复核探针（M2/M3/M4a/M5a 实测归档）

  目的
    独立复核各交付者在 M2/M3/M4a/M5a 期间报出的一批名字与坑，**不照抄**：
    A 组新增可用名字（含 `≤` 版与 `rate_ratio` 的乘除引理）；
    B 组禁止清单增补（`div_lt_div_of_neg_right`、`sq_pos_of_ne_zero` 隐式参数）；
    C 组工具事实（`decide` 对 ℚ 的可靠域、`theories/Marcus/plan.md` §8.2 三处示例纠正、Zone 构造子判定）。

  运行命令（在仓库根目录执行）
    proofs/scripts/lake env lean theories/Marcus/probes/marcus-api-closeout.lean

  本文件为 **正向探针**：必须 0 error / 0 warning。
  **失败**的写法（"expect FAIL"）只出现在注释里，附原始报错。

  校准基准：mathlib v4.17.0（lean-toolchain = leanprover/lean4:v4.17.0）
  校准日期：2026-09-20 — api_researcher

  English: marcus-api-closeout.lean — review probes appended at the close-out of API-NOTES
  (measured archive for M2/M3/M4a/M5a)

  Purpose
    Independently re-check a batch of names and pitfalls reported by the various contributors
    during M2/M3/M4a/M5a, **without copying them**:
    Group A: newly available names (including the `≤` versions and the multiplication/division
    lemma for `rate_ratio`);
    Group B: additions to the forbidden list (`div_lt_div_of_neg_right`, the implicit argument of
    `sq_pos_of_ne_zero`);
    Group C: tooling facts (the reliable domain of `decide` over ℚ, the three corrections to the
    examples in `theories/Marcus/plan.md` §8.2, and constructor discrimination for Zone).

  Run command (execute in the repository root)
    proofs/scripts/lake env lean theories/Marcus/probes/marcus-api-closeout.lean

  This file is a **positive probe**: it must produce 0 error / 0 warning.
  **Failing** spellings ("expect FAIL") appear only in comments, together with the original error.

  Calibration baseline: mathlib v4.17.0 (lean-toolchain = leanprover/lean4:v4.17.0)
  Calibration date: 2026-09-20 — api_researcher
-/

import Mathlib

set_option linter.unusedVariables false

namespace MarcusApiCloseout

/-! ## A 组 — 新增「可用」名字

  `#check` 原始输出（完整）：

  ```
  Real.exp_le_exp {x y : ℝ} : Real.exp x ≤ Real.exp y ↔ x ≤ y
  Real.exp_le_exp_of_le {x y : ℝ} (h : x ≤ y) : Real.exp x ≤ Real.exp y
  div_le_div_of_nonneg_right {G₀} [GroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀]
    [PosMulReflectLT G₀] {a b c : G₀} [MulPosMono G₀] (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c
  mul_le_mul_of_nonneg_left {α} [Mul α] [Zero α] [Preorder α] [PosMulMono α] (h : b ≤ c)
    (a0 : 0 ≤ a) : a * b ≤ a * c
  mul_div_mul_left {G₀} [CommGroupWithZero G₀] {c : G₀} (a b : G₀) (hc : c ≠ 0) :
    c * a / (c * b) = a / b
  Real.exp_sub (x y : ℝ) : Real.exp (x - y) = Real.exp x / Real.exp y
  pow_lt_pow_left₀ {M₀} [MonoidWithZero M₀] [PartialOrder M₀] {a b : M₀} [ZeroLEOneClass M₀]
    [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hab : a < b) (ha : 0 ≤ a) {n : ℕ} :
    n ≠ 0 → a ^ n < b ^ n
  sq_lt_sq₀ {M₀} [MonoidWithZero M₀] [LinearOrder M₀] [ZeroLEOneClass M₀] [PosMulStrictMono M₀]
    [MulPosStrictMono M₀] {a b : M₀} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 ↔ a < b
  ```

  ⚠️ `Real.exp_le_exp_iff` **不存在**（`Real.exp_le_exp` 本身就是 iff）。

  English: ## Group A — newly available "usable" names

  `#check` raw output (complete) — see the code block reproduced verbatim above:

  ⚠️ `Real.exp_le_exp_iff` **does not exist** (`Real.exp_le_exp` is itself an iff).
-/

#check Real.exp_le_exp
#check Real.exp_le_exp_of_le
#check div_le_div_of_nonneg_right
#check mul_le_mul_of_nonneg_left
#check mul_div_mul_left
#check Real.exp_sub
#check pow_lt_pow_left₀
#check sq_lt_sq₀

noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

noncomputable def rate (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(barrier lam x) / (kB * T))

-- A-1: `Real.exp_le_exp` 是 iff → `≤` 版峰值定理用它
-- English: A-1: `Real.exp_le_exp` is an iff → the `≤` version of the peak theorem uses it
example {x y : ℝ} (h : x ≤ y) : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr h
example {x y : ℝ} (h : Real.exp x ≤ Real.exp y) : x ≤ y := Real.exp_le_exp.mp h
example {x y : ℝ} (h : x ≤ y) : Real.exp x ≤ Real.exp y := Real.exp_le_exp_of_le h

-- A-2: M3 的 `rate_peak_at_lam`（`≤` 版峰值）实测体 —— 用到全部三个 `≤` 引理
-- English: A-2: the measured proof body of M3's `rate_peak_at_lam` (the `≤` version of the
-- peak) — it uses all three `≤` lemmas
theorem rate_peak_at_lam {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    (x : ℝ) : rate A lam kB T x ≤ rate A lam kB T lam := by
  unfold rate
  apply mul_le_mul_of_nonneg_left _ hA.le                  -- A-2a: 乘非负数
                                                           -- English: A-2a: multiply by a nonnegative number
  rw [Real.exp_le_exp]                                     -- A-2b: 吃掉 exp（iff，正向）
                                                           -- English: A-2b: eliminate the exp (an iff, forward direction)
  exact div_le_div_of_nonneg_right (by linarith [barrier_min_at_lam hlam x]) hkT.le  -- A-2c
where
  barrier_min_at_lam {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : barrier lam lam ≤ barrier lam x := by
    unfold barrier
    rw [div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
    nlinarith [sq_nonneg (lam - x)]

-- A-3: `Real.exp_sub` 的**方向** —— 把「exp 相除」变「exp 差」必须用 `← Real.exp_sub`
-- English: A-3: the **direction** of `Real.exp_sub` — turning "a quotient of exps" into "a
-- difference of exps" requires `← Real.exp_sub`
example (a b : ℝ) : Real.exp a / Real.exp b = Real.exp (a - b) := (Real.exp_sub a b).symm
example (a b : ℝ) : Real.exp (a - b) = Real.exp a / Real.exp b := Real.exp_sub a b
-- A-4: `mul_div_mul_left` 是 M3 `rate_ratio` 的关键一步（约掉分子分母的 A）
-- English: A-4: `mul_div_mul_left` is a key step for M3's `rate_ratio` (it cancels the A in
-- numerator and denominator)
example {A y x : ℝ} (hA : A ≠ 0) : A * y / (A * x) = y / x := mul_div_mul_left y x hA
-- A-5: `rate_ratio` 实测体（用到 mul_div_mul_left + ← Real.exp_sub）
-- English: A-5: the measured proof body of `rate_ratio` (uses mul_div_mul_left + ← Real.exp_sub)
theorem rate_ratio {A lam kB T : ℝ} (hA : A ≠ 0) (hkT : kB * T ≠ 0) (x y : ℝ) :
    rate A lam kB T y / rate A lam kB T x
      = Real.exp ((barrier lam x - barrier lam y) / (kB * T)) := by
  unfold rate
  rw [mul_div_mul_left _ _ hA, ← Real.exp_sub]
  congr 1
  field_simp
  ring

/-! ## B 组 — 禁止清单增补

  ⚠️ **不存在**：`div_lt_div_of_neg_right`（`unknown identifier`）——
     负除数下用 `div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a`
     （**iff，右边是 `b < a`，顺序反转**，M2 两支方向反全靠它）。
     另 `Real.exp_le_exp_iff`（`unknown constant`）、`div_lt_div_iff_of_neg_right` 也不存在。

  ⚠️ **`sq_pos_of_ne_zero` 的 `a` 是隐式参数**：
     `@sq_pos_of_ne_zero : ∀ {R} [LinearOrderedSemiring R] [ExistsAddOfLE R] {a : R}, a ≠ 0 → 0 < a ^ 2`
     正确 `sq_pos_of_ne_zero hdq`；写成 `sq_pos_of_ne_zero dq hdq` 报
     `application type mismatch: dq has type ℝ but is expected to have type ?m ≠ 0`。
     （本条同时订正 `theories/Marcus/plan.md` §7.2 的旧提示，已由 lead 修改。）

  English: ## Group B — additions to the forbidden list

  ⚠️ **Do not exist**: `div_lt_div_of_neg_right` (`unknown identifier`) —
     with a negative divisor use `div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a`
     (**an iff, and the right-hand side is `b < a`, so the order is reversed**; both directions of
     the M2 branches rely on it).
     Also nonexistent: `Real.exp_le_exp_iff` (`unknown constant`) and `div_lt_div_iff_of_neg_right`.

  ⚠️ **The `a` of `sq_pos_of_ne_zero` is an implicit argument**:
     `@sq_pos_of_ne_zero : ∀ {R} [LinearOrderedSemiring R] [ExistsAddOfLE R] {a : R}, a ≠ 0 → 0 < a ^ 2`
     Correct: `sq_pos_of_ne_zero hdq`; writing `sq_pos_of_ne_zero dq hdq` reports
     `application type mismatch: dq has type ℝ but is expected to have type ?m ≠ 0`.
     (This entry also corrects the old hint in `theories/Marcus/plan.md` §7.2, which the lead has already edited.)
-/

#check div_lt_div_right_of_neg
#check @sq_pos_of_ne_zero
example {a b c : ℝ} (hc : c < 0) : a / c < b / c ↔ b < a := div_lt_div_right_of_neg hc
example {dq : ℝ} (hdq : dq ≠ 0) : 0 < dq ^ 2 := sq_pos_of_ne_zero hdq

/-! ## C 组 — 工具事实

  ### C-1 `by decide` 对 ℚ 的可靠域

  实测：**整数/无除法字面量**（含负整数）可算；**含除法或十进制**一律卡在
  `Rat.instDecidableLt` → `Int.decNonneg`，报
  `'Decidable' instance … did not reduce to 'isTrue' or 'isFalse'`。
  ⇒ 含除法/十进制的判定证据必须走 `norm_num [zoneQ]`。

  ### C-2 `theories/Marcus/plan.md` §8.2 三处旧示例纠正（M5a 交付者发现，已由 lead 改 plan）

  (1) `rw [← zoneQ_eq_zone]` 的方向**取决于目标里出现的是哪一边**：
      `←` 的模式是 `zone ↑?lam ↑?x`；§8.2 的目标里是 `zoneQ …`，所以必须**正向**
      `rw [zoneQ_eq_zone]`。（若目标里是 `zone ↑lam ↑x`，则 `←` 才对 —— 两种都存在，见下。）
  (2) **cast 字面量 ≠ `OfNat` 字面量**：`((1:ℚ):ℝ)` 与 `(1:ℝ)` 不是 defeq。
      目标含 `InvertedRegion (1:ℝ) 3` 时，`exact h`（`h : ↑1 < ↑3`）报
      `type mismatch: h has type ↑1 < ↑3 but is expected to have type InvertedRegion 1 3`。
  (3) **`rw` 不走 defeq**：`rw [← zoneQ_inverted_iff]` 不会展开 `def InvertedRegion`，
      报 `did not find instance of the pattern ↑?lam < ↑?x`；
      而 `exact (…).mp h` 走 defeq、无此限制（或先 `show`）。

  English: ## Group C — tooling facts

  ### C-1 The reliable domain of `by decide` over ℚ

  Measured: **integer / division-free literals** (including negative integers) reduce;
  **anything containing a division or a decimal** always gets stuck at
  `Rat.instDecidableLt` → `Int.decNonneg`, reporting
  `'Decidable' instance … did not reduce to 'isTrue' or 'isFalse'`.
  ⇒ Decidability evidence involving divisions / decimals must go through `norm_num [zoneQ]`.

  ### C-2 Corrections to three old examples in `theories/Marcus/plan.md` §8.2 (found by the M5a contributor; the lead has already fixed the plan)

  (1) The direction of `rw [← zoneQ_eq_zone]` **depends on which side occurs in the goal**:
      the `←` pattern is `zone ↑?lam ↑?x`; the goals in §8.2 contain `zoneQ …`, so the **forward**
      direction `rw [zoneQ_eq_zone]` is required. (If the goal contains `zone ↑lam ↑x`, then `←`
      is the right one — both cases occur, see below.)
  (2) **A cast literal ≠ an `OfNat` literal**: `((1:ℚ):ℝ)` and `(1:ℝ)` are not defeq.
      When the goal contains `InvertedRegion (1:ℝ) 3`, `exact h` (with `h : ↑1 < ↑3`) reports
      `type mismatch: h has type ↑1 < ↑3 but is expected to have type InvertedRegion 1 3`.
  (3) **`rw` does not use defeq**: `rw [← zoneQ_inverted_iff]` will not unfold `def InvertedRegion`,
      and reports `did not find instance of the pattern ↑?lam < ↑?x`;
      whereas `exact (…).mp h` does go through defeq and has no such restriction (or use `show` first).
-/

inductive Zone where
  | normal
  | barrierless
  | inverted
  deriving DecidableEq, Repr

noncomputable def zone (lam x : ℝ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

def zoneQ (lam x : ℚ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

def InvertedRegion (lam x : ℝ) : Prop := lam < x

-- C-1：整数（含负整数）→ `decide` ✅
-- English: C-1: integers (including negative integers) → `decide` ✅
example : zoneQ (1 : ℚ) 3 = Zone.inverted := by decide
example : zoneQ (1 : ℚ) (-3) = Zone.normal := by decide
example : zoneQ (1 : ℚ) 1 = Zone.barrierless := by decide
example : zoneQ (1 : ℚ) 0 = Zone.normal := by decide
-- C-1：含除法 / 十进制 → `decide` ❌（见下注释），必须 `norm_num [zoneQ]` ✅
-- English: C-1: with a division / a decimal → `decide` ❌ (see the comment below);
-- `norm_num [zoneQ]` is required ✅
--   example : zoneQ (1 : ℚ) (0.5 : ℚ) = Zone.normal := by decide
--   -- error: tactic 'decide' failed … did not reduce to 'isTrue' or 'isFalse'
--   --        （卡点 Rat.instDecidableLt → Int.decNonneg）
--   --        English: (the blocker is Rat.instDecidableLt → Int.decNonneg)
example : zoneQ (1 : ℚ) (0.5 : ℚ) = Zone.normal := by norm_num [zoneQ]
example : zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by norm_num [zoneQ]
example : zoneQ (1 : ℚ) (6 / 8) = Zone.normal := by norm_num [zoneQ]

-- M5a 的语句依赖（复核用）
-- English: statement dependencies of M5a (for re-checking)
theorem zone_eq_inverted_iff (lam x : ℝ) : zone lam x = Zone.inverted ↔ InvertedRegion lam x := by
  by_cases h : x < lam
  · unfold zone InvertedRegion; rw [if_pos h]; simp [not_lt.mpr h.le]
  · unfold zone InvertedRegion; rw [if_neg h]
    by_cases h2 : x = lam
    · rw [if_pos h2]; simp [h2]
    · rw [if_neg h2]
      have hlt : lam < x := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h2)
      simp [h, hlt]

theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ) := by
  unfold zoneQ zone
  simp only [Rat.cast_lt, Rat.cast_inj]

theorem zoneQ_inverted_iff (lam x : ℚ) : zoneQ lam x = Zone.inverted ↔ (lam : ℝ) < (x : ℝ) := by
  rw [zoneQ_eq_zone, zone_eq_inverted_iff]
  rfl

-- C-2(1) ✅ 正向：目标是 `zoneQ …` 时用正向
-- English: C-2(1) ✅ forward: use the forward direction when the goal is `zoneQ …`
example {lam x : ℚ} (h : zone (lam : ℝ) (x : ℝ) = Zone.inverted) : zoneQ lam x = Zone.inverted := by
  rw [zoneQ_eq_zone]; exact h
-- C-2(1) ✅ 反向：目标是 `zone ↑lam ↑x` 时用 `←`（说明"方向反了"是**分情形**的）
-- English: C-2(1) ✅ backward: use `←` when the goal is `zone ↑lam ↑x` (this shows that
-- "the direction is reversed" is **case-dependent**)
example {lam x : ℚ} (h : zoneQ lam x = Zone.inverted) : zone (lam : ℝ) (x : ℝ) = Zone.inverted := by
  rw [← zoneQ_eq_zone]; exact h

-- C-2(2) ❌ `exact h` 因 cast/OfNat 字面量不等而 type mismatch：
-- English: C-2(2) ❌ `exact h` gives a type mismatch because the cast / OfNat literals differ:
--   example (h : ((1 : ℚ) : ℝ) < ((3 : ℚ) : ℝ)) : InvertedRegion (1 : ℝ) 3 := h
--   -- error: type mismatch / h has type ↑1 < ↑3 but is expected to have type InvertedRegion 1 3
-- C-2(2) ✅ 两条出路：显式写 cast 字面量，或 `norm_num [InvertedRegion]`
-- English: C-2(2) ✅ two ways out: write the cast literal explicitly, or use
-- `norm_num [InvertedRegion]`
example (h : ((1 : ℚ) : ℝ) < ((3 : ℚ) : ℝ)) :
    InvertedRegion ((1 : ℚ) : ℝ) ((3 : ℚ) : ℝ) := h
example : InvertedRegion (1 : ℝ) 3 := by norm_num [InvertedRegion]

-- C-2(3) ❌ `rw` 不展开 def `InvertedRegion`：
-- English: C-2(3) ❌ `rw` does not unfold the def `InvertedRegion`:
--   example {lam x : ℚ} (h : zoneQ lam x = Zone.inverted) : InvertedRegion (lam : ℝ) (x : ℝ) := by
--     rw [← zoneQ_inverted_iff]; exact h
--   -- error: tactic 'rewrite' failed, did not find instance of the pattern ↑?lam < ↑?x
-- C-2(3) ✅ `exact (…).mp` 走 defeq
-- English: C-2(3) ✅ `exact (…).mp` goes through defeq
example {lam x : ℚ} (h : zoneQ lam x = Zone.inverted) : InvertedRegion (lam : ℝ) (x : ℝ) :=
  (zoneQ_inverted_iff lam x).mp h
-- C-2(3) ✅ 或先 `show`
-- English: C-2(3) ✅ or use `show` first
example {lam x : ℚ} (h : zoneQ lam x = Zone.inverted) : InvertedRegion (lam : ℝ) (x : ℝ) := by
  show (lam : ℝ) < (x : ℝ)
  exact (zoneQ_inverted_iff lam x).mp h

-- C-3：`Zone` 构造子互异可直接 `by decide`（6 组全通过）
-- English: C-3: distinctness of the `Zone` constructors is directly provable by `by decide`
-- (all 6 pairs pass)
example : Zone.normal ≠ Zone.barrierless := by decide
example : Zone.normal ≠ Zone.inverted := by decide
example : Zone.barrierless ≠ Zone.inverted := by decide
example : Zone.inverted ≠ Zone.normal := by decide
example : Zone.barrierless ≠ Zone.normal := by decide
example : Zone.inverted ≠ Zone.barrierless := by decide

end MarcusApiCloseout

/-! ## D 组 — ⚠️「未使用的前提」≠「可推出的前提」（M2 verifier 发现 A）

  本日志曾把 `barrier_antitone_of_pos` 的 `h₁ : 0 ≤ x₁` 说成"可由 `h₃ : x₂ ≤ lam`
  与 `h₂ : x₁ < x₂` **推出**"。**这是假命题**（verifier 给出内核反例，我已独立复现）。
  正确表述是"**证明未使用（unused）**"。二者语义不同：后者会被当成可复用的推理依据。

  下面两条把区别钉成机器检查的事实：`D-1` 证明前提为假的情形仍满足其余全部前提
  （⇒ 不可推出）；`D-2` 证明去掉该前提定理仍成立（⇒ 未使用）。

  English: ## Group D — ⚠️ "an unused hypothesis" ≠ "a hypothesis that can be derived"
  (finding A of the M2 verifier)

  This log once stated that `h₁ : 0 ≤ x₁` of `barrier_antitone_of_pos` "**can be derived** from
  `h₃ : x₂ ≤ lam` and `h₂ : x₁ < x₂`". **That is a false proposition** (the verifier produced a
  kernel counterexample, which I have independently reproduced).
  The correct wording is "**the proof does not use it (unused)**". The two differ in meaning:
  the former would be taken as a reusable basis for inference.

  The two items below pin the difference down as machine-checked facts: `D-1` shows a situation in
  which the hypothesis is false while all the other hypotheses hold (⇒ not derivable);
  `D-2` shows that the theorem still holds after that hypothesis is removed (⇒ unused).
-/

namespace MarcusApiCloseout

noncomputable def barrier' (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

-- D-1（内核反例）`0 ≤ x₁` **不可由其余前提推出**：lam=1, x₁=-5, x₂=-4
-- English: D-1 (kernel counterexample): `0 ≤ x₁` **cannot be derived from the remaining
-- hypotheses**: lam=1, x₁=-5, x₂=-4
example : ¬ (∀ (lam x₁ x₂ : ℝ), 0 < lam → x₁ < x₂ → x₂ ≤ lam → 0 ≤ x₁) := by
  intro h
  have := h 1 (-5) (-4) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

-- D-2（未使用的实证）去掉 `h₁`，`barrier_antitone_of_pos` 照样成立
-- English: D-2 (evidence that it is unused): removing `h₁`, `barrier_antitone_of_pos` still
-- holds
theorem barrier_antitone_of_pos_no_h1 {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) : barrier' lam x₂ < barrier' lam x₁ := by
  unfold barrier'
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith

end MarcusApiCloseout
