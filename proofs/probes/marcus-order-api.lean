/-
  marcus-order-api.lean — mathlib API 探针（Marcus 反转区，B 组 + C 组 + E 组）

  目的
    校准 "除法/序"、"平方/幂单调"、"单调性包装" 三类引理的名字与签名，供
    lemma 1/2/3/5/6/7（barrier 的两支单调性与对称性）使用。

  运行命令（在仓库根目录执行）
    proofs/scripts/lake env lean proofs/probes/marcus-order-api.lean

  本文件为 **正向探针**：所有 #check 与 example 必须全部成功、无 error。
  任何一个 error 即表示 mathlib 名字再次漂移，请交 api_researcher 重新校准。
  已确认 **不存在** / **已废弃** 的名字写在注释里。

  校准基准：mathlib v4.17.0（lean-toolchain = leanprover/lean4:v4.17.0）
  校准日期：2026-09-20 — api_researcher

  English: marcus-order-api.lean — mathlib API probe (Marcus inverted region, groups B + C + E)

  Purpose
    Calibrate the names and signatures of three classes of lemmas — "division / order",
    "square / power monotonicity", "monotonicity wrappers" — for use by
    lemma 1/2/3/5/6/7 (the two branches of monotonicity and the symmetry of the barrier).

  Run command (executed at the repository root)
    proofs/scripts/lake env lean proofs/probes/marcus-order-api.lean

  This file is a **positive probe**: every #check and example must succeed, with no error.
  Any single error means that a mathlib name has drifted again; hand it to api_researcher for recalibration.
  Names confirmed **nonexistent** / **deprecated** are recorded in the comments.

  Calibration baseline: mathlib v4.17.0 (lean-toolchain = leanprover/lean4:v4.17.0)
  Calibration date: 2026-09-20 — api_researcher
-/

import Mathlib

set_option linter.unusedVariables false

/-! ## B 组：除法 / 序

  ⚠️ 已废弃（names drift，仍能用但会 warning，**新代码不要用**）：
    div_lt_iff  → div_lt_iff₀        (deprecated since 2024-10-02)
    lt_div_iff  → lt_div_iff₀        (deprecated since 2024-10-02)
    div_lt_div_right → div_lt_div_iff_of_pos_right (deprecated since 2024-11-12)
  ⚠️ 不存在（**禁止使用**）：
    div_lt_div_iff_of_neg_right, div_lt_div_iff_of_neg_left,
    div_lt_div_of_neg_right, div_lt_div_of_neg_left
  负分母请用 `div_lt_iff_of_neg` / `lt_div_iff_of_neg`，或见下面 L5 的 div_neg 路线。

  English: ## Group B: division / order

  ⚠️ Deprecated (names drift; still usable but emits a warning — **do not use in new code**):
    div_lt_iff  → div_lt_iff₀        (deprecated since 2024-10-02)
    lt_div_iff  → lt_div_iff₀        (deprecated since 2024-10-02)
    div_lt_div_right → div_lt_div_iff_of_pos_right (deprecated since 2024-11-12)
  ⚠️ Nonexistent (**forbidden to use**):
    div_lt_div_iff_of_neg_right, div_lt_div_iff_of_neg_left,
    div_lt_div_of_neg_right, div_lt_div_of_neg_left
  For a negative denominator use `div_lt_iff_of_neg` / `lt_div_iff_of_neg`, or see the div_neg route of L5 below.
-/

-- 正分母（barrier 的 4*lam，在 0 < lam 时为正）
-- English: positive denominator (the barrier's 4*lam, which is positive when 0 < lam)
#check div_lt_div_iff_of_pos_right -- (hc : 0 < c) : a / c < b / c ↔ a < b   ← iff，最短路线
                                   -- English: (hc : 0 < c) : a / c < b / c ↔ a < b   ← iff, the shortest route
#check div_lt_div_of_pos_right     -- (h : a < b) (hc : 0 < c) : a / c < b / c  ← 方向版
                                   -- English: (h : a < b) (hc : 0 < c) : a / c < b / c  ← the direction form
#check div_pos                     -- (ha : 0 < a) (hb : 0 < b) : 0 < a / b
#check div_nonneg                  -- (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b
#check one_div_pos                 -- 0 < 1 / a ↔ 0 < a
#check div_eq_mul_inv              -- (a b : G) : a / b = a * b⁻¹
#check mul_div_assoc               -- (a b c : G) : a * b / c = a * (b / c)
#check neg_div                     -- (a b : R) : -b / a = -(b / a)      ← 注意参数顺序！
                                   -- English: (a b : R) : -b / a = -(b / a)      ← mind the argument order!
#check div_neg                     -- {b : R} (a : R) : a / -b = -(a / b)
#check neg_lt_neg_iff              -- -a < -b ↔ b < a
-- 负分母（0 < lam 的镜像情形，与上面不同名！）
-- English: negative denominator (the mirror case of 0 < lam, named differently from the above!)
#check div_lt_iff_of_neg           -- (hc : c < 0) : b / c < a ↔ b < a * c
#check lt_div_iff_of_neg           -- (hc : c < 0) : a < b / c ↔ b < a * c
#check div_lt_div_right_of_neg     -- (hc : c < 0) : a / c < b / c ↔ b < a  ← **右边方向反直觉！**
                                   -- English: (hc : c < 0) : a / c < b / c ↔ b < a  ← **the right-hand direction is counterintuitive!**
-- ⚠️ 不存在（**禁止使用**）：div_lt_div_iff_of_neg_right, div_lt_div_of_neg_right,
--    div_lt_div_iff_of_neg_left, div_lt_div_of_neg_left
-- English: ⚠️ Nonexistent (**forbidden to use**): div_lt_div_iff_of_neg_right, div_lt_div_of_neg_right,
--    div_lt_div_iff_of_neg_left, div_lt_div_of_neg_left
example {a b c : ℝ} (hc : c < 0) : a / c < b / c ↔ b < a := div_lt_div_right_of_neg hc
-- 非废弃的 iff 版本（替换 div_lt_iff / lt_div_iff）
-- English: the non-deprecated iff versions (replacing div_lt_iff / lt_div_iff)
#check div_lt_iff₀                 -- (hc : 0 < c) : b / c < a ↔ b < a * c
#check lt_div_iff₀                 -- (hc : 0 < c) : a < b / c ↔ a * c < b
-- ⚠️ 同名易混：div_lt_div_iff₀ 是「两个分母」的版本，不是上面的 of_pos_right
-- English: ⚠️ easily confused by name: div_lt_div_iff₀ is the "two denominators" version, not the of_pos_right above
#check div_lt_div_iff₀             -- (hb : 0 < b) (hd : 0 < d) : a / b < c / d ↔ a * d < c * b

/-! ## C 组：平方 / 幂单调

  **从 `0 ≤ a < b` 推出 `a^2 < b^2` 的最省事引理名：**

    (sq_lt_sq₀ ha hb).2 hab        -- sq_lt_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a^2 < b^2 ↔ a < b
    nlinarith                       -- 实测：裸 nlinarith 也能直接证，无需任何 hint

  ⚠️ 不存在（**禁止使用**）：sq_lt_sq_iff
  ⚠️ 已废弃：pow_lt_pow_left → pow_lt_pow_left₀ (since 2024-11-13)
  `sq_lt_sq` 是绝对值版本（`a^2 < b^2 ↔ |a| < |b|`），不是「非负底数」版本；
  非负底数请用 `sq_lt_sq₀`。

  English: ## Group C: square / power monotonicity

  **The most convenient lemma names for deriving `a^2 < b^2` from `0 ≤ a < b`:**

    (sq_lt_sq₀ ha hb).2 hab        -- sq_lt_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a^2 < b^2 ↔ a < b
    nlinarith                       -- measured: bare nlinarith proves it directly, with no hint at all

  ⚠️ Nonexistent (**forbidden to use**): sq_lt_sq_iff
  ⚠️ Deprecated: pow_lt_pow_left → pow_lt_pow_left₀ (since 2024-11-13)
  `sq_lt_sq` is the absolute-value version (`a^2 < b^2 ↔ |a| < |b|`), not the "nonnegative base" version;
  for a nonnegative base use `sq_lt_sq₀`.
-/

#check sq_lt_sq₀            -- (ha : 0 ≤ a) (hb : 0 ≤ b) : a^2 < b^2 ↔ a < b   ← 推荐
                            -- English: (ha : 0 ≤ a) (hb : 0 ≤ b) : a^2 < b^2 ↔ a < b   ← recommended
#check sq_le_sq₀            -- (ha : 0 ≤ a) (hb : 0 ≤ b) : a^2 ≤ b^2 ↔ a ≤ b
#check sq_lt_sq             -- a^2 < b^2 ↔ |a| < |b|
#check sq_le_sq             -- a^2 ≤ b^2 ↔ |a| ≤ |b|
#check sq_lt_sq'            -- (h1 : -b < a) (h2 : a < b) : a^2 < b^2
#check sq_le_sq'            -- (h1 : -b ≤ a) (h2 : a ≤ b) : a^2 ≤ b^2
#check sq_pos_of_ne_zero    -- a ≠ 0 → 0 < a^2
#check sq_nonneg            -- (a : α) : 0 ≤ a^2
#check sq_eq_zero_iff       -- a^2 = 0 ↔ a = 0
#check mul_self_lt_mul_self -- (ha : 0 ≤ a) (hab : a < b) : a * a < b * b  ← 结论是 * 不是 ^
                            -- English: (ha : 0 ≤ a) (hab : a < b) : a * a < b * b  ← the conclusion uses * and not ^
#check mul_self_lt_mul_self_iff -- (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b
#check lt_of_mul_self_lt_mul_self₀ -- (hb : 0 ≤ b) : a * a < b * b → a < b   ← 反向
                                   -- English: (hb : 0 ≤ b) : a * a < b * b → a < b   ← the converse direction
#check pow_lt_pow_left₀     -- (hab : a < b) (ha : 0 ≤ a) : n ≠ 0 → a^n < b^n
#check pow_left_strictMonoOn₀ -- (hn : n ≠ 0) : StrictMonoOn (· ^ n) {a | 0 ≤ a}

-- C-1: 四种等价写法，实测都过
-- English: C-1: four equivalent formulations, all measured to go through
example {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a < b) : a ^ 2 < b ^ 2 :=
  (sq_lt_sq₀ ha hb).2 hab
example {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a < b) : a ^ 2 < b ^ 2 := by nlinarith
example {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : a ^ 2 < b ^ 2 :=
  (sq_lt_sq₀ ha (ha.trans hab.le)).2 hab
example {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : a ^ 2 < b ^ 2 := by
  simpa only [pow_two] using mul_self_lt_mul_self ha hab

/-! ## E 组：单调性包装

  ⚠️ 不存在（**禁止使用**）：strictMonoOn_iff（在 Set 命名空间下也不叫这个）；
     Set 命名空间下的真名是 `Set.strictMonoOn_iff_strictMono`（是「子类型上的
     StrictMono」，不是「∀ 形式」，对 barrier 这种 Ici/Iic 上的单调没用）。
  ✅ 实用的是：`StrictMonoOn.lt_iff_lt` / `StrictAntiOn.lt_iff_lt`（iff 版），
     以及现成的 `strictMonoOn_mul_self`、`pow_left_strictMonoOn₀`。
  ⚠️ `StrictMonoOn.const_mul` / `StrictMonoOn.div_const` 在 v4.17 **不可用**
     （点记法报 invalid field notation）—— 复合要手写 intro a ha b hb hab。

  English: ## Group E: monotonicity wrappers

  ⚠️ Nonexistent (**forbidden to use**): strictMonoOn_iff (nor is it called that under the Set namespace);
     the real name under the Set namespace is `Set.strictMonoOn_iff_strictMono` (it is "StrictMono on the
     subtype", not the "∀ form", so it is useless for the monotonicity of the barrier on Ici/Iic).
  ✅ The practical ones are: `StrictMonoOn.lt_iff_lt` / `StrictAntiOn.lt_iff_lt` (the iff versions),
     plus the ready-made `strictMonoOn_mul_self` and `pow_left_strictMonoOn₀`.
  ⚠️ `StrictMonoOn.const_mul` / `StrictMonoOn.div_const` are **unavailable** in v4.17
     (dot notation reports invalid field notation) — for a composite, write intro a ha b hb hab by hand.
-/

#check StrictMonoOn                    -- (f : α → β) (s : Set α) : Prop
#check StrictAntiOn                    -- (f : α → β) (s : Set α) : Prop
#check MonotoneOn                      -- (f : α → β) (s : Set α) : Prop
#check StrictMonoOn.lt_iff_lt          -- (hf) (ha : a ∈ s) (hb : b ∈ s) : f a < f b ↔ a < b
#check StrictAntiOn.lt_iff_lt          -- (hf) (ha : a ∈ s) (hb : b ∈ s) : f a < f b ↔ b < a
#check Set.strictMonoOn_iff_strictMono -- StrictMonoOn f s ↔ StrictMono fun a : s => f a
#check strictMonoOn_mul_self           -- StrictMonoOn (fun x => x * x) {x | 0 ≤ x}
#check pow_left_strictMonoOn₀          -- (hn : n ≠ 0) : StrictMonoOn (· ^ n) {a | 0 ≤ a}

-- E-1: 复用 StrictMonoOn.lt_iff_lt
-- English: E-1: reusing StrictMonoOn.lt_iff_lt
example {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a * a < b * b ↔ a < b :=
  strictMonoOn_mul_self.lt_iff_lt ha hb

/-- E-2: barrier 在 `Set.Ici lam` 上严格单增（lam > 0）—— lemma 2 的打包形式

English: E-2: the barrier is strictly increasing on `Set.Ici lam` (lam > 0) — the packaged form of lemma 2 -/
theorem barrier_strictMonoOn_Ici {lam : ℝ} (hlam : 0 < lam) :
    StrictMonoOn (fun x => (lam - x) ^ 2 / (4 * lam)) (Set.Ici lam) := by
  intro a ha b hb hab
  rw [Set.mem_Ici] at ha hb            -- ⚠️ 必须显式展开，linarith 不认 `a ∈ Set.Ici lam`
                                       -- English: ⚠️ must be unfolded explicitly; linarith does not recognize `a ∈ Set.Ici lam`
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith

/-- E-3: barrier 在 `Set.Iic lam` 上严格单减（lam > 0）—— lemma 3 的打包形式

English: E-3: the barrier is strictly decreasing on `Set.Iic lam` (lam > 0) — the packaged form of lemma 3 -/
theorem barrier_strictAntiOn_Iic {lam : ℝ} (hlam : 0 < lam) :
    StrictAntiOn (fun x => (lam - x) ^ 2 / (4 * lam)) (Set.Iic lam) := by
  intro a ha b hb hab
  rw [Set.mem_Iic] at ha hb
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith
