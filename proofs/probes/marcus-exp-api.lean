/-
  marcus-exp-api.lean — mathlib API 探针（Marcus 反转区，A 组 + D 组）

  目的
    校准 "exp 层" 与 "乘法/序" 两类引理的名字与签名，供 lemma 4
    （rate 单调性：barrier x < barrier y → rate y < rate x）使用。

  运行命令（在仓库根目录执行）
    proofs/scripts/lake env lean proofs/probes/marcus-exp-api.lean

  本文件为 **正向探针**：所有 #check 与 example 必须全部成功、无 error。
  任何一个 error 即表示 mathlib 名字再次漂移，请交 api_researcher 重新校准。
  已确认 **不存在** 的名字写在 A 组 / D 组注释里（不要写成 #check，否则本文件不编译）。

  校准基准：mathlib v4.17.0（lean-toolchain = leanprover/lean4:v4.17.0）
  校准日期：2026-09-20 — api_researcher

  English: marcus-exp-api.lean — mathlib API probe (Marcus inverted region, group A + group D)

  Purpose
    Calibrate the names and signatures of two families of lemmas — the "exp layer" and
    "multiplication / order" — for use by lemma 4
    (rate monotonicity: barrier x < barrier y → rate y < rate x).

  Run command (execute from the repository root)
    proofs/scripts/lake env lean proofs/probes/marcus-exp-api.lean

  This file is a **positive probe**: every #check and example must succeed, with no error.
  A single error means the mathlib names have drifted again; hand it to api_researcher for recalibration.
  Names confirmed **not to exist** are written in the group A / group D comments (do not write
  them as #check, or this file will not compile).

  Calibration baseline: mathlib v4.17.0 (lean-toolchain = leanprover/lean4:v4.17.0)
  Calibration date: 2026-09-20 — api_researcher
-/

import Mathlib

/-! ## A 组：Real.exp 层

  #check 清单（全部存在，见 API-NOTES.md 原始输出）：
    Real.exp_lt_exp, Real.exp_le_exp, Real.exp_pos, Real.exp_nonneg, Real.exp_neg,
    Real.exp_sub, Real.exp_add, Real.exp_zero, Real.exp_strictMono, Real.exp_monotone

  ⚠️ 不存在（**禁止使用**）：
    Real.exp_lt_exp_iff   -- unknown constant
    Real.exp_le_exp_iff   -- unknown constant
  Real.exp_lt_exp 本身就是 `↔`（iff），不要再找 *_iff 版本。

  English: ## Group A: the Real.exp layer

  #check list (all exist; see the raw output in API-NOTES.md):
    Real.exp_lt_exp, Real.exp_le_exp, Real.exp_pos, Real.exp_nonneg, Real.exp_neg,
    Real.exp_sub, Real.exp_add, Real.exp_zero, Real.exp_strictMono, Real.exp_monotone

  ⚠️ Do not exist (**forbidden to use**):
    Real.exp_lt_exp_iff   -- unknown constant
    Real.exp_le_exp_iff   -- unknown constant
  Real.exp_lt_exp is itself an `↔` (iff); do not look for a *_iff version.
-/

#check Real.exp_lt_exp    -- {x y : ℝ} : Real.exp x < Real.exp y ↔ x < y   ← 是 iff！
-- English: {x y : ℝ} : Real.exp x < Real.exp y ↔ x < y   ← this is an iff!
#check Real.exp_le_exp    -- {x y : ℝ} : Real.exp x ≤ Real.exp y ↔ x ≤ y   ← 是 iff！
-- English: {x y : ℝ} : Real.exp x ≤ Real.exp y ↔ x ≤ y   ← this is an iff!
#check Real.exp_pos       -- (x : ℝ) : 0 < Real.exp x
#check Real.exp_nonneg    -- (x : ℝ) : 0 ≤ Real.exp x
#check Real.exp_neg       -- (x : ℝ) : Real.exp (-x) = (Real.exp x)⁻¹
#check Real.exp_sub       -- (x y : ℝ) : Real.exp (x - y) = Real.exp x / Real.exp y
#check Real.exp_add       -- (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y
#check Real.exp_zero      -- Real.exp 0 = 1
#check Real.exp_strictMono -- StrictMono Real.exp
#check Real.exp_monotone   -- Monotone Real.exp

-- A-1: `Real.exp_lt_exp` 的两个方向都能用
-- English: A-1: both directions of `Real.exp_lt_exp` can be used
example {x y : ℝ} (h : x < y) : Real.exp x < Real.exp y := Real.exp_lt_exp.mpr h
example {x y : ℝ} (h : Real.exp x < Real.exp y) : x < y := Real.exp_lt_exp.mp h
-- A-2: 严格单调包装也可用（两种写法等价）
-- English: A-2: the strict-monotonicity wrapper can also be used (the two spellings are equivalent)
example {x y : ℝ} (h : x < y) : Real.exp x < Real.exp y := Real.exp_strictMono h
example {x y : ℝ} (h : x < y) : Real.exp x < Real.exp y := Real.exp_lt_exp.2 h
-- A-3: exp_pos 可直接喂给 one_div_pos / div_lt_div_of_pos_right / mul_lt_mul_of_pos_left
-- English: A-3: exp_pos can be fed directly to one_div_pos / div_lt_div_of_pos_right / mul_lt_mul_of_pos_left
example (x : ℝ) : 0 < 1 / Real.exp x := one_div_pos.mpr (Real.exp_pos x)
example (x : ℝ) : 0 < 1 / Real.exp x := by positivity
example {c u v : ℝ} (hc : 0 < c) (h : u < v) : u / c < v / c := div_lt_div_of_pos_right h hc
example {u v c : ℝ} (h : u < v) : u / Real.exp c < v / Real.exp c :=
  div_lt_div_of_pos_right h (Real.exp_pos c)

/-! ## D 组：乘法 / 序

English: ## Group D: multiplication / order
-/

#check mul_lt_mul_of_pos_left  -- (bc : b < c) (a0 : 0 < a) : a * b < a * c
#check mul_lt_mul_of_pos_right -- (bc : b < c) (a0 : 0 < a) : b * a < c * a
#check mul_pos                 -- (ha : 0 < a) (hb : 0 < b) : 0 < a * b
#check mul_nonneg              -- (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b
#check mul_lt_mul₀             -- (hab : a < b) (hcd : c < d) : a * c < b * d

-- D-1: lemma 4 的尾段 — 乘正数保序
-- English: D-1: the tail end of lemma 4 — multiplying by a positive number preserves the order
example {A u v : ℝ} (hA : 0 < A) (h : u < v) : A * u < A * v := mul_lt_mul_of_pos_left h hA
-- D-2: 不用现成引理也可以（裸 `linarith` 不行，见 API-NOTES 记录）
-- English: D-2: it also works without a ready-made lemma (bare `linarith` does not work; see the API-NOTES record)
example {A u v : ℝ} (hA : 0 < A) (h : u < v) : A * u < A * v := by nlinarith

-- D-3: ⚠️ 从正积里提取因子 — **left/right 极易写反**
--      `rate A lam kB T x = A * Real.exp (…)`，正的因子 A 在**左**，exp 在**右**。
--      要从 `0 < A * exp u` 得 `0 < A`，必须用 `pos_of_mul_pos_left`（靠右因子的非负性）。
--      实测：用 `pos_of_mul_pos_right` 会报 application type mismatch（它的结论是 `0 < b`）。
-- English: D-3: ⚠️ extracting a factor from a positive product — **left/right are very easy to swap**
-- English: `rate A lam kB T x = A * Real.exp (…)`: the positive factor A is on the **left**, exp on the **right**.
-- English: To get `0 < A` from `0 < A * exp u`, use `pos_of_mul_pos_left` (needs nonnegativity of the right factor).
-- English: Measured: `pos_of_mul_pos_right` gives an application type mismatch (its conclusion is `0 < b`).
#check pos_of_mul_pos_left   -- (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a   ← 取左因子
-- English: (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a   ← extracts the left factor
#check pos_of_mul_pos_right  -- (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b   ← 取右因子
-- English: (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b   ← extracts the right factor
example {A u : ℝ} (hA : 0 < A) : 0 < A * Real.exp u := mul_pos hA (Real.exp_pos u)
example {A u : ℝ} (h : 0 < A * Real.exp u) : 0 < A :=
  pos_of_mul_pos_left h (Real.exp_pos u).le

-- D-4: 乘负数翻转序（M4a 拉伸目标 `inverted_descriptor_holds_of_neg` 用，A < 0）
--      ⚠️ 实测签名（与直觉的参数顺序不同）：`(h : b < a) (hc : c < 0) : c * a < c * b`
-- English: D-4: multiplying by a negative number reverses the order (used by the M4a stretch
-- English: target `inverted_descriptor_holds_of_neg`, A < 0)
-- English: ⚠️ measured signature (argument order differs from intuition): `(h : b < a) (hc : c < 0) : c * a < c * b`
#check mul_lt_mul_of_neg_left  -- (h : b < a) (hc : c < 0) : c * a < c * b
example {A u v : ℝ} (hA : A < 0) (h : u < v) : A * v < A * u := mul_lt_mul_of_neg_left h hA

/-! ## 核心：lemma 4（rate 单调性）实测骨架

  目标形态：`barrier lam x < barrier lam y → rate A lam kB T y < rate A lam kB T x`
  链条：取负 (linarith) → 除以正数 (div_lt_div_of_pos_right) → exp 严格单调
        (Real.exp_lt_exp.mpr) → 乘正数 (mul_lt_mul_of_pos_left)

  English: ## Core: measured skeleton of lemma 4 (rate monotonicity)

  Target shape: `barrier lam x < barrier lam y → rate A lam kB T y < rate A lam kB T x`
  Chain: negate (linarith) → divide by a positive number (div_lt_div_of_pos_right) → exp strict
         monotonicity (Real.exp_lt_exp.mpr) → multiply by a positive number (mul_lt_mul_of_pos_left)
-/
noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)
noncomputable def rate (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(barrier lam x) / (kB * T))

-- L4 骨架（最短，2 行）
-- English: L4 skeleton (shortest, 2 lines)
theorem L4_skeleton {A lam kB T x y : ℝ} (hA : 0 < A) (hkT : 0 < kB * T)
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  unfold rate
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (div_lt_div_of_pos_right (by linarith) hkT)) hA

-- L4 骨架（可读版，逐步）
-- English: L4 skeleton (readable version, step by step)
theorem L4_stepwise {A lam kB T x y : ℝ} (hA : 0 < A) (hkT : 0 < kB * T)
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  unfold rate
  apply mul_lt_mul_of_pos_left _ hA          -- 乘正数：A * (…) < A * (…)
  -- English: multiply by a positive number: A * (…) < A * (…)
  rw [Real.exp_lt_exp]                        -- 吃掉 exp：x < y ↔ exp x < exp y
  -- English: eliminate the exp: x < y ↔ exp x < exp y
  exact div_lt_div_of_pos_right (by linarith) hkT  -- 除以正数；取负方向由 linarith 翻转
  -- English: divide by a positive number; the direction flip from negating is handled by linarith
