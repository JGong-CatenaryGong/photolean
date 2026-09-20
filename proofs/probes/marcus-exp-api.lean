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
-/

#check Real.exp_lt_exp    -- {x y : ℝ} : Real.exp x < Real.exp y ↔ x < y   ← 是 iff！
#check Real.exp_le_exp    -- {x y : ℝ} : Real.exp x ≤ Real.exp y ↔ x ≤ y   ← 是 iff！
#check Real.exp_pos       -- (x : ℝ) : 0 < Real.exp x
#check Real.exp_nonneg    -- (x : ℝ) : 0 ≤ Real.exp x
#check Real.exp_neg       -- (x : ℝ) : Real.exp (-x) = (Real.exp x)⁻¹
#check Real.exp_sub       -- (x y : ℝ) : Real.exp (x - y) = Real.exp x / Real.exp y
#check Real.exp_add       -- (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y
#check Real.exp_zero      -- Real.exp 0 = 1
#check Real.exp_strictMono -- StrictMono Real.exp
#check Real.exp_monotone   -- Monotone Real.exp

-- A-1: `Real.exp_lt_exp` 的两个方向都能用
example {x y : ℝ} (h : x < y) : Real.exp x < Real.exp y := Real.exp_lt_exp.mpr h
example {x y : ℝ} (h : Real.exp x < Real.exp y) : x < y := Real.exp_lt_exp.mp h
-- A-2: 严格单调包装也可用（两种写法等价）
example {x y : ℝ} (h : x < y) : Real.exp x < Real.exp y := Real.exp_strictMono h
example {x y : ℝ} (h : x < y) : Real.exp x < Real.exp y := Real.exp_lt_exp.2 h
-- A-3: exp_pos 可直接喂给 div_lt_div_of_pos_right / mul_lt_mul_of_pos_left
example (x y : ℝ) : 1 / Real.exp x < 1 / Real.exp y ↔ Real.exp y < Real.exp x := by
  rw [div_lt_div_iff_of_pos_right (Real.exp_pos y), div_lt_div_iff_of_pos_right (Real.exp_pos x)]
  exact Real.exp_lt_exp

/-! ## D 组：乘法 / 序 -/

#check mul_lt_mul_of_pos_left  -- (bc : b < c) (a0 : 0 < a) : a * b < a * c
#check mul_lt_mul_of_pos_right -- (bc : b < c) (a0 : 0 < a) : b * a < c * a
#check mul_pos                 -- (ha : 0 < a) (hb : 0 < b) : 0 < a * b
#check mul_nonneg              -- (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b
#check mul_lt_mul₀             -- (hab : a < b) (hcd : c < d) : a * c < b * d

-- D-1: lemma 4 的尾段 — 乘正数保序
example {A u v : ℝ} (hA : 0 < A) (h : u < v) : A * u < A * v := mul_lt_mul_of_pos_left h hA
-- D-2: 不用现成引理也可以（linarith 不行，见 API-NOTES 记录）
example {A u v : ℝ} (hA : 0 < A) (h : u < v) : A * u < A * v := by nlinarith

/-! ## 核心：lemma 4（rate 单调性）实测骨架

  目标形态：`barrier lam x < barrier lam y → rate A lam kB T y < rate A lam kB T x`
  链条：取负 (linarith) → 除以正数 (div_lt_div_of_pos_right) → exp 严格单调
        (Real.exp_lt_exp.mpr) → 乘正数 (mul_lt_mul_of_pos_left)
-/
noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)
noncomputable def rate (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(barrier lam x) / (kB * T))

-- L4 骨架（最短，2 行）
theorem L4_skeleton {A lam kB T x y : ℝ} (hA : 0 < A) (hkT : 0 < kB * T)
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  unfold rate
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (div_lt_div_of_pos_right (by linarith) hkT)) hA

-- L4 骨架（可读版，逐步）
theorem L4_stepwise {A lam kB T x y : ℝ} (hA : 0 < A) (hkT : 0 < kB * T)
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  unfold rate
  apply mul_lt_mul_of_pos_left _ hA          -- 乘正数：A * (…) < A * (…)
  rw [Real.exp_lt_exp]                        -- 吃掉 exp：x < y ↔ exp x < exp y
  exact div_lt_div_of_pos_right (by linarith) hkT  -- 除以正数；取负方向由 linarith 翻转
