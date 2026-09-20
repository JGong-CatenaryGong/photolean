/-
  marcus-tactic-api.lean — mathlib API 探针（Marcus 反转区，F 组 + G 组）

  目的
    ⑴ F 组：`ℚ` 层与 `ℚ → ℝ` 转移（`decide`、`Rat.cast_*`、`norm_num` 十进制字面量）；
    ⑵ G 组：战术可用性实测（nlinarith / positivity / norm_num / field_simp /
       ring_nf / gcongr / linarith），含题目指定的三类目标形态。

  运行命令（在仓库根目录执行）
    proofs/scripts/lake env lean proofs/probes/marcus-tactic-api.lean

  本文件为 **正向探针**：所有 example 必须全部成功、无 error。
  实测 **失败** 的写法写在注释里（带原始报错），不要写成 example，否则本文件不编译。

  校准基准：mathlib v4.17.0（lean-toolchain = leanprover/lean4:v4.17.0）
  校准日期：2026-09-20 — api_researcher
-/

import Mathlib

set_option linter.unusedVariables false

/-! ## ⚠️ 头号坑：**`λ` 不能作标识符**

  题目伪代码里的 `λ`（希腊字母 lambda）在 Lean 4 里是**保留关键字**（lambda 抽象
  的语法记号），写在 `def barrier (λ x : ℝ)` 或绑定位置会直接报

      error: unexpected token 'λ'; expected '_' or identifier

  实测：`noncomputable def barrier (λ x : ℝ) : ℝ := ...` 编译失败。
  **必须改名**，推荐 `lam`（本探针与 API-NOTES 全部用 `lam`）。
  同名可用：`lambda`。`λ` 只允许出现在注释里。
-/

noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-! ## F 组：ℚ 层与 ℚ → ℝ 转移

  ⚠️ 不存在（**禁止使用**）：`Rat.cast_pos_iff`（真名是 `Rat.cast_pos`，本身就是 iff）
                                `Rat.cast_lt_cast`
-/

-- 题目指定：`(1:ℚ) < 3` 用 `by decide` 是否真的能编译？ → **能**。原样通过。
example : (1 : ℚ) < 3 := by decide
example : ¬ ((3 : ℚ) < 1) := by decide
example : (1 : ℚ) ≤ 3 := by decide
example : (0 : ℚ) < 1 / 2 := by norm_num

-- ℚ → ℝ 转移：三个 cast 引理都是 **iff**
#check Rat.cast_lt   -- {p q : ℚ} {K} [LinearOrderedField K] : ↑p < ↑q ↔ p < q
#check Rat.cast_le   -- {p q : ℚ} {K} [LinearOrderedField K] : ↑p ≤ ↑q ↔ p ≤ q
#check Rat.cast_pos  -- {q : ℚ} {K} [LinearOrderedField K] : 0 < ↑q ↔ 0 < q
#check Rat.cast_inj  -- {p q : ℚ} {α} [DivisionRing α] [CharZero α] : ↑p = ↑q ↔ p = q
#check Rat.cast_div  -- (p q : ℚ) : ↑(p / q) = ↑p / ↑q
#check Rat.cast_one  -- ↑(1 : ℚ) = 1
#check Rat.cast_mk   -- (a b : ℤ) : ↑(Rat.divInt a b) = ↑a / ↑b   ← 注意是 divInt 形式

example {p q : ℚ} (h : p < q) : (p : ℝ) < (q : ℝ) := Rat.cast_lt.mpr h
example {p q : ℚ} (h : (p : ℝ) < (q : ℝ)) : p < q := Rat.cast_lt.mp h
example {q : ℚ} (h : (0 : ℚ) < q) : (0 : ℝ) < (q : ℝ) := Rat.cast_pos.mpr h
example (a b : ℤ) : (((Rat.divInt a b : ℚ)) : ℝ) = (a : ℝ) / (b : ℝ) := Rat.cast_mk a b
-- norm_num 直接吃十进制字面量与 ℚ→ℝ 混合
example : ((1 : ℚ) : ℝ) = 1 := by norm_num
example : ((1 : ℚ) / 2 : ℝ) < 1 := by norm_num
example : (((1 : ℚ) / 2 : ℚ) : ℝ) = 0.5 := by norm_num

/-! ## G 组：战术可用性实测

  三类目标形态（题目指定）全部通过，逐条见下。
  另外实测 **失败** 的路径：
    - `gcongr` 直接作用在 `(lam-x₁)^2/(4*lam) < (lam-x₂)^2/(4*lam)` 上失败：
      gcongr 走 `sq` 的单调性，需要 `0 ≤ lam - x₁`，而 lam ≤ x₁ 时它是 ≤ 0。
      必须先把底数改写成非负形式 `(x₁ - lam)^2` 再 `gcongr`，或改用 nlinarith 路线。
    - 单个 `nlinarith` 裸证原目标（不去分母）失败（分母符号没被利用）。
    - `field_simp` 在不等式上直接收尾失败：`error: simp made no progress`
      （需要先给出分母非零 `h : lam ≠ 0`，且目标为等式时才好用）。
-/

-- G-1: positivity 收尾（lam > 0 时 (lam-x)^2/(4*lam) ≥ 0）
example {lam x : ℝ} (hlam : 0 < lam) : 0 ≤ (lam - x) ^ 2 / (4 * lam) := by positivity
-- positivity 也能直接给正性前提
example {lam : ℝ} (hlam : 0 < lam) : (0 : ℝ) < 4 * lam := by positivity
example {kB T : ℝ} (h : 0 < kB * T) : (0 : ℝ) < kB * T := by positivity

-- G-2: **最关键** — barrier 右支严格单增的「最短成功证明」（2 行战术）
example {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ} (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) :
    (lam - x₁) ^ 2 / (4 * lam) < (lam - x₂) ^ 2 / (4 * lam) := by
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith

-- G-2b: 同一目标，显式走 sq_lt_sq₀ + div_lt_div_of_pos_right（不依赖 nlinarith 的启发式）
example {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ} (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) :
    (lam - x₁) ^ 2 / (4 * lam) < (lam - x₂) ^ 2 / (4 * lam) := by
  have hge : (0 : ℝ) ≤ x₁ - lam := by linarith
  have hlt : x₁ - lam < x₂ - lam := by linarith
  have hsq : (x₁ - lam) ^ 2 < (x₂ - lam) ^ 2 := (sq_lt_sq₀ hge (hge.trans hlt.le)).2 hlt
  rw [show (lam - x₁) ^ 2 = (x₁ - lam) ^ 2 by ring,
      show (lam - x₂) ^ 2 = (x₂ - lam) ^ 2 by ring]
  exact div_lt_div_of_pos_right hsq (by linarith : (0 : ℝ) < 4 * lam)

-- G-3: 对称性 — lam - (2*lam - x) 与原式相等。**不需要 hlam : lam ≠ 0**
--      （Lean 除零约定 x/0 = 0 使两边在 lam = 0 时同时为 0，故 lam ≠ 0 前提是多余的）
example (lam x : ℝ) :
    (lam - x) ^ 2 / (4 * lam) = (lam - (2 * lam - x)) ^ 2 / (4 * lam) := by ring_nf
example {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    (lam - x) ^ 2 / (4 * lam) = (lam - (2 * lam - x)) ^ 2 / (4 * lam) := by ring_nf

-- G-4: norm_num 处理十进制字面量
example : (0.5 : ℝ) < 1 := by norm_num
example : (1.2 : ℝ) = 6 / 5 := by norm_num
example : (0.5 : ℝ) * 4 = 2 := by norm_num
-- norm_num 不负责非线性不等式；配合去分母 + nlinarith
example {lam : ℝ} (hlam : 0 < lam) : -(lam - 1.2) ^ 2 / (4 * lam) < (1.5 : ℝ) := by
  rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith [sq_nonneg (lam - 1.2)]

-- G-5: field_simp（等式 + 显式非零前提）
example {lam x : ℝ} (h : lam ≠ 0) : barrier lam x * (4 * lam) = (lam - x) ^ 2 := by
  unfold barrier; field_simp
example {lam x y : ℝ} (h : lam ≠ 0)
    (h2 : (lam - x) ^ 2 / (4 * lam) = (lam - y) ^ 2 / (4 * lam)) :
    (lam - x) ^ 2 = (lam - y) ^ 2 := by
  field_simp at h2
  linarith

-- G-6: gcongr（在真正线性/单调的位置可用）
example {a b c : ℝ} (ha : 0 < a) (hbc : b < c) : a * b < a * c := by gcongr
-- gcongr 在改写为非负底数后也能吃掉平方
example {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ} (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) :
    (x₁ - lam) ^ 2 < (x₂ - lam) ^ 2 := by
  gcongr
  linarith

-- G-7: linarith / nlinarith 基本盘
example {a b : ℝ} (h : a < b) : a < b + 1 := by linarith
example {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : a ^ 2 < b ^ 2 := by nlinarith
-- ⚠️ nlinarith 的启发式并非万能：下面这条**真命题**裸 nlinarith 失败
--     error: linarith failed to find a contradiction / a✝ : 0 ≥ a^2 + b^2
--     `example {a b : ℝ} (h : a < b) : a ^ 2 + b ^ 2 > 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h]`
--   必须把"至少一个非零"显式做出来喂给它：
example {a b : ℝ} (h : a < b) : a ^ 2 + b ^ 2 > 0 := by
  have hne : a ≠ 0 ∨ b ≠ 0 := by rintro (h0 | h0) <;> linarith
  rcases hne with h0 | h0
  · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg b]
  · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg a]
