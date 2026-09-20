/-
  marcus-lemma-skeletons.lean — 引理 1–7 的**实测通过**证明骨架（statement-first 校验）

  目的
    ⑴ 证明每条 `plan.md` 风格的语句在 mathlib v4.17.0 下 **能编译**（statement-first）；
    ⑵ 给出每条引理的**最短成功证明**，供 prover_a..d 直接复用，不必猜名字。

  运行命令（在仓库根目录执行）
    proofs/scripts/lake env lean proofs/probes/marcus-lemma-skeletons.lean

  ⚠️ 本文件只是**校准证据**，不是交付物：交付证明写在 `PhotoLean/**`，
     属主见 `proofs/TASKS.md`。probes 目录不参与 `SOURCE_DIRS` 的 sorry/axiom 扫描。

  ⚠️ 标识符：Lean 4 里 `λ` 是保留关键字，不能做变量名 —— 本文件统一用 `lam`。
     题目伪代码的 `λ` 必须改写为 `lam`（或 `lambda`）。

  校准基准：mathlib v4.17.0（lean-toolchain = leanprover/lean4:v4.17.0）
  校准日期：2026-09-20 — api_researcher
-/

import Mathlib

set_option linter.unusedVariables false

noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

noncomputable def rate (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(barrier lam x) / (kB * T))

def InvertedRegion (lam x : ℝ) : Prop := lam < x

def InvertedDescriptor (A lam kB T : ℝ) : Prop :=
  ∀ x₁ x₂, lam < x₁ → x₁ < x₂ → rate A lam kB T x₂ < rate A lam kB T x₁

/-! ## 引理 1 — `0 < lam → 0 ≤ barrier lam x` -/

theorem L1_barrier_nonneg {lam x : ℝ} (hlam : 0 < lam) : 0 ≤ barrier lam x := by
  unfold barrier; positivity

/-- L1 的备用写法（不依赖 positivity，只用 `div_nonneg` + `sq_nonneg`） -/
theorem L1_barrier_nonneg' {lam x : ℝ} (hlam : 0 < lam) : 0 ≤ barrier lam x := by
  unfold barrier
  exact div_nonneg (sq_nonneg _) (by linarith)

/-! ## 引理 2 — `0 < lam → lam ≤ x₁ → x₁ < x₂ → barrier lam x₁ < barrier lam x₂`

  最短成功证明（2 行战术）：
    `rw [div_lt_div_iff_of_pos_right (by linarith : 0 < 4*lam)]` 去分母，
    然后 **裸 `nlinarith`** 就够（实测无需 `sq_nonneg` hint）。
-/

theorem L2_barrier_right_strict {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h₁ : lam ≤ x₁)
    (h₂ : x₁ < x₂) : barrier lam x₁ < barrier lam x₂ := by
  unfold barrier
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith

/-- L2 的显式版（不依赖 nlinarith 启发式，走 `sq_lt_sq₀`） -/
theorem L2_barrier_right_strict' {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h₁ : lam ≤ x₁)
    (h₂ : x₁ < x₂) : barrier lam x₁ < barrier lam x₂ := by
  have hge : (0 : ℝ) ≤ x₁ - lam := by linarith
  have hlt : x₁ - lam < x₂ - lam := by linarith
  have hsq : (x₁ - lam) ^ 2 < (x₂ - lam) ^ 2 := (sq_lt_sq₀ hge (hge.trans hlt.le)).2 hlt
  unfold barrier
  rw [show (lam - x₁) ^ 2 = (x₁ - lam) ^ 2 by ring,
      show (lam - x₂) ^ 2 = (x₂ - lam) ^ 2 by ring]
  exact div_lt_div_of_pos_right hsq (by linarith : (0 : ℝ) < 4 * lam)

/-! ## 引理 3 — `0 < lam → 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ lam → barrier lam x₂ < barrier lam x₁`

  **实测：前提 `0 ≤ x₁` 是多余的**（从 `x₂ ≤ lam` 与 `x₁ < x₂` 可推出），
  下面的 `L3_barrier_left_strict'` 不带它同样编译通过。
  若 `plan.md` 把它列为前提，属"物理近似显式化"的冗余前提，不影响正确性，
  但 prover 可以省掉。
-/

theorem L3_barrier_left_strict {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h₀ : 0 ≤ x₁) (h₁ : x₁ < x₂)
    (h₂ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁ := by
  unfold barrier
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith

/-- L3 去掉冗余前提 `0 ≤ x₁` 后仍成立（实测通过） -/
theorem L3_barrier_left_strict' {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h₁ : x₁ < x₂)
    (h₂ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁ := by
  unfold barrier
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith

/-! ## 引理 4（**核心**）— `0 < A → 0 < kB*T → barrier lam x < barrier lam y → rate … y < rate … x`

  链条：取负（linarith）→ 除以正数（`div_lt_div_of_pos_right`）
        → exp 严格单调（`Real.exp_lt_exp.2`）→ 乘正数（`mul_lt_mul_of_pos_left`）。
  最短版 **2 行**；逐步版见下。
-/

theorem L4_rate_strict {A lam kB T x y : ℝ} (hA : 0 < A) (hkT : 0 < kB * T)
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  unfold rate
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (div_lt_div_of_pos_right (by linarith) hkT)) hA

/-- L4 逐步版（每条引理对应一个物理/数学步骤，便于 prover 调试） -/
theorem L4_rate_strict_stepwise {A lam kB T x y : ℝ} (hA : 0 < A) (hkT : 0 < kB * T)
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  unfold rate
  apply mul_lt_mul_of_pos_left _ hA           -- 乘正数 A
  rw [Real.exp_lt_exp]                        -- exp 严格单调，消去 exp
  exact div_lt_div_of_pos_right (by linarith) hkT  -- 除以正数 kB*T；取负已由 linarith 翻转

/-! ## 引理 5 — `lam < 0 → lam < x₁ → x₁ < x₂ → barrier lam x₁ > barrier lam x₂`

  关键坑：`0 < lam` 时用 `div_lt_div_iff_of_pos_right`，但这里 `4*lam < 0`，
  **没有** `div_lt_div_iff_of_neg_right`（不存在）。路线是把 `4*lam` 改写成
  `-(4*(-lam))`，再用 `div_neg` + `neg_lt_neg_iff` 把负分母翻成正分母。
-/

theorem L5_barrier_neg_lam {lam x₁ x₂ : ℝ} (hlam : lam < 0) (h₁ : lam < x₁) (h₂ : x₁ < x₂) :
    barrier lam x₂ < barrier lam x₁ := by
  unfold barrier
  rw [show (4 : ℝ) * lam = -(4 * (-lam)) by ring, div_neg, div_neg, neg_lt_neg_iff]
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * (-lam))]
  nlinarith

/-- L5 的显式版（走 `mul_self_lt_mul_self` + `sq_lt_sq₀`，不用 nlinarith） -/
theorem L5_barrier_neg_lam' {lam x₁ x₂ : ℝ} (hlam : lam < 0) (h₁ : lam < x₁)
    (h₂ : x₁ < x₂) : barrier lam x₂ < barrier lam x₁ := by
  unfold barrier
  rw [show (4 : ℝ) * lam = -(4 * (-lam)) by ring, div_neg, div_neg, neg_lt_neg_iff]
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * (-lam))]
  rw [show (lam - x₁) ^ 2 = (x₁ - lam) ^ 2 by ring,
      show (lam - x₂) ^ 2 = (x₂ - lam) ^ 2 by ring]
  simpa only [pow_two] using
    mul_self_lt_mul_self (by linarith : (0 : ℝ) ≤ x₁ - lam) (by linarith : x₁ - lam < x₂ - lam)

/-! ## 引理 6 — `lam = 0 → barrier 0 x = 0`（Lean 除零约定 `x / 0 = 0`） -/

theorem L6_barrier_zero (x : ℝ) : barrier 0 x = 0 := by
  unfold barrier; ring

theorem L6_barrier_zero' {lam : ℝ} (h : lam = 0) (x : ℝ) : barrier lam x = 0 := by
  subst h; unfold barrier; ring

/-! ## 引理 7 — 对称性 `barrier lam x = barrier lam (2*lam - x)`（**不需要** `lam ≠ 0`） -/

theorem L7_barrier_symm (lam x : ℝ) : barrier lam x = barrier lam (2 * lam - x) := by
  unfold barrier; ring_nf

/-- L7 带 `lam ≠ 0` 前提（题目原样写法）：同样通过，但前提是多余的 -/
theorem L7_barrier_symm_with_h {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    barrier lam x = barrier lam (2 * lam - x) := by
  unfold barrier; ring_nf

/-! ## 实例层：`InvertedDescriptor` 由 L5（经 L4 的 rate 链）推出 -/

theorem InvertedDescriptor_of_neg {A lam kB T : ℝ} (hA : 0 < A) (hkT : 0 < kB * T)
    (hlam : lam < 0) : InvertedDescriptor A lam kB T := by
  intro x₁ x₂ hx₁ hx₂
  -- ⚠️ 不要在这里一口气 unfold rate/barrier 再 rw：`div_neg` 会与 rate 自带的负号
  --    叠成双重否定，`neg_lt_neg_iff` 就匹配不上了。先把 barrier 的不等式单独做出来。
  have hbar : barrier lam x₂ < barrier lam x₁ := by
    unfold barrier
    rw [show (4 : ℝ) * lam = -(4 * (-lam)) by ring, div_neg, div_neg, neg_lt_neg_iff]
    rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * (-lam))]
    nlinarith
  exact L4_rate_strict hA hkT hbar
