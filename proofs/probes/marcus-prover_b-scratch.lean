/-
  marcus-prover_b-scratch.lean — prover_b 的 M3 速率层探针（非交付文件）

  目的：
    1. 在写交付文件前，把 M3 三条语句在**真定义**（`PhotoLean.Marcus.Basic` 的
       `barrier` / `rate`，不重定义）上跑通；
    2. 确认 `rate_ratio` 拉伸目标所需的 exp/除法引理名字与用法。

  运行：proofs/scripts/lake env lean proofs/probes/marcus-prover_b-scratch.lean

  English: marcus-prover_b-scratch.lean — prover_b's M3 rate-layer probe (not a deliverable file)

  Purpose:
    1. Before writing the deliverable file, run the three M3 statements through on the **real
       definitions** (`barrier` / `rate` of `PhotoLean.Marcus.Basic`, without redefining them);
    2. Confirm the names and usage of the exp/division lemmas needed for the `rate_ratio` stretched target.

  Run: proofs/scripts/lake env lean proofs/probes/marcus-prover_b-scratch.lean
-/

import PhotoLean.Marcus.Basic

namespace PhotoLean.Marcus.Scratch

/-- M3-1：与 statement skeleton 逐字一致的语句，作用于 Basic 的真定义。

English: M3-1: the statement that is verbatim identical to the statement skeleton, acting on Basic's real definitions. --/
theorem rate_pos {A lam kB T : ℝ} (hA : 0 < A) (x : ℝ) : 0 < rate A lam kB T x := by
  unfold rate; positivity

/-- M3-2：核心转移引理。

English: M3-2: the core transfer lemma. --/
theorem rate_gt_of_barrier_lt {A lam kB T : ℝ} (hA : 0 < A) (hkT : 0 < kB * T) {x y : ℝ}
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  have hu : -(barrier lam y) / (kB * T) < -(barrier lam x) / (kB * T) :=
    div_lt_div_of_pos_right (by linarith) hkT
  have hexp := Real.exp_lt_exp.mpr hu
  unfold rate
  exact mul_lt_mul_of_pos_left hexp hA

-- ── rate_ratio 候选路线（拉伸目标）────────────────────────────────────────────
-- English: ── candidate routes for rate_ratio (stretched target) ──────────────────────────────

-- 候选 A：先 exp 相除
-- English: candidate A: divide the exps first
example {A lam kB T : ℝ} (hA : A ≠ 0) (hkT : kB * T ≠ 0) (x y : ℝ) :
    (A * Real.exp (-(barrier lam y) / (kB * T))) / (A * Real.exp (-(barrier lam x) / (kB * T)))
      = Real.exp (-(barrier lam y) / (kB * T)) / Real.exp (-(barrier lam x) / (kB * T)) := by
  rw [mul_div_mul_left _ _ hA]

-- 候选 B：exp 相除 = exp 差
-- English: candidate B: quotient of exps = exp of the difference
example {u v : ℝ} : Real.exp u / Real.exp v = Real.exp (u - v) := (Real.exp_sub u v).symm

-- 候选 C：指数做代数
-- English: candidate C: do the algebra in the exponent
example {lam kB T x y : ℝ} (hkT : kB * T ≠ 0) :
    (-(barrier lam y) / (kB * T)) - (-(barrier lam x) / (kB * T))
      = (barrier lam x - barrier lam y) / (kB * T) := by
  field_simp
  ring

/-- M3-3（拉伸目标）路线 1：`mul_div_mul_left` + `Real.exp_sub` + `field_simp; ring`。

English: M3-3 (stretched target), route 1: `mul_div_mul_left` + `Real.exp_sub` + `field_simp; ring`. --/
theorem rate_ratio_try1 {A lam kB T : ℝ} (hA : A ≠ 0) (hkT : kB * T ≠ 0) (x y : ℝ) :
    rate A lam kB T y / rate A lam kB T x
      = Real.exp ((barrier lam x - barrier lam y) / (kB * T)) := by
  unfold rate
  rw [mul_div_mul_left _ _ hA, ← Real.exp_sub]
  congr 1
  field_simp
  ring

end PhotoLean.Marcus.Scratch
