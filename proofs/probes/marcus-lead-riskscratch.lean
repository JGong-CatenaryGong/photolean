/-
lead 风险探针（不属于任何交付文件）：把两处最难的证明内核**先跑通**，供 Sprint 3/4 复用。

风险点：
  (a) M3 核心引理 `rate_gt_of_barrier_lt` —— 全项目唯一的 Real.exp 单调性使用点；
  (b) M4a `descriptor_sharp` 的**必要性**两支 —— 尤其 `lam = 0` 分支，
      Lean 的除零约定 `x / 0 = 0` 会让 `barrier 0 x = 0`，必须显式覆盖。

本文件不产生交付定理，只作为 Sprint 2/3/4 的"最短成功骨架"证据。
运行：proofs/scripts/lake env lean proofs/probes/marcus-lead-riskscratch.lean

English: Lead risk probe (not part of any deliverable file): get the two hardest proof
kernels **working first**, for reuse in Sprints 3/4.

Risk points:
  (a) M3 core lemma `rate_gt_of_barrier_lt` — the only place in the whole project that
      uses the monotonicity of `Real.exp`;
  (b) the two **necessity** branches of M4a `descriptor_sharp` — especially the `lam = 0`
      branch: Lean’s division-by-zero convention `x / 0 = 0` gives `barrier 0 x = 0`, which
      must be covered explicitly.

English: This file produces no deliverable theorem; it is only evidence of the "shortest
successful skeleton" for Sprints 2/3/4.
Run: proofs/scripts/lake env lean proofs/probes/marcus-lead-riskscratch.lean
-/
import Mathlib

-- 注：`barrier_antitone_of_pos` 的前提 `h₁ : 0 ≤ x₁` 数学上可由 `h₃` 推出（冗余），
-- 但保留为**显式物理前提**（驱动力非负），故关掉未使用变量 linter。
-- English: Note: the hypothesis `h₁ : 0 ≤ x₁` of `barrier_antitone_of_pos` is
-- English: mathematically derivable from `h₃` (redundant), but it is kept as an
-- English: **explicit physical hypothesis** (nonnegative driving force); hence the
-- English: unused-variable linter is disabled.
set_option linter.unusedVariables false

namespace LeadRisk

noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)
noncomputable def rate (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(barrier lam x) / (kB * T))
def InvertedRegion (lam x : ℝ) : Prop := lam < x
def InvertedDescriptor (A lam kB T : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, lam < x₁ → x₁ < x₂ → rate A lam kB T x₂ < rate A lam kB T x₁

-- ── M2 骨架 ────────────────────────────────────────────────────────────────
-- English: ── M2 skeleton ───────────────────────────────────────────────────
theorem barrier_at_lam (lam : ℝ) : barrier lam lam = 0 := by simp [barrier]

theorem barrier_zero_lam (x : ℝ) : barrier 0 x = 0 := by simp [barrier]

theorem barrier_nonneg {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : 0 ≤ barrier lam x := by
  unfold barrier; positivity

theorem barrier_min_at_lam {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : barrier lam lam ≤ barrier lam x := by
  rw [barrier_at_lam]; unfold barrier; positivity

theorem barrier_mono_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) : barrier lam x₁ < barrier lam x₂ := by
  have h4 : (0 : ℝ) < 4 * lam := by positivity
  have hsq : (lam - x₁) ^ 2 < (lam - x₂) ^ 2 := by nlinarith
  exact div_lt_div_of_pos_right hsq h4

theorem barrier_antitone_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁ := by
  have h4 : (0 : ℝ) < 4 * lam := by positivity
  have hsq : (lam - x₂) ^ 2 < (lam - x₁) ^ 2 := by nlinarith
  exact div_lt_div_of_pos_right hsq h4

theorem barrier_antitone_of_neg {lam : ℝ} (hlam : lam < 0) {x₁ x₂ : ℝ}
    (h₁ : lam < x₁) (h₂ : x₁ < x₂) : barrier lam x₂ < barrier lam x₁ := by
  have h4 : 4 * lam < 0 := by linarith
  have hsq : (lam - x₁) ^ 2 < (lam - x₂) ^ 2 := by nlinarith
  unfold barrier
  exact (div_lt_div_right_of_neg h4).mpr hsq

-- ── M3 核心引理（风险点 a） ────────────────────────────────────────────────
-- English: ── M3 core lemma (risk point a) ──────────────────────────────────
theorem rate_pos {A lam kB T : ℝ} (hA : 0 < A) (x : ℝ) : 0 < rate A lam kB T x := by
  unfold rate; positivity

theorem rate_gt_of_barrier_lt {A lam kB T : ℝ} (hA : 0 < A) (hkT : 0 < kB * T) {x y : ℝ}
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  have hu : -(barrier lam y) / (kB * T) < -(barrier lam x) / (kB * T) := by
    exact div_lt_div_of_pos_right (by linarith) hkT
  have hexp := Real.exp_lt_exp.mpr hu
  unfold rate
  exact mul_lt_mul_of_pos_left hexp hA

theorem inverted_rate_decreases {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    {x₁ x₂ : ℝ} (h₁ : lam < x₁) (h₂ : x₁ < x₂) : rate A lam kB T x₂ < rate A lam kB T x₁ :=
  rate_gt_of_barrier_lt hA hkT (barrier_mono_of_pos hlam (le_of_lt h₁) h₂)

-- ── M4a 必要性（风险点 b） ─────────────────────────────────────────────────
-- English: ── M4a necessity (risk point b) ──────────────────────────────────
theorem sharp_A_pos {A lam kB T : ℝ} (hpos : ∀ x, 0 < rate A lam kB T x) : 0 < A := by
  have h := hpos lam
  unfold rate at h
  exact pos_of_mul_pos_left h (le_of_lt (Real.exp_pos _))

theorem sharp_lam_pos_of_lt {A lam kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hA : 0 < A)
    (hdesc : InvertedDescriptor A lam kB T) (hlt : lam < 0) : False := by
  have hkT : 0 < kB * T := mul_pos hkB hT
  have hb : barrier lam (lam + 2) < barrier lam (lam + 1) :=
    barrier_antitone_of_neg hlt (by linarith) (by linarith)
  have hu : -(barrier lam (lam + 1)) / (kB * T) < -(barrier lam (lam + 2)) / (kB * T) := by
    exact div_lt_div_of_pos_right (by linarith) hkT
  have hexp := Real.exp_lt_exp.mpr hu
  have hrate : rate A lam kB T (lam + 1) < rate A lam kB T (lam + 2) := by
    unfold rate
    exact mul_lt_mul_of_pos_left hexp hA
  have hd := hdesc (lam + 1) (lam + 2) (by linarith) (by linarith)
  exact absurd hd (not_lt.mpr (le_of_lt hrate))

/-- `lam = 0` 分支：**不需要任何正性前提** —— 除零约定使势垒恒为零，速率恒为 `A`。-

English: The `lam = 0` branch: **no positivity hypothesis is needed at all** — the
division-by-zero convention makes the barrier identically zero, so the rate is identically
`A`.
-/
theorem sharp_lam_pos_of_eq {A kB T : ℝ} (hdesc : InvertedDescriptor A 0 kB T) : False := by
  have hrate : ∀ x : ℝ, rate A 0 kB T x = A := by
    intro x
    unfold rate
    rw [barrier_zero_lam]
    simp
  have hd := hdesc 1 2 (by norm_num) (by norm_num)
  rw [hrate 2, hrate 1] at hd
  exact lt_irrefl A hd

/-- 锐利刻画（必要性）：把两支合起来。-

English: Sharp characterization (necessity direction): combine the two branches.
-/
theorem sharp_lam_pos {A lam kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hA : 0 < A)
    (hdesc : InvertedDescriptor A lam kB T) : 0 < lam := by
  rcases lt_trichotomy lam 0 with h | h | h
  · exact (sharp_lam_pos_of_lt hkB hT hA hdesc h).elim
  · subst h; exact (sharp_lam_pos_of_eq hdesc).elim
  · exact h

end LeadRisk
