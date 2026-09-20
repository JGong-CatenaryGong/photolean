/-
prover_a 探针（M2 势垒代数，Sprint 2）— 非交付文件。

用途：
  1. 名字校准：`#check` 确认 mathlib v4.17.0 上实际存在的名字与签名（禁止猜名）；
  2. 最短成功骨架：把 `barrier_symm` / `barrier_mono_cases`（lead 风险探针未覆盖的两条）
     的候选战术在**真实 M1 定义**（`import PhotoLean.Marcus.Basic`）上跑通。

运行：proofs/scripts/lake env lean proofs/probes/marcus-prover_a2-scratch.lean
期望：全部 `example` 通过，无 error。

English:
prover_a probe (M2 barrier algebra, Sprint 2) - a non-deliverable file.

Purpose:
  1. Name calibration: `#check` confirms the names and signatures that actually exist on mathlib v4.17.0 (guessing names is forbidden);
  2. Minimal success skeleton: run the candidate tactics for `barrier_symm` / `barrier_mono_cases` (the two not covered by the lead risk probe)
     through on the **real M1 definitions** (`import PhotoLean.Marcus.Basic`).

Run: proofs/scripts/lake env lean proofs/probes/marcus-prover_a2-scratch.lean
Expected: all `example`s pass, no error.
-/
import PhotoLean.Marcus.Basic

-- ── 名字校准（mathlib v4.17.0，lean-toolchain 4.17.0）────────────────────────
-- English: Name calibration (mathlib v4.17.0, lean-toolchain 4.17.0)
#check @div_lt_div_of_pos_right
#check @div_lt_div_right_of_neg
#check @div_lt_div_iff_of_pos_right
#check @div_le_div_iff_of_pos_right
#check @sq_nonneg
#check @mul_self_lt_mul_self

namespace PhotoLean.Marcus

-- ── M2-3 `barrier_symm`：两个候选战术 ───────────────────────────────────────
-- English: M2-3 `barrier_symm`: two candidate tactics

-- (a) 带前提 hlam：`unfold` + `congr 1` + `ring`
-- English: (a) With the hypothesis `hlam`: `unfold` + `congr 1` + `ring`
example {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    barrier lam x = barrier lam (2 * lam - x) := by
  unfold barrier; congr 1; ring

-- (b) 带前提 hlam：`ring_nf` 一把收
-- English: (b) With the hypothesis `hlam`: `ring_nf` finishes it in one go
example {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    barrier lam x = barrier lam (2 * lam - x) := by
  unfold barrier; ring_nf

-- (c) **不要前提**：验证 `hlam : lam ≠ 0` 是否数学冗余（除零约定下两端同为 0）
-- English: (c) **No hypothesis needed**: check whether `hlam : lam ≠ 0` is mathematically redundant (under the division-by-zero convention both sides are 0)
example (lam x : ℝ) : barrier lam x = barrier lam (2 * lam - x) := by
  unfold barrier; ring_nf

-- ── M2-4 `barrier_min_at_lam`：两个候选战术 ─────────────────────────────────
-- English: M2-4 `barrier_min_at_lam`: two candidate tactics

-- (a) 复用 `barrier_at_lam`（探针内局部声明，交付文件里它先于本条）+ `positivity`
-- English: (a) Reuse `barrier_at_lam` (declared locally inside this probe; in the deliverable file it precedes this one) + `positivity`
theorem scratch_at_lam (lam : ℝ) : barrier lam lam = 0 := by simp [barrier]

example {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : barrier lam lam ≤ barrier lam x := by
  rw [scratch_at_lam]; unfold barrier; positivity

-- (b) 去分母 + `nlinarith [sq_nonneg (lam - x)]`
-- English: (b) Clear denominators + `nlinarith [sq_nonneg (lam - x)]`
example {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : barrier lam lam ≤ barrier lam x := by
  unfold barrier
  rw [div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith [sq_nonneg (lam - x)]

-- ── M2-9 `barrier_mono_cases`：四元合取组装 ─────────────────────────────────
-- English: M2-9 `barrier_mono_cases`: assembling the four-part conjunction
-- 注：以下四条用**已有交付名**（`barrier_mono_of_pos` 等来自 lead 风险骨架，
-- 本探针内重新声明为局部定义以独立验证组装形态）。
-- English: Note: the following four declarations use **already-delivered names** (`barrier_mono_of_pos` etc. from the lead risk skeleton,
-- English: re-declared inside this probe as local definitions to independently verify the assembly shape).

theorem scratch_mono_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) : barrier lam x₁ < barrier lam x₂ := by
  have h4 : (0 : ℝ) < 4 * lam := by positivity
  have hsq : (lam - x₁) ^ 2 < (lam - x₂) ^ 2 := by nlinarith
  exact div_lt_div_of_pos_right hsq h4

theorem scratch_antitone_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁ := by
  have h4 : (0 : ℝ) < 4 * lam := by positivity
  have hsq : (lam - x₂) ^ 2 < (lam - x₁) ^ 2 := by nlinarith
  exact div_lt_div_of_pos_right hsq h4

theorem scratch_antitone_of_neg {lam : ℝ} (hlam : lam < 0) {x₁ x₂ : ℝ}
    (h₁ : lam < x₁) (h₂ : x₁ < x₂) : barrier lam x₂ < barrier lam x₁ := by
  have h4 : 4 * lam < 0 := by linarith
  have hsq : (lam - x₁) ^ 2 < (lam - x₂) ^ 2 := by nlinarith
  unfold barrier
  exact (div_lt_div_right_of_neg h4).mpr hsq

theorem scratch_zero_lam (x : ℝ) : barrier 0 x = 0 := by simp [barrier]

example (lam : ℝ) :
    (0 < lam → ∀ x₁ x₂ : ℝ, lam ≤ x₁ → x₁ < x₂ → barrier lam x₁ < barrier lam x₂) ∧
    (0 < lam → ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ lam → barrier lam x₂ < barrier lam x₁) ∧
    (lam < 0 → ∀ x₁ x₂ : ℝ, lam < x₁ → x₁ < x₂ → barrier lam x₂ < barrier lam x₁) ∧
    (lam = 0 → ∀ x : ℝ, barrier lam x = 0) :=
  ⟨fun h x₁ x₂ h₁ h₂ => scratch_mono_of_pos h h₁ h₂,
   fun h x₁ x₂ h₁ h₂ h₃ => scratch_antitone_of_pos h h₁ h₂ h₃,
   fun h x₁ x₂ h₁ h₂ => scratch_antitone_of_neg h h₁ h₂,
   fun h x => by subst h; exact scratch_zero_lam x⟩

end PhotoLean.Marcus
