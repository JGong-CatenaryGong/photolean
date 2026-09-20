/-
lead 风险探针 2（非交付文件）：Sprint 2 的两个风险点提前跑通。
  (a) M1 分类器正确性 + M5a 的 ℚ→ℝ 转移引理（`Rat.cast_lt` / `Rat.cast_inj` 的实际行为）；
  (b) M3 剩余两条速率定理（normal_rate_increases / rate_peak_at_lam）的战术骨架。
运行：proofs/scripts/lake env lean theories/Marcus/probes/marcus-lead-risk2.lean

English: Lead risk probe 2 (non-deliverable file): get the two risk points of Sprint 2
working ahead of time.
  (a) M1 classifier correctness + the M5a ℚ→ℝ transfer lemma (the actual behaviour of
      `Rat.cast_lt` / `Rat.cast_inj`);
  (b) the tactic skeleton for the two remaining M3 rate theorems
      (`normal_rate_increases` / `rate_peak_at_lam`).
Run: proofs/scripts/lake env lean theories/Marcus/probes/marcus-lead-risk2.lean
-/
import Mathlib

set_option linter.unusedVariables false

namespace LeadRisk2

noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)
noncomputable def rate (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(barrier lam x) / (kB * T))
def InvertedRegion (lam x : ℝ) : Prop := lam < x
def NormalRegion (lam x : ℝ) : Prop := x < lam

inductive Zone where
  | normal
  | barrierless
  | inverted
  deriving DecidableEq, Repr

noncomputable def zone (lam x : ℝ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

def zoneQ (lam x : ℚ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

-- ── M1：分类器正确性 ────────────────────────────────────────────────────────
-- English: ── M1: classifier correctness ─────────────────────────────────────
theorem zone_eq_normal_iff (lam x : ℝ) : zone lam x = Zone.normal ↔ NormalRegion lam x := by
  unfold zone NormalRegion
  by_cases h : x < lam
  · simp [h]
  · by_cases h2 : x = lam
    · simp [h, h2]
    · simp [h, h2, not_lt.mp h]

theorem zone_eq_barrierless_iff (lam x : ℝ) : zone lam x = Zone.barrierless ↔ x = lam := by
  unfold zone
  split_ifs with h1 h2
  · exact ⟨fun hc => absurd hc (by decide), fun hc => by rw [hc] at h1; exact absurd h1 (lt_irrefl lam)⟩
  · exact ⟨fun _ => h2, fun _ => rfl⟩
  · exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc h2⟩

theorem zone_eq_inverted_iff (lam x : ℝ) : zone lam x = Zone.inverted ↔ InvertedRegion lam x := by
  unfold zone InvertedRegion
  split_ifs with h1 h2
  · exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc (not_lt.mpr (le_of_lt h1))⟩
  · exact ⟨fun hc => absurd hc (by decide), fun hc => by rw [h2] at hc; exact absurd hc (lt_irrefl lam)⟩
  · have h3 : lam < x := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    exact ⟨fun _ => h3, fun _ => rfl⟩

theorem zone_trichotomy (lam x : ℝ) :
    zone lam x = Zone.normal ∨ zone lam x = Zone.barrierless ∨ zone lam x = Zone.inverted := by
  unfold zone
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

-- ── M5a：ℚ → ℝ 转移引理 ────────────────────────────────────────────────────
-- English: ── M5a: ℚ → ℝ transfer lemma ─────────────────────────────────────
theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ) := by
  unfold zoneQ zone
  by_cases h : x < lam
  · have h' : (x : ℝ) < (lam : ℝ) := Rat.cast_lt.mpr h
    simp [h, h']
  · have h' : ¬ (x : ℝ) < (lam : ℝ) := fun hc => h (Rat.cast_lt.mp hc)
    by_cases h2 : x = lam
    · have h2' : (x : ℝ) = (lam : ℝ) := by exact_mod_cast h2
      simp [h, h2, h', h2']
    · have h2' : ¬ (x : ℝ) = (lam : ℝ) := fun hc => h2 (Rat.cast_inj.mp hc)
      simp [h, h2, h', h2']

theorem zoneQ_inverted_iff (lam x : ℚ) : zoneQ lam x = Zone.inverted ↔ (lam : ℝ) < (x : ℝ) := by
  rw [zoneQ_eq_zone, zone_eq_inverted_iff]
  exact Iff.rfl   -- `InvertedRegion (↑lam) (↑x)` 就是 `(↑lam : ℝ) < ↑x`（定义层 defeq）
                  -- English: `InvertedRegion (↑lam) (↑x)` is exactly `(↑lam : ℝ) < ↑x`
                  -- English: (definitionally equal, i.e. `defeq` at the definition layer)

-- ── M3 剩余两条 ─────────────────────────────────────────────────────────────
-- English: ── M3: the remaining two ──────────────────────────────────────────
theorem barrier_antitone_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁ := by
  have h4 : (0 : ℝ) < 4 * lam := by positivity
  have hsq : (lam - x₂) ^ 2 < (lam - x₁) ^ 2 := by nlinarith
  exact div_lt_div_of_pos_right hsq h4

theorem barrier_min_at_lam {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : barrier lam lam ≤ barrier lam x := by
  have h : barrier lam lam = 0 := by simp [barrier]
  rw [h]; unfold barrier; positivity

theorem rate_gt_of_barrier_lt {A lam kB T : ℝ} (hA : 0 < A) (hkT : 0 < kB * T) {x y : ℝ}
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  have hu : -(barrier lam y) / (kB * T) < -(barrier lam x) / (kB * T) :=
    div_lt_div_of_pos_right (by linarith) hkT
  have hexp := Real.exp_lt_exp.mpr hu
  unfold rate
  exact mul_lt_mul_of_pos_left hexp hA

theorem normal_rate_increases {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    {x₁ x₂ : ℝ} (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) :
    rate A lam kB T x₁ < rate A lam kB T x₂ :=
  rate_gt_of_barrier_lt hA hkT (barrier_antitone_of_pos hlam h₁ h₂ h₃)

theorem rate_peak_at_lam {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    (x : ℝ) : rate A lam kB T x ≤ rate A lam kB T lam := by
  have hb : barrier lam lam ≤ barrier lam x := barrier_min_at_lam hlam x
  have hu : -(barrier lam x) / (kB * T) ≤ -(barrier lam lam) / (kB * T) :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hkT)
  have hexp := Real.exp_le_exp.mpr hu
  unfold rate
  exact mul_le_mul_of_nonneg_left hexp (le_of_lt hA)

end LeadRisk2
