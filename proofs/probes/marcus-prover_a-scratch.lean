/-
prover_a 的临时探针（M1，`PhotoLean/Marcus/Basic.lean`）。

目的：在动交付文件之前，用一次 `lake env lean` 同时确认
  1. M1 要用的核心 API 名字（`if_pos` / `if_neg` / `iff_of_true` / `iff_of_false`
     / `le_of_not_gt` / `lt_of_le_of_ne` / `ne_of_lt` / `le_of_lt` / `Ne.symm` /
     `lt_irrefl` / `not_lt.mpr`）；
  2. 三条 `zone_eq_*_iff` 与 `zone_trichotomy` 的候选证明体**真的过内核**；
  3. `by decide` 能否判 `Zone` 构造子互异（derived DecidableEq 的可归约性）。
`#check` 的每一项都在下面立刻被证明体使用 —— 即"名字已实测"的判据。

运行：`proofs/scripts/lake env lean proofs/probes/marcus-prover_a-scratch.lean`
本文件不在 SOURCE_DIRS（`PhotoLean`），不影响 check.sh 的 sorry 扫描。
-/

import Mathlib

namespace PhotoLean.Marcus.Scratch

/-! ## 1. API 名字校准（M1 用到的全部引理） -/

#check @if_pos
#check @if_neg
#check @iff_of_true
#check @iff_of_false
#check @le_of_not_gt
#check @le_of_lt
#check @ne_of_lt
#check @lt_of_le_of_ne
#check @Ne.symm
#check @lt_irrefl
#check @not_lt
#check @absurd

/-! ## 2. 定义（与 `proofs/probes/marcus-statement-skeleton.lean` M1 段逐字一致） -/

noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

noncomputable def rate (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(barrier lam x) / (kB * T))

def InvertedRegion (lam x : ℝ) : Prop := lam < x

def NormalRegion (lam x : ℝ) : Prop := x < lam

def InvertedDescriptor (A lam kB T : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, lam < x₁ → x₁ < x₂ → rate A lam kB T x₂ < rate A lam kB T x₁

def NormalDescriptor (A lam kB T : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ lam → rate A lam kB T x₁ < rate A lam kB T x₂

inductive Zone where
  | normal
  | barrierless
  | inverted
  deriving DecidableEq, Repr

noncomputable def zone (lam x : ℝ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

/-! ## 3. `Zone` 构造子互异：derived `DecidableEq` 是否可被 `decide` 归约 -/

example : Zone.barrierless ≠ Zone.normal := by decide
example : Zone.normal ≠ Zone.barrierless := by decide
example : Zone.inverted ≠ Zone.normal := by decide
example : Zone.normal ≠ Zone.inverted := by decide
example : Zone.inverted ≠ Zone.barrierless := by decide
example : Zone.barrierless ≠ Zone.inverted := by decide

/-! ## 4. 候选证明体（`by_cases` + `if_pos`/`if_neg` + 匿名构造子，零 simp 依赖） -/

theorem zone_eq_normal_iff (lam x : ℝ) : zone lam x = Zone.normal ↔ NormalRegion lam x := by
  unfold zone NormalRegion
  by_cases h : x < lam
  · rw [if_pos h]
    exact iff_of_true rfl h
  · rw [if_neg h]
    by_cases h2 : x = lam
    · rw [if_pos h2]
      exact iff_of_false (by decide) h
    · rw [if_neg h2]
      exact iff_of_false (by decide) h

theorem zone_eq_barrierless_iff (lam x : ℝ) : zone lam x = Zone.barrierless ↔ x = lam := by
  unfold zone
  by_cases h : x < lam
  · rw [if_pos h]
    exact iff_of_false (by decide) (ne_of_lt h)
  · rw [if_neg h]
    by_cases h2 : x = lam
    · rw [if_pos h2]
      exact iff_of_true rfl h2
    · rw [if_neg h2]
      exact iff_of_false (by decide) h2

theorem zone_eq_inverted_iff (lam x : ℝ) : zone lam x = Zone.inverted ↔ InvertedRegion lam x := by
  unfold zone InvertedRegion
  by_cases h : x < lam
  · rw [if_pos h]
    exact iff_of_false (by decide) (not_lt.mpr (le_of_lt h))
  · rw [if_neg h]
    by_cases h2 : x = lam
    · rw [if_pos h2]
      exact iff_of_false (by decide) (by rw [h2]; exact lt_irrefl lam)
    · rw [if_neg h2]
      exact iff_of_true rfl (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h2))

theorem zone_trichotomy (lam x : ℝ) :
    zone lam x = Zone.normal ∨ zone lam x = Zone.barrierless ∨ zone lam x = Zone.inverted := by
  unfold zone
  by_cases h : x < lam
  · rw [if_pos h]; exact Or.inl rfl
  · rw [if_neg h]
    by_cases h2 : x = lam
    · rw [if_pos h2]; exact Or.inr (Or.inl rfl)
    · rw [if_neg h2]; exact Or.inr (Or.inr rfl)

/-! ## 5. 备选形态（记录哪条路不通或哪条更短，供经验库回写） -/

-- 备选 A：`cases` + `simp`（不依赖 `decide`，但依赖 `simp` 对构造子互异的处理）
theorem zone_trichotomy_altA (lam x : ℝ) :
    zone lam x = Zone.normal ∨ zone lam x = Zone.barrierless ∨ zone lam x = Zone.inverted := by
  cases h : zone lam x <;> simp

-- 备选 B：`simp [zone, NormalRegion, h]` —— **实测：单层 `by_cases` 不够**，
-- 第二分支报 `unsolved goals ⊢ ¬(if x = lam then Zone.barrierless else Zone.inverted) = Zone.normal`
-- （`simp` 把 `a ↔ False` 归约成 `¬a` 后，内层 `if` 缺 `x = lam` 的判据）。补第二层后通过：
theorem zone_eq_normal_iff_altB (lam x : ℝ) : zone lam x = Zone.normal ↔ NormalRegion lam x := by
  by_cases h : x < lam
  · simp [zone, NormalRegion, h]
  · by_cases h2 : x = lam
    · simp [zone, NormalRegion, h, h2]
    · simp [zone, NormalRegion, h, h2]

-- 备选 C：`lt_trichotomy` 三分 + `simp` —— **实测：把 `h` 直接塞给 `simp` 无效**
-- （报 `unsolved goals ... ⊢ (if x < lam then ... ) = Zone.inverted`：`lam < x` 不能反向简化
-- `x < lam`）。改用 `not_lt.mpr (le_of_lt h)` / `ne_of_gt h` 显式给否命题后通过：
theorem zone_eq_inverted_iff_altC (lam x : ℝ) : zone lam x = Zone.inverted ↔ InvertedRegion lam x := by
  rcases lt_trichotomy x lam with h | h | h
  · simp [zone, InvertedRegion, h, not_lt.mpr (le_of_lt h)]
  · subst h; simp [zone, InvertedRegion, lt_irrefl]
  · simp [zone, InvertedRegion, not_lt.mpr (le_of_lt h), ne_of_gt h, h]

end PhotoLean.Marcus.Scratch
