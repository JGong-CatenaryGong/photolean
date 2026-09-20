/-
prover_a 的临时探针（M1，`PhotoLean/Marcus/Basic.lean`）。

目的：在动交付文件之前，用一次 `lake env lean` 同时确认
  1. M1 要用的核心 API 名字（`if_pos` / `if_neg` / `iff_of_true` / `iff_of_false`
     / `le_of_not_gt` / `lt_of_le_of_ne` / `ne_of_lt` / `le_of_lt` / `Ne.symm` /
     `lt_irrefl` / `not_lt.mpr`）；
  2. 三条 `zone_eq_*_iff` 与 `zone_trichotomy` 的候选证明体**真的过内核**；
  3. `by decide` 能否判 `Zone` 构造子互异（derived DecidableEq 的可归约性）。
`#check` 的每一项都在下面立刻被证明体使用 —— 即"名字已实测"的判据。

运行：`proofs/scripts/lake env lean theories/Marcus/probes/marcus-prover_a-scratch.lean`
本文件不在 SOURCE_DIRS（`PhotoLean`），不影响 check.sh 的 sorry 扫描。

English: Scratch probe by prover_a (M1, `PhotoLean/Marcus/Basic.lean`).

English: Purpose: before touching the deliverable file, a single `lake env lean` run confirms at once
English:   1. the core API names needed by M1 (`if_pos` / `if_neg` / `iff_of_true` / `iff_of_false`
English:      / `le_of_not_gt` / `lt_of_le_of_ne` / `ne_of_lt` / `le_of_lt` / `Ne.symm` /
English:      `lt_irrefl` / `not_lt.mpr`);
English:   2. that the candidate proof bodies of the three `zone_eq_*_iff` lemmas and of `zone_trichotomy` **really pass the kernel**;
English:   3. whether `by decide` can decide that the `Zone` constructors are pairwise distinct (reducibility of the derived `DecidableEq`).
English: Every `#check` item is used immediately below by a proof body — that is the criterion for "the name has been tested in practice".

English: How to run: `proofs/scripts/lake env lean theories/Marcus/probes/marcus-prover_a-scratch.lean`
English: This file is not in SOURCE_DIRS (`PhotoLean`) and does not affect check.sh's scan for unproved placeholders.
-/

import Mathlib

namespace PhotoLean.Marcus.Scratch

/-! ## 1. API 名字校准（M1 用到的全部引理）

English: ## 1. API name calibration (all lemmas used by M1)
-/

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

/-! ## 2. 定义（与 `theories/Marcus/probes/marcus-statement-skeleton.lean` M1 段逐字一致）

English: ## 2. Definitions (verbatim identical to the M1 section of `theories/Marcus/probes/marcus-statement-skeleton.lean`)
-/

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

/-! ## 3. `Zone` 构造子互异：derived `DecidableEq` 是否可被 `decide` 归约

English: ## 3. Pairwise distinctness of the `Zone` constructors: can the derived `DecidableEq` be reduced by `decide`
-/

example : Zone.barrierless ≠ Zone.normal := by decide
example : Zone.normal ≠ Zone.barrierless := by decide
example : Zone.inverted ≠ Zone.normal := by decide
example : Zone.normal ≠ Zone.inverted := by decide
example : Zone.inverted ≠ Zone.barrierless := by decide
example : Zone.barrierless ≠ Zone.inverted := by decide

/-! ## 4. 候选证明体（`by_cases` + `if_pos`/`if_neg` + 匿名构造子，零 simp 依赖）

English: ## 4. Candidate proof bodies (`by_cases` + `if_pos`/`if_neg` + anonymous proof terms, no reliance on simp)
-/

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

/-! ## 5. 备选形态（记录哪条路不通或哪条更短，供经验库回写）

English: ## 5. Alternative forms (recording which route fails and which one is shorter, for write-back into the experience bank)
-/

-- 备选 A：`cases` + `simp`（不依赖 `decide`，但依赖 `simp` 对构造子互异的处理）
-- English: Alternative A: `cases` + `simp` (does not rely on `decide`, but relies on how `simp` handles constructor distinctness)
theorem zone_trichotomy_altA (lam x : ℝ) :
    zone lam x = Zone.normal ∨ zone lam x = Zone.barrierless ∨ zone lam x = Zone.inverted := by
  cases h : zone lam x <;> simp

-- 备选 B：`simp [zone, NormalRegion, h]` —— **实测：单层 `by_cases` 不够**，
-- 第二分支报 `unsolved goals ⊢ ¬(if x = lam then Zone.barrierless else Zone.inverted) = Zone.normal`
-- （`simp` 把 `a ↔ False` 归约成 `¬a` 后，内层 `if` 缺 `x = lam` 的判据）。补第二层后通过：
-- English: Alternative B: `simp [zone, NormalRegion, h]` — **verified in practice: a single layer of `by_cases` is not enough**;
-- English: the second branch reports `unsolved goals ⊢ ¬(if x = lam then Zone.barrierless else Zone.inverted) = Zone.normal`
-- English: (after `simp` reduces `a ↔ False` to `¬a`, the inner `if` lacks a criterion for `x = lam`). It goes through once the second layer is added:
theorem zone_eq_normal_iff_altB (lam x : ℝ) : zone lam x = Zone.normal ↔ NormalRegion lam x := by
  by_cases h : x < lam
  · simp [zone, NormalRegion, h]
  · by_cases h2 : x = lam
    · simp [zone, NormalRegion, h, h2]
    · simp [zone, NormalRegion, h, h2]

-- 备选 C：`lt_trichotomy` 三分 + `simp` —— **实测：把 `h` 直接塞给 `simp` 无效**
-- （报 `unsolved goals ... ⊢ (if x < lam then ... ) = Zone.inverted`：`lam < x` 不能反向简化
-- `x < lam`）。改用 `not_lt.mpr (le_of_lt h)` / `ne_of_gt h` 显式给否命题后通过：
-- English: Alternative C: `lt_trichotomy` trichotomy + `simp` — **verified in practice: feeding `h` straight into `simp` does not work**
-- English: (it reports `unsolved goals ... ⊢ (if x < lam then ... ) = Zone.inverted`: `lam < x` cannot be used to simplify
-- English: `x < lam` in the reverse direction). It goes through after supplying the negations explicitly via `not_lt.mpr (le_of_lt h)` / `ne_of_gt h`:
theorem zone_eq_inverted_iff_altC (lam x : ℝ) : zone lam x = Zone.inverted ↔ InvertedRegion lam x := by
  rcases lt_trichotomy x lam with h | h | h
  · simp [zone, InvertedRegion, h, not_lt.mpr (le_of_lt h)]
  · subst h; simp [zone, InvertedRegion, lt_irrefl]
  · simp [zone, InvertedRegion, not_lt.mpr (le_of_lt h), ne_of_gt h, h]

end PhotoLean.Marcus.Scratch
