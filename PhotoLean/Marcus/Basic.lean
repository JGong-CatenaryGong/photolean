/-
PhotoLean.Marcus.Basic — M1 描述层（Marcus 反转区）。

**语句权威**：`proofs/probes/marcus-statement-skeleton.lean` 的 M1 段
（Sprint 0 已编译通过）。本文件的 8 个定义与 4 条定理签名与它**逐字一致**；
定理体已全部补齐（零占位证明、无自定义公理声明）。

**注**：本文件头刻意不写出被 `check.sh --strict` 扫描的两个关键字字面量
（块注释同样在扫描范围内，写了会造成误报 FAIL）。

**命名约定（工具链硬约束）**：Lean 4 中 `λ` 是 lambda 关键字，不可作标识符，
故物理记号一律 ASCII 化：重组能 `lam`、驱动力 `x`、前置因子 `A`、`kB`、`T`。

验收（契约 `proofs/ENGINE.yml`）：
  proofs/scripts/lake build PhotoLean.Marcus.Basic
  proofs/scripts/check.sh --strict PhotoLean.Marcus.Basic
  proofs/scripts/axioms.sh PhotoLean.Marcus.Basic PhotoLean.Marcus.<theorem>

English: PhotoLean.Marcus.Basic — the M1 description layer (the Marcus inverted region).

**Statement authority**: the M1 section of `proofs/probes/marcus-statement-skeleton.lean`
(compiled successfully in Sprint 0). The 8 definitions and 4 theorem signatures in this
file are **verbatim identical** to it; all theorem bodies are complete (zero placeholder
proofs, no custom axiomatic declarations).

**Note**: this file header deliberately does not spell out the two keyword literals scanned
by `check.sh --strict` (block comments are within the scan range as well, so writing them
would trigger a false-positive FAIL).

**Naming convention (hard toolchain constraint)**: in Lean 4, `λ` is a lambda keyword and
cannot serve as an identifier, so the physical notation is uniformly ASCII-ized:
reorganization energy `lam`, driving force `x`, pre-exponential factor `A`, `kB`, `T`.

Acceptance (contract `proofs/ENGINE.yml`):
  proofs/scripts/lake build PhotoLean.Marcus.Basic
  proofs/scripts/check.sh --strict PhotoLean.Marcus.Basic
  proofs/scripts/axioms.sh PhotoLean.Marcus.Basic PhotoLean.Marcus.<theorem>
-/
import Mathlib

namespace PhotoLean.Marcus

/-! ## 基础定义（M1 §2.2）

English: ## Basic definitions (M1 §2.2) -/

/-- 经典马库斯势垒：驱动力 `x = -ΔG°`，重组能 `lam`。

English: The classical Marcus barrier: driving force `x = -ΔG°`, reorganization energy `lam`. -/
noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- 马库斯速率：`k = A · exp(-ΔG‡/(k_B T))`。

English: The Marcus rate: `k = A · exp(-ΔG‡/(k_B T))`. -/
noncomputable def rate (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(barrier lam x) / (kB * T))

/-- 反转区：驱动力超过重组能。

English: Inverted region: the driving force exceeds the reorganization energy. -/
def InvertedRegion (lam x : ℝ) : Prop := lam < x

/-- 正常区：驱动力小于重组能。

English: Normal region: the driving force is less than the reorganization energy. -/
def NormalRegion (lam x : ℝ) : Prop := x < lam

/-- 反转区描述：反转区内速率随驱动力严格递减。

English: Inverted-region descriptor: within the inverted region the rate is strictly
decreasing in the driving force. -/
def InvertedDescriptor (A lam kB T : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, lam < x₁ → x₁ < x₂ → rate A lam kB T x₂ < rate A lam kB T x₁

/-- 正常区描述：正常区内速率随驱动力严格递增。

English: Normal-region descriptor: within the normal region the rate is strictly
increasing in the driving force. -/
def NormalDescriptor (A lam kB T : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ lam → rate A lam kB T x₁ < rate A lam kB T x₂

/-- 区域分类。

English: Region classification. -/
inductive Zone where
  | normal
  | barrierless
  | inverted
  deriving DecidableEq, Repr

/-- 分类器。

English: The classifier. -/
noncomputable def zone (lam x : ℝ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

/-! ## 分类器正确性（M1 §4.2）

证明骨架统一为：`unfold` 定义 → 对 `x < lam` 与 `x = lam` 两层 `by_cases`
→ `if_pos` / `if_neg` 消去 `if` → `iff_of_true` / `iff_of_false` 收尾。
`Zone` 三个构造子的互异由 derived `DecidableEq` 的可归约性给出（`by decide`），
不依赖 `simp` 的构造子判据。

English: ## Classifier correctness (M1 §4.2)

The proof skeleton is uniform: `unfold` the definitions → two layers of `by_cases`
on `x < lam` and `x = lam` → eliminate `if` with `if_pos` / `if_neg` → finish with
`iff_of_true` / `iff_of_false`. The distinctness of the three `Zone` constructors is
obtained from the reducibility of the derived `DecidableEq` (`by decide`), without
relying on the constructor lemmas of `simp`. -/

/-- 分类器判"正常区"当且仅当 `x < lam`。

English: The classifier returns "normal region" if and only if `x < lam`. -/
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

/-- 分类器判"无势垒点"当且仅当 `x = lam`。

English: The classifier returns "barrierless point" if and only if `x = lam`. -/
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

/-- 分类器判"反转区"当且仅当 `lam < x`（`InvertedRegion`）。

English: The classifier returns "inverted region" if and only if `lam < x` (`InvertedRegion`). -/
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

/-- 三分性：分类器必然落在三个区之一（直接由 `zone` 的两层 `if` 的构造给出）。

English: Trichotomy: the classifier necessarily falls into one of the three regions
(directly from the construction of the two nested `if`s in `zone`). -/
theorem zone_trichotomy (lam x : ℝ) :
    zone lam x = Zone.normal ∨ zone lam x = Zone.barrierless ∨ zone lam x = Zone.inverted := by
  unfold zone
  by_cases h : x < lam
  · rw [if_pos h]; exact Or.inl rfl
  · rw [if_neg h]
    by_cases h2 : x = lam
    · rw [if_pos h2]; exact Or.inr (Or.inl rfl)
    · rw [if_neg h2]; exact Or.inr (Or.inr rfl)

end PhotoLean.Marcus
