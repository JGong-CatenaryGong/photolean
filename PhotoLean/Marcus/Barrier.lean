/-
PhotoLean.Marcus.Barrier — M2 势垒代数（Marcus 反转区）。

**语句权威**：`proofs/probes/marcus-statement-skeleton.lean` 的 M2 段
（Sprint 0 已编译通过）。本文件 9 条定理签名与它**逐字一致**；
证明体全部经内核检查（零占位证明、无自定义公理声明）。

**注**：本文件头刻意不写出被 `check.sh --strict` 扫描的两个关键字字面量
（块注释同样在扫描范围内，写了会造成误报 FAIL）。

**显式物理前提：未被证明使用（unused），而非可由其余前提推出（plan §5；实测见 proofs/API-NOTES.md）**：
- `barrier_symm` 的 `hlam : lam ≠ 0`：实测 `unfold barrier; ring_nf` **不需要**它 ——
  除零约定下 `lam = 0` 时两端同为 `0`；仍按语句权威保留为显式物理前提。
- `barrier_antitone_of_pos` 的 `h₁ : 0 ≤ x₁`：**证明未使用**它（`hlam`、`h₂`、`h₃`
  已足以推出结论），但它**并非**由 `h₂`、`h₃ : x₂ ≤ lam` 蕴含 —— **内核已验证的反例**：
  `lam = 1, x₁ = -5, x₂ = -4` 满足 `0 < lam`、`x₁ < x₂`、`x₂ ≤ lam`，而 `0 ≤ x₁` 为假。
  保留为显式物理前提（驱动力非负，normal 区的物理定义域）。
故顶部关掉未使用变量 linter（warning 不影响验收）。

验收（契约 `proofs/ENGINE.yml`）：
  proofs/scripts/lake build PhotoLean.Marcus.Barrier
  proofs/scripts/check.sh --strict PhotoLean.Marcus.Barrier
  proofs/scripts/axioms.sh PhotoLean.Marcus.Barrier PhotoLean.Marcus.<theorem>

English: PhotoLean.Marcus.Barrier — M2 barrier algebra (Marcus inverted region).

**Statement authority**: the M2 section of `proofs/probes/marcus-statement-skeleton.lean`
(compiled in Sprint 0). The 9 theorem signatures in this file are **verbatim identical**
to it; every proof body has been checked by the kernel (zero placeholder proofs, no
custom axiom declarations).

**Note**: this file header deliberately does not spell out the two keyword literals
scanned by `check.sh --strict` (block comments are scanned as well, so writing them
here would cause a false-positive FAIL).

**Explicit physical hypotheses: unused by the proofs, rather than derivable from the
remaining hypotheses (plan §5; measurements in proofs/API-NOTES.md)**:
- `hlam : lam ≠ 0` of `barrier_symm`: measurements show `unfold barrier; ring_nf` does
  **not** need it — under the division-by-zero convention both sides are `0` when
  `lam = 0`; it is still kept as an explicit physical hypothesis, per the statement
  authority.
- `h₁ : 0 ≤ x₁` of `barrier_antitone_of_pos`: the **proof does not use** it (`hlam`,
  `h₂`, `h₃` already suffice to derive the conclusion), but it is **not** implied by
  `h₂`, `h₃ : x₂ ≤ lam` — **a kernel-verified counterexample**:
  `lam = 1, x₁ = -5, x₂ = -4` satisfies `0 < lam`, `x₁ < x₂`, `x₂ ≤ lam`, while `0 ≤ x₁`
  is false. It is kept as an explicit physical hypothesis (nonnegative driving force,
  the physical domain of the normal region).
Hence the unused-variable linter is switched off at the top (warnings do not affect
acceptance).

Acceptance (contract `proofs/ENGINE.yml`):
  proofs/scripts/lake build PhotoLean.Marcus.Barrier
  proofs/scripts/check.sh --strict PhotoLean.Marcus.Barrier
  proofs/scripts/axioms.sh PhotoLean.Marcus.Barrier PhotoLean.Marcus.<theorem>
-/
import PhotoLean.Marcus.Basic

set_option linter.unusedVariables false

namespace PhotoLean.Marcus

/-! ## M2 — 势垒代数（§5）

English: ## M2 — barrier algebra (§5). -/

/-- `lam > 0` 时势垒非负（物理：势垒高度不可能为负）。

English: For `lam > 0` the barrier is nonnegative (physics: a barrier height cannot be
negative). -/
theorem barrier_nonneg {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : 0 ≤ barrier lam x := by
  unfold barrier; positivity

/-- 无势垒点：`x = lam` 处势垒为零（**无需前提**，含 `lam = 0` 的退化情形）。

English: Barrier-free point: the barrier vanishes at `x = lam` (**no hypothesis needed**,
including the degenerate case `lam = 0`). -/
theorem barrier_at_lam (lam : ℝ) : barrier lam lam = 0 := by
  simp [barrier]

/-- 抛物线对称性：以 `x = lam` 为轴（`(lam - x)² = (lam - (2lam - x))²`）。
`hlam : lam ≠ 0` 是**显式物理前提**（重组能非零）；实测证明中不需要它 ——
除零约定 `x / 0 = 0` 使 `lam = 0` 时两端同为 `0`。

English: Parabolic symmetry: the axis is `x = lam` (`(lam - x)² = (lam - (2lam - x))²`).
`hlam : lam ≠ 0` is an **explicit physical hypothesis** (nonzero reorganization energy);
measurements show the proof does not need it — the division-by-zero convention `x / 0 = 0`
makes both sides equal `0` when `lam = 0`. -/
theorem barrier_symm {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) : barrier lam x = barrier lam (2 * lam - x) := by
  unfold barrier; congr 1; ring

/-- 峰值（势垒最小）：`lam > 0` 时 `x = lam` 是全局最小点（速率峰的代数内核）。

English: Peak (barrier minimum): for `lam > 0`, `x = lam` is the global minimizer (the
algebraic core of the rate peak). -/
theorem barrier_min_at_lam {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : barrier lam lam ≤ barrier lam x := by
  rw [barrier_at_lam]; unfold barrier; positivity

/-- `lam > 0`、反转区（`lam ≤ x₁ < x₂`）：势垒严格递增 —— 反转区的代数内核。
证明内核：`(lam - x₁)² < (lam - x₂)²`（`nlinarith`，由 `x₁ < x₂` 且两者 ≥ `lam`），
再以正分母 `4 * lam` 除（`div_lt_div_of_pos_right`）。

English: `lam > 0`, inverted region (`lam ≤ x₁ < x₂`): the barrier is strictly increasing
— the algebraic core of the inverted region. Proof kernel: `(lam - x₁)² < (lam - x₂)²`
(`nlinarith`, from `x₁ < x₂` with both ≥ `lam`), then divide by the positive denominator
`4 * lam` (`div_lt_div_of_pos_right`). -/
theorem barrier_mono_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) : barrier lam x₁ < barrier lam x₂ := by
  have h4 : (0 : ℝ) < 4 * lam := by positivity
  have hsq : (lam - x₁) ^ 2 < (lam - x₂) ^ 2 := by nlinarith
  exact div_lt_div_of_pos_right hsq h4

/-- `lam > 0`、正常区（`0 ≤ x₁ < x₂ ≤ lam`）：势垒严格递减。
`h₁ : 0 ≤ x₁` 是**显式物理前提**（驱动力非负），但**证明未使用**它（unused；`hlam`、`h₂`、`h₃`
已足以推出结论）。注意它**并非**由 `h₂`、`h₃` 蕴含 —— **内核已验证的反例**（同文件头）：
`lam = 1, x₁ = -5, x₂ = -4` 满足 `0 < lam`、`x₁ < x₂`、`x₂ ≤ lam`，却使 `0 ≤ x₁` 为假。
按 statement-first，语句与权威骨架逐字一致，故该前提**保留不动**。

English: `lam > 0`, normal region (`0 ≤ x₁ < x₂ ≤ lam`): the barrier is strictly decreasing.
`h₁ : 0 ≤ x₁` is an **explicit physical hypothesis** (nonnegative driving force), but the
**proof does not use** it (unused; `hlam`, `h₂`, `h₃` already suffice to derive the
conclusion). Note that it is **not** implied by `h₂`, `h₃` — **a kernel-verified
counterexample** (same as the file header): `lam = 1, x₁ = -5, x₂ = -4` satisfies
`0 < lam`, `x₁ < x₂`, `x₂ ≤ lam`, yet makes `0 ≤ x₁` false. By statement-first, the
statement is verbatim identical to the authoritative skeleton, so this hypothesis is
**left untouched**. -/
theorem barrier_antitone_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁ := by
  have h4 : (0 : ℝ) < 4 * lam := by positivity
  have hsq : (lam - x₂) ^ 2 < (lam - x₁) ^ 2 := by nlinarith
  exact div_lt_div_of_pos_right hsq h4

/-- `lam < 0`：反转区内方向**反转**（势垒递减）—— M4a 锐利性的必要分支。
平方项仍随 `x` 严格递增，但分母 `4 * lam` 为负使不等号翻转：
用 `div_lt_div_right_of_neg : c < 0 → (a / c < b / c ↔ b < a)`（**iff，右侧顺序反转**；
`div_lt_div_of_neg_right` 在 mathlib v4.17.0 中不存在）。

English: `lam < 0`: inside the inverted region the direction is **reversed** (the barrier
decreases) — an essential branch for M4a sharpness. The square term still strictly
increases in `x`, but the negative denominator `4 * lam` flips the inequality: use
`div_lt_div_right_of_neg : c < 0 → (a / c < b / c ↔ b < a)` (**iff, with the order
reversed on the right**; `div_lt_div_of_neg_right` does not exist in mathlib v4.17.0). -/
theorem barrier_antitone_of_neg {lam : ℝ} (hlam : lam < 0) {x₁ x₂ : ℝ}
    (h₁ : lam < x₁) (h₂ : x₁ < x₂) : barrier lam x₂ < barrier lam x₁ := by
  have h4 : 4 * lam < 0 := by linarith
  have hsq : (lam - x₁) ^ 2 < (lam - x₂) ^ 2 := by nlinarith
  unfold barrier
  exact (div_lt_div_right_of_neg h4).mpr hsq

/-- `lam = 0` 的退化：除零约定 `x / 0 = 0` 使势垒恒为零 ——
M4a 锐利性"`lam > 0` 不可去"的另一必要分支（此时速率恒为 `A`）。

English: The degenerate case `lam = 0`: the division-by-zero convention `x / 0 = 0` makes
the barrier identically zero — the other essential branch for M4a sharpness ("`lam > 0`
cannot be dropped") (the rate is constantly `A` in that case). -/
theorem barrier_zero_lam (x : ℝ) : barrier 0 x = 0 := by
  simp [barrier]

/-- 结构定理：`lam > 0`（反转区增 / 正常区减）、`lam < 0`（反转区减）、`lam = 0`（恒零）
四种情形**穷尽** —— 直接由前四条组装，`lam = 0` 支用 `subst` 把 `barrier 0` 归约到
`barrier_zero_lam`。

English: Structure theorem: `lam > 0` (increasing in the inverted region / decreasing in
the normal region), `lam < 0` (decreasing in the inverted region), `lam = 0` (identically
zero) — the four cases are **exhaustive** — assembled directly from the first four lemmas,
with the `lam = 0` branch using `subst` to reduce `barrier 0` to `barrier_zero_lam`. -/
theorem barrier_mono_cases (lam : ℝ) :
    (0 < lam → ∀ x₁ x₂ : ℝ, lam ≤ x₁ → x₁ < x₂ → barrier lam x₁ < barrier lam x₂) ∧
    (0 < lam → ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ lam → barrier lam x₂ < barrier lam x₁) ∧
    (lam < 0 → ∀ x₁ x₂ : ℝ, lam < x₁ → x₁ < x₂ → barrier lam x₂ < barrier lam x₁) ∧
    (lam = 0 → ∀ x : ℝ, barrier lam x = 0) :=
  ⟨fun h x₁ x₂ h₁ h₂ => barrier_mono_of_pos h h₁ h₂,
   fun h x₁ x₂ h₁ h₂ h₃ => barrier_antitone_of_pos h h₁ h₂ h₃,
   fun h x₁ x₂ h₁ h₂ => barrier_antitone_of_neg h h₁ h₂,
   fun h x => by subst h; exact barrier_zero_lam x⟩

end PhotoLean.Marcus
