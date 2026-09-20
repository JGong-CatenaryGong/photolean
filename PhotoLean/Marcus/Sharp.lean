/-
PhotoLean.Marcus.Sharp — M4a 锐利刻画（Marcus 反转区，**本项目主定理的落点**）。

**语句权威**：`proofs/probes/marcus-statement-skeleton.lean` 的 M4a 段
（Sprint 0 已编译通过）。本文件 5 条定理的签名与它**逐字一致**；
证明体全部经内核检查（零占位证明、无自定义公理声明）。

**依赖**：`import PhotoLean.Marcus.Barrier`（M2 势垒代数）+ `import PhotoLean.Marcus.Rate`
（M3 速率层）。本文件**只使用** M2 的 `barrier_mono_of_pos` / `barrier_antitone_of_pos` /
`barrier_antitone_of_neg` / `barrier_zero_lam` 与 M3 的 `rate_pos` /
`rate_gt_of_barrier_lt` —— 刻意**不依赖** Sprint 3 才交付的
`normal_rate_increases` / `inverted_rate_decreases` / `rate_peak_at_lam`，
使 M4a 不被 M3 的收尾阻塞。

**本文件的物理内容（规划期发现，plan §7.1）**：只写 `InvertedDescriptor`
**不足以**刻画反转区 —— 它并不蕴含 `lam > 0`。非物理分支
`A < 0 ∧ lam < 0 ∧ 0 < kB·T` 下 `barrier` 在反转区递减、乘负前置因子后速率仍递减，
描述**形式成立**但速率是**负的**。因此把"速率处处为正"并入刻画，得到锐利形式
`(∀ x, 0 < rate … x) ∧ InvertedDescriptor …  ↔  0 < A ∧ 0 < lam`
（在物理前提 `0 < kB`、`0 < T` 下）。`inverted_descriptor_holds_of_neg` 把这条
非物理分支**保留为定理**，作为"正性前提不可去"的可检查证据。

**`descriptor_sharp` 必要性方向的分支覆盖（verifier 重点）**：
`0 < lam` 由 `sharp_lam_pos` 对 `lt_trichotomy lam 0` 的**三支**分别处理得到 ——
1. `lam < 0` → `sharp_lam_pos_of_lt`（用 `barrier_antitone_of_neg`：势垒递减使速率递增，
   与描述要求的严格递减矛盾）；
2. `lam = 0` → `sharp_lam_pos_of_eq`（**单独覆盖，不被第一支吃掉**：除零约定
   `x / 0 = 0` 使 `barrier 0 · ≡ 0`，速率恒为 `A`，取 `x₁ = 1 < 2 = x₂` 得 `A < A`；
   该分支的签名里**没有** `hkB` / `hT` / `hA`，即它只依赖 `barrier_zero_lam`）；
3. `0 < lam` → 直接取该假设。

**注**：本文件刻意不写出被 `check.sh --strict` 扫描的关键字字面量
（块注释同样在扫描范围内，写了会造成误报 FAIL）。

验收（契约 `proofs/ENGINE.yml`）：
  proofs/scripts/lake build PhotoLean.Marcus.Sharp
  proofs/scripts/check.sh --strict PhotoLean.Marcus.Sharp
  proofs/scripts/axioms.sh PhotoLean.Marcus.Sharp PhotoLean.Marcus.<theorem>

English: PhotoLean.Marcus.Sharp — M4a sharp characterization (the Marcus inverted
region, **the place where this project's main theorem lands**).

**Statement authority**: the M4a section of
`proofs/probes/marcus-statement-skeleton.lean` (already compiled in Sprint 0). The
signatures of the 5 theorems in this file are **verbatim identical** to it; all proof
bodies have been checked by the kernel (zero placeholder proofs, no custom axiom
declarations).

**Dependencies**: `import PhotoLean.Marcus.Barrier` (M2 barrier algebra) +
`import PhotoLean.Marcus.Rate` (M3 rate layer). This file **uses only** the M2 lemmas
`barrier_mono_of_pos` / `barrier_antitone_of_pos` / `barrier_antitone_of_neg` /
`barrier_zero_lam` together with the M3 lemmas `rate_pos` / `rate_gt_of_barrier_lt`
— it deliberately does **not depend** on `normal_rate_increases` /
`inverted_rate_decreases` / `rate_peak_at_lam`, which are only delivered in Sprint 3,
so that M4a is not blocked by the wrap-up of M3.

**Physical content of this file (discovered during planning, plan §7.1)**: writing only
`InvertedDescriptor` is **not enough** to characterize the inverted region — it does
not imply `lam > 0`. On the non-physical branch `A < 0 ∧ lam < 0 ∧ 0 < kB·T`, `barrier`
decreases on the inverted region, and after multiplication by the negative prefactor
the rate still decreases: the description **holds formally** while the rate is
**negative**. We therefore fold "the rate is everywhere positive" into the
characterization and obtain the sharp form
`(∀ x, 0 < rate … x) ∧ InvertedDescriptor …  ↔  0 < A ∧ 0 < lam`
(under the physical premises `0 < kB`, `0 < T`). `inverted_descriptor_holds_of_neg`
keeps this non-physical branch **as a theorem**, as checkable evidence that the
positivity premise cannot be dropped.

**Branch coverage in the necessity direction of `descriptor_sharp` (a focus point for
the verifier)**: `0 < lam` is obtained by `sharp_lam_pos`, which handles the **three
branches** of `lt_trichotomy lam 0` separately —
1. `lam < 0` → `sharp_lam_pos_of_lt` (uses `barrier_antitone_of_neg`: the barrier
   decreasing makes the rate increasing, contradicting the strict decrease required by
   the description);
2. `lam = 0` → `sharp_lam_pos_of_eq` (**covered separately, not swallowed by the first
   branch**: the division-by-zero convention `x / 0 = 0` makes `barrier 0 · ≡ 0`, so the
   rate is constantly `A`, and taking `x₁ = 1 < 2 = x₂` yields `A < A`; the signature of
   this branch has **no** `hkB` / `hT` / `hA`, i.e. it depends only on
   `barrier_zero_lam`);
3. `0 < lam` → take that hypothesis directly.

**Note**: this file deliberately does not write out the keyword literals scanned by
`check.sh --strict` (block comments are inside the scan range as well, so writing them
would cause a false-positive FAIL).

Acceptance (contract `proofs/ENGINE.yml`):
  proofs/scripts/lake build PhotoLean.Marcus.Sharp
  proofs/scripts/check.sh --strict PhotoLean.Marcus.Sharp
  proofs/scripts/axioms.sh PhotoLean.Marcus.Sharp PhotoLean.Marcus.<theorem>
-/
import PhotoLean.Marcus.Barrier
import PhotoLean.Marcus.Rate

namespace PhotoLean.Marcus

/-! ## 描述的充分性（M4a §7.1）

两条都是"势垒代数（M2）+ 核心转移引理（M3）"的一行复合：
反转区里 `barrier` 递增 ⇒ 速率递减（`rate_gt_of_barrier_lt` 的方向是
`barrier x < barrier y ⇒ rate y < rate x`，故反转区取 `x := x₁`、`y := x₂`）；
正常区里 `barrier` 递减 ⇒ 速率递增（取 `x := x₂`、`y := x₁`）。

English:

## Sufficiency of the description (M4a §7.1)

Both theorems are one-line compositions of "barrier algebra (M2) + core transition
lemma (M3)": on the inverted region `barrier` is increasing ⇒ the rate is decreasing
(the direction of `rate_gt_of_barrier_lt` is `barrier x < barrier y ⇒ rate y < rate x`,
so on the inverted region take `x := x₁`, `y := x₂`); on the normal region `barrier` is
decreasing ⇒ the rate is increasing (take `x := x₂`, `y := x₁`). -/

/-- 主定理的充分性方向：`A > 0 ∧ lam > 0 ∧ k_B·T > 0` ⇒ 反转区描述成立。
依赖：`barrier_mono_of_pos`（M2）+ `rate_gt_of_barrier_lt`（M3）。

English: the sufficiency direction of the main theorem: `A > 0 ∧ lam > 0 ∧ k_B·T > 0`
⇒ the inverted-region description holds.
Dependencies: `barrier_mono_of_pos` (M2) + `rate_gt_of_barrier_lt` (M3). -/
theorem inverted_descriptor_holds {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) : InvertedDescriptor A lam kB T :=
  fun x₁ x₂ h₁ h₂ =>
    rate_gt_of_barrier_lt (x := x₁) (y := x₂) hA hkT (barrier_mono_of_pos hlam (le_of_lt h₁) h₂)

/-- 正常区描述成立：`A > 0 ∧ lam > 0 ∧ k_B·T > 0` ⇒ 正常区内速率随驱动力严格递增。
依赖：`barrier_antitone_of_pos`（M2）+ `rate_gt_of_barrier_lt`（M3）。
`h₀ : 0 ≤ x₁` 是**显式物理前提**（驱动力非负），但**证明未使用**它（unused：`hlam`、`h₁`、`h₂` 已足以推出结论）。
注意它**并非**由其余前提蕴含 —— **内核已验证的反例**：`lam = 1, x₁ = -5, x₂ = -4` 满足 `0 < lam`、`x₁ < x₂`、`x₂ ≤ lam`，却使 `0 ≤ x₁` 为假。按 statement-first，语句与权威骨架逐字一致，故该前提**保留不动**。

English: the normal-region description holds: `A > 0 ∧ lam > 0 ∧ k_B·T > 0` ⇒ on the
normal region the rate is strictly increasing in the driving force.
Dependencies: `barrier_antitone_of_pos` (M2) + `rate_gt_of_barrier_lt` (M3).
`h₀ : 0 ≤ x₁` is an **explicit physical premise** (the driving force is nonnegative), but the
proof does **not use** it (unused: `hlam`, `h₁`, `h₂` already suffice).
Note it is **not** implied by the remaining premises — kernel-verified counterexample:
`lam = 1, x₁ = -5, x₂ = -4` satisfies `0 < lam`, `x₁ < x₂`, `x₂ ≤ lam`, yet makes `0 ≤ x₁` false.
By statement-first discipline the statement matches the authoritative skeleton verbatim, so the
premise is **kept unchanged**. -/
theorem normal_descriptor_holds {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) : NormalDescriptor A lam kB T :=
  fun x₁ x₂ h₀ h₁ h₂ =>
    rate_gt_of_barrier_lt (x := x₂) (y := x₁) hA hkT (barrier_antitone_of_pos hlam h₀ h₁ h₂)

/-! ## 必要性方向的内部内核（M4a §7.1）

`descriptor_sharp` 的 `(⟹)` 要证 `0 < A` 与 `0 < lam`。

- `0 < A`：取 `x = lam`，由 `0 < A · exp u` 与 `exp u > 0` 反推（**必须**用
  `pos_of_mul_pos_left` 取**左**因子；`pos_of_mul_pos_left` 的前提是"右因子非负"，
  写 `_right` 会 `application type mismatch` —— 见 `proofs/API-NOTES.md` 记录 D-2）。
- `0 < lam`：对 `lt_trichotomy lam 0` 三分。`lam < 0` 支与 `lam = 0` 支分别导出
  与描述矛盾的严格不等式，故只能落在 `0 < lam`。**两支的数学机制不同**
  （前者靠 `barrier_antitone_of_neg` 的方向反转，后者靠除零约定 `x / 0 = 0`），
  因此分别成条、不可相互替代。

English:

## Internal core of the necessity direction (M4a §7.1)

The `(⟹)` direction of `descriptor_sharp` has to prove `0 < A` and `0 < lam`.

- `0 < A`: take `x = lam` and reason backwards from `0 < A · exp u` and `exp u > 0`
  (one **must** use `pos_of_mul_pos_left` to extract the **left** factor; the premise of
  `pos_of_mul_pos_left` is "the right factor is nonnegative", so writing `_right` gives
  an `application type mismatch` — see `proofs/API-NOTES.md` record D-2).
- `0 < lam`: split `lt_trichotomy lam 0` into three cases. The `lam < 0` case and the
  `lam = 0` case each derive a strict inequality contradicting the description, so only
  `0 < lam` can remain. **The two cases work by different mathematical mechanisms**
  (the former relies on the direction reversal of `barrier_antitone_of_neg`, the latter
  on the division-by-zero convention `x / 0 = 0`), hence they are stated as separate
  lemmas and cannot replace one another. -/

/-- 速率处处正 ⇒ `A > 0`。

English: an everywhere-positive rate ⇒ `A > 0`. -/
theorem sharp_A_pos {A lam kB T : ℝ} (hpos : ∀ x, 0 < rate A lam kB T x) : 0 < A := by
  have h := hpos lam
  unfold rate at h
  exact pos_of_mul_pos_left h (le_of_lt (Real.exp_pos _))

/-- `lam < 0` 分支：反转区内 `barrier` 严格递减（`barrier_antitone_of_neg`）⇒
`exp(-Φ/k_BT)` 严格递增 ⇒ 速率严格递增，与描述要求的严格递减矛盾。
取 `x₁ = lam + 1 < lam + 2 = x₂`（两者都在反转区内）。

English: the `lam < 0` branch: on the inverted region `barrier` is strictly decreasing
(`barrier_antitone_of_neg`) ⇒ `exp(-Φ/k_BT)` is strictly increasing ⇒ the rate is
strictly increasing, contradicting the strict decrease required by the description.
Take `x₁ = lam + 1 < lam + 2 = x₂` (both lie in the inverted region). -/
theorem sharp_lam_pos_of_lt {A lam kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hA : 0 < A)
    (hdesc : InvertedDescriptor A lam kB T) (hlt : lam < 0) : False := by
  have hkT : 0 < kB * T := mul_pos hkB hT
  have hb : barrier lam (lam + 2) < barrier lam (lam + 1) :=
    barrier_antitone_of_neg hlt (by linarith) (by linarith)
  have hu : -(barrier lam (lam + 1)) / (kB * T) < -(barrier lam (lam + 2)) / (kB * T) :=
    div_lt_div_of_pos_right (by linarith) hkT
  have hexp := Real.exp_lt_exp.mpr hu
  have hrate : rate A lam kB T (lam + 1) < rate A lam kB T (lam + 2) := by
    unfold rate
    exact mul_lt_mul_of_pos_left hexp hA
  have hd := hdesc (lam + 1) (lam + 2) (by linarith) (by linarith)
  exact absurd hd (not_lt.mpr (le_of_lt hrate))

/-- `lam = 0` 分支（**锐利性最易漏的一支**）：除零约定 `x / 0 = 0` 使
`barrier 0 x = 0`（`barrier_zero_lam`），故速率恒为 `A · exp 0 = A`；
取 `x₁ = 1 < 2 = x₂` 得描述要求的 `A < A`，矛盾。

**与 `sharp_lam_pos_of_lt` 的机制完全不同**（不涉及任何单调性/序），
且本条的签名里**没有** `hkB` / `hT` / `hA` —— 它只依赖 `barrier_zero_lam`，
不可能被 `lam < 0` 支替代。这正是 verifier 要复核的点。

English: the `lam = 0` branch (**the branch most easily missed for sharpness**): the
division-by-zero convention `x / 0 = 0` gives `barrier 0 x = 0` (`barrier_zero_lam`),
so the rate is constantly `A · exp 0 = A`; taking `x₁ = 1 < 2 = x₂` yields the `A < A`
required by the description, a contradiction.

This is **completely different in mechanism** from `sharp_lam_pos_of_lt` (no
monotonicity or order is involved), and the signature of this lemma has **no** `hkB` /
`hT` / `hA` — it depends only on `barrier_zero_lam` and cannot possibly be replaced by
the `lam < 0` branch. This is exactly the point the verifier has to re-check. -/
theorem sharp_lam_pos_of_eq {A kB T : ℝ} (hdesc : InvertedDescriptor A 0 kB T) : False := by
  have hrate : ∀ x : ℝ, rate A 0 kB T x = A := by
    intro x
    unfold rate
    rw [barrier_zero_lam]
    simp
  have hd := hdesc 1 2 (by norm_num) (by norm_num)
  rw [hrate 2, hrate 1] at hd
  exact lt_irrefl A hd

/-- 必要性内核汇总：描述成立且速率为正 ⇒ `lam > 0`。
对 `lt_trichotomy lam 0` 的**三支**分别处理（`lam < 0` 与 `lam = 0` 两支各自矛盾，
第三支即结论），不经由 `le_antisymm` 之类的间接路线 —— 保证 `lam = 0` 是真分支。

English: summary of the necessity core: if the description holds and the rate is
positive, then `lam > 0`. The **three branches** of `lt_trichotomy lam 0` are handled
separately (the `lam < 0` and `lam = 0` branches are each contradictory, and the third
branch is the conclusion), without an indirect route such as `le_antisymm` — which
guarantees that `lam = 0` is a genuine branch. -/
theorem sharp_lam_pos {A lam kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hA : 0 < A)
    (hdesc : InvertedDescriptor A lam kB T) : 0 < lam := by
  rcases lt_trichotomy lam 0 with h | h | h
  · exact (sharp_lam_pos_of_lt hkB hT hA hdesc h).elim
  · subst h; exact (sharp_lam_pos_of_eq hdesc).elim
  · exact h

/-! ## 锐利刻画与失效形态（M4a §7.1）

English:

## Sharp characterization and failure mode (M4a §7.1) -/

/-- **锐利刻画（本项目主定理的成立条件）**：在物理正性前提 `0 < k_B`、`0 < T` 下，
"速率处处为正 **且** 反转区描述成立" **⟺** `0 < A ∧ 0 < lam`。

- `(⟸)`：`rate_pos`（M3）+ `inverted_descriptor_holds`（本文件）；
- `(⟹)`：`sharp_A_pos` 得 `0 < A`，再 `sharp_lam_pos` 得 `0 < lam`
  （后者内部覆盖 `lam < 0` 与 `lam = 0` 两支）。

**为什么"速率处处为正"不可去**：见文件头与 `inverted_descriptor_holds_of_neg` ——
非物理分支 `A < 0 ∧ lam < 0` 同样满足 `InvertedDescriptor`。

English: **the sharp characterization (the condition under which this project's main
theorem holds)**: under the physical positivity premises `0 < k_B`, `0 < T`, "the rate
is everywhere positive **and** the inverted-region description holds" **⟺**
`0 < A ∧ 0 < lam`.

- `(⟸)`: `rate_pos` (M3) + `inverted_descriptor_holds` (this file);
- `(⟹)`: `sharp_A_pos` gives `0 < A`, then `sharp_lam_pos` gives `0 < lam` (the latter
  internally covers the `lam < 0` and `lam = 0` branches).

**Why "the rate is everywhere positive" cannot be dropped**: see the file header and
`inverted_descriptor_holds_of_neg` — the non-physical branch `A < 0 ∧ lam < 0` also
satisfies `InvertedDescriptor`. -/
theorem descriptor_sharp {kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (A lam : ℝ) :
    ((∀ x : ℝ, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T) ↔ 0 < A ∧ 0 < lam := by
  constructor
  · rintro ⟨hpos, hdesc⟩
    have hA := sharp_A_pos hpos
    exact ⟨hA, sharp_lam_pos hkB hT hA hdesc⟩
  · rintro ⟨hA, hlam⟩
    exact ⟨fun x => rate_pos hA x, inverted_descriptor_holds hA hlam (mul_pos hkB hT)⟩

/-- 必要性的"失效"形态：`lam ≤ 0` 时描述必然失效（在物理正性前提 `0 < k_B`、`0 < T`
与速率正性前提 `0 < A` 下）—— 即 `descriptor_sharp` 必要性方向的直接推论。

English: the "failure" form of necessity: when `lam ≤ 0` the description necessarily
fails (under the physical positivity premises `0 < k_B`, `0 < T` and the rate
positivity premise `0 < A`) — i.e. a direct corollary of the necessity direction of
`descriptor_sharp`. -/
theorem descriptor_fails_of_nonpos_lam {A kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T)
    (hA : 0 < A) {lam : ℝ} (hlam : lam ≤ 0) : ¬ InvertedDescriptor A lam kB T :=
  fun hdesc => absurd (sharp_lam_pos hkB hT hA hdesc) (not_lt.mpr hlam)

/-! ## 非物理分支（拉伸目标，M4a §7.1）

English:

## Non-physical branch (stretch goal, M4a §7.1) -/

/-- **[拉伸] 非物理分支确实满足描述** —— "速率正性"前提不可去的可检查证据：
`A < 0 ∧ lam < 0 ∧ 0 < k_B·T` 时，反转区内 `barrier` **递减**
（`barrier_antitone_of_neg`）⇒ `exp(-Φ/k_BT)` **递增** ⇒ 乘**负**前置因子 `A`
后速率**递减**，于是 `InvertedDescriptor` 成立，但速率处处**非正**（物理上不可采纳）。
与 `descriptor_sharp` 合起来说明：`(∀ x, 0 < rate … x)` 这一合取项不可删。

English: **[stretch] the non-physical branch really does satisfy the description** —
checkable evidence that the "rate positivity" premise cannot be dropped: when
`A < 0 ∧ lam < 0 ∧ 0 < k_B·T`, on the inverted region `barrier` is **decreasing**
(`barrier_antitone_of_neg`) ⇒ `exp(-Φ/k_BT)` is **increasing** ⇒ after multiplication by
the **negative** prefactor `A` the rate **decreases**, so `InvertedDescriptor` holds,
yet the rate is everywhere **nonpositive** (physically unacceptable). Together with
`descriptor_sharp` this shows that the conjunct `(∀ x, 0 < rate … x)` cannot be deleted. -/
theorem inverted_descriptor_holds_of_neg {A lam kB T : ℝ} (hA : A < 0) (hkT : 0 < kB * T)
    (hlam : lam < 0) : InvertedDescriptor A lam kB T := by
  intro x₁ x₂ h₁ h₂
  have hb : barrier lam x₂ < barrier lam x₁ := barrier_antitone_of_neg hlam h₁ h₂
  have hu : -(barrier lam x₁) / (kB * T) < -(barrier lam x₂) / (kB * T) :=
    div_lt_div_of_pos_right (by linarith) hkT
  have hexp := Real.exp_lt_exp.mpr hu
  unfold rate
  exact mul_lt_mul_of_neg_left hexp hA

end PhotoLean.Marcus
