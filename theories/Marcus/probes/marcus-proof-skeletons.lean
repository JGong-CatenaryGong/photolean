/-
  marcus-proof-skeletons.lean — 语句权威的**证明体**（proof bodies）

  ⚠️ **语句权威是 `marcus-statement-skeleton.lean`**（lead 维护，本文件不复制它的注释）。
     本文件**逐字复制它的定理签名**，只补上证明体，目的是给 prover_a..d 提供
     "已实测通过、可直接搬进 `PhotoLean/Marcus/*.lean`"的证明骨架。
     签名若与 `marcus-statement-skeleton.lean` 不一致，**以那个文件为准**。

  与 `marcus-statement-skeleton.lean` 的关系：本文件 = 那份骨架去掉所有 `sorry`
  后的可编译版本（M1–M5a 全覆盖）。**它不含 sorry / axiom**。

  运行命令（在仓库根目录执行）
    proofs/scripts/lake env lean theories/Marcus/probes/marcus-proof-skeletons.lean
  期望：**0 error、0 warning**（已 `set_option linter.unusedVariables false`；
        `barrier_antitone_of_pos` 的 `h₁ : 0 ≤ x₁` 是显式物理前提但数学上冗余，
        见 API-NOTES 说明）。

  校准基准：mathlib v4.17.0（lean-toolchain = leanprover/lean4:v4.17.0）
  校准日期：2026-09-20 — api_researcher（每条都独立重跑过，非照抄 lead 结论）

  English: marcus-proof-skeletons.lean — the **proof bodies** for the authoritative statements

  ⚠️ **The authoritative statements are `marcus-statement-skeleton.lean`** (maintained by the lead;
     this file does not copy its comments).
     This file **copies its theorem signatures verbatim** and adds only the proof bodies, in order
     to give prover_a..d proof skeletons that are "already measured to pass and can be moved
     straight into `PhotoLean/Marcus/*.lean`".
     If a signature disagrees with `marcus-statement-skeleton.lean`, **that file prevails**.

  Relation to `marcus-statement-skeleton.lean`: this file = that skeleton with all unfinished-proof
  placeholders removed, i.e. a compilable version (full coverage of M1–M5a). **It contains no
  unfinished proofs and no custom axiom declarations**.

  Run command (execute in the repository root)
    proofs/scripts/lake env lean theories/Marcus/probes/marcus-proof-skeletons.lean
  Expected: **0 error, 0 warning** (it already sets `set_option linter.unusedVariables false`;
        the `h₁ : 0 ≤ x₁` of `barrier_antitone_of_pos` is an explicit physical hypothesis that is
        mathematically redundant — see the note in API-NOTES).

  Calibration baseline: mathlib v4.17.0 (lean-toolchain = leanprover/lean4:v4.17.0)
  Calibration date: 2026-09-20 — api_researcher (every entry was re-run independently, not copied
  from the lead's conclusions)
-/

import Mathlib

set_option linter.unusedVariables false

namespace PhotoLean.Marcus.Skeleton

/-! ## M1 — 描述层

English: ## M1 — description layer -/

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

/-! M1 的推荐战术：`by_cases` + `rw [if_pos/if_neg]` + `simp`。
    `split_ifs <;> simp_all` 也能过 `zone_trichotomy`，但对前三条会留下
    `¬x = lam` / `lam < x` 之类 simp 推不出的目标，需手工补 `ne_of_lt` /
    `lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h2)`。

English: The recommended tactic for M1: `by_cases` + `rw [if_pos/if_neg]` + `simp`.
    `split_ifs <;> simp_all` also closes `zone_trichotomy`, but for the first three it leaves
    goals such as `¬x = lam` / `lam < x` that `simp` cannot discharge, so one must supply
    `ne_of_lt` / `lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h2)` by hand. -/

theorem zone_eq_normal_iff (lam x : ℝ) : zone lam x = Zone.normal ↔ NormalRegion lam x := by
  by_cases h : x < lam
  · unfold zone NormalRegion; rw [if_pos h]; simp [h]
  · unfold zone NormalRegion; rw [if_neg h]
    by_cases h2 : x = lam
    · rw [if_pos h2]; simp [h2]
    · rw [if_neg h2]; simp [h, h2]

theorem zone_eq_barrierless_iff (lam x : ℝ) : zone lam x = Zone.barrierless ↔ x = lam := by
  by_cases h : x < lam
  · unfold zone; rw [if_pos h]; simp [ne_of_lt h]
  · unfold zone; rw [if_neg h]
    by_cases h2 : x = lam
    · rw [if_pos h2]; simp [h2]
    · rw [if_neg h2]; simp [h2]

theorem zone_eq_inverted_iff (lam x : ℝ) : zone lam x = Zone.inverted ↔ InvertedRegion lam x := by
  by_cases h : x < lam
  · unfold zone InvertedRegion; rw [if_pos h]; simp [not_lt.mpr h.le]
  · unfold zone InvertedRegion; rw [if_neg h]
    by_cases h2 : x = lam
    · rw [if_pos h2]; simp [h2]
    · rw [if_neg h2]
      have hlt : lam < x := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h2)
      simp [h, hlt]

theorem zone_trichotomy (lam x : ℝ) :
    zone lam x = Zone.normal ∨ zone lam x = Zone.barrierless ∨ zone lam x = Zone.inverted := by
  unfold zone
  split_ifs <;> simp

/-! ## M2 — 势垒代数

  统一模式：`unfold barrier` → 用 `div_lt_div_iff_of_pos_right` 去分母（lam>0）
  → 裸 `nlinarith`。`lam < 0` 时先 `4*lam = -(4*(-lam))` 再用 `div_neg` +
  `neg_lt_neg_iff` 翻成正分母（**不存在 `div_lt_div_iff_of_neg_right`**）。
  这些证明体由 api_researcher 独立重跑确认。

  English: ## M2 — barrier algebra

  Uniform pattern: `unfold barrier` → clear the denominator with `div_lt_div_iff_of_pos_right`
  (lam>0) → bare `nlinarith`.
  For `lam < 0`, first rewrite `4*lam = -(4*(-lam))`, then use `div_neg` + `neg_lt_neg_iff` to
  turn it into a positive denominator (**`div_lt_div_iff_of_neg_right` does not exist**).
  These proof bodies were confirmed by independent re-runs by api_researcher.
-/

theorem barrier_nonneg {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : 0 ≤ barrier lam x := by
  unfold barrier; positivity

theorem barrier_at_lam (lam : ℝ) : barrier lam lam = 0 := by
  unfold barrier; ring

theorem barrier_symm {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) : barrier lam x = barrier lam (2 * lam - x) := by
  unfold barrier; ring_nf

theorem barrier_min_at_lam {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : barrier lam lam ≤ barrier lam x := by
  unfold barrier
  rw [div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith [sq_nonneg (lam - x)]

theorem barrier_mono_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) : barrier lam x₁ < barrier lam x₂ := by
  unfold barrier
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith

theorem barrier_antitone_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁ := by
  unfold barrier
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith

theorem barrier_antitone_of_neg {lam : ℝ} (hlam : lam < 0) {x₁ x₂ : ℝ}
    (h₁ : lam < x₁) (h₂ : x₁ < x₂) : barrier lam x₂ < barrier lam x₁ := by
  unfold barrier
  rw [show (4 : ℝ) * lam = -(4 * (-lam)) by ring, div_neg, div_neg, neg_lt_neg_iff]
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * (-lam))]
  nlinarith

theorem barrier_zero_lam (x : ℝ) : barrier 0 x = 0 := by
  unfold barrier; ring

theorem barrier_mono_cases (lam : ℝ) :
    (0 < lam → ∀ x₁ x₂ : ℝ, lam ≤ x₁ → x₁ < x₂ → barrier lam x₁ < barrier lam x₂) ∧
    (0 < lam → ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ lam → barrier lam x₂ < barrier lam x₁) ∧
    (lam < 0 → ∀ x₁ x₂ : ℝ, lam < x₁ → x₁ < x₂ → barrier lam x₂ < barrier lam x₁) ∧
    (lam = 0 → ∀ x : ℝ, barrier lam x = 0) :=
  ⟨fun h x₁ x₂ h₁ h₂ => barrier_mono_of_pos h h₁ h₂,
   fun h x₁ x₂ h₁ h₂ h₃ => barrier_antitone_of_pos h h₁ h₂ h₃,
   fun h x₁ x₂ h₁ h₂ => barrier_antitone_of_neg h h₁ h₂,
   fun h x => by subst h; exact barrier_zero_lam x⟩

/-! ## M3 — 速率层

  核心引理 `rate_gt_of_barrier_lt` 的链条：
  取负 (linarith) → 除以正数 (`div_lt_div_of_pos_right`)
  → exp 严格单调 (`Real.exp_lt_exp.2`，**它是 iff**) → 乘正数 (`mul_lt_mul_of_pos_left`).

  English: ## M3 — rate layer

  The chain of the core lemma `rate_gt_of_barrier_lt`:
  negate (linarith) → divide by a positive number (`div_lt_div_of_pos_right`)
  → strict monotonicity of exp (`Real.exp_lt_exp.2`, **it is an iff**) → multiply by a positive
  number (`mul_lt_mul_of_pos_left`).
-/

theorem rate_pos {A lam kB T : ℝ} (hA : 0 < A) (x : ℝ) : 0 < rate A lam kB T x := by
  unfold rate; positivity

theorem rate_gt_of_barrier_lt {A lam kB T : ℝ} (hA : 0 < A) (hkT : 0 < kB * T) {x y : ℝ}
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  unfold rate
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (div_lt_div_of_pos_right (by linarith) hkT)) hA

theorem rate_ratio {A lam kB T : ℝ} (hA : A ≠ 0) (hkT : kB * T ≠ 0) (x y : ℝ) :
    rate A lam kB T y / rate A lam kB T x
      = Real.exp ((barrier lam x - barrier lam y) / (kB * T)) := by
  unfold rate
  rw [mul_div_mul_left _ _ hA, ← Real.exp_sub]
  congr 1
  field_simp
  ring

theorem normal_rate_increases {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    {x₁ x₂ : ℝ} (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) :
    rate A lam kB T x₁ < rate A lam kB T x₂ :=
  rate_gt_of_barrier_lt hA hkT (barrier_antitone_of_pos hlam h₁ h₂ h₃)

theorem inverted_rate_decreases {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    {x₁ x₂ : ℝ} (h₁ : lam < x₁) (h₂ : x₁ < x₂) :
    rate A lam kB T x₂ < rate A lam kB T x₁ :=
  rate_gt_of_barrier_lt hA hkT (barrier_mono_of_pos hlam h₁.le h₂)

theorem rate_peak_at_lam {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    (x : ℝ) : rate A lam kB T x ≤ rate A lam kB T lam := by
  unfold rate
  apply mul_le_mul_of_nonneg_left _ hA.le
  rw [Real.exp_le_exp]
  exact div_le_div_of_nonneg_right (by linarith [barrier_min_at_lam hlam x]) hkT.le

/-! ## M4a — 锐利刻画

English: ## M4a — sharp characterization -/

theorem inverted_descriptor_holds {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) : InvertedDescriptor A lam kB T :=
  fun _ _ h₁ h₂ => inverted_rate_decreases hA hlam hkT h₁ h₂

theorem normal_descriptor_holds {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T) :
    NormalDescriptor A lam kB T :=
  fun _ _ h₁ h₂ h₃ => normal_rate_increases hA hlam hkT h₁ h₂ h₃

/-- 必要性的一半：速率处处正 ⇒ `A > 0`。
    ⚠️ 必须用 `pos_of_mul_pos_left`（正的因子 A 在积的**左**边）。

English: One half of necessity: the rate is positive everywhere ⇒ `A > 0`.
    ⚠️ One must use `pos_of_mul_pos_left` (the positive factor A is on the **left** of the
    product). -/
theorem sharp_A_pos {A lam kB T : ℝ} (hpos : ∀ x, 0 < rate A lam kB T x) : 0 < A := by
  have h := hpos lam
  unfold rate at h
  exact pos_of_mul_pos_left h (le_of_lt (Real.exp_pos _))

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

/-- `lam = 0` 分支：**不需要任何正性前提** —— 除零约定使势垒恒为 0，速率恒为 `A`。

English: The `lam = 0` branch: **no positivity hypothesis is needed** — the division-by-zero
    convention makes the barrier identically 0 and the rate identically `A`. -/
theorem sharp_lam_pos_of_eq {A kB T : ℝ} (hdesc : InvertedDescriptor A 0 kB T) : False := by
  have hrate : ∀ x : ℝ, rate A 0 kB T x = A := by
    intro x
    unfold rate
    rw [barrier_zero_lam]
    simp
  have hd := hdesc 1 2 (by norm_num) (by norm_num)
  rw [hrate 2, hrate 1] at hd
  exact lt_irrefl A hd

theorem sharp_lam_pos {A lam kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hA : 0 < A)
    (hdesc : InvertedDescriptor A lam kB T) : 0 < lam := by
  rcases lt_trichotomy lam 0 with h | h | h
  · exact (sharp_lam_pos_of_lt hkB hT hA hdesc h).elim
  · subst h; exact (sharp_lam_pos_of_eq hdesc).elim
  · exact h

theorem descriptor_sharp {kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (A lam : ℝ) :
    ((∀ x : ℝ, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T) ↔ 0 < A ∧ 0 < lam := by
  constructor
  · rintro ⟨hpos, hdesc⟩
    exact ⟨sharp_A_pos hpos, sharp_lam_pos hkB hT (sharp_A_pos hpos) hdesc⟩
  · rintro ⟨hA, hlam⟩
    exact ⟨rate_pos hA, inverted_descriptor_holds hA hlam (mul_pos hkB hT)⟩

/-- 锐利性必要性：`lam ≤ 0` 时描述必假（`lam < 0` 用 L5 反向；`lam = 0` 用除零约定）。

English: Sharpness, necessity direction: when `lam ≤ 0` the description must fail (for
    `lam < 0` use L5 in the reverse direction; for `lam = 0` use the division-by-zero
    convention). -/
theorem descriptor_fails_of_nonpos_lam {A kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T)
    (hA : 0 < A) {lam : ℝ} (hlam : lam ≤ 0) : ¬ InvertedDescriptor A lam kB T := by
  intro h
  have hkT : 0 < kB * T := mul_pos hkB hT
  rcases lt_or_eq_of_le hlam with hlt | heq
  · have hbar : barrier lam 1 < barrier lam 0 :=
      barrier_antitone_of_neg hlt (by linarith) (by norm_num)
    have hthis : rate A lam kB T 0 < rate A lam kB T 1 := rate_gt_of_barrier_lt hA hkT hbar
    have hbad : rate A lam kB T 1 < rate A lam kB T 0 := h 0 1 (by linarith) (by norm_num)
    linarith
  · subst heq
    have hrate : ∀ x : ℝ, rate A 0 kB T x = A := by
      intro x; unfold rate barrier; simp
    have hbad : rate A 0 kB T 2 < rate A 0 kB T 1 := h 1 2 (by norm_num) (by norm_num)
    rw [hrate 2, hrate 1] at hbad
    exact absurd hbad (lt_irrefl A)

/-- 拉伸目标（非物理分支 `A < 0, lam < 0`）：`A < 0` 使乘法翻转序。

English: A stretch goal (the non-physical branch `A < 0, lam < 0`): `A < 0` makes
    multiplication reverse the order. -/
theorem inverted_descriptor_holds_of_neg {A lam kB T : ℝ} (hA : A < 0) (hkT : 0 < kB * T)
    (hlam : lam < 0) : InvertedDescriptor A lam kB T := by
  intro x₁ x₂ hx₁ hx₂
  unfold rate
  apply mul_lt_mul_of_neg_left _ hA
  rw [Real.exp_lt_exp]
  exact div_lt_div_of_pos_right (by linarith [barrier_antitone_of_neg hlam hx₁ hx₂]) hkT

/-- **语义要点**：`InvertedDescriptor` **只在 `lam > 0` 时成立**。
    `lam < 0` 时 `barrier` 随 `x` 递减（`barrier_antitone_of_neg`），故速率随 `x` **递增**，
    与描述方向相反 —— 本定理给出机器检查的反例（`A = kB = T = 1, lam = -1`）。
    ⇒ `inverted_descriptor_holds` 的 `hlam : 0 < lam` 与
    `inverted_descriptor_holds_of_neg` 的 `hA : A < 0` **都不可删减或互换**。

English: **Semantic point**: `InvertedDescriptor` **holds only when `lam > 0`**.
    For `lam < 0`, `barrier` is decreasing in `x` (`barrier_antitone_of_neg`), hence the rate is
    **increasing** in `x`, the opposite of the direction of the description — this theorem provides
    a machine-checked counterexample (`A = kB = T = 1, lam = -1`).
    ⇒ The `hlam : 0 < lam` of `inverted_descriptor_holds` and the `hA : A < 0` of
    `inverted_descriptor_holds_of_neg` **can neither be deleted nor interchanged**. -/
theorem not_invertedDescriptor_of_neg_lam : ¬ InvertedDescriptor 1 (-1) 1 1 := by
  intro h
  have hlt : rate 1 (-1) 1 1 1 < rate 1 (-1) 1 1 0 := h 0 1 (by norm_num) (by norm_num)
  have h1 : rate 1 (-1) 1 1 1 = Real.exp 1 := by unfold rate barrier; norm_num
  have h0 : rate 1 (-1) 1 1 0 = Real.exp (1 / 4) := by unfold rate barrier; norm_num
  rw [h1, h0] at hlt
  have : (1 : ℝ) < 1 / 4 := Real.exp_lt_exp.mp hlt
  norm_num at this

/-! ## M4b — 微观充分条件

English: ## M4b — microscopic sufficient condition -/

noncomputable def lamInner (kk dq : ℝ) : ℝ := kk * dq ^ 2 / 2

noncomputable def lamOuter (dE a1 a2 R nSq epsS : ℝ) : ℝ :=
  dE ^ 2 * (1 / (2 * a1) + 1 / (2 * a2) - 1 / R) * (1 / nSq - 1 / epsS)

theorem lamInner_nonneg {kk : ℝ} (hkk : 0 ≤ kk) (dq : ℝ) : 0 ≤ lamInner kk dq := by
  unfold lamInner; positivity

theorem lamInner_pos {kk : ℝ} (hkk : 0 < kk) {dq : ℝ} (hdq : dq ≠ 0) :
    0 < lamInner kk dq := by
  unfold lamInner; positivity

theorem lamOuter_pos {dE a1 a2 R nSq epsS : ℝ} (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) : 0 < lamOuter dE a1 a2 R nSq epsS := by
  unfold lamOuter
  have h1 : 0 < 1 / (2 * a1) + 1 / (2 * a2) - 1 / R := by linarith
  have h2 : 0 < 1 / nSq - 1 / epsS := by linarith
  positivity

theorem lam_total_pos {lamIn lamOut : ℝ} (h₁ : 0 ≤ lamIn) (h₂ : 0 < lamOut) : 0 < lamIn + lamOut := by
  linarith

theorem descriptor_holds_of_microscopic {A kB T kk dq dE a1 a2 R nSq epsS : ℝ} (hA : 0 < A)
    (hkB : 0 < kB) (hT : 0 < T) (hkk : 0 ≤ kk) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    InvertedDescriptor A (lamInner kk dq + lamOuter dE a1 a2 R nSq epsS) kB T :=
  inverted_descriptor_holds hA
    (lam_total_pos (lamInner_nonneg hkk dq)
      (lamOuter_pos hdE ha1 ha2 hR hgeom hnSq hepsS hPekar))
    (mul_pos hkB hT)

/-! ## M5a — ℚ 判定层

  `zoneQ_eq_zone` 的关键：`simp only [Rat.cast_lt, Rat.cast_inj]`（**不能**用 `rw`，
  会因依值 `Decidable` 实例报 "motive is not type correct"）。

English: ## M5a — ℚ decision layer

  The key to `zoneQ_eq_zone`: `simp only [Rat.cast_lt, Rat.cast_inj]` (**one cannot** use `rw`,
  which reports "motive is not type correct" because of the dependent `Decidable` instance). -/

def zoneQ (lam x : ℚ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

def barrierQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ) := by
  unfold zoneQ zone
  simp only [Rat.cast_lt, Rat.cast_inj]

theorem zoneQ_inverted_iff (lam x : ℚ) : zoneQ lam x = Zone.inverted ↔ (lam : ℝ) < (x : ℝ) := by
  rw [zoneQ_eq_zone, zone_eq_inverted_iff]
  rfl

end PhotoLean.Marcus.Skeleton
