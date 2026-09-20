/-
prover_a 的 M4a 临时探针（`PhotoLean/Marcus/Sharp.lean`）。

**与 lead 探针的关键差别**：这里 `import` 的是**真实模块**
（`PhotoLean.Marcus.Barrier` + `PhotoLean.Marcus.Rate`），而不是本地重定义 ——
即验证的是"真实 `barrier_mono_of_pos` / `barrier_antitone_of_pos` /
`barrier_antitone_of_neg` / `barrier_zero_lam` / `rate_pos` / `rate_gt_of_barrier_lt`
能按预期组装出 M4a 的五条定理"，避免"探针里能过、真实模块里签名对不上"。

命名空间用 `SharpScratch`，避免与交付文件 `PhotoLean/Marcus/Sharp.lean` 的同名常量冲突。

运行：`proofs/scripts/lake env lean theories/Marcus/probes/marcus-prover_a3-scratch.lean`

English: prover_a's temporary M4a probe (for `PhotoLean/Marcus/Sharp.lean`).

**Key difference from the lead probe**: what is `import`ed here are the **real modules**
(`PhotoLean.Marcus.Barrier` + `PhotoLean.Marcus.Rate`) rather than local redefinitions —
that is, what is checked is whether the real `barrier_mono_of_pos` / `barrier_antitone_of_pos` /
`barrier_antitone_of_neg` / `barrier_zero_lam` / `rate_pos` / `rate_gt_of_barrier_lt`
assemble as intended into the five theorems of M4a, so as to avoid the situation where "it passes in the probe
but the signatures do not line up in the real module".

The namespace `SharpScratch` is used to avoid clashing with same-named constants in the delivered file
`PhotoLean/Marcus/Sharp.lean`.

Run: `proofs/scripts/lake env lean theories/Marcus/probes/marcus-prover_a3-scratch.lean`
-/

import PhotoLean.Marcus.Barrier
import PhotoLean.Marcus.Rate
import PhotoLean.Marcus.Sharp

namespace PhotoLean.Marcus.SharpScratch

/-! ## 1. 两条描述定理（只依赖 M2 + M3 的现成件，各 1 行）

English: ## 1. The two description theorems (depending only on the ready-made pieces from M2 + M3; one line each) -/

theorem inverted_descriptor_holds {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) : InvertedDescriptor A lam kB T :=
  fun x₁ x₂ h₁ h₂ =>
    rate_gt_of_barrier_lt (x := x₁) (y := x₂) hA hkT (barrier_mono_of_pos hlam (le_of_lt h₁) h₂)

theorem normal_descriptor_holds {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) : NormalDescriptor A lam kB T :=
  fun x₁ x₂ h₀ h₁ h₂ =>
    rate_gt_of_barrier_lt (x := x₂) (y := x₁) hA hkT (barrier_antitone_of_pos hlam h₀ h₁ h₂)

/-! ## 2. 必要性的三块内核

English: ## 2. The three core blocks of the necessity argument -/

/-- 速率处处正 ⇒ `A > 0`：取 `x = lam`，`0 < A * exp u` 且 `exp u > 0`。
注意必须用 `pos_of_mul_pos_left`（取**左**因子；用 `_right` 会 type mismatch，
见 proofs/API-NOTES.md 记录 D-2）。

English: the rate is positive everywhere ⇒ `A > 0`: take `x = lam`, so that `0 < A * exp u` while `exp u > 0`.
Note that `pos_of_mul_pos_left` must be used (it takes the **left** factor; using `_right` gives a type mismatch,
see record D-2 in proofs/API-NOTES.md).--/
theorem sharp_A_pos {A lam kB T : ℝ} (hpos : ∀ x, 0 < rate A lam kB T x) : 0 < A := by
  have h := hpos lam
  unfold rate at h
  exact pos_of_mul_pos_left h (le_of_lt (Real.exp_pos _))

/-- `lam < 0` 分支：反转区内 `barrier` 递减 ⇒ `rate` 递增，与描述方向矛盾。

English: the `lam < 0` branch: inside the inverted region `barrier` is decreasing ⇒ `rate` is increasing, which contradicts the direction required by the descriptor.--/
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

/-- `lam = 0` 分支：除零约定使势垒恒为 0 ⇒ 速率恒为 `A` ⇒ 严格不等式退化为 `A < A`。
**不需要任何正性前提**（`hkB` / `hT` / `hA` 都不参与）。

English: the `lam = 0` branch: the division-by-zero convention makes the barrier identically 0 ⇒ the rate
is identically `A` ⇒ the strict inequality degenerates to `A < A`.
**No positivity hypothesis is needed** (none of `hkB` / `hT` / `hA` takes part).--/
theorem sharp_lam_pos_of_eq {A kB T : ℝ} (hdesc : InvertedDescriptor A 0 kB T) : False := by
  have hrate : ∀ x : ℝ, rate A 0 kB T x = A := by
    intro x
    unfold rate
    rw [barrier_zero_lam]
    simp
  have hd := hdesc 1 2 (by norm_num) (by norm_num)
  rw [hrate 2, hrate 1] at hd
  exact lt_irrefl A hd

/-- 三分组装：`lam < 0` / `lam = 0` 两支矛盾，第三支即结论。

English: trichotomy assembly: the two branches `lam < 0` / `lam = 0` are contradictory, so the third branch is the conclusion.--/
theorem sharp_lam_pos {A lam kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hA : 0 < A)
    (hdesc : InvertedDescriptor A lam kB T) : 0 < lam := by
  rcases lt_trichotomy lam 0 with h | h | h
  · exact (sharp_lam_pos_of_lt hkB hT hA hdesc h).elim
  · subst h; exact (sharp_lam_pos_of_eq hdesc).elim
  · exact h

/-! ## 3. 五条交付定理

English: ## 3. The five delivered theorems -/

/-- 锐利刻画：正性前提 `0 < kB`、`0 < T` 下，⟺ 成立。

English: sharp characterization: under the positivity hypotheses `0 < kB` and `0 < T` the equivalence holds.--/
theorem descriptor_sharp {kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (A lam : ℝ) :
    ((∀ x : ℝ, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T) ↔ 0 < A ∧ 0 < lam := by
  constructor
  · rintro ⟨hpos, hdesc⟩
    have hA := sharp_A_pos hpos
    exact ⟨hA, sharp_lam_pos hkB hT hA hdesc⟩
  · rintro ⟨hA, hlam⟩
    exact ⟨fun x => rate_pos hA x, inverted_descriptor_holds hA hlam (mul_pos hkB hT)⟩

theorem descriptor_fails_of_nonpos_lam {A kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T)
    (hA : 0 < A) {lam : ℝ} (hlam : lam ≤ 0) : ¬ InvertedDescriptor A lam kB T :=
  fun hdesc => absurd (sharp_lam_pos hkB hT hA hdesc) (not_lt.mpr hlam)

/-- 拉伸目标：非物理分支 `A < 0 ∧ lam < 0`。`barrier` 递减 ⇒ `exp` 递增
⇒ 乘**负**前置因子后递减 ⇒ 描述重新成立（"速率正性"前提不可去的证据）。

English: stretched goal: the unphysical branch `A < 0 ∧ lam < 0`. `barrier` decreasing ⇒ `exp` increasing
⇒ after multiplication by the **negative** prefactor it is decreasing again ⇒ the descriptor holds once more (evidence that the "positivity of the rate" hypothesis cannot be dropped).--/
theorem inverted_descriptor_holds_of_neg {A lam kB T : ℝ} (hA : A < 0) (hkT : 0 < kB * T)
    (hlam : lam < 0) : InvertedDescriptor A lam kB T := by
  intro x₁ x₂ h₁ h₂
  have hb : barrier lam x₂ < barrier lam x₁ := barrier_antitone_of_neg hlam h₁ h₂
  have hu : -(barrier lam x₁) / (kB * T) < -(barrier lam x₂) / (kB * T) :=
    div_lt_div_of_pos_right (by linarith) hkT
  have hexp := Real.exp_lt_exp.mpr hu
  unfold rate
  exact mul_lt_mul_of_neg_left hexp hA

/-! ## 4. 分支覆盖自查（`lam = 0` 支是否真被单独覆盖）

English: ## 4. Self-check of branch coverage (is the `lam = 0` branch really covered as a separate case) -/

-- `sharp_lam_pos_of_eq` 的签名里**没有** `hkB` / `hT` / `hA` —— 它确实只看 `barrier 0 x = 0`。
-- English: the signature of `sharp_lam_pos_of_eq` contains **no** `hkB` / `hT` / `hA` — it really only looks at `barrier 0 x = 0`.
#check @sharp_lam_pos_of_eq
-- 若 `lam = 0` 支被 `lam < 0` 支"顺带吃掉"，下面这条（无正性前提）就不该存在：
-- English: if the `lam = 0` branch were "swallowed along the way" by the `lam < 0` branch, the item below (which has no positivity hypothesis) should not exist:
example {A kB T : ℝ} (hdesc : InvertedDescriptor A 0 kB T) : False := sharp_lam_pos_of_eq hdesc

end PhotoLean.Marcus.SharpScratch

/-! ## 5. 对**已交付** `Sharp.lean` 的分支覆盖取证（verifier 可复跑）

交付后再跑这一节：它针对真实模块（`import PhotoLean.Marcus.Sharp`）取证，
回答 lead 的复核要求 ——"`descriptor_sharp` 的 `lam = 0` 那一支是否真被覆盖"。

English: ## 5. Branch-coverage evidence for the **already delivered** `Sharp.lean` (the verifier can re-run this section)
This section is run only after delivery: it collects evidence about the real module (`import PhotoLean.Marcus.Sharp`),
answering the review request from lead — "is that `lam = 0` branch of `descriptor_sharp` really covered?" -/

namespace PhotoLean.Marcus.SharpEvidence

-- 证据 1：`lam = 0` 支的**类型里没有任何正性前提**（`0 < kB` / `0 < T` / `0 < A`
-- 都不出现）—— 它只可能由 `barrier_zero_lam`（除零约定）推出，
-- 不可能被 `lam < 0` 支顺带得到（后者必须吃一个 `hlt : lam < 0`）。
-- （注意：`#check` / `#print` 不能紧跟文档注释，会报 `unexpected token`。）
-- English: Evidence 1: **no positivity hypothesis occurs anywhere in the type** of the `lam = 0` branch
-- (`0 < kB` / `0 < T` / `0 < A` do not appear) — it can only be derived from `barrier_zero_lam`
-- (the division-by-zero convention), and it cannot be obtained along the way from the `lam < 0` branch
-- (the latter has to consume an `hlt : lam < 0`).
-- (Note: `#check` / `#print` cannot directly follow a doc comment, otherwise `unexpected token` is reported.)
#check @PhotoLean.Marcus.sharp_lam_pos_of_eq

/-- 证据 2：`descriptor_fails_of_nonpos_lam` 在 **`lam = 0`** 处可直接实例化 ——
内核必须真的走 `sharp_lam_pos` 的中间分支才能造出这个证明项。

English: Evidence 2: `descriptor_fails_of_nonpos_lam` can be instantiated directly at **`lam = 0`** — the kernel
really has to walk the middle branch of `sharp_lam_pos` in order to build this proof term. -/
example : ¬ InvertedDescriptor (1 : ℝ) 0 1 1 :=
  descriptor_fails_of_nonpos_lam (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- 证据 3：必要性主引理的证明项里**必须**同时出现三支的引用
-- （`sharp_lam_pos_of_lt` / `sharp_lam_pos_of_eq` 与 `lt_trichotomy`）。
-- English: Evidence 3: the proof term of the main necessity lemma **must** mention all three branches at once
-- (`sharp_lam_pos_of_lt` / `sharp_lam_pos_of_eq` together with `lt_trichotomy`).
#print PhotoLean.Marcus.sharp_lam_pos

/-- 证据 4（物理落点）：非物理分支满足描述，但速率处处非正 ——
故 `descriptor_sharp` 里的合取项"速率处处为正"不可删。

English: Evidence 4 (the physical bottom line): the unphysical branch satisfies the descriptor, yet the rate is
nowhere positive — hence the conjunct "the rate is positive everywhere" in `descriptor_sharp` cannot be deleted. -/
example : InvertedDescriptor (-1) (-1) 1 1 :=
  inverted_descriptor_holds_of_neg (by norm_num) (by norm_num) (by norm_num)

example : ¬ (∀ x : ℝ, 0 < rate (-1) (-1) 1 1 x) := by
  intro h
  have h0 := h 0
  have hneg : rate (-1) (-1) 1 1 0 < 0 := by
    unfold rate
    have := Real.exp_pos (-(barrier (-1) 0) / (1 * 1))
    linarith
  linarith

end PhotoLean.Marcus.SharpEvidence
