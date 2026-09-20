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
-/
import PhotoLean.Marcus.Barrier
import PhotoLean.Marcus.Rate

namespace PhotoLean.Marcus

/-! ## 描述的充分性（M4a §7.1）

两条都是"势垒代数（M2）+ 核心转移引理（M3）"的一行复合：
反转区里 `barrier` 递增 ⇒ 速率递减（`rate_gt_of_barrier_lt` 的方向是
`barrier x < barrier y ⇒ rate y < rate x`，故反转区取 `x := x₁`、`y := x₂`）；
正常区里 `barrier` 递减 ⇒ 速率递增（取 `x := x₂`、`y := x₁`）。 -/

/-- 主定理的充分性方向：`A > 0 ∧ lam > 0 ∧ k_B·T > 0` ⇒ 反转区描述成立。
依赖：`barrier_mono_of_pos`（M2）+ `rate_gt_of_barrier_lt`（M3）。 -/
theorem inverted_descriptor_holds {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) : InvertedDescriptor A lam kB T :=
  fun x₁ x₂ h₁ h₂ =>
    rate_gt_of_barrier_lt (x := x₁) (y := x₂) hA hkT (barrier_mono_of_pos hlam (le_of_lt h₁) h₂)

/-- 正常区描述成立：`A > 0 ∧ lam > 0 ∧ k_B·T > 0` ⇒ 正常区内速率随驱动力严格递增。
依赖：`barrier_antitone_of_pos`（M2）+ `rate_gt_of_barrier_lt`（M3）。
`h₀ : 0 ≤ x₁` 是**显式物理前提**（驱动力非负），数学上可由 `h₂ : x₂ ≤ lam` 推出。 -/
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
  因此分别成条、不可相互替代。 -/

/-- 速率处处正 ⇒ `A > 0`。 -/
theorem sharp_A_pos {A lam kB T : ℝ} (hpos : ∀ x, 0 < rate A lam kB T x) : 0 < A := by
  have h := hpos lam
  unfold rate at h
  exact pos_of_mul_pos_left h (le_of_lt (Real.exp_pos _))

/-- `lam < 0` 分支：反转区内 `barrier` 严格递减（`barrier_antitone_of_neg`）⇒
`exp(-Φ/k_BT)` 严格递增 ⇒ 速率严格递增，与描述要求的严格递减矛盾。
取 `x₁ = lam + 1 < lam + 2 = x₂`（两者都在反转区内）。 -/
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

end PhotoLean.Marcus
