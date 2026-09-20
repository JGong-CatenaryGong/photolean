/-
Sprint 0 语句骨架 — Marcus 反转区（M1–M5）。

**为什么放在这里**：契约 `proofs/ENGINE.yml` 的 `SOURCE_DIRS="PhotoLean"` 会被
`check.sh --strict` 全目录扫描，源码树内不允许出现 sorry。因此 statement-first 的
骨架落在 `theories/Marcus/probes/`（不在 SOURCE_DIRS），用 `sorry` 占位，**只验证语句能编译**。

**本文件是语句的权威**（statement-first）：`PhotoLean/Marcus/*.lean` 里的定理签名
必须与本文件逐字一致；任何改动（含因 API 漂移的改动）都必须先改这里、编译通过、
记入 `proofs/API-NOTES.md`，再搬进源码树。

**命名约定（工具链约束）**：Lean 4 中 `λ` 是 lambda 关键字，**不可作标识符**。
故物理量用 ASCII：重组能 `lam`、驱动力 `x`、前置因子 `A`、`kB`、`T`、
内外层重组能 `lamIn` / `lamOut`、静态介电常数 `epsS`、折射率平方 `nSq`。

运行：
  proofs/scripts/lake env lean theories/Marcus/probes/marcus-statement-skeleton.lean
期望：只出现 "declaration uses 'sorry'" 类 warning，**无 error**。

文件末尾另有一节"风险探针"（risk probes）：它们**不含 sorry**，用于在 Sprint 0
就把两处最大风险（Real.exp 单调性的签名方向 / Rat 上的可计算判定）落实。

English:
Sprint 0 statement skeleton — the Marcus inverted region (M1–M5).

**Why it lives here**: the contract `proofs/ENGINE.yml` declares `SOURCE_DIRS="PhotoLean"`, and
`check.sh --strict` scans that whole directory tree, so no unfinished-proof placeholder may appear inside the source tree. Hence the
statement-first skeleton lives in `theories/Marcus/probes/` (outside SOURCE_DIRS), uses an unfinished-proof placeholder, and **only checks that the statements compile**.

**This file is the authority on the statements** (statement-first): the theorem signatures in `PhotoLean/Marcus/*.lean`
must agree with this file verbatim; any change (including changes forced by API drift) must first be made here, compiled, and
recorded in `proofs/API-NOTES.md`, and only then moved into the source tree.

**Naming convention (toolchain constraint)**: in Lean 4, `λ` is a lambda keyword and **cannot serve as an identifier**.
The physical quantities are therefore spelled in ASCII: reorganisation energy `lam`, driving force `x`, pre-exponential factor `A`, `kB`, `T`,
inner and outer reorganisation energies `lamIn` / `lamOut`, static dielectric constant `epsS`, squared refractive index `nSq`.

Run:
  proofs/scripts/lake env lean theories/Marcus/probes/marcus-statement-skeleton.lean
Expectation: only warnings of the "declaration uses an unfinished-proof placeholder" kind, and **no error**.

The end of the file also holds a "risk probes" section: it **contains no unfinished-proof placeholder**, and serves, already in Sprint 0,
to pin down the two biggest risks (the signature direction of `Real.exp` monotonicity / decidable evaluation over `Rat`).
-/

import Mathlib

namespace PhotoLean.Marcus.Skeleton

/-! ## M1 — 描述层（对应 PhotoLean/Marcus/Basic.lean）

English: ## M1 — the descriptive layer (corresponds to PhotoLean/Marcus/Basic.lean) -/

/-- 经典马库斯势垒：驱动力 `x = -ΔG°`，重组能 `lam`。

English: The classical Marcus barrier: driving force `x = -ΔG°`, reorganisation energy `lam`. --/
noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- 马库斯速率：`k = A · exp(-ΔG‡/(k_B T))`。

English: The Marcus rate: `k = A · exp(-ΔG‡/(k_B T))`. --/
noncomputable def rate (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(barrier lam x) / (kB * T))

/-- 反转区：驱动力超过重组能。

English: Inverted region: the driving force exceeds the reorganisation energy. --/
def InvertedRegion (lam x : ℝ) : Prop := lam < x

/-- 正常区：驱动力小于重组能。

English: Normal region: the driving force is below the reorganisation energy. --/
def NormalRegion (lam x : ℝ) : Prop := x < lam

/-- 反转区描述：反转区内速率随驱动力严格递减。

English: Inverted-region descriptor: within the inverted region the rate is strictly decreasing in the driving force. --/
def InvertedDescriptor (A lam kB T : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, lam < x₁ → x₁ < x₂ → rate A lam kB T x₂ < rate A lam kB T x₁

/-- 正常区描述：正常区内速率随驱动力严格递增。

English: Normal-region descriptor: within the normal region the rate is strictly increasing in the driving force. --/
def NormalDescriptor (A lam kB T : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ lam → rate A lam kB T x₁ < rate A lam kB T x₂

/-- 区域分类。

English: Zone classification. --/
inductive Zone where
  | normal
  | barrierless
  | inverted
  deriving DecidableEq, Repr

/-- 分类器。

English: The classifier. --/
noncomputable def zone (lam x : ℝ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

theorem zone_eq_normal_iff (lam x : ℝ) : zone lam x = Zone.normal ↔ NormalRegion lam x := by
  sorry

theorem zone_eq_barrierless_iff (lam x : ℝ) : zone lam x = Zone.barrierless ↔ x = lam := by
  sorry

theorem zone_eq_inverted_iff (lam x : ℝ) : zone lam x = Zone.inverted ↔ InvertedRegion lam x := by
  sorry

theorem zone_trichotomy (lam x : ℝ) :
    zone lam x = Zone.normal ∨ zone lam x = Zone.barrierless ∨ zone lam x = Zone.inverted := by
  sorry

/-! ## M2 — 势垒代数（对应 PhotoLean/Marcus/Barrier.lean）

English: ## M2 — barrier algebra (corresponds to PhotoLean/Marcus/Barrier.lean) -/

theorem barrier_nonneg {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : 0 ≤ barrier lam x := by
  sorry

theorem barrier_at_lam (lam : ℝ) : barrier lam lam = 0 := by
  sorry

theorem barrier_symm {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) : barrier lam x = barrier lam (2 * lam - x) := by
  sorry

theorem barrier_min_at_lam {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : barrier lam lam ≤ barrier lam x := by
  sorry

theorem barrier_mono_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) : barrier lam x₁ < barrier lam x₂ := by
  sorry

theorem barrier_antitone_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁ := by
  sorry

theorem barrier_antitone_of_neg {lam : ℝ} (hlam : lam < 0) {x₁ x₂ : ℝ}
    (h₁ : lam < x₁) (h₂ : x₁ < x₂) : barrier lam x₂ < barrier lam x₁ := by
  sorry

theorem barrier_zero_lam (x : ℝ) : barrier 0 x = 0 := by
  sorry

theorem barrier_mono_cases (lam : ℝ) :
    (0 < lam → ∀ x₁ x₂ : ℝ, lam ≤ x₁ → x₁ < x₂ → barrier lam x₁ < barrier lam x₂) ∧
    (0 < lam → ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ lam → barrier lam x₂ < barrier lam x₁) ∧
    (lam < 0 → ∀ x₁ x₂ : ℝ, lam < x₁ → x₁ < x₂ → barrier lam x₂ < barrier lam x₁) ∧
    (lam = 0 → ∀ x : ℝ, barrier lam x = 0) := by
  sorry

/-! ## M3 — 速率层（对应 PhotoLean/Marcus/Rate.lean）

English: ## M3 — the rate layer (corresponds to PhotoLean/Marcus/Rate.lean) -/

theorem rate_pos {A lam kB T : ℝ} (hA : 0 < A) (x : ℝ) : 0 < rate A lam kB T x := by
  sorry

theorem rate_gt_of_barrier_lt {A lam kB T : ℝ} (hA : 0 < A) (hkT : 0 < kB * T) {x y : ℝ}
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  sorry

theorem rate_ratio {A lam kB T : ℝ} (hA : A ≠ 0) (hkT : kB * T ≠ 0) (x y : ℝ) :
    rate A lam kB T y / rate A lam kB T x
      = Real.exp ((barrier lam x - barrier lam y) / (kB * T)) := by
  sorry

theorem normal_rate_increases {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    {x₁ x₂ : ℝ} (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) :
    rate A lam kB T x₁ < rate A lam kB T x₂ := by
  sorry

theorem inverted_rate_decreases {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    {x₁ x₂ : ℝ} (h₁ : lam < x₁) (h₂ : x₁ < x₂) :
    rate A lam kB T x₂ < rate A lam kB T x₁ := by
  sorry

theorem rate_peak_at_lam {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    (x : ℝ) : rate A lam kB T x ≤ rate A lam kB T lam := by
  sorry

/-! ## M4a — 锐利刻画（对应 PhotoLean/Marcus/Sharp.lean）

English: ## M4a — the sharp characterisation (corresponds to PhotoLean/Marcus/Sharp.lean) -/

theorem inverted_descriptor_holds {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) : InvertedDescriptor A lam kB T := by
  sorry

theorem normal_descriptor_holds {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T) :
    NormalDescriptor A lam kB T := by
  sorry

/-- 锐利刻画：在 `k_B > 0, T > 0` 下，"速率处处正 ∧ 描述成立" ⟺ `A > 0 ∧ lam > 0`。

English: Sharp characterisation: under `k_B > 0, T > 0`, "the rate is positive everywhere ∧ the descriptor holds" ⟺ `A > 0 ∧ lam > 0`. --/
theorem descriptor_sharp {kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (A lam : ℝ) :
    ((∀ x : ℝ, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T) ↔ 0 < A ∧ 0 < lam := by
  sorry

theorem descriptor_fails_of_nonpos_lam {A kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T)
    (hA : 0 < A) {lam : ℝ} (hlam : lam ≤ 0) : ¬ InvertedDescriptor A lam kB T := by
  sorry

/-- 拉伸目标：非物理分支（A<0, lam<0）确实满足描述 ⇒ 正性前提不可去。

English: Stretch goal: the unphysical branch (A<0, lam<0) does satisfy the descriptor ⇒ the positivity hypotheses cannot be dropped. --/
theorem inverted_descriptor_holds_of_neg {A lam kB T : ℝ} (hA : A < 0) (hkT : 0 < kB * T)
    (hlam : lam < 0) : InvertedDescriptor A lam kB T := by
  sorry

/-! ## M4b — 微观充分条件（对应 PhotoLean/Marcus/Reorg.lean）

English: ## M4b — microscopic sufficient conditions (corresponds to PhotoLean/Marcus/Reorg.lean) -/

/-- 内层重组能：力常数 × 位移平方 / 2。

English: Inner reorganisation energy: force constant × squared displacement / 2. --/
noncomputable def lamInner (kk dq : ℝ) : ℝ := kk * dq ^ 2 / 2

/-- 外层重组能（两球连续介质模型，Pekar 形式）。

English: Outer reorganisation energy (two-sphere continuum model, Pekar form). --/
noncomputable def lamOuter (dE a1 a2 R nSq epsS : ℝ) : ℝ :=
  dE ^ 2 * (1 / (2 * a1) + 1 / (2 * a2) - 1 / R) * (1 / nSq - 1 / epsS)

theorem lamInner_nonneg {kk : ℝ} (hkk : 0 ≤ kk) (dq : ℝ) : 0 ≤ lamInner kk dq := by
  sorry

theorem lamInner_pos {kk : ℝ} (hkk : 0 < kk) {dq : ℝ} (hdq : dq ≠ 0) :
    0 < lamInner kk dq := by
  sorry

theorem lamOuter_pos {dE a1 a2 R nSq epsS : ℝ} (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) : 0 < lamOuter dE a1 a2 R nSq epsS := by
  sorry

theorem lam_total_pos {lamIn lamOut : ℝ} (h₁ : 0 ≤ lamIn) (h₂ : 0 < lamOut) : 0 < lamIn + lamOut := by
  sorry

/-- 几何因子正性**可由"两球不重叠"推出**（把 `hgeom` 从假设变成推导）。
    [拉伸项；由 prover_d 交付，2026-09-20 回填骨架 —— verifier 在 M4c 验收中指出此记账缺口]

English: Positivity of the geometric factor **can be derived from "the two spheres do not overlap"** (turning `hgeom` from a hypothesis into a consequence).
    [Stretch item; delivered by prover_d, back-filled into the skeleton on 2026-09-20 — the verifier flagged this bookkeeping gap during the M4c acceptance review] --/
theorem hgeom_of_nonoverlap {a1 a2 R : ℝ} (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hRge : a1 + a2 ≤ R) : 1 / R < 1 / (2 * a1) + 1 / (2 * a2) := by
  sorry

/-- 复合定理：微观正性（内层非负 + 外层段 Pekar 正性）⇒ 反转区描述成立。

English: Composite theorem: microscopic positivity (inner energy nonnegative + Pekar positivity of the outer term) ⇒ the inverted-region descriptor holds. --/
theorem descriptor_holds_of_microscopic {A kB T kk dq dE a1 a2 R nSq epsS : ℝ} (hA : 0 < A)
    (hkB : 0 < kB) (hT : 0 < T) (hkk : 0 ≤ kk) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    InvertedDescriptor A (lamInner kk dq + lamOuter dE a1 a2 R nSq epsS) kB T := by
  sorry

/-- [拉伸项] 同上的**几何版**：用"两球不重叠" `a1 + a2 ≤ R` 替代 `hgeom`
    （后者由 `hgeom_of_nonoverlap` 推出）。[由 prover_d 交付，2026-09-20 回填骨架]

English: [Stretch item] The **geometric version** of the above: replace `hgeom` by "the two spheres do not overlap", `a1 + a2 ≤ R`
    (the former being derived by `hgeom_of_nonoverlap`). [Delivered by prover_d, back-filled into the skeleton on 2026-09-20] --/
theorem descriptor_holds_of_nonoverlap {A kB T kk dq dE a1 a2 R nSq epsS : ℝ} (hA : 0 < A)
    (hkB : 0 < kB) (hT : 0 < T) (hkk : 0 ≤ kk) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hRge : a1 + a2 ≤ R) (hnSq : 0 < nSq) (hepsS : 0 < epsS) (hPekar : 1 / epsS < 1 / nSq) :
    InvertedDescriptor A (lamInner kk dq + lamOuter dE a1 a2 R nSq epsS) kB T := by
  sorry

/-! ## M5a — ℚ 判定层（对应 PhotoLean/Marcus/RatModel.lean）

English: ## M5a — the ℚ decision layer (corresponds to PhotoLean/Marcus/RatModel.lean) -/

/-- ℚ 分类器（可计算）。

English: The ℚ classifier (computable). --/
def zoneQ (lam x : ℚ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

def barrierQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ) := by
  sorry

theorem zoneQ_inverted_iff (lam x : ℚ) : zoneQ lam x = Zone.inverted ↔ (lam : ℝ) < (x : ℝ) := by
  sorry

/-! ## 风险探针（risk probes）— **不含 sorry**，Sprint 0 必须真通过

English: ## Risk probes — they **contain no unfinished-proof placeholder**, and Sprint 0 must genuinely pass them -/

-- R1: ℚ 上的判定是否真能被内核算出（M5 的判定证据链依赖它）
-- English: R1: whether decidability over ℚ can really be computed by the kernel (the decidability-evidence chain of M5 depends on it)
--   **实测结论（Sprint 0）**：`decide` 对**整数**字面量的比较可算（内核能归约到底），
-- English:   **Measured conclusion (Sprint 0)**: `decide` can compute comparisons of **integer** literals (the kernel reduces them all the way down),
--   但对**含除法的有理字面量**（如 `3 / 4`）**卡在 `Rat` 的 gcd/除法归约上**
-- English:   but for **rational literals containing division** (such as `3 / 4`) it **gets stuck on `Rat`'s gcd/division reduction**
--   （报错：'Decidable' instance did not reduce to 'isTrue' or 'isFalse'）。
-- English:   (error: 'Decidable' instance did not reduce to 'isTrue' or 'isFalse').
--   对策：判定证据用 `norm_num [zoneQ]`（它走证明项而非内核归约），
-- English:   Workaround: use `norm_num [zoneQ]` for decidability evidence (it goes through proof terms rather than kernel reduction),
--   `decide` 只用于整数参数。此结论已写入 proofs/API-NOTES.md。
-- English:   and reserve `decide` for integer arguments. This conclusion has been written into proofs/API-NOTES.md.
example : zoneQ (1 : ℚ) 3 = Zone.inverted := by decide
example : zoneQ (1 : ℚ) 1 = Zone.barrierless := by decide
example : zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by norm_num [zoneQ]
example : zoneQ (1 : ℚ) (6 / 8) = Zone.normal := by norm_num [zoneQ]

-- R2: Real.exp 单调性的**签名与方向**（M3 核心引理依赖它）
-- English: R2: the **signature and direction** of `Real.exp` monotonicity (the core lemmas of M3 depend on it)
example {a b : ℝ} (h : a < b) : Real.exp a < Real.exp b := Real.exp_lt_exp.mpr h

-- R3: 势垒非负性的最短证明（M2 的第一条）
-- English: R3: the shortest proof of barrier nonnegativity (the first item of M2)
example {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : 0 ≤ (lam - x) ^ 2 / (4 * lam) := by positivity

-- R4: 反转区势垒严格单增的最小内核（M2 的关键目标形态）
-- English: R4: the minimal kernel for strict monotonicity of the barrier in the inverted region (the key target shape of M2)
example {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ} (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) :
    (lam - x₁) ^ 2 / (4 * lam) < (lam - x₂) ^ 2 / (4 * lam) := by
  have hpos : (0 : ℝ) < 4 * lam := by positivity
  have hsq : (lam - x₁) ^ 2 < (lam - x₂) ^ 2 := by nlinarith
  exact div_lt_div_of_pos_right hsq hpos

end PhotoLean.Marcus.Skeleton
