/-
  marcus-ident-rat-api.lean — 标识符合法性与 ℚ 判定域探针（Marcus 反转区）

  目的
    ⑴ **标识符禁止清单实测**：哪些 Unicode/Greek 符号不能作 Lean 标识符；
    ⑵ **`by decide` 对 ℚ 的可靠域**：整数参数 vs 含除法字面量；
    ⑶ 独立复核 lead 在 `marcus-lead-riskscratch.lean` 里报的四条风险结论
       （R1–R4）与三条名字/签名结论（`div_lt_div_right_of_neg`、
       `pos_of_mul_pos_left`、`pow_lt_pow_left₀`）。

  运行命令（在仓库根目录执行）
    proofs/scripts/lake env lean theories/Marcus/probes/marcus-ident-rat-api.lean

  本文件为 **正向探针**：必须 0 error。
  **不合法** 的标识符与 **失败** 的写法写在注释里（否则本文件不编译）。

  校准基准：mathlib v4.17.0（lean-toolchain = leanprover/lean4:v4.17.0）
  校准日期：2026-09-20 — api_researcher

  English: marcus-ident-rat-api.lean — probe for identifier legality and the reliable decision domain over ℚ (Marcus inverted region)

  Purpose
    (1) **Measured identifier blacklist**: which Unicode/Greek symbols cannot be used as Lean identifiers;
    (2) **Reliable domain of `by decide` over ℚ**: integer arguments vs literals containing division;
    (3) Independently re-check the four risk conclusions (R1–R4) reported by lead in `marcus-lead-riskscratch.lean`,
        together with the three name/signature conclusions (`div_lt_div_right_of_neg`,
        `pos_of_mul_pos_left`, `pow_lt_pow_left₀`).

  Run command (executed from the repository root)
    proofs/scripts/lake env lean theories/Marcus/probes/marcus-ident-rat-api.lean

  This file is a **positive probe**: it must produce 0 error.
  **Illegal** identifiers and **failing** phrasings are written inside comments (otherwise this file would not compile).

  Calibration baseline: mathlib v4.17.0 (lean-toolchain = leanprover/lean4:v4.17.0)
  Calibration date: 2026-09-20 — api_researcher
-/

import Mathlib

set_option linter.unusedVariables false

/-! ## ⑴ 标识符禁止清单（实测，2026-09-20）

  Lean 4 的**保留 token** 不能作标识符，报错统一为
  `error: unexpected token '<tok>'; expected '_' or identifier`。

  **禁止**（20 个，实测全部报 token 错误）：
    λ  Π  Σ  ↓  ←  →  ↔  ∀  ∃  ∧  ∨  ¬  ≠  ≤  ≥  ∑  ∏  ∫  ∈  ⊆

  **合法**（30 个，实测均可作绑定名 `example (ε : ℝ) : ε = ε := rfl`）：
    Λ  α  β  γ  Γ  δ  Δ  ε  ζ  η  θ  Θ  ι  κ  μ  ν  ξ  Ξ
    π  ρ  σ  τ  υ  φ  Φ  χ  ψ  ω  Ω

  要点：
  - `λ` 是 lambda 抽象的语法记号 → **绝对不能用**。`Λ`（大写）合法。
  - 小写 `π` / `σ` 合法，但大写 `Π` / `Σ` 是依值积/和记号 → 禁止。
  - `ε` / `δ` / `Δ` / `μ` **合法**，物理量可以用它们；但本项目仍统一 ASCII 化
    （`lam` / `lamIn` / `lamOut` / `nSq` / `epsS` / `dE` / `dq` / `a1` / `a2`），
    见 `marcus-statement-skeleton.lean`。

  English: ## (1) Identifier blacklist (measured, 2026-09-20)

  Lean 4's **reserved tokens** cannot be used as identifiers, and the error reported is uniformly
  `error: unexpected token '<tok>'; expected '_' or identifier`.

  **Forbidden** (20 of them; in the measurement every single one reports a token error):
    λ  Π  Σ  ↓  ←  →  ↔  ∀  ∃  ∧  ∨  ¬  ≠  ≤  ≥  ∑  ∏  ∫  ∈  ⊆

  **Legal** (30 of them; in the measurement all of them can be used as a binder name `example (ε : ℝ) : ε = ε := rfl`):
    Λ  α  β  γ  Γ  δ  Δ  ε  ζ  η  θ  Θ  ι  κ  μ  ν  ξ  Ξ
    π  ρ  σ  τ  υ  φ  Φ  χ  ψ  ω  Ω

  Key points:
  - `λ` is the syntax token for lambda abstraction → **absolutely unusable**. `Λ` (upper case) is legal.
  - Lower-case `π` / `σ` are legal, but upper-case `Π` / `Σ` are the dependent-product and dependent-sum notation → forbidden.
  - `ε` / `δ` / `Δ` / `μ` are **legal** and may be used for physical quantities; this project nevertheless standardizes on ASCII
    (`lam` / `lamIn` / `lamOut` / `nSq` / `epsS` / `dE` / `dq` / `a1` / `a2`),
    see `marcus-statement-skeleton.lean`.
-/

-- 合法：下面这些 example 全部编译通过（不合法的那 20 个不会出现在这里）
-- English: Legal: every example below compiles (the 20 illegal symbols do not appear here)
example (ε : ℝ) : ε = ε := rfl
example (δ : ℝ) : δ = δ := rfl
example (Δ : ℝ) : Δ = Δ := rfl
example (μ : ℝ) : μ = μ := rfl
example (Λ : ℝ) : Λ = Λ := rfl
example (σ π θ φ ω : ℝ) : σ + π + θ + φ + ω = σ + π + θ + φ + ω := rfl
-- 对照（不合法，仅注释）：
-- English: Contrast (illegal; comment only):
--   example (λ : ℝ) : λ = λ := rfl
--   -- error: unexpected token 'λ'; expected '_' or identifier

/-! ## ⑵ `by decide` 对 `ℚ` 的可靠域

  **规范（M5 判定层）**：
  - 参数是**整数字面量**的比较 → `decide` ✅（内核能到底）
  - 参数含**除法/约分**的有理字面量 → `decide` ❌，必须 `norm_num [zoneQ]` ✅

  `decide` 失败时内核归约卡住，原始报错：
  ```
  tactic 'decide' failed for proposition
    zoneQ 1 (3 / 4) = Zone.normal
  since its 'Decidable' instance
    instDecidableEqZone (zoneQ 1 (3 / 4)) Zone.normal
  did not reduce to 'isTrue' or 'isFalse'.

  After unfolding the instances 'instDecidableEqBool', 'instDecidableEqNat',
  'instDecidableEqZone', 'Bool.decEq', 'Int.decLt', 'Nat.decEq',
  'Rat.instDecidableLt' and 'Int.decNonneg✝', reduction got stuck at the
  'Decidable' instance
    match h : (zoneQ 1 (3 / 4)).toCtorIdx.beq Zone.normal.toCtorIdx with
    | true => isTrue ⋯
    | false => isFalse ⋯
  ```
  （注意：卡点在 `Rat.instDecidableLt` → `Int.decNonneg` 路径，不是 `Eq`。）

  English: ## (2) The reliable domain of `by decide` over `ℚ`

  **Convention (M5 decision layer)**:
  - Comparisons whose parameters are **integer literals** → `decide` ✅ (the kernel reduces all the way down)
  - Rational literals whose parameters contain **division / reduction of fractions** → `decide` ❌; one must use `norm_num [zoneQ]` ✅

  When `decide` fails, kernel reduction gets stuck. The raw error output quoted verbatim in the fenced block above
  (which is English console text and is therefore left untouched) documents exactly this failure.

  (Note: the place where reduction gets stuck is the `Rat.instDecidableLt` → `Int.decNonneg` path, not `Eq`.)
-/

namespace IdentRatProbe

inductive Zone where
  | normal
  | barrierless
  | inverted
  deriving DecidableEq, Repr

noncomputable def zone (lam x : ℝ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

def zoneQ (lam x : ℚ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

-- ✅ 整数字面量：decide 可以
-- English: ✅ Integer literals: decide works
example : zoneQ (1 : ℚ) 3 = Zone.inverted := by decide
example : zoneQ (1 : ℚ) 1 = Zone.barrierless := by decide
example : zoneQ (1 : ℚ) 0 = Zone.normal := by decide
-- ❌ 含除法：decide 不行（见上方报错），改用 norm_num
-- English: ❌ Contains division: decide does not work (see the error above); switch to norm_num
--    example : zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by decide
-- ✅ 含除法：norm_num [zoneQ] 可以
-- English: ✅ Contains division: norm_num [zoneQ] works
example : zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by norm_num [zoneQ]
example : zoneQ (1 : ℚ) (6 / 8) = Zone.normal := by norm_num [zoneQ]
example : zoneQ (1 : ℚ) (5 / 4) = Zone.inverted := by norm_num [zoneQ]
example : zoneQ (1 : ℚ) (4 / 4) = Zone.barrierless := by norm_num [zoneQ]
-- ✅ ℚ → ℝ 分类器一致性（M5a）
-- English: ✅ Consistency of the ℚ → ℝ classifiers (M5a)
theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ) := by
  unfold zoneQ zone
  simp only [Rat.cast_lt, Rat.cast_inj]

end IdentRatProbe

/-! ## ⑶ lead 风险探针的独立复核（R1–R4 + 三条名字结论）

  R1 = `zoneQ` 的 decide 域 → 见上。
  R2/R3/R4 = 下面三条 example，**逐字取自** `marcus-statement-skeleton.lean`
     的"风险探针"节，独立重跑确认通过。

  English: ## (3) Independent re-check of lead's risk probes (R1–R4 + the three name conclusions)

  R1 = the decide domain of `zoneQ` → see above.
  R2/R3/R4 = the three examples below, **copied word for word** from the "risk probe" section of
     `marcus-statement-skeleton.lean`, re-run independently and confirmed to pass.
-/

noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

-- R2: `Real.exp_lt_exp` 是 **iff**，`.mpr` 方向是 `a < b → exp a < exp b`
-- English: R2: `Real.exp_lt_exp` is an **iff**; the `.mpr` direction is `a < b → exp a < exp b`
example {a b : ℝ} (h : a < b) : Real.exp a < Real.exp b := Real.exp_lt_exp.mpr h
-- R3: 势垒非负的最短证明
-- English: R3: the shortest proof that the barrier is nonnegative
example {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : 0 ≤ (lam - x) ^ 2 / (4 * lam) := by positivity
-- R4: 反转区势垒严格单增（lead 版：分两步 have，比一步 rw+nlinarith 更长但更稳）
-- English: R4: the barrier is strictly increasing on the inverted region (lead's version: two `have` steps; longer than a single rw+nlinarith but more robust)
example {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ} (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) :
    (lam - x₁) ^ 2 / (4 * lam) < (lam - x₂) ^ 2 / (4 * lam) := by
  have hpos : (0 : ℝ) < 4 * lam := by positivity
  have hsq : (lam - x₁) ^ 2 < (lam - x₂) ^ 2 := by nlinarith
  exact div_lt_div_of_pos_right hsq hpos
-- 同目标，最短版（api_researcher 实测，少一行）
-- English: Same goal, shortest version (measured by api_researcher; one line fewer)
example {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ} (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) :
    (lam - x₁) ^ 2 / (4 * lam) < (lam - x₂) ^ 2 / (4 * lam) := by
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith

-- 结论 1：`div_lt_div_right_of_neg` 存在且是 iff，**右边方向是 `b < a`**（反直觉）
-- English: Conclusion 1: `div_lt_div_right_of_neg` exists and is an iff, and **its right-hand direction is `b < a`** (counter-intuitive)
#check div_lt_div_right_of_neg
-- 结论 2：`pos_of_mul_pos_left`（取左因子）vs `pos_of_mul_pos_right`（取右因子）
-- English: Conclusion 2: `pos_of_mul_pos_left` (takes the left factor) vs `pos_of_mul_pos_right` (takes the right factor)
#check pos_of_mul_pos_left
#check pos_of_mul_pos_right
example {A u : ℝ} (h : 0 < A * Real.exp u) : 0 < A :=
  pos_of_mul_pos_left h (Real.exp_pos u).le
-- 结论 3：`pow_lt_pow_left₀` 的参数顺序 + `n ≠ 0`；`sq_lt_sq` 带绝对值
-- English: Conclusion 3: the argument order of `pow_lt_pow_left₀` plus its `n ≠ 0`; `sq_lt_sq` carries absolute values
#check pow_lt_pow_left₀
#check sq_lt_sq
example {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) :
    (lam - x₁) ^ 2 < (lam - x₂) ^ 2 := by nlinarith   -- nlinarith 更省事，无需引理
-- English: nlinarith is less trouble here; no lemma needed
