/-
PhotoLean.Marcus.Reorg — M4b：微观重组能正性（Marcus 反转区；theories/Marcus/plan.md §7.2）。

**本模块零依赖**：只 `import Mathlib`，不 import 任何项目内模块 —— 因此它与关键路径
（Basic → Barrier → Rate → Sharp → Compose）**可完全并行**。复合定理
（`descriptor_holds_of_microscopic`）属于 M4c，放在 `Marcus/Compose.lean`，不在本文件。

## 语义（人工复核用）

- `lamInner kk dq = kk * dq ^ 2 / 2`：**内层（内球）重组能** —— 简正模式力常数 `kk`
  乘以核位移平方 `dq ^ 2` 再取半（谐振子 ½kx² 形式）。
  物理上 `kk` 允许为 0（无内层重组），故 `lamInner_nonneg` 只要求 `0 ≤ kk`；
  `lamInner_pos` 则要求 `0 < kk` **且** `dq ≠ 0`：力常数严格正与位移非零缺一不可。

- `lamOuter dE a1 a2 R nSq epsS
     = dE ^ 2 * (1 / (2 * a1) + 1 / (2 * a2) - 1 / R) * (1 / nSq - 1 / epsS)`：
  **外层（外球/溶剂）重组能**，两球连续介质（Pekar）形式。物理量对应：
  `dE` = 转移电荷量 Δe，`a1` / `a2` = 两球半径，`R` = 两球球心间距，
  `nSq` = n²（光学折射率平方），`epsS` = ε_s（静态介电常数）。
  三个因子依次是：电荷平方 `dE ^ 2`、几何因子 `(1/(2a₁) + 1/(2a₂) − 1/R)`、
  Pekar 因子 `(1/n² − 1/ε_s)`。

## 物理近似（全部显式化为定理前提；不得折叠进定义）

| 前提 | 物理含义 |
|---|---|
| `0 < dE` | 转移电荷量非零 |
| `0 < a1` / `0 < a2` | 两球半径严格正 |
| `0 < R` | 球心间距严格正 |
| `1 / R < 1 / (2 * a1) + 1 / (2 * a2)` | **几何因子正性**（R 小于两球半径并联尺度） |
| `0 < nSq` / `0 < epsS` | 折射率平方、静态介电常数严格正（Pekar 因子的定义域） |
| `1 / epsS < 1 / nSq` | **Pekar 因子正性**，等价于 `n² < ε_s`：溶剂侧"反转区存在"的充分条件 |

**Lean 侧命名一律 ASCII**（`kk` / `dE` / `dq` / `nSq` / `epsS` / `a1` / `a2`）：
Lean 4 中 `λ` 是 lambda 关键字、下标 `a₁` 不是合法标识符字符 —— 希腊字母只留在注释里。

**语句权威**：`theories/Marcus/probes/marcus-statement-skeleton.lean` 的 M4b 段；本文件的定义与
定理签名与之逐字一致。

**验收**：`proofs/scripts/check.sh --strict PhotoLean.Marcus.Reorg`（构建 + 扫描）**与**
`proofs/scripts/axioms.sh PhotoLean.Marcus.Reorg <带命名空间的定理名>`（公理纪律）缺一不可
—— 单独构建通过不构成验收。

English: PhotoLean.Marcus.Reorg — M4b: positivity of the microscopic reorganization energy
(Marcus inverted region; theories/Marcus/plan.md §7.2).

**Zero dependencies**: this module only does `import Mathlib` and imports no in-project module —
hence it is **fully parallelizable** with the critical path (Basic → Barrier → Rate → Sharp → Compose).
The composition theorem (`descriptor_holds_of_microscopic`) belongs to M4c and lives in
`Marcus/Compose.lean`, not in this file.

## Semantics (for human review)

- `lamInner kk dq = kk * dq ^ 2 / 2`: the **inner-sphere reorganization energy** — the normal-mode
  force constant `kk` times the squared nuclear displacement `dq ^ 2`, halved (harmonic-oscillator
  form ½kx²). Physically `kk` is allowed to be 0 (no inner-sphere reorganization), so
  `lamInner_nonneg` only requires `0 ≤ kk`; `lamInner_pos` instead requires `0 < kk` **and**
  `dq ≠ 0`: a strictly positive force constant and a nonzero displacement are both indispensable.

- `lamOuter dE a1 a2 R nSq epsS
     = dE ^ 2 * (1 / (2 * a1) + 1 / (2 * a2) - 1 / R) * (1 / nSq - 1 / epsS)`:
  the **outer-sphere (solvent) reorganization energy**, in the two-sphere continuum (Pekar) form.
  Physical-quantity correspondence: `dE` = transferred charge Δe, `a1` / `a2` = radii of the two
  spheres, `R` = center-to-center distance of the two spheres, `nSq` = n² (squared optical
  refractive index), `epsS` = ε_s (static dielectric constant). The three factors are, in order:
  the charge squared `dE ^ 2`, the geometric factor `(1/(2a₁) + 1/(2a₂) − 1/R)`, and the Pekar
  factor `(1/n² − 1/ε_s)`.

## Physical approximations (all made explicit as theorem premises; none may be folded into definitions)

| Premise | Physical meaning |
|---|---|
| `0 < dE` | transferred charge is nonzero |
| `0 < a1` / `0 < a2` | both sphere radii are strictly positive |
| `0 < R` | center-to-center distance is strictly positive |
| `1 / R < 1 / (2 * a1) + 1 / (2 * a2)` | **positivity of the geometric factor** (R below the parallel scale of the two radii) |
| `0 < nSq` / `0 < epsS` | squared refractive index and static dielectric constant are strictly positive (domain of the Pekar factor) |
| `1 / epsS < 1 / nSq` | **positivity of the Pekar factor**, equivalent to `n² < ε_s`: the solvent-side sufficient condition for "the inverted region to exist" |

**Naming on the Lean side is uniformly ASCII** (`kk` / `dE` / `dq` / `nSq` / `epsS` / `a1` / `a2`):
in Lean 4, `λ` is the lambda keyword and the subscript `a₁` is not a legal identifier character —
Greek letters are kept in comments only.

**Statement authority**: the M4b section of `theories/Marcus/probes/marcus-statement-skeleton.lean`; the
definitions and theorem signatures in this file match it word for word.

**Acceptance**: `proofs/scripts/check.sh --strict PhotoLean.Marcus.Reorg` (build + scan) **and**
`proofs/scripts/axioms.sh PhotoLean.Marcus.Reorg <fully-qualified theorem name>` (axiom discipline)
are both indispensable — a bare successful build does not constitute acceptance.
-/

import Mathlib

namespace PhotoLean.Marcus

/-- 内层（内球）重组能：简正模式力常数 × 位移平方 / 2。
    English: Inner-sphere reorganization energy: normal-mode force constant × displacement squared / 2. -/
noncomputable def lamInner (kk dq : ℝ) : ℝ := kk * dq ^ 2 / 2

/-- 外层（外球/溶剂）重组能（两球连续介质模型，Pekar 形式）。
    English: Outer-sphere (solvent) reorganization energy (two-sphere continuum model, Pekar form). -/
noncomputable def lamOuter (dE a1 a2 R nSq epsS : ℝ) : ℝ :=
  dE ^ 2 * (1 / (2 * a1) + 1 / (2 * a2) - 1 / R) * (1 / nSq - 1 / epsS)

/-- 内层重组能非负：力常数非负即可（`kk = 0` 即无内层重组，物理上允许）。
    English: Inner-sphere reorganization energy is nonnegative: a nonnegative force constant
    suffices (`kk = 0` means no inner-sphere reorganization, which is physically allowed). -/
theorem lamInner_nonneg {kk : ℝ} (hkk : 0 ≤ kk) (dq : ℝ) : 0 ≤ lamInner kk dq := by
  unfold lamInner
  positivity

/-- 内层重组能严格正：力常数严格正 **且** 位移非零（`dq ≠ 0`）。
    mathlib v4.17 签名实测：`sq_pos_of_ne_zero : a ≠ 0 → 0 < a ^ 2`（`a` 为隐式参数）。
    English: Inner-sphere reorganization energy is strictly positive: the force constant is strictly
    positive **and** the displacement is nonzero (`dq ≠ 0`). mathlib v4.17 signature verified in
    practice: `sq_pos_of_ne_zero : a ≠ 0 → 0 < a ^ 2` (`a` is an implicit argument). -/
theorem lamInner_pos {kk : ℝ} (hkk : 0 < kk) {dq : ℝ} (hdq : dq ≠ 0) :
    0 < lamInner kk dq := by
  have hsq : 0 < dq ^ 2 := sq_pos_of_ne_zero hdq
  unfold lamInner
  positivity

/-
前提说明（人工复核用）：`ha1` / `ha2` / `hR` / `hnSq` / `hepsS` 是**物理定义域前提**
（保证 `lamOuter` 的参数落在物理有意义的两球连续介质几何里：两球半径严格正、球心间距
严格正、折射率平方严格正、静态介电常数严格正）。按 `theories/Marcus/plan.md` §7.2 的要求，物理前提
必须在定理签名里可见、不得折叠进定义，故它们**保留在签名中**。

就本定理的结论而言，证明**未使用**（unused）这五条：`hdE` / `hgeom` / `hPekar`
三条已足够。请注意它们**并非**由 `hgeom` / `hPekar` 蕴含 —— 反例（内核已验证）：
`a1 = -1`、`a2 = 1`、`R = -1`、`nSq = 1`、`epsS = 2` 时
`1 / R < 1 / (2 * a1) + 1 / (2 * a2)` 与 `1 / epsS < 1 / nSq` 都成立，
但 `ha1`（`0 < a1`）与 `hR`（`0 < R`）均为假。因此此处只能说"证明未使用"，
不能说"被 `hgeom` / `hPekar` 蕴含"。

代价是 Lean 的未使用变量警告；下面作用域限定的 `set_option` 把它关闭，
**不改变语句**（签名与骨架逐字一致）。

English: Note on the premises (for human review): `ha1` / `ha2` / `hR` / `hnSq` / `hepsS` are
**physical domain premises** (they keep the arguments of `lamOuter` inside the physically meaningful
two-sphere continuum geometry: both sphere radii strictly positive, center-to-center distance
strictly positive, squared refractive index strictly positive, static dielectric constant strictly
positive). As `theories/Marcus/plan.md` §7.2 requires, physical premises must be visible in the theorem signature
and must not be folded into definitions, so they are **kept in the signature**.

For the conclusion of this theorem, the proof **does not use** (unused) these five: the three
premises `hdE` / `hgeom` / `hPekar` already suffice. Note that they are **not** implied by
`hgeom` / `hPekar` — counterexample (verified in the kernel): with `a1 = -1`, `a2 = 1`, `R = -1`,
`nSq = 1`, `epsS = 2`, both `1 / R < 1 / (2 * a1) + 1 / (2 * a2)` and `1 / epsS < 1 / nSq` hold,
yet `ha1` (`0 < a1`) and `hR` (`0 < R`) are both false. Hence here one may only say "the proof does
not use them", not "they are implied by `hgeom` / `hPekar`".

The price is Lean's unused-variable warning; the scoped `set_option` below switches it off and
**does not change the statement** (signature and skeleton agree word for word).
-/
set_option linter.unusedVariables false in
/-- **Pekar 因子正性**：`1 / epsS < 1 / nSq`（等价 `n² < ε_s`）加几何因子正性
    ⇒ 外层重组能为正 —— 这是"反转区存在"的**溶剂侧充分条件**。
    English: **Positivity of the Pekar factor**: `1 / epsS < 1 / nSq` (equivalently `n² < ε_s`) plus
    positivity of the geometric factor ⇒ the outer-sphere reorganization energy is positive — this
    is the **solvent-side sufficient condition** for "the inverted region to exist". -/
theorem lamOuter_pos {dE a1 a2 R nSq epsS : ℝ} (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) : 0 < lamOuter dE a1 a2 R nSq epsS := by
  -- 两个因子的正性由两条不等式前提直接给出（`linarith` 会先把目标化归成
  -- `0 < (1 / (2 * a1) + 1 / (2 * a2)) - 1 / R` 与 `0 < 1 / nSq - 1 / epsS`）。
  -- English: positivity of the two factors follows directly from the two inequality premises
  -- English: (`linarith` first reduces the goal to `0 < (1 / (2 * a1) + 1 / (2 * a2)) - 1 / R`
  -- English: and `0 < 1 / nSq - 1 / epsS`).
  have hgeom' : 0 < 1 / (2 * a1) + 1 / (2 * a2) - 1 / R := by linarith
  have hPekar' : 0 < 1 / nSq - 1 / epsS := by linarith
  have hdE2 : 0 < dE ^ 2 := by positivity
  unfold lamOuter
  exact mul_pos (mul_pos hdE2 hgeom') hPekar'

/-- 重组能分解的加性：内层非负 + 外层严格正 ⇒ 总重组能严格正。
    （M4c 的复合定理用它把 `lamInner kk dq + lamOuter ...` 的正性交给
    `lamInner_nonneg` 与 `lamOuter_pos`。）
    English: Additivity of the reorganization-energy decomposition: nonnegative inner part + strictly
    positive outer part ⇒ the total reorganization energy is strictly positive.
    (The M4c composition theorem uses it to hand the positivity of
    `lamInner kk dq + lamOuter ...` over to `lamInner_nonneg` and `lamOuter_pos`.) -/
theorem lam_total_pos {lamIn lamOut : ℝ} (h₁ : 0 ≤ lamIn) (h₂ : 0 < lamOut) : 0 < lamIn + lamOut := by
  linarith

/-!
## 追加项（拉伸）：把几何前提 `hgeom` 从"假设"降级为"推导"

`lamOuter_pos` 的前提 `hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)` 在物理上就是
"两球分离（`a1 + a2 ≤ R`）"这一几何约定的代数后果；下面把它证出来：几何侧的前提只剩
"两球半径严格正 + 两球不重叠"，`hgeom` 不再是独立的物理近似。

本引理**不依赖任何物理近似**，只用 `1/x` 在正数上的反单调性与一次通分 —— 这是本计划里
唯一真正需要不等式技巧的几何引理。唯一前提 `0 < R`（球心间距严格正）由 `hRge` 推出，
因此**不在签名里**（它是结论，不是假设）。

English: Addendum (stretch): demoting the geometric premise `hgeom` from "assumption" to "derivation".

The premise `hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)` of `lamOuter_pos` is physically just the
algebraic consequence of the geometric convention "the two spheres are separated (`a1 + a2 ≤ R`)";
below we prove it: on the geometric side the only remaining premises are "both sphere radii strictly
positive + the two spheres do not overlap", and `hgeom` is no longer an independent physical
approximation.

This lemma **relies on no physical approximation**: it uses only the antitonicity of `1/x` on the
positive numbers plus one common-denominator computation — this is the only geometric lemma in this
plan that genuinely needs inequality technique. Its only premise `0 < R` (strictly positive
center-to-center distance) is derived from `hRge`, hence it is **not in the signature** (it is a
conclusion, not an assumption).
-/

/-- 几何因子正性可由"两球不重叠"推出（把 `hgeom` 从假设变为推导）：
    `a1 + a2 ≤ R ⇒ 1/R < 1/(2*a1) + 1/(2*a2)`。
    English: Positivity of the geometric factor follows from "the two spheres do not overlap"
    (turning `hgeom` from an assumption into a derivation):
    `a1 + a2 ≤ R ⇒ 1/R < 1/(2*a1) + 1/(2*a2)`. -/
theorem hgeom_of_nonoverlap {a1 a2 R : ℝ} (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hRge : a1 + a2 ≤ R) : 1 / R < 1 / (2 * a1) + 1 / (2 * a2) := by
  -- (1) 分母正性：`0 < a1 + a2 ≤ R` 给出 `0 < a1 + a2`（`linarith` 用 `ha1`/`ha2`）。
  -- English: (1) Positivity of the denominator: `0 < a1 + a2 ≤ R` gives `0 < a1 + a2`
  -- English: (`linarith` uses `ha1`/`ha2`).
  have hpos : 0 < a1 + a2 := by linarith
  -- (2) `one_div_le_one_div_of_le`（非严格版）需要的是**较小**分母的正性，
  --     于是直接得到 `1 / R ≤ 1 / (a1 + a2)`。
  -- English: (2) `one_div_le_one_div_of_le` (the non-strict version) needs positivity of the
  -- English: **smaller** denominator, so we obtain `1 / R ≤ 1 / (a1 + a2)` directly.
  have h1 : 1 / R ≤ 1 / (a1 + a2) := one_div_le_one_div_of_le hpos hRge
  -- (3) 通分：`1/(2a1) + 1/(2a2) = (a1+a2)/(2a1a2)`。
  --     `field_simp` 在这里好用，因为目标是**等式**且分母非零由 `positivity` 直接给出
  --     （API-NOTES G-5：`field_simp` 只对等式可靠，对不等式会 `simp made no progress`）。
  -- English: (3) Common denominator: `1/(2a1) + 1/(2a2) = (a1+a2)/(2a1a2)`.
  -- English: `field_simp` is handy here because the goal is an **equality** and the nonzero
  -- English: denominators are supplied directly by `positivity`
  -- English: (API-NOTES G-5: `field_simp` is reliable only for equalities; on inequalities it
  -- English: reports `simp made no progress`).
  have hden : 0 < 2 * a1 * a2 := by positivity
  have hsum : 1 / (2 * a1) + 1 / (2 * a2) = (a1 + a2) / (2 * a1 * a2) := by
    field_simp
    ring
  -- (4) 两边同乘正分母 `(a1 + a2) * (2 * a1 * a2)`（`div_lt_div_iff₀`），
  --     等价于 `2 * a1 * a2 < (a1 + a2) ^ 2`，即 `0 < a1 ^ 2 + a2 ^ 2`。
  --     这条严格不等式由 `a1 > 0`（故 `a1 ^ 2 > 0`）与 `a2 ^ 2 ≥ 0` 得到。
  -- English: (4) multiply both sides by the positive denominator `(a1 + a2) * (2 * a1 * a2)`
  -- English: (`div_lt_div_iff₀`), which is equivalent to `2 * a1 * a2 < (a1 + a2) ^ 2`, i.e.
  -- English: `0 < a1 ^ 2 + a2 ^ 2`. This strict inequality follows from `a1 > 0` (hence
  -- English: `a1 ^ 2 > 0`) together with `a2 ^ 2 ≥ 0`.
  have h2 : 1 / (a1 + a2) < 1 / (2 * a1) + 1 / (2 * a2) := by
    rw [hsum]
    rw [div_lt_div_iff₀ hpos hden]
    nlinarith [sq_nonneg a2, sq_pos_of_ne_zero (ne_of_gt ha1)]
  -- (5) 传递（`linarith` 直接合成 `≤` 与 `<`）。
  -- English: (5) transitivity (`linarith` composes `≤` and `<` directly).
  linarith

end PhotoLean.Marcus
