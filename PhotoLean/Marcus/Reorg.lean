/-
PhotoLean.Marcus.Reorg — M4b：微观重组能正性（Marcus 反转区；plan.md §7.2）。

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

**语句权威**：`proofs/probes/marcus-statement-skeleton.lean` 的 M4b 段；本文件的定义与
定理签名与之逐字一致。

**验收**：`proofs/scripts/check.sh --strict PhotoLean.Marcus.Reorg`（构建 + 扫描）**与**
`proofs/scripts/axioms.sh PhotoLean.Marcus.Reorg <带命名空间的定理名>`（公理纪律）缺一不可
—— 单独构建通过不构成验收。
-/

import Mathlib

namespace PhotoLean.Marcus

/-- 内层（内球）重组能：简正模式力常数 × 位移平方 / 2。--/
noncomputable def lamInner (kk dq : ℝ) : ℝ := kk * dq ^ 2 / 2

/-- 外层（外球/溶剂）重组能（两球连续介质模型，Pekar 形式）。--/
noncomputable def lamOuter (dE a1 a2 R nSq epsS : ℝ) : ℝ :=
  dE ^ 2 * (1 / (2 * a1) + 1 / (2 * a2) - 1 / R) * (1 / nSq - 1 / epsS)

/-- 内层重组能非负：力常数非负即可（`kk = 0` 即无内层重组，物理上允许）。--/
theorem lamInner_nonneg {kk : ℝ} (hkk : 0 ≤ kk) (dq : ℝ) : 0 ≤ lamInner kk dq := by
  unfold lamInner
  positivity

/-- 内层重组能严格正：力常数严格正 **且** 位移非零（`dq ≠ 0`）。
    mathlib v4.17 签名实测：`sq_pos_of_ne_zero : a ≠ 0 → 0 < a ^ 2`（`a` 为隐式参数）。--/
theorem lamInner_pos {kk : ℝ} (hkk : 0 < kk) {dq : ℝ} (hdq : dq ≠ 0) :
    0 < lamInner kk dq := by
  have hsq : 0 < dq ^ 2 := sq_pos_of_ne_zero hdq
  unfold lamInner
  positivity

/-
前提说明（人工复核用）：`ha1` / `ha2` / `hR` / `hnSq` / `hepsS` 是**物理定义域前提**
（保证 `lamOuter` 的参数落在物理有意义的两球连续介质几何里：两球半径严格正、球心间距
严格正、折射率平方严格正、静态介电常数严格正）。按 `plan.md` §7.2 的要求，物理前提
必须在定理签名里可见、不得折叠进定义，故它们**保留在签名中**。

就本定理的结论而言，证明**未使用**（unused）这五条：`hdE` / `hgeom` / `hPekar`
三条已足够。请注意它们**并非**由 `hgeom` / `hPekar` 蕴含 —— 反例（内核已验证）：
`a1 = -1`、`a2 = 1`、`R = -1`、`nSq = 1`、`epsS = 2` 时
`1 / R < 1 / (2 * a1) + 1 / (2 * a2)` 与 `1 / epsS < 1 / nSq` 都成立，
但 `ha1`（`0 < a1`）与 `hR`（`0 < R`）均为假。因此此处只能说"证明未使用"，
不能说"被 `hgeom` / `hPekar` 蕴含"。

代价是 Lean 的未使用变量警告；下面作用域限定的 `set_option` 把它关闭，
**不改变语句**（签名与骨架逐字一致）。
-/
set_option linter.unusedVariables false in
/-- **Pekar 因子正性**：`1 / epsS < 1 / nSq`（等价 `n² < ε_s`）加几何因子正性
    ⇒ 外层重组能为正 —— 这是"反转区存在"的**溶剂侧充分条件**。--/
theorem lamOuter_pos {dE a1 a2 R nSq epsS : ℝ} (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) : 0 < lamOuter dE a1 a2 R nSq epsS := by
  -- 两个因子的正性由两条不等式前提直接给出（`linarith` 会先把目标化归成
  -- `0 < (1 / (2 * a1) + 1 / (2 * a2)) - 1 / R` 与 `0 < 1 / nSq - 1 / epsS`）。
  have hgeom' : 0 < 1 / (2 * a1) + 1 / (2 * a2) - 1 / R := by linarith
  have hPekar' : 0 < 1 / nSq - 1 / epsS := by linarith
  have hdE2 : 0 < dE ^ 2 := by positivity
  unfold lamOuter
  exact mul_pos (mul_pos hdE2 hgeom') hPekar'

/-- 重组能分解的加性：内层非负 + 外层严格正 ⇒ 总重组能严格正。
    （M4c 的复合定理用它把 `lamInner kk dq + lamOuter ...` 的正性交给
    `lamInner_nonneg` 与 `lamOuter_pos`。）--/
theorem lam_total_pos {lamIn lamOut : ℝ} (h₁ : 0 ≤ lamIn) (h₂ : 0 < lamOut) : 0 < lamIn + lamOut := by
  linarith

end PhotoLean.Marcus
