# theories/RACI/RESULTS.md — RACI (Restricted Access to a Conical Intersection): results and verdicts

> **Status: integration in progress** — the RACI modules are being ported from the ChemLean
> repository and registered against the existing graph. The bilingual results body below is
> completed at close-out.

## 1. Status / 现状

**English.** Integrated and verified: the RACI (Restricted Access to a Conical Intersection)
work, ported from the independent ChemLean repository (same Lean 4.17.0 / mathlib v4.17.0
toolchain), is PhotoLean's seventeenth theory — 11 modules building on the first pass, strict
scan clean, 59/59 theorems (46 upstream + 13 integration additions) with
`#print axioms` = `[propext, Classical.choice, Quot.sound]`, fidelity 71/71 word-for-word with 0
differences, registered on the relation graph at `Relations.lean` §17, and independently audited
by the final verifier (PASS).

**中文.** 已纳管并验证：RACI（受限锥形交叉）工作自独立的 ChemLean 仓库（同一 Lean 4.17.0 /
mathlib v4.17.0 工具链）移植，成为 PhotoLean 第十七个理论——11 个模块一次构建通过、严格扫描
干净、59/59 定理（46 上游 + 13 纳管新增）的 `#print axioms` 恰为
`[propext, Classical.choice, Quot.sound]`、保真 71/71 逐字零差异、已登记进关系图
`Relations.lean` §17，并经终审 verifier 独立审计（PASS）。

## 2. What the theory proves / 理论证明了什么

**English.** The accepted mechanism of aggregation-induced emission (AIE) — a chromophore dark
in dilute solution that lights up in the aggregate — as a machine-checked conditional theorem in
a declared model class:

* **M1 (the CI algebra).** A two-state adiabatic Hamiltonian has a conical intersection exactly
  where the discriminant `(a−d)² + 4b²` vanishes, equivalently `a = d ∧ b = 0`, equivalently
  eigenvalue degeneracy; the branching space of a surjective degeneracy map has codimension **2**
  (the von Neumann–Wigner rule), with the explicit linearized instance and its constant gap.
* **M2 (accessibility).** The free phase allows every torsion angle (accessibility gap `0`) while
  the aggregate allows only `|θ| ≥ δ` (gap `2δ > 0`): a strictly positive accessibility jump.
* **M3 (rates).** The barrier rate `A·exp(−βB)` and the Landau–Zener probability are strictly
  decreasing in the gap.
* **M4 (the RACI theorem).** With the radiative rate (approximately) unchanged, the yield is
  strictly antitone in the nonradiative rate, hence `Φ_agg > Φ_sol` — plus the channel-ratio
  generalization (Φ rises ⟺ `knr/kr` drops) and the kr-nonincreasing sufficient version.
* **M1\* (the seam).** Near a non-degenerate CI the conical set is locally a codimension-2
  submanifold slice (implicit function theorem).
* **M6 (Longuet–Higgins).** The lower eigenvector on the canonical loop around the CI flips sign
  after one circuit (monodromy −1).

The PhotoLean-standard additions: the named admissible model (`torsionH`, with its conical point
and its enhancement verdict at concrete parameters) and the named **non-model** (`nonModelNoCI`,
a constant diagonal Hamiltonian with an everywhere-empty conical set — the RACI premise chain is
uninstantiable there, kernel-checked), plus the ℚ decision layer (the discriminant's
`conical | gapped` zone classifier with correctness rows and cast coherence; decisions never
evaluate `exp` or `sqrt`).

**中文.** 聚集诱导发射（AIE）——在稀溶液中不发光的生色团在聚集态发光——其公认机制以声明式模型
类中的机器可检查条件定理形式呈现：

* **M1（CI 代数）。** 两态绝热 Hamiltonian 恰在判别式 `(a−d)² + 4b²` 为零处有锥形交叉，
  等价于 `a = d ∧ b = 0`，等价于本征值简并；满射简并映射的 branching space 余维 **2**
  （von Neumann–Wigner 规则），含显式线性化实例及其恒定能隙。
* **M2（可达性）。** 自由相允许一切扭转角（可达性能隙 `0`）而聚集相只允许 `|θ| ≥ δ`
  （能隙 `2δ > 0`）：严格为正的可达性跳变。
* **M3（速率）。** 势垒速率 `A·exp(−βB)` 与 Landau–Zener 概率随能隙严格递减。
* **M4（RACI 定理）。** 辐射速率（近似）不变时产额对非辐射速率严格反单调，故
  `Φ_agg > Φ_sol`——另含通道比推广（Φ 上升 ⟺ `knr/kr` 下降）与 kr 不增的充分版本。
* **M1\*（接缝）。** 非退化 CI 附近，锥形集局部上是余维 2 子流形切片（隐函数定理）。
* **M6（Longuet–Higgins）。** 绕 CI 的标准回路一周后较低本征矢变号（monodromy −1）。

PhotoLean 标准新增：命名容许模型（`torsionH`，含其锥形点与具体参数下的增强判决）与命名
**非模型**（`nonModelNoCI`，锥形集处处为空的常对角 Hamiltonian——RACI 前提链在其上不可
实例化，经内核验证），加 ℚ 决策层（判别式的 `conical | gapped` 分区分类器及其正确性行与
cast 相干；判定绝不求值 `exp` 或 `sqrt`）。

## 3. Position on the graph / 在关系图上的位置

**English.** `Relations.lean` §17: the composition certificate `RACI.quantumYield =
QuantumYield.yieldOf ![kr, knr] 0`; the enhancement as the dilution theorem run backwards
(`qy_two_channel_strictAnti_of_nr_lt`); the energy-gap-law link
(`log (barrierRate A β B) = log A − β·B`); the ICvsISC composition note (`fcBarrier lam lam = 0`
— the maximal-rate point); and the Marcus look-alike (the classical surfaces really cross at
`tsCoord`, a single-condition degeneracy, vs the CI's two-condition codimension-2 degeneracy).
All remaining pairs are registered in the §17 no-edge registry with reasons.

**中文.** `Relations.lean` §17：组合证书 `RACI.quantumYield = QuantumYield.yieldOf ![kr, knr] 0`；
增强作为稀释定理的反向读法（`qy_two_channel_strictAnti_of_nr_lt`）；能隙律链接
（`log (barrierRate A β B) = log A − β·B`）；ICvsISC 组合注记（`fcBarrier lam lam = 0`——
最大速率点）；以及 Marcus 形似注（经典两曲面在 `tsCoord` 真实相交——单条件简并，而 CI 是
双条件余维 2 简并）。其余全部配对在 §17 无边登记中附理由登记。

## 4. Honesty boundaries / 诚实边界

**English.** The theorem is conditional (AIE is not proved to happen universally): the
constraint must raise the accessibility gap and the radiative rate must be (approximately)
preserved; the named non-model shows the premise chain is uninstantiable where no conical
intersection exists. Declared, never proved: the two-state truncation, the single torsion
coordinate, the linearized gap model, the `|θ| ≥ δ` aggregate window, the Arrhenius/LZ rate
forms, the quantum-yield-as-rate-ratio reading, and all collected prefactors.

**中文.** 该定理是条件性的（并未证明 AIE 普遍发生）：约束必须提升可达性能隙、且辐射速率须
（近似）保持；命名非模型表明在不存在锥形交叉处前提链不可实例化。声明而不证：两态截断、
单一扭转坐标、线性能隙模型、`|θ| ≥ δ` 聚集窗口、Arrhenius/LZ 速率形、量子产率=速率比
读法、以及全部收集常数。
