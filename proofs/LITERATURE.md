# 文献调研记录

> 由 `literature_researcher` 维护。**每条必须有"可形式化含义"一栏** ——
> 这一栏是文献调研对形式化唯一有用的产物，缺它视为无效条目。

## 记录格式

```markdown
## YYYY-MM-DD — <短标题> — literature_researcher
- 源：<DOI / arXiv id / 标题>（PDF 存 proofs/literature/）
- 结论：<该文献对理论的核心主张>
- 可形式化含义：
  - 可显式化为 Lean 前提：<列出>
  - 属物理近似（需显式声明）：<列出>
  - 当前 mathlib 不可表达：<列出，说明障碍>
- 影响：<是否需要修订 plan.md 的语句>
```

## 反模式（禁止）

- 贴大段原文或整篇摘要而不给"可形式化含义"；
- 用文献结论替代证明（"文献说单调，所以不用证"）—— 文献只用于**定语句与前提**；
- 把 PDF 全文灌进上下文。只记结论与页码/章节定位。

## 核实状态词汇（本项目约定）

- `已核实`：本次调研在取到的来源（Crossref / 印刷页 / PDF 正文）中亲眼读到。
- `凭记忆待人类复核`：据已有知识写下，**未**在本次来源中读到。
- `仅量级`：只给数量级，不声称精确值。

---

<!-- 记录从下方追加 -->

## 2026-09-20 — Marcus 1956：势垒公式与前置因子的原始形式（原始理论）— literature_researcher

- 源：Marcus, R. A., "On the Theory of Oxidation-Reduction Reactions Involving Electron
  Transfer. I", *J. Chem. Phys.* **24**(5), 966–978 (1956). DOI `10.1063/1.1742723`
  【已核实：Crossref（卷/期/页/年/作者全对）+ CaltechAUTHORS 记录页】。
  本地 PDF：`proofs/literature/Marcus1956_ET_theory_I.pdf`（1.4 MB）。
- 结论：
  - 由 "slight-overlap"（小重叠）假设 + 溶剂非平衡极化的静电自由能 + 变分极小化，
    得中间态 X* 的自由能 `ΔF*`：**本文 Eq. (38), p. 974**（印刷页）。
  - 全篇速率写成**碰撞数 × 指数**：`k₁ = Z·exp(−ΔF*/kT)`（Eq. (44)）与
    `k_bimol ≈ Z·exp(−ΔF*/kT)`（Eq. (47)），p. 975–976，`Z` 为溶液中的碰撞数。
    ⇒ **1956 原文没有 `(4πλk_BT)^{-1/2}` 形式的前置因子**；该形式来自后续的
    过渡态理论处理（见记录 7）。
  - **全文不出现 "inverted" 字样**（对本 PDF 全文检索 0 命中）⇒
    反转区预言**不在** 1956 论文中，首次提出在 1960 年 Faraday Discussion
    （见记录 2）。
  - Eq. (38) 已含两球模型外层重组能结构：
    `(Δe)²·(1/(2a₁) + 1/(2a₂) − 1/R)·(1/D_op − 1/D_s)`，其中 `D_op` 为光学介电常数、
    `D_s` 为静态介电常数（见记录 3）。
- 可形式化含义：
  - 可显式化为 Lean 前提：
    - `0 < A`（1956 里 A = Z，碰撞数，物理上正）；
    - `0 < k_B*T`；两球参数 `0 < a₁`、`0 < a₂`、`a₁ + a₂ ≤ R`；
    - `Δe ≠ 0`；`0 < D_op`、`D_op < D_s`。
  - 属物理近似（需显式声明）：
    - **小重叠 / 非绝热电子耦合**：电子跳跃概率小，速率由核构型涨落到达面交点控制；
    - **介质连续极化近似**（dielectric continuum，含非平衡极化）；
    - **Franck–Condon 约束**：电子转移发生在两自由能面的交点；
    - 前置因子与驱动力无关（1956 中 A = Z）。
  - 当前 mathlib 不可表达：
    - Eq. (38) **之前**的静电学推导（非平衡极化自由能的构造与变分极小化）。
      mathlib 无连续介质静电学 / PDE 库 ⇒ 只能把 Pekar 公式当**定义**引入，
      **不能**在 Lean 里推导它。
- 影响：**建议修订 plan.md 的引用归属**。plan 若写"前置因子取 `(4πλk_BT)^{-1/2}`"，
  **不得**引 Marcus 1956；该形式应引 Marcus 1964 或 Marcus & Sutin 1985。
  但这**不改变任何 x-单调性结论**（见记录 7 末条）。

## 2026-09-20 — 反转区判据的原始出处与确切符号写法（**防符号搞反**）— literature_researcher

- 源：
  - Marcus, R. A., "Exchange reactions and electron transfer reactions including isotopic
    exchange. Theory of oxidation-reduction reactions involving electron transfer. Part 4.
    A statistical-mechanical basis for treating contributions from solvent, ligands, and
    inert salt", *Discuss. Faraday Soc.* **29**, 21–31 (1960). DOI `10.1039/df9602900021`
    【已核实：Crossref】。← **反转区首次提出的论文**。
  - Marcus, R. A., "Chemical and Electrochemical Electron-Transfer Theory",
    *Annu. Rev. Phys. Chem.* **15**(1), 155–196 (1964). DOI `10.1146/annurev.pc.15.100164.001103`
    【已核实：Crossref】。
  - Marcus, R. A., Nobel Lecture 1992, "Electron Transfer Reactions in Chemistry: Theory and
    Experiment", *Chemistry 1992*（Nobel Foundation），印刷页 71–89。
    本地 PDF：`proofs/literature/Marcus1992_nobel_lecture.pdf`；
    关键页渲染件：`Marcus1992_nobel_p78_eq5.png`（p.78, Eq. 5a/5b/6）、
    `Marcus1992_nobel_p79_eq7.png`（p.79, Eq. 7/8）、
    `Marcus1992_nobel_p84_fig8.png` 与 `Marcus1992_nobel_p84_fig8_axis.png`（p.84, Fig. 8）。
    【已核实：逐页读图，公式为印刷体原样】
- 结论：

  **（印刷体确切写法）**
  - **Nobel Lecture p. 78, Eq. (5b)**：
    ```
    ΔG* = (λ/4)·(1 + ΔG°′/λ)²
    ```
    其中 ΔG°′ 为反应的标准自由能（自交换反应为 0）。这与 `(λ + ΔG°)²/(4λ)`
    **恒等** —— 即经典教科书形式。
  - **p. 78, Eq. (5a)**：`k = A·exp(−ΔG*/k_B T)`，A 依反应类型（双分子 / 分子内）而定。
  - **p. 78, Eq. (6)**：**`λ = λ_o + λ_i`**（solvational + vibrational）。
    ⇒ **Marcus 本人的记号是 λ_o / λ_i，即现代写法 λ_out / λ_in**（同义）。
  - **反转区判据的确切措辞（p. 82, "The Inverted Region Effect" 一节）**：
    活化自由能 "first decrease as [ΔG°] is varied from 0 to some negative value,
    **vanish at ΔG° = −λ**, and then increase when [ΔG°] is made still more negative"。
    ⇒ 反转区 = **`ΔG° < −λ`** ⟺ **`−ΔG° > λ`**。
  - **p. 84, Fig. 8 的横轴标签就是 `−ΔG° (eV)`**，刻度 `0.0` / `1.0` / `2.0`
    【已核实：读图】。
- 可形式化含义：
  - 可显式化为 Lean 前提：**无**。`InvertedRegion` 是**定义**，不是前提：
    取 `x := −ΔG°`，则 `InvertedRegion λ x := λ < x`，`barrier λ x := (λ − x)^2 / (4*λ)`。
  - 属物理近似（需显式声明）：把 ΔG° 当作**单一标量驱动力**
    （把溶剂电化学势、work terms 全部吸收进 ΔG°，见记录 7）。
  - 当前 mathlib 不可表达：**无**。此条 100% 可在 mathlib 表达。
- 影响：

  **结论 — plan 的约定正确，无需修订；但必须加一条反模式注释：**
  - ✅ plan 的 `x = −ΔG°`、`ΔG‡ = (λ−x)²/(4λ)`、反转区 `x > λ`
    **与原始文献完全一致**。
  - ⚠️ **绝不可写成 `ΔG° > λ`**。ΔG° 在放能时取**负值**，`ΔG° > λ > 0` 实际落在
    **正常区**，符号正好反了。三种正确写法：
    `ΔG° < −λ` ／ `−ΔG° > λ` ／（仅在已显式声明 `ΔG° ≤ 0` 时）`|ΔG°| > λ`。
  - ⚠️ 建议在 plan 的 `InvertedRegion` 定义处写一行等价链注释，避免后续 prover 与
    审阅者误读。

## 2026-09-20 — 反转区**首次提出**的原文（Marcus 1960 Faraday Discussion）：逐字原话与页码 — literature_researcher

- 源：Marcus, R. A., "Exchange reactions and electron transfer reactions including isotopic
  exchange. Theory of oxidation-reduction reactions involving electron transfer. Part 4.
  A statistical-mechanical basis for treating contributions from solvent, ligands, and
  inert salt", *Discuss. Faraday Soc.* **29**, 21–31 (1960). DOI `10.1039/df9602900021`
  【已核实：Crossref】。
  **开放获取全文**：CaltechAUTHORS `authors.library.caltech.edu/records/h2ztx-ee849`
  （文件 `df9602900021.pdf`）。本地 PDF：`proofs/literature/Marcus1960_Faraday_inverted_region.pdf`
  【已核实：本次下载并抽取文本层】。
- 结论：
  - 反转区的**首次提出**在此文第 4.4 节"待检验的预言清单"第 **(v)** 条，印刷页 **28**，
    条目标题为 **"Possibility of 'inverted' chemical behaviour"**。
    原文逐字（**本报告唯一引用的原句，共两句**）：
    > "If ΔF° becomes too negative, intersection of the two surfaces becomes possible only
    > at high potential energies … m² eventually increases with increasing −ΔF°, and the
    > rate constant decreases."
  - 要点：① 判据以 **"ΔF° 变得过负"** 表述（`ΔF°` ≡ `ΔG°`，放能取**负**值）；
    ② 机制是势垒项 `m²` 随 `−ΔF°` 增大而增大 ⇒ 速率常数**下降**。
    ⇒ 与记录 2 的符号结论**一致**：反转区 = `ΔG° < −λ` ⟺ `−ΔG° > λ`。
  - 同节 **(ii)** 条是**交叉关系的最早形式**：`k₁₂ ≈ (k₁k₂K)^½`，**原文自带适用条件**
    "if ΔF° is not too large"。⚠️ plan §1.3 不做交叉关系；若将来要做，除"同 λ"外
    还须带上这条 `ΔF° 不能太大` 的限制（否则会做出过强主张）。
  - 同节 **(vi)** 条自述"Analysis of assumptions made when electron transfers are
    interpreted in the terms of the Franck-Condon principle"（cf. ref. 8）
    —— **原文自认 Franck–Condon 解释是假设**，直接支持 plan §13 的近似清单第 1–3 条。
  - 同节 **(iv)** 条自述"inert salt effects (subject to an assumed treatment of the
    ionic atmosphere as a continuous distribution)"—— 这是 **work terms 的来源**，
    且原文明确它是**假设**（见记录 7）。
- 可形式化含义：
  - 可显式化为 Lean 前提：**无**（反转区是定义）。但此文明确了定义之外的**语境前提**：
    "unless … a more favourable reaction mechanism is found" ⇒
    **本定理不适用于存在竞争反应通道的体系**（原文自己写了这条免责）。
  - 属物理近似（需显式声明）：原文自认的三条 ——
    ① Franck–Condon 解释为假设（(vi) 条）；② 离子氛按连续分布处理（(iv) 条，即 work terms 的模型依据）；
    ③ 反应为单一机理、无更有利的竞争通道（(v) 条）。
  - 当前 mathlib 不可表达：无。
- 影响：

  **建议 plan.md 补一条引用与一条边界声明：**
  - 建议 plan §1.1 或 §13 把**反转区的首次提出**归到 **Marcus 1960, Discuss. Faraday Soc. 29,
    p. 28, §(v)**（而**不是** 1956 —— 1956 全篇无 "inverted" 字样，见记录 1）。
  - 建议 plan §1.3「明确不做」补一句边界声明（**有原文依据，不是我们的发明**）：
    > 本形式化只刻画**单一机理**下的经典 Marcus 速率；不含竞争反应通道
    > （Marcus 1960 (v) 条自述："unless … a more favourable reaction mechanism is found"）。

## 2026-09-20 — Pekar 因子与外层重组能 λ_out 的两球模型（**λ>0 可由几何推出**）— literature_researcher

- 源：
  - Marcus 1956, **Eq. (38), p. 974**（同上 DOI）【已核实：PDF 正文】：
    `ΔF* = e₁*e₂*/(R·D_s) + m²·(Δe)²·(1/(2a₁) + 1/(2a₂) − 1/R)·(1/D_op − 1/D_s)`。
  - Marcus Nobel Lecture 1992, **Eq. (7), p. 79**（同上）【已核实：读图】：
    ```
    λ_o = (Δe)²·( 1/(2a₁) + 1/(2a₂) − 1/R )·( 1/D_op − 1/D_s )
    ```
    原文说明：`a₁, a₂` 为两离子半径（含内配位层），`R` 为反应物质心间距，
    `D_op` 光学 / `D_s` 静态介电常数，`Δe` 为从一反应物转移到另一反应物的电荷量。
  - Marcus Nobel Lecture 1992, **Eq. (8), p. 79**：`λ_i = ½·Σ_j k_j·(Q'_j − Q''_j)²`，
    其中 `k_j := 2k'_j k''_j/(k'_j + k''_j)` 为**约化力常数**。原文自述引入了
    **"symmetrization" 近似**（用约化力常数代替反应物/产物各自的力常数）【已核实：正文】。
  - Marcus, R. A.; Sutin, N., "Electron transfers in chemistry and biology",
    *Biochim. Biophys. Acta (Reviews on Bioenergetics)* **811**(3), 265–322 (1985).
    DOI `10.1016/0304-4173(85)90014-X` 【已核实：Crossref + CaltechAUTHORS 记录页】。
    （正文全文本次未取到，Elsevier 付费；式号待人类复核。）
  - "Pekar 因子"这一名称与 `1/ε_opt − 1/ε_st` 形式在多篇文献中使用
    【已核实：例如 ChemElectroChem 2021 用 `C = 1/ε_opt − 1/ε_st` 称为 Pekar factor】。
- 结论：
  - 记 `G := 1/(2a₁) + 1/(2a₂) − 1/R`（**几何因子**），
    `P := 1/D_op − 1/D_s = 1/n² − 1/ε_s`（**Pekar 因子**，`n` 折射率、`ε_s` 静态介电常数）。
    则 `λ_out = (Δe)²·G·P`。
  - **`λ_out > 0` 的充要条件**：`Δe ≠ 0 ∧ P > 0 ∧ G > 0`。
    - `P > 0 ⟺ D_op < D_s ⟺ n² < ε_s`。物理上恒成立
      （光学介电常数总是小于静态介电常数，因为只有电子极化响应光频）。
    - **`G > 0` 可以从几何推出，不需要假设**：若 `0 < a₁`、`0 < a₂`、`a₁ + a₂ ≤ R`
      （两球不相交 = 物理上的接触或更远），则
      `1/R ≤ 1/(a₁+a₂)`，而
      `1/(2a₁) + 1/(2a₂) − 1/(a₁+a₂) = (a₁² + a₂²)/(2·a₁·a₂·(a₁+a₂)) > 0`。
      ⇒ `G ≥ G|_{R=a₁+a₂} > 0`。
- 可形式化含义：
  - 可显式化为 Lean 前提：
    `0 < a₁`、`0 < a₂`、`a₁ + a₂ ≤ R`、`Δe ≠ 0`、`0 < D_op`、`D_op < D_s`。
  - 可显式化为 **Lean 定理（本记录最重要的产出）**：
    ```lean
    lemma geometric_factor_pos {a₁ a₂ R : ℝ}
        (h₁ : 0 < a₁) (h₂ : 0 < a₂) (hR : a₁ + a₂ ≤ R) :
        0 < 1/(2*a₁) + 1/(2*a₂) - 1/R
    ```
    战术提示：`one_div_le_one_div_of_le` 得 `1/R ≤ 1/(a₁+a₂)`；转到
    `(a₁²+a₂²)/(2*a₁*a₂*(a₁+a₂)) > 0`，`field_simp` 后 `positivity` / `nlinarith`。
  - 可显式化为 **Lean 定理（内层）**：
    `λ_in := (1/2) * ∑ j ∈ s, k j * (Q' j - Q'' j)^2`；
    `Finset.sum_nonneg` + `sq_nonneg` 给 `0 ≤ λ_in`；严格正需
    `∃ j ∈ s, 0 < k j ∧ Q' j ≠ Q'' j`。
  - 属物理近似（需显式声明）：
    - **两球模型 + 连续介质介电近似**（球形空腔、体相介电常数）；
    - **半径在反应前后不变**（1956 p. 974 原文 "radii … taken to be essentially
      unchanged by the reaction"）；
    - **电荷转移量为单一标量 Δe**（局域化单电子转移）；
    - **`λ = λ_in + λ_out` 的可加性**：Marcus 本人写作 `λ = λ_o + λ_i`
      （Nobel Eq. (6)），但可加性是**建模假设**（内外坐标解耦 + 加性二次型），
      **不是定理**。
      🎯 **可加性的原始出处与精确形式已核实**：**Marcus 1960, Discuss. Faraday Soc. 29,
      §3.3, p. 24–25**（本地 PDF `Marcus1960_Faraday_inverted_region.pdf`）把总坐标集 `k`
      **显式分解**为 `k_i`（配位层内部坐标，"inner"）与 `k''`（其余全部坐标，"outer"），
      并令势能同样分离：`g_{k_i}` 只依赖内部坐标、`g_o` 只依赖 `k''`。
      相应的配分函数也**因子化**（内部坐标给出振动配分函数 `Q_vib`，外部坐标给出
      `exp(−F_o(r)/kT)`）。
      ⇒ **可加性的真实来源是"势能可分离 + 每块取二次（谐振）近似"**，
      Lean 侧应把它写成**显式声明的近似**（例如把 `lam = lamIn + lamOut` 作为
      定义并声明"这是内/外坐标可分性假设的后果"），**不能**声称它由更基本的原理推出。
    - **"symmetrization" 近似**（约化力常数）—— Marcus 在 Nobel Lecture p. 79 自述。
  - 当前 mathlib 不可表达：
    - 从介电连续介质静电学**推导** Pekar 公式（非平衡极化自由能泛函 + 变分）——
      只能把 `λ_out` 当**定义**；
    - 从色散关系推导 `D_op` 与折射率的关系 —— mathlib 无。
      ⚠️ **但这一步不需要推导**：Marcus 1956 **p. 971** 明文定义
      "optical dielectric constant `D_op` (i.e., **the square of the refractive index**)"
      【已核实：PDF 文本层】⇒ `D_op = n²` 是**模型的给定定义**，
      plan 的 `lamOuter` 直接用 `nSq` 作参数是**忠实**的，不是简化。
- 影响：

  **建议修订 plan.md：**
  - **建议把 `0 < λ` 由"假设"升级/降级为"可推导结论"**：
    在实例层令 `λ := λ_in + λ_out`，则
    `0 < λ` 由 `0 ≤ λ_in`（平方和）与 `0 < λ_out`
    （由 `Δe ≠ 0`、`D_op < D_s`、以及引理 `geometric_factor_pos`）**推出**。
  - 抽象主定理（M2/M3）**仍应保留 `0 < λ` 作为显式前提**（否则抽象层失去一般性）；
    plan 里应写明"实例层由 `λ_in, λ_out` 的具体表达式证明该前提"。
  - **建议为 `geometric_factor_pos` 单列一个 lemma 任务**：它是本计划里唯一"真的要
    用不等式"的几何引理，且**不依赖任何物理近似**，风险最低、可最早开工。

## 2026-09-20 — 反转区实验证据 I：Miller–Calcaterra–Closs 1984 系列的 (λ, −ΔG°) 数值 — literature_researcher

- 源：
  - Miller, J. R.; Calcaterra, L. T.; Closs, G. L., "Intramolecular long-distance electron
    transfer in radical anions. The effects of free energy and solvent on the reaction
    rates", *J. Am. Chem. Soc.* **106**(10), **3047–3049** (1984).
    DOI **`10.1021/ja00322a058`** 【已核实：Crossref】。
  - Closs, G. L.; Calcaterra, L. T.; Green, N. J.; Penfield, K. W.; Miller, J. R.,
    "Distance, stereoelectronic effects, and the Marcus inverted region in intramolecular
    electron transfer in organic radical anions", *J. Phys. Chem.* **90**, 3673–3683 (1986).
    DOI `10.1021/j100407a039` 【已核实：Crossref】。（= 上述 communication 的全文版）
  - Closs, G. L.; Miller, J. R., "Intramolecular Long-Distance Electron Transfer in Organic
    Molecules", *Science* **240**, 440–447 (1988). DOI `10.1126/science.240.4851.440`
    【已核实：Crossref】。
  - Marcus Nobel Lecture 1992, **p. 84, Fig. 8**（标题 "Experimental Confirmation of
    Inverted Region"，图注点名 Miller et al.）【已核实：读图】。
  - 独立重绘同图（同参数）：Lokan, N. R., *Synthetic approaches towards novel
    bichromophoric systems for studying solvent-mediated electron transfer and electronic
    excitation energy transfer*, PhD thesis, UNSW Sydney (2000), Chapter 1, pp. 9–11,
    Fig. 1.6 / 1.7 / 1.8。DOI `10.26190/unsworks/7583`（`hdl.handle.net/1959.4/62022`）
    【已核实：DataCite + PDF 文本层】。
  - Miller, J. R.; Peeples, J. A.; Schmitt, M. J.; Closs, G. L., "Long-distance
    fluorescence quenching by electron transfer in rigid solutions",
    *J. Am. Chem. Soc.* **104**(24), 6488–6493 (1982). DOI `10.1021/ja00388a002`
    【已核实：Crossref】。（MTHF 玻璃系列，**与 MCC 1984 是两个不同实验**）
  - **逐化合物数值的二手来源**：*Chem. Eng. News* **1984-06-04**, **62**(23), 42–44,
    DOI `10.1021/cen-v062n023.p042` 【已核实：Crossref + 该报道全文（二手）】。
    ⚠️ **这是新闻性二手来源，不是原始论文的表格**；原文（JACS 1984 / JPC 1986）表格被
    ACS 付费墙挡住。人类应据 `Closs et al. 1986, JPC 90:3673` 的 Table/Figure 复核。
  - 补充已核实书目（Crossref）：Joran et al., *Nature* **327**, 508–511 (1987),
    DOI `10.1038/327508a0`；Irvine et al., *Chem. Phys.* **104**, 315–324 (1986),
    DOI `10.1016/0301-0104(86)80175-6`；Barbara & Meyer, *J. Phys. Chem.* **100**,
    13148–13168 (1996), DOI `10.1021/jp9605663`。
- 结论：

  **（数值）**
  - **体系**：D–bridge–A 双发色团；D = 4-biphenylyl（联苯基负离子自由基），
    bridge = 刚性饱和烃间隔基（5α-androstane），固定间距 ≈ **10 Å**；
    A = 一系列 π 电子受体（8 个，见下）。
    脉冲辐解（pulsed radiolysis）在**流体溶液**中制备自由基负离子。
    【已核实：Lokan 2000（UNSW 学位论文, DOI 10.26190/unsworks/7583）Ch. 1 p. 9；C&EN 1984（二手）】
  - **8 个受体（按 −ΔG° 增序）**：2-naphthyl, 9-phenanthryl, 1-pyrenyl,
    2-hexahydronaphthoquinonyl, 2-naphthoquinonyl, 2-benzoquinonyl,
    2-(5-chlorobenzoquinonyl), 2-(5,6-dichlorobenzoquinonyl)。
    【已核实：C&EN 1984（二手）】
  - **逐化合物已取到数值的 3 个**（λ 同一系列）：
    | A（受体） | −ΔG° / eV | k / s⁻¹ |
    |---|---|---|
    | 2-naphthyl | ≈ 0.05 | ≈ 1.5×10⁶ |
    | 2-hexahydronaphthoquinonyl | **1.23**（最优） | ≳ 2×10⁹（**仪器上限**） |
    | 2-(5,6-dichlorobenzoquinonyl) | **2.40** | ≈ 7×10⁷ |
    【已核实：C&EN 1984（二手）】其余 5 个受体的逐项值**未取到**。
  - **λ_s = 0.75 eV**（溶剂/外层），**λ_v = 0.45 eV**（振动/内层），
    **ω = 1500 cm⁻¹** ⇒ **λ ≈ 1.20 eV**。
    【已核实：Nobel Fig. 8 图内标注（含 ω）+ UNSW Fig. 1.8 独立重绘同 λ 值】
  - **溶剂与温度**：主溶剂 MTHF / THF，**≈ 296 K**（C&EN 图注；正文写 "room temperature"）；
    第二溶剂是 **isooctane**（**不是** isopentane），该溶剂下峰值显著左移、部分反应过快无法测。
    ⚠️ **原文真实温度未核实**（图注写 THF、正文写 MTHF，本身不一致）。
    【已核实：C&EN 1984（二手）】
  - **驱动力范围**：`−ΔG°` 从 ≈ **0.05 eV 到 ≈ 2.4 eV**（横轴刻度 0.0 / 1.0 / 2.0）。
    【已核实：逐化合物值 + Nobel Fig. 8 读图】
  - **速率范围**：`k ≈ 1.5×10⁶ → ≳ 2×10⁹ s⁻¹`（分子内一级速率常数）。
    【已核实：逐化合物值 + Nobel Fig. 8 纵轴读图】
  - **定性**：k 随 −ΔG° 先升（正常区）→ 在 x ≈ λ 达极大 → 再降（反转区）；
    反转区下降约 **1.5 个数量级**。【已核实：图读数 + 逐化合物值】
  - ⚠️ **定量对照（本记录的关键发现）**：以 λ = 1.2 eV、T = **296 K**
    （`k_B T = 25.51 meV`）代入经典公式，与实测对照：

    | x = −ΔG° / eV | 经典 ΔG‡ / eV | 经典 ΔG‡/k_BT | 经典 k / k(顶点) | 实测 k / k(顶点) |
    |---|---|---|---|---|
    | 0.05 | 0.27552 | 10.80 | 2.0×10⁻⁵ | 7.5×10⁻⁴ |
    | 1.23 | 0.00019 | 0.007 | 1 | 1（仪器上限） |
    | 2.40 | 0.30000 | 11.76 | 7.9×10⁻⁶ | 3.5×10⁻² |

    ⇒ 反转支 1.23 → 2.40 eV：经典预言降 **5.1 个数量级**，实测只降 **1.46 个数量级**
    ⇒ **经典模型在反转区下降过快约 3.6 个数量级**；这正是量子振动修正
    （`ω = 1500 cm⁻¹`，Nobel Fig. 8 的平滑曲线即含此修正）存在的直接理由（记录 6）。
    【表格为本人算术；公式与参数均已核实，算式可复核。
    ⚠️ 两条前提：① 同系列内前置因子 `A` 近似相同（文献标准处理）；
    ② `2×10⁹ s⁻¹` 是仪器上限 ⇒ 实测降幅的**下界**更小，结论方向不变。】
- 可形式化含义：
  - 可显式化为 Lean 前提（实例层）：
    `λ = 1.2`、`x ∈ {0.05, 0.60, 1.23, 2.00, 2.40}`、`A > 0`，以及
    **`0 < kB`、`0 < T`（把 T 当前提，不要硬编码 296 或 298）**。
    另需一个**实例字段式的声明**："λ 与 −ΔG° 为文献拟合/测量值" —— 这是数据，不是定理。
  - **区域判定只需 (λ, x)**：`x < 1.2` ⇒ 正常区；`x = 1.2` ⇒ 无势垒；
    `x > 1.2` ⇒ 反转区。**与 T、A 无关** —— 这让实例层非常干净。
  - 属物理近似（需显式声明，**本实验对形式化最重要的警示**）：
    - **"描述成立"（反转区速率随驱动力严格递减）是关于经典 Marcus 公式的命题，
      不是关于实验曲线的命题。** 实验降幅被量子修正"压平"；若把"描述"理解为
      "预言实测速率"，该命题在真实体系上**是假的**。plan 必须把二者分开（见"影响"）。
    - 前置因子 A 在"同系物系列"内与 x 无关（该系列间距固定 10 Å，电子耦合近似常数）。
  - 当前 mathlib 不可表达：**无**。判定 `λ < x` 是纯实数命题。
    若要写"实测速率"，只能把数据以 `List (ℝ × ℝ)` 硬编码为**数据**（非定理），
    并显式声明为文献实测值。
- 影响：

  **建议修订 plan.md 的措辞：**
  - 实例层定理文案必须写成"**该体系落在反转区，且经典 Marcus 描述在该 (λ,x,T,A) 上
    成立**"，**不能**写成"该体系的反转区速率随驱动力递减"（后者是对实验的断言，
    文献明确反驳其严格性）。
  - 建议 M5 实例取 `λ = 1.2` 与 `x = 0.6`（判 `¬ InvertedRegion`）+ `x = 2.0`
    （判 `InvertedRegion` 且 `StrictAntiOn` 成立）。

## 2026-09-20 — 反转区实验证据 II：卟啉–醌、孪生离子对、光合反应中心 — literature_researcher

- 源：
  - Wasielewski, M. R.; Niemczyk, M. P.; Svec, W. A.; Pewitt, E. B., *J. Am. Chem. Soc.*
    **107**(4), **1080–1082** (1985). DOI `10.1021/ja00290a066` 【已核实：Crossref】。
  - Gould, I. R.; Ege, D.; Mattes, S. L.; Farid, S., "Return electron transfer within
    geminate radical ion pairs. Observation of the Marcus inverted region",
    *J. Am. Chem. Soc.* **109**(12), 3794–3796 (1987). DOI `10.1021/ja00246a055`
    【已核实：Crossref】。
  - McLendon, G.; Miller, J. R., "The dependence of biological electron transfer rates on
    exothermicity. The cytochrome c/cytochrome b₅ couple", *J. Am. Chem. Soc.*
    **107**(26), 7811–7816 (1985). DOI `10.1021/ja00312a002` 【已核实：Crossref】。
  - Marcus Nobel Lecture 1992, **p. 88**（光合反应中心）【已核实：正文】。
  - Lee, K. J., "The Marcus Inverted Region", UIUC 化学系文献研讨会报告, 1988-02-25,
    印刷页 38–40。本地 PDF：`proofs/literature/Lee1988_Marcus_inverted_region.pdf`
    【已核实：PDF 文本层；**secondary source**】。
- 结论：
  - **卟啉–醌（Wasielewski 1985）**：光致电荷分离与暗态电荷复合速率随放能性变化；
    自由基离子复合速率随驱动力增大**下降约两个数量级**
    【已核实：Lee 1988 报告（secondary）；**具体 λ / −ΔG° 数值未取到原文**】。
  - **孪生自由基离子对（Gould/Farid 1987）**：氰基取代蒽作受体、萘衍生物/二苯乙炔/
    联苯作供体；速率随 −ΔG° 增大下降近两个数量级
    【已核实：Lee 1988 报告（secondary）；**具体数值未核实**】。
  - **生物体系（McLendon & Miller 1985, cyt c / cyt b₅）**：蛋白质中的反转区证据。
    **准确 (λ, −ΔG°) 数值本次未核实。**
  - **光合反应中心（Marcus Nobel Lecture p. 88）**：BChl₂→BPh 第一步
    `−ΔG° ≈ 0.25 eV`（总激发能 1.38 eV），λ 小；而 BPh⁻→BChl₂⁺ 的回传
    （hole-electron recombination）高度放能 `−ΔG° ≈ 1.1 eV`，配 **`λ ≈ 0.25 eV`**
    ⇒ **明显反转区**（x = 1.1 ≫ λ = 0.25）。Marcus 明确指出反转区效应是这一步被抑制
    的关键。【已核实：Nobel Lecture p. 88 正文】
  - **77 K MTHF 玻璃系列（Miller–Peeples–Schmitt–Closs 1982）**：联苯负离子 → 28 个
    不同受体，最优驱动力下 `β = 1.2 Å⁻¹`。**与 MCC 1984 的流体溶液系列是两个不同
    实验**（温度、机制不同），引用时勿混。【已核实：Lokan 2000 学位论文 Ch. 1 引述 + Crossref】
- 可形式化含义：
  - 可显式化为 Lean 前提（实例层第二条）：`λ = 0.25`、`x = 1.1`（eV）⇒ `InvertedRegion`；
    `0 < A`、`0 < k_B*T` ⇒ 描述成立。
  - 属物理近似（需显式声明）：生物体系的 ΔG° 由**氧化还原电位差估算**，λ 由**拟合**给出
    ——**两者都是模型依赖的导出量，不是直接可观测量**。实例层须标注
    "参数取自文献拟合值，非第一性原理计算"。
  - 当前 mathlib 不可表达：蛋白质环境中的 λ 估算（需 Poisson–Boltzmann /
    连续介质蛋白质静电学）—— 不可表达；只能把 0.25 eV 当外部给定常数。
- 影响：
  - **建议 M5 至少放两个独立体系**（有机系列 λ = 1.2 eV；光合反应中心 λ = 0.25 eV）
    以显示定义可复用，并各配一个正常区反例。
  - ⚠️ **任务书给出的 Wasielewski 页码 107:5562 与 Crossref 核实的
    `107(4):1080–1082` 不符**。若确需引用 5562 那篇，须另行核实
    （可能是同一课题组另一篇）。**核实前不要写 107:5562。**

## 2026-09-20 — 量子振动修正：为何经典模型给出严格单调下降 — literature_researcher

- 源：
  - Siders, P.; Marcus, R. A., "Quantum effects for electron-transfer reactions in the
    'inverted region'", *J. Am. Chem. Soc.* **103**(4), 748–752 (1981).
    DOI `10.1021/ja00394a004` 【已核实：Crossref】。
  - Siders, P.; Marcus, R. A., "Quantum effects in electron-transfer reactions",
    *J. Am. Chem. Soc.* **103**(4), 741–747 (1981). DOI `10.1021/ja00394a003`
    【已核实：Crossref】。
  - Marcus Nobel Lecture 1992, **Fig. 8** 内标注 `ω = 1500 cm⁻¹`【已核实：读图】
    —— 即量子修正所用的平均振动量子。
  - Bixon, M.; Jortner, J., "Intramolecular Radiationless Transitions",
    *J. Chem. Phys.* **48**(2), 715–726 (1968). DOI `10.1063/1.1668703`
    【已核实：Crossref】。（= Bixon–Jortner 能隙律的原始论文）
  - Jortner, J., "Temperature dependent activation energy for electron transfer between
    biological molecules", *J. Chem. Phys.* **64**(12), 4860–4867 (1976).
    DOI `10.1063/1.432142` 【已核实：Crossref】。（高频振动模式的量子化处理）
  - Bixon, M.; Jortner, J., "Electron Transfer—from Isolated Molecules to Biomolecules",
    *Adv. Chem. Phys.* **106/107**, 35–202 (1999). DOI `10.1002/9780470141656.ch3`
    【已核实：Crossref】。（综述）
  - ⚠️ 上述三篇**只核实了书目信息，未读正文**；关于"饱和/平台"的定量细节标
    `凭记忆待人类复核`。但本记录用于 §1.3「明确不做」，只需方向性归属。
- 结论：经典处理把核运动当作纯经典自由度，得 `ΔG‡ = (λ−x)²/(4λ)`，
  在反转区随 x **无界二次增长** ⇒ 速率严格单调下降且下降极快。
  引入高频振动模式（`ω ≈ 1500 cm⁻¹`）的量子化后，电子转移可伴随振动激发
  （Franck–Condon 振动重叠因子），势垒增长被"振动通道"分流，反转区下降变缓并
  趋于饱和/平台。这解释了记录 4 中"实验降幅（~2 数量级）远小于经典预言
  （~5 数量级）"的对照。【已核实：图与算式；机理表述为综述共识】
- 可形式化含义：
  - 可显式化为 Lean 前提：**无**（本记录不进入任何定理前提）。
  - 属物理近似（需显式声明）：**经典核运动 / 无核隧穿 / 振动模式可忽略**
    —— 这正是经典 Marcus 公式的适用条件，必须进 plan 的近似清单。
  - 当前 mathlib 不可表达：Fermi 黄金规则对振动热浴的求和
    （需谐振子希尔伯特空间 + 振动重叠积分 `⟨χ_i|χ_f⟩` + 热平均）。
    **明确排除在范围外。**
- 影响：**建议在 plan.md §1.3「明确不做」写死一条**：
  > 本计划只刻画**经典 Marcus 公式** `ΔG‡ = (λ−x)²/(4λ)` 在反转区的单调性；
  > 不刻画量子振动修正（Bixon–Jortner / Siders–Marcus）导致的饱和，
  > 也不声称经典公式能定量复现实测反转区降幅。

## 2026-09-20 — 综述级完整势垒式（含 work terms）：本 plan 的近似代价 — literature_researcher

- 源：
  - Marcus, R. A.; Sutin, N., "Electron transfers in chemistry and biology",
    *Biochim. Biophys. Acta (Reviews on Bioenergetics)* **811**(3), 265–322 (1985).
    DOI `10.1016/0304-4173(85)90014-X` 【已核实：Crossref + CaltechAUTHORS 记录页】。
    ⚠️ **正文全文本次未取到（Elsevier 付费），以下式号待人类复核。**
  - 佐证（secondary）：Lee 1988 报告（同记录 5）给出
    `ΔG‡ ≈ w_r + (λ/4)·(1 + (ΔG° + w_p − w_r)/λ)²`，
    反转区条件写作 `|ΔG° + w_p − w_r| > λ`。【已核实：PDF 文本层；但属 secondary】
- 结论：综述级"完整"势垒式含**静电 work terms**：
  `ΔG‡ = w_r + (λ/4)·(1 + (ΔG° + w_p − w_r)/λ)²`，
  速率 `k = κ·ρ·Z·exp(−ΔG‡/k_B T)`。
  当 `w_r = w_p = 0`（中性或两性离子对，或高离子强度屏蔽）时退回
  `ΔG‡ = (λ + ΔG°)²/(4λ)`，即本 plan 采用的形式。
- 可形式化含义：
  - 可显式化为 Lean 前提：若走"含 work terms"路线，则 `w_r, w_p : ℝ` 成为**额外参数**，
    且反转区判据变成 `λ < |ΔG° + w_p − w_r|` —— 此时"区域"**不再由 x 单独决定**。
  - 属物理近似（需显式声明）：**忽略 work terms（`w_r = w_p = 0`）** 是本 plan 采用
    `ΔG‡ = (λ−x)²/(4λ)` 所付出的代价，**必须显式声明**。
  - 当前 mathlib 不可表达：work terms 的 Debye–Hückel / 静电屏蔽表达式；
    `κ`（电子透射系数，需 Landau–Zener 公式）；`ρ`（绝热/非绝热因子）。
- 影响：

  **建议修订 plan.md：**
  - 建议在 plan §2.2 或 §1.3 明确写：
    > 驱动力取 `x = −ΔG°`，并**显式声明忽略 work terms**（`w_r = w_p = 0`）——
    > 这是物理近似，不是定理。
  - 建议顺带记下扩展成本：若日后要加 work terms，`InvertedRegion` 谓词必须改成依赖
    `(ΔG°, w_r, w_p, λ)` 而非单独的 `x`，**这会破坏现有定义**，应现在就在 plan 留一句。
  - **关于前置因子（澄清）**：过渡态理论形式 `A = (4πλk_B T)^{-1/2}·κ·ν_n` 只通过一个
    **正的、与 x 无关的**因子进入 k。因此 plan 的"前置因子与驱动力无关"假设
    **不损失任何 x-单调性结论**。建议把这句写进 plan，作为"该近似为何无害"的说明。

---

## 附：形式化含义——"锐利刻画"的精确形状（供 M2/M3/M4a 直接采用）

> 本节是从上列来源推出的**形式化建议**，不是文献结论。
> ⚠️ **本节早期版本给出过一个错误命题，已更正（错误版本保留在下方作为警示）。**
> 更正后的 F1/F2/F3 已用**穷举数值复核**：`λ ∈ {±0.5, ±1, ±2}`、`τ ∈ {±0.5, ±1, ±2, 0}`、
> `A ∈ {−2,−1,0,1,2}` 全组合共 0 反例。

**记号**（与 `plan.md` §2.2 完全一致）：
`barrier λ x := (λ - x)^2 / (4*λ)`，`rate λ τ A x := A * Real.exp (-(barrier λ x) / τ)`，
`desc λ τ A := StrictAntiOn (rate λ τ A) (Set.Ioi λ)`（= plan 的 `InvertedDescriptor`）。
（Lean 除零约定 `z/0 = 0` 全程有效。）

### F1（**仅 `desc`** 的精确刻画）

```
desc λ τ A   ↔   0 < A * λ / τ          -- 等价的整数形式：0 < A * λ * τ
```

**机制**：`rate = A·exp(e(x))`，其中 `e(x) = -(x-λ)²/(4·λ·τ)`，故
`e'(x) = -(x-λ)/(2·λ·τ)`。在 `(λ,∞)` 上 `x-λ > 0`，于是 `sign e' = -sign(λ·τ)`：

- `λ·τ > 0` ⇒ `e` 严格递减 ⇒ `rate` 严格递减 ⟺ `A > 0`；
- `λ·τ < 0` ⇒ `e` 严格递增 ⇒ `rate` 严格递减 ⟺ `A < 0`；
- `λ·τ = 0`（含 `λ = 0` 或 `τ = 0`）⇒ `e ≡ 0` ⇒ `rate ≡ A` 常数 ⇒ **非**严格递减。

⇒ **`desc` 单独并不蕴含 `A > 0`，也不蕴含 `λ > 0`。**

### F2（**并入速率正性**后的刻画）

```
(∀ x : ℝ, 0 < rate λ τ A x) ∧ desc λ τ A   ↔   0 < A ∧ 0 < λ * τ
```

因为 `Real.exp > 0` 恒成立，故 `(∀x, 0 < rate λ τ A x) ↔ 0 < A`（`A > 0` 是其充要条件）。

### F3（`plan.md` §7.1 `descriptor_sharp` 的形状 —— **已逐字核对，写法正确**）

plan 把 `0 < kB`、`0 < T` 作为**显式前提**，于是 `0 < τ := kB*T`，F2 退化为：

```
(∀ x, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T   ↔   0 < A ∧ 0 < lam
```

✅ 这与 `plan.md` §7.1（第 341–342 行）的语句**逐字一致** ⇒ **plan 无需修改**。
✅ plan §7.1 的 I7（`A=-1, λ=-1, kB*T=1`）与 §7.1 的"规划期发现"也经复核为**正确**。
**要点**：`⟺` 的左边**必须**含 `∀x, 0 < rate ...` 这个合取项（见下方反例）。

### ⚠️ 典型误写（**本书早期版本出现过，保留作为警示**）

> ❌ **误写 A**：`desc λ τ A ↔ 0 < λ ∧ 0 < τ ∧ 0 < A`
>
> **反例（lead 构造，已复核）**：`λ = −1`、`τ = 1`、`A = −1`。
> `barrier (−1) x = −(x+1)²/4` 在 `(−1,∞)` 上严格**递减** ⇒ `−(barrier)/τ = (x+1)²/4`
> 严格**递增** ⇒ `exp` 递增 ⇒ 乘负的 `A` ⇒ `rate` **严格递减** ⇒ `desc` **成立**，但 `A < 0`。
> ⇒ 必要性中关于 `A` 的一项**不成立**（同理 `λ<0 ∧ τ<0 ∧ A>0` 也让 `desc` 成立）。

> ❌ **误写 B**：`(∀x, 0<rate) ∧ desc ↔ 0 < A ∧ 0 < λ ∧ 0 < τ`
>
> **反例（已复核）**：`λ = −3/2`、`τ = −1`、`A = 1`。
> `rate = exp(−(x−λ)²/(4λτ))` 在 `(λ,∞)` 上**处处为正**且**严格递减**（`λτ = 3/2 > 0`，`A>0`），
> 但 `0 < λ`、`0 < τ` 均**不成立**。
> ⇒ **`τ > 0` 只能作前提，不能作结论。** 这正是 `plan.md` §7.1 把 `0<kB`、`0<T`
> 放在前提位置（而非写进 `⟺` 右边）的原因 —— 该写法是对的。

**可复用的教训（建议写入 `proofs/EXPERIENCE.md`）**：
"锐利刻画"的 `⟺` 右边**必须与左边的合取项一一对应**。
`desc` 的符号信息只包含 `sign(A·λ/τ)`（一个乘积），
因此**单独**由 `desc` 反推三个参数各自的符号是**不可能**的 ——
必须把"速率正性"（`0 < A`）作为左结合取项，才能把 `A` 定下来；
`λ`、`τ` 的符号仍只能作为前提。**先数左边的信息量，再写右边的合取。**

**前置因子的稳健性**：若改用 TST 前置因子
`A(λ,τ) = (4*π*λ*τ)^(-1/2) * κ * ν`，则它只贡献一个**与 `x` 无关的正因子**，
`desc` 的结论与必要性分析**全部不变**（只要 `λ>0, τ>0, κ>0, ν>0`）。
⇒ plan 采用"常前置因子"不会损失任何 x-单调性结论。

---

## 实例参数候选表（供 M5 使用）

> 约定：`x := −ΔG°`（放能取正）。区域判定：`x < λ` 正常区；`x = λ` 无势垒；`x > λ` 反转区。
> **判定只用 (λ, x)**，与 T、A 无关。
> 「来源」列凡标 **（二手）** 者 = 从新闻 / 讲义 / 学位论文读到，**原文表格未取到**（ACS 付费墙）。
> 人类可用 `Closs et al. J. Phys. Chem. 1986, 90, 3673–3683`（DOI `10.1021/j100407a039`）
> 的 Table / Figure 逐项复核 —— 该文是 MCC 系统的**全文版**，含 λ / 溶剂表。

| 体系 | λ / eV | −ΔG° / eV | T / K | 区域判定 | 来源 | 核实状态 |
|---|---|---|---|---|---|---|
| **MCC · A = 2-(5,6-dichlorobenzoquinonyl)**（联苯–5α-androstane–受体，10 Å，脉冲辐解；k ≈ 7×10⁷ s⁻¹） | **1.20**（λ_s=0.75 + λ_v=0.45） | **2.40** | **296** | **反转区**（2.40 > 1.20，ΔG‡ = 0.300 eV） | C&EN 1984-06-04, 62(23):42–44（二手，DOI `10.1021/cen-v062n023.p042`）；与 Nobel Fig. 8 上界一致 | `已核实` |
| **MCC · A = 2-hexahydronaphthoquinonyl**（k ≳ 2×10⁹ s⁻¹，仪器上限） | 1.20 | **1.23**（最优 / 无势垒点） | 296 | **边界**（x ≈ λ，ΔG‡ = 1.9×10⁻⁴ eV） | 同上（二手）；Lokan 2000 学位论文 Ch.1 p.10 正文 | `已核实` |
| **MCC · A = 2-naphthyl**（k ≈ 1.5×10⁶ s⁻¹） | 1.20 | **0.05** | 296 | **深度正常区**（0.05 ≪ 1.20，ΔG‡ = 0.276 eV） | 同上（二手） | `已核实` |
| MCC（同一系列，横轴读数） | 1.20 | **2.00** | 296 | **反转区** | Marcus Nobel Lecture 1992 **Fig. 8** 横轴（刻度 0.0/1.0/2.0 eV） | `已核实` |
| MCC（同一系列，左支单调升段） | 1.20 | **0.60** | 296 | **正常区** | 同上（左支读图） | `已核实` |
| MCC 系列其余 5 个受体（9-phenanthryl, 1-pyrenyl, 2-naphthoquinonyl, 2-benzoquinonyl, 2-(5-chlorobenzoquinonyl)） | 1.20 | 逐项值 **未取到**（仅知增序） | 296 | 未判定 | C&EN 1984（二手，只给序列） | `仅量级` |
| 光合反应中心 BPh⁻→BChl₂⁺ 回传（hole–electron recombination） | **0.25** | **1.10** | 建模取值 | **反转区**（1.10 ≫ 0.25） | Marcus Nobel Lecture 1992 p.88 正文 | `已核实` |
| 光合反应中心 BChl₂*→BPh 第一步 | 0.25 | **0.25**（正文作 ~0.25 eV） | 建模取值 | **边界 / 近最优**（x ≈ λ） | Marcus Nobel Lecture 1992 p.88 正文 | `已核实` |
| Wasielewski 卟啉–醌（光致电荷分离 / 暗复合） | — | 随放能性增大 | — | 反转区（定性：降约 2 个数量级） | Lee 1988 报告（二手）；JACS 107(4):1080–1082 (1985) | `仅量级` |
| Gould/Farid 孪生自由基离子对（氰基蒽受体） | — | 随放能性增大 | — | 反转区（定性：降近 2 个数量级） | Lee 1988 报告（二手）；JACS 109(12):3794–3796 (1987) | `仅量级` |
| McLendon & Miller cyt c / cyt b₅（蛋白质） | — | — | — | 反转区（定性） | JACS 107(26):7811–7816 (1985) | `仅量级` |
| MCC 非极性溶剂对照（**isooctane**，**不是** isopentane） | 未取到 | 峰值显著左移 | — | — | C&EN 1984（二手）：部分反应过快无法测 | `仅量级` |
| Miller–Peeples–Schmitt–Closs MTHF 玻璃（联苯负离子 → 28 受体） | — | 最优驱动力附近 | **77** | 含反转区；β = 1.2 Å⁻¹ | JACS 104(24):6488–6493 (1982) | `仅量级` |

**⚠️ 关于 T（供 M5）**：C&EN（二手）记 1984 系列为 "MTHF at room temperature"，
其复制图注写 **296 K**；**原文真实温度未核实**（且图注写 THF、正文写 MTHF，本身不一致）。
⇒ **建议 M5 把 T 当显式前提 `0 < T`，不要硬编码具体温度** ——
区域判定只依赖 `(λ, x)`，单调性只依赖 `0 < kB*T`，二者都与 T 的具体值无关。

**⚠️ 关于 `ω = 1500 cm⁻¹` 的核实状态（澄清）**：该值**不是**二手转述 ——
它直接印在 **Marcus Nobel Lecture 1992 Fig. 8 的图内标注**（本地渲染件
`Marcus1992_nobel_p84_fig8.png`，与 λ_s / λ_v 处于同一块标注），本次已读图确认
⇒ 状态为 `已核实（读图）`。第二条调研路径未见该值属正常（它只出现在该图内）。

**🔬 经典公式 vs 实测（用上表已核实数字做的算术，供 §1.3 的边界声明背书）**：
取 λ = 1.20 eV、T = 296 K（`k_B T = 25.51 meV`）。**反转支** x: 1.23 → 2.40 eV：
经典公式预言速率降 `exp(−11.761)/exp(−0.0074) = 7.86×10⁻⁶`（**5.1 个数量级**），
实测只降 `7×10⁷ / 2×10⁹ = 3.5×10⁻²`（**1.46 个数量级**）。
⇒ 经典公式在反转区**下降过快约 3.6 个数量级**。
（⚠️ 两点前提：① 该系列内前置因子 `A` 近似相同 —— 这是文献的标准处理；
② 2×10⁹ s⁻¹ 是**仪器上限**，真实顶点速率可能更高，故实测降幅的**下界**更小、结论方向不变。
这也正是 Nobel Fig. 8 的平滑曲线含 `ω = 1500 cm⁻¹` 量子修正的原因。）
**该算术是本人计算，非文献结论**；数字本身标 `已核实`。**含义**：M5 不能把
"描述成立"写成对实测速率的断言（详见记录「反转区实验证据 I」的 影响 栏）。

### 基本常数（供实例层直接写进 Lean）

| 量 | 值 | 来源 | 核实状态 |
|---|---|---|---|
| `k_B` | `1.380 649 × 10⁻²³` J/K（**exact**） | NIST CODATA 2022, `physics.nist.gov/cgi-bin/cuu/Value?k` | `已核实` |
| 元电荷 `e` | `1.602 176 634 × 10⁻¹⁹` C（**exact**） | NIST CODATA, `physics.nist.gov/cgi-bin/cuu/Value?e` | `已核实` |
| `k_B`（eV/K） | `8.617333262145 × 10⁻⁵` eV/K（**exact**，= k_B/e，两者皆为 SI 精确值） | 由前两行相除 | `已核实`（算术自洽） |
| `k_B·T` at T = 298.15 K | **25.693 meV**（0.025693 eV） | 由上一行相乘 | `已核实`（算术自洽） |
| `k_B·T` at T = 77 K | **6.635 meV** | 由上一行相乘 | `已核实`（算术自洽） |

> ✅ 已从"凭记忆"升级为"已核实"：2019 SI 重新定义后 `k_B` 与 `e` 都是**精确值**，
> 因此 `k_B` 的 eV/K 表示与 `k_B·T` 都是**精确算术结果**，不是测量值。

> 实例层建议：**不要把 298.15 K 当作某个实验的真实温度声称**。
> 应显式写成"本实例取 T = 298.15 K 作为建模选择，只需 `0 < k_B*T`"——
> 区域判定与单调性都与 T 的具体值无关。

---

## 更正与冲突清单（相对任务书的预设）

1. **任务书给出的 DOI `10.1021/ja00323a043` 不是 Miller–Calcaterra–Closs 1984。**
   Crossref 核实该 DOI = Mislow & Siegel, "Stereoisomerism and local chirality",
   *JACS* **106**(11), 3319–3328 (1984)。**MCC 1984 的正确 DOI 是
   `10.1021/ja00322a058`，*JACS* 106(10), 3047–3049。**
2. **任务书给出的 Wasielewski 页码 107:5562 未获证实。** Crossref 核实同标题论文为
   *JACS* **107**(4), 1080–1082 (1985), DOI `10.1021/ja00290a066`。
   经第二次独立复核：**107:5562 是另一篇论文**（DOI `10.1021/ja00305a059`），与
   "Dependence of rate constants for photoinduced charge separation and dark charge
   recombination on the free energy of reaction in restricted-distance porphyrin-quinone
   molecules" **不是同一篇**。若确需引用，须单独核实其内容。
   （另：UIUC 1988 讲义把 MCC 1984 的页码印作 "106, 3074" —— 经 Crossref 确认为**笔误**，
   正确为 106(10):3047–3049；该笔误不构成数值冲突。）
3. **✅ 无冲突：经典势垒公式的原始写法就是 `(λ + ΔG°)²/(4λ)`。**
   Marcus 本人印刷体（Nobel Lecture 1992, Eq. (5b), p.78）写作
   `ΔG* = (λ/4)(1 + ΔG°′/λ)²`，二者恒等。
4. **✅ 无冲突：反转区判据。** **原始出处是 Marcus 1960, Discuss. Faraday Soc. 29, p.28 §(v)**
   （标题 "Possibility of 'inverted' chemical behaviour"，原文 "If ΔF° becomes too negative …"）；
   Marcus Nobel Lecture 1992 p.82 的现代措辞为 "vanish at ΔG° = −λ"。
   两者一致 ⇒ 反转区 = `ΔG° < −λ` ⟺ `−ΔG° > λ`，与本 plan 的 `x > λ`（`x := −ΔG°`）一致。
   **⚠️ 但 `ΔG° > λ` 是符号反了的错写**（详见记录 2 与新记录）。
   **⚠️ 反转区的首次提出应引 1960，不是 1956**（1956 全篇无 "inverted" 字样）。
5. **⚠️ 前置因子归属**：`(4πλk_BT)^{-1/2}` **不在** Marcus 1956 中
   （1956 是 `k₁ = Z·exp(−ΔF*/kT)`，Eq. (44)；`Z` = 碰撞数，Eq. (43) 给出其显式形式）。
   引用须改。该项经第二来源独立复核确认。
6. **⚠️ 记号**：Marcus 本人写 `λ = λ_o + λ_i`（solvational + vibrational）；
   plan 的 `λ = λ_in + λ_out` 是同义的现代写法。
7. **⚠️ work terms**：综述级的完整式含 `w_r, w_p`；plan 的形式隐含 `w_r = w_p = 0`，
   须显式声明（记录 7）。
8. **⚠️ 本文件"附"一节早期版本曾给出错误命题**（已更正，错误版本保留为警示）：
   曾写 `desc λ τ A ↔ 0 < λ ∧ 0 < τ ∧ 0 < A`，其**必要性不成立**
   —— 反例 `λ = −1, τ = 1, A = −1` 使 `desc` 成立而 `A < 0`。
   正确刻画是 **`desc ↔ 0 < A·λ/τ`**（仅 `desc`）与
   **`(∀x, 0<rate) ∧ desc ↔ 0 < A ∧ 0 < λ·τ`**（并入速率正性）。
   ✅ **`plan.md` §7.1 的 `descriptor_sharp` 语句本身正确，无需修改**
   （它把 `0<kB`、`0<T` 作前提，且左边含正性合取项）。
9. **✅ 可强化之处（非冲突，是建议）**：`plan.md` §7.2 的 `lamOuter_pos` 把几何因子不等式
   `hgeom : 1/R < 1/(2a₁) + 1/(2a₂)` 当作**假设**；本文件记录 3 证明它可从
   `0 < a₁`、`0 < a₂`、`a₁ + a₂ ≤ R` **推出**（推论 `geometric_factor_pos`）。
   建议 M4b 把 `hR` + `hgeom` 两条前提换成单条 `hRge : a₁ + a₂ ≤ R`，
   使"反转区存在"的溶剂侧条件更基本（`a₁+a₂ ≤ R` 即"两球不重叠"，有直接几何意义）。

---

## 不可表达清单的排序（供 `plan.md` §14「下一站」直接采用）

> 排序依据：**对 M1–M5 现有语句的实际影响**（越大越靠前）× 所需数学基础的可复用度。
> 全部为"当前 mathlib 下不可表达或代价过高"的项；**M1–M5 均不依赖任何一项**。

| 序 | 不可表达项 | 对 M1–M5 的影响 | 若将来要做，需要什么数学基础 |
|---|---|---|---|
| **1** | **Franck–Condon 因子 / 振动重叠积分（`χ_i` 与 `χ_f` 的内积）** | **零**（M1–M5 只用经典抛物线势垒）。但它是"经典反转区为何被实验削弱"的**直接前置**，同时是序 3 的公共前置 | 一维谐振子在 `L²(ℝ)` 中的本征函数系 + Hermite 多项式的正交完备性 + 重叠积分的 Laguerre 闭式。mathlib 已有 `Lp`、Hilbert 空间与部分特殊函数，但**没有**谐振子本征基的完备性定理 ⇒ **需自建，且是全部项里最可行的** |
| **2** | **溶剂连续介质静电学的第一性推导（Pekar 公式的来源）** | **中**：`lamOuter` 目前是**定义**（plan §7.2）。若将来改成"推导"，M4b 的语句会从"前提"升级为"定理" | 非平衡极化的变分原理 + 泊松方程在球形空腔上的边值问题。mathlib **没有 PDE / 边值问题库**，且建设成本远超收益 ⇒ **建议永久保持为定义** |
| **3** | **Fermi 黄金规则 + 振动热浴无穷求和（Bixon–Jortner / Jortner 能隙律）** | **零**（§1.3 已明确不做）；是 §14 第一条的主体 | 级数收敛性 + 振动配分函数（生成函数）+ 热平均。mathlib 有级数收敛基础设施，但**没有**统计力学 / 配分函数层 ⇒ 需在序 1 完成后自建 |
| **4** | **电子耦合的指数衰减 `V(R) = V₀·exp(−β(R−R₀))` 与超交换机制** | **零**（§1.3 已明确不做）；属 §14 第三条 | 紧束缚模型 / 微扰论中的有效耦合推导。mathlib 无量子力学算子谱理论的应用层 ⇒ 自建成本高 |
| **5** | **Marcus 交叉关系 `k₁₂ = √(k₁₁k₂₂K₁₂)`** | **零**（§1.3 已明确不做） | 形式上只是 `Real.sqrt` 层的代数恒等式 —— **可表达**；真正的障碍是它依赖"交叉反应与自交换反应 `λ` 相同"这一**物理假设** ⇒ 若要做，应把它写成**前提**而非可证定理。**这是全部项里最便宜的一条，但必须说清它是假设** |
| **6** | **前置因子 `κ`（Landau–Zener 透射系数）、`ρ`（绝热因子）** | **极低**：plan 把 `A` 当正常数（§13 第 9 条已论证该近似的稳健性） | Landau–Zener 公式需要含时两能级体系的渐近分析（Stokes 现象 / 复时间鞍点）⇒ mathlib 无 |
| **7** | **物理单位与量纲检查（eV / K / J）** | **零，但需纪律**：Lean 里 `kB`、`T`、`lam`、`x`、`A` 都是裸 `ℝ`，**量纲错误不会被内核拦住** | mathlib **没有**物理单位系统（`Unitful` 一类）⇒ 只能靠文档与实例注释约束。**建议 M5 的每个实例都写明单位**，并在 `Instances.lean` 顶部写一行单位约定注释 |

**对 `plan.md` §14 的建议排序**：
1. **先做序 1（Franck–Condon 因子）** —— 它是序 1 与序 3 的公共前置，且 mathlib 的
   `Lp` / Fourier / 特殊函数基础可复用，是"下一站"里唯一低成本高收益的一项。
2. **序 2（溶剂静电学第一性推导）建议永久排除** —— 代价/收益比最差；
   `lamOuter` 保持为定义是正确的工程选择。
3. **序 5（交叉关系）是最便宜的一项**，但若要做，必须在语句层面明确
   "同 `λ` 假设"是**前提**而非定理，否则会做出一个物理上过强的主张。
