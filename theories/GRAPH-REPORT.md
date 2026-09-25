# theories/GRAPH-REPORT.md — the PhotoLean relation graph: consolidated report (17 theories, 1 kernel, 3 adjudication classes)

> **Status / 状态.** This is the **consolidated** (non-incremental) report of the relation graph of the
> **seventeen** delivered theories. Its companion `theories/RELATIONS.md` is the *discussion draft in
> incremental mode*: it grew one batch at a time (§1–§7 the seven-theory graph, §8 the photophysics
> batch of nine, §9 the seventeenth node RACI), so a reader has to reassemble the whole graph from
> three layers. This file is that reassembly: one node inventory, one edge inventory, one
> adjudication section, one no-edge registry, one verification record — all measured at the tree
> state named below.
> **中文**：本文件是**十七**个已交付理论关系图的**总结性（非增量）**报告。其姊妹文件
> `theories/RELATIONS.md` 是**增量模式**的讨论稿：它按批次生长（§1–§7 为七理论图、§8 为九个理论的
> 光物理批次、§9 为第十七个节点 RACI），读者需要从三层里重新拼出整张图。本文件就是这个拼装结果：
> 一份节点清单、一份边清单、一节裁定、一份无边登记、一份复核记录——全部在下列树状态上实测。

> **Measurement state / 实测状态.** HEAD `5af10d1` plus this round's documentation-only edits
> (working tree otherwise clean; `.lake/tmp/` is gitignored). Gate re-run this round:
> `proofs/scripts/check.sh --strict` → **verdict: PASS** (`build: OK`, scan `clean`, 17/17 leaf data
> planes `OK`); all **17 fidelity probes** → `0 signature differences`, `not delivered yet: 0`.
> Numbers in the tables below are those outputs, not recollections.
> **中文**：HEAD `5af10d1` 加上本轮仅文档改动（工作树其余干净；`.lake/tmp/` 已 gitignore）。本轮重跑门：
> `proofs/scripts/check.sh --strict` → **verdict: PASS**（`build: OK`、扫描 `clean`、17/17 叶子数据面 `OK`）；
> **17 个保真探针**全部 `0 signature differences`、`not delivered yet: 0`。下表数字取自这些输出，不是回忆。

---

## 0. One-paragraph summary / 一段话总结

**English.** The repository delivers **17 theories** in **92 theory modules** (95 `.lean` files
including `Kernel.lean`, `Relations.lean`, `Smoke.lean`); their statement authorities contain
**1153 declarations**, every one of them delivered word-for-word (17/17 probes: 0 differences), and
each theory's board records an independent verifier PASS. They are wired into **one graph** by
`PhotoLean/Relations.lean`: **78 declarations** in 17 sections, whose content is (i) **15 `rfl`
kernel certificates** that pin each theory's copy of the shared object to `PhotoLean.Kernel`, (ii)
**7 true equivalences**, **3 one-way entailments**, **definitional-reuse and ledger re-exports**,
(iii) **composition edges** that make newer theories *consume* older ones as components (the Kasha →
Marcus conditional edge, Sabatier → BEP, the photophysics batch through the QuantumYield spine, and
RACI through five rows), (iv) **three adjudication classes** — **A1** adjudicated conflation
(symmetry factor β = 1/2: exactly the equal-curvature diagonal), **A2** adjudicated independence
(Kasha vs Kasha–Vavilov: pointwise independent, coincident only under the closed quantification
with a loss channel), **A3** identifiability (static vs dynamic Stern–Volmer: intensity-only data
non-injective, lifetime channel is the exact discriminator) — and (v) a **no-edge registry** so that
*every* pair of nodes either carries a registered edge or a registered reason for its absence. Every
first form the kernel refuted — StokesShift's SS-C9 direction, FluorPhos's FP-C5 corner, the four
literature families of BEP's instance layer, and the A1 conflation witness — is delivered as a
counterexample-witness theorem, never deleted (10 rows, §7).
**中文**：仓库交付 **17 个理论**、**92 个理论模块**（含 `Kernel.lean`、`Relations.lean`、`Smoke.lean`
共 95 个 `.lean`）；语句权威共 **1153 条声明**，全部逐字交付（17/17 探针 0 差异），每个理论的任务板
都有独立 verifier PASS 记录。它们由 `PhotoLean/Relations.lean` 接成**一张图**：17 个小节、**78 条
声明**，内容为：（i）**15 条 `rfl` 内核证书**，把各理论自带的共享对象副本钉到 `PhotoLean.Kernel`；
（ii）**7 条真等价**、**3 条单向蕴含**、若干定义复用与清单 re-export；（iii）**组合边**——较新理论把
较老理论当组件消费（Kasha → Marcus 条件边、Sabatier → BEP、光物理批次经 QuantumYield 代数脊柱、
RACI 经五行）；（iv）**三个裁定类**——**A1** 已裁决混同（对称因子 β = 1/2：恰在等曲率对角线成立）、
**A2** 已裁决独立性（Kasha 对 Kasha–Vavilov：逐点独立，只在"带损失通道的闭合量化"下重合）、
**A3** 可辨识性（静态对动态 Stern–Volmer：仅强度观测非单射，寿命通道是精确判别器）；（v）**无边
登记**，使**任意**两节点之间要么有已登记边、要么有已登记的缺席理由。内核证伪过的每个初式——StokesShift
的 SS-C9 方向、FluorPhos 的 FP-C5 角落、BEP 实例层的四个文献族、以及 A1 的证伪见证——都以反例见证
定理交付，绝不删除（共 10 行，见 §7）。

---

## 1. The nodes / 节点清单

### 1.1 Family structure / 家族结构

**English.** The seventeen theories are not seventeen parallel objects; they fall into five families,
and the family is what determines *how* a node can touch the graph:

| family | members | what they share | how they can connect |
|---|---|---|---|
| F1 — readings of the quadratic object | Marcus, Hammond, BEP | one equal-curvature two-parabola model (`Kernel`) | definitional certificates + equivalences + entailments (the dense core) |
| F1′ — generalization of the object | SymmetryFactor | unequal curvature `(kr, kp)` at thermoneutrality | specialization certificates to `Kernel`/`BEP` + the A1 verdict |
| F1″ — kernel-carrying batch nodes | EnergyGapLaw, StokesShift, ICvsISC | their own copies of the kernel barrier/surfaces | `rfl` certificates (§12) + composition rows |
| F2 — rate-cascade / algebraic layer | Kasha, KashaVavilov, SternVolmer, QuantumYield, FluorPhos | no potential-energy surface; rates, branches, yields | composition into the ladder (conditional premise) or into the QY spine |
| F3 — geometry / spectroscopy | Goldschmidt, Forster, Einstein | scalars other than a reaction-coordinate energy (radii, transfer geometry, radiative conversions) | mostly **no-edge** registrations; shape look-alikes stated as such |
| F4 — nonadiabatic kinetics | RACI | a two-state Hamiltonian family with a codimension-2 degeneracy | five rows (QY certificate, EGL log-link, ICvsISC note, Marcus look-alike) + no-edge registry |

**中文**：十七个理论不是十七个平行对象，而是五个家族；家族决定了节点**能怎样**接触关系图：F1 是同一
二次对象的三种读法（共享内核，密度最高的核心）；F1′ 是对象的非等曲率推广（SymmetryFactor，经特化证书
与 A1 判决接入）；F1″ 是携带内核副本的光物理批次节点（经 §12 `rfl` 证书 + 组合行接入）；F2 是速率级联/
代数层（不出现势能面：阶梯分支与产额，经组合或 QY 脊柱接入）；F3 是几何/谱学（标量不是反应坐标能量：
离子半径、转移几何、辐射跃迁，主要经**无边登记**与"形状相似"注记接入）；F4 是非绝热动力学（RACI，
两态哈密顿家族与余维 2 简并，五行加无边登记）。

### 1.2 The seventeen rows / 十七行

| # | node | modules | statement authority | delivered (public) | entry mode into the graph |
|---|---|---|---|---|---|
| 1 | Marcus (inverted region) | `PhotoLean/Marcus/` (8) | 51 | 82 | F1 core; E1–E7, O1–O2, N1–N2, look-alike C1–C5, RACI look-alike row |
| 2 | Hammond (postulate) | `PhotoLean/Hammond/` (6) | 102 | 102 | F1 core; E1, E2, E4, E5, E6, E7, O1, O3, N1–N2 |
| 3 | Bell–Evans–Polanyi | `PhotoLean/BEP/` (6) | 191 | 191 | F1 core; E2, E3, O1–O3, N1; its instance layer refuted four literature families as equal-curvature two-parabola |
| 4 | Kasha's rule | `PhotoLean/Kasha/` (6) | 151 | 151 | F2; **conditional composition** K1–K3 + certificate K4 (`kernel_marcusIC`) |
| 5 | Sabatier / volcano | `PhotoLean/Sabatier/` (6) | 132 | 134 (107 thm + 27 def; +36 private) | composition S1–S4 over BEP; look-alike cluster C1–C5 with Marcus |
| 6 | Goldschmidt | `PhotoLean/Goldschmidt/` (6) | 139 | 139 (98 thm + 40 def + 1 inductive; +8 private) | **no-edge** to all six of the then-graph; N4 shape registration with Sabatier |
| 7 | Symmetry factor | `PhotoLean/SymmetryFactor/` (5) | 35 | 35 (28 thm + 7 def) | **A1** adjudicated conflation + specialization certificates to `Kernel.tsCoord`, `BEP.transfer` |
| 8 | Kasha–Vavilov | `PhotoLean/KashaVavilov/` (3) | 29 | 39 (29 authority + 10 auxiliary) | **A2** adjudicated independence (§13) |
| 9 | Stern–Volmer | `PhotoLean/SternVolmer/` (4) | 46 | 46 | **A3** identifiability (§14) + QY dilution composition |
| 10 | QuantumYield | `PhotoLean/QuantumYield/` (4) | 29 | 29 | **the batch's algebraic spine** (§15): every group-A/B/C contact runs through it |
| 11 | FluorPhos | `PhotoLean/FluorPhos/` (4) | 30 | 30 (incl. negative row `fpC5_firstForm_refuted`) | cascade compositions into QY; quench invariance into SV |
| 12 | EnergyGapLaw | `PhotoLean/EnergyGapLaw/` (5) | 26 | 27 (26 authority + 1 auxiliary) | kernel copies (§12) + EGL/Kasha ordering row + Hammond boundary row |
| 13 | StokesShift | `PhotoLean/StokesShift/` (4) | 36 | 36 (incl. `invertedCorner_firstForm_refuted`) | kernel copies (§12) + emission-window boundary row |
| 14 | ICvsISC | `PhotoLean/ICvsISC/` (4) | 20 | 20 | kernel copies (§12) + IC/ISC rate identification row; RACI's §17 note |
| 15 | Förster (FRET) | `PhotoLean/Forster/` (4) | 32 | 32 | QY composition (`1 − Φ_D`) + SV look-alike (`fretEff6_inv_eq_one_plus`) |
| 16 | Einstein A/B | `PhotoLean/Einstein/` (4) | 33 | 33 | QY radiative-rate anchor (`einstein_yield_via_qy`) |
| 17 | RACI | `PhotoLean/RACI/` (13) | 71 | 88 (59 thm + 29 def) | five rows in §17 + the §17 no-edge registry |

Totals / 合计: modules **92** (95 `.lean` with `Kernel.lean` + `Relations.lean` + `Smoke.lean`);
statement authority **1153** declarations, all delivered word-for-word; public delivered
declarations **1214** (private helpers and `instance` declarations excluded — the counts are the
fidelity probe's `word-for-word + not-in-authority` totals, so the authority-external auxiliaries
are included: e.g. KashaVavilov 10, EnergyGapLaw 1, Sabatier 2, RACI 17, Marcus 31; the private
helpers e.g. Sabatier 36, Goldschmidt 8, and the single delivered `instance` — QuantumYield's
`instDecidableQYData` — are not counted, which is why QuantumYield reads 29 rather than 30).
**中文（合计）**：模块 **92**（加 `Kernel.lean` + `Relations.lean` + `Smoke.lean` 共 95 个 `.lean`）；
语句权威 **1153** 条声明，全部逐字交付；公开交付声明 **1214** 条（不含 private 辅助引理与 `instance`
声明——计数口径即保真探针的 `word-for-word + not-in-authority`，故权威外辅助行计入：KashaVavilov 10、
EnergyGapLaw 1、Sabatier 2、RACI 17、Marcus 31；private 辅助（Sabatier 36、Goldschmidt 8）与唯一交付的
`instance`（QuantumYield 的 `instDecidableQYData`）不计，故 QuantumYield 记 **29** 而非 30）。

**Entry-mode legend / 接入方式图例**: *certificates* are definitional `rfl`/unfold pins (regression
alarms, no new mathematics); *equivalences* are two-way theorems; *entailments* are one-way;
*compositions* consume an older theory as a component (premise attached); *adjudications* (A1/A2/A3)
decide a literature conflation question with an exact boundary; *no-edge* is a registered absence
with its dependency fact and modelling reason.
**中文**：*证书* = 定义层 `rfl`/展开钉（回归报警器，无新数学）；*等价* = 双向定理；*蕴含* = 单向；
*组合* = 把较老理论当组件消费（前提随边登记）；*裁定*（A1/A2/A3）= 用精确边界判决文献中的混同问题；
*无边* = 带依赖事实与建模理由的已登记缺席。

---

## 2. The shared kernel / 共享内核

**English.** `PhotoLean/Kernel.lean` imports `Mathlib` only, sits at the bottom of the dependency
graph, and holds **6 definitions + 2 theorems**: `reactantSurface`, `productSurface`, `barrier`,
`reverseBarrier`, `tsCoord`, `transfer` (and the two barrier–rate algebra theorems). Every
kernel-reading theory keeps its **own copy** of the needed objects, and a `rfl` certificate binds
copy and kernel body-level: if a delivered definition drifts, its nearest certificate stops being
`rfl` and the build fails at that pin — the **regression alarm**. Measured (2026-09-24): perturbing
`Kernel.barrier` fails inside `PhotoLean/Kernel.lean` itself (the algebra theorem
`reverseBarrier_eq_barrier_neg`), and perturbing `Kernel.reactantSurface` fails in the theory module
that keeps the copy (`PhotoLean/StokesShift/Basic.lean`, `cert_s0Surface`) — in both cases *before*
`PhotoLean/Relations.lean` is reached, so the alarm is layered (kernel theorem → theory certificate →
relation-module certificate) rather than a property of the relation module alone.
**中文**：`PhotoLean/Kernel.lean` 只 `import Mathlib`，处在依赖图底部，含 **6 定义 + 2 定理**：
`reactantSurface`、`productSurface`、`barrier`、`reverseBarrier`、`tsCoord`、`transfer`（以及两条
势垒–速率代数定理）。每个"内核读法"理论都保留所需对象的**自带副本**，而 `rfl` 证书在定义体层面把副本与
内核绑定：一旦某个已交付定义漂移，**最近的**证书就不再是 `rfl`，构建在该钉住点失败——这就是**回归报警器**。
实测（2026-09-24）：扰动 `Kernel.barrier` 在 `PhotoLean/Kernel.lean` 内部失败（代数定理
`reverseBarrier_eq_barrier_neg`）；扰动 `Kernel.reactantSurface` 在保留副本的**理论模块**里失败
（`PhotoLean/StokesShift/Basic.lean` 的 `cert_s0Surface`）——两次都在到达 `PhotoLean/Relations.lean`
**之前**，故报警是多层的（内核定理 → 理论证书 → 关系模块证书），而非关系模块一处的性质。

**Delivered `rfl` certificates / 已交付 `rfl` 证书 (15)**:
§1 — `kernel_barrier_eq_marcus`, `kernel_barrier_eq_hammond`, `kernel_barrier_eq_bep`,
`kernel_reverseBarrier_eq_hammond`, `kernel_tsCoord_eq_hammond`, `kernel_transfer_eq_bep`,
`kernel_reactantSurface_eq_hammond`, `kernel_productSurface_eq_hammond` (8);
§12 — `eg_barrier_eq_kernel`, `eg_rate_eq_marcus`, `eg_invertedGap_iff_marcus`,
`ss_s0Surface_eq_kernel`, `ss_s1Surface_eq_kernel`, `icvscic_barrier_eq_kernel`,
`icvscic_icRate_eq_marcus` (7).
Two RACI/IC certificate-style rows (`kernel_surfaces_cross_at_tsCoord` is *not* one: it carries the
load-bearing `lam ≠ 0` and is proved by `field_simp; ring`, not by `rfl`).

---

## 3. The edge inventory / 边清单

**English.** `PhotoLean/Relations.lean` is the machine-checked edge inventory: 78 declarations in
17 sections. The table states each section's declared role and its accounting (the module's own
rule: re-exports and certificates add **no** mathematics *to this module*; genuinely new rows are
only those proved here beyond composition).

| § | rows | role | accounting |
|---|---|---|---|
| §1 | 8 | kernel certificates (all `rfl`) | naming certificates; regression alarms |
| §2 | 6 | true equivalences E1–E6, reused verbatim | re-exports, no new mathematics |
| §3 | 3 | one-way entailments O1–O3 | O1–O2 re-exports; **O3 proved here** |
| §4 | 4 | definitional reuse over `Marcus.Reorg` | re-exports, one definition two theories |
| §5 | 4 | remaining ledger rows of the bridge inventory | re-exports (alias + ℚ-side classifier) |
| §6 | 3 | non-relations and shape differences (E7, N1, N2) | **all proved here** |
| §7 | 5 | Kasha → Marcus conditional composition K1–K4 | 4 re-exports + **1 certificate proved here** |
| §8 | 6 | Sabatier → BEP composition S1–S4 | re-exports (S2, S4 carry two each) |
| §9 | 7 | Sabatier ↔ Marcus look-alike cluster C1–C5 | 1 certificate (C1) + 6 rows proved here, of which **4 genuinely new** (C2 uniqueness, C3a, C4, C5a; C3b and C5b are assemblies) |
| §10 | 0 | no-edge registry (first seven) | documentation, not theorems |
| §11 | 4 | **A1** adjudicated conflation (SymmetryFactor) | 2 tie-back certificates + 2 verdict re-exports; the mathematics lives in `PhotoLean/SymmetryFactor/*` |
| §12 | 7 | batch kernel certificates (EGL, StokesShift, ICvsISC) | `rfl` pins, no new mathematics |
| §13 | 2 | **A2** adjudication re-exports (Kasha vs Kasha–Vavilov) | re-exports |
| §14 | 2 | **A3** adjudication re-exports (Stern–Volmer) | re-exports |
| §15 | 12 | batch composition edges over the QuantumYield spine | proved here (incl. kernel/kernel-copy certificates and shape rows with machine content) |
| §16 | 0 | extended no-edge registry (sixteen nodes) | documentation, not theorems |
| §17 | 5 | the seventeenth node RACI | proved here (1 composition certificate + 4 rows) |

**中文**：`PhotoLean/Relations.lean` 是机器检查的边清单：17 节、78 条声明。上表给出每节声明的角色与记账
（模块自己的规则：re-export 与证书**不给本模块**增加数学；真正的新内容只有在本模块内证明、且不是组装
的行）。§6 三条全是本模块新证（E7 为两条已交付锐利刻画的复合、N1 与 N2 是非关系定理）；§9 的七行中
真正的新数学是四行（C2 唯一性半边、C3a、C4、C5a）；§11 的四行全是证书/re-export，A1 的数学在
`PhotoLean/SymmetryFactor/*`；§12 的七行是 `rfl` 钉；§15 的十二行与 §17 的五行为本模块所证。

---

## 4. The three adjudication classes / 三个裁定类

**English.** Beyond "edge" and "no edge", the graph now speaks a third vocabulary: an
**adjudication** decides a question the literature leaves conflated, and delivers three things — an
iff boundary, witness instances on both sides, and an explanation of why the confusion persists in
practice. The scientific payoff is that the disputed identification stops being "wrong" or "a law"
and becomes **a special case with a machine-checked boundary**.

### A1 — adjudicated conflation: the symmetry factor β = 1/2

* **Verdict / 判决**: `SymmetryFactor.betaHalf_iff_equalForceConstants` —
  `BetaHalfReading kr kp ↔ kr = kp` for `0 < kr, 0 < kp`; the conflated reading (β, i.e. the
  thermoneutral crossing coordinate, equals `1/2`) holds **exactly** on the equal-curvature
  diagonal. Crossing coordinate closed form: `√kp/(√kr+√kp)`, unique in `[0,1]`, no calculus.
* **Witnesses / 见证**: `(1,4) ↦ 2/3 ≠ 1/2` (`betaHalf_falsified_by_unequal`); the direction
  asymmetry `(4,1) ↦ 1/3` (`tsCoordZero_gt_half_iff_stiffProduct`: a stiffer product well already
  puts the crossing past the middle at zero driving force).
* **Why it persists / 混同为何长存**: the equal-curvature diagonal is exactly the symmetric picture
  every textbook draws (and Marcus's own declared symmetrization): two tie-back certificates
  (`symmetryFactor_tsCoordZero_eq_kernel`, `symmetryFactor_tsCoordZero_eq_bepTransfer`) plus
  `betaHalf_holds_in_kernel` show the conflation is a **theorem** throughout that family; the
  one-row package `symmetryFactor_conflation_falsified_and_holds_in_kernel` states both halves.
* Literature: a first-hand practice locus (Butler–Volmer "usually both taken to be equal to 0.5")
  paired with the IUPAC Technical Report's printed warning (LITERATURE S1/S2 of the theory).

### A2 — adjudicated independence: Kasha's rule vs Kasha–Vavilov

* **Verdict / 判决**: `kv_d2_verdict` is a four-part conjunction —
  (i) a witness where Kasha's rule holds and Vavilov-at-1 fails, (ii) a witness where Vavilov-at-1
  holds and Kasha's rule fails (both at positive excitation, `ic 0 = 1 > 0`, inside the lossy
  regime), (iii) the **closed-form coincidence boundary** under the closed quantification with a
  loss channel: `KashaRule rad ic N ↔ VavilovUpTo rad ic N` for every `RateData rad ic N` with
  `0 < ic 0`, and (iv) the lossless corner, where the two closed forms separate (making the loss
  premise load-bearing).
* Companion boundary row: `kv_antiKasha_boundary` — under `RateData`, a Kasha violation is always
  an *observable* anti-Kasha emission (`0 < upperYield ↔ ¬ KashaRule`: the maximal-emitter argument).
* **Why it persists / 独立性为何被掩盖**: every ordinary lossy fluorophore sits in the regime where
  the closed forms coincide, so the two rules are never seen to differ outside the degenerate
  lossless model and single-step readings.

### A3 — identifiability: static vs dynamic Stern–Volmer quenching

* **Verdict / 判决**: `sv_d1_verdict` (weakest premises `k0 ≠ 0`, `0 < Ka`) — both plots are
  linear; the intensity-only observation map is **non-injective** on the two-mechanism space
  (matched parameters give pointwise-identical curves at every concentration); and the lifetime
  channel is the **exact discriminator**: `LifetimeTracks m k0 kq Ka ↔ m = Mech.dyn`.
* Companion boundary row: `sv_identifiability_boundary` for `0 < Ka` alone (`lifetimeTracks_iff_dyn`),
  i.e. only the static-side scale `Ka` is load-bearing there.
* **Positive witness of coexistence / 共存的正面见证**: `mixed_witness` — the second difference
  `svRatioBoth 2 1 1 1 − 2·svRatioBoth 2 1 1 0 + svRatioBoth 2 1 1 (−1) = 1`; upward curvature is
  the signature that *both* mechanisms are present.
* **Why it persists / 为何长存**: routine practice measures intensity only; lifetime resolution is a
  separate experiment, so the two mechanisms are routinely conflated.

**中文**：除"有边/无边"之外，关系图现在有第三种词汇：**裁定**——判决文献留下混同的问题，并交付三样东西：
iff 边界、两侧见证实例、以及"混同为何在实践层面长存"的解释。其科学收益是：有争议的等同不再被判为
"错"或"是定律"，而成为**带机器检查边界的特例**。**A1**：`betaHalf_iff_equalForceConstants : BetaHalfReading kr kp ↔ kr = kp`（`0 < kr, 0 < kp`）——被混同的 β=1/2 读法**恰好**在等曲率
对角线上成立；闭式 `√kp/(√kr+√kp)` 在 `[0,1]` 内唯一、无需微积分；见证 `(1,4) ↦ 2/3`（被证伪）与方向
不对称 `(4,1) ↦ 1/3`；长存原因正是教科书画的对称图恰是它成立的区域，两条回接证书加
`betaHalf_holds_in_kernel` 说明在该族里它是**定理**。**A2**：`kv_d2_verdict` 是四段合取（双向逐点独立
见证、带损失通道闭合量化下的重合 iff 边界、无损角分离），配 `kv_antiKasha_boundary`（Kasha 违反 ⟺ 可
观测的反 Kasha 发射）；普通有损荧光体都落在闭合式重合区，因此实践上看不到差别。**A3**：`sv_d1_verdict`
（最弱前提 `k0 ≠ 0`、`0 < Ka`）——两条曲线都线性、仅强度观测**非单射**、寿命通道是**精确**判别器
（`LifetimeTracks m ↔ m = Mech.dyn`），配 `sv_identifiability_boundary`（只需 `0 < Ka`）与共存正面见证
`mixed_witness`（二阶差分 = 1，向上弯曲）；长存原因是常规实验只测强度。

---

## 5. The composition spine / 组合脊柱

**English.** Group A/B/C contacts of the photophysics batch are not pairwise ad hoc bridges: they all
factor through **one algebraic layer**, `PhotoLean/QuantumYield` (the parallel-channel calculus,
`yieldOf ![k₁, k₂] 0`), and through the kernel. The chains, read left-to-right (each arrow is a
delivered row):

```
Kernel.barrier ── cert ──> Kasha.marcusIC ── K1 ──> Kasha's rule window
Kernel.barrier ── cert ──> EnergyGapLaw.nrBarrier ──> Marcus.rate ──> ICvsISC.icRate
QuantumYield.yieldOf ── kasha_radBranch_eq_yieldOf ──> Kasha.radBranch            (ladder branch)
QuantumYield.yieldOf ── phiF_eq_yieldOf ──> fluor. yield = kF/(kF+kISC+kIC)       (FluorPhos)
QuantumYield.yieldOf ── phiP_eq_yieldOf_cascade ──> phosphor. yield               (cascade)
QuantumYield.yieldOf ── sv_quench_dilutes_yield ──> Stern–Volmer dilution          (SV → QY)
QuantumYield.yieldOf ── einstein_yield_via_qy ──> Einstein A anchor                (radiative)
QuantumYield.yieldOf ── fretEff6_eq_one_sub_yieldOf ──> FRET transfer efficiency
QuantumYield.yieldOf ── raci_qy_eq_yieldOf_two_channel ──> RACI.quantumYield      (AIE)
RACI.barrierRate ── log_barrierRate_eq ──> affine energy-gap law                 (RACI → EGL)
ICvsISC.fcBarrier ── icvsisc_barrier_zero_at_crossing ──> the CI maximal-rate point (RACI)
```

The composition edge of the *older* batch is the same idea with a modelling premise attached:
**Kasha → Marcus** is conditional on `hic` ("the S₂ → S₁ internal-conversion rate *is* the Marcus
rate"); the edge is registered with the premise, and no row claims that the identification holds on
its own. **Sabatier → BEP** carries the geometric reading of the BEP defect law: each tangent lies
below its parabola, so the linear volcano underestimates the barrier pointwise
(`bepLine_le_eact`, `linearVolcano_le_parabolic`).

**中文**：光物理批次的 A/B/C 组接触不是逐对临时搭桥，而是全部经由**一个代数层** `PhotoLean/QuantumYield`
（并行通道演算 `yieldOf ![k₁, k₂] 0`）与内核因子化。上列链条每条箭头都是一个已交付行。较老批次的组合边
是同一思想加上随边登记的前提：**Kasha → Marcus** 以 `hic`（"S₂ → S₁ 内转换速率**就是** Marcus 速率"）
为条件，边连同前提登记，没有任何一行声称该同一性单独成立；**Sabatier → BEP** 承载 BEP 缺陷律的几何读法
（切线在抛物线之下 ⇒ 线性火山逐点低估势垒）。

---

## 6. The no-edge registry, consolidated / 无边登记（总结版）

**English.** An absent edge is a registered fact with two components: the **dependency fact**
(measured import structure) and the **modelling reason** (which vocabulary or scalar is missing).
The registry is complete in the sense that **every** node sits on the graph: each pair either has an
edge above or a row here. The consolidated classes:

1. **Pure-vocabulary separations.** Kasha ↔ BEP; Kasha ↔ Hammond; Sabatier ↔ Hammond;
   Sabatier ↔ Kasha (first batch); the batch nodes against the two-parabola family
   (KashaVavilov, SternVolmer, QuantumYield, FluorPhos, EnergyGapLaw, StokesShift, ICvsISC,
   Forster, Einstein each with their listed partners); RACI ↔ Hammond/BEP/Sabatier/Goldschmidt/
   SymmetryFactor/FluorPhos/StokesShift/Forster/Einstein (seventeenth node). Reason pattern: no
   shared scalar — a cascade of yields, a concentration-axis rate model, band positions, transfer
   geometry or a two-state Hamiltonian shares nothing with a barrier profile, a descriptor axis or
   ionic radii. (Coverage note, 2026-09-24: `Relations.lean` §16 carries a *completion* block that
   registers the 26 pairs the earlier bullets left out — all of them absences or undelivered
   candidates whose drafts live in the per-theory `plan.md` §10 — plus the one edge delivered
   in-module rather than re-exported, StokesShift's SS-C9 `emEnergy_pos_iff_inverted` to
   `Marcus.InvertedRegion`. §16 therefore now accounts for every one of the 136 node pairs.)
2. **Contact only through the spine.** SternVolmer, QuantumYield, FluorPhos, Einstein: their
   contacts to the energy-side theories are exactly the §15 composition rows through `QuantumYield`.
3. **Shape look-alikes registered without edge.** N4 (Goldschmidt symmetric band ≡ absolute-deviation
   bound ≡ Sabatier `NearOptimal`; three-way classifiers on both sides, different propositions);
   SV/FO shared `1 + control` form (`fretEff6_inv_eq_one_plus`); RACI ↔ Marcus (a classical
   single-condition surface crossing vs a codimension-2 conical intersection — the row
   `kernel_surfaces_cross_at_tsCoord` pins the classical side); Einstein ↔ StokesShift mirror rule
   (detailed balance is about intensities, the mirror rule about positions); Forster ↔ Goldschmidt
   (two geometric threshold criteria, no shared scalar); ICvsISC ↔ FluorPhos (`kISC` sharing is a
   premise-level note, not a Lean row).
4. **The registry's own lesson, three times over**: "the same statement *shape* is not the same
   statement" (N1/N2 → N3 → N4), and "a shared predicate is not a shared mechanism" (N3's C1/C2 vs
   C3–C5).

**Dependency facts (measured) / 依赖事实（实测）**: every photophysics module imports only `Mathlib`,
its own theory's earlier modules, and (for the two-parabola carriers) `PhotoLean.Kernel` /
`PhotoLean.Marcus.Basic`; `PhotoLean/Relations.lean` is the **only** module importing across the
batch; RACI imports only `Mathlib` + own modules; Goldschmidt imports `Mathlib` + own modules.
**中文**：不存在的边是**带两部分内容的已登记事实**：**依赖事实**（实测 import 结构）与**建模理由**
（缺哪个词汇/标量）。登记在"**每个**节点都在图上"的意义下完整：每一对要么有上文的边、要么在这里有
一行。总结为四类：①纯词汇分离（Kasha↔BEP、Kasha↔Hammond、Sabatier↔Hammond、Sabatier↔Kasha，
以及批次各节点与双抛物面家族、RACI 与九个节点——理由模式是"不共享标量"）；②只经脊柱接触（SV/QY/FP/
Einstein 与能量侧理论的联系**恰是** §15 的组合行）；③只登记形状相似、不建边（N4、SV/FO 的 `1 + control`
同形、RACI↔Marcus 的实交 vs 余维 2 简并、Einstein↔StokesShift 镜像律、Forster↔Goldschmidt 双几何阈值、
ICvsISC↔FluorPhos 的 `kISC` 前提层注记）；④登记处自身三次重复的教训："**同样的语句形状不等于同样的
语句**"（N1/N2 → N3 → N4）、"**共享谓词不等于共享机制**"（N3 的 C1/C2 对 C3–C5）。

---

## 7. What the graph refused / 关系图拒绝过什么

**English.** Negative results are first-class in this repository: when the kernel refuted a drafted
statement, the statement was **re-frozen with a counterexample-witness theorem** rather than
weakened silently or deleted. The consolidated list:

| refused first form | witness | delivered correction |
|---|---|---|
| `invertedCorner` first form (StokesShift, SS-C9: direction reversed) | `lam = 1`, `e00 = 2` | `emEnergy_pos_iff_inverted` + `invertedCorner_firstForm_refuted` |
| φ_P monotonicity first form (FluorPhos, FP-C5: false at `kF = kIC = 0`, both sides `1/2`) | `kF = kIC = 0`, `kISC = 1 → 2` | re-frozen with exactly load-bearing `0 < kF + kIC` + `fpC5_firstForm_refuted` |
| four literature families read as equal-curvature two-parabola models (BEP instance layer) | the four instance rows' own parameters | `inst_I11_F1_not_model_consistent`, `inst_I11_F2_not_model_consistent`, `inst_I11_F3_not_model_consistent`, `inst_I11_F5_not_model_consistent` |
| an affine slope read as model conformance (BEP, I12) | the instance row | `inst_I12_affine_conforms_model_refuted` |
| β = 1/2 read as a law (SymmetryFactor, A1) | `(kr, kp) = (1, 4)` | `betaHalf_falsified_by_unequal` + `inst_conflation_falsified` |
| `kernel_surfaces_cross_at_tsCoord` without `lam ≠ 0` | `lam = 0`, `x = 1` | premise restored as load-bearing (a linter-driven trim had made the row false) |
| EG-C4 `secant_slope_neg_iff` note calling `x₁ ≠ x₂` decorative | `x₁ = x₂ = 2`, `lam = 1` | premise confirmed load-bearing; rule restated: *a spot is decorative iff the stripped statement still proves* |
| `Rat.*_cast` bridge rows (4 rows, Stern–Volmer R1) | vacuous `↑x = ↑x` (name elaborated inside `namespace Rat`, shadowing the RHS) | re-frozen with fully qualified RHS; `#print` confirmed a real bridge |
| three vacuity re-freezes of the Phase-3 audit (existentials whose universal form was trivially true) | universal-form witnesses | statements strengthened, re-frozen, re-delivered |

**Measured count / 实测计数**: **10** rows whose name marks a refutation, a falsification or a
not-model-consistent verdict — `grep -rhoE '^(theorem|lemma) [A-Za-z_][A-Za-z0-9_.]*(refut|falsif|not_model_consistent)[A-Za-z0-9_.]*' PhotoLean/ | sort -u`
yields: `fpC5_firstForm_refuted`, `invertedCorner_firstForm_refuted`,
`inst_I11_F1/F2/F3/F5_not_model_consistent`, `inst_I12_affine_conforms_model_refuted`,
`betaHalf_falsified_by_unequal`, `inst_conflation_falsified`, and
`symmetryFactor_conflation_falsified_and_holds_in_kernel` (this last one packs **both** halves — the
refutation at `(1,4)` and the persistence theorem on the equal-curvature diagonal — so it is a
refutation row *and* a holds-row; counted once here). Plus the 3 vacuity re-freezes and the
`Rat.*_cast` re-freeze, which are statement revisions registered in the plans' §3.1 logs.

**中文**：本仓库把负结果当一等公民：内核一旦证伪草拟语句，语句就**连同反例见证定理一起重冻结**，而不是
悄悄削弱或删除。上表汇总：StokesShift 的 SS-C9 方向写反（见证 `lam = 1, e00 = 2`）、FluorPhos 的
FP-C5 在 `kF = kIC = 0` 处为假（见证 `kISC = 1 → 2`，两侧 φ_P 都等于 1/2）、BEP 实例层把四个文献族
读成等曲率双抛物模型被证伪（四行 `inst_I11_F*_not_model_consistent`）、仿射斜率被误读为模型符合
（`inst_I12_affine_conforms_model_refuted`）、A1 的 β = 1/2 在 `(1,4)` 处被证伪
（`betaHalf_falsified_by_unequal` / `inst_conflation_falsified`）、`kernel_surfaces_cross_at_tsCoord`
被"看似可删"的 `lam ≠ 0` 实为承重（`lam = 0, x = 1` 处为假）、EG-C4 把 `x₁ ≠ x₂` 误记为装饰性前提
（实为承重；判据规则重述为"**去掉前提后语句仍能证明**才算装饰"）、Stern–Volmer 四条 `Rat.*_cast`
因 `Rat.` 前缀在 `namespace Rat` 内取到遮蔽 RHS 而成为空泛的 `↑x = ↑x`（重冻结并 `#print` 复核）、以及
阶段三审计中三处存在量词空泛化重冻结。**实测计数**：名字标记证伪的共 **10 行**
（`*refuted*` / `*falsified*` / `*not_model_consistent`；其中
`symmetryFactor_conflation_falsified_and_holds_in_kernel` 一行同时打包"证伪"与"在对角线上成立"两半，
只计一次），另有 3 处空泛化重冻结与 1 处 `Rat.*_cast`
重冻结属语句修订，记于各理论 plan 的 §3.1 日志。

---

## 8. The weakest-premise ledger / 最弱前提账

**English.** From 2026-09-21 on, every delivered row must carry **only load-bearing premises** (the
weakest-premise standard). The audited anchors, quoted as they stand in the modules:

| row | premises |
|---|---|
| `sv_d1_verdict` | `(hk0 : k0 ≠ 0) (hKa : 0 < Ka)` (trimmed in Phase 3) |
| `sv_identifiability_boundary` (`lifetimeTracks_iff_dyn`) | `(hKa : 0 < Ka)` only |
| `sv_quench_dilutes_yield` | `(hpos : 0 < kr + knr) (hq : 0 ≤ kq * q)` |
| `fretEff6_eq_one_sub_yieldOf` | `(hkD : 0 < kD) (hr6 : 0 ≤ r6) (hR : R ≠ 0)` |
| `fretEff6_inv_eq_one_plus` | `(hr6 : 0 < r6) (hR : R ≠ 0)` |
| `egBarrier_zero_iff_emEnergy_zero`, `eg_boundary_eq_tsCoord_zero` | `(hlam : lam ≠ 0)` |
| `icvsisc_barrier_zero_at_crossing` | **none** (survives `lam = 0`) |
| `kernel_surfaces_cross_at_tsCoord` | `(hlam : lam ≠ 0)` — load-bearing, false without it |
| `qy_two_channel_strictAnti_of_nr_lt` | `(hkr : 0 < kr) (h1 : 0 ≤ knr₁) (h2 : 0 ≤ knr₂) (h : knr₂ < knr₁)` |
| `log_barrierRate_eq` | `(hA : 0 < A)` only |

**中文**：自 2026-09-21 起，每条交付行只允许携带**承重前提**（最弱前提标准）。上表为审计锚点，按模块内
原样引用。两个直接对照：`icvsisc_barrier_zero_at_crossing` **无前提**（`lam = 0` 下仍真），而
`kernel_surfaces_cross_at_tsCoord` 的 `lam ≠ 0` 是承重前提（去掉即假）——两条同族的"交叉点"行前提不同，
差别由证明而非观感决定。

---

## 9. Honest boundaries / 诚实边界

**English.** 1. **Declared models only.** Every row is a statement *inside* a declared model
(two harmonic surfaces / a finite ladder with exponential-race branching / a descriptor-axis
optimisation / a two-state Hamiltonian family). An edge relates *statements about named models*; no
row claims theory equivalence or derivability of one theory from another. 2. **Conditional edges
stay conditional.** `hic` (Kasha) is a premise, not a theorem; the edge is registered with it.
3. **The degenerate curvature convention.** `x / 0 = 0` and totalized `Real.sqrt` make
`√(negative) = 0`; the convention is documented upstream at every occurrence, no relation depends
on it, and substantive rows carry their `lam ≠ 0` / `0 < lam` premises explicitly.
4. **Prose vs theorem.** The quantifier-shape discussion (RELATIONS.md §4) is explicitly prose; the
registry sections are documentation; everything else named here is a compiled declaration whose
`#print axioms` is `[propext, Classical.choice, Quot.sound]`. 5. **Opt-in certificate discipline.**
"Same physical quantity, two names" is mechanically decided *for theories that write their
certificates*; there is no signature **type** forcing a future theory to register one (the
review's S1 suggestion remains unimplemented, review finding M10). 6. **Coverage note.** The
per-theory fidelity probes glob `PhotoLean/<Theory>/*.lean` only: `Kernel.lean` and
`Relations.lean` are pinned by the compile-time re-export (every statement written out verbatim)
plus module docstrings, not by a skeleton probe. 7. **Module-level residue.** Three files carry
pre-existing `unused variable` linter warnings (`SternVolmer/Basic.lean:65`,
`SternVolmer/RatModel.lean:61`, `FluorPhos/RatModel.lean:89`; 5 warning lines total) — the strict
scan is `clean` (it scans for placeholder/axiom keywords), and no delivered row depends on the
unused binders. 8. **Accounting.** Sections whose rows add no mathematics are labelled as such; the
genuinely new rows of each batch are enumerated in the module and in RELATIONS.md §5.
**中文**：①**只谈声明模型**——每条行都是某个声明模型**内部**的陈述；边关联的是"具名模型上的命题"，
不声称理论等价、也不声称一个理论可由另一个推出。②**条件边保持条件**——`hic`（Kasha）是前提不是定理，
边随前提登记。③**退化曲率约定**——`x / 0 = 0` 与全定义 `Real.sqrt` 使 `√(负数) = 0`：上游每处均已注明，
本图无一行依赖它，实质行显式携带 `lam ≠ 0` / `0 < lam`。④**正文与定理分工**——量词形态讨论（RELATIONS.md
§4）与两份登记表明确是正文/文档，其余点名之处都是可编译声明，其 `#print axioms` 恰为
`[propext, Classical.choice, Quot.sound]`。⑤**证书纪律是自愿登记**——"同一物理量两个名字"对**写了证书**
的理论是机械判定的；仓库不存在签名**类型**强制未来理论登记（首轮审查 S1 建议未实现，评审发现 M10）。
⑥**覆盖范围**——逐理论保真探针只 glob `PhotoLean/<理论>/*.lean`，`Kernel.lean` 与 `Relations.lean` 由
编译期逐字 re-export 钉加模块 docstring 保障，而非骨架探针。⑦**模块级残留**——三个文件带既有
`unused variable` linter 警告（共 5 条警告行），严格扫描仍为 `clean`，无交付行依赖这些未用绑定。
⑧**记账**——不含新数学的小节已如实标注；每批真正的新内容在模块与 RELATIONS.md §5 中逐条列出。

---

## 10. Verification record / 复核记录

**English.** Every number below was produced by the commands in §11, this round, at the measurement
state named in the status box:

| gate | command | result |
|---|---|---|
| whole-tree build + scan + leaf planes | `proofs/scripts/check.sh --strict` | `build: OK`, scan `clean`, 17/17 leaf data planes `OK`, **verdict: PASS** |
| statement fidelity (17 probes) | `python3 theories/BEP/probes/bep-fidelity.py --theory <T>` | 51/102/191/151/132/139/35/29/46/29/30/26/36/20/32/33/71 word-for-word; **0 signature differences, 0 not delivered** for all 17 |
| realization of the delivery claim | `proofs/scripts/axioms.sh <Mod> <fully.qualified.thm>` | spot rows of every batch: `verdict: PASS (only mathlib infrastructure axioms)`; the 59 RACI theorems and the 46 upstream photophysics theorem rows were run to completion in the close-out rounds |
| independent review | `verifier` role, read-only | each of the 17 boards records a verifier PASS (batch: runs 1–5 + the Phase-3 final review; RACI: close-out run) |
| commit discipline | `git log --oneline` | one commit per theory for the batch, per-module/theory for the earlier work, doc commits for the registration rounds |

**Honest reading of the gate / 门结果的诚实读法**: the whole-tree result is meaningful only
together with the tree state it was taken in (HEAD + `git status`); the fidelity numbers are
*signature* comparisons (they compare up to the first `:=`, so definition **bodies** are not
covered — the `rfl` certificates are what pin bodies).
**中文**：上表每个数字都由 §11 的命令在本轮、于状态框所述树状态上产出。**门结果的诚实读法**：全树结果
只有连同当时的树状态（HEAD + `git status`）才有意义；保真数字是**签名**比较（比较到第一个 `:=` 为止，
**不覆盖定义体**）——定义体由 `rfl` 证书钉住。

---

## 11. Reproduction / 复核

```bash
# whole-tree gate (build + strict scan + leaf data planes)
proofs/scripts/check.sh --strict

# statement fidelity — all seventeen theories
for T in Marcus Hammond BEP Kasha Sabatier Goldschmidt SymmetryFactor \
         KashaVavilov SternVolmer QuantumYield FluorPhos EnergyGapLaw \
         StokesShift ICvsISC Forster Einstein RACI; do
  python3 theories/BEP/probes/bep-fidelity.py --theory "$T"
done

# the relation module's own rows (spot list; every named row has an axioms.sh call in RELATIONS.md §7)
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.hammond_trend_exact_bep_law_inexact
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.kernel_marcusIC
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.marcus_rate_eq_activity
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.marcusRate_antiVolcanoDescriptor
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.symmetryFactor_betaHalf_iff
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.sv_d1_verdict
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.kv_d2_verdict
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.kernel_surfaces_cross_at_tsCoord
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.raci_qy_eq_yieldOf_two_channel

# statement authorities (placeholders on purpose; compile-only, warnings expected)
proofs/scripts/lake env lean theories/RACI/probes/RACI-statement-skeleton.lean
```

---

## 12. Onboarding an eighteenth node / 第十八个节点的接入清单

**English.** The graph has a repeatable entry procedure; a new theory is "on the graph" only when
all of the following hold:

1. a **statement authority** skeleton compiling (`theories/<T>/probes/<T>-statement-skeleton.lean`),
   with a fidelity probe reporting `0 signature differences` against the delivered modules;
2. the required **kernel copies** and their `rfl` (or unfold) certificates, if the theory reads the
   quadratic object — a failing certificate is a stop-and-investigate event, never a reason to edit
   a delivered module;
3. **no `sorry`, no custom axiom** in delivered rows; `#print axioms` = `[propext, Classical.choice,
   Quot.sound]`; `check.sh --strict` green;
4. **weakest premises** on every row, and physical approximations explicit as premises;
5. an **edge or a registered absence** against *every* existing node — written into
   `PhotoLean/Relations.lean` (a new numbered section) **and** into the next batch layer of
   `theories/RELATIONS.md` (this consolidated report is then refreshed);
6. refuted drafts delivered as **counterexample-witness theorems**;
7. an independent **verifier PASS** recorded on the theory's `TASKS.md`, only then a tick by the lead;
8. the README current-state section and the theory's four leaves updated (theory-closure checklist),
   with one commit per unit of work.

**中文**：关系图有可重复的接入流程；只有下列全部成立，新理论才算"在图上"：①语句权威骨架可编译且有
保真探针 `0 signature differences`；②若是二次对象的读法，必须携带内核副本及其 `rfl`（或展开）证书
——证书失败是"停下来排查"事件，绝不是去改交付模块；③交付行无 `sorry`、无自定义公理，
`#print axioms` 恰为三条 mathlib 基础设施公理，`check.sh --strict` 通过；④每行最弱前提、物理近似显式化
为前提；⑤对**每个**既有节点给出边或已登记缺席，写入 `PhotoLean/Relations.lean` 新编号小节，并追加到
`theories/RELATIONS.md` 的下一批层（随后刷新本总结报告）；⑥被证伪的草稿以**反例见证定理**交付；
⑦独立 **verifier PASS** 记入该理论 `TASKS.md`，之后才由 lead 打勾；⑧更新 README 当前状态段与四个叶子
文件（理论关闭清单），按工作单元提交。

---

## 13. File map / 文件地图

| artifact | role |
|---|---|
| `PhotoLean/Kernel.lean` | the shared object: 6 definitions + 2 theorems, `import Mathlib` only |
| `PhotoLean/Relations.lean` | the machine-checked edge inventory: 78 declarations, §1–§17 |
| `PhotoLean/<T>/**` | the 17 theories, 92 modules |
| `theories/RELATIONS.md` | the bilingual **incremental** discussion draft (§1–§9) |
| `theories/GRAPH-REPORT.md` | **this file** — the consolidated report |
| `theories/<T>/{plan,TASKS,LITERATURE,RESULTS}.md` + `probes/` | per-theory leaves: plan (with §3.1 correction logs), board (verifier records), literature (with formalizable implications), bilingual results, statement authorities and probes |
| `proofs/EXPERIENCE.md` | cross-round write-back, including every measured failure path |
| `proofs/API-NOTES.md` | mathlib calibration; §photobatch statement-change index (rows 1–18) |
| `README.md` | current state: 17 theories, relation paragraph, reproduction commands |

**中文**：上表为文件地图：内核、关系模块、17 个理论模块、增量的双语讨论稿、本总结报告、各理论的四件
叶子 + 探针、经验库、API 校准日志与 README 当前状态段。本报告与 `theories/RELATIONS.md` 分工固定：
前者是**一次成型的总结**，后者是**按批追加的讨论稿**；两者都引用同一份机器检查清单
`PhotoLean/Relations.lean`，因此不会漂移出可检查内容。
