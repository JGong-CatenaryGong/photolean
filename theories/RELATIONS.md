# theories/RELATIONS.md — seven theories, one graph: composition, look-alikes, no-edges, and the first adjudicated conflation

> **Status.** This is the discussion draft of the relation graph of the **seven** delivered theories
> (Marcus inverted region, Hammond postulate, Bell–Evans–Polanyi principle, Kasha's rule, Sabatier
> principle / volcano plot — the five of the second-batch graph — the Goldschmidt tolerance factor
> with Goldschmidt's rules of ionic substitution, which shares no module and no object with them
> and therefore enters the graph only through the no-edge registry (§2.5/§3 N4), and the
> **symmetry-factor adjudication** (`SymmetryFactor`, 2026-09-21), which generalizes the kernel's
> two-parabola object to **unequal curvatures** and enters as the graph's first **adjudicated
> conflation**, class **A1**, §3bis/§11 of the Lean companion).
> Its machine-checked companion is `PhotoLean/Relations.lean`
> (**50 declarations**: 46 at the second batch — measured 2026-09-21, commit `eb5e178` — plus the
> 4 rows of §11 added by the third batch the same day; the sixth-theory registration had been a
> comment-only extension of §10) over
> the shared kernel `PhotoLean/Kernel.lean` (6 definitions + 2 theorems); every claim below that
> names a Lean theorem is backed by a declaration that compiles and whose `#print axioms` output is
> `[propext, Classical.choice, Quot.sound]`. It is written in the bilingual style of the
> `RESULTS.md` deliverables (English original followed by its Chinese rendering); the language
> policy and the freeze of the historical `.en.md` mirrors are recorded in `README.md`.
>
> **Provenance.** Three tasks built this file. The first (2026-09-20) took the bridge inventory of the
> review record (`review/REVIEW.md` §3.1, 13 rows / 16 theorems) as its input and collected the
> edges of the three two-parabola theories. The second (2026-09-21) executed `AGENTS.md` iron
> rule 8 item ② for the two newer theories: the Kasha → Marcus conditional composition (§2.4), the
> Sabatier → BEP composition (§2.4), the Sabatier ↔ Marcus look-alike cluster (§3, N3) and the
> no-edge registry (§2.5). The statement forms of the new rows were calibrated first in
> `theories/Marcus/probes/relations-b2-statement-skeleton.lean`; no candidate had to be demoted to
> prose, and the one failed proof path (a rewrite pattern in the uniqueness half of C2) is recorded
> in `proofs/EXPERIENCE.md`. The third (2026-09-21, the H1-crossing round of
> adjudication rows and the two specialization certificates (§3bis, `Relations.lean` §11), plus the
> seventh node's pairs in the no-edge registry (§2.5).
>
> **中文（状态与来源）**：本文件是**七个**已交付理论（Marcus 反转区、Hammond 假说、Bell–Evans–Polanyi
> 原理、Kasha 规则、Sabatier 原则/火山图，Goldschmidt 容忍因子与取代规则——经**无边登记**接入——以及
> **对称因子裁决** `SymmetryFactor`，它把内核的双抛物面对象推广到**非等曲率**，以本图第一条
> **已裁决混同**（A1 类，§3bis / Lean 对应物 §11）的身份接入）**关系图**的讨论稿。可机器检查的对应物是
> `PhotoLean/Relations.lean`（**50 条声明**：第二批 46 条——实测 2026-09-21、提交 `eb5e178`——加同日
> 第三批的 §11 四条）与共享内核
> `PhotoLean/Kernel.lean`（6 定义 + 2 定理）；下文凡点名 Lean 定理之处，均有可编译声明支撑，且其
> `#print axioms` 输出恰为 `[propext, Classical.choice, Quot.sound]`。本文按各理论 `RESULTS.md` 的
> 双语排版书写（英文原文后紧跟中文对照）；语言政策与历史 `.en.md` 镜像的冻结见 `README.md`。
> **来源**：本文件由三次任务建成。第一次（2026-09-20）以审查记录 `review/REVIEW.md` §3.1（13 行 /
> 16 条定理）为输入，收集三个双抛物面理论的关系边；第二次（2026-09-21）执行 `AGENTS.md` 铁律 8 第 ② 项，
> 为两个较新的理论登记关系边 —— Kasha → Marcus 条件性组合（§2.4）、Sabatier → BEP 组合（§2.4）、
> Sabatier ↔ Marcus 形似实异簇（§3 N3）与**无边登记**（§2.5）。新增语句的形态先在
> `theories/Marcus/probes/relations-b2-statement-skeleton.lean` 中完成标定；本次**没有任何候选被降级**为
> 正文，唯一失败的证明路径（C2 唯一性半边的一处 `rw` 模式）记录在 `proofs/EXPERIENCE.md`。第三次
> 两条特化证书（§3bis、`Relations.lean` §11），以及第七节点在无边登记（§2.5）中的各对。

---

## 1. The shared object / 同一个对象

**English.** All three theories describe one elementary reaction step by the same classical model:
two harmonic potential-energy surfaces of **equal** curvature `2λ`, the reactant well at `q = 0`,
the product well at `q = 1`, and the transition state taken as the classical **crossing point**. In
the driving-force convention `x = -ΔG°` the crossing point is the transition-state coordinate
`q‡ = (λ − x)/(2λ)`, the forward barrier is `Ea = (λ − x)²/(4λ)`, the reverse barrier is
`(λ + x)²/(4λ)`, and the transfer (Brønsted/Leffler) coefficient is `α = 1/2 − x/(2λ)`. These six
objects now have **one definition each** — `PhotoLean.Kernel.{reactantSurface, productSurface,
barrier, reverseBarrier, tsCoord, transfer}` — and `PhotoLean/Kernel.lean` imports `Mathlib` only,
so it sits at the bottom of the dependency graph and cannot import any theory.

The three theories are three **readings** of this single quadratic object:

| theory | reading | observable | exact statement |
|---|---|---|---|
| Marcus | the *rate* `k = A·exp(−Ea/k_BT)` | rate direction | `InvertedDescriptor`: on `lam < x` the rate strictly decreases |
| Hammond | the *structure* `q‡` | transition-state coordinate | `HammondDescriptor`: `x₁ < x₂ ⇒ q‡(x₂) < q‡(x₁)` |
| BEP | the *activation energy* as an affine function of `x` | Brønsted slope / window error | `EPConformsOnWindow`: `|Ea(x) − line(x)| ≤ tol` on a window |

**中文（同一个对象）**：三个理论用同一个经典模型描述同一个基元步骤：两条**等曲率** `2λ` 的谐振势能面，
反应物井在 `q = 0`、产物井在 `q = 1`，过渡态取经典**交叉点**。在驱动力约定 `x = -ΔG°` 下，交叉点即
过渡态坐标 `q‡ = (λ − x)/(2λ)`，正向势垒 `Ea = (λ − x)²/(4λ)`，逆向势垒 `(λ + x)²/(4λ)`，
转移（Brønsted/Leffler）系数 `α = 1/2 − x/(2λ)`。这六个对象现在各有**唯一定义**：
`PhotoLean.Kernel.{reactantSurface, productSurface, barrier, reverseBarrier, tsCoord, transfer}`；
`PhotoLean/Kernel.lean` 只 `import Mathlib`，位于依赖图底部，不 import 任何理论模块。
三个理论是同一二次对象的三种**读法**：Marcus 读**速率**（`k = A·exp(−Ea/k_BT)` 在反转区随驱动力递减），
Hammond 读**结构**（过渡态坐标随驱动力严格递减），BEP 读**活化能的仿射性**（容差窗口内的线性自由能关系）。

**English.** The two newer theories are **not** readings of that quadratic object, and the graph
says so: Kasha's rule is a statement about a finite rate cascade (no potential-energy surface
appears in it), and the Sabatier volcano is an optimisation over a descriptor axis whose branches
are the repository's BEP *lines*, not parabolas. They join the graph by **composition** (§2.4) —
the Kasha edge consumes the kernel barrier through a declared modelling premise, the Sabatier edge
consumes `BEP.eact` — and by the one **shared functional form** that the Marcus rate and the
Sabatier activity turn out to have (§3, N3/C1). Nothing else of the two is claimed to be a
re-reading of the kernel.

**中文**：两个较新的理论**不是**这个二次对象的读法，关系图如实登记这一点：Kasha 规则是关于有限速率级联的
命题（其中不出现任何势能面），Sabatier 火山是描述符轴上的优化问题（其两条支路用的是本仓库的 BEP
**直线**而非抛物线）。它们通过**组合**进入关系图（§2.4：Kasha 边经一个声明的建模前提消费内核势垒，
Sabatier 边消费 `BEP.eact`），并通过 Marcus 速率与 Sabatier 活性恰好共有的**同一函数形式**
（§3 N3/C1）与图相连；除此之外，不声称二者是内核的重新读法。

---

## 2. The relation graph / 关系图

### 2.1 True equivalences (`↔`) / 真等价

**English.** Six delivered equivalences are re-exported verbatim in §2 of `PhotoLean/Relations.lean`
(none re-proved), and one further equivalence is *composed* in §6 of that module:

| # | statement (module) | reading |
|---|---|---|
| E1 | `transfer_eq_tsCoord_bridge` (BEP ↔ Hammond) | the BEP coefficient *is* the transition-state coordinate; **not** definitional — `BEP.transfer` was deliberately written in linear-response form, so the identity needs `lam ≠ 0` |
| E2 | `secSlope_eq_lefflerSecant` (BEP ↔ Hammond) | the *observable* window slope of barrier data equals the Leffler secant over the same pair |
| E3 | `epBounds_iff_no_inverted_direction` (BEP ↔ Marcus) | `0 ≤ α ≤ 1` exactly when neither the forward direction `x` nor the reverse direction `−x` lies in the Marcus inverted region |
| E4 | `tsCoord_lt_zero_iff_inverted` (Hammond ↔ Marcus) | the transition state leaves the reactant side exactly in the inverted region |
| E5 | `lefflerSecant_neg_iff_inverted` (Hammond ↔ Marcus) | a negative Brønsted coefficient is exactly the inverted region, seen from barrier data |
| E6 | `hammondZoneQ_beyondReactant_iff_inverted` (Hammond ↔ Marcus, over `ℚ`) | the two computable classifiers single out the same instances |
| E7 | `hammond_sharp_iff_marcus_sharp` (**composed in this task**) | `HammondDescriptor lam ↔ (rate-positivity ∧ Marcus.InvertedDescriptor)`: under `0 < A, 0 < k_B, 0 < T` the two sharp conditions coincide, i.e. both descriptions characterize exactly the positive-curvature model. Honest accounting: the statement is a **composition** of the two delivered sharp characterizations (`Hammond.hammond_sharp`, `Marcus.descriptor_sharp`) — no new mathematics beyond the composition |

**中文（真等价）**：上表 7 条真 `↔`。E1–E6 是 §2 中逐字复用（未重新证明）；E7 是本次**复合**：
在 `0 < A`、`0 < k_B`、`0 < T` 下，`HammondDescriptor lam ↔ (速率处处正 ∧ Marcus.InvertedDescriptor)`——
两个锐利条件（`hammond_sharp`、`descriptor_sharp`）刻画的是**同一个**正曲率模型，因此两条"描述"作为
对曲率的假设是**同外延**的。记账上如实说明：E7 的数学内容就是这两条已交付锐利刻画的**复合**，复合之外
没有新数学。注意 E1 刻意非定义性：BEP 把 `transfer` 写成线性响应体，使同一性必须**证明**
而不能靠 `rfl` 展开——这是反"伪造等价"的设计，不是巧合。

### 2.2 One-way entailments (`→`) / 单向蕴含

**English.** Three edges point one way and are documented as such (no over-claiming):

| # | statement | reading |
|---|---|---|
| O1 | `epBounds_of_reactionRegion` (Hammond → BEP) | a step strictly inside the Hammond window satisfies the Evans–Polanyi bounds; the converse fails |
| O2 | `epBounds_of_marcus_normal` (Marcus → BEP) | a normal-region step with `−λ ≤ x` satisfies the bounds; both hypotheses are needed |
| O3 | `hammondDescriptor_of_epConformsOnWindow` (**new here**) | window conformance entails the structural descriptor — and the road runs **through the positivity conjunct `0 < lam` only**; the tolerance bound is not consumed |

**中文（单向蕴含）**：上表 3 条 `→` 边，均如实标注单向。O3 是本任务新发现的边：BEP 的窗口符合性
**蕴含** Hammond 结构描述，但真正的逻辑通道只是谓词里的合取项 `0 < lam`（它单独就能推出结构律），
容差界本身不被消费。记在这里是为了**不让关系图过度声称**一条更深的联系。

### 2.3 Definitional reuse and alias certificates (`rfl`) / 定义复用与别名证书

**English.** §4 of `Relations.lean` re-exports the four Hammond-composition rows that consume
`Marcus.Reorg`'s inner/outer reorganization energy instead of redefining it
(`hammond_descriptor_of_inner`, `hammond_descriptor_of_microscopic`,
`hammond_descriptor_of_nonoverlap`, `exists_reactionRegion_of_microscopic`) — the cleanest kind of
bridge: one definition, two theories. §5 re-exports the four remaining ledger rows of the
inventory: `bep_eact_eq_marcus_barrier`, `bep_rate_eq_exp_neg_eact`,
`hammond_barrier_eq_gapReactant`, `marcus_rat_zoneQ_inverted_iff`.

§1 of `Relations.lean` holds the eight **kernel certificates** — `kernel_barrier_eq_marcus`,
`kernel_barrier_eq_hammond`, `kernel_barrier_eq_bep`, `kernel_reverseBarrier_eq_hammond`,
`kernel_tsCoord_eq_hammond`, `kernel_transfer_eq_bep`, `kernel_reactantSurface_eq_hammond`,
`kernel_productSurface_eq_hammond`. Each is closed by `rfl`: the kernel definition and the
theory's own copy are the *same body*. Their epistemic status is a **naming certificate**, not a
mathematical discovery — and their operational role is a **regression alarm**: if one of them
stops being `rfl`, the kernel and a delivered definition have drifted apart, and the required
response is to stop and investigate, never to edit a delivered module in order to restore the
certificate.

**中文（定义复用与别名证书）**：§4 复用 Hammond 复合层对 `Marcus.Reorg` 内/外球重组能的 4 条
（不重新定义 `lamInner/lamOuter`）——这是最干净的一种桥：一份定义、两个理论。§5 收齐清单余下的
4 行（BEP 势垒等同、速率重写、Hammond 前向间隙等同、ℚ 侧反转区判定）。§1 是 8 条**内核证书**，
全部由 `rfl` 闭合：内核定义与各理论自带副本**体逐字节相同**。它们的认识论地位是**命名校验**（不是
数学发现），运行角色是**回归报警器**：哪一条不再 `rfl`，就说明内核与某个已交付定义漂移了——
此时的动作是**停下来排查**，绝不是改交付模块去把证书凑回来。

### 2.4 Composition edges (`→`, conditional) / 组合边（单向、条件性）

**English.** Two edges of the second batch are **compositions** rather than comparisons: a newer
theory consumes an older one as a component. Both are re-exported verbatim into `Relations.lean`
§7–§8 (the statements live in `Kasha/Compose.lean` and `Sabatier/Compose.lean`).

| # | statement | reading |
|---|---|---|
| K1 | `kashaWithin_one_marcus` (Kasha → Marcus, **conditional**) | under the declared modelling premise `hic` — the `S₂ → S₁` internal-conversion rate *is* the Marcus rate `Kasha.marcusIC` — conformance to Kasha's rule at tolerance `tol` is **exactly** the gap window `(λ − x)² ≤ 4λ·k_BT·log K` |
| K2 | `not_kashaWithin_of_gap_far` (Kasha → Marcus, one-way) | outside the window the tolerance fails: a gap deep in the Marcus inverted region, or an activation-controlled one, leaks emission from above the lowest state — the model-side face of the anti-Kasha family |
| K3 | `kashaWindow_halfWidth` (Kasha → Marcus) | the same criterion as a half-width bound `\|λ − x\| ≤ √K′` around the reorganization energy |
| K4 | `kernel_marcusIC` (**certificate proved here**) | the Kasha internal-conversion rate is the kernel barrier inside the Marcus rate law; Kasha states its rate against `Marcus.Basic` and does not import the kernel, so this row is what puts it on the shared kernel of §1 |
| S1 | `linearVolcano_eq_bepTangent` (Sabatier → BEP) | the literature's linear volcano *is* the maximum of the two tangent lines of the two-parabola branches |
| S2 | `bepLine_le_eact`, `linearVolcano_le_parabolic` (Sabatier → BEP) | each tangent lies below its parabola, so the linear volcano **underestimates** the barrier pointwise — the BEP defect law `x²/(4λ) ≥ 0` read geometrically |
| S3 | `parabolic_descriptor` (Sabatier → BEP) | the Sabatier description holds in the two-parabola model with **no linearization** |
| S4 | `apexPar_self`, `linearVolcano_apex_exact` (Sabatier → BEP) | a symmetric cycle's apex is thermoneutral, and there the linear and the parabolic volcano agree exactly |

**Conditionality is part of the edge.** `hic` is a premise of the Kasha theory, not a theorem of
this module: the edge is registered with the premise attached, and the Kasha plan's honesty table
is its home.

**中文（组合边）**：第二批的两条边是**组合**而非比较——较新的理论把较老的理论当作组件消费，
两者都已逐字 re-export 进 `Relations.lean` §7–§8（语句本体在 `Kasha/Compose.lean` 与
`Sabatier/Compose.lean`）。**K1**（条件性）：在"`S₂ → S₁` 内转换速率**就是** Marcus 速率
`Kasha.marcusIC`"这一**声明的建模前提** `hic` 下，Kasha 规则在容差 `tol` 下的符合性**恰好等价于**
能隙窗口 `(λ − x)² ≤ 4λ·k_BT·log K`；**K2** 是窗口外的单向失败方向（深反转区或活化控制侧泄漏上级发射，
即反 Kasha 族的模型侧面孔）；**K3** 是同一判据的半宽形式；**K4** 是本次**新证的内核证书**，把 Kasha
的内转换速率钉到共享内核的势垒上（Kasha 自身只 import `Marcus.Basic`）。**S1–S4** 是 Sabatier → BEP：
文献的线性火山**就是**双抛物面两支切线之最大；切线在抛物线之下 ⇒ 线性模型**逐点低估**势垒（BEP 缺陷律的
几何读法）；双抛物面模型**无需线性化**本身就是火山；对称循环顶点落在热中性处且两种模型在该点精确相合。
**条件性属于边本身**：`hic` 是 Kasha 理论的前提而非本模块的定理，边连同前提一起登记，其归属是 Kasha
规划的诚实表。

### 2.5 The no-edge registry / 无边登记

**English.** An absent edge is a registered fact, not an oversight: the graph is complete in the
sense that **every** theory sits on it. The registry lives at the end of `Relations.lean` (§10),
each pair with its dependency fact and its modelling reason.

| pair | edge | why |
|---|---|---|
| Marcus ↔ BEP, Marcus ↔ Hammond | yes, first batch | §2.1–§2.3 |
| Marcus ↔ Sabatier | yes, second batch | the look-alike cluster, §3 N3 |
| Kasha → Marcus | yes, second batch | conditional composition, §2.4 |
| Sabatier → BEP | yes, second batch | composition, §2.4 |
| Kasha ↔ BEP | **none** | Kasha consumes only the barrier inside `marcusIC`; no row of the ladder theory mentions a line law, a defect or a tolerance window |
| Kasha ↔ Hammond | **none** | branching probabilities vs. the structural coordinate; no row connects them |
| Sabatier ↔ Hammond | **none** | Sabatier imports `BEP.Basic` only |
| Sabatier ↔ Kasha | **none** | no shared module and no shared object |
| Goldschmidt ↔ all six | **none** | the Goldschmidt tree imports `Mathlib` and its own modules only (`Basic`/`Rules` ← `Mathlib`, `Criterion` ← `Basic`, `Sharp` ← `Basic`+`Rules`+`Criterion`, `RatModel` ← `Basic`+`Criterion`+`Rules`, `Instances` ← **four** of them (`Basic`+`Rules`+`Criterion`+`RatModel`; it does not import `Sharp`)); the modelling reason is that its content is *geometric* (ionic radii, a packing ratio, a band on it, three substitution rules) while the six state facts about *energies* on one reaction coordinate (SymmetryFactor's scalar is a curvature **pair** `(kr,kp)`, still an energy-model quantity, not a radius) — the two vocabularies share no scalar |
| Goldschmidt ↔ Sabatier | **none** (a shape look-alike only) | a symmetric band about an ideal value is an absolute-deviation bound in both, and both have a three-way classifier — but the scalars are unrelated (radius ratio vs. binding energy), the sharp conditions differ (Goldschmidt's window equivalence is exact for every band; Sabatier's is `0 < alphaA * alphaB`) and the classifiers decide different propositions — §3 N4 |
| SymmetryFactor ↔ Marcus, Hammond, BEP | yes, third batch | the seventh theory generalizes the kernel's two-parabola object to unequal curvatures; at the equal-curvature diagonal its coordinate IS `Kernel.tsCoord · 0` and IS `BEP.transfer · 0` (certificates), and its A1 verdict decides the β = 1/2 reading that E1 identifies with the structural coefficient — §3bis, `Relations.lean` §11 |
| SymmetryFactor ↔ Kasha, Sabatier, Goldschmidt | **none** | the curvature-pair scalar `(kr,kp)` shares no object with the ladder's branching rates, the volcano's descriptor axis, or the ionic radii; dependency fact: `PhotoLean/SymmetryFactor/*` imports `Mathlib`, `PhotoLean.Kernel`, `PhotoLean.BEP.Criterion` and its own modules only |

**中文（无边登记）**：不存在的边是**被登记的事实**而非疏漏——关系图的完整性取"**每个理论都在图上**"之义。
登记表位于 `Relations.lean` 末尾（§10），逐对给出依赖图事实与建模理由。有边者为：Marcus ↔ BEP、
Marcus ↔ Hammond（第一批，§2.1–§2.3）、Marcus ↔ Sabatier（第二批，形似实异簇 §3 N3）、Kasha → Marcus
（条件性组合，§2.4）、Sabatier → BEP（组合，§2.4）、SymmetryFactor ↔ Marcus/Hammond/BEP（第三批，A1 裁决 +
特化证书，§3bis / `Relations.lean` §11）；**无边**者为：Kasha ↔ BEP（Kasha 只消费
`marcusIC` 里的势垒，阶梯理论没有任何一行提到直线律、缺陷或容差窗口）、Kasha ↔ Hammond（分支概率与结构
坐标之间没有已证联系）、Sabatier ↔ Hammond（Sabatier 只 import `BEP.Basic`）、Sabatier ↔ Kasha
（不共享模块、不共享对象）、**Goldschmidt ↔ 全部六个**（Goldschmidt 树只 import `Mathlib` 与自身模块；
建模理由：它的内容是**几何量**——离子半径、堆积比值、其上的容忍带、三条取代规则——而六个理论说的是
同一反应坐标上的**能量**事实（SymmetryFactor 的标量是曲率**对** `(kr,kp)`，仍是能量模型量而非半径），
两套词汇不共享任何标量）、**Goldschmidt ↔ Sabatier**（只有形状相似、无
边：两侧的对称带都等价于「偏离理想值的绝对值有界」，也都各有一个三分类器，但标量无关联、锐利条件不同、
分类器判定的是不同的命题——§3 N4）、**SymmetryFactor ↔ Kasha/Sabatier/Goldschmidt**（曲率对标量与阶梯分支
速率、火山描述符轴、离子半径均无共享对象；依赖事实：`PhotoLean/SymmetryFactor/*` 只 import `Mathlib`、
`PhotoLean.Kernel`、`PhotoLean.BEP.Criterion` 与自身模块）。

---

## 3. Look-alike but different: the non-relations / 形似实异：非关系

**English.** The relation graph is not complete without the edges that **do not exist**. Two of them
are pinned as theorems (new in this task); the rest belong to §4 (prose, because they are not
theorem-shaped). One qualifier, stated up front: the two blocks below are *readings* attached to the
delivered statements — the theorems themselves are exactly the ones cited.

**N1 — exact in one reading, exactly false in the other** (`hammond_trend_exact_bep_law_inexact`).
For every `lam ≠ 0`, *in the same model*:

* the transition-state coordinate is **exactly** affine — there are `c, k` with
  `Kernel.tsCoord lam x = c + k·x` for all `x` (it is `1/2 − x/(2λ)`); together with the structural
  descriptor's own sharp condition `0 < lam` (`hammond_sharp`) this makes "more driving force,
  earlier transition state" hold with **no tolerance parameter**. The qualifier matters: the
  affinity is exact for every `lam ≠ 0`, but at `lam < 0` the *direction* is reversed — the
  delivered witness is `Hammond.exists_direction_reversal_of_neg`, and the descriptor fails there
  (N2's third conjunct) — so the trend is affinity **plus** `0 < lam`;
* the BEP line law is **exactly violated on every non-degenerate interval** — for all `p < q`,
  `¬ BEP.EPLinearOn lam (Set.Icc p q)` (the second-difference engine
  `BEP.not_epLinearOn_of_ne_zero`; the exact defect is the quadratic remainder `x²/(4λ)`).

This is the sharpest statement of why the BEP reading *must* be stated with a tolerance
(`bepDefect` law, sharp radius `2√(λ·tol)`, `epExact_iff_degenerate`) while the Hammond reading must
not: one description is exact on the linear object `q‡ = q‡(x)` (at positive curvature), the other
is a claim about a quadratic that is false everywhere off the degenerate model.

**N2 — the two `∀∀` predicates are not equally strong**
(`rate_predicate_satisfiable_without_positive_curvature`). The rate predicate is satisfied in a
parameter region where the rate is *everywhere negative* (`A = lam = −1`, `k_BT = 1`): the formal
monotone pattern survives multiplication by a negative prefactor. The structural predicate, by
contrast, holds exactly for positive curvature (`hammond_sharp`). So "the rate decreases across the
inverted region" does **not** pin the physical model, while "the transition-state coordinate
decreases" does — the shape difference that the positivity conjunct in `descriptor_sharp` repairs.

**中文（非关系）**：关系图必须包含**不存在**的边。两条被钉成定理（本任务新增）；先声明口径：以下解读
是**挂在交付语句上的读法**，定理本身以下列名为准。
**N1**（`hammond_trend_exact_bep_law_inexact`）——对每个 `lam ≠ 0`，在**同一个**模型里，过渡态坐标
**精确**仿射（`q‡ = 1/2 − x/(2λ)`）；再加上结构描述自身的锐利条件 `0 < lam`（`hammond_sharp`），
"驱动力越大、过渡态越早"**无需任何容差参数**即成立。限定词不可省：仿射性对每个 `lam ≠ 0` 都成立，
但 `lam < 0` 时**方向**反转——已交付的见证是 `Hammond.exists_direction_reversal_of_neg`，且描述在该处
失效（N2 第三合取项）——所以"趋势"= 仿射 **且** `0 < lam`，不是仿射本身。同一模型里 BEP 线性律在
任何**非退化区间**上都**精确**被违反（`BEP.not_epLinearOn_of_ne_zero`，二阶差分引擎；精确缺陷是二次
余项 `x²/(4λ)`）。这正是"BEP 读法必须带容差、Hammond 读法必须不带"的形式化分界。
**N2**（`rate_predicate_satisfiable_without_positive_curvature`）——速率谓词在速率**处处为负**的参数区
（`A = lam = −1`，`k_BT = 1`）仍成立（乘负前置因子不改变单调模式）；结构谓词则当且仅当曲率为正
（`hammond_sharp`）。因此"反转区速率递减"**钉不住**物理模型，"过渡态坐标递减"钉得住——这正是
`descriptor_sharp` 里那条正性合取项所修补的强度差。

**N3 — the Sabatier volcano and the Marcus rate: one predicate, two optima** (second batch). The
two theories share more than a shape. `marcus_rate_eq_activity` (C1) shows the Marcus rate **is**
the Sabatier activity functional applied to the kernel barrier, scaled by `A`; and
`marcusRate_antiVolcanoDescriptor` (C2) shows the Marcus rate satisfies the very same predicate
`Sabatier.AntiVolcanoDescriptor`, with `lam` as its unique global maximizer. What the pair does
**not** share is the optimum, and three facets pin the difference — each a theorem, none a caveat:

* **the height at the optimum** (C3): the Marcus optimum is the *barrierless* point
  (`Kernel.barrier lam lam = 0`, identically in `lam`), while the Sabatier reference pass sits at
  `1/2` (`apexBarrier_reference_nonzero`) — a volcano pass is not a barrierless point;
* **the secant at the optimum** (C4): the one-sided secant of the Marcus barrier at the optimum is
  exactly `h/(4λ)`, so it vanishes with the step, whereas the volcano legs have step-independent
  secant slopes `α_A` and `−α_B` (`volcanoBarrier_secSlope_of_apex_le` and its counterpart below
  the apex) — a smooth optimum against a kink, both stated without calculus;
* **the parameter dependence of the optimal position** (C5): the Marcus optimum is fixed by the
  curvature alone (`marcus_optimum_fixed_by_curvature`: the same `λ` is optimal for every
  admissible `A` and `k_BT`), while the Sabatier apex moves when only the offsets change with the
  slopes held fixed (`sabatier_apex_moves_with_offsets`).

**中文（N3：同一个谓词，两个最优）**：两个理论共享的不只是外形。C1（`marcus_rate_eq_activity`）证明
Marcus 速率**就是** Sabatier 活性泛函作用于内核势垒再乘 `A`；C2（`marcusRate_antiVolcanoDescriptor`）
证明 Marcus 速率满足**同一个**谓词 `Sabatier.AntiVolcanoDescriptor`，且 `lam` 是其唯一全局最大点。
二者**不**共享的是最优点本身，三个面把差异钉死，每一面都是定理而非附注：**高度**（C3）——Marcus 最优点是
**无势垒点**（`Kernel.barrier lam lam = 0`，对 `lam` 恒成立），而 Sabatier 参考火山口在 `1/2`
（`apexBarrier_reference_nonzero`）：火山口不是无势垒点；**割线**（C4）——Marcus 势垒在最优点的单侧割线
恰为 `h/(4λ)`，随步长消失，而火山两侧腿的割线斜率与步长无关（`α_A` 与 `−α_B`）：平滑最优对折角最优，
两侧都不涉及微分；**参数依赖**（C5）——Marcus 最优位置仅由曲率决定（`marcus_optimum_fixed_by_curvature`：
同一个 `λ` 对一切可采纳的 `A`、`k_BT` 都最优），而 Sabatier 顶点在斜率不变、只改偏移量时就会移动
（`sabatier_apex_moves_with_offsets`）。与 §2.5 的无边登记合读，这是 N1/N2 同一教训的第二批形态：
**共享谓词不等于共享机制**，而且差异是定理，不是免责声明。


**N4 — the Goldschmidt tolerance band and the Sabatier volcano: the same *shape*, no edge**
(sixth theory, 2026-09-21). Two shapes coincide and the coincidence is registered rather than
monetised into an edge. (i) *Symmetric band = absolute-deviation bound.* Goldschmidt's G3 row
`conforms_symmetric_band_iff` proves
`GoldschmidtConforms (1 - delta) (1 + delta) rA rB rO ↔ |rA - idealA rB rO| ≤ delta * idealAO rB rO`
for every `delta` (no `0 ≤ delta` premise — plan §3.1 item 2); Sabatier's S1 definition
`NearOptimal tol apexD dE := |dE - apexD| ≤ tol` is the same shape read on a descriptor axis. (ii)
*Three-way classifier of a scalar against a band.* `GoldschmidtZone` with `goldschmidtZone lo hi t` (the
exact characterization of its `tooLarge` branch being `lo ≤ t ∧ hi < t`, because the cascade tests
`t < lo` first) versus `Sabatier.SZone` with `sabatierZone apexD dE`. What does **not** transfer, and
why the registry says "no edge": the scalars are unrelated — a ratio of ionic radii against a binding
free energy — and no map between them is delivered anywhere in the repository; the sharp conditions
have different contents (Goldschmidt's is an exact *radius window* for every band, Sabatier's is the
product condition `0 < alphaA * alphaB` on the two BEP slopes); and the two classifiers decide
different propositions, one by comparing squares of rationals (`Rat.zoneQ`) and the other by
comparing reals through `√2`. The lesson of N1/N2 repeats a third time in a new form: **the same
statement shape is not the same statement.**

**中文（N4：同样的"形状"，没有边）**：两个形状重合，本文件把它**登记**而非变现成一条边。(i) *对称带 =
偏离理想的绝对值有界*：Goldschmidt 的 G3 行 `conforms_symmetric_band_iff` 对**任意** `delta` 证明
`GoldschmidtConforms (1-δ) (1+δ) rA rB rO ↔ |rA - idealA rB rO| ≤ δ * idealAO rB rO`（无需 `0 ≤ δ`，
plan §3.1 第 2 条）；Sabatier 的 S1 定义 `NearOptimal tol apexD dE := |dE - apexD| ≤ tol` 是同一形状在
描述符轴上的读法。(ii) *标量对带的三分类器*：`GoldschmidtZone` 的 `goldschmidtZone lo hi t`（其
`tooLarge` 支的**精确**刻画是 `lo ≤ t ∧ hi < t`，因为级联先测 `t < lo`）对 `Sabatier.SZone` 的
`sabatierZone apexD dE`。**不传递**的原因恰好也是登记"无边"的理由：标量互不相关——离子半径之比对结合
自由能——且仓库里没有任何已交付的映射把两者连起来；锐利条件内容不同（Goldschmidt 是对任意带都精确的
**半径窗口**，Sabatier 是两条 BEP 斜率上的乘积条件 `0 < alphaA * alphaB`）；两个分类器判定的是不同的
命题，一个比较有理数的平方（`Rat.zoneQ`），另一个经 `√2` 比较实数。N1/N2 的教训以新形态第三次出现：
**同样的语句形状不等于同样的语句。**

---

## 3bis. Adjudicated conflation (class A1): the symmetry factor / 已裁决混同（A1 类）：对称因子

**English.** The non-relations of §3 say "similar shape, no edge". Class **A1** says something
stronger, and it is new with the seventh theory (`PhotoLean.SymmetryFactor`, delivered 2026-09-21):
**the literature treats two readings as interchangeable, and the kernel decides the identification
together with its exact validity boundary.** The pair is the electrochemical **symmetry factor** β
(Butler–Volmer, "usually both taken to be equal to 0.5" — a first-hand practice locus,
`theories/SymmetryFactor/LITERATURE.md` S1) against the **structural transfer coefficient** of the
two-parabola model, generalized here to *unequal* force constants `kr, kp`. The thermoneutral
crossing coordinate is `√kp/(√kr+√kp)`, and the verdict is the sharp equivalence

> `betaHalf_iff_equalForceConstants` : `BetaHalfReading kr kp ↔ kr = kp`  (for `0 < kr, 0 < kp`)

so the conflated reading holds **exactly** on the equal-curvature diagonal. Kernel witnesses:
`(1,4) ↦ 2/3 ≠ 1/2` (refuted, `betaHalf_falsified_by_unequal`), `(4,1) ↦ 1/3` (the direction
asymmetry — the crossing sits on the side of the *softer* well, a late transition state at **zero**
driving force when the product well is stiffer, `tsCoordZero_gt_half_iff_stiffProduct`). The IUPAC
Technical Report's printed warning — β deviates from 0.5 exactly when the two force constants
differ, and α "can by no means be assumed" (LITERATURE S2, pp. 255–257) — is thereby turned from
prose into a decided boundary.

**Why the conflation survives, decided too.** The equal-curvature diagonal is not a corner case but
the model every textbook draws (and Marcus's own declared *symmetrization* approximation, LITERATURE
S4). Two certificates tie the seventh node to the shared kernel there:
`symmetryFactor_tsCoordZero_eq_kernel` (`tsCoordZero lam lam = Kernel.tsCoord lam 0`) and
`symmetryFactor_tsCoordZero_eq_bepTransfer` (`= BEP.transfer lam 0`, extending the E1 chain), and
`betaHalf_holds_in_kernel` states that the conflated reading is a **theorem** throughout that
family. One row packages both halves — `symmetryFactor_conflation_falsified_and_holds_in_kernel`:
refuted at `(1,4)`, holds for every `0 < lam` on the diagonal. That is the whole adjudication: the
identification is neither a mistake nor a law, but a **special case with a machine-checked
boundary**.

**Honest scope.** The verdict is a statement **inside the declared model** (two harmonic surfaces,
classical crossing, thermoneutral `x = 0`); the *kinetic* reading (a derivative of the barrier at
general driving force) and the Leffler `α = q‡` identification *under asymmetry* are registered
non-goals (`theories/SymmetryFactor/plan.md` §1.3), the former needing analysis substrate
(METHOD.md §7 boundary). The instance rows decide **declared numbers**, not measured electrodes. S1
is a preprint modelling-review (a practice locus, not an authority recommendation) and is cited as a
pair with S2, never alone.

**中文（A1：已裁决混同）**：§3 的非关系说的是"形状相似、无边"。**A1** 类说的更强，且随第七个理论
（`PhotoLean.SymmetryFactor`，2026-09-21 交付）新增：**文献把两种读法当作可互换，而内核对这个等同
连同其精确有效边界作出裁决**。这一对是电化学**对称因子** β（Butler–Volmer，"通常都取 0.5"——一手
实践位点，LITERATURE S1）对双抛物面模型的**结构转移系数**（此处推广到**非等**力常数 `kr, kp`）。
热中性交叉坐标为 `√kp/(√kr+√kp)`，判决是锐利等价

> `betaHalf_iff_equalForceConstants`：`BetaHalfReading kr kp ↔ kr = kp`（`0 < kr, 0 < kp` 下）

即被混同的读法**恰好**在等曲率对角线上成立。内核见证：`(1,4) ↦ 2/3 ≠ 1/2`（被证伪，
`betaHalf_falsified_by_unequal`）、`(4,1) ↦ 1/3`（方向不对称——交叉点偏向**较软**的势阱，产物阱更硬时
在**零**驱动力下过渡态就偏晚，`tsCoordZero_gt_half_iff_stiffProduct`）。IUPAC 技术报告的印刷警告
——两力常数不等时 β 恰好偏离 0.5、α"绝不能被假定"（LITERATURE S2, pp.255–257）——由此从散文变成
被裁决的边界。

**混同为何长存，也被裁决**：等曲率对角线不是边角情形，而是每本教科书画的那个模型（也是 Marcus 自己
声明的*对称化*近似，LITERATURE S4）。两条证书把第七节点在該处钉到共享内核：
`symmetryFactor_tsCoordZero_eq_kernel`（`tsCoordZero lam lam = Kernel.tsCoord lam 0`）与
`symmetryFactor_tsCoordZero_eq_bepTransfer`（`= BEP.transfer lam 0`，延伸 E1 链），而
`betaHalf_holds_in_kernel` 说明被混同的读法在整个该家族里是**定理**。一行把两半打包——
`symmetryFactor_conflation_falsified_and_holds_in_kernel`：在 `(1,4)` 被证伪、在对角线上对每个
`0 < lam` 成立。这就是整个裁决：这个等同既非错误也非定律，而是**一个带机器检查边界的特例**。

**诚实范围**：判决是**声明模型内部**的陈述（两条谐振面、经典交叉、热中性 `x = 0`）；*动力学*读法
（一般驱动力下势垒的导数）与非对称下的 Leffler `α = q‡` 等同是登记的非目标（plan §1.3），前者需要
分析基质（METHOD.md §7 边界）。实例行判决的是**声明的数字**，不是实测电极。S1 是预印本建模综述
（实践位点，非权威推荐），与 S2 成对引用，绝不单引。

---

## 4. The quantifier shapes (prose) / 量词形态（正文讨论，非定理）

**English.** The three predicates have three different logical shapes, and this difference is *not*
itself a theorem — it is a modelling observation, recorded here rather than dressed up as one:

| predicate | shape | free parameters | what it can and cannot say |
|---|---|---|---|
| `HammondDescriptor lam` | two points, unrestricted | none beyond `lam` | exact monotonicity of a function; sharp condition `0 < lam` |
| `Marcus.InvertedDescriptor A lam kB T` | two points, restricted to the ray `lam < x₁` | `A, kB, T` (the sign of `A` and of `kB·T` genuinely changes the truth value — see N2) | formal monotonicity of a composed function; needs the separate positivity conjunct to pin the model (N2) |
| `BEP.EPConformsOnWindow lam tol a b` | continuum-uniform error bound on `Icc a b` | `tol`, window `a b` (two metrical parameters) | a quantitative approximation claim; monotone under window enlargement (`epConformsOnWindow_mono`) and in `lam` (`epConformsOnWindow_mono_lam`); sharp radius `epConformsOnWindow_iff_radius` |

Three honest corollaries of the table:

1. The window predicate is **not a two-point property**: no finite sample of driving forces can
   certify or refute it, which is exactly why BEP needed a defect law (`bepDefect = x²/(4λ)`) and a
   radius before it could be called sharp.
2. The three predicates are **not degrees of one statement**. What *is* theorem-shaped is the
   implication lattice pinned in §2 (E1–E7, O1–O3); the rest — "the tolerance window is a
   different kind of claim from a monotonicity statement" — is a choice of modelling language and
   is stated as such.
3. The only logical road between the window predicate and the structural predicate is the latter's
   positivity conjunct (O3). There is no bridge from the *error bound* itself to `HammondDescriptor`,
   and none is claimed.

**中文（量词形态）**：三条谓词的逻辑形态不同，这一差异**本身不是定理**，而是建模观察，如实记在此处
而非硬凑成定理：`HammondDescriptor` 是**无参、全域的两点单调性**；`Marcus.InvertedDescriptor` 是**带
(A,kB,T) 参数、限定在射线 `lam < x₁` 上的两点单调性**（`A` 与 `kB·T` 的**符号**确实会改变真值，见 N2）；
`BEP.EPConformsOnWindow` 是**窗口上的连续统一致误差界**，带两个度量参数（容差与窗口），对窗口扩大与
`lam` 单调（`epConformsOnWindow_mono`、`epConformsOnWindow_mono_lam`），其精确半径为 `2√(λ·tol)`。
三条推论：①窗口谓词**不是两点性质**——任何有限采样都既不能证实也不能证伪它，这正是 BEP 必须先有缺陷律
与半径才谈得上"锐利"的原因；②三者**不是同一陈述的不同强度**——真正呈定理形态的是 §2 钉住的蕴含格
（E1–E7、O1–O3），其余（"容差窗口与单调性陈述是不同种类的断言"）是建模语言的选择；③窗口谓词通往结构
谓词的**唯一**逻辑通道是后者的正性合取项（O3），从误差界本身出发没有桥，也不声称有。

---

## 5. What the extraction and the collection gained / 抽取与收集的增量

**English.** (i) The shared signature `Σ = {lam, x}` is now fixed **by kernel-level certificates**
rather than by naming discipline alone: the barrier/coordinate identity of the three
theories is a `rfl` certificate over one definition, so "same physical quantity, two names" is
mechanically decidable instead of conventional — a future theory that reuses the name `lam` with a
different meaning must fail to close its own certificate, and the check is one line rather than an
audit. **Scope of the mechanism (wording corrected 2026-09-21, review finding M10):** the pin is
mechanical for every theory that *writes* its certificates against the kernel; writing them is
itself still a discipline — there is no signature *type* (the first review's S1, an explicit
`structure` fixing Σ, is not implemented), and nothing forces a future theory to register a
certificate at all. "Fixed by types" would over-claim; "fixed by certificates, opt-in per theory"
is what is delivered.
(ii) The two *substantive* identities (E1, E2) were already proved rather than definitional, and
E3–E6 give the cross-theory content; E7 states the co-extensiveness of the two sharp conditions
(composition of two delivered theorems, counted as such). (iii) The non-relations N1–N2 are now
theorems: the relation graph states where the three readings come apart, not only where they agree.
(iv) The re-exports of §1, §2, §4, §5 of `Relations.lean` add **no mathematics** — by the
accounting rule of the review, they must not be counted as new results; their value is the
compile-time pin (a statement drift anywhere upstream makes the module fail to compile) and the
single readable inventory. (v) **Coverage note (honest)**: the three per-theory fidelity probes
glob only `PhotoLean/<Theory>/*.lean`, so they do **not** cover `Kernel.lean` or `Relations.lean`;
the statement authority of the two new modules is the compile-time re-export pin above (every
statement written out verbatim) plus the module docstrings, not a skeleton probe.

**中文（增量）**：①共享签名 `Σ = {lam, x}` 由**内核级证书**固定，而不再仅靠命名纪律：三个理论的
势垒/坐标同一性是"一份定义上的 `rfl` 证书"，因此"同一物理量两个名字"从约定变为**可机械判定**——未来的
第四个理论若复用 `lam` 名字却赋不同含义，将无法闭合自己的证书（检查成本是一行而非一次审计）。
**机制的适用范围（2026-09-21 评审修正轮 M10 修订措辞）**：钉合对**写了证书**的理论是机械的，而
"写证书"本身仍是纪律——仓库中不存在签名**类型**（首轮审查的 S1 建议、固定 Σ 的显式 `structure`
未实现），也没有任何机制强迫未来的理论登记证书。"由类型固定"是过度声称；"由证书固定、逐理论
自愿登记"才是已交付的事实。②两条**实质**同一性（E1、E2）本来就被刻意做成"可证明而非定义性"，
E3–E6 给出跨理论内容，E7 把两个锐利条件的同外延性写成命题（是两条已交付定理的**复合**，按复合记账）。
③"非关系" N1–N2 成为定理：关系图不仅登记三者在哪里一致，也登记它们在哪里分道扬镳。④`Relations.lean`
中 §1、§2、§4、§5 的复用条目**不含新数学**——按审查的记账规则，它们不得计为新结果；其价值在编译期
钉死（上游任何语句漂移都会使模块编译失败）与"一处可读的清单"。⑤**覆盖范围备注（诚实）**：三个逐理论
保真探针各自只 glob `PhotoLean/<理论>/*.lean`，**不覆盖** `Kernel.lean` 与 `Relations.lean`；这两个新
模块的语句权威是上述**编译期复用钉子**（每条语句逐字写出）与模块 docstring，而不是骨架探针。

**English (second batch, 2026-09-21).** (vi) Two **composition** edges are now on the graph
(§2.4): the Kasha → Marcus edge is the first edge in this repository whose premise is a *modelling
identification* rather than a mathematical hypothesis, and it is registered with the premise
attached; the Sabatier → BEP edge carries the geometric reading of the BEP defect law (each tangent
lies below its parabola, so the linear volcano underestimates the barrier pointwise). (vii) The
look-alike cluster N3 is the second-batch form of the accounting rule: one shared predicate
(`Sabatier.AntiVolcanoDescriptor`) instantiated at the Marcus rate, plus three differences stated
as theorems. (viii) The **no-edge registry** (§2.5) makes the graph complete in the "every theory
sits on it" sense — the checkable form of `AGENTS.md` iron rule 8 item ②. (ix) **Accounting of the
second batch**: `Relations.lean` grew from 28 to 46 declarations; of the 18 new rows, 10 are
verbatim re-exports (K1–K3, S1–S4 — counting declarations, S2 and S4 carry two each — and the
supporting row `marcusIC_pos`, which the enumeration in the first draft of this sentence omitted;
the count of 10 was already correct) and 2 are certificates (`kernel_marcusIC`, C1) — twelve rows
that add no mathematics — while 6 are proved here (C2, C3a, C3b, C4, C5a, C5b), of which C3b and
C5b are assemblies of C3a and C2 respectively. The batch's genuinely new mathematical content is
therefore four rows: the uniqueness half of C2, C3a, C4 and C5a.

**中文（第二批增量，2026-09-21）**：⑥关系图新增两条**组合边**（§2.4）：Kasha → Marcus 是本仓库第一条
以**建模同一性**（而非数学假设）为前提的边，登记时把该前提一并带上；Sabatier → BEP 携带 BEP 缺陷律的
几何读法（切线在抛物线之下 ⇒ 线性火山逐点低估势垒）。⑦形似实异簇 N3 是记账规则的第二批形态：一个共享
谓词（`Sabatier.AntiVolcanoDescriptor`）在 Marcus 速率上的实例化，加上三条以定理形式陈述的差异。
⑧**无边登记**（§2.5）使关系图在"每个理论都在图上"的意义下完整——这正是 `AGENTS.md` 铁律 8 第 ② 项的
可检查形态。⑨**第二批记账**：`Relations.lean` 由 28 条增至 46 条；18 条新增中 10 条是逐字 re-export
（K1–K3、S1–S4——按声明计 S2 与 S4 各含两条——及支撑行 `marcusIC_pos`；本句初稿的枚举漏掉了
`marcusIC_pos` 之名，总数 10 原本就对，2026-09-21 评审修正轮补名）、2 条是证书
（`kernel_marcusIC`、C1），共 12 条不含新数学；6 条在本模块证明
（C2、C3a、C3b、C4、C5a、C5b），其中 C3b 与 C5b 分别是 C3a 与 C2 的组装。故本批**真正的新数学内容是
四行**：C2 的唯一性半边、C3a、C4、C5a。

**English (third batch, 2026-09-21 — the H1 crossing).** (x) The seventh theory (`SymmetryFactor`)
adds the graph's first **adjudicated conflation** (§3bis, class A1): `Relations.lean` grew from 46
to **50** declarations, and **all four new rows are re-exports/certificates that add no mathematics
here** — two tie-back certificates (`symmetryFactor_tsCoordZero_eq_kernel`,
`symmetryFactor_tsCoordZero_eq_bepTransfer`: the equal-curvature specialization to `Kernel.tsCoord`
and `BEP.transfer`) and two re-exports of the delivered verdict (`symmetryFactor_betaHalf_iff`,
`symmetryFactor_conflation_falsified_and_holds_in_kernel`). The genuinely new mathematics — the
closed form `√kp/(√kr+√kp)`, its uniqueness on `[0,1]`, and the sharp verdict
`BetaHalfReading kr kp ↔ kr = kp` with the witnesses `(1,4) ↦ 2/3`, `(4,1) ↦ 1/3` — lives in
`PhotoLean/SymmetryFactor/*`, not in the relation module, exactly as the accounting rule requires.
(xi) The seventh node's remaining pairs are in the no-edge registry (§2.5): edges to
Marcus/Hammond/BEP, no edge to Kasha/Sabatier/Goldschmidt, with the measured import fact. The
A1 class is itself the increment: the graph could previously say "these look alike but no edge
holds" (N-rows); it can now say "**the literature treats these as the same, and here is the kernel's
boundary of that sameness**" — a negative adjudication with a first-hand practice locus attached.

**中文（第三批增量，2026-09-21——H1 跨越）**：⑩第七个理论（`SymmetryFactor`）新增本图第一条
**已裁决混同**（§3bis，A1 类）：`Relations.lean` 由 46 条增至 **50** 条，且**四条新增全是不含本模块
新数学的 re-export/证书**——两条回接证书（`symmetryFactor_tsCoordZero_eq_kernel`、
`symmetryFactor_tsCoordZero_eq_bepTransfer`：等曲率特化到 `Kernel.tsCoord` 与 `BEP.transfer`）与
两条已交付判决的 re-export（`symmetryFactor_betaHalf_iff`、
`symmetryFactor_conflation_falsified_and_holds_in_kernel`）。真正的新数学——闭式 `√kp/(√kr+√kp)`、
其在 `[0,1]` 上的唯一性、锐利判决 `BetaHalfReading kr kp ↔ kr = kp` 连同见证 `(1,4) ↦ 2/3`、
`(4,1) ↦ 1/3`——全在 `PhotoLean/SymmetryFactor/*`，不在关系模块内，正如记账规则所要求。⑪第七节点
其余各对已入无边登记（§2.5）：与 Marcus/Hammond/BEP 有边，与 Kasha/Sabatier/Goldschmidt 无边，附
实测 import 事实。A1 类本身就是增量：此前图只能说"形似而无边"（N 行），现在能说"**文献把二者当
同一个，而这是内核对'同一个'的边界判决**"——一条附带一手实践位点的否定性裁决。

---

## 6. Honest boundaries / 诚实边界

**English.** 1. **Scope of the substrate.** Everything about the two-parabola family (the Marcus
rate, the Hammond trend, the BEP line law and the compositions of §2.4) is a statement *inside* the
equal-curvature two-parabola model; the newer theories carry their own declared premises (Kasha: the
finite ladder, the exponential-race branching, the time-integrated yields; Sabatier: the
descriptor-axis optimisation with `Ea = max` of two branches; SymmetryFactor: the unequal-curvature
generalization **at thermoneutrality and in its structural reading** — the kinetic reading is a
registered non-goal, §3bis). The BEP instance layer actually
**refutes** four first-hand literature families as equal-curvature two-parabola families while
their affine slopes conform — the graph is a graph of *declared* models, and it was empirically
bounded by that theory's own instance work.
2. **Degenerate curvature.** `lam = 0` values carried by `x / 0 = 0` are a formal convention of the
model (documented upstream at every occurrence); no relation above depends on it: the certificates
are body-level, and the substantive equivalences carry their `lam ≠ 0` / `0 < lam` premises
explicitly. The seventh theory inherits the same convention with a new face: totalized `Real.sqrt`
makes `√(negative) = 0`, flagged wherever consumed (and the reason two of its rows are
premise-free, its plan §3.1). 3. **No theory-equivalence claim.** The edges relate *statements about
named models*; they are not a claim that the delivered theories are equivalent as theories, nor that
any one of them is derivable from another — and the A1 row is a verdict about two *readings inside
one declared model*, not about electrode kinetics. The composition edges (§2.4) are one-way in that
sense too: they use an older theory as a component, under a stated premise. 4. **Prose vs theorem.**
§4 is explicitly prose; the other sections are theorem-backed. 5. **Accounting.** First batch: 28 = 8 certificates +
6 equivalences + 3 entailments + 4 reuse rows + 4 ledger rows + 3 new theorems, with four
declarations proved in that task (O3 in §2.2 and the three of §3/§6). Second batch:
46 = 28 + 18, of which 10 verbatim re-exports and 2 certificates add no mathematics and 6 are
proved here — four rows of genuinely new content, as §5 (ix) records. Third batch (the H1 crossing):
50 = 46 + 4, and **all four** are re-exports/certificates (two equal-curvature tie-backs to
`Kernel.tsCoord`/`BEP.transfer`, two re-exports of the delivered A1 verdict) — the seventh theory's
mathematics lives entirely in `PhotoLean/SymmetryFactor/*`, none in the relation module. 6. **Verification record
(first batch).** The delivered state was independently gated by a read-only verifier: build with
zero warnings, strict scan `clean`, all 30 declarations of `Kernel.lean` + `Relations.lean` at
`[propext, Classical.choice, Quot.sound]`, and the additivity audit (the only change inside the
three theory directories is the scoping of one linter option in `PhotoLean/Marcus/Barrier.lean`;
comment-stripped code byte-identical once those three scoped option lines are removed as well).
7. **The Kasha edge is conditional.** `hic` is a modelling identification, not a theorem: the edge
states what follows *if* the `S₂ → S₁` internal conversion is a Marcus process. Nothing here claims
that it is one. 8. **What an absent edge means.** §2.5 registers the absence of an edge as a fact
about the *graph* — the import structure plus the modelling vocabulary — not as a claim that no
physical connection between the two phenomena could exist. The reason is recorded per pair so that
it can be re-examined.

**中文（诚实边界）**：①**基质的范围**——凡属双抛物面家族的内容（Marcus 速率、Hammond 趋势、BEP 线性律
与 §2.4 的组合）都是等曲率双抛物模型**内部**的陈述；较新的理论各自携带自己的声明前提（Kasha：有限
阶梯、指数竞争分支、时间积分产额；Sabatier：描述符轴上的优化、`Ea = max` 两支；SymmetryFactor：
**热中性、结构读法**下的非等曲率推广——动力学读法是登记的非目标，§3bis）。BEP 的实例层实测把四个
一手文献族**证伪**为等曲率双抛物族（尽管其仿射斜率符合）——关系图是**声明的模型**之图，其边界由该理论
自己的实例工作经验性地划定。②**退化曲率**——`lam = 0` 处依赖除零约定 `x / 0 = 0` 的取值是模型的形式
约定（上游每处均已注明），本文件没有一条关系依赖它：证书是定义体层面的，实质等价全部显式携带
`lam ≠ 0` / `0 < lam` 前提。③**不声称理论等价**——各条边关联的是**具名模型上的命题**，不是"五个理论
作为理论等价"，也不是"由谁推出谁"；§2.4 的组合边在此意义上同样是单向的：它们把较老的理论当作组件使用，
且前提写明。④**正文与定理分工**——§4 明确是正文讨论，其余各节的表格有定理支撑；§3bis 的 A1 裁决
正文有定理支撑（`betaHalf_iff_equalForceConstants` 等），其"实践位点"是文献记录而非定理。⑤**记账**——第一批：
28 = 8 证书 + 6 等价 + 3 单向 + 4 复用 + 4 清单行 + 3 新定理，该任务**实际作证** 4 条（§2.2 的 O3 与
§3/§6 的三条）；第二批：46 = 28 + 18，其中 10 条逐字 re-export 与 2 条证书不含新数学、6 条在本模块证明
——真正的新内容四行，见 §5 第 (ix) 条；第三批（H1 跨越）：50 = 46 + 4，**四条全是** re-export/证书
（两条等曲率回接到 `Kernel.tsCoord`/`BEP.transfer`、两条 A1 判决的 re-export）——第七个理论的数学全在
`PhotoLean/SymmetryFactor/*`，关系模块内无新数学。⑥**验证记录（第一批）**——交付状态由只读 verifier 独立跑门：
零警告构建、严格扫描 `clean`、`Kernel.lean` + `Relations.lean` 全部 30 条声明公理恰为
`[propext, Classical.choice, Quot.sound]`，加性审计通过（三个理论目录内唯一改动是
`PhotoLean/Marcus/Barrier.lean` 一个 linter 选项的作用域收窄；剥注释并剔除那三行作用域行后，代码逐字节相同）。
⑦**Kasha 边是条件性的**——`hic` 是建模同一性而非定理：该边陈述的是"**若** `S₂ → S₁` 内转换是 Marcus
过程，则如何"，不声称它确实是。⑧**"无边"的含义**——§2.5 登记的是关于**关系图**（依赖结构 + 建模词汇）
的事实，不是"两种现象之间不可能存在物理联系"的断言；理由逐对写明，以便复查。

---

## 7. Reproduction / 复核

```bash
proofs/scripts/lake build
proofs/scripts/check.sh --strict
# first batch — the non-relations
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.hammond_trend_exact_bep_law_inexact
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.hammond_sharp_iff_marcus_sharp
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.rate_predicate_satisfiable_without_positive_curvature
# second batch — the composition edges and the look-alike cluster
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.kernel_marcusIC
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.kashaWithin_one_marcus
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.marcus_rate_eq_activity
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.marcusRate_antiVolcanoDescriptor
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.marcus_secant_at_optimum
# third batch — the A1 adjudicated conflation (§11)
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.symmetryFactor_betaHalf_iff
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.symmetryFactor_conflation_falsified_and_holds_in_kernel
proofs/scripts/axioms.sh PhotoLean.SymmetryFactor.Sharp PhotoLean.SymmetryFactor.betaHalf_iff_equalForceConstants
proofs/scripts/axioms.sh PhotoLean.SymmetryFactor.Instances PhotoLean.SymmetryFactor.inst_conflation_falsified
# statement calibration probes (placeholders on purpose; exit 0 with warnings)
proofs/scripts/lake env lean theories/Marcus/probes/relations-b2-statement-skeleton.lean
proofs/scripts/lake env lean theories/SymmetryFactor/probes/SymmetryFactor-statement-skeleton.lean
# fidelity: 51 / 191 / 102 / 151 / 132 / 139 / 35 word-for-word, 0 differences
python3 theories/Marcus/probes/marcus-fidelity.py
python3 theories/BEP/probes/bep-fidelity.py
python3 theories/hammond/probes/hammond-fidelity.py
python3 theories/BEP/probes/bep-fidelity.py --theory kasha
python3 theories/BEP/probes/bep-fidelity.py --theory Sabatier
python3 theories/BEP/probes/bep-fidelity.py --theory goldschmidt
python3 theories/BEP/probes/bep-fidelity.py --theory SymmetryFactor
```

**English.** The last fidelity line is the seventh theory (SymmetryFactor, 35 authority
declarations, all delivered: `delivered, word-for-word: 35`, `not delivered yet: 0`,
`signature differences: 0`); the sixth (Goldschmidt, 139) is registered through the no-edge
registry rather than by a relation edge (§2.5, §3 N4), while the seventh enters through the A1
adjudicated conflation (§3bis, §11). Each `axioms.sh` call must print
`verdict: PASS (only mathlib infrastructure axioms)`; the seven fidelity probes must report 0
signature differences (51, 191, 102, 151, 132, 139, 35); the calibration probes compile with
placeholders and no errors. The whole inventory is in `PhotoLean/Relations.lean` §1–§11.
(The English half said "five probes" and omitted 139 until the 2026-09-21 review-fix round,
finding M8 — the Chinese half and the command block above were already correct; the seventh
probe, 35, was added with the H1 crossing.)

**中文**：最后一条保真命令是第七个理论（SymmetryFactor，权威 35 条声明、全部交付：
`delivered, word-for-word: 35`、`not delivered yet: 0`、`signature differences: 0`）；第六个
（Goldschmidt，139 条）经**无边登记**而非关系边接入（§2.5、§3 N4），第七个则经 A1 已裁决混同接入
（§3bis、§11）。上述每条 `axioms.sh` 必须打印
`verdict: PASS (only mathlib infrastructure axioms)`；七个保真探针必须报告 0 签名差异
（51 / 191 / 102 / 151 / 132 / 139 / 35——Kasha 的 151 是 2026-09-21 评审修正轮之后的权威计数：
`kashaDescriptor_nonvacuous` 语句强化 + 新增 `perLevel_ic_ge_rad_insufficient`，见
`theories/kasha/plan.md` §3.1）；标定探针以占位编译通过、无 error。
完整清单见 `PhotoLean/Relations.lean` §1–§11。

---

## 8. The photophysics batch (2026-09-22/23): nine nodes, two new adjudication classes / 光物理批次：九个节点、两个新裁定类

**English.** The fourth batch adds nine theories in three groups — the rate-cascade group
(KashaVavilov, SternVolmer, QuantumYield, FluorPhos) reusing the Kasha ladder by import, the
two-parabola group (EnergyGapLaw, StokesShift, ICvsISC) carrying kernel-pinned copies, and the
geometric/spectroscopic group (Forster, Einstein). Its machine-checked companion is
`PhotoLean/Relations.lean` §12–§16 (23 new rows). The graph gains two adjudication classes
beyond A1: **A2 (adjudicated independence)** — Kasha vs Kasha–Vavilov: pointwise independent in
both directions (witnesses inside the lossy regime), coinciding exactly under the closed
quantification with a loss channel, separated in the lossless corner (§13); and **A3
(identifiability)** — static vs dynamic quenching: the intensity-only Stern–Volmer observation is
non-injective on the two-mechanism space (matched parameters give pointwise-identical curves at
every concentration), the lifetime channel is the exact discriminator, and upward curvature is
the positive coexistence witness (§14). The batch's compositions all run through one algebraic
spine — QuantumYield (§15): the ladder's `radBranch`, the Stern–Volmer dilution, the
fluorescence/phosphorescence cascade, the FRET added-donor channel and the Einstein radiative
anchor are all quantum-yield identities; the two-parabola group composes through the kernel
certificates (§12) plus two new rows (the energy-gap ordering of the Kasha IC rates; the
Stokes/EGL barrier–window boundary). The refuted first forms of SS-C9 and FP-C5 are delivered as
counterexample-witness theorems in their theories (`invertedCorner_firstForm_refuted`,
`fpC5_firstForm_refuted`) — negative results as first-class citizens. Every remaining pair is
registered in the extended no-edge registry (§16) with its reason.

**中文。** 第四批以三组加入九个理论——速率级联组（KashaVavilov、SternVolmer、QuantumYield、
FluorPhos）以导入复用 Kasha 阶梯；双抛物面组（EnergyGapLaw、StokesShift、ICvsISC）携带内核
钉住的副本；几何/谱学组（Forster、Einstein）。其机器检查对应物是
`PhotoLean/Relations.lean` §12–§16（23 条新行）。图在 A1 之外获得两个新裁定类：
**A2（已裁决独立性）**——Kasha 对 Kasha–Vavilov：双向逐点独立（见证在有损区内）、闭合量化
加损失通道下恰重合、无损角分离（§13）；**A3（可辨识性）**——静态对动态猝灭：仅强度的
Stern–Volmer 观测在两机制空间上非单射（匹配参数下曲线在每个浓度逐点相同）、寿命通道是精确
判别器、向上弯曲是共存正见证（§14）。批次的组合边都经过同一条代数脊柱——QuantumYield（§15）：
阶梯的 `radBranch`、Stern–Volmer 稀释、荧光/磷光级联、FRET 加通道与 Einstein 辐射锚都是量子
产额恒等式；双抛物面组经内核证书（§12）加两条新行（Kasha IC 速率的能隙排序；Stokes/EGL
势垒–窗口边界）组合。SS-C9 与 FP-C5 的被反驳初式以反例见证定理交付于各自理论
（`invertedCorner_firstForm_refuted`、`fpC5_firstForm_refuted`）——负结果是一等公民。
其余全部配对登记于扩展的无边注册表（§16），各附理由。


---

## 9. The seventeenth node: RACI (integration of the ChemLean work) / 第十七个节点：RACI（纳管 ChemLean 工作）

**English.** The seventeenth theory — Restricted Access to a Conical Intersection (RACI), the
accepted mechanism of aggregation-induced emission — is ported from the independent ChemLean
repository (same Lean 4.17.0 / mathlib v4.17.0 toolchain) and enters the graph through
`Relations.lean` §17. Its machine edges: the composition certificate `RACI.quantumYield =
QuantumYield.yieldOf ![kr, knr] 0` (the enhancement is the dilution theorem run backwards); the
energy-gap-law link (`log (barrierRate A β B) = log A − β·B`, the affine gap law exactly); the
ICvsISC composition note (`fcBarrier lam lam = 0`, the maximal-rate point of the FC competition);
and the Marcus look-alike (the classical surfaces really cross at `tsCoord` — a single-condition
degeneracy, the classical model having no coupling coordinate — vs the CI's two-condition
codimension-2 degeneracy; different objects, the registry records why no theorem transfers). The
named admissible model (`torsionH`) and the named non-model (`nonModelNoCI`, an everywhere-empty
conical set) sit in `PhotoLean/RACI/Instances.lean`, with the ℚ discriminant decision layer in
`RatModel.lean`. All remaining pairs are in the §17 no-edge registry with reasons.

**中文.** 第十七个理论——受限锥形交叉（RACI，聚集诱导发射的公认机制）——自独立的 ChemLean
仓库（同一 Lean 4.17.0 / mathlib v4.17.0 工具链）移植，经 `Relations.lean` §17 接入关系图。
其机器边：组合证书 `RACI.quantumYield = QuantumYield.yieldOf ![kr, knr] 0`（增强即稀释定理
的反向读法）；能隙律链接（`log (barrierRate A β B) = log A − β·B`，恰为仿射能隙律）；
ICvsISC 组合注记（`fcBarrier lam lam = 0`，FC 竞争的最大速率点）；以及 Marcus 形似注
（经典两曲面在 `tsCoord` 真实相交——单条件简并，经典模型无耦合坐标——而 CI 是双条件余维 2
简并；对象不同，登记处记录为何无定理迁移）。命名容许模型（`torsionH`）与命名非模型
（`nonModelNoCI`，锥形集处处为空）位于 `PhotoLean/RACI/Instances.lean`，ℚ 判别式决策层在
`RatModel.lean`。其余全部配对在 §17 无边登记中附理由登记。
