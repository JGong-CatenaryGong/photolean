# theories/RELATIONS.md — three principles, one quadratic object

> **Status.** This is the discussion draft of the relation graph of the three delivered theories
> (Marcus inverted region, Hammond postulate, Bell–Evans–Polanyi principle). Its machine-checked
> companion is `PhotoLean/Relations.lean` (28 declarations) over the shared kernel
> `PhotoLean/Kernel.lean` (6 definitions + 2 theorems); every claim below that names a Lean
> theorem is backed by a declaration that compiles and whose `#print axioms` output is
> `[propext, Classical.choice, Quot.sound]`. It is written in the bilingual style of the
> `RESULTS.md` deliverables (English original followed by its Chinese rendering); the language
> policy and the freeze of the historical `.en.md` mirrors are recorded in `README.md`.
>
> **Provenance.** The bridge inventory of the 2026-09-20 review record (`review/REVIEW.md` §3.1,
> 13 rows / 16 theorems in the delivered modules) is the input document of this task; it is
> preserved in the repository as an input record (committed alongside this consolidation, not as a
> delivered artifact of the three theories). This file is the frozen output: the inventory
> collected into one module, extended with the non-relations of §3, and written up here.
>
> **中文（状态与来源）**：本文件是三个已交付理论（Marcus 反转区、Hammond 假说、Bell–Evans–Polanyi
> 原理）**关系图**的讨论稿。可机器检查的对应物是 `PhotoLean/Relations.lean`（28 条声明）与共享内核
> `PhotoLean/Kernel.lean`（6 定义 + 2 定理）；下文凡点名 Lean 定理之处，均有可编译声明支撑，且其
> `#print axioms` 输出恰为 `[propext, Classical.choice, Quot.sound]`。本文按各理论 `RESULTS.md` 的
> 双语排版书写（英文原文后紧跟中文对照）；语言政策与历史 `.en.md` 镜像的冻结见 `README.md`。
> 2026-09-20 审查记录（`review/REVIEW.md` §3.1，13 行 / 16 条定理）是本次任务的输入文档，已作为
> **输入记录**随本次固化一并提交（它不是三个理论的交付物）；本文件是冻结后的产出：清单收敛到一个
> 模块、补上 §3 的"非关系"，并在本文中给出完整讨论。

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

**English.** (i) The shared signature `Σ = {lam, x}` is now fixed **by types and kernel-level
certificates** rather than by naming discipline: the barrier/coordinate identity of the three
theories is a `rfl` certificate over one definition, so "same physical quantity, two names" is
mechanically decidable instead of conventional — a future theory that reuses the name `lam` with a
different meaning must fail to close its own certificate, and the check is one line rather than an
audit.
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

**中文（增量）**：①共享签名 `Σ = {lam, x}` 由**类型与内核级证书**固定，而不再靠命名纪律：三个理论的
势垒/坐标同一性是"一份定义上的 `rfl` 证书"，因此"同一物理量两个名字"从约定变为**可机械判定**——未来的
第四个理论若复用 `lam` 名字却赋不同含义，将无法闭合自己的证书（这正是 S1 建议的"从纪律升级为类型"，
现在检查成本是一行而非一次审计）。②两条**实质**同一性（E1、E2）本来就被刻意做成"可证明而非定义性"，
E3–E6 给出跨理论内容，E7 把两个锐利条件的同外延性写成命题（是两条已交付定理的**复合**，按复合记账）。
③"非关系" N1–N2 成为定理：关系图不仅登记三者在哪里一致，也登记它们在哪里分道扬镳。④`Relations.lean`
中 §1、§2、§4、§5 的复用条目**不含新数学**——按审查的记账规则，它们不得计为新结果；其价值在编译期
钉死（上游任何语句漂移都会使模块编译失败）与"一处可读的清单"。⑤**覆盖范围备注（诚实）**：三个逐理论
保真探针各自只 glob `PhotoLean/<理论>/*.lean`，**不覆盖** `Kernel.lean` 与 `Relations.lean`；这两个新
模块的语句权威是上述**编译期复用钉子**（每条语句逐字写出）与模块 docstring，而不是骨架探针。

---

## 6. Honest boundaries / 诚实边界

**English.** 1. **One model, equal curvature.** Everything above is a statement *inside* the
equal-curvature two-parabola model (registered as a model premise in the three plans). The BEP
instance layer delivered by that theory actually **refutes** four first-hand literature families as
equal-curvature two-parabola families while their affine slopes conform — i.e. the relation graph
is a graph of *this* substrate, and it was empirically bounded by that theory's own instance work.
2. **Degenerate curvature.** `lam = 0` values carried by `x / 0 = 0` are a formal convention of the
model (documented upstream at every occurrence); no relation above depends on it: the certificates
are body-level, and the substantive equivalences carry their `lam ≠ 0` / `0 < lam` premises
explicitly. 3. **No theory-equivalence claim.** E1–E7 relate *statements about one model*; they are
not a claim that the three theories are equivalent as theories, nor that any of them is derivable
from another. 4. **Prose vs theorem.** §4 is explicitly prose; §2's tables are theorem-backed. 5.
**Re-export accounting.** The count 28 = 8 certificates + 6 equivalences + 3 entailments + 4 reuse
rows + 4 ledger rows + 3 new theorems; the declarations *proved* in this task are four — O3 in §2.2
and the three of §6 — and among those, E7 is itself a composition of two delivered sharp theorems
(§2.1). The other 24 are certificates and ledger rows. 6. **Verification record.** The delivered
state was independently gated by a read-only verifier: build with zero warnings, strict scan
`clean`, all 30 declarations of `Kernel.lean` + `Relations.lean` at
`[propext, Classical.choice, Quot.sound]`, and the additivity audit (the only change inside the
three theory directories is the scoping of one linter option in `PhotoLean/Marcus/Barrier.lean`;
comment-stripped code byte-identical once those three scoped option lines are removed as well).

**中文（诚实边界）**：①**单一模型、等曲率**——以上全部是等曲率双抛物模型**内部**的陈述（该模型前提登记
在各理论 plan 中）；BEP 的实例层实测把四个一手文献族**证伪**为等曲率双抛物族（尽管其仿射斜率符合），
即关系图是这个**基质**上的图，且其边界由该理论自己的实例工作经验性地划定。②**退化曲率**——`lam = 0`
处依赖除零约定 `x / 0 = 0` 的取值是模型的形式约定（上游每处均已注明），本文件没有一条关系依赖它：证书
是定义体层面的，实质等价全部显式携带 `lam ≠ 0` / `0 < lam` 前提。③**不声称理论等价**——E1–E7 关联的是
**同一模型上的命题**，不是"三个理论作为理论等价"，也不是"由谁推出谁"。④**正文与定理分工**——§4 明确
是正文讨论，§2 的表格有定理支撑。⑤**复用记账**——28 = 8 证书 + 6 等价 + 3 单向 + 4 复用 + 4 清单行 +
3 新定理；本任务**实际作证**的是 4 条：§2.2 的 O3 与 §6 的 3 条，其中 E7 本身是两条已交付锐利定理的
**复合**（§2.1）；其余 24 条是证书与清单。⑥**验证记录**——交付状态由只读 verifier 独立跑门：零警告构建、
严格扫描 `clean`、`Kernel.lean` + `Relations.lean` 全部 30 条声明公理恰为
`[propext, Classical.choice, Quot.sound]`，加性审计通过（三个理论目录内唯一改动是
`PhotoLean/Marcus/Barrier.lean` 一个 linter 选项的作用域收窄；剥注释并剔除那三行作用域行后，代码逐字节相同）。

---

## 7. Reproduction / 复核

```bash
proofs/scripts/lake build
proofs/scripts/check.sh --strict
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.hammond_trend_exact_bep_law_inexact
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.hammond_sharp_iff_marcus_sharp
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.rate_predicate_satisfiable_without_positive_curvature
python3 theories/{Marcus,BEP,hammond}/probes/*-fidelity.py   # 51 / 191 / 102 word-for-word, 0 differences
```

**English.** Each of the three `axioms.sh` calls must print
`verdict: PASS (only mathlib infrastructure axioms)`; the three fidelity probes must report 0
signature differences (51, 191, 102). The whole inventory is in
`PhotoLean/Relations.lean` §1–§6.

**中文**：上述三条 `axioms.sh` 必须各自打印 `verdict: PASS (only mathlib infrastructure axioms)`；
三个保真探针必须报告 0 差异（51 / 191 / 102）。完整清单见 `PhotoLean/Relations.lean` §1–§6。
