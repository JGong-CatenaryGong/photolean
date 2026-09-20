# theories/Sabatier/RESULTS.md — the Sabatier principle (volcano plot), formalized in Lean

> The single bilingual deliverable of the Sabatier theory: every section carries the English original
> immediately followed by its Chinese rendering (contract `proofs/ENGINE.yml`, language policy in
> `proofs/ENGINE.md` §1.5). The human request had three parts — (①) turn the Sabatier principle into a
> formal description, (②) prove the description / find the exact conditions under which it holds,
> (③) plug instances in and decide whether each one conforms — answered in §2, §3 and §4 below.
> Every number in this file is a value measured from the delivered tree (module and line counts,
> declaration counts, fidelity numbers, `#print axioms` footprints, commit counts), or is explicitly
> labelled as *reported* by another agent, or is arithmetic on a source's printed number (the
> literature rows). No number is a plan target.
>
> 本文件是 Sabatier 理论的唯一双语交付物：每节英文原文后紧跟中文对照。人类需求分三部分 ——
> ①把萨巴蒂尔原则转化为形式化描述、②证明该描述并找出其精确成立条件、③代入实例判断是否符合 ——
> 分别在下面 §2、§3、§4 答复。本文件中的每个数字，或为交付树实测值（模块与行数、声明数、逐字一致数、
> `#print axioms` 足迹、提交数），或明确标注为*报告值*，或为对文献印刷数字的算术（实例行）；
> 没有任何数字是计划目标。

---

## 1. Executive summary

**English.** Six Lean modules under `PhotoLean/Sabatier/` — `Basic.lean` (S1, the description layer),
`Criterion.lean` (S2, the laws), `Sharp.lean` (S3, the exact conditions and their sharpness),
`Compose.lean` (S4, the two-parabola / cross-theory form), `RatModel.lean` (S5a, the computable
rational decision layer) and `Instances.lean` (S5b, the instance verdicts) — **2 133 lines** (`wc -l PhotoLean/Sabatier/*.lean`;
measured after the last source-touching commit, `03a0069`; the closeout commits that follow touch no
source file, so the number is stable at this file's revision)
containing **134 public declarations: 107 theorems and 27 definitions/inductives** (26 `def` + 1
`inductive`), plus 36 private helper lemmas. The statement authority
`theories/Sabatier/probes/sabatier-statement-skeleton.lean` carries **132** of them (105 theorems +
27 definitions/inductives); the remaining 2 are auxiliary theorems of the description layer
(`branchDown_le_branchUp_of_apex_le`, `branchUp_le_branchDown_of_le_apex`). **Fidelity: 132/132 authority rows word for word, signature
differences 0** (`python3 theories/BEP/probes/bep-fidelity.py --theory Sabatier`, per milestone
30/19/11/13/21/38 for S1/S2/S3/S4/S5a/S5b). **All 107 theorems are kernel-complete: zero unproved
placeholders, zero custom axioms** (the strict scan is clean; one-shot `#print axioms` over all 107
theorems gives the contract's footprint `[propext, Classical.choice, Quot.sound]` for 106 of them and
the subset `[propext]` for one, `sabatierZoneQ_eq_optimal_iff`). **71 commits touch
`PhotoLean/Sabatier/`** (measured at `03a0069`; re-measure with
`git log --oneline -- PhotoLean/Sabatier/ | wc -l`), message `feat(S<k>): <lemma>` — one lemma (or
one instance row group) per commit for S2/S3/S4/S5a/S5b; S1 was delivered as one grouped per-module
commit and S5b as twelve row-group commits, both registered as deviations on the board. Counts in
this file are pinned to the revision named beside them: a count that is not pinned goes stale
silently (verifier run 3, V2–V4).

**The one-sentence result.** In a two-branch Brønsted–Evans–Polanyi model `Ea(dE) = max (alphaA·dE +
betaA) (betaB − alphaB·dE)` of a two-step catalytic cycle, the **Sabatier description** — the
effective barrier has a *unique global minimum* at the apex `dE* = (betaB − betaA)/(alphaA + alphaB)`,
so the activity `exp(−Ea/k_BT)` has a *unique maximum* there — holds **iff `0 < alphaA · alphaB`**,
i.e. iff the two branches penalize opposite ends of the descriptor axis (one grows with `dE`, the
other falls). Under the physical orientation (`0 < alphaA`, `0 < alphaB` — one branch per end,
exactly the literature's opposite-sign-branch picture) the description holds unconditionally; a
zero slope degenerates the apex into a half-line plateau and equal-signs-twice destroys the interior
optimum altogether, and both failure modes are delivered with kernel witnesses. The tolerance form
of "not too strong, not too weak" is quantitative: within `tol` of the apex the barrier exceeds the
pass height by at most `max(alphaA, alphaB)·tol`.

**中文（摘要）**：`PhotoLean/Sabatier/` 下六个 Lean 模块（S1 描述层、S2 定律层、S3 精确条件与其紧性、
S4 两抛物线/跨理论形式、S5a 可计算有理判定层、S5b 实例判定层），共 **2 133 行**（`wc -l PhotoLean/Sabatier/*.lean`；在最后一个触及源码的提交 `03a0069` 之后实测；其后各收尾提交不触及源码，故该数字在本文件所在 revision 稳定），**134 条公开声明
（107 定理 + 27 定义/归纳类型，即 26 个 `def` 与 1 个 `inductive`）**，另有 36 条 private 辅助引理。
语句权威 `sabatier-statement-skeleton.lean` 覆盖其中 **132** 条（105 定理 + 27 定义/归纳类型）；
余下 2 条是描述层的辅助定理（`branchDown_le_branchUp_of_apex_le`、`branchUp_le_branchDown_of_le_apex`）。
**逐字一致 132/132，签名差异 0**（按里程碑 S1/S2/S3/S4/S5a/S5b 分别为 30/19/11/13/21/38）。
**107 条定理全部内核证毕：零未完成占位、零自定义公理**（严格扫描 clean；对全部 107 条一次性
`#print axioms`，106 条为契约足迹 `[propext, Classical.choice, Quot.sound]`，1 条
`sabatierZoneQ_eq_optimal_iff` 为其子集 `[propext]`）。在 `03a0069` 上**71 个提交触及 `PhotoLean/Sabatier/`**（用 `git log --oneline --
PhotoLean/Sabatier/ | wc -l` 复测），格式 `feat(S<k>): <lemma>` —— S2/S3/S4/S5a/S5b 每条引理（或每个实例行组）
一个提交；S1 是一个整模块合并提交、S5b 是 12 个行组提交，两处合并都已登记在任务板上。

**一句话结论**：在两步催化循环的双支 Brønsted–Evans–Polanyi 模型
`Ea(dE) = max (alphaA·dE + betaA) (betaB − alphaB·dE)` 中，**萨巴蒂尔描述**（有效势垒在顶点
`dE* = (betaB − betaA)/(alphaA + alphaB)` 取**唯一全局最小**，因而活性 `exp(−Ea/k_BT)` 在顶点取唯一最大）
成立的**充要条件是 `0 < alphaA · alphaB`** —— 即两条支路分别惩罚描述符轴的两端。在物理定向
（`0 < alphaA` 且 `0 < alphaB`，恰是文献的"两条异号支路"图像）下该描述无条件成立；某条斜率退化为 0 时
顶点摊平成半直线平台，两条同号斜率则根本没有内部极值 —— 两种失效模式都配有内核见证。
"不过强、不过弱"的容差形式被量化：偏离顶点不超过 `tol` 时，势垒高出山口至多 `max(alphaA, alphaB)·tol`。

---

## 2. Part ① — the formal description

**English.** The model is one scalar descriptor `dE` (the binding free energy of the key intermediate;
the convention is *more negative = stronger binding*, plan §2) and two BEP branches, `branchUp
alphaA betaA dE = alphaA*dE + betaA` (the step penalized by weak binding) and `branchDown alphaB
betaB dE = betaB − alphaB*dE` (the step penalized by strong binding). The effective barrier is their
maximum — a **declared modelling premise**, not a derived law (plan §12; the literature's kinetic
treatments use an energetic-span difference or a Langmuir coverage factor on the strong-binding leg,
and the printed `max` forms act on step free energies, not barriers). The apex is the *crossing point*
of the two branches, a derived quantity: `apex_crossing` and `apex_unique_crossing` show it is the
unique solution of `branchUp = branchDown` (whenever `alphaA + alphaB ≠ 0`), and `apex_eq_zero_iff`
shows that the apex sits at the thermoneutral descriptor value exactly when the two offsets balance
(`betaA = betaB`) — this is the honest form of the literature's "the ideal catalyst sits at ΔG = 0",
which the literature itself reports as an idealization that shifts in practice.

The description itself is the predicate `VolcanoDescriptor f de0` — `de0` is the *unique global
minimizer* of the barrier profile `f` — with its dual `AntiVolcanoDescriptor f de0` (unique global
*maximizer*), which is the form in which the volcano plot of the activity is stated. The activity is
`activity f kB T dE = exp (−(f dE)/(kB·T))`; the point verdicts are `TooStrong`/`Optimal`/`TooWeak
apexD dE` (`dE` below / at / above the apex), the tolerance form is `NearOptimal tol apexD dE :=
|dE − apexD| ≤ tol`, and `SZone`/`sabatierZone` is a decidable three-way classifier with its three
`…_iff` characterizations.

**中文（第一部分：形式化描述）**：模型由单个描述符 `dE`（关键中间体的结合自由能；约定*越负=结合越强*，
见 plan §2）与两条 BEP 支路构成：`branchUp alphaA betaA dE = alphaA·dE + betaA`（被*弱*结合惩罚的步骤）
与 `branchDown alphaB betaB dE = betaB − alphaB·dE`（被*强*结合惩罚的步骤）。有效势垒取两者之最大值 —— 这是
**显式声明的建模前提**而非推导出的定律（plan §12：文献的动力学处理用的是 energetic span 之差，或强结合腿上
的 Langmuir 覆盖因子；文献印出的 `max` 形式作用于步骤自由能而非势垒）。顶点是两条支路的*交点*，是推导量：
`apex_crossing` 与 `apex_unique_crossing` 证明它是 `branchUp = branchDown` 的唯一解
（在 `alphaA + alphaB ≠ 0` 时），`apex_eq_zero_iff` 则证明顶点落在热中性描述符值上**当且仅当**两个偏移量相等
（`betaA = betaB`）—— 这正是文献"理想催化剂位于 ΔG = 0"的诚实形式（文献自己也报告该理想化在实践中会偏移）。

描述本身是谓词 `VolcanoDescriptor f de0`（`de0` 是势垒剖面 `f` 的**唯一全局最小点**），其对偶
`AntiVolcanoDescriptor f de0`（唯一全局*最大*点）则是活性火山图所采用的陈述形式。活性为
`activity f kB T dE = exp (−(f dE)/(kB·T))`；点判定为 `TooStrong`/`Optimal`/`TooWeak apexD dE`
（`dE` 低于/等于/高于顶点），容差形式为 `NearOptimal tol apexD dE := |dE − apexD| ≤ tol`，
`SZone`/`sabatierZone` 是带三条 `…_iff` 刻画的可靠三分类器。

---

## 3. Part ② — the laws, and the exact conditions for the Sabatier description to hold

### 3.1 The sharp condition (the central result)

**English.** `volcano_descriptor_iff` (S3) states, for every `(alphaA, betaA, alphaB, betaB)`:

  `VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE) (apex alphaA betaA alphaB betaB)
     ↔ 0 < alphaA * alphaB`.

Two readings, both *proved*: (i) **physical orientation** — `volcano_descriptor_of_physical` (S2)
turns `0 < alphaA ∧ 0 < alphaB` (`SabatierConforms alphaA alphaB`, the series-level verdict) into the
description; (ii) **label invariance** — `volcano_descriptor_iff_labels` and `volcano_descriptor_of_neg`
show the general condition is `SabatierConforms alphaA alphaB ∨ SabatierConforms (−alphaB) (−alphaA)`,
i.e. a series whose two branches *both* descend is the same volcano read with the two branches
interchanged (the relabelling identity `volcanoBarrier_relabel`; this is why the sharp statement is a
product and the naive parameter swap is not a symmetry — `apex_relabel` shows the swap *negates* the
apex, a false statement form that the Sprint-0 risk probe caught and that plan §3.1 records).
The volcano plot proper is `volcanoActivity_peak_iff` (S3): the activity has its unique global
maximum at the apex **iff** `0 < alphaA * alphaB`; the barrier-to-activity transfer is
`antiDescriptor_activity_iff` (S2), and the ratio form `activity_ratio` matches the repository's
Marcus rate-ratio convention. Sharpness comes with witnesses, not just an implication: `flat_witness`
/`not_descriptor_flat` (both slopes zero ⇒ a constant profile), `plateau_witness`/
`not_descriptor_plateau` (one slope zero ⇒ the barrier is minimal on a whole half-line, so there is no
pointed apex), `antiVolcano_monotone`/`not_descriptor_mixedSign` (opposite-slope signs ⇒ the barrier
is strictly monotone and the activity has no interior maximum).

**中文（第二部分之一：精确条件）**：`volcano_descriptor_iff`（S3）断言：对任意参数，
`VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE) (apex alphaA betaA alphaB betaB)
↔ 0 < alphaA * alphaB`。两种读法都被证明：(i) **物理定向** —— `volcano_descriptor_of_physical`（S2）把
`0 < alphaA ∧ 0 < alphaB`（即序列级判定 `SabatierConforms`）化为描述成立；(ii) **标签不变性** ——
`volcano_descriptor_iff_labels` 与 `volcano_descriptor_of_neg` 证明一般条件是
`SabatierConforms alphaA alphaB ∨ SabatierConforms (−alphaB) (−alphaA)`，即两条支路都"下降"的序列不过是
把两条支路互换后的同一个火山（重标签恒等式 `volcanoBarrier_relabel`；也正因如此，紧条件是一个乘积，
而朴素的参数互换**不是**对称性 —— `apex_relabel` 表明该互换会把顶点**取负**，这条假语句形式被 Sprint-0
风险探针抓到并记入 plan §3.1）。火山图本身是 `volcanoActivity_peak_iff`（S3）：活性在顶点取唯一全局最大
**当且仅当** `0 < alphaA * alphaB`；势垒到活性的转移是 `antiDescriptor_activity_iff`（S2），比值形式
`activity_ratio` 与本仓库 Marcus 的速率比约定一致。紧性不只是蕴含，还带见证：`flat_witness`/
`not_descriptor_flat`（两条斜率全为 0 ⇒ 常值剖面）、`plateau_witness`/`not_descriptor_plateau`
（一条斜率为 0 ⇒ 势垒在半直线上都取最小，没有尖顶）、`antiVolcano_monotone`/`not_descriptor_mixedSign`
（斜率异号 ⇒ 势垒严格单调、活性没有内部极大）。

### 3.2 The quantitative tolerance law

**English.** `volcanoBarrier_le_apex_add` (S2) bounds the price of missing the optimum: for
`0 < alphaA`, `0 < alphaB`, if `|dE − dE*| ≤ tol` then `Ea(dE) − Ea(dE*) ≤ max(alphaA, alphaB)·tol`
(the sign of `tol` is *derived* from the hypothesis, not assumed). `volcanoBarrier_apex_form` writes
the excess over the pass as the maximum of the two one-sided penalties,
`Ea(dE) = Ea(dE*) + max(alphaA·(dE − dE*), alphaB·(dE* − dE))`, and the observable legs are exact:
`volcanoBarrier_secSlope_of_apex_le` / `…_of_le_apex` show the finite differences of the barrier on
the two legs are `alphaA` and `−alphaB` — the literature's "the volcano legs have slopes ±α", made an
exact statement about observable secants. The two leg monotonicities
(`volcanoBarrier_strictMono_of_apex_le`, `volcanoBarrier_strictAnti_of_le_apex`) are the volcano shape
itself, and the four `exists_*` rows record non-vacuity.

**中文（第二部分之二：定量容差律）**：`volcanoBarrier_le_apex_add`（S2）给出错过最优点的代价上界：
在 `0 < alphaA`、`0 < alphaB` 下，若 `|dE − dE*| ≤ tol`，则 `Ea(dE) − Ea(dE*) ≤ max(alphaA, alphaB)·tol`
（`tol` 的符号由假设**推出**，不是额外假定）。`volcanoBarrier_apex_form` 把超出山口的部分写成两侧惩罚的
最大者：`Ea(dE) = Ea(dE*) + max(alphaA·(dE − dE*), alphaB·(dE* − dE))`；两条腿的可观测斜率是精确的 ——
`volcanoBarrier_secSlope_of_apex_le` / `…_of_le_apex` 证明势垒在两腿上的有限差分分别为 `alphaA` 与
`−alphaB`，把文献的"火山腿斜率为 ±α"变成关于可观测割线的精确命题。两条腿的单调性
（`volcanoBarrier_strictMono_of_apex_le`、`volcanoBarrier_strictAnti_of_le_apex`）就是火山形状本身，
四条 `exists_*` 记录非空性。

### 3.3 The microscopic / cross-theory form

**English.** `Compose.lean` (S4) rebuilds the volcano inside the repository's own two-parabola model
(`PhotoLean.BEP`): `parabolicBarrier lam1 lam2` is the maximum of the two Marcus-type step barriers
`BEP.eact lam1 (−dE)` and `BEP.eact lam2 dE`. `parabolic_descriptor` proves that this profile is a
volcano at its apex for every `0 < lam1`, `0 < lam2` — **no BEP linearization is needed for the
Sabatier description** — with the closed-form apex `apexPar lam1 lam2 = (lam2·√lam1 − lam1·√lam2)/
(√lam1 + √lam2)` and `parabolicBarrier_crossing`/`parabolicBarrier_apex_le`/`…_eq_apex_iff` for the
crossing, global minimality and uniqueness. The *linear* volcano is recovered as its tangent-line
form: `linearVolcano_eq_bepTangent` identifies `volcanoBarrier (1/2) (lam1/4) (1/2) (lam2/4)` with the
maximum of the two tangent lines of the parabolas, `bepLine_le_eact` is the tangent inequality, and
`linearVolcano_le_parabolic` concludes that the linear volcano is a pointwise **lower bound** on the
parabolic one — the linearization systematically underestimates the barrier away from the apex. For a
symmetric cycle (`lam1 = lam2`) the apex is at the thermoneutral value (`apexPar_self`) and there the
two volcanoes agree exactly (`linearVolcano_apex_exact`).

**中文（第二部分之三：微观/跨理论形式）**：`Compose.lean`（S4）在本仓库既有的两抛物线模型
（`PhotoLean.BEP`）内重建火山：`parabolicBarrier lam1 lam2` 是两条 Marcus 型步骤势垒
`BEP.eact lam1 (−dE)` 与 `BEP.eact lam2 dE` 的最大者。`parabolic_descriptor` 证明：只要
`0 < lam1`、`0 < lam2`，该剖面在顶点处就是火山 —— **萨巴蒂尔描述并不需要 BEP 线性化** ——
顶点有闭式表达 `apexPar lam1 lam2 = (lam2·√lam1 − lam1·√lam2)/(√lam1 + √lam2)`，
交点、全局最小与唯一性分别由 `parabolicBarrier_crossing`、`parabolicBarrier_apex_le`、
`parabolicBarrier_eq_apex_iff` 给出。*线性*火山则被恢复为它的切线形式：`linearVolcano_eq_bepTangent`
把 `volcanoBarrier (1/2) (lam1/4) (1/2) (lam2/4)` 认作两条抛物线切线之最大者，`bepLine_le_eact`
是切线不等式，`linearVolcano_le_parabolic` 由此得出线性火山是抛物线火山的**逐点下界** ——
线性化在远离顶点处系统性地低估势垒。对称循环（`lam1 = lam2`）的顶点落在热中性值上（`apexPar_self`），
且在那里两种火山完全一致（`linearVolcano_apex_exact`）。

---

## 4. Part ③ — instances, and what the kernel decides

**English.** `Instances.lean` (S5b) delivers 38 kernel-checked instance verdicts in three tiers,
deliberately kept apart (plan §8.2): **model rows** (I1–I8, the machinery on constructed numbers),
**literature rows** (I9–I11 HER, I12 OER; the printed number is a *premise*, the verdict on it is
checked), and **non-conforming rows** (I4, I5 — series that fail the description, decided with S3's
witnesses). Every number below was independently reproduced by the kernel-independent exact-rational
cross-check `theories/Sabatier/probes/sabatier-instance-check.py` (`all instance rows reproduced
exactly`), and every row is a kernel-checked theorem.

| row | series `(alphaA, betaA, alphaB, betaB)` | what the kernel decides |
|---|---|---|
| I1 | `(1/2, 1/2, 1/2, 1/2)` symmetric, apex `0` | conforms; pass height `1/2`; `dE = 0` optimal; `dE = −1/2` too strong with barrier `3/4` |
| I2, I3 | `(1/2, 0, 1, 1)` asymmetric, apex `2/3` | conforms; `dE = 0` too strong (barrier `1`), `dE = 1` too weak (barrier `1/2`), `dE = −1/3` too strong (barrier `4/3`) |
| I4 | `(0, 1, 1, 1)` | does **not** conform; no `VolcanoDescriptor`; the barrier is minimal on a whole half-line (`plateau_witness`) |
| I5 | `(1, 0, −1, 1)` | does **not** conform; the barrier is strictly monotone — no interior optimum |
| I6 | I2 series, `tol = 1/2` | `dE = 1/2` is `NearOptimal`; the barrier excess `1/6` respects the tolerance bound |
| I7 | two parabolas `lam1 = 1`, `lam2 = 4` | apex `2/3`; branches cross there; pass height `25/36`; the linear volcano underestimates it (`2/3 < 25/36`) |
| I9 | HER, Pt, `ΔG_H* = −0.09 eV` | too strong; inside the 10 %-of-1 band; barrier `109/200` on the reference volcano |
| I10 | HER, Au, `ΔG_H* = +0.45 eV` | too weak; outside the 10 % band; barrier `29/40` |
| I11 | HER, W, `ΔG_H* = −0.43 eV` | too strong; inside a `1/2` band (tolerance sensitivity) |
| I12 | OER, `max(x, 3.20 − x)` | apex `8/5` (= the printed optimal `1.60 eV`); conforms; overpotential `8/5 − 123/100 = 37/100` (= the printed `0.37 V`) |

The literature numbers carry their printed loci in the module docstrings
(`theories/Sabatier/LITERATURE.md` §R2.1–§R2.2: Nørskov et al. 2005, Table I with Eq. [8]
`ΔG_H* = ΔE_H + 0.24 eV`, `[arith]`; Man et al. 2011, Eq. 4.16–4.18 for the OER `max` form), the W row
carries the source's own caveat that the measured value for W/Mo/Nb is probably not representative of
the metallic state, and the numbers are *label* by source (the same metal has different printed values
in different sources; the record forbids mixing families). I12 is the *derivable* tier: the number
`3.20 eV` enters as a stated premise and the apex and the overpotential are computed by the kernel.

**中文（第三部分：实例与内核判定）**：`Instances.lean`（S5b）交付 38 条内核判定的实例结论，刻意分为三层
（plan §8.2）：**模型行**（I1–I8：在构造数字上跑通机制）、**文献行**（I9–I11 为 HER、I12 为 OER；
印刷数值是*前提*，对其的判定由内核检查）、以及**不符合行**（I4、I5：不满足描述的序列，用 S3 的见证判定）。
下表中每个数字都被内核无关的精确有理数交叉校验脚本
`theories/Sabatier/probes/sabatier-instance-check.py` 独立复现（`all instance rows reproduced exactly`），
每一行都是内核证毕的定理。

| 行 | 序列 `(alphaA, betaA, alphaB, betaB)` | 内核判定的内容 |
|---|---|---|
| I1 | `(1/2, 1/2, 1/2, 1/2)` 对称，顶点 `0` | 符合；山口高 `1/2`；`dE = 0` 最优；`dE = −1/2` 过强且势垒 `3/4` |
| I2、I3 | `(1/2, 0, 1, 1)` 非对称，顶点 `2/3` | 符合；`dE = 0` 过强（势垒 `1`）、`dE = 1` 过弱（势垒 `1/2`）、`dE = −1/3` 过强（势垒 `4/3`） |
| I4 | `(0, 1, 1, 1)` | **不**符合；不存在 `VolcanoDescriptor`；势垒在整条半直线上取最小（`plateau_witness`） |
| I5 | `(1, 0, −1, 1)` | **不**符合；势垒严格单调 —— 没有内部最优 |
| I6 | I2 序列，`tol = 1/2` | `dE = 1/2` 为 `NearOptimal`；势垒超出量 `1/6` 满足容差上界 |
| I7 | 两抛物线 `lam1 = 1`、`lam2 = 4` | 顶点 `2/3`；两支在此相交；山口高 `25/36`；线性火山低估它（`2/3 < 25/36`） |
| I9 | HER，Pt，`ΔG_H* = −0.09 eV` | 过强；位于 10 %-of-1 容差带内；参考火山上的势垒 `109/200` |
| I10 | HER，Au，`ΔG_H* = +0.45 eV` | 过弱；在 10 % 带外；势垒 `29/40` |
| I11 | HER，W，`ΔG_H* = −0.43 eV` | 过强；在 `1/2` 带内（展示容差敏感性） |
| I12 | OER，`max(x, 3.20 − x)` | 顶点 `8/5`（= 印刷的最优值 `1.60 eV`）；符合；过电位 `8/5 − 123/100 = 37/100`（= 印刷的 `0.37 V`） |

文献数字在模块 docstring 中带有各自的印刷出处（`theories/Sabatier/LITERATURE.md` §R2.1–§R2.2：
Nørskov et al. 2005 Table I 与 Eq. [8] `ΔG_H* = ΔE_H + 0.24 eV`，标注 `[arith]`；OER 的 `max` 形式见
Man et al. 2011 Eq. 4.16–4.18）；W 行携带文献自身的告诫（W/Mo/Nb 的测量值很可能不代表金属态）；
数字按来源标注（同一金属在不同来源中的印刷值不同，记录禁止混用不同族）。I12 属于*可推导*层：
`3.20 eV` 作为显式前提进入，顶点与过电位由内核算出。

---

## 5. Evidence, and what the process caught

**English.** *Gates.* Every module: `proofs/scripts/lake build` OK with no warnings,
`proofs/scripts/check.sh --strict` → `clean` / `verdict: PASS`, and `#print axioms`: one-shot over all
107 theorems gave the contract's footprint for 106 and the subset `[propext]` for one; the scan finds
zero placeholders and zero custom axioms. *Fidelity*: 132/132 authority rows word for word.
*Pre-verification evidence* (ours, for cross-checking, not a substitute for the verifier): the
Sprint-0 risk probe (`probes/sabatier-risk-probe.lean`, 0 error), the four API probes (0 error each),
the exact-rational instance cross-check, and the milestone fidelity numbers. *Independent verification*: verifier run 1
(S1 + the Sprint-0 artifacts) **PASS** with 12 findings, none HIGH; verifier run 2
(S2/S3/S4/S5a) **PASS** (64/64 axiom rows, a 425 250-point brute force of the sharp condition with
0 counterexamples, proof-term anti-circularity checks, clean-archive rebuild); verifier run 3
(S5b + the frozen whole tree + the documentation plane) — **the mathematics PASS** (38/38 axiom rows,
an independent exact-rational recomputation of all 38 instance numbers, whole-tree gate PASS) and the
**documentation plane FAIL** on findings V1–V14, which were then disposed (false docstring
arithmetic corrected, three counts re-measured, provenance labels aligned with the literature
record, the two Chinese experience entries translated, and the acceptance gate's scan extended to
`constant`). Verifier run 4 (the targeted re-audit of those disposals) confirmed them, reported the
residual documentation items R1–R7 and found **no invalidated declaration**; R1–R7 were then disposed
in the closeout commits, and verifier run 5 (the final confirmation) reproduced the counts, the bare
gate and the fidelity numbers and converted the verdict to **PASS** with one LOW attribution item,
also disposed. The run verdicts are recorded in
`theories/Sabatier/TASKS.md` § "Acceptance records".

*What the process caught (three corrections, all logged in `plan.md` §3.1).* (1) Two authority rows of
the first skeleton draft were **false** and the Sprint-0 risk probe produced kernel counterexamples:
`apex_comm`/`volcanoBarrier_comm` — the "label swap" is not an invariance but *negates* the apex
(because the second branch enters with slope `−alphaB`); they were replaced by the relabelling
identity. (2) `activity_descriptor_iff` was false: `exp(−Ea/k_BT)` is strictly *decreasing* in the
barrier, so the barrier's unique minimum is the activity's unique **maximum**; the corrected pair is
`AntiVolcanoDescriptor` + `antiDescriptor_activity_iff`/`volcanoActivity_peak_iff`. (3) The
kernel-independent rational cross-check caught a **sign-convention label inversion in the instance
rows** before the kernel ever met it: the catalyst at `dE = 0` of the asymmetric series (apex `2/3`) is
on the *too-strong* side, not the too-weak side; the I2 rows were corrected and both sides are now
delivered. None of the three ever reached a delivered theorem in its false form.

**中文（证据，以及流程抓到了什么）**：*验收门*：每个模块 `lake build` 无警告通过、
`check.sh --strict` 输出 `clean` / `verdict: PASS`；`#print axioms` 一次性覆盖全部 107 条定理 ——
106 条为契约足迹、1 条为其子集 `[propext]`；扫描零占位符、零自定义公理。*逐字一致*：132/132。
*我方预验证证据*（供交叉核对，不替代 verifier）：Sprint-0 风险探针、四个 API 探针（各 0 error）、
精确有理数实例交叉校验、各里程碑逐字一致数字。*独立验收*：各轮判决记录在
`theories/Sabatier/TASKS.md` 的 §"Acceptance records"。

*流程抓到的三处修正（均记入 `plan.md` §3.1）*：(1) 首版骨架的两条权威语句是**假**的，Sprint-0 风险探针
给出了内核反例：`apex_comm`/`volcanoBarrier_comm` —— "标签互换"不是不变性，而会把顶点**取负**（因为第二条
支路以斜率 `−alphaB` 进入）；已替换为重标签恒等式。(2) `activity_descriptor_iff` 为假：`exp(−Ea/k_BT)` 对
势垒严格**递减**，因此势垒的唯一最小点是活性的唯一**最大**点；修正后的形式是 `AntiVolcanoDescriptor` 与
`antiDescriptor_activity_iff`/`volcanoActivity_peak_iff`。(3) 内核无关的有理数交叉校验在**内核遇到该行之前**
抓到实例行里的一个**符号约定标签颠倒**：非对称序列（顶点 `2/3`）中 `dE = 0` 的催化剂在*过强*一侧而非过弱一侧；
I2 行已修正，且两侧现在都已交付。三处错误形态没有任何一处进入过交付定理。

---

## 6. Limits, non-goals, and registered deviations

**English.** The honesty table of `plan.md` §12 lists, claim by claim, what is *assumed* and what is
*proved*; the essentials: `Ea = max(branches)`, the BEP linearity in the descriptor, and the
Arrhenius activity form are **modelling premises** (declared, never hidden in a definition); the
volcano shape and its sharp condition, the tolerance bound, the leg slopes, the two-parabola volcano
and the tangent-line bridge are **theorems**; the literature's `ΔG_H*` values are **derived
numbers** — the printed `ΔE_H` plus `0.24 eV` by the source's own Eq. [8], the literature record's
`[arith]` column — and enter the instance rows as premises. The literature record's clean negatives
are part of the result: **no source states the sharp condition `0 < alphaA·alphaB`** (it is this theory's own
exactification), **no IUPAC entry for the Sabatier principle exists**, and the `max` form is *not* a
kinetic law of the sources. Scope limits (plan §13): one descriptor, two branches, no coverages/
microkinetics/scaling relations, no claim about any measured rate. Registered deviations: the
authority append of the S5b literature rows (plan §3.1) and the S4 module's `sqrt`-only apex form;
out of scope for this delivery: a `√`-free parametrization of the parabolic apex. The theory's data
plane lives under `theories/Sabatier/` and its Lean sources under `PhotoLean/Sabatier/` (the
contract's `SOURCE_DIRS` is global; the same layout as the four earlier theories).

**中文（限制、非目标与已登记偏差）**：`plan.md` §12 的诚实表逐条列出哪些是*假设*、哪些是*已证明*。要点：
`Ea = max(两支)`、描述符上的 BEP 线性、以及 Arrhenius 活性形式都是**建模前提**（显式声明，不藏在定义里）；
火山形状与紧条件、容差上界、两腿斜率、两抛物线火山与切线桥都是**定理**；文献的 `ΔG_H*` 数值是**推导数字**
（来源印刷的 `ΔE_H` 加 `0.24 eV`，用来源自己的 Eq. [8]，即文献记录的 `[arith]` 列），作为实例行的前提进入。文献记录的三个干净否定本身也是结果：**没有任何来源陈述过紧条件 `0 < alphaA·alphaB`**
（它是本理论自己的精确化）、**IUPAC 没有萨巴蒂尔原则词条**、`max` 形式**不是**来源的动力学定律。
范围限制见 plan §13：单一描述符、两支路、不含覆盖度/微观动力学/标度关系，也不对任何实测速率作断言。
已登记偏差：S5b 文献行对权威的追加（plan §3.1）、以及 S4 顶点只给出含 `sqrt` 的形式；
本次交付范围之外：抛物线顶点的无 `√` 参数化。理论数据面位于 `theories/Sabatier/`，Lean 源码位于
`PhotoLean/Sabatier/`（契约的 `SOURCE_DIRS` 是全局的；与前四个理论同一布局）。

---

## 7. Reproduction

**English.**
```
# build + discipline scan (contract commands; lake only through the wrapper)
proofs/scripts/check.sh --strict                      # bare: all default targets, whole-tree scan
proofs/scripts/check.sh --strict PhotoLean.Sabatier.Basic      # per module

# axiom footprint of a single theorem (namespace-qualified)
proofs/scripts/axioms.sh PhotoLean.Sabatier.Instances PhotoLean.Sabatier.inst_I12_OER_overpotential

# statement fidelity against the authority, per milestone
python3 theories/BEP/probes/bep-fidelity.py --theory Sabatier --milestone S3

# kernel-independent exact-rational re-derivation of every instance number
python3 theories/Sabatier/probes/sabatier-instance-check.py

# the Sprint-0 evidence (statement forms) and the API calibration
proofs/scripts/lake env lean theories/Sabatier/probes/sabatier-risk-probe.lean
proofs/scripts/lake env lean theories/Sabatier/probes/sabatier-statement-skeleton.lean
```
**中文（复现）**：同上命令：全树与单模块验收门、单定理公理足迹、按里程碑的语句逐字一致检查、
实例数字的内核无关精确有理数复算、以及 Sprint-0 的语句形式证据与 API 校准探针。
