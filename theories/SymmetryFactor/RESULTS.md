# theories/SymmetryFactor/RESULTS.md — the symmetry-factor adjudication (human-facing answers, bilingual)

> The contract's only bilingual file: each section gives the English original followed by its
> Chinese rendering. Status: **delivered 2026-09-21, author-gated; independent verifier PASS
> pending** — the board rows stand at `review` until the verdict lands (iron rules 6/7).

## 1. Executive summary

**English.** Five Lean modules under `PhotoLean/SymmetryFactor/` — `Basic.lean` (F1, description),
`Criterion.lean` (F1, the crossing law), `Sharp.lean` (F2, the verdicts), `RatModel.lean` (F3, the
computable ℚ decision layer) and `Instances.lean` (F4, named verdict rows) — containing **35
declarations: 28 theorems and 7 definitions**, all completely proved: **zero unproved placeholders,
zero custom axioms**; every theorem's `#print axioms` lists at most `propext`, `Classical.choice`,
`Quot.sound`. Every signature matches the statement authority
`theories/SymmetryFactor/probes/SymmetryFactor-statement-skeleton.lean` **35/35 word for word**
(`signature differences: 0`). Two Sprint-0 statement corrections (both premise-drops under the
weakest-premise standard) are logged in `plan.md` §3.1.

**The one-sentence result.** In the two-parabola model with **unequal** force constants `kr, kp > 0`,
the thermoneutral crossing coordinate is `√kp/(√kr+√kp)` — the unique crossing of the two surfaces
inside `[0,1]` — and therefore the working reading "the transfer coefficient / symmetry factor is
1/2" holds **exactly when `kr = kp`** (`betaHalf_iff_equalForceConstants`), fails at every unequal
pair (kernel witnesses `(1,4) ↦ 2/3`, `(4,1) ↦ 1/3`), and holds throughout the equal-curvature
Marcus family, tied back by certificates to `Kernel.tsCoord` and `BEP.transfer` at thermoneutrality.

**Why this is the repository's first adjudicated conflation (H1∃).** The literature record is a
pair: a first-hand practice locus — a modelling review that states the charge-transfer coefficient
is "usually both taken to be equal to 0.5" with no force-constant condition (LITERATURE S1,
arXiv:2104.05424 §2.1) — and the standards body's printed warning that the value "can by no means
be assumed" and that β deviates from 0.5 exactly when the two force constants differ (LITERATURE
S2, IUPAC TR 2014, pp. 255–257). The kernel now **decides** the identification and its exact
boundary; and the decision *explains the persistence of the conflation*: the symmetrized
equal-curvature model — the picture every textbook draws, and Marcus's own declared approximation
(LITERATURE S4) — is precisely the regime where the reading is a theorem.

**中文（摘要）**：`PhotoLean/SymmetryFactor/` 下五个模块（F1 描述层与交叉律、F2 判决层、F3 可计算
ℚ 判定层、F4 具名判决行），共 **35 条声明：28 定理 + 7 定义**，全部完整证明：**零占位、零自定义
公理**（每条 `#print axioms` 至多 `propext / Classical.choice / Quot.sound`）；交付签名与语句权威
**逐字一致 35/35**（差异 0）。两条 Sprint-0 语句订正（均为最弱前提标准下的前提删除）记入
`plan.md` §3.1。**一句话结论**：在**非等曲率**双抛物面模型（`kr, kp > 0`）中，热中性交叉坐标为
`√kp/(√kr+√kp)`（`[0,1]` 内唯一交叉点），因此"转移系数/对称因子 = 1/2"的工作读法**恰在 `kr = kp`
时成立**（`betaHalf_iff_equalForceConstants`），在一切不相等对上失败（内核见证 `(1,4) ↦ 2/3`、
`(4,1) ↦ 1/3`），并在整个等曲率 Marcus 家族成立——经证书回接到 `Kernel.tsCoord` 与
`BEP.transfer` 的热中性值。**为什么这是本仓库第一条"已裁决混同"（H1∃）**：文献记录成对——
一手**实践位点**（某建模综述原文：电荷转移系数"通常都取 0.5"，无力常数条件；S1）与标准机构的
**印刷警告**（α"绝不能被假定"、两力常数不等时 β 大幅偏离 0.5；S2，IUPAC TR 2014, pp.255–257）。
内核如今**裁决**了这个等同及其精确边界；且裁决**解释了混同为何长存**：对称化等曲率模型——教科书
画的那张图、Marcus 自己声明的近似（S4）——恰好是该读法成为定理的区域。

## 2. What is decided, and what the decision is not

**English.** *Decided (theorems):* the closed form is the unique crossing in `[0,1]`
(`tsCoordZero_crosses`, `crossing_unique_in_unit_interval`; the interval restriction is
load-bearing — the second real root `q = 2` at `(1,4)` is a delivered witness,
`crossing_witness_outside_interval`); the verdict iff and its witnesses; the direction asymmetry
(the crossing sits on the side of the **softer** well: a stiffer product well gives a *late*
transition state at **zero** driving force, `tsCoordZero_gt_half_iff_stiffProduct` — a Hammond-style
structural verdict needing no driving force); the two monotonicities; the equal-curvature tie-back
certificates; and the ℚ decision layer with cast bridges (`betaHalfQ_cast`: the ℚ verdict **is** the
real verdict at perfect-square curvatures). *Not decided (registered, plan §1.3):* the kinetic
reading (a derivative of the barrier at general driving force — analysis substrate), the Leffler
α = q‡ identification under asymmetry (stretch goal), and anything about measured electrodes. The
instance rows are kernel facts about **declared numbers**, and the whole adjudication is a statement
**inside the declared model** — the scope qualifier travels with every headline (the discipline of
RELATIONS.md §6, and the lesson of the Kasha run-3 finding #5: no premise-free display of a
conditional headline).

**中文（裁决了什么、没裁决什么）**：**已裁决（定理）**：闭式即 `[0,1]` 内唯一交叉点（区间限定是
承载的——`(1,4)` 处第二个实根 `q = 2` 是交付见证）；判决 iff 及其见证；方向不对称（交叉点偏向
**较软**的势阱：产物阱更硬 ⇒ 零驱动力下过渡态就**偏晚**——不需要任何驱动力的 Hammond 式结构
判决）；两条单调性；等曲率回接证书；ℚ 判定层与 cast 桥（ℚ 判决**就是**完全平方曲率下的实判决）。
**未裁决（登记在案，plan §1.3）**：动力学读法（一般驱动力下势垒的导数——分析基质）、非对称下的
Leffler α = q‡ 等同（延伸目标）、以及任何关于实测电极的断言。实例行是**关于声明数字**的内核
事实；整个裁决是**声明模型内部**的陈述——限定词随每一条头条走（RELATIONS.md §6 的纪律、Kasha
run-3 finding #5 的教训：条件性头条不得无前提展示）。

## 3. Evidence and gates

**English.** Author-side gates (raw): five-module and full-tree `lake build` → exit 0, **0
warnings**; `check.sh --strict` → leaf plane 7/7, scan `clean`, `verdict: PASS`; authority compiles
at 0 error with placeholders; fidelity unscoped **35/35** and milestone-scoped **15/10/5/5**, all
`signature differences: 0`; `axioms.sh` on all 28 theorems → every footprint exactly `[propext,
Classical.choice, Quot.sound]`. The API round refuted four guessed names **before** any proof was
written (`Real.sqrt_four`, `sq_eq_sq_iff_eq_or_eq`, `transfer_thermoneutral`'s module, bare
`norm_num` on `Real.sqrt` — plan §3.1 item 3, `proofs/API-NOTES.md` §symmetryFactor); the
`norm_cast`/`exact_mod_cast` route for the cast bridge was **tried and rejected** on measured type
mismatches (`(1/2:ℝ)` does not present as a `Rat.cast`), and the deterministic `Rat.cast_inj` +
explicit numeral lemma route replaced it. Vacuity discipline (the M1 lesson) was applied
prospectively: the theory has no bare `∃`-non-vacuity row; `inst_nonvacuous_both_readings` pins
both readings at concrete positive curvatures, and under the totalized convention
`BetaHalfReading 0 0` is **false** (0 ≠ 1/2), so no degenerate parameter satisfies the reading for
free. **Independent verification is pending**; per iron rule 6 this section is an author-side
record, not a verdict.

**中文（证据与门）**：作者侧门（原始结果）：五模块与全树构建 exit 0、**零警告**；
`check.sh --strict` → 叶数据面 7/7、扫描 `clean`、`verdict: PASS`；权威以占位编译 0 error；保真
未限定 **35/35**、按里程碑 **15/10/5/5**，签名差异全 0；全部 28 条定理逐条过 `axioms.sh`，足迹
恰为 `[propext, Classical.choice, Quot.sound]`。API 轮在**动笔证明之前**证伪了四个猜测名
（plan §3.1 第 3 条、API-NOTES §symmetryFactor）；cast 桥的 `norm_cast`/`exact_mod_cast` 路线
**实测被拒**（`(1/2:ℝ)` 不以 `Rat.cast` 形态呈现，type mismatch），改走 `Rat.cast_inj` + 显式
数字引理的确定性路线。空洞性纪律（M1 教训）**前置执行**：本理论没有裸 `∃` 非空洞行；
`inst_nonvacuous_both_readings` 把两种读法钉在具体正曲率上，且在totalized约定下
`BetaHalfReading 0 0` 为**假**（0 ≠ 1/2）——不存在白拿的退化参数。**独立验证 PENDING**；按
铁律 6，本节是作者侧记录而非判决。

## 4. Limits and honesty

**English.** 1. The model is chosen, not derived (plan §1.2): two harmonic surfaces, classical
crossing, thermoneutral scope; totalized division and totalized `Real.sqrt` are Lean conventions,
flagged wherever consumed. 2. S1 is a **preprint** and a modelling review — it documents practice
(the criterion L1 asked for), it is not an authority recommendation; the authority side is S2's
printed IUPAC pages. The paper must cite the pair, never S1 alone. 3. L2 (Fletcher 2009 upgrade to
first-hand) was **not done** — registered as open (LITERATURE S5); the verdict does not depend on
it. 4. The observable (Tafel-slope) α is not formalized; the structural reading is tied to it only
through the delivered equal-curvature E1 (`transfer = tsCoord`), and the tie is itself part of what
the asymmetry breaks (stretch goal, plan §1.3.2). 5. This theory enters the relation graph as the
first row of class **A1 (adjudicated conflation)** — distinct from the N-look-alikes: an N-row says
"similar shape, no edge"; an A-row says "the literature treats these as the same, and here is the
kernel's boundary of that sameness" (`PhotoLean/Relations.lean` §11).

**中文（限制与诚实）**：① 模型为选择而非推导（两条谐振面、经典交叉、热中性范围；totalized 除法
与 totalized `Real.sqrt` 是 Lean 约定，凡消费处均已标注）。② S1 是**预印本**兼建模综述——它记录
实践（正是 L1 判据要的位点），不是权威推荐；权威一侧是 S2 的 IUPAC 印刷页。论文必须**成对**
引用，不得单引 S1。③ L2（Fletcher 2009 一手化）**未做**，已登记为开放项；判决不依赖它。
④ 可观测（Tafel 斜率）α 未形式化；结构读法只经已交付的等曲率 E1（`transfer = tsCoord`）与之
相连，而这个连接本身正是非对称性打破的对象（延伸目标）。⑤ 本理论以 **A1 类（已裁决混同）**
首行的身份接入关系图——与 N 形似实异不同：N 行说"形状相似、无边"，A 行说"文献把二者当同一个，
而这是内核对'同一个'的边界判决"（`Relations.lean` §11）。

## 5. Reproduction

```bash
proofs/scripts/lake build
proofs/scripts/check.sh --strict
proofs/scripts/lake env lean theories/SymmetryFactor/probes/SymmetryFactor-statement-skeleton.lean
python3 theories/BEP/probes/bep-fidelity.py --theory SymmetryFactor            # 35/35, 0 differences
python3 theories/BEP/probes/bep-fidelity.py --theory SymmetryFactor --milestone F2   # 10/10
proofs/scripts/axioms.sh PhotoLean.SymmetryFactor.Sharp PhotoLean.SymmetryFactor.betaHalf_iff_equalForceConstants
proofs/scripts/axioms.sh PhotoLean.SymmetryFactor.Instances PhotoLean.SymmetryFactor.inst_conflation_falsified
```

**中文（复现）**：上列命令依次复现全量构建、严格门、权威编译、保真（未限定与里程碑级）与两条
头条定理的公理足迹；每条 `axioms.sh` 必须打印 `verdict: PASS (only mathlib infrastructure
axioms)`。
