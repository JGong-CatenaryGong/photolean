# theories/BEP/RESULTS.md — the Bell–Evans–Polanyi principle, formalized in Lean

> The single bilingual deliverable of the BEP theory: every section carries the English original
> immediately followed by its Chinese rendering (contract `proofs/ENGINE.yml`, language policy in
> `proofs/ENGINE.md` §1.5). The human request had three parts — (①) turn the BEP principle into a
> formal description, (②) prove the description / find its exact validity conditions, (③) plug
> instances in and decide whether they conform — answered in §2, §3 and §4 below. Every number in
> this file is a measured value from the delivered tree, never a plan target.
>
> 本文件是 BEP 理论的唯一双语交付物：每节英文原文后紧跟中文对照。人类需求分三部分 ——
> ①把 BEP 原理转化为形式化描述、②证明该描述并找出其精确成立条件、③代入实例判断是否符合 ——
> 分别在下面的 §2、§3、§4 答复。本文件中的每个数字都是交付树的实测值，不是计划目标。

---

## 1. Executive summary

**Delivered.** Six Lean modules under `PhotoLean/BEP/` — `Basic.lean` (B1, description),
`Criterion.lean` (B2, laws), `Sharp.lean` (B3, sharp conditions), `Compose.lean` (B4, microscopic
and cross-module), `RatModel.lean` (B5a, computable rational verdict layer) and `Instances.lean`
(B5b, instance verdicts) — containing **191 declarations: 32 definitions, 2 inductive types and 157
theorems**, all completely proved: **zero unproved placeholders, zero custom axioms**. Every
statement was calibrated before proof work and the delivered signatures match the statement
authority `theories/BEP/probes/bep-statement-skeleton.lean` **191/191 word for word** (0
differences, 0 declarations outside the authority). Delivery discipline: **one commit per lemma**
(164 lemma/definition commits in the BEP areas — B1 18, B2 28, B3 32, B4 13, B5a 25, B5b 48 — plus
probe, scaffold and documentation commits).

**The one-sentence result.** Inside the equal-curvature two-parabola model with driving force
`x = -ΔG°` (exergonic: `x > 0`) and reorganization energy `λ`, the barrier is
`Ea(x) = (λ - x)²/(4λ)`; the Bell–Evans–Polanyi line law is then *exactly* violated by the
quadratic remainder `x²/(4λ)`, its slope `α = 1/2 - x/(2λ)` **is** the transition-state coordinate
`q‡` (the Leffler/Brønsted identification) and equals `1/2` exactly at thermoneutrality, the
forward and reverse coefficients are complementary (`α + α_r = 1`), the bounds `0 ≤ α ≤ 1` hold
**iff** `-λ ≤ x ≤ λ` **iff** *neither direction of the step lies in the Marcus inverted region*,
**exact affinity holds only in the degenerate model `λ = 0`** (and on no nontrivial window for
`λ ≠ 0`), so BEP conformance must be stated with a tolerance — whose sharp validity radius is
`2√(λ·tol)`, and for which the **best possible affine law on a symmetric window** is the tangent
line shifted by `w²/(8λ)`, with worst-case violation `w²/(8λ)`, **exactly half** the tangent
line's. Plugging in instances: **four** of the five **first-hand literature families** have per-point data
and are formalized (the fifth is aggregate-only and is deliberately left `UNSUPPORTED` rather than
guessed); all four conform to the *affine* BEP description on their printed rows (two-point slopes
inside `(0,1)`, every point `conforming`) while **all four are refuted as equal-curvature
two-parabola families** (their second divided difference is negative, whereas the model with
`λ > 0` forces `1/(4λ) > 0`) — the affine law survives, the model behind it does not, and the
formalization states exactly that distinction. The plan's original wish for "at least one
conforming literature family" is therefore **not met and is not pretended to be met**: the
literature block is a table of refutations, and the conforming two-parabola rows are the
model-constructed `I1`–`I3`.

**摘要（交付概况）**：`PhotoLean/BEP/` 下六个 Lean 模块（B1 描述层、B2 定律层、B3 精确条件层、
B4 微观与跨模块层、B5a 可计算有理判决层、B5b 实例判决层）共 **191 条声明：32 个定义、2 个归纳类型、
157 条定理**，全部完整证明，**零占位证明、零自定义公理**；所有语句在动证明前先完成标定，交付签名与
语句权威 `theories/BEP/probes/bep-statement-skeleton.lean` **逐字一致 191/191**（0 差异、0 权威外声明）；
**每定理一个提交**（BEP 区域 164 个引理/定义提交：B1 18、B2 28、B3 32、B4 13、B5a 25、B5b 48）另加脚手架与文档提交。**一句话结论**：等曲率双抛物
模型（驱动力 `x = -ΔG°`，放能时 `x > 0`；重组能 `λ`）中势垒 `Ea(x) = (λ-x)²/(4λ)`，BEP 线性律被精确
违反的余项是 `x²/(4λ)`；其斜率 `α = 1/2 - x/(2λ)` **就是**过渡态坐标 `q‡`（Leffler/Brønsted 同一性），
且只在热中性点等于 `1/2`；正逆系数互补（`α + α_r = 1`）；界 `0 ≤ α ≤ 1` 成立**当且仅当** `-λ ≤ x ≤ λ`，
**当且仅当**该步的正逆两个方向都**不在** Marcus 反转区；**精确仿射只在退化模型 `λ = 0` 成立**（`λ ≠ 0`
时在任何非平凡窗口上都不成立），所以"符合 BEP"必须带容差表述 —— 其精确有效半径是 `2√(λ·tol)`，而在
对称窗口上**最优仿射律**是切线整体上移 `w²/(8λ)`，最坏违反恰为切线的**一半**。代入实例：五个**一手文献族**中
有逐点数据、被形式化的是**四个**（第五个只有族汇总，标为 `UNSUPPORTED` 而**不猜数**）；这四族在印刷行上
全部符合**仿射** BEP 描述（两点斜率落在 `(0,1)`、逐点判决为 `conforming`），但**四族都作为等曲率双抛物族
被证伪**（它们的二阶差商为负，而 `λ > 0` 的模型强制 `1/(4λ) > 0`）—— 仿射律存活、其背后的模型不成立，
形式化恰好把这两件事分开陈述。因此计划原先"至少有一个文献族判定为 conforming"的愿望**未满足、也不假装
满足**：文献块是一张证伪表，而 conforming 的双抛物行来自模型构造的 `I1`–`I3`。

---

## 2. Part ① — the formal description (what "BEP" became in Lean)

**The model (assumptions, all explicit).** Reaction coordinate `q` with the reactant well at
`q = 0` and the product well at `q = 1`; harmonic surfaces of **equal** curvature `2λ`; the
transition state is the classical **crossing point**; the driving force is `x = -ΔG°` (exergonic:
`x > 0`); `λ` is held fixed across a compared family; no tunneling/recrossing and **no work or
steric terms** (the same exclusion Cohen & Marcus make in their own treatment); the empirical
`ΔH`-based literature is bridged to the model's `ΔG°` only under the family-wise constant-entropy
declaration. None of this is derived: it is the premise set, registered with its printed anchor
(Migliore et al., *Chem. Rev.* 114:3381 (2014), §6.2) in `theories/BEP/plan.md` §13.

**模型（假设全部显式）**：反应坐标 `q`，反应物井在 `q = 0`、产物井在 `q = 1`；两个谐振面**等曲率** `2λ`；
过渡态取经典**交叉点**；驱动力 `x = -ΔG°`（放能时 `x > 0`）；被比较的"族"内 `λ` 固定；无隧穿/再穿越，
且**无功项与位阻项**（与 Cohen & Marcus 自身处理所排除的项一致）；经验文献以 `ΔH` 为变量，只有在该族
"熵变恒定"的**声明**下才与模型的 `ΔG°` 对应。以上不从模型推出，是前提集，其印刷锚点
（Migliore 等，*Chem. Rev.* 114:3381 (2014) §6.2）登记在 `theories/BEP/plan.md` §13。

**The definitions delivered** (`Basic.lean`, 17 `def` + 1 inductive):

```text
eact lam x            = (lam - x)^2 / (4*lam)            barrier (same body as Marcus.barrier)
bepLine lam x         = lam/4 - x/2                      the BEP / linear-free-energy line
bepDefect lam x       = eact lam x - bepLine lam x       exact violation of the line law
transfer lam x        = 1/2 - x/(2*lam)                  BEP/Brønsted/Leffler coefficient (linear-response form)
reverseTransfer lam x = 1/2 + x/(2*lam)                  the reverse direction's coefficient
secSlope lam x h      = (eact lam x - eact lam (x+h))/h  OBSERVABLE finite-difference slope over [x, x+h]
bepRadius lam tol     = 2*sqrt(lam*tol)                  the tolerance validity radius
bepBestLine lam w x   = lam/4 + w^2/(8*lam) - x/2        the minimax affine law on [-w, w]
EPBounds / EPLinearOn / EPExact / EPConformsOnWindow / EPBestOnWindow / EPRegime / EPConforms / EPDescriptor
EPZone (9 constructors) + epZone : ℝ → ℝ → EPZone        decidable regime classifier
```

**已交付定义**（`Basic.lean`，17 个 `def` + 1 个归纳类型）：上表给出势垒、BEP 直线、精确偏离、正/逆
系数、**可观测量**（窗口上的有限差商）、容差半径、极小极大最优线，以及界/精确性/窗口符合性/最优性/
区域谓词与 9 构造子的**可判定区域分类器** `epZone`（退化、非物理、热中性、放能、吸能、正向极限、
逆向极限、正向越界、逆向越界）。

**The computable decision layer** (`RatModel.lean`, B5a) mirrors every quantity in `ℚ`
(`qEact`, `qBepLine`, `qBepDefect`, `qTransfer`, `qReverseTransfer`, `qSecSlope`, `qAlphaObs`,
`qLamOfPair`, `qConformsWindow` — the last in *squared* form so that no square root is needed —
plus the six-branch verdict `EPQVerdict`/`epQVerdict` and the model-consistency witnesses
`qSecondDividedDiff`/`qModelConsistent3`), with `cast` lemmas proving each ℚ quantity is the ℝ one.
**可计算判决层**（`RatModel.lean`，B5a）把每个量在 `ℚ` 上重写（`qConformsWindow` 用**平方形式**以避免开方），
并给出六分支判决 `epQVerdict` 与模型一致性见证 `qSecondDividedDiff`/`qModelConsistent3`，每个量都有
`cast` 引理证明它就是 ℝ 侧那个量（而不是另立一套）。

---

## 3. Part ② — the laws and their exact validity conditions

**English.** The BEP description has three layers of content: exact laws inside the model, the
sharp conditions under which it is (or is not) true, and the bridges to the two sibling theories.
The load-bearing results, with their exact statements:

| result | statement (Lean name) | meaning |
|---|---|---|
| exact expansion | `eact_expansion : lam ≠ 0 → eact lam x = lam/4 - x/2 + x^2/(4*lam)` | the model barrier is affine + a quadratic remainder — the IUPAC-printed shape (`Δ‡G = Δ‡Gº + ½Δ_rGº + (Δ_rGº)²/(16Δ‡Gº)`) |
| exact violation | `bepDefect_eq : lam ≠ 0 → bepDefect lam x = x^2/(4*lam)` | the BEP line's exact error is a pure square |
| defect sign | `bepDefect_nonneg`, `bepDefect_pos_iff`, `bepDefect_sign_flips` | for `λ > 0` the linear law always *under*-estimates the barrier, strictly except at thermoneutrality; the sign of the violation **is** the sign of `λ` |
| observable = structure | `secSlope_eq_transfer_mid : secSlope lam x h = transfer lam (x + h/2)` | the slope measured from barrier data over a window equals the model coefficient **at the window midpoint** — an exact identity for parabolas (no mean-value theorem involved) |
| coefficient = TS coordinate | `transfer_eq_tsCoord : transfer lam x = (lam - x)/(2*lam)` | the Leffler/Brønsted identification: the BEP slope is the transition-state position (`= Hammond.tsCoord`) |
| thermoneutrality | `transfer_thermoneutral : transfer lam 0 = 1/2` | Evans–Polanyi's empirical half is a *theorem at `x = 0`* (and only there — see the caveats in §6) |
| complementarity | `transfer_add_reverse : transfer lam x + reverseTransfer lam x = 1` | forward + reverse coefficients sum to one (the single-electron limit of the literature's `α_c + α_a = n/ν`) |
| barrier reversal | `eact_neg_eq_add : eact lam (-x) = eact lam x + x` | the forward-minus-reverse barrier is the driving force (microscopic consistency) |
| **bounds ⟺ regime** | `epBounds_iff_region : 0 < lam → (EPBounds lam x ↔ -lam ≤ x ∧ x ≤ lam)`; `epBounds_iff_no_inverted_direction : EPBounds lam x ↔ ¬ (InvertedRegion lam x ∨ InvertedRegion lam (-x))` | the transfer coefficient stays in `[0,1]` exactly while the crossing point lies between the wells, exactly while **neither direction is in the Marcus inverted region** — the printed analogue is Cohen & Marcus 1968 eqs. (5a)–(5c) |
| inverted / boundary values | `transfer_at_lam : transfer lam lam = 0`, `transfer_at_neg_lam : transfer lam (-lam) = 1`, `not_epBounds_of_gt`, `not_epBounds_of_lt_neg` | `α = 0` at the barrierless-forward limit, `α = 1` at the reverse limit, `α < 0` beyond it and `α > 1` beyond the other end |
| **exactness** | `epExact_iff_degenerate : EPExact lam ↔ lam = 0`; `not_epLinearOn_of_ne_zero : lam ≠ 0 → a < b → ¬ EPLinearOn lam (Set.Icc a b)` | **exact BEP holds only in the degenerate model** (zero barrier, zero driving-force dependence) and on **no** nontrivial window otherwise — the formal statement of "BEP is an approximation, never an identity" |
| **tolerance radius** | `epConformsOnWindow_iff_radius : 0 < lam → 0 < tol → 0 ≤ w → (EPConformsOnWindow lam tol (-w) w ↔ w ≤ bepRadius lam tol)` | the sharp validity condition of the linear law within tolerance `tol`: the driving-force window must satisfy `w ≤ 2√(λ·tol)`; `epConformsOnWindow_at_radius` shows the bound is attained |
| accuracy grows with `λ` | `bepDefect_antitone_lam`, `bepRadius_mono`, `epConformsOnWindow_mono_lam` | larger reorganization energy ⇒ smaller violation and a wider window of validity |
| **best affine law** | `bepBestLine_error`, `epBestOnWindow_holds`, `bepLine_worst_case`, `bepBestLine_halves` | on a symmetric window the minimax affine law is the tangent shifted up by `w²/(8λ)`; no affine law can beat `w²/(8λ)` (three-point equioscillation), the tangent's own worst case is `w²/(4λ)`, so the best BEP line is **exactly twice as good** as the tangent |
| cross-module bridges | `eact_eq_barrier`, `rate_eq_exp_neg_eact`, `transfer_eq_tsCoord_bridge`, `epBounds_of_reactionRegion`, `epBounds_of_marcus_normal`, `secSlope_eq_lefflerSecant` | the BEP barrier **is** the delivered Marcus barrier (so the BEP description constrains the delivered rate descriptor `A·exp(-Ea/kT)`), the BEP coefficient **is** the Hammond transition-state coordinate, and the BEP observable secant **is** Hammond's Leffler secant |
| microscopic composition | `epDescriptor_of_microscopic`, `bepDefect_le_of_microscopic`, `bepRadius_add`, `epConformsOnWindow_of_microscopic`, `epConformsOnWindow_shrinks_with_inner`, `transfer_complementary_microscopic` | `λ = λ_inner + λ_outer` with both parts positive: the description holds, the violation shrinks and the tolerance window widens as the outer contribution is added |
| sharpness witnesses | `bepDefect_zero_lam_witness`, `bepDefect_neg_lam_witness`, `secSlope_needs_h_ne_zero`, `exists_conforms_fails` | each hypothesis is exhibited as necessary by a kernel-checked witness (λ = 0 breaks the defect law; λ < 0 flips its sign; `h = 0` breaks the secant identity; and an explicit window/tolerance pair violates conformance) |

**中文。** BEP 描述的内容分三层：模型内的精确定律、成立的精确条件（以及不成立之处）、以及通向两个兄弟
理论的桥。上表逐条给出：**精确定律**（势垒 = 仿射部 + 二次余项 `x²/(4λ)`，与 IUPAC 印刷式同形；
偏离的符号恰是 `λ` 的符号）；**可观测量 = 结构量**（由势垒数据测得的窗口斜率精确等于窗口中点的模型系数；
该系数就是过渡态坐标 `q‡`，即 Leffler/Brønsted 同一性；热中性点系数恰为 `1/2`；正逆互补为 1；正逆势垒差
等于驱动力）；**精确条件**（界 `0 ≤ α ≤ 1` ⟺ 交叉点落在两井之间 ⟺ 正逆两方向都不在 Marcus 反转区；
`α = 0`/`α = 1` 出现在两个极限端点，越界则 `α < 0`/`α > 1`；**精确仿射只在退化模型 `λ = 0` 成立**，
`λ ≠ 0` 时任何非平凡窗口都不成立 —— 这就是"BEP 是近似而非恒等式"的形式化陈述）；**容差有效半径**
（在容差 `tol` 内成立的充要条件是窗口半宽 `w ≤ 2√(λ·tol)`，且该界可达）；**精度随 `λ` 单调改善**；
**极小极大最优直线**（对称窗口上最优仿射律是切线上移 `w²/(8λ)`，任何仿射律都无法优于 `w²/(8λ)`
——用三点等振荡证明；切线的自身最坏违反是 `w²/(4λ)`，故最优线恰比切线好一倍）；**跨模块桥**
（BEP 势垒**就是**已交付的 Marcus 势垒，故 BEP 描述约束已交付的速率描述子；BEP 系数**就是** Hammond 的
过渡态坐标；BEP 可观测量割线**就是** Hammond 的 Leffler 割线）；**微观加和**（`λ = λ_内 + λ_外`，两者正时
描述成立、偏离随加入外层而缩小、容差窗口随之变宽）；**锐利性见证**（每条前提都由内核检验的反例/见证
证明是必要的：`λ = 0` 破坏偏离律、`λ < 0` 翻转其符号、`h = 0` 破坏割线恒等式，另有一对显式的窗口/容差
使符合性失败）。

---

## 4. Part ③ — instance verdicts

**English.** Two things are being decided, and the formalization keeps them apart: (a) does the
instance satisfy the *affine BEP description* (slope inside `[0,1]`, i.e. no direction in the
inverted region), and (b) is it *reproducible by the equal-curvature two-parabola model* at all
(positive curvature, hence positive second divided difference `1/(4λ)`)? Model-constructed families
(`I1`–`I10`, kernel-checked rational arithmetic) and literature families (`I11`/`I12`, numbers
quoted verbatim from `theories/BEP/LITERATURE.md` §R1.10 with their `first-hand` status and unit)
are labelled per row.

| id | family / parameters | verdict | provenance |
|---|---|---|---|
| I1 | thermoneutral `λ=2, x=0` | conforming, `α = 1/2`, defect `0` | model-constructed (plan §8.2) |
| I2 | mildly exergonic `λ=2, x=1/2` | conforming, `α = 3/8` | model-constructed |
| I3 | mildly endergonic `λ=2, x=-1/2` | conforming, `α = 5/8` | model-constructed |
| I4 | forward limit `λ=2, x=2` | boundary, `α = 0` | model-constructed |
| I5 | reverse limit `λ=2, x=-2` | boundary, `α = 1` | model-constructed |
| I6 | forward inverted `λ=2, x=3` | **not conforming**, `α = -1/4 < 0` | model-constructed |
| I7 | reverse inverted `λ=2, x=-3` | **not conforming**, `α = 5/4 > 1` | model-constructed |
| I8 | degenerate `λ=0, x=1` | exact affinity *trivially* (barrier ≡ 0) but the **line law fails** (`bepDefect 0 x = x/2`); `α = 1/2` | model-constructed |
| I9 | unphysical curvature `λ=-2, x=1` | **not conforming**, defect `< 0` — note `α = 3/4 ∈ [0,1]` (the value `13/16` is the *two-point observable slope* `qAlphaObs` at the pair `x₁ = 1, x₂ = 3/2` of this model, a different quantity — kernel-checked, and no delivered theorem equates it with the coefficient), i.e. **the bounds alone do not detect it; the defect law does** | model-constructed |
| I10 | tolerance threshold `λ=2, w=1` | conforms at `tol = 1/8` (= `w²/(4λ)`), **fails** at `tol = 1/16`; threshold `w* = 2√(λ·tol) = 1` | model-constructed |
| I11 F1 | f-HAT of phenols, water/•OOH (*Antioxidants* 15(7):840, Table 1) | 8 printed points all `conforming` at the family `λ̂`; **family curvature negative** ⇒ `¬ ∃ λ>0` consistent with the three chosen points; two-point `λ̂ = 9/20`, `α_obs = 34/63` | literature, `first-hand` |
| I11 F2 | same family, PE solvent (*ibid.*) | 7 points `conforming`; **negative curvature** ⇒ model-refuted; `λ̂ = 16/15`, `α_obs = 89/153` | literature, `first-hand` |
| I11 F3 | •OOCH₃ oxidant, water (*ibid.*, Table 2) | 4 points `conforming`; **negative curvature** ⇒ model-refuted; `λ̂ = 22/5`, `α_obs = 83/107` | literature, `first-hand` |
| I11 F5 | 2-butanol + •OOH, CCSD(T) (*Chem. Sci.* 6:5866, Table 1) | 5 points `conforming`; **negative curvature** ⇒ model-refuted; `λ̂ = 7958/675`, `α_obs = 467/610` | literature, `first-hand` (ΔE, not ΔG° — flagged in the docstring) |
| F4 | •OOCH₃ oxidant, PE (*ibid.*, Table 2) | **UNSUPPORTED** — the record prints family aggregates only, no per-point pairs; no Lean row was invented for it | literature, `first-hand` but aggregate-only |
| I12 | summary over the literature set | **affine BEP conforms, the two-parabola model is refuted**: `¬ ∃ λ : ℚ, qModelConsistent3 …` for the chosen triples | literature + model |

**Point-level counts come from the non-Lean checker.** The "N printed points conforming" figures come from
`theories/BEP/probes/bep-instance-check.py` (exact rational arithmetic), not from a delivered Lean
declaration; the Lean layer's own I11 rows assert `0 < α_obs < 1` on the *chosen* pairs and the
negative curvature on the *chosen* triples.

**Reading the two verdict kinds separately.** Point-level *conformance* and family-level *model
consistency* are different questions, and the table answers both: the literature families are
`conforming` at the point level (their two-point slopes lie in `[0,1]`) while their triples are
**not** consistent with any positive-`λ` equal-curvature two-parabola model. The delivered
`_lamHat` rows use adjacent printed pairs and the refutation rows use three printed rows; the model
solver is pair-dependent on real data: other documented pairs of the *same* families give other
values, negative among them (F1 `16(2)`/`8` → `-2079/25`, F2 `13`/`19(2)` → `-53/60`, F3
`19(2)`/`1` → `-749/108`, F5 `R3`/`R4` → `-19667/1620`; the abscissa-widest pairs give `-37`,
`-609/10`, `-1701/292` and `+20923/810`), which is itself evidence of the inconsistency — no
verdict depends on `λ̂`. A ±half-unit
perturbation of every printed number flips **no** verdict (verifier B5b), so the rows are not
knife-edge.

All rational literals are checked by the kernel (`norm_num`; `by decide` is unusable on ℚ
comparisons containing `/` and `native_decide` is banned because `Lean.ofReduceBool` is not in
`ALLOWED_AXIOMS`). The instance values were independently recomputed by the non-Lean checker
`theories/BEP/probes/bep-instance-check.py` (exact `fractions`, **280** values as printed by the checker itself, `CROSS-CHECK: OK`), and
that check caught two transcription defects in the literature record's own λ̂ column (R4, R5 of
§R1.10.5), which were corrected in the record with a note — the record and the checker's ledger are
updated together.

**中文。** 实例判决要分开回答两件事，形式化严格保持区分：(a) 该实例是否符合**仿射 BEP 描述**（斜率落在
`[0,1]` 内，即两方向都不在反转区）；(b) 它是否能被**等曲率双抛物模型**复现（曲率为正，从而二阶差商
`1/(4λ) > 0`）。模型构造族（`I1`–`I10`，内核检验的有理算术）与文献族（`I11`/`I12`，数字逐字取自
`theories/BEP/LITERATURE.md` §R1.10 并标注 `first-hand` 状态与单位）逐行标明出处。上表给出结论，其中
三点最值得注意：**I8** 显示退化模型下"精确仿射"平凡成立但直线律不成立；**I9** 显示 `λ < 0` 时 `α` 仍可
落在 `[0,1]`，因此**单靠界抓不住非物理曲率，抓住它的是偏离律的符号**；**I11/I12** 显示五个一手文献族
"仿射侧合规、模型侧被证伪"。所有有理字面量均由内核检验（`norm_num`；含 `/` 的 ℚ 比较不能用 `by decide`，
`native_decide` 因引入 `Lean.ofReduceBool` 而被禁用）。实例数值另由非 Lean 独立检查器
`theories/BEP/probes/bep-instance-check.py` 复算（精确 `fractions`，**280** 个数值，由检查器自身打印，`CROSS-CHECK: OK`），
该检查还查出文献记录自身 λ̂ 列的两处转录缺陷（§R1.10.5 的 R4、R5），记录已带更正说明修正 ——
记录与检查器的数值副本必须同批更新。

---

## 5. Acceptance evidence

**English.** Every delivered declaration passed the three-layer gate (`lake build` +
`check.sh --strict` + `axioms.sh`), and each milestone was then re-judged by an **independent,
read-only verifier** working from fixed file hashes with its own parser and its own kernel probes.
Records so far:

| batch | scope | verdict | key evidence |
|---|---|---|---|
| #1 | `Basic.lean` (33) | **PASS** | graded on `sha256 5a366027…`; 33/33 `axioms.sh` clean (`depends on axioms: [propext, Classical.choice, Quot.sound]` quoted in full); verifier's own parser 33/33 word-for-word including `EPZone`'s nine constructors and the `deriving` clause; all nine classifier branch boundaries plus cascade exhaustiveness kernel-checked; hypothesis necessity split **5 load-bearing / 3 decorative** (the decorative ones were *proved* in strengthened form); non-vacuity witnesses for all nine zones; `#print` bodies identical to plan §4.1; **six falsification attempts all failed** |
| #2 | `Criterion.lean` (28) + `Compose.lean` (12) | **PASS / PASS** | graded on `sha256 b3ef9225…` / `b68e948c…`; 40/40 `axioms.sh` clean; verifier's own parser 28/28 and 12/12; 40/40 proof terms screened for circularity (**only two `rfl`s, both documented as definitional**); 20 hypothesis-necessity counterexamples; the mean-value identity hand-recomputed at three rational parameter sets; the headline bridge `epBounds_iff_no_inverted_direction` non-vacuous with same-true/same-false witnesses for both directions; a ≈7 200-instance rational-grid falsification of 31 statements found **0 counterexamples** |
| #4 | `RatModel.lean` (37) | **PASS** | graded on `sha256 75040761…` (skeleton `c9aa2cb1…`); 37/37 word-for-word, 0 extras; 22/22 `axioms.sh` clean; **all three kernel-counterexample-driven corrections reproduced independently** (the verifier proved the negations of the premise-dropped forms); eight cast lemmas `#print`-checked as genuine ℝ transfers **and used**; unconstrained-definition audit: **zero** in the settled state; all 25 commits touching the file are single-file commits (24 by `prover_c` plus the lead's `qReverseTransfer_cast` follow-up) |
| #3 | `Sharp.lean` (32) | **PASS** | graded on `sha256 b9b3b568…`; 32/32 `axioms.sh` clean; verifier's own parser: set equality 32/32 with the `epSupError` body compared too; the minimax lower bound **is** the original `∀ c a, ∃ x ∈ Set.Icc (-w) w` form (`#print` of `EPBestOnWindow` shows the pre-registered disjunctive fallback was not used) and is non-vacuous; the radius theorem checked in both directions (strict-interior case, failing-window case, attained radius); `a < b` load-bearing (a single point *is* trivially affine); 11 hypothesis-necessity counterexamples; the four sharpness witnesses use the totalised-division values and `secSlope_needs_h_ne_zero` really kills the mean-value identity; every load-bearing proof is a real derivation (no `rfl`), `Sharp.lean` imports only `Basic.lean`; edge-value falsification (w=0, tol=0, x=±λ, w<0, tol<0, lam<0, empty window) left every statement standing |
| #5 | `Instances.lean` (48) | **PASS** | graded on `sha256 99161212…` (unchanged start→end); 48/48 `axioms.sh` clean; 48/48 word-for-word, order identical; **all verdicts independently recomputed** (I1–I10 coefficients, cascade and threshold; the 12 I11 literals recomputed from §R1.10's printed kcal/mol rows); refutation derivations non-circular; `#print` shows real `norm_num` terms and a real existential refutation; `inst_nonvacuous` exhibits two distinct verdicts; F4 absent with no invented numbers; a ±half-unit perturbation grid flips no verdict; 48/48 commits touch only the owner's file |
| closeout | frozen tree | **three FAIL runs so far, all documentation-only; mathematics re-verified independently in every run** | first run (anchors: Basic `19133be2…`, Criterion `d0a0e7b8…`, Sharp `a874ce82…`, Compose `1a47e958…`, RatModel `75040761…`, Instances `029b02a3…`, skeleton `c9aa2cb1…`): gate PASS twice, 191/191 `axioms.sh` clean, statement fidelity 191/191, comment-only deltas confirmed **per declaration**, kernel spot-checks clean — but **eight documentation findings** (the I9 row's `α` conflated with the two-point slope; "276 values" where the checker prints 280; "167 commits" where 164 are measured; the plan's "R² ≈ 0.93–0.95" against the record's own F2 = 0.548; a reproduction command naming the wrong module; "24/24" where 25 is measured; plan text claiming a closeout record that did not yet exist; two stale board numbers). All eight were corrected (commits `ff62528`, `159644c`, `0c74c71`). **Second run**: the mathematics re-passed independently (191/191 `axioms.sh`, 191/191 fidelity, 34/34 definition bodies, comment-only deltas confirmed per declaration, the checker's `280` values, all kernel probes as expected, anchors identical start→end, `git status` clean) but the audit **FAILed again on documentation only** — three stale draft rows still in this board, the string `rate_exp` naming a theorem that never existed, an `EXPERIENCE.md` claim of `R² = 0.93–0.95 in four of five` against the record's `0.934 / 0.548 / 0.934 / 0.952`, this very row claiming a `PASS` that did not yet exist, and two LOW unit/wording items. Those corrections are recorded in `theories/BEP/TASKS.md` (both FAIL runs preserved) and in `proofs/EXPERIENCE.md`. **Third run**: the mathematics re-passed independently again (from-source re-elaboration of all six modules, 191/191 `axioms.sh`, 191/191 fidelity with 34/34 definition bodies, per-declaration token identity against every graded blob, `checked 280`, an independent 608 266-point rational grid with **0 counterexamples**) and the audit **FAILed a third time on documentation only**: a status line and the plan header claimed a closeout PASS that does not exist, the plan header omitted the second run, the literature record's §R1.10.6 still carried the "four of five" R² sentence, and this file's `13/16` note did not name the sample pair. All five were corrected. The FAILs are preserved here on purpose, exactly as in the `hammond` closeout, because a closeout that hides its own documentation defects is worthless; the mathematics never needed rework. |

Cross-checks that do not replace the kernel: the statement-fidelity checker
`theories/BEP/probes/bep-fidelity.py` (191/191 word-for-word, 0 differences, 0 declarations outside
the authority) and the exact-rational instance cross-check
`theories/BEP/probes/bep-instance-check.py` (280 values, exit 0, `CROSS-CHECK: OK`). The
verifiers' observations are all closed or registered: the statement authority is now under version
control (verifier O1/M1), the missing 13th B4 declaration was delivered
(`secSlope_eq_lefflerSecant`), comment-only wording fixes landed with the comment-stripped token streams proven identical
**per declaration** by the closeout audit (`Basic.lean`, `Criterion.lean`, `Sharp.lean`,
`Instances.lean`; `Compose.lean` gained exactly one declaration), the B5a/B5b
experience entries were written, and the two bookkeeping numbers on the board were corrected to the
measured values.

**中文。** 每条交付声明都过了三层门（`lake build` + `check.sh --strict` + `axioms.sh`），随后每个里程碑
由**独立、只读**的验证器按固定文件哈希、用自写解析器与自写内核探针重新判定。目前为止：#1 `Basic.lean`
（33 条）PASS —— 33/33 公理干净、逐字保真、九条分类器分支边界与级联无缝隙全部内核核验、五条前提承重
三条装饰、九个区域非空、六次证伪尝试全部失败；#2 `Criterion.lean` + `Compose.lean`（28 + 12）PASS/PASS ——
40/40 公理干净、逐字保真、证明项反循环筛查（只有两个 `rfl` 且都在 docstring 里声明为定义性）、20 个前提
必要性反例、中值恒等式三组有理参数手算复核、约 7200 个有理网格实例证伪 0 反例；#4 `RatModel.lean`（37）
PASS —— 37/37 逐字、22/22 公理干净、三处反例驱动的语句修正被**独立复现**（验证器自己证明了去掉前提后
的命题之否定）、八个 cast 引理经 `#print` 确认是真正的 ℝ 迁移**且被实际使用**、未受约束定义审计为零。
#3 `Sharp.lean`（32）与 #5 `Instances.lean`（48）的独立判定以及冻结态 closeout 的记录附于本节之后。
不替代内核的交叉检查：语句保真检查器（191/191 逐字、0 差异、0 权威外声明）与精确有理实例复算器
（280 个数值、exit 0、`CROSS-CHECK: OK`）。验证器提出的观察已全部关闭或登记：语句权威已纳入版本控制、
遗漏的第 13 条 B4 声明已交付（`secSlope_eq_lefflerSecant`）、注释级措辞修正以"去注释 token 流哈希不变"
证明未动语句、B5a/B5b 经验条目已补、任务板上两处计数已改为实测值。

---

## 6. Boundaries of the claim (what is NOT proved)

**English.** The formalization proves *conditional* statements inside a model; it does not prove
that chemistry obeys BEP. Explicit boundaries, all registered in `theories/BEP/plan.md` §13:

1. **Model assumptions.** One scalar reaction coordinate; crossing point = transition state; equal
   curvatures `2λ`; `λ` fixed across the compared family; no work/steric terms; no
   tunneling/recrossing. The theorems inherit them as premises.
2. **`ΔH` vs `ΔG°`.** The literature's classical variable is the enthalpy; the model is stated in
   the Gibbs energy. The bridge is a *declaration* (approximately constant entropy of activation
   within the family) — the record found **no first-hand source** for "constant entropy of
   activation is necessary", so it is declared, never cited.
3. **Naming.** `0 ≤ α ≤ 1` is a statement about the *model* coefficient: no source read in the
   record states it as a law of chemical families, and documented counterexamples exist
   (`α = -0.7`, `β = 1.7`, `α = 1.42 … 1.67` for nitroalkanes; `α ≈ 1.5`; the identity-reaction
   `δΔG‡/0` case). Likewise the complementarity `α_f + α_r = 1` is a model theorem and the
   literature's general form is `α_c + α_a = n/ν` (single electron, same rate-determining step).
4. **`α(0) = 1/2` only at thermoneutrality.** The record's own sources say β = 0.5 has "no physical
   basis" and that it is an assumption; Marcus's Nobel lecture prints the half slope with the
   qualifier "when [ΔG°] is small". The theorem is exactly at `x = 0`.
5. **Family assumptions are documented approximations.** Constant entropy, a single varying
   parameter, one site/adsorption mode, and a *constant* `λ` — the last is **refuted** by a
   first-hand experimental family (Salamone et al., *JACS* 143:11759 (2021): a broken EP line whose
   saturated branch alone fits `λ = 58 kcal/mol`, the other branch requiring `λ` to grow with
   driving force). Kinetic counterexamples to a material-independent coefficient (Tafel slopes are
   coverage-dependent and not RDS-unique) are registered too.
6. **Out of scope.** Tunneling, recrossing, diffusion control (the record found no source for the
   popular "diffusion control ⇒ Ea = solvent viscous-flow activation energy", so it is not cited at
   all), electronic-structure detail, surface catalysis coverage effects, temperature/prefactor
   dependence, and any claim about measured molecules rather than model families.

**中文。** 形式化证明的是模型内的**条件性**命题，不证明化学服从 BEP。显式边界（全部登记在
`theories/BEP/plan.md` §13）：①**模型假设**（单标量反应坐标、交叉点即过渡态、等曲率 `2λ`、族内 `λ`
固定、无功项与位阻项、无隧穿/再穿越），定理只以之为前提；②**`ΔH` 与 `ΔG°`**：文献的经典变量是焓，
模型用 Gibbs 能，其间桥接是**声明**（族内活化熵近似恒定）—— 记录确认"活化熵恒定是线性 BEP 的必要条件"
在**一手源中 0 命中**，故只声明、不引用；③**命名**：`0 ≤ α ≤ 1` 是关于**模型**系数的陈述，记录中没有
任何一手文献把它表述为化学族定律，反而有印刷页码的反例（硝基烷烃 `α = -0.7`、`β = 1.7`、`α = 1.42…1.67`、
`α ≈ 1.5`，以及恒等反应的 `δΔG‡/0`），互补性同理（文献通式是 `α_c + α_a = n/ν`，限单电子且同一速控步）；
④**`α(0)=1/2` 只在热中性点**成立（记录自身的源说 β = 0.5 "没有物理依据"、是假设；Marcus 诺奖演讲的
半斜率自带"当 [ΔG°] 很小时"的限定）；⑤**族假设都是有据的近似**：恒定熵、单一变动参数、同一位点/吸附
模式、常数 `λ` —— 最后一条被一手实验族**证伪**（Salamone 等，*JACS* 143:11759 (2021)：EP 线断成两支，
只有饱和支拟合 `λ = 58 kcal/mol`，另一支要求 `λ` 随驱动力增大），此外还有关于系数与材料无关的**动力学**
反例（Tafel 斜率依赖覆盖度且不唯一对应速控步）；⑥**范围之外**：隧穿、再穿越、扩散控制（记录中"扩散控制
⇒ Ea = 溶剂黏流活化能"的说法 0 命中，故一律不引）、电子结构细节、表面催化覆盖度效应、温度与前因子依赖，
以及任何关于真实分子而非模型族的断言。

---

## 7. Reproduction

**English.** From the repository root:

```bash
# 1. the three-layer gate for one module (repeat per delivered module)
proofs/scripts/lake build PhotoLean.BEP.Basic
proofs/scripts/check.sh --strict PhotoLean.BEP.Basic        # must print: verdict: PASS
proofs/scripts/axioms.sh PhotoLean.BEP.Criterion PhotoLean.BEP.bepDefect_eq   # module + fully-qualified name

# 2. the whole delivered set at once (bare run builds every defaultTargets entry)
proofs/scripts/check.sh --strict

# 3. statement fidelity against the frozen authority (the skeleton is committed)
python3 theories/BEP/probes/bep-fidelity.py            # expect: 191/191, 0 differences

# 4. non-Lean independent recomputation of every instance value
python3 theories/BEP/probes/bep-instance-check.py      # expect: checked 280 values, CROSS-CHECK: OK, exit 0

# 5. the probes (probe files may carry placeholders; the delivered modules may not)
proofs/scripts/lake env lean theories/BEP/probes/bep-risk-probe.lean
proofs/scripts/lake env lean theories/BEP/probes/bep-statement-skeleton.lean
```

**中文。** 复现命令同上：①单模块三层门（`lake build` + `check.sh --strict` + 带命名空间的 `axioms.sh`）；
②裸跑 `check.sh --strict` 覆盖全部 `defaultTargets`（BEP 六个模块均已登记）；③语句保真检查器对冻结权威
逐字比对（期望 191/191、0 差异）；④非 Lean 独立复算全部实例数值（期望 `CROSS-CHECK: OK`、exit 0）；
⑤探针文件（探针允许占位，交付模块不允许）。

---

## 8. Provenance and literature

**English.** The statement set, the regime structure and every instance number rest on
`theories/BEP/LITERATURE.md` (1584 lines, sections §R1–§R1.19), which records each source with a
checkable locus, a `first-hand` / `not-accessed` status, and a *formalizable implication*. Landmark
anchors: the normative wording of the principle and the affine+quadratic shape (IUPAC glossary and
its printed `Δ‡G = Δ‡Gº + ½Δ_rGº + (Δ_rGº)²/(16Δ‡Gº)`); the quadratic barrier law at **Marcus 1968
Eq. (2), p. 891** (the record corrected the common mis-attribution to Marcus 1956, whose full text
has zero hits for the relevant terms); the regime structure `α = ½[1 + A/λ] (|A| < λ)`, `α = 0`,
`α = 1` at **Cohen & Marcus 1968 Eqs. (5a)–(5c), p. 4250**; the premise set at **Migliore et al.
2014 §6.2**; the two-branch experimental violation at **Salamone et al. 2021**; and the five
`first-hand` data families of §R1.10 (two phenol/HAT solvent columns, one oxidant column, one
CCSD(T) alcohol series; the fifth column is aggregate-only and is therefore `UNSUPPORTED` for
per-point instances). Four classical sources (Evans & Polanyi 1938, Bell 1936, Semenov, Polanyi
1963) remain `not-accessed` and are used **only** for naming/attribution, never for content. The
literature record also carries the honest negatives: no source states `0 ≤ α ≤ 1` as a law of
chemical families; Brønsted 1928 does not state `β_f + β_r = 1`; two popular claims (constant
activation entropy as a *necessary* condition; the diffusion-control `Ea` formula) have zero
first-hand support and are marked declaration-only or uncited.

**中文。** 语句集、区域结构与每个实例数字都依赖 `theories/BEP/LITERATURE.md`（1584 行，§R1–§R1.19），
其中每条源都带可核查位点、`first-hand`/`not-accessed` 状态与**可形式化含义**。里程碑锚点：原理的规范措辞
与"仿射 + 二次余项"形状（IUPAC 术语表及其印刷式）；二次势垒律的正确出处是 **Marcus 1968 Eq. (2), p. 891**
（记录更正了常见的"归给 Marcus 1956"误引：1956 全文对相关术语 0 命中）；区域结构
`α = ½[1 + A/λ]（|A| < λ）`、`α = 0`、`α = 1` 见 **Cohen & Marcus 1968 Eqs. (5a)–(5c), p. 4250**；
前提集的印刷出处是 **Migliore 等 2014 §6.2**；双支实验违例见 **Salamone 等 2021**；五个 `first-hand`
数据族取自 §R1.10（两个酚类 HAT 溶剂列、一个氧化剂列、一个 CCSD(T) 醇系列；第五列只有族汇总，故逐点
实例标为 `UNSUPPORTED`）。四个经典源（Evans & Polanyi 1938、Bell 1936、Semenov、Polanyi 1963）仍为
`not-accessed`，**只用于命名/归属，不用于任何内容主张**。文献记录也保留了诚实的否定结论：没有任何源把
`0 ≤ α ≤ 1` 表述为化学族定律；Brønsted 1928 没有 `β_f + β_r = 1`；两条流行说法（"活化熵恒定是必要条件"、
扩散控制的 `Ea` 公式）一手支持为 0，已分别标为仅声明或不引用。
