# theories/hammond/RESULTS.md — the Hammond postulate, formalized in Lean

> The single bilingual deliverable of the Hammond theory: every section carries the English
> original immediately followed by its Chinese rendering (contract `proofs/ENGINE.yml`,
> language policy in `proofs/ENGINE.md` §1.5). The human request had three parts — (①) turn the
> postulate into a formal description, (②) prove it / find its exact validity conditions,
> (③) plug instances in and decide whether they conform — and the answers are §2, §3, §4 below.
>
> 本文件是 Hammond 理论的唯一双语交付物：每节英文原文后紧跟中文对照。人类需求分三部分 ——
> ①把假说转化为形式化描述、②证明它/找出成立的精确条件、③代入实例判断是否符合 —— 答复分别在
> 下面的 §2、§3、§4。

---

## 1. Executive summary

**Delivered.** Six Lean modules under `PhotoLean/Hammond/` — `Basic.lean` (H1),
`Criterion.lean` (H2), `Sharp.lean` (H3), `Compose.lean` (H4), `RatModel.lean` (H5a),
`Instances.lean` (H5b) — containing **102 declarations: 17 definitions and 85 theorems**, all with
complete proofs: **zero unproved placeholders, zero custom axioms**. Every statement was compiled
*before* any proof work (the statement skeleton, see §2.3), delivered signatures match it
**102/102 word for word**, and every theorem is delivered as **one commit per lemma** —
85 per-lemma commits plus 2 definition commits, 87 worker commits in total.

**The one-sentence result.** In the two-parabola (Marcus-type) model, the transition-state
coordinate is `q‡ = (λ - x)/(2λ)` with driving force `x = -ΔG°`; Hammond's structural trend is
then an exact theorem — *the more exergonic the step, the more reactant-like the transition state* —
and it holds **if and only if `λ > 0`**; the Brønsted/Leffler coefficient **measured from barrier
data** equals `q‡` at the midpoint of the compared pair, lies in `(0,1)` exactly when the crossing
point falls between the two wells, and turns **negative exactly in the Marcus inverted region**,
where the structural-resemblance reading leaves its domain of applicability — not because a
molecule "violates Hammond", but because the crossing point is no longer a structural
intermediate.

**摘要**：交付 6 个 Lean 模块（H1–H5b），共 **102 条声明（17 个定义 + 85 条定理）**，全部完整证明，
**零占位证明、零自定义公理**；所有语句在动证明之前先编译通过（语句骨架），交付签名与之**逐字一致
102/102**，且**每定理一个提交**（87 个提交）。一句话结论：在双抛物面（Marcus 型）模型中，过渡态坐标
`q‡ = (λ - x)/(2λ)`（驱动力 `x = -ΔG°`），Hammond 的结构趋势是一条精确定理 —— *越放能，过渡态越像
反应物* —— 且**成立当且仅当 `λ > 0`**；由**势垒数据测得的** Brønsted/Leffler 系数等于所比较对中点的
`q‡`，它落在 `(0,1)` 内恰好等价于交叉点落在两井之间，并且在 **Marcus 反转区恰好变为负** —— 那里
"结构相似"的解读**离开了它的适用域**，而不是"分子违反了 Hammond 假说"。

---

## 2. Part ① — the formal description

### 2.1 The model (assumptions, all explicit)

Reaction coordinate `q` with the reactant well at `q = 0` and the product well at `q = 1`;
harmonic surfaces of **equal** curvature `2λ`:

```text
reactant surface   E_R(q) = lam * q^2
product  surface   E_P(q) = lam * (q - 1)^2 + dG        (dG = ΔG°; exergonic ⇔ dG < 0)
crossing point     q‡ = tsCoord lam x = (lam - x)/(2 lam)      (driving force x = -dG)
forward barrier    gapReactant lam x = (lam - x)^2 / (4 lam)
reverse barrier    gapProduct  lam x = (lam + x)^2 / (4 lam)
Leffler coefficient (measured, a finite difference of barrier data)
                   lefflerSecant lam x₁ x₂ = -(gapReactant lam x₂ - gapReactant lam x₁)/(x₂ - x₁)
```

**Not derived here** (documented as modeling assumptions, plan §13): one scalar coordinate stands
for molecular structure; the two curvatures are equal; `λ` is held fixed across a compared
pair/series; the transition state is the classical crossing point (no tunneling, no recrossing);
`λ` takes the Marcus reorganization form. **§6 of this file states every boundary of the claim.**

**模型（假设全部显式）**：反应坐标 `q`，反应物井在 `q = 0`、产物井在 `q = 1`，两个谐振面**等曲率**
`2λ`。上式给出交叉点坐标 `q‡`、正/逆势垒、以及由势垒数据**测得**的 Leffler 系数。**以下内容不从
模型推出，只作为建模假设记录**（plan §13）：用一个标量坐标代表分子结构；两面等曲率；比较对内
`λ` 固定；过渡态是经典交点（无隧穿、无再穿越）；`λ` 取 Marcus 重组能形式。**本文件 §6 逐条声明
结论的边界。**

### 2.2 The Lean objects (namespace `PhotoLean.Hammond`)

| Object | Meaning | 含义 |
|---|---|---|
| `reactantSurface`, `productSurface` | the two potential-energy surfaces | 两个势能面 |
| `tsCoord lam x` | transition-state coordinate `q‡` | 过渡态坐标 |
| `gapReactant`, `gapProduct` | forward / reverse barrier | 正/逆势垒 |
| `lefflerSecant lam x₁ x₂` | Leffler/Brønsted coefficient as a **barrier-data observable** (a secant, not a copy of `q‡`) | 由势垒数据测得（割线，**不是** `q‡` 的副本） |
| `ReactionRegion lam x := -lam < x ∧ x < lam` | the crossing point lies strictly between the wells | 交点严格落在两井之间 |
| `ReactantLike`, `ProductLike` | `q‡ < 1/2` (early) / `1/2 < q‡` (late) | 早/晚过渡态 |
| `HammondConforms lam x := 0 < lam ∧ ReactionRegion lam x` | **the instance-level verdict**: "the Hammond description applies to this instance" | **实例级判决**：本模型 Hammond 描述适用于该实例 |
| `HammondDescriptor lam` | `∀ x₁ x₂, x₁ < x₂ → tsCoord lam x₂ < tsCoord lam x₁` — the postulate's trend, family level | 假说的趋势（族级） |
| `HZone` + `hammondZone` | 7-branch structural classifier: `early / half / late / atReactant / atProduct / beyondReactant / beyondProduct` | 七分支结构分类器 |
| `Rat.tsCoordQ`, `Rat.gapReactantQ`, `Rat.lefflerSecantQ`, `Rat.hammondZoneQ` | the same objects over `ℚ`, computable, for instance verdicts | `ℚ` 上同一批对象，可计算，供实例判决 |

**Objects and meaning / 对象与含义**：见上表双语对照。

### 2.3 Statement discipline

The authority is `theories/hammond/probes/hammond-statement-skeleton.lean`: all 102 signatures
were elaborated **before** proof work (0 error). Two statements were corrected before delivery
(recorded in `proofs/API-NOTES.md` and the experience bank): the reverse-barrier identity needed
the product-well reference (`… - dG`), and the verdict characterization had to use the classifier
(the original three-predicate disjunction was a trichotomy tautology). The corrections were
adopted with both sides' kernel counterexamples.

**语句纪律**：语句权威是骨架文件，102 条签名在**动证明之前**全部编译通过（0 error）。交付前修正了
两条语句（记入 API 日志与经验库）：逆势垒恒等式需补产物井参考（`… - dG`）；判决刻化必须用分类器
（原三条符号谓词的析取是三分律恒真式）。两条修正都附双方内核反例。

---

## 3. Part ② — proofs and the exact validity conditions

### 3.1 The Hammond trend is a theorem (H2, `Criterion.lean`)

| Theorem | Statement (natural language) | 中文 |
|---|---|---|
| `tsCoord_antitone` | for `λ>0`, `x₁<x₂ ⇒ q‡(x₂) < q‡(x₁)`: more driving force, earlier TS | `λ>0` 时驱动力越大、过渡态越早 |
| `hammond_descriptor_holds` | for `λ>0` the Hammond descriptor holds for the whole family | `λ>0` 时整族的 Hammond 描述成立 |
| `reactantLike_iff` / `productLike_iff` | exergonic ⇔ reactant-like; endergonic ⇔ product-like (Hammond's operational statement) | 放能 ⇔ 像反应物；吸能 ⇔ 像产物（Hammond 的操作性陈述） |
| `gap_compare_iff` | the TS is closer **in energy** to the reactant well ⇔ it is **reactant-like** | 过渡态在**能量**上更靠近反应物井 ⇔ 它在**结构**上更像反应物 |
| `lefflerSecant_eq_midpoint` | the Brønsted coefficient computed from the model's barrier data **equals** `q‡` at the midpoint — exact, no mean-value theorem (the finite-difference form of Marcus 1968, p. 896, eq. (32)) | 由模型势垒数据算得的 Brønsted 系数**恰等于**中点处的 `q‡`（精确等式，无需中值定理；即 Marcus 1968, p. 896, eq. (32) 的有限差形式） |
| `lefflerSecant_symm` | `α(x)` via a symmetric finite difference equals `q‡(x)` | 对称差分给出逐点 `α(x) = q‡(x)` |
| `lefflerSecant_mem_iff` | `0 < α < 1` ⇔ the crossing point lies strictly between the wells | `0<α<1` ⇔ 交点严格落在两井之间 |
| `tsCoord_lt_zero_iff_inverted` | `q‡ < 0` ⇔ the Marcus inverted region `λ < x` | `q‡<0` ⇔ Marcus 反转区 `λ<x` |
| `lefflerSecant_neg_iff_inverted` | `α < 0` ⇔ the midpoint is in the inverted region | `α<0` ⇔ 中点在反转区 |
| `conforms_iff_zone` | the verdict ⇔ the classifier says early/half/late | 判决 ⇔ 分类器给出早/中/晚 |
| `exists_reactantLike`, `exists_productLike`, `exists_reactionRegion` | the predicates are inhabited (not vacuous) | 谓词非空（不退化为空真） |
| `barrier_eq_gapReactant` | `rfl`-bridge to the already-delivered Marcus barrier — the two theories are about the same object | 与已交付 Marcus 势垒的 `rfl` 桥：两个理论讲同一个对象 |

**Primary locus (literature record §3.2/§10, status `verified`, read first-hand; round 4)**:
Marcus 1968, *J. Phys. Chem.* **72**(3), 891,
`10.1021/j100849a019`, §"Meaning of the Brønsted Slope", printed **p. 896, eq. (32)**:
"`α = ½(1 + ΔF°'/λ)` (32) when `|ΔF°'| ≲ λ`", with the same page describing the coordinate as the
"product-like character" of the transition state. Two consequences used below: the identity is the
model's, but it has a primary locus; and its stated applicability range `|ΔF°'| ≲ λ` **is** our
`ReactionRegion` (`-λ < x < λ`) — the regime boundary is documented upstream, not invented here.

**中心恒等式的原始出处（第 4 轮调研）**：Marcus 1968（`10.1021/j100849a019`）p. 896 eq. (32)：
`α = ½(1 + ΔF°'/λ)`（当 `|ΔF°'| ≲ λ`），同页把该坐标称作过渡态的 "product-like character"。两点后果：
该恒等式是模型内的，但有原始出处；且它自带的适用范围 `|ΔF°'| ≲ λ` **就是**我们的
`ReactionRegion` —— 区域边界有上游文献依据，不是我们自己划的。

### 3.2 The exact validity condition (H3, `Sharp.lean`)

```lean
theorem hammond_sharp (lam : ℝ) : HammondDescriptor lam ↔ 0 < lam
```

Both failure branches come with **explicit two-point counter-witnesses** (not a negated
quantifier): `exists_direction_reversal_of_neg` for `λ<0` (the coordinate then *increases* with
driving force) and `exists_direction_reversal_of_eq` for `λ=0` (by the division-by-zero
convention the coordinate is constant, and a constant cannot be strictly decreasing). The
witnesses are `(x₁,x₂) = (0,1)` and the necessity proof consumes them inside all three branches of
`lt_trichotomy` (kernel-verified).

**精确的成立条件**：`HammondDescriptor lam ↔ 0 < lam`。两个失效分支都给出**显式两点反例见证**
（不是"否定全称量词"）：`λ<0` 时坐标随驱动力**递增**；`λ=0` 时按除零约定坐标恒定，而恒定不可能严格
递减。见证取 `(0,1)`，必要性证明在 `lt_trichotomy` 的三个分支里真正消耗它们（内核级已核）。

### 3.3 Where the condition comes from microscopically (H4, `Compose.lean`)

```lean
theorem hammond_descriptor_of_inner {kk dq} (hkk : 0 < kk) (hdq : dq ≠ 0) :
    HammondDescriptor (Marcus.lamInner kk dq)
theorem hammond_descriptor_of_microscopic {kk dq dE a1 a2 R nSq epsS} (…) (hPekar : 1/epsS < 1/nSq) :
    HammondDescriptor (Marcus.lamInner kk dq + Marcus.lamOuter dE a1 a2 R nSq epsS)
theorem hammond_descriptor_of_nonoverlap (… hRge : a1 + a2 ≤ R …) : HammondDescriptor (…)
theorem exists_reactionRegion_of_microscopic (…) : ∃ x, ReactionRegion (…) x
```

A positive molecular force constant with a non-zero geometry change, or the full Marcus
reorganization energy (inner + outer with the Pekar factor and the geometric factor), makes the
curvature positive and hence the description valid. **Note the difference from the Marcus rate
result: there is no `A`, `kB`, `T` in any premise** — the structural statement is
temperature-independent, so its assumptions are strictly weaker.

**微观来源**：力常数为正且几何位移非零，或完整的 Marcus 重组能（内层 + 外层，含 Pekar 因子与几何
因子），都使曲率为正、描述成立。**与 Marcus 速率版的差异：前提里没有 `A`、`kB`、`T`** —— 结构陈述
与温度无关，假设更弱、结论更强。

---

## 4. Part ③ — instance verdicts (H5, `RatModel.lean` + `Instances.lean`)

The decision layer mirrors everything on `ℚ` (computable) with transfer lemmas
(`tsCoordQ_cast`, `hammondZoneQ_eq_hammondZone`, …), so a rational computation is **binding for the
real theory**. `Conforms` means `HammondConforms`; every verdict below is a kernel-checked theorem
(29 of them), not a comment.

| # | Instance | `λ` | `x = -ΔG°` | `q‡` | verdict | 中文判决 |
|---|---|---|---|---|---|---|
| I1 | thermoneutral | 1 | 0 | `1/2` | conforms; TS halfway (`half`) | 符合；过渡态恰好居中 |
| I2 | mildly exergonic | 1 | `3/4` | `1/8` | conforms; reactant-like (`early`) | 符合；像反应物（早） |
| I3 | endergonic | 1 | `-1/2` | `3/4` | conforms; product-like (`late`) | 符合；像产物（晚） |
| I4 | barrierless point | 1 | 1 | `0` | **boundary**: `¬ HammondConforms` (strict regime fails) while `HammondDescriptor 1` still holds — the two levels differ | **边界**：点级判决不成立，但族级描述仍成立 —— 两个层次确实不同 |
| I5 | literature MCC, normal region | `6/5` | `1/20` | `23/48` | conforms (`early`) | 符合 |
| I6 | literature MCC, inverted region | `6/5` | `12/5` | `-1/2` | **outside the domain** (`beyondReactant`); also `Marcus.InvertedRegion`; measured secant over `3/5→12/5` is `-1/8 < 0` | **落在适用域之外**；同时是 Marcus 反转区；测得的割线为负 |
| I7 | literature reaction centre, deep inverted | `1/4` | `11/10` | `-17/10` | **outside the domain** (`beyondReactant`) | **落在适用域之外** |
| I8 | non-physical curvature | `-1/2`, `0` | any | — | **rejected**: `¬ HammondDescriptor` in both branches; no `x` satisfies the regime | **拒收**：两个分支描述都不成立；没有任何 `x` 落在区域内 |
| I9 | MCC pair `3/5 → 12/5` | `6/5` | `3/5`, `12/5` | descending | `tsCoord (12/5) < tsCoord (3/5)` — the Hammond direction instantiated on literature parameters | 在文献参数上实例化 Hammond 方向 |
| I10 | non-vacuity on literature parameters | `6/5` | `±1/20` | — | `ReactantLike ∧ ProductLike` both inhabited | 两类谓词都非空 |

Table note: for I2/I3 the `q‡` cells are values computed from the definitions (independently
recomputed by two verifiers); the *delivered* theorems of those rows are the zone and verdict
statements (`inst_I2_exergonic_zone/_reactantLike/_conforms`, `inst_I3_endergonic_*`). Rows I1, I4,
I5, I6, I7 do carry a delivered coordinate theorem (`inst_*_coord`).

Values come from `theories/hammond/LITERATURE.md` §6 (the MCC series `λ = 1.20 eV` — the sum of the
`λ_s = 0.75` and `λ_v = 0.45 eV` annotations legible inside Nobel 1992 Fig. 8 — and the reaction
centre `λ ≈ 0.25 eV`; the driving forces are the sibling record's C&EN-based values and the
Nobel-lecture "~" numbers). **Wording rule honoured**: I6/I7 say "outside the domain of
applicability of the model's Hammond description"; they never say that a molecule violates
Hammond's postulate, and no instance theorem asserts anything about measured rates or structures.

**实例判决**：判定层在 `ℚ` 上复制了全部对象并给出转移引理，因此有理数计算对实数理论**有约束力**。
上表 10 组实例、29 条内核可检验的判决定理：4 组符合（I1/I2/I3/I5）、1 组落在边界（I4：点级不成立、
族级成立）、3 组落在适用域之外（I6/I7 及反转区对，I9 给出结构单调方向）、非物理分支被拒收（I8）、
谓词非空（I10）。参数取自 `LITERATURE.md` §6（MCC 系列 `λ = 1.20 eV`，来自 Nobel 1992 图 8 内可读的
`λ_s = 0.75` 与 `λ_v = 0.45 eV` 标注之和；反应中心 `λ ≈ 0.25 eV`）。**措辞铁律已遵守**：I6/I7 写的是
"落在本模型 Hammond 描述的适用域之外"，绝无"分子违反 Hammond 假说"，也没有任何实例定理对实测速率
或结构作断言。

---

## 5. Evidence and independent verification

| Check | Command / artifact | Result |
|---|---|---|
| Compile | `proofs/scripts/lake build PhotoLean.Hammond.<M>` for all six modules | Build completed successfully (0 warning) |
| Gate (build + placeholder/axiom scan) | `proofs/scripts/check.sh --strict <M>`, and bare `check.sh --strict` | all PASS, scan clean |
| Axiom discipline | `proofs/scripts/axioms.sh <M> <thm>` for **every** theorem | 85/85 `verdict: PASS (only mathlib infrastructure axioms)` (`propext`, `Classical.choice`, `Quot.sound`) |
| Statement fidelity | `python3 theories/hammond/probes/hammond-fidelity.py` | 102/102 word-for-word, 0 differences, 0 extra declarations |
| Commit discipline | `git log --oneline` + `git show --stat` | 87 worker commits: one per theorem (+ one per file for the definitions); each commit touches exactly its owner's file |
| Independent numeric cross-check (lead) | `python3 theories/hammond/probes/hammond-instance-check.py` | exact rationals reproduce I5 `23/48`, I6 `-1/2`, I7 `-17/10`, secant `-1/8`, reverse-barrier identity |
| Falsification audit (independent prover) | `theories/hammond/probes/hammond-audit-b.lean` — 99 kernel checks + 41 `#print axioms` | no false statement, no vacuous hypothesis; hypothesis-necessity counterexamples for every main premise |
| Independent verifier, batch 1 (H1 + H5a) | read-only reviewer, own fidelity implementation, own probes | **PASS / PASS** — 31/31 axioms clean, 48/48 declarations verbatim by a second implementation, 15-point classifier grid on both `ℝ` and `ℚ`, 7 necessity counterexamples |
| Independent verifier, batch 2 (H2 + H3) | read-only reviewer, own signature parser, own necessity probes, `#print` proof-term inspection | **PASS / PASS** — 21/21 axioms clean; `lefflerSecant` shown to be barrier-data only and its key theorem a real computation (not `rfl`); `hammond_sharp`'s proof is `⟨necessity, H2⟩` with both reversal witnesses consumed across all three `lt_trichotomy` branches |
| Independent verifier, batch 3 (H4 + H5b) | read-only reviewer, own recomputation from the definitions, mechanical premise diff | **PASS / PASS** — 33/33 axioms clean; H4 calls only the delivered Marcus lemmas; dropping `hPekar` makes the descriptor fail (`lamInner + lamOuter = -2/3`, kernel counterexample); all 29 instance verdicts traced through the ℚ→ℝ transfer chain; independent values `23/48`, `-1/2`, `-17/10`, secant `-1/8` |
| Frozen-state pass (after the comment-only edits) | read-only reviewer on the frozen revision | see `theories/hammond/TASKS.md` notes |

**证据**：六模块编译 0 warning；`check.sh --strict` 全通过（含裸跑全树）；**85/85** 定理 `#print axioms`
只含允许的三条基础设施公理；保真 **102/102** 逐字一致；**87** 个工人提交、每定理一个且只动属主文件；
lead 的独立数值对拍、prover_b 的 99 条对抗性审计、verifier 的三批只读独立验收（批次 1 已判
**H1 PASS / H5a PASS**，批次 2/3 的判决记入任务板验收表）。

---

## 6. Honest boundaries (what this does NOT claim)

1. **Literature wording.** The famous sentence "the transition state resembles the species to which it
   is closest in energy" is a **later paraphrase**; Hammond 1955 (p. 334) says verbatim "If two states
   … have nearly the same energy content, their interconversion will involve only a small
   reorganization of the molecular structures", with the consequence "In highly exothermic steps it
   will be expected that the transition states will resemble reactants closely and in endothermic
   steps the products will provide the best models for the transition states."
2. **Regime boundary and identity have upstream loci but stay model-internal.** Marcus 1968 eq. (32)
(p. 896) states the α formula with the explicit range `|ΔF°'| ≲ λ` — i.e. `ReactionRegion` — and the
same page calls the coordinate the "product-like character" of the TS; so the energy–structure link
is *derived inside the parabolic model* upstream as well. What no source states is the
*inverted-region* sign flip as an identity (next item).
3. **The inverted-region sign flip is a model theorem, not a literature identity.** No source found by
   the survey states "inverted region ⇔ Brønsted slope < 0" as an identity; the statement-level
   support is the Nobel lecture's Brønsted/Tafel analogy (p. 82) plus the slope formula of Cohen &
   Marcus 1968 / Marcus 1968, with García-Padilla & Qiu 2025 as the modern published analogue.
   `0 < α < 1` is likewise **model-internal** (measured α's can lie outside `(0,1)`, e.g. the
   nitroalkane anomaly).
4. **The postulate is a heuristic with many exceptions** (IUPAC calls it a *hypothesis*; "many
   exceptions"; no general computational verification; no photochemical analogue). This project
   proves one exact realization inside one model, not the postulate itself.
5. **Model scope.** One scalar coordinate; equal curvatures; `λ` fixed across the compared series;
   classical crossing point. With unequal curvatures the `α = q‡` identity degrades (Villegas-Escobar
   2026) — recorded as the first next station.
6. **Instance scope.** Only electron-transfer parameter sets receive verdicts; bond-breaking
   proton/atom/methyl transfer may not be given a `beyondReactant` verdict (Nobel p. 90; Marcus 1968
   Appendix II). Provenance is documented per instance (the MCC driving forces are secondary-source
   values; the reaction-centre numbers are the lecture's "~" values).
7. **Two statements were corrected before delivery** and one delivered statement family is weaker
   than the sharpest provable form (documented, not changed): `tsCoord_mem_iff`'s `0 < lam` could be
   `0 ≤ lam`; the `0 < lam` hypothesis of `hammondZone_eq_{early,late,atReactant}_iff` is redundant;
   `atProduct` needs only `lam ≠ 0`; the `lam ≠ 0` hypotheses of the two crossing identities and of
   `tsCoord_at_lam` are redundant. A redundant hypothesis is a *weaker statement*, not a defect — but
   it is recorded rather than hidden.
8. **No claim about measured rates or structures.** The rate-level theory is the previously delivered
   `PhotoLean/Marcus/` layer; this theory never asserts that a real system's rate or geometry follows
   the model.

**诚实边界**：① 广为流传的"最接近能量者"是转述，Hammond 1955 原文另有措辞；② 反转区与斜率反号在
文献里**没有**现成的恒等式，本文给出的是**模型定理**（支撑：Nobel 讲演 p.82 的类比 + 1968 两篇的斜率
公式 + 2025 年发表的现代类似物），`0<α<1` 同样是模型内部刻画；③ 假说本身是启发式（IUPAC 定性为
*hypothesis*、有"many exceptions"），本项目只是把其中一个精确实现做成定理；④ 模型范围：单坐标、等曲率、
系列内 `λ` 固定、经典交点 —— 不等曲率会让 `α = q‡` 退化（列为下一站）；⑤ 实例范围只限电子转移参数，
断键型质子/原子/甲基转移不得给"反转区"判决；⑥ 交付前修正的两条语句与**弱于最锐形式**的若干前提都如实
记录（冗余前提是"更弱的陈述"，不是缺陷）；⑦ 不对实测速率与结构作任何断言。

---

## 7. Reproduce

```bash
# statements (authority), falsification audit, numeric cross-checks
proofs/scripts/lake env lean theories/hammond/probes/hammond-statement-skeleton.lean   # 0 error (placeholders allowed here)
proofs/scripts/lake env lean theories/hammond/probes/hammond-lead-audit.lean           # 0 error
proofs/scripts/lake env lean theories/hammond/probes/hammond-audit-b.lean              # 0 error
python3 theories/hammond/probes/hammond-fidelity.py                                    # 102/102
python3 theories/hammond/probes/hammond-instance-check.py                              # exact rationals
# acceptance gate per module, and the frozen full-tree gate
for M in Basic Criterion Sharp Compose RatModel Instances; do proofs/scripts/check.sh --strict PhotoLean.Hammond.$M; done
proofs/scripts/check.sh --strict
proofs/scripts/axioms.sh PhotoLean.Hammond.Instances PhotoLean.Hammond.inst_I6_mcc_inverted_notConforms
```

**复现**：上列命令依次给出语句骨架、lead 审计探针、prover_b 对抗审计（均 0 error）、保真 102/102、
精确有理数对拍、逐模块验收门与冻结全树门。

---

## 8. Next stations

① **Unequal curvatures** `λ_R ≠ λ_P`: monotonicity survives, the affine `α` does not (the sharpest
boundary of this theory). ② Anharmonic surfaces: the secant identity becomes a mean-value
inequality. ③ Dynamical recrossing / variational TS: needs a dynamics layer outside mathlib.
④ Photochemical analogues: the literature records no established photochemical Hammond principle.

**下一站**：① 不等曲率（单调性仍在，仿射 `α` 失效 —— 本理论最锋利的边界）；② 非谐振面（割线恒等式
退化为中值不等式）；③ 动力学再穿越/变分过渡态（需要 mathlib 之外的动力学层）；④ 光化学类比
（文献记录：尚无公认的光化学 Hammond 原理）。
