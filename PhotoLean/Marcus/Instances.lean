/-
PhotoLean.Marcus.Instances — M5b 第一批：实例代入与区域判定（人类需求第三部分）。

需求原文：「用一些实例代入这个形式化理论，判断该实例是否会符合马库斯反转区的描述」。
本文件把每个实例的 `(lam, x)` 代进 M1 的描述层，给出**有名字的判定定理**：
判定结论不是文档里的声称，而是由内核检查的证明项给出（`plan.md` §11 的 M5 附加要求）。

**判定证据链（两层，缺一不可）**

  1. **内核计算**（ℚ 判定层，M5a `PhotoLean.Marcus.Rat.zoneQ`）：`(lam, x)` 落在哪个区
     由内核算出。
     * 整数参数：`by decide` —— 内核把 `Rat` 的比较与 `Zone` 的构造子索引归约到底；
     * 含除法 / 小数的有理参数：`by norm_num [Rat.zoneQ]` ——
       `by decide` 在 `Rat` 的 gcd 归约上卡住（实测报 `'Decidable' instance did not reduce`，
       见 `proofs/API-NOTES.md` F-2）。
  2. **转移引理**：把 ℚ 上的判定值搬到 ℝ 理论层。
     M5a 提供 `Rat.zoneQ_eq_zone` / `Rat.zoneQ_inverted_iff`；本文件补上正常区方向的两条
     （`normalRegion_of_zoneQ_normal` / `not_invertedRegion_of_zoneQ_normal`）。
     ℝ 十进制字面量与 ℚ 分数字面量之间的桥接是**显式**的 `norm_num` 等式
     （如 `(1.20 : ℝ) = ((120 : ℚ) / 100 : ℚ)`），不是隐含的 coercion 猜想。

**参数来源**：`plan.md` §8.3 与 `proofs/LITERATURE.md` §实例参数候选表（只用「已核实」条目）。
约定 `x := -ΔG°`（放能取正）；**区域判定只用 `(lam, x)`**，与 `A`、`kB`、`T` 无关
（`plan.md` §8.3：`T = 298.15 K` 只是建模取值，不声称它是某实验的真实温度）。
所有物理参数都**显式写在语句里**，不折进定义（`plan.md` §2.4 的证明纪律）。

**本批范围**：只含**区域判定** I1–I6（Sprint 3 的 I1–I3 区域部分 + Sprint 5 的文献参数部分），
不依赖 `Rate` / `Sharp`。依赖速率比较与描述算子的条目登记在文末，留待后续里程碑追加。

**实测偏差记录（写给 verifier）**：任务书参考片段里的 `rw [← Rat.zoneQ_eq_zone] at h`
方向是反的 —— `←` 的改写模式是 `zone ↑?lam ↑?x`，与目标里的 `Rat.zoneQ 1 3` 对不上，
实测报 `did not find instance of the pattern`；正确写法是**正向** `rw [Rat.zoneQ_eq_zone] at h`。
另外 `rw` 不展开 `InvertedRegion` / `NormalRegion` 这类 `def`（它不走 defeq），
故本文件统一用 `unfold` + 显式桥接等式。以下写法全部在 mathlib v4.17.0 上实测编译通过。

**注**：文件头刻意不写出被 `check.sh --strict` 扫描的关键字字面量（块注释同样在扫描范围内）。

验收（契约 `proofs/ENGINE.yml`）：
  proofs/scripts/lake build PhotoLean.Marcus.Instances
  proofs/scripts/check.sh --strict PhotoLean.Marcus.Instances
  proofs/scripts/axioms.sh PhotoLean.Marcus.Instances PhotoLean.Marcus.inst_I1_inverted

English: PhotoLean.Marcus.Instances — M5b batch 1: instance substitution and region decisions
(human requirement, part three).

Original requirement (quoted verbatim in Chinese above): 'Substitute some instances into this
formalized theory, and decide whether the instance matches the description of the Marcus
inverted region.'
This file substitutes each instance's `(lam, x)` into the M1 description layer and produces
**named decision theorems**: the decision is not a claim written in a document, but a proof term
checked by the kernel (the extra M5 requirement of `plan.md` §11).

**The decision evidence chain (two layers, both indispensable)**

  1. **Kernel computation** (the ℚ decision layer, M5a `PhotoLean.Marcus.Rat.zoneQ`): which
     region `(lam, x)` falls into is computed by the kernel.
     * Integer parameters: `by decide` — the kernel reduces the comparison on `Rat` and the
       constructor indices of `Zone` down to the ground;
     * Rational parameters with division / decimals: `by norm_num [Rat.zoneQ]` —
       `by decide` gets stuck on the gcd reduction of `Rat` (the observed message is
       `'Decidable' instance did not reduce`, see `proofs/API-NOTES.md` F-2).
  2. **Transfer lemmas**: lift the ℚ-level decision value to the ℝ theory layer.
     M5a provides `Rat.zoneQ_eq_zone` / `Rat.zoneQ_inverted_iff`; this file adds the two lemmas
     for the normal-region direction (`normalRegion_of_zoneQ_normal` /
     `not_invertedRegion_of_zoneQ_normal`). The bridge between ℝ decimal literals and ℚ
     fractional literals is an **explicit** `norm_num` equation
     (e.g. `(1.20 : ℝ) = ((120 : ℚ) / 100 : ℚ)`), not an implicit coercion conjecture.

**Where the parameters come from**: `plan.md` §8.3 and the candidate-instance-parameter table in
`proofs/LITERATURE.md` (only entries with verification status 'verified').
Convention: `x := -ΔG°` (exergonic values are taken positive); **region decisions use
`(lam, x)` only** and are independent of `A`, `kB`, `T` (`plan.md` §8.3: `T = 298.15 K` is
merely a modelling value, and no claim is made that it is the true temperature of any
experiment). All physical parameters are written **explicitly in the statements** and are not
folded into definitions (the proof discipline of `plan.md` §2.4).

**Scope of this batch**: only the **region decisions** I1–I6 (the region part of Sprint 3's
I1–I3 plus the literature-parameter part of Sprint 5), independent of `Rate` / `Sharp`.
Entries that depend on rate comparisons and the descriptor operator are registered at the end
of the file, to be appended in later milestones.

**Observed deviation record (for the verifier)**: in the reference snippet of the task brief the
direction of `rw [← Rat.zoneQ_eq_zone] at h` is reversed — the rewrite pattern of `←` is
`zone ↑?lam ↑?x`, which does not match `Rat.zoneQ 1 3` in the goal; the observed error is
`did not find instance of the pattern`, and the correct form is the **forward** rewrite
`rw [Rat.zoneQ_eq_zone] at h`. Moreover, `rw` does not unfold `def`s such as `InvertedRegion` /
`NormalRegion` (it does not go through defeq), so this file uniformly uses `unfold` plus
explicit bridging equations. All the forms below were compiled and tested on mathlib v4.17.0.

**Note**: the file header deliberately does not spell out the keyword literals scanned by
`check.sh --strict` (block comments are inside the scan range as well).

Acceptance (contract `proofs/ENGINE.yml`):
  proofs/scripts/lake build PhotoLean.Marcus.Instances
  proofs/scripts/check.sh --strict PhotoLean.Marcus.Instances
  proofs/scripts/axioms.sh PhotoLean.Marcus.Instances PhotoLean.Marcus.inst_I1_inverted
-/
import PhotoLean.Marcus.RatModel
import PhotoLean.Marcus.Sharp

namespace PhotoLean.Marcus

/-! ## I1 — 纯数实例：`lam = 1, x = 3`（反转区）

证据链 1：`Rat.zoneQ 1 3` 走整数参数路径，`by decide` 由内核算出 `Zone.inverted`。
证据链 2：`Rat.zoneQ_inverted_iff` 把判定搬到 ℝ 层；ℝ 侧的两个字面量各自用
`norm_num` 桥接到 ℚ 分数字面量（`(1 : ℝ) = ↑(1 : ℚ)`、`(3 : ℝ) = ↑(3 : ℚ)`），
再由 `InvertedRegion` 的定义读出判定结论。

English: ## I1 — A pure-numeric instance: `lam = 1, x = 3` (inverted region)

Evidence chain 1: `Rat.zoneQ 1 3` takes the integer-parameter path, and `by decide` lets the
kernel compute `Zone.inverted`.
Evidence chain 2: `Rat.zoneQ_inverted_iff` moves the decision up to the ℝ layer; the two literals
on the ℝ side are each bridged to a ℚ fractional literal by `norm_num`
(`(1 : ℝ) = ↑(1 : ℚ)`, `(3 : ℝ) = ↑(3 : ℚ)`), and the decision conclusion is then read off from
the definition of `InvertedRegion`.
-/

/-- I1 判定（内核计算）：`lam = 1, x = 3` 落在反转区。

English: I1 decision (kernel computation): `lam = 1, x = 3` lies in the inverted region.
-/
theorem inst_I1_zoneQ : Rat.zoneQ (1 : ℚ) 3 = Zone.inverted := by decide

/-- I1 判定结论：`lam = 1, x = 3` 符合反转区描述的前提（`InvertedRegion`）。

English: I1 decision conclusion: `lam = 1, x = 3` satisfies the premise of the inverted-region
description (`InvertedRegion`).
-/
theorem inst_I1_inverted : InvertedRegion (1 : ℝ) 3 := by
  have h : (((1 : ℚ)) : ℝ) < (((3 : ℚ)) : ℝ) :=
    (Rat.zoneQ_inverted_iff (1 : ℚ) 3).mp inst_I1_zoneQ
  have hl : (1 : ℝ) = (((1 : ℚ)) : ℝ) := by norm_num
  have hx : (3 : ℝ) = (((3 : ℚ)) : ℝ) := by norm_num
  unfold InvertedRegion
  rw [hl, hx]
  exact h

/-! ## 判定证据链 2 的辅助引理（ℚ 判定值 ⇒ ℝ 判定）

M5a 的 `Rat.zoneQ_inverted_iff` 已经覆盖反转区方向；这里补上**正常区**方向的两条，
使得 I2 / I5 的「不符合反转区」判定同样由 ℚ 层的判定值（内核算出）推出，而不是靠数值巧合。
`rw [← Rat.zoneQ_eq_zone]` 在这里方向正确：目标形如 `zone ↑lam ↑x = _`，`←` 的模式
`zone ↑?lam ↑?x` 能对上。

English: ## Auxiliary lemmas for decision evidence chain 2 (ℚ decision value ⇒ ℝ decision)

M5a's `Rat.zoneQ_inverted_iff` already covers the inverted-region direction; here we add the two
lemmas for the **normal-region** direction, so that the 'does not match the inverted region'
decisions for I2 / I5 are likewise derived from the ℚ-layer decision value (computed by the
kernel), instead of relying on a numerical coincidence.
The direction of `rw [← Rat.zoneQ_eq_zone]` is correct here: the goal has the shape
`zone ↑lam ↑x = _`, which the `←` pattern `zone ↑?lam ↑?x` does match.
-/

/-- 转移引理（正常区）：ℚ 层判 `normal` ⇒ ℝ 层 `NormalRegion`（即 `x < lam`）。

English: Transfer lemma (normal region): a ℚ-layer decision of `normal` ⇒ the ℝ-layer
`NormalRegion` (i.e. `x < lam`).
-/
theorem normalRegion_of_zoneQ_normal {lam x : ℚ} (h : Rat.zoneQ lam x = Zone.normal) :
    NormalRegion (lam : ℝ) (x : ℝ) := by
  have h1 : zone (lam : ℝ) (x : ℝ) = Zone.normal := by
    rw [← Rat.zoneQ_eq_zone]
    exact h
  exact (zone_eq_normal_iff (lam : ℝ) (x : ℝ)).mp h1

/-- 转移引理（排除反转区）：ℚ 层判 `normal` ⇒ ℝ 层**不**在反转区。

证明只用 M5a 的接口：若 ℝ 侧真的落在反转区，`Rat.zoneQ_inverted_iff` 会迫使
ℚ 层判定为 `inverted`，与已算出的 `normal` 矛盾（`Zone` 的构造子互异由 `by decide` 给出）。

English: Transfer lemma (ruling out the inverted region): a ℚ-layer decision of `normal` ⇒
the ℝ layer is **not** in the inverted region.

The proof uses only M5a's interface: if the ℝ side really were in the inverted region,
`Rat.zoneQ_inverted_iff` would force the ℚ-layer decision to be `inverted`, contradicting the
already computed `normal` (the distinctness of `Zone`'s constructors is supplied by `by decide`).
-/
theorem not_invertedRegion_of_zoneQ_normal {lam x : ℚ} (h : Rat.zoneQ lam x = Zone.normal) :
    ¬ InvertedRegion (lam : ℝ) (x : ℝ) := by
  intro hinv
  have hq : Rat.zoneQ lam x = Zone.inverted := (Rat.zoneQ_inverted_iff lam x).mpr hinv
  rw [h] at hq
  exact absurd hq (by decide)

/-! ## I2 — 纯数实例：`lam = 1, x = 3/4`（正常区）

证据链 1：`x = 3/4` 是**含除法**的有理字面量，`by decide` 会卡在 `Rat` 的 gcd 归约上，
故走 `by norm_num [Rat.zoneQ]`（`proofs/API-NOTES.md` F-2 的实测结论）。
证据链 2：ℚ 层的 `normal` 判定经 `not_invertedRegion_of_zoneQ_normal` 搬到 ℝ 层，
得到「该实例**不符合**反转区描述的前提」这一否定判定。

English: ## I2 — A pure-numeric instance: `lam = 1, x = 3/4` (normal region)

Evidence chain 1: `x = 3/4` is a rational literal that **involves division**, so `by decide` gets
stuck on the gcd reduction of `Rat`; hence the `by norm_num [Rat.zoneQ]` route is taken (an
observed conclusion recorded in `proofs/API-NOTES.md` F-2).
Evidence chain 2: the ℚ-layer decision `normal` is moved to the ℝ layer by
`not_invertedRegion_of_zoneQ_normal`, which yields the negative decision 'this instance **does
not** satisfy the premise of the inverted-region description'.
-/

/-- I2 判定（内核计算）：`lam = 1, x = 3/4` 落在正常区。

English: I2 decision (kernel computation): `lam = 1, x = 3/4` lies in the normal region.
-/
theorem inst_I2_zoneQ : Rat.zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by norm_num [Rat.zoneQ]

/-- I2 判定结论：`lam = 1, x = 3/4` **不符合**反转区描述的前提。

English: I2 decision conclusion: `lam = 1, x = 3/4` **does not** satisfy the premise of the
inverted-region description.
-/
theorem inst_I2_not_inverted : ¬ InvertedRegion (1 : ℝ) (3 / 4) := by
  intro hinv
  have hl : (1 : ℝ) = (((1 : ℚ)) : ℝ) := by norm_num
  have hx : (3 / 4 : ℝ) = (((3 : ℚ) / 4 : ℚ) : ℝ) := by norm_num
  unfold InvertedRegion at hinv
  rw [hl, hx] at hinv
  exact not_invertedRegion_of_zoneQ_normal inst_I2_zoneQ hinv

/-! ## I3 — 文献参数·无势垒点附近：MCC 系列 `lam = 1.20, x = 1.23`

来源：`plan.md` §8.3 与 `proofs/LITERATURE.md` §实例参数候选表（核实状态 `已核实`）——
Miller–Calcaterra–Closs 联苯–androstane–受体自由基负离子（流体溶液，间距 10 Å）：
`lam = lam_s(0.75) + lam_v(0.45) = 1.20` eV，最优（近无势垒）驱动力 `x ≈ 1.23` eV，
文献给出 `ΔG‡ ≈ 0.0002` eV。
势垒值由 M1 的 `barrier` 定义**直接算出**：`(1.20 - 1.23)^2 / (4 · 1.20) = 0.0001875` eV
（0.1875 meV，与文献的 0.2 meV 量级一致）。该数值是定理，不是注释里的声称。
区域判定：`1.20 < 1.23`，形式判定为**反转区** —— 与文献「近无势垒」并不矛盾：
势垒虽小但严格为正，反应仍在反转区一侧。

English: ## I3 — Literature parameters, near the barrierless point: the MCC series
`lam = 1.20, x = 1.23`

Source: `plan.md` §8.3 and the candidate-instance-parameter table in `proofs/LITERATURE.md`
(verification status 'verified') — Miller–Calcaterra–Closs biphenyl–androstane–acceptor radical
anion (fluid solution, separation 10 Å): `lam = lam_s(0.75) + lam_v(0.45) = 1.20` eV, optimal
(near-barrierless) driving force `x ≈ 1.23` eV, with the literature reporting `ΔG‡ ≈ 0.0002` eV.
The barrier value is **computed directly** from the M1 `barrier` definition:
`(1.20 - 1.23)^2 / (4 · 1.20) = 0.0001875` eV (0.1875 meV, consistent with the literature's
order of magnitude of 0.2 meV). This number is a theorem, not a claim made in a comment.
Region decision: `1.20 < 1.23`, formally decided as the **inverted region** — which does not
contradict the literature's 'near-barrierless': the barrier, though small, is strictly positive,
so the reaction still lies on the inverted-region side.
-/

/-- I3 判定（内核计算）：文献最优点的势垒值 `barrier 1.20 1.23 = 0.0001875` eV。

English: I3 decision (kernel computation): the barrier value at the literature optimum is
`barrier 1.20 1.23 = 0.0001875` eV.
-/
theorem inst_I3_barrier_value : barrier (1.20 : ℝ) 1.23 = 0.0001875 := by norm_num [barrier]

/-- I3 判定（内核计算）：ℚ 层把 `(1.20, 1.23)` 判为反转区。

English: I3 decision (kernel computation): the ℚ layer decides `(1.20, 1.23)` to be in the
inverted region.
-/
theorem inst_I3_zoneQ : Rat.zoneQ ((120 : ℚ) / 100) ((123 : ℚ) / 100) = Zone.inverted := by
  norm_num [Rat.zoneQ]

/-- I3 判定结论：`lam = 1.20, x = 1.23` 落在反转区。

English: I3 decision conclusion: `lam = 1.20, x = 1.23` lies in the inverted region.
-/
theorem inst_I3_inverted : InvertedRegion (1.20 : ℝ) 1.23 := by
  have h : (((120 : ℚ) / 100 : ℚ) : ℝ) < (((123 : ℚ) / 100 : ℚ) : ℝ) :=
    (Rat.zoneQ_inverted_iff _ _).mp inst_I3_zoneQ
  have hl : (1.20 : ℝ) = (((120 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  have hx : (1.23 : ℝ) = (((123 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  unfold InvertedRegion
  rw [hl, hx]
  exact h

/-! ## I4 — 文献参数·反转区：MCC 系列 `lam = 1.20`，`x = 2.40` 与 `x = 2.00`

来源同上（`已核实`）：MCC 实验系列的两个放能性取值（2.40 为系列上界，2.00 为内插刻度值），
二者都满足 `x > lam = 1.20` ⇒ **反转区**。这正是「马库斯反转区」的实验落点：
**在经典模型内**，驱动力超过重组能后速率随放能性增大而下降
（速率下降的机器检查版本见本文件后半的 `inst_I4_mcc_rate_drop`；
按 `plan.md` §8.3 的定量警示，**不得**读作对实验速率的断言）。

English: ## I4 — Literature parameters, inverted region: the MCC series `lam = 1.20`,
`x = 2.40` and `x = 2.00`

Source as above ('verified'): two exergonicity values of the MCC experimental series (2.40 is the
series' upper bound, 2.00 is an interpolated scale value); both satisfy `x > lam = 1.20`
⇒ **inverted region**. This is precisely the experimental locus of the 'Marcus inverted region':
**within the classical model**, once the driving force exceeds the reorganization energy the rate
decreases as exergonicity grows (the machine-checked version of the rate drop is
`inst_I4_mcc_rate_drop` later in this file; per the quantitative warning of `plan.md` §8.3 it
**must not** be read as an assertion about experimental rates).
-/

/-- I4 判定（内核计算）：ℚ 层把 `(1.20, 2.40)` 判为反转区。

English: I4 decision (kernel computation): the ℚ layer decides `(1.20, 2.40)` to be in the
inverted region.
-/
theorem inst_I4_mcc_x240_zoneQ : Rat.zoneQ ((120 : ℚ) / 100) ((240 : ℚ) / 100) = Zone.inverted := by
  norm_num [Rat.zoneQ]

/-- I4 判定结论：`lam = 1.20, x = 2.40` 落在反转区。

English: I4 decision conclusion: `lam = 1.20, x = 2.40` lies in the inverted region.
-/
theorem inst_I4_mcc_x240 : InvertedRegion (1.20 : ℝ) 2.40 := by
  have h : (((120 : ℚ) / 100 : ℚ) : ℝ) < (((240 : ℚ) / 100 : ℚ) : ℝ) :=
    (Rat.zoneQ_inverted_iff _ _).mp inst_I4_mcc_x240_zoneQ
  have hl : (1.20 : ℝ) = (((120 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  have hx : (2.40 : ℝ) = (((240 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  unfold InvertedRegion
  rw [hl, hx]
  exact h

/-- I4 判定（内核计算）：ℚ 层把 `(1.20, 2.00)` 判为反转区。

English: I4 decision (kernel computation): the ℚ layer decides `(1.20, 2.00)` to be in the
inverted region.
-/
theorem inst_I4_mcc_x200_zoneQ : Rat.zoneQ ((120 : ℚ) / 100) ((200 : ℚ) / 100) = Zone.inverted := by
  norm_num [Rat.zoneQ]

/-- I4 判定结论：`lam = 1.20, x = 2.00` 落在反转区。

English: I4 decision conclusion: `lam = 1.20, x = 2.00` lies in the inverted region.
-/
theorem inst_I4_mcc_x200 : InvertedRegion (1.20 : ℝ) 2.00 := by
  have h : (((120 : ℚ) / 100 : ℚ) : ℝ) < (((200 : ℚ) / 100 : ℚ) : ℝ) :=
    (Rat.zoneQ_inverted_iff _ _).mp inst_I4_mcc_x200_zoneQ
  have hl : (1.20 : ℝ) = (((120 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  have hx : (2.00 : ℝ) = (((200 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  unfold InvertedRegion
  rw [hl, hx]
  exact h

/-! ## I5 — 文献参数·正常区：MCC 系列 `lam = 1.20, x = 0.60`

来源同上（`已核实`）：左支单调升段取值 `x = 0.60 < lam = 1.20` ⇒ **正常区**。
判定结论给出两件事：`NormalRegion 1.20 0.60` 成立，且 `InvertedRegion 1.20 0.60` **不**成立
（后者即「该实例不符合马库斯反转区的描述」这一人类需求中的否定判定）。

English: ## I5 — Literature parameters, normal region: the MCC series `lam = 1.20, x = 0.60`

Source as above ('verified'): a value on the monotonically rising left branch,
`x = 0.60 < lam = 1.20` ⇒ **normal region**.
The decision conclusion supplies two facts: `NormalRegion 1.20 0.60` holds, and
`InvertedRegion 1.20 0.60` **does not** hold (the latter is the negative decision in the human
requirement, 'this instance does not match the description of the Marcus inverted region').
-/

/-- I5 判定（内核计算）：ℚ 层把 `(1.20, 0.60)` 判为正常区。

English: I5 decision (kernel computation): the ℚ layer decides `(1.20, 0.60)` to be in the
normal region.
-/
theorem inst_I5_mcc_x060_zoneQ : Rat.zoneQ ((120 : ℚ) / 100) ((60 : ℚ) / 100) = Zone.normal := by
  norm_num [Rat.zoneQ]

/-- I5 判定结论：`lam = 1.20, x = 0.60` 落在正常区。

English: I5 decision conclusion: `lam = 1.20, x = 0.60` lies in the normal region.
-/
theorem inst_I5_mcc_x060 : NormalRegion (1.20 : ℝ) 0.60 := by
  have h : (((60 : ℚ) / 100 : ℚ) : ℝ) < (((120 : ℚ) / 100 : ℚ) : ℝ) :=
    normalRegion_of_zoneQ_normal inst_I5_mcc_x060_zoneQ
  have hl : (1.20 : ℝ) = (((120 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  have hx : (0.60 : ℝ) = (((60 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  unfold NormalRegion
  rw [hl, hx]
  exact h

/-- I5 判定结论（否定形态）：`lam = 1.20, x = 0.60` **不符合**反转区描述的前提。

English: I5 decision conclusion (negative form): `lam = 1.20, x = 0.60` **does not** satisfy
the premise of the inverted-region description.
-/
theorem inst_I5_mcc_not_inverted : ¬ InvertedRegion (1.20 : ℝ) 0.60 := by
  intro hinv
  have hl : (1.20 : ℝ) = (((120 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  have hx : (0.60 : ℝ) = (((60 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  unfold InvertedRegion at hinv
  rw [hl, hx] at hinv
  exact not_invertedRegion_of_zoneQ_normal inst_I5_mcc_x060_zoneQ hinv

/-! ## I6 — 文献参数·深反转区：光合反应中心 `lam = 0.25, x = 1.10`

来源：`plan.md` §8.3 与 `proofs/LITERATURE.md` §实例参数候选表（`已核实`）——
光合反应中心 BPh⁻ → BChl₂⁺ 回传（hole–electron recombination）：
`lam = 0.25` eV，`x = 1.10` eV（Marcus Nobel Lecture 1992 p.88 正文）。
`x = 1.10 ≫ 0.25 = lam` ⇒ **深反转区**：这是本实例集里 `x / lam` 最大的一条
（`1.10 / 0.25 = 4.4`），即马库斯反转区最极端的实验落点。

English: ## I6 — Literature parameters, deep inverted region: the photosynthetic reaction
centre `lam = 0.25, x = 1.10`

Source: `plan.md` §8.3 and the candidate-instance-parameter table in `proofs/LITERATURE.md`
('verified') — photosynthetic reaction centre BPh⁻ → BChl₂⁺ back-transfer (hole–electron
recombination): `lam = 0.25` eV, `x = 1.10` eV (Marcus Nobel Lecture 1992 p.88, main text).
`x = 1.10 ≫ 0.25 = lam` ⇒ **deep inverted region**: this is the entry with the largest `x / lam`
in the present instance set (`1.10 / 0.25 = 4.4`), i.e. the most extreme experimental locus of
the Marcus inverted region.
-/

/-- I6 判定（内核计算）：ℚ 层把 `(0.25, 1.10)` 判为反转区。

English: I6 decision (kernel computation): the ℚ layer decides `(0.25, 1.10)` to be in the
inverted region.
-/
theorem inst_I6_rc_x110_zoneQ : Rat.zoneQ ((25 : ℚ) / 100) ((110 : ℚ) / 100) = Zone.inverted := by
  norm_num [Rat.zoneQ]

/-- I6 判定结论：`lam = 0.25, x = 1.10` 落在（深）反转区。

English: I6 decision conclusion: `lam = 0.25, x = 1.10` lies in the (deep) inverted region.
-/
theorem inst_I6_rc_x110 : InvertedRegion (0.25 : ℝ) 1.10 := by
  have h : (((25 : ℚ) / 100 : ℚ) : ℝ) < (((110 : ℚ) / 100 : ℚ) : ℝ) :=
    (Rat.zoneQ_inverted_iff _ _).mp inst_I6_rc_x110_zoneQ
  have hl : (0.25 : ℝ) = (((25 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  have hx : (1.10 : ℝ) = (((110 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  unfold InvertedRegion
  rw [hl, hx]
  exact h

end PhotoLean.Marcus

/-! ## 待后续里程碑：速率比较与描述算子条目（**不在本批**）

本批只交付**区域判定**（人类需求里「判断该实例是否符合反转区描述」的前半）。
以下条目的语句已由 `proofs/probes/marcus-statement-skeleton.lean` 与 `plan.md` §7–§8 定稿，
但证明依赖**尚未交付**的模块（`Marcus/Rate.lean` 的速率定理、`Marcus/Sharp.lean`
的锐利刻画 / 描述算子结论），故本批**不写入**；待 lead 在 Sprint 5 派发后追加：

| 条目 | 形状 | 依赖的定理 |
|---|---|---|
| 速率峰（`plan.md` §8.2 的 I3 / 本批 I3 的速率部分） | `x = lam` 处速率取最大（`A = kB·T = 1`） | `rate_peak_at_lam` |
| 反转区速率递减（本批 I4 / I6 的速率部分） | `rate … 2.40 < rate … 2.00`（同 `A, kB, T`） | `inverted_rate_decreases` |
| 正常区速率递增（本批 I5 的速率部分） | `rate … 0.60 < rate … 1.20`（同 `A, kB, T`） | `normal_rate_increases` |
| 非物理反例 `lam ≤ 0`（`plan.md` §8.2 的 I6） | 描述算子不成立 ⇒ 判「不符合」 | `descriptor_fails_of_nonpos_lam` |
| 非物理分支 `A < 0 ∧ lam < 0`（`plan.md` §8.2 的 I7） | 描述算子成立但速率非正 ⇒ 判「不可采纳」 | `inverted_descriptor_holds_of_neg` + 速率正性 |

这些条目一旦交付，将把本文件的「区域判定」升级为「速率单调性 / 描述算子判定」。

**编号说明（写给 verifier）**：本文件的 `inst_I3_*`–`inst_I6_*` 采用 **lead 在 M5b 第一批
派发里的编号**（I3 = 文献无势垒点附近 `(1.20, 1.23)`；I4 = MCC 反转区对；I5 = MCC 正常区；
I6 = 光合反应中心深反转区）。`plan.md` §8.2 表格的旧编号把 I3 留给「`x = lam` 速率峰」，
把 I6/I7 留给非物理分支 —— 那几条依赖上述未交付模块，正好对应本注释的表格。

English: ## For later milestones: rate comparisons and descriptor-operator entries
(**not part of this batch**)

This batch delivers only the **region decisions** (the first half of the human requirement,
'decide whether the instance matches the inverted-region description').
The statements of the following entries were finalized by
`proofs/probes/marcus-statement-skeleton.lean` and `plan.md` §7–§8, but their proofs depend on
modules **not yet delivered** (the rate theorems of `Marcus/Rate.lean`, the sharp
characterization / descriptor-operator conclusions of `Marcus/Sharp.lean`), so they are
**not written** into this batch; they are to be appended once the lead dispatches them in
Sprint 5:

| Entry | Shape | Depended-on theorem |
|---|---|---|
| rate peak (I3 of `plan.md` §8.2 / the rate part of I3 in this batch) | the rate is maximal at `x = lam` (`A = kB·T = 1`) | `rate_peak_at_lam` |
| rate decreasing in the inverted region (the rate part of I4 / I6 in this batch) | `rate … 2.40 < rate … 2.00` (same `A, kB, T`) | `inverted_rate_decreases` |
| rate increasing in the normal region (the rate part of I5 in this batch) | `rate … 0.60 < rate … 1.20` (same `A, kB, T`) | `normal_rate_increases` |
| non-physical counterexample `lam ≤ 0` (I6 of `plan.md` §8.2) | the descriptor operator fails ⇒ decide 'does not match' | `descriptor_fails_of_nonpos_lam` |
| non-physical branch `A < 0 ∧ lam < 0` (I7 of `plan.md` §8.2) | the descriptor operator holds but the rate is not positive ⇒ decide 'not acceptable' | `inverted_descriptor_holds_of_neg` + rate positivity |

Once delivered, these entries will upgrade this file's 'region decisions' into 'rate monotonicity
/ descriptor-operator decisions'.

**Numbering note (for the verifier)**: the names `inst_I3_*`–`inst_I6_*` in this file follow the
**numbering used by the lead in the M5b batch-1 dispatch** (I3 = near the literature's
barrierless point `(1.20, 1.23)`; I4 = the MCC inverted-region pair; I5 = the MCC normal region;
I6 = the deep inverted region of the photosynthetic reaction centre). The old numbering in the
`plan.md` §8.2 table reserves I3 for the '`x = lam` rate peak' and I6/I7 for the non-physical
branches — those entries depend on the not-yet-delivered modules named above and correspond
exactly to the table in this comment.
-/

/-! # M5b 第二批：描述算子实例化 + 速率比较（人类需求第三部分的**最强证据**）

**范围**：第一批只判「实例落在哪个区」；本批判「**该实例是否满足反转区描述**」——
用文献的**自身参数**把主定理（M4a `Sharp.lean` 的 `inverted_descriptor_holds` /
`descriptor_sharp`）与速率层（M3 `Rate.lean` 的 `inverted_rate_decreases` /
`normal_rate_increases` / `rate_peak_at_lam`）实例化。依赖因此从 `RatModel` 扩到 `Sharp`
（顶部补 `import PhotoLean.Marcus.Sharp`；`Sharp` 自身已含 `Barrier` + `Rate`）。

**本批交付的判定内容**

| 条目 | 判定内容 | 证据方式（内核） |
|---|---|---|
| `inst_I7_nonpos_lam_not_descriptor` | `lam = -1/2 ≤ 0`：描述**失效** | `descriptor_fails_of_nonpos_lam` 实例化 |
| `inst_I7_unphysical_descriptor` | `A = lam = -1`：描述**形式成立** | `inverted_descriptor_holds_of_neg` 实例化 |
| `inst_I7_unphysical_rate_not_pos` | 同一实例速率**不是处处为正** | `x = 0` 处 `rate = -exp(1/4) < 0`，内核算 |
| `inst_I7_unphysical_not_admissible` | 该实例**不可采纳**（合取被否） | 上一条的直接推论 |
| `inst_I4_mcc_descriptor_any_kT` / `inst_I4_mcc_descriptor` | MCC `lam = 1.20`：**反转区描述成立**（`kBT > 0` 任意） | `inverted_descriptor_holds` 实例化 |
| `inst_I4_mcc_admissible` | 同一实例**可采纳**：速率处处为正 **且** 描述成立 | 主定理 `descriptor_sharp` 的 `(⟸)` 实例化 |
| `inst_I4_mcc_rate_drop` | 反转区标志结论：`rate(2.40) < rate(1.23)`（**与 kBT 无关**） | `inverted_rate_decreases` 实例化 |
| `inst_I4_mcc_rate_drop_x200` | 同上，文献反转区对内 `rate(2.40) < rate(2.00)` | 同上 |
| `inst_I4_mcc_rate_drop_unit_kT` | `kB = T = 1` 的具体推论 | 上一条的实例化 |
| `inst_I5_mcc_rate_rise` | 正常区：`rate(0.60) < rate(1.20)` | `normal_rate_increases` 实例化 |
| `inst_I3_rate_peak` | 峰位：`rate(2.40) ≤ rate(1.20)`（`x = lam` 最优） | `rate_peak_at_lam` 实例化 |

**温度的处理（承 plan §8.3）**：`kBT` 一律写成**显式前提 `0 < kBT`**；`T := 1` 只是把温度
折进 `kBT` 的单位选择（`kB := kBT`、`T := 1` ⇒ `kB * T = kBT`）。因此「判定与温度无关」
是**语句的一部分**，不是注释里的声称 —— `inst_I4_mcc_rate_drop` 等对**任意** `0 < kBT` 成立。

**实例层文案边界（plan §8.3 的定量警示，必须遵守）**：本批结论只能读作
「**经典 Marcus 模型**在文献参数 `(lam, x, kBT, A)` 上满足反转区描述」——
**不得**读作对实验的断言：经典公式在反转区下降过快（`lam = 1.20`、`x: 1.23 → 2.40` 时
预言降 5.1 个数量级，实测只降 1.46 个数量级），这正是量子振动修正（Bixon–Jortner）的动机。

**实测偏差（写给 verifier）**：派发提示里的速率非正写法
`intro h; have := h 0; norm_num [rate, barrier] at this`
在本环境（mathlib v4.17.0）**不足以收尾**：`norm_num at this` 会把假设化为
`Real.exp (1/4) < 0`，但**不能**用它反驳（`norm_num` 不认识 `Real.exp` 的正性），
留下未解目标 `False`。奏效写法是先 `norm_num at h0` 归约，再
`linarith [Real.exp_pos (1/4)]` 闭合（见 `inst_I7_unphysical_rate_not_pos` 的证明体）。

**上文「待后续里程碑」表格已由本批交付**（该表 5 条全部落地：速率峰 / 反转区速率递减 /
正常区速率递增 / `lam ≤ 0` 失效判定 / 非物理分支的速率正性反证），以本批定理为准。

English: # M5b batch 2: descriptor-operator instantiation + rate comparisons
(the **strongest evidence** for part three of the human requirement)

**Scope**: the first batch only decides 'which region the instance falls into'; this batch decides
'**whether the instance satisfies the inverted-region description**' — by instantiating the main
theorems (M4a `Sharp.lean`'s `inverted_descriptor_holds` / `descriptor_sharp`) and the rate layer
(M3 `Rate.lean`'s `inverted_rate_decreases` / `normal_rate_increases` / `rate_peak_at_lam`) at the
literature's **own parameters**. The dependency therefore widens from `RatModel` to `Sharp`
(`import PhotoLean.Marcus.Sharp` is added at the top; `Sharp` itself already contains
`Barrier` + `Rate`).

**Decisions delivered by this batch**

| Entry | Decision content | Evidence method (kernel) |
|---|---|---|
| `inst_I7_nonpos_lam_not_descriptor` | `lam = -1/2 ≤ 0`: the description **fails** | instantiation of `descriptor_fails_of_nonpos_lam` |
| `inst_I7_unphysical_descriptor` | `A = lam = -1`: the description **holds formally** | instantiation of `inverted_descriptor_holds_of_neg` |
| `inst_I7_unphysical_rate_not_pos` | for the same instance the rate is **not everywhere positive** | at `x = 0`, `rate = -exp(1/4) < 0`, computed by the kernel |
| `inst_I7_unphysical_not_admissible` | this instance is **not acceptable** (the conjunction is refuted) | immediate corollary of the previous entry |
| `inst_I4_mcc_descriptor_any_kT` / `inst_I4_mcc_descriptor` | MCC `lam = 1.20`: **the inverted-region description holds** (for arbitrary `kBT > 0`) | instantiation of `inverted_descriptor_holds` |
| `inst_I4_mcc_admissible` | the same instance is **acceptable**: the rate is everywhere positive **and** the description holds | instantiation of the `(⟸)` direction of the main theorem `descriptor_sharp` |
| `inst_I4_mcc_rate_drop` | hallmark inverted-region conclusion: `rate(2.40) < rate(1.23)` (**independent of kBT**) | instantiation of `inverted_rate_decreases` |
| `inst_I4_mcc_rate_drop_x200` | as above, within the literature inverted-region pair: `rate(2.40) < rate(2.00)` | as above |
| `inst_I4_mcc_rate_drop_unit_kT` | the concrete corollary for `kB = T = 1` | instantiation of the previous entry |
| `inst_I5_mcc_rate_rise` | normal region: `rate(0.60) < rate(1.20)` | instantiation of `normal_rate_increases` |
| `inst_I3_rate_peak` | peak location: `rate(2.40) ≤ rate(1.20)` (`x = lam` is optimal) | instantiation of `rate_peak_at_lam` |

**How temperature is handled (following plan §8.3)**: `kBT` is always written as the **explicit
premise `0 < kBT`**; `T := 1` is merely the choice of units that folds temperature into `kBT`
(`kB := kBT`, `T := 1` ⇒ `kB * T = kBT`). Hence 'the decision is independent of temperature' is
**part of the statement**, not a claim in a comment — `inst_I4_mcc_rate_drop` and the like hold
for **arbitrary** `0 < kBT`.

**Boundary of the instance-level prose (the quantitative warning of plan §8.3, which must be
observed)**: the conclusions of this batch may only be read as 'the **classical Marcus model**
satisfies the inverted-region description at the literature parameters `(lam, x, kBT, A)`' —
**not** as an assertion about experiment: the classical formula falls off too fast in the
inverted region (for `lam = 1.20`, `x: 1.23 → 2.40` it predicts a drop of 5.1 orders of
magnitude, whereas the measured drop is only 1.46 orders of magnitude), which is precisely the
motivation for quantum vibrational corrections (Bixon–Jortner).

**Observed deviation (for the verifier)**: the non-positive-rate form suggested in the dispatch,
`intro h; have := h 0; norm_num [rate, barrier] at this`,
is **not enough to close the goal** in this environment (mathlib v4.17.0): `norm_num at this`
normalizes the hypothesis to `Real.exp (1/4) < 0`, but **cannot** be used to refute it (`norm_num`
does not know about the positivity of `Real.exp`), leaving the goal `False` unsolved. The form
that works is to reduce with `norm_num at h0` first and then close with
`linarith [Real.exp_pos (1/4)]` (see the proof body of `inst_I7_unphysical_rate_not_pos`).

**The 'for later milestones' table above has now been delivered by this batch** (all 5 entries
landed: the rate peak / rate decrease in the inverted region / rate increase in the normal region
/ the `lam ≤ 0` failure decision / the rate-positivity refutation of the non-physical branch);
the theorems of this batch are authoritative.
-/

namespace PhotoLean.Marcus

/-! ## I7 — 非物理参数的判定（`lam ≤ 0` 与 `A < 0 ∧ lam < 0` 两个分支）

判定内容分三层，**缺一不可**：
1. `lam = -1/2 ≤ 0`：**描述失效**（`descriptor_fails_of_nonpos_lam`，M4a 必要性方向的推论）；
2. `A = lam = -1`：描述**形式成立**（`inverted_descriptor_holds_of_neg`，M4a 拉伸目标）——
   即「描述算子本身」**判不出**这个非物理实例；
3. 但该实例的速率在 `x = 0` 处为 `-exp(1/4) < 0` ⇒ **速率正性前提不可去**；
   合起来给出「**不可采纳**」这一判定（`inst_I7_unphysical_not_admissible`）。

English: ## I7 — Decisions for non-physical parameters (the two branches `lam ≤ 0` and
`A < 0 ∧ lam < 0`)

The decision content has three layers, **all of which are indispensable**:
1. `lam = -1/2 ≤ 0`: **the description fails** (`descriptor_fails_of_nonpos_lam`, a corollary of
   the necessity direction of M4a);
2. `A = lam = -1`: the description **holds formally** (`inverted_descriptor_holds_of_neg`, the
   M4a stretching goal) — i.e. 'the descriptor operator itself' **cannot decide** this
   non-physical instance;
3. but the rate of this instance at `x = 0` is `-exp(1/4) < 0` ⇒ **the rate-positivity premise
   cannot be dropped**; taken together they yield the decision '**not acceptable**'
   (`inst_I7_unphysical_not_admissible`).
-/

/-- I7a 非物理参数判定：`lam = -1/2 ≤ 0` 时反转区描述**失效**
（依据 M4a `descriptor_fails_of_nonpos_lam`：物理正性前提 `0 < A`、`0 < kB`、`0 < T` 下
描述成立蕴含 `0 < lam`，与 `lam ≤ 0` 矛盾）。

English: I7a decision for non-physical parameters: for `lam = -1/2 ≤ 0` the inverted-region
description **fails** (by M4a `descriptor_fails_of_nonpos_lam`: under the physical positivity
premises `0 < A`, `0 < kB`, `0 < T`, the description holding implies `0 < lam`, which contradicts
`lam ≤ 0`).
-/
theorem inst_I7_nonpos_lam_not_descriptor : ¬ InvertedDescriptor (1 : ℝ) (-1 / 2) 1 1 :=
  descriptor_fails_of_nonpos_lam (A := 1) (kB := 1) (T := 1) (lam := -1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- I7b 非物理分支：`A = -1 < 0` 且 `lam = -1 < 0` 时反转区描述**形式上成立** ——
此时 `barrier` 在反转区**递减**（`barrier_antitone_of_neg`），乘负前置因子后速率仍递减。
这一条是「『速率处处为正』前提不可去」的可检查证据（M4a 拉伸目标 `inverted_descriptor_holds_of_neg`）。

English: I7b non-physical branch: for `A = -1 < 0` and `lam = -1 < 0` the inverted-region
description **holds formally** — here `barrier` is **decreasing** on the inverted region
(`barrier_antitone_of_neg`), and multiplying by the negative prefactor keeps the rate decreasing.
This entry is checkable evidence that the premise 'the rate is everywhere positive' cannot be
dropped (the M4a stretching goal `inverted_descriptor_holds_of_neg`).
-/
theorem inst_I7_unphysical_descriptor : InvertedDescriptor (-1) (-1) 1 1 :=
  inverted_descriptor_holds_of_neg (A := -1) (lam := -1) (kB := 1) (T := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- I7c ……但上一条的速率**不是处处为正** ⇒ 该实例**不可采纳**
（「速率正性」前提不可去）：取 `x = 0`，`barrier (-1) 0 = -1/4`，
故 `rate (-1) (-1) 1 1 0 = -1 · exp(1/4) < 0`（`Real.exp` 恒正）。
内核计算给出 `barrier` 的值与指数归约，`Real.exp_pos` 给出正性。

English: I7c … but the rate of the previous entry is **not everywhere positive** ⇒ this
instance is **not acceptable** (the 'rate positivity' premise cannot be dropped): take `x = 0`,
`barrier (-1) 0 = -1/4`, hence `rate (-1) (-1) 1 1 0 = -1 · exp(1/4) < 0` (`Real.exp` is always
positive). The kernel computation yields the value of `barrier` and the reduction of the
exponential, while `Real.exp_pos` supplies the positivity.
-/
theorem inst_I7_unphysical_rate_not_pos : ¬ (∀ x : ℝ, 0 < rate (-1) (-1) 1 1 x) := by
  intro h
  have h0 := h 0
  have hb : barrier (-1) 0 = -(1 / 4) := by norm_num [barrier]
  rw [rate, hb] at h0
  norm_num at h0
  linarith [Real.exp_pos (1 / 4)]

/-- I7 判定汇总：非物理分支 `(A, lam) = (-1, -1)` 的实例**不可采纳** ——
「速率处处为正」与「反转区描述」的合取**不成立**（由 I7c 直接给出）。
与 I7b 合读：描述算子单独**不足以**接受一个实例，这正是 M4a `descriptor_sharp`
要把正性并入刻画的理由。

English: I7 decision summary: the instance of the non-physical branch `(A, lam) = (-1, -1)` is
**not acceptable** — the conjunction of 'the rate is everywhere positive' and 'the inverted-region
description' **does not hold** (given directly by I7c).
Read together with I7b: the descriptor operator alone is **not enough** to accept an instance,
which is exactly why M4a `descriptor_sharp` folds positivity into the characterization.
-/
theorem inst_I7_unphysical_not_admissible :
    ¬ ((∀ x : ℝ, 0 < rate (-1) (-1) 1 1 x) ∧ InvertedDescriptor (-1) (-1) 1 1) :=
  fun h => inst_I7_unphysical_rate_not_pos h.1

/-! ## I4 — 文献参数 MCC 系列的**描述算子实例化**（人类需求第三部分的核心判定）

`lam = 1.20`（MCC 系列参数来源与第一批 I4 相同：`plan.md` §8.3 /
`proofs/LITERATURE.md` §实例参数候选表，核实状态「已核实」）。三条按强度递进：

1. `inst_I4_mcc_descriptor_any_kT`：对**任意** `kBT > 0`，反转区描述成立（`A = 1`）——
   主定理 `inverted_descriptor_holds` 在文献参数上的实例化，同时是「判定与温度无关」的
   **语句级**证据（`kBT` 是定理的全称变量，不是注释里的声称）；
2. `inst_I4_mcc_descriptor`：`kB = T = 1` 的特例（与派发语句逐字一致）；
3. `inst_I4_mcc_admissible`：速率**处处为正** **且**描述成立 —— 主定理 `descriptor_sharp`
   的 `(⟸)` 方向实例化，即「该实例**可采纳**」的完整判定（与 I7 的不可采纳实例对照）。

`inst_I6_rc_descriptor_any_kT` 把同一实例化搬到**深反转区**的光合反应中心参数
（`lam = 0.25`，`x = 1.10`，第一批 I6 已判其落在反转区），使 I3–I6 四条文献实例
都带有描述算子层面的判定。

English: ## I4 — **Descriptor-operator instantiation** for the literature MCC-series
parameters (the core decision of part three of the human requirement)

`lam = 1.20` (the parameter source of the MCC series is the same as for I4 in the first batch:
`plan.md` §8.3 / the candidate-instance-parameter table in `proofs/LITERATURE.md`, verification
status 'verified'). The three entries progress in strength:

1. `inst_I4_mcc_descriptor_any_kT`: for **arbitrary** `kBT > 0` the inverted-region description
   holds (`A = 1`) — an instantiation of the main theorem `inverted_descriptor_holds` at the
   literature parameters, and at the same time **statement-level** evidence that 'the decision is
   independent of temperature' (`kBT` is a universally quantified variable of the theorem, not a
   claim in a comment);
2. `inst_I4_mcc_descriptor`: the special case `kB = T = 1` (verbatim identical to the dispatched
   statement);
3. `inst_I4_mcc_admissible`: the rate is **everywhere positive** **and** the description holds —
   an instantiation of the `(⟸)` direction of the main theorem `descriptor_sharp`, i.e. the
   complete decision 'this instance **is acceptable**' (contrast with the non-acceptable instance
   of I7).

`inst_I6_rc_descriptor_any_kT` moves the same instantiation to the **deep inverted region**
photosynthetic reaction centre parameters (`lam = 0.25`, `x = 1.10`; batch 1's I6 already decided
that it falls in the inverted region), so that all four literature instances I3–I6 come with a
descriptor-operator-level decision.
-/

/-- I4 描述算子判定（**与温度无关**）：文献 MCC 参数 `lam = 1.20`、`A = 1` 下，
对**任意** `kBT > 0`，反转区描述成立（主定理 `inverted_descriptor_holds` 实例化）。

English: I4 descriptor-operator decision (**independent of temperature**): under the literature
MCC parameters `lam = 1.20`, `A = 1`, the inverted-region description holds for **arbitrary**
`kBT > 0` (an instantiation of the main theorem `inverted_descriptor_holds`).
-/
theorem inst_I4_mcc_descriptor_any_kT {kBT : ℝ} (hkBT : 0 < kBT) :
    InvertedDescriptor (1 : ℝ) (1.20 : ℝ) kBT 1 :=
  inverted_descriptor_holds (A := 1) (lam := 1.20) (kB := kBT) (T := 1)
    (by norm_num) (by norm_num) (by simpa using hkBT)

/-- I4 描述算子判定（`kB = T = 1` 的具体实例）：`lam = 1.20` 上反转区描述成立。

English: I4 descriptor-operator decision (the concrete instance `kB = T = 1`): the
inverted-region description holds at `lam = 1.20`.
-/
theorem inst_I4_mcc_descriptor : InvertedDescriptor (1 : ℝ) (1.20 : ℝ) 1 1 :=
  inst_I4_mcc_descriptor_any_kT (by norm_num)

/-- I4 判定汇总：文献 MCC 实例 **可采纳** —— 速率处处为正 **且** 反转区描述成立
（主定理 `descriptor_sharp` 的 `(⟸)` 方向实例化：`0 < A ∧ 0 < lam` 给出两件事）。
与 `inst_I7_unphysical_not_admissible` 对读：可采纳性由「正性 + 描述」两条共同承担。

English: I4 decision summary: the literature MCC instance **is acceptable** — the rate is
everywhere positive **and** the inverted-region description holds (an instantiation of the `(⟸)`
direction of the main theorem `descriptor_sharp`: `0 < A ∧ 0 < lam` yields both facts).
Read against `inst_I7_unphysical_not_admissible`: acceptability is borne jointly by the two
components 'positivity + description'.
-/
theorem inst_I4_mcc_admissible {kBT : ℝ} (hkBT : 0 < kBT) :
    (∀ x : ℝ, 0 < rate (1 : ℝ) (1.20 : ℝ) kBT 1 x) ∧
      InvertedDescriptor (1 : ℝ) (1.20 : ℝ) kBT 1 :=
  (descriptor_sharp (kB := kBT) (T := 1) (by simpa using hkBT) (by norm_num) 1 1.20).mpr
    ⟨by norm_num, by norm_num⟩

/-- I6 描述算子判定（深反转区）：光合反应中心参数 `lam = 0.25`、`A = 1` 下，
对**任意** `kBT > 0`，反转区描述成立（与 I4 同一条主定理，仅更换文献参数）。

English: I6 descriptor-operator decision (deep inverted region): under the photosynthetic
reaction centre parameters `lam = 0.25`, `A = 1`, the inverted-region description holds for
**arbitrary** `kBT > 0` (the same main theorem as for I4, only with different literature
parameters).
-/
theorem inst_I6_rc_descriptor_any_kT {kBT : ℝ} (hkBT : 0 < kBT) :
    InvertedDescriptor (1 : ℝ) (0.25 : ℝ) kBT 1 :=
  inverted_descriptor_holds (A := 1) (lam := 0.25) (kB := kBT) (T := 1)
    (by norm_num) (by norm_num) (by simpa using hkBT)

/-! ## 速率比较 —— 反转区的标志性结论（**与温度无关**）

反转区的标志性物理结论是「**驱动力更大的体系速率反而更小**」。本组把 M3 速率层
（`inverted_rate_decreases` / `normal_rate_increases` / `rate_peak_at_lam`）实例化到
文献 MCC 参数 `lam = 1.20`：

* `inst_I4_mcc_rate_drop`：`rate(2.40) < rate(1.23)` —— 系列内 (1.23, 2.40) 一对；
  两者都由第一批判为反转区（`1.23` 是近无势垒点、`2.40` 是系列放能上界）；
* `inst_I4_mcc_rate_drop_x200`：`rate(2.40) < rate(2.00)` —— 第一批 I4 的两个反转区刻度
  （`2.00` 为内插刻度值，`2.40` 为系列上界）之间的速率比较；
* `inst_I4_mcc_rate_drop_unit_kT`：上一条在 `kB = T = 1` 的具体化（派发建议的推论形态）；
* `inst_I5_mcc_rate_rise`：正常区方向 `rate(0.60) < rate(1.20)` —— 速率升到 `x = lam`；
* `inst_I3_rate_peak`：`rate(2.40) ≤ rate(1.20)` —— `x = lam`（文献最优/无势垒点附近）
  是速率的极大点。

每条的证明都是「M2 势垒单调性 + M3 核心转移引理」的复合，由 `Rate.lean` 的三条
单调性定理打包，故实例层不出现新的实分析风险。

**温度无关性**：含 `kBT` 的定理都把 `0 < kBT` 写成**前提**、`T := 1` 只作单位选择
（`kB * T = kBT`），故结论对**任意**正温度成立 —— 这是「判定与温度无关」的语句级证据，
而非注释里的声称。

**文案边界（plan §8.3，必须遵守）**：以上是**经典 Marcus 模型**在文献参数上的性质，
**不是**对实验的断言：经典公式在此区间下降过快（`x: 1.23 → 2.40` 预言降 5.1 个数量级，
实测只降 1.46 个数量级），实验数据的严格版本需要量子振动修正（Bixon–Jortner）。
本组定理只断言**严格不等号的方向**，不断言下降的**幅度**。

English: ## Rate comparisons — the hallmark conclusion of the inverted region
(**independent of temperature**)

The hallmark physical conclusion of the inverted region is '**a system with a larger driving
force has a smaller rate**'. This group instantiates the M3 rate layer
(`inverted_rate_decreases` / `normal_rate_increases` / `rate_peak_at_lam`) at the literature MCC
parameters `lam = 1.20`:

* `inst_I4_mcc_rate_drop`: `rate(2.40) < rate(1.23)` — the pair (1.23, 2.40) within the series;
  both were decided to be in the inverted region by the first batch (`1.23` is the
  near-barrierless point, `2.40` is the series' exergonicity upper bound);
* `inst_I4_mcc_rate_drop_x200`: `rate(2.40) < rate(2.00)` — the rate comparison between the two
  inverted-region scale values of batch 1's I4 (`2.00` is an interpolated scale value, `2.40` the
  series' upper bound);
* `inst_I4_mcc_rate_drop_unit_kT`: the specialization of the previous entry to `kB = T = 1`
  (the corollary form suggested by the dispatch);
* `inst_I5_mcc_rate_rise`: the normal-region direction `rate(0.60) < rate(1.20)` — the rate rises
  up to `x = lam`;
* `inst_I3_rate_peak`: `rate(2.40) ≤ rate(1.20)` — `x = lam` (near the literature optimum /
  barrierless point) is the maximum point of the rate.

Every proof is a composite of 'M2 barrier monotonicity + M3 core transfer lemmas', packaged by
the three monotonicity theorems of `Rate.lean`, so no new real-analysis risk arises at the
instance level.

**Independence of temperature**: every theorem involving `kBT` writes `0 < kBT` as a **premise**
and uses `T := 1` only as a choice of units (`kB * T = kBT`), so the conclusions hold for
**arbitrary** positive temperature — this is statement-level evidence for 'the decision is
independent of temperature', not a claim in a comment.

**Prose boundary (plan §8.3, which must be observed)**: the above are properties of the
**classical Marcus model** at the literature parameters, **not** assertions about experiment:
the classical formula falls off too fast in this interval (for `x: 1.23 → 2.40` it predicts a drop
of 5.1 orders of magnitude, whereas the measured drop is only 1.46 orders of magnitude), and a
rigorous version for experimental data requires quantum vibrational corrections
(Bixon–Jortner). The theorems of this group assert only the **direction of the strict
inequality**, never the **magnitude** of the drop.
-/

/-- I4 速率比较（**反转区的标志性结论**，且**与温度无关**）：文献 MCC 参数
`lam = 1.20`、`A = 1` 下，对任意 `kBT > 0`，驱动力 2.40 的速率**严格小于**
驱动力 1.23（无势垒点附近）的速率。依据：`inverted_rate_decreases`
（`1.20 < 1.23 < 2.40` 都在反转区）。

English: I4 rate comparison (**the hallmark conclusion of the inverted region**, and
**independent of temperature**): under the literature MCC parameters `lam = 1.20`, `A = 1`, for
arbitrary `kBT > 0` the rate at driving force 2.40 is **strictly smaller** than the rate at
driving force 1.23 (near the barrierless point). Basis: `inverted_rate_decreases`
(`1.20 < 1.23 < 2.40`, all in the inverted region).
-/
theorem inst_I4_mcc_rate_drop {kBT : ℝ} (hkBT : 0 < kBT) :
    rate (1 : ℝ) (1.20 : ℝ) kBT 1 2.40 < rate (1 : ℝ) (1.20 : ℝ) kBT 1 1.23 :=
  inverted_rate_decreases (A := 1) (lam := 1.20) (kB := kBT) (T := 1)
    (by norm_num) (by norm_num) (by simpa using hkBT) (by norm_num) (by norm_num)

/-- I4 速率比较（文献反转区对的内插刻度）：`rate(2.40) < rate(2.00)`。
`2.00` 与 `2.40` 是第一批 I4 判为反转区的两个刻度（见 `inst_I4_mcc_x200` /
`inst_I4_mcc_x240`）；本条把「同系列内放能性更大 ⇒ 速率更小」在该对上落实。

English: I4 rate comparison (the interpolated scale value within the literature
inverted-region pair): `rate(2.40) < rate(2.00)`.
`2.00` and `2.40` are the two scale values that batch 1's I4 decided to be in the inverted region
(see `inst_I4_mcc_x200` / `inst_I4_mcc_x240`); this entry realizes 'larger exergonicity within the
same series ⇒ smaller rate' on that pair.
-/
theorem inst_I4_mcc_rate_drop_x200 {kBT : ℝ} (hkBT : 0 < kBT) :
    rate (1 : ℝ) (1.20 : ℝ) kBT 1 2.40 < rate (1 : ℝ) (1.20 : ℝ) kBT 1 2.00 :=
  inverted_rate_decreases (A := 1) (lam := 1.20) (kB := kBT) (T := 1)
    (by norm_num) (by norm_num) (by simpa using hkBT) (by norm_num) (by norm_num)

/-- I4 速率比较（`kB = T = 1` 的具体推论，即 `kBT = 1`）：派发建议的实例形态。

English: I4 rate comparison (the concrete corollary for `kB = T = 1`, i.e. `kBT = 1`): the
instance form suggested by the dispatch.
-/
theorem inst_I4_mcc_rate_drop_unit_kT :
    rate (1 : ℝ) (1.20 : ℝ) 1 1 2.40 < rate (1 : ℝ) (1.20 : ℝ) 1 1 1.23 :=
  inst_I4_mcc_rate_drop (kBT := 1) (by norm_num)

/-- I5 速率比较（**正常区**：速率随驱动力**上升**至 `x = lam`）：
文献 MCC 刻度 `x = 0.60 < lam = 1.20` 处的速率严格小于 `x = lam = 1.20` 处。
依据：`normal_rate_increases`（`0 ≤ 0.60 < 1.20 ≤ lam`）。

English: I5 rate comparison (**normal region**: the rate **rises** with the driving force up to
`x = lam`): the rate at the literature MCC scale value `x = 0.60 < lam = 1.20` is strictly smaller
than the rate at `x = lam = 1.20`. Basis: `normal_rate_increases` (`0 ≤ 0.60 < 1.20 ≤ lam`).
-/
theorem inst_I5_mcc_rate_rise {kBT : ℝ} (hkBT : 0 < kBT) :
    rate (1 : ℝ) (1.20 : ℝ) kBT 1 0.60 < rate (1 : ℝ) (1.20 : ℝ) kBT 1 1.20 :=
  normal_rate_increases (A := 1) (lam := 1.20) (kB := kBT) (T := 1)
    (by norm_num) (by norm_num) (by simpa using hkBT)
    (by norm_num : (0 : ℝ) ≤ 0.60) (by norm_num) (by norm_num)

/-- I3 峰值：`x = lam = 1.20` 处速率**最大**（文献的最优/无势垒点）——
对任意驱动力（此处取 I4 的 `2.40`）速率不超过它。依据：`rate_peak_at_lam`
（M2 `barrier_min_at_lam` + 非严格 `Real.exp` 单调性）。

English: I3 peak: the rate is **maximal** at `x = lam = 1.20` (the literature optimum /
barrierless point) — for an arbitrary driving force (here I4's `2.40`) the rate does not exceed
it. Basis: `rate_peak_at_lam` (M2 `barrier_min_at_lam` + the non-strict monotonicity of
`Real.exp`).
-/
theorem inst_I3_rate_peak {kBT : ℝ} (hkBT : 0 < kBT) :
    rate (1 : ℝ) (1.20 : ℝ) kBT 1 2.40 ≤ rate (1 : ℝ) (1.20 : ℝ) kBT 1 1.20 :=
  rate_peak_at_lam (A := 1) (lam := 1.20) (kB := kBT) (T := 1)
    (by norm_num) (by norm_num) (by simpa using hkBT) 2.40

end PhotoLean.Marcus
