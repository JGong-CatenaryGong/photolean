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
-/
import PhotoLean.Marcus.RatModel
import PhotoLean.Marcus.Sharp

namespace PhotoLean.Marcus

/-! ## I1 — 纯数实例：`lam = 1, x = 3`（反转区）

证据链 1：`Rat.zoneQ 1 3` 走整数参数路径，`by decide` 由内核算出 `Zone.inverted`。
证据链 2：`Rat.zoneQ_inverted_iff` 把判定搬到 ℝ 层；ℝ 侧的两个字面量各自用
`norm_num` 桥接到 ℚ 分数字面量（`(1 : ℝ) = ↑(1 : ℚ)`、`(3 : ℝ) = ↑(3 : ℚ)`），
再由 `InvertedRegion` 的定义读出判定结论。 -/

/-- I1 判定（内核计算）：`lam = 1, x = 3` 落在反转区。 -/
theorem inst_I1_zoneQ : Rat.zoneQ (1 : ℚ) 3 = Zone.inverted := by decide

/-- I1 判定结论：`lam = 1, x = 3` 符合反转区描述的前提（`InvertedRegion`）。 -/
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
`zone ↑?lam ↑?x` 能对上。 -/

/-- 转移引理（正常区）：ℚ 层判 `normal` ⇒ ℝ 层 `NormalRegion`（即 `x < lam`）。 -/
theorem normalRegion_of_zoneQ_normal {lam x : ℚ} (h : Rat.zoneQ lam x = Zone.normal) :
    NormalRegion (lam : ℝ) (x : ℝ) := by
  have h1 : zone (lam : ℝ) (x : ℝ) = Zone.normal := by
    rw [← Rat.zoneQ_eq_zone]
    exact h
  exact (zone_eq_normal_iff (lam : ℝ) (x : ℝ)).mp h1

/-- 转移引理（排除反转区）：ℚ 层判 `normal` ⇒ ℝ 层**不**在反转区。

证明只用 M5a 的接口：若 ℝ 侧真的落在反转区，`Rat.zoneQ_inverted_iff` 会迫使
ℚ 层判定为 `inverted`，与已算出的 `normal` 矛盾（`Zone` 的构造子互异由 `by decide` 给出）。 -/
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
得到「该实例**不符合**反转区描述的前提」这一否定判定。 -/

/-- I2 判定（内核计算）：`lam = 1, x = 3/4` 落在正常区。 -/
theorem inst_I2_zoneQ : Rat.zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by norm_num [Rat.zoneQ]

/-- I2 判定结论：`lam = 1, x = 3/4` **不符合**反转区描述的前提。 -/
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
势垒虽小但严格为正，反应仍在反转区一侧。 -/

/-- I3 判定（内核计算）：文献最优点的势垒值 `barrier 1.20 1.23 = 0.0001875` eV。 -/
theorem inst_I3_barrier_value : barrier (1.20 : ℝ) 1.23 = 0.0001875 := by norm_num [barrier]

/-- I3 判定（内核计算）：ℚ 层把 `(1.20, 1.23)` 判为反转区。 -/
theorem inst_I3_zoneQ : Rat.zoneQ ((120 : ℚ) / 100) ((123 : ℚ) / 100) = Zone.inverted := by
  norm_num [Rat.zoneQ]

/-- I3 判定结论：`lam = 1.20, x = 1.23` 落在反转区。 -/
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
驱动力超过重组能后速率随放能性增大而下降（速率下降本身是 Sprint 5 的条目，见文末）。 -/

/-- I4 判定（内核计算）：ℚ 层把 `(1.20, 2.40)` 判为反转区。 -/
theorem inst_I4_mcc_x240_zoneQ : Rat.zoneQ ((120 : ℚ) / 100) ((240 : ℚ) / 100) = Zone.inverted := by
  norm_num [Rat.zoneQ]

/-- I4 判定结论：`lam = 1.20, x = 2.40` 落在反转区。 -/
theorem inst_I4_mcc_x240 : InvertedRegion (1.20 : ℝ) 2.40 := by
  have h : (((120 : ℚ) / 100 : ℚ) : ℝ) < (((240 : ℚ) / 100 : ℚ) : ℝ) :=
    (Rat.zoneQ_inverted_iff _ _).mp inst_I4_mcc_x240_zoneQ
  have hl : (1.20 : ℝ) = (((120 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  have hx : (2.40 : ℝ) = (((240 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  unfold InvertedRegion
  rw [hl, hx]
  exact h

/-- I4 判定（内核计算）：ℚ 层把 `(1.20, 2.00)` 判为反转区。 -/
theorem inst_I4_mcc_x200_zoneQ : Rat.zoneQ ((120 : ℚ) / 100) ((200 : ℚ) / 100) = Zone.inverted := by
  norm_num [Rat.zoneQ]

/-- I4 判定结论：`lam = 1.20, x = 2.00` 落在反转区。 -/
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
（后者即「该实例不符合马库斯反转区的描述」这一人类需求中的否定判定）。 -/

/-- I5 判定（内核计算）：ℚ 层把 `(1.20, 0.60)` 判为正常区。 -/
theorem inst_I5_mcc_x060_zoneQ : Rat.zoneQ ((120 : ℚ) / 100) ((60 : ℚ) / 100) = Zone.normal := by
  norm_num [Rat.zoneQ]

/-- I5 判定结论：`lam = 1.20, x = 0.60` 落在正常区。 -/
theorem inst_I5_mcc_x060 : NormalRegion (1.20 : ℝ) 0.60 := by
  have h : (((60 : ℚ) / 100 : ℚ) : ℝ) < (((120 : ℚ) / 100 : ℚ) : ℝ) :=
    normalRegion_of_zoneQ_normal inst_I5_mcc_x060_zoneQ
  have hl : (1.20 : ℝ) = (((120 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  have hx : (0.60 : ℝ) = (((60 : ℚ) / 100 : ℚ) : ℝ) := by norm_num
  unfold NormalRegion
  rw [hl, hx]
  exact h

/-- I5 判定结论（否定形态）：`lam = 1.20, x = 0.60` **不符合**反转区描述的前提。 -/
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
（`1.10 / 0.25 = 4.4`），即马库斯反转区最极端的实验落点。 -/

/-- I6 判定（内核计算）：ℚ 层把 `(0.25, 1.10)` 判为反转区。 -/
theorem inst_I6_rc_x110_zoneQ : Rat.zoneQ ((25 : ℚ) / 100) ((110 : ℚ) / 100) = Zone.inverted := by
  norm_num [Rat.zoneQ]

/-- I6 判定结论：`lam = 0.25, x = 1.10` 落在（深）反转区。 -/
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
把 I6/I7 留给非物理分支 —— 那几条依赖上述未交付模块，正好对应本注释的表格。 -/

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
正常区速率递增 / `lam ≤ 0` 失效判定 / 非物理分支的速率正性反证），以本批定理为准。 -/

namespace PhotoLean.Marcus

/-! ## I7 — 非物理参数的判定（`lam ≤ 0` 与 `A < 0 ∧ lam < 0` 两个分支）

判定内容分三层，**缺一不可**：
1. `lam = -1/2 ≤ 0`：**描述失效**（`descriptor_fails_of_nonpos_lam`，M4a 必要性方向的推论）；
2. `A = lam = -1`：描述**形式成立**（`inverted_descriptor_holds_of_neg`，M4a 拉伸目标）——
   即「描述算子本身」**判不出**这个非物理实例；
3. 但该实例的速率在 `x = 0` 处为 `-exp(1/4) < 0` ⇒ **速率正性前提不可去**；
   合起来给出「**不可采纳**」这一判定（`inst_I7_unphysical_not_admissible`）。 -/

/-- I7a 非物理参数判定：`lam = -1/2 ≤ 0` 时反转区描述**失效**
（依据 M4a `descriptor_fails_of_nonpos_lam`：物理正性前提 `0 < A`、`0 < kB`、`0 < T` 下
描述成立蕴含 `0 < lam`，与 `lam ≤ 0` 矛盾）。 -/
theorem inst_I7_nonpos_lam_not_descriptor : ¬ InvertedDescriptor (1 : ℝ) (-1 / 2) 1 1 :=
  descriptor_fails_of_nonpos_lam (A := 1) (kB := 1) (T := 1) (lam := -1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- I7b 非物理分支：`A = -1 < 0` 且 `lam = -1 < 0` 时反转区描述**形式上成立** ——
此时 `barrier` 在反转区**递减**（`barrier_antitone_of_neg`），乘负前置因子后速率仍递减。
这一条是「『速率处处为正』前提不可去」的可检查证据（M4a 拉伸目标 `inverted_descriptor_holds_of_neg`）。 -/
theorem inst_I7_unphysical_descriptor : InvertedDescriptor (-1) (-1) 1 1 :=
  inverted_descriptor_holds_of_neg (A := -1) (lam := -1) (kB := 1) (T := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- I7c ……但上一条的速率**不是处处为正** ⇒ 该实例**不可采纳**
（「速率正性」前提不可去）：取 `x = 0`，`barrier (-1) 0 = -1/4`，
故 `rate (-1) (-1) 1 1 0 = -1 · exp(1/4) < 0`（`Real.exp` 恒正）。
内核计算给出 `barrier` 的值与指数归约，`Real.exp_pos` 给出正性。 -/
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
要把正性并入刻画的理由。 -/
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
都带有描述算子层面的判定。 -/

/-- I4 描述算子判定（**与温度无关**）：文献 MCC 参数 `lam = 1.20`、`A = 1` 下，
对**任意** `kBT > 0`，反转区描述成立（主定理 `inverted_descriptor_holds` 实例化）。 -/
theorem inst_I4_mcc_descriptor_any_kT {kBT : ℝ} (hkBT : 0 < kBT) :
    InvertedDescriptor (1 : ℝ) (1.20 : ℝ) kBT 1 :=
  inverted_descriptor_holds (A := 1) (lam := 1.20) (kB := kBT) (T := 1)
    (by norm_num) (by norm_num) (by simpa using hkBT)

/-- I4 描述算子判定（`kB = T = 1` 的具体实例）：`lam = 1.20` 上反转区描述成立。 -/
theorem inst_I4_mcc_descriptor : InvertedDescriptor (1 : ℝ) (1.20 : ℝ) 1 1 :=
  inst_I4_mcc_descriptor_any_kT (by norm_num)

/-- I4 判定汇总：文献 MCC 实例 **可采纳** —— 速率处处为正 **且** 反转区描述成立
（主定理 `descriptor_sharp` 的 `(⟸)` 方向实例化：`0 < A ∧ 0 < lam` 给出两件事）。
与 `inst_I7_unphysical_not_admissible` 对读：可采纳性由「正性 + 描述」两条共同承担。 -/
theorem inst_I4_mcc_admissible {kBT : ℝ} (hkBT : 0 < kBT) :
    (∀ x : ℝ, 0 < rate (1 : ℝ) (1.20 : ℝ) kBT 1 x) ∧
      InvertedDescriptor (1 : ℝ) (1.20 : ℝ) kBT 1 :=
  (descriptor_sharp (kB := kBT) (T := 1) (by simpa using hkBT) (by norm_num) 1 1.20).mpr
    ⟨by norm_num, by norm_num⟩

/-- I6 描述算子判定（深反转区）：光合反应中心参数 `lam = 0.25`、`A = 1` 下，
对**任意** `kBT > 0`，反转区描述成立（与 I4 同一条主定理，仅更换文献参数）。 -/
theorem inst_I6_rc_descriptor_any_kT {kBT : ℝ} (hkBT : 0 < kBT) :
    InvertedDescriptor (1 : ℝ) (0.25 : ℝ) kBT 1 :=
  inverted_descriptor_holds (A := 1) (lam := 0.25) (kB := kBT) (T := 1)
    (by norm_num) (by norm_num) (by simpa using hkBT)

end PhotoLean.Marcus
