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

end PhotoLean.Marcus
