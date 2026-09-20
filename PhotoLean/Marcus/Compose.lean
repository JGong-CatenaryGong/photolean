/-
PhotoLean.Marcus.Compose — M4c：复合定理（plan.md §7.2；属主 prover_d）。

把 M4a 主定理（`PhotoLean.Marcus.inverted_descriptor_holds`）的前提 `0 < lam` 从"假设"
降级为"由微观参数推出" —— 这才是"找到成立条件"的完整形态：

    内层重组能非负（`lamInner_nonneg`，力常数允许为 0）
  + 外层重组能严格正（`lamOuter_pos`：几何因子正 + Pekar 因子正）
  ⇒ 总重组能严格正（`lam_total_pos`）
  ⇒ 反转区描述成立（`inverted_descriptor_holds`，另需 `0 < A` 与 `0 < kB * T`）。

## 模块依赖

- `PhotoLean.Marcus.Sharp`（M4a）：`InvertedDescriptor` 定义链 + `inverted_descriptor_holds`；
- `PhotoLean.Marcus.Reorg`（M4b）：`lamInner` / `lamOuter` 与三条正性引理
  （`lamInner_nonneg` / `lamOuter_pos` / `lam_total_pos`）。

## 两条定理的差别（几何前提的强弱）

- `descriptor_holds_of_microscopic`：几何因子正性 `hgeom` 作为**显式前提**（plan §7.2 原件）。
- `descriptor_holds_of_nonoverlap`（拉伸）：把 `hgeom` 换成更基本的几何约定
  `a1 + a2 ≤ R`（两球不重叠），由 M4b 的 `hgeom_of_nonoverlap` 供给 —— 于是几何侧
  只剩下"两球半径严格正 + 不重叠"，`hgeom` 不再是独立假设。

## 物理近似（全部显式化为定理前提，不得折叠进定义）

| 前提 | 物理含义 |
|---|---|
| `0 < A` | 指前因子严格正（速率正性的必要条件，M4a 的锐利性已证其不可去） |
| `0 < kB` / `0 < T` | 热能的定义域（两者相乘即 `kB · T > 0`） |
| `0 ≤ kk` | 内层简正模式力常数非负（`kk = 0` 表示无内层重组，物理上允许） |
| `0 < dE` | 转移电荷量非零 |
| `0 < a1` / `0 < a2` | 两球半径严格正 |
| `0 < R` | 两球球心间距严格正 |
| `hgeom` / `hRge` | 几何因子正性；拉伸版换成"两球不重叠" `a1 + a2 ≤ R` |
| `0 < nSq` / `0 < epsS` | 折射率平方、静态介电常数严格正（Pekar 因子的定义域） |
| `1 / epsS < 1 / nSq` | Pekar 因子正性，等价 `n² < ε_s`（反转区存在的溶剂侧充分条件） |

注意 `dq` **不需要**非零：这里走的是"内层只要求非负"的宽口径（`lamInner_nonneg`），
比 `lamInner_pos`（要求 `kk > 0` **且** `dq ≠ 0`）更宽 —— 因为外层已单独提供严格正性。

**语句权威**：`plan.md` §7.2 的 M4b/M4c 段 + `proofs/probes/marcus-statement-skeleton.lean`
（本文件两条定理的签名与之逐字一致；`hgeom_of_nonoverlap` 只出现在 `plan.md` §7.2 末尾，
骨架文件的 M4b 段尚未回填它，签名同样逐字一致）。

**验收**：`proofs/scripts/check.sh --strict PhotoLean.Marcus.Compose` **与**
`proofs/scripts/axioms.sh PhotoLean.Marcus.Compose <带命名空间的定理名>` 缺一不可
—— 单独构建通过不构成验收。
-/

import PhotoLean.Marcus.Sharp
import PhotoLean.Marcus.Reorg

namespace PhotoLean.Marcus

/-- 复合定理：微观正性（内层非负 + 外层 Pekar 正性）⇒ 反转区描述成立。
    把主定理的前提 `lam > 0` 从"假设"降级为"由微观参数推出"。--/
theorem descriptor_holds_of_microscopic {A kB T kk dq dE a1 a2 R nSq epsS : ℝ} (hA : 0 < A)
    (hkB : 0 < kB) (hT : 0 < T) (hkk : 0 ≤ kk) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    InvertedDescriptor A (lamInner kk dq + lamOuter dE a1 a2 R nSq epsS) kB T :=
  -- 三步复合，全部由已验证的引理供给，本定理自身不含任何实质推理：
  --   ① `lamInner_nonneg`（`kk ≥ 0`）+ `lamOuter_pos`（几何因子正 ∧ Pekar 因子正）
  --      ⇒ `lam_total_pos` 给出总重组能 `lamInner kk dq + lamOuter … > 0`；
  --   ② `mul_pos hkB hT` 给出 `kB * T > 0`；
  --   ③ `inverted_descriptor_holds`（M4a）用 ①②与 `0 < A` 得描述。
  inverted_descriptor_holds hA
    (lam_total_pos (lamInner_nonneg hkk dq)
      (lamOuter_pos hdE ha1 ha2 hR hgeom hnSq hepsS hPekar))
    (mul_pos hkB hT)

/-!
## 拉伸：把几何前提换成"两球不重叠"

`descriptor_holds_of_microscopic` 把几何因子正性 `hgeom` 当假设；下面这条把它交给 M4b 的
`hgeom_of_nonoverlap`（`a1 + a2 ≤ R ⇒ hgeom`）。于是**几何侧不再有任何"因子正性"式的假设**：
只剩 `0 < a1`、`0 < a2` 与两球不重叠 `a1 + a2 ≤ R`（`0 < R` 也随之降级为结论）。
其余前提与 `descriptor_holds_of_microscopic` 逐字相同。
-/

/-- 复合定理（拉伸）：几何前提换成"两球不重叠" `a1 + a2 ≤ R` 的版本 ——
    `hgeom` 由 `hgeom_of_nonoverlap` 推出，不再是假设。--/
theorem descriptor_holds_of_nonoverlap {A kB T kk dq dE a1 a2 R nSq epsS : ℝ} (hA : 0 < A)
    (hkB : 0 < kB) (hT : 0 < T) (hkk : 0 ≤ kk) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hRge : a1 + a2 ≤ R) (hnSq : 0 < nSq) (hepsS : 0 < epsS) (hPekar : 1 / epsS < 1 / nSq) :
    InvertedDescriptor A (lamInner kk dq + lamOuter dE a1 a2 R nSq epsS) kB T := by
  -- 本定理签名里**没有** `0 < R`（球心间距严格正）：它由 `0 < a1 + a2 ≤ R` 推出，
  -- 是结论而不是假设 —— 物理上"不重叠 + 半径正"已经把 `R` 限制在正半轴。
  have hR : 0 < R := lt_of_lt_of_le (by linarith : (0 : ℝ) < a1 + a2) hRge
  -- 唯一的实质步骤：几何因子正性由"两球不重叠"推出（M4b 的 `hgeom_of_nonoverlap`），
  -- 之后与 `descriptor_holds_of_microscopic` 完全同构。
  exact descriptor_holds_of_microscopic hA hkB hT hkk hdE ha1 ha2 hR
    (hgeom_of_nonoverlap ha1 ha2 hRge) hnSq hepsS hPekar

end PhotoLean.Marcus
