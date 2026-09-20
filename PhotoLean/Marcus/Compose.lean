/-
PhotoLean.Marcus.Compose — M4c：复合定理（theories/Marcus/plan.md §7.2；属主 prover_d）。

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

**语句权威**：`theories/Marcus/plan.md` §7.2 的 M4b/M4c 段 + `theories/Marcus/probes/marcus-statement-skeleton.lean`
（本文件两条定理的签名与之逐字一致；`hgeom_of_nonoverlap` 只出现在 `theories/Marcus/plan.md` §7.2 末尾，
骨架文件的 M4b 段**已回填它**（2026-09-20 补记；`theories/Marcus/TASKS.md` 验收记录有载），签名同样逐字一致）。

**验收**：`proofs/scripts/check.sh --strict PhotoLean.Marcus.Compose` **与**
`proofs/scripts/axioms.sh PhotoLean.Marcus.Compose <带命名空间的定理名>` 缺一不可
—— 单独构建通过不构成验收。

English: PhotoLean.Marcus.Compose — M4c: composition theorems (theories/Marcus/plan.md §7.2; owner prover_d).

Downgrades the hypothesis `0 < lam` of the M4a main theorem
(`PhotoLean.Marcus.inverted_descriptor_holds`) from "assumed" to "derived from the
microscopic parameters" — this is the complete shape of "finding the conditions under which
it holds":

    inner reorganization energy nonnegative (`lamInner_nonneg`; the force constant is
      allowed to be 0)
  + outer reorganization energy strictly positive (`lamOuter_pos`: geometric factor positive
    + Pekar factor positive)
  ⇒ total reorganization energy strictly positive (`lam_total_pos`)
  ⇒ the inverted-region descriptor holds (`inverted_descriptor_holds`; additionally needs
    `0 < A` and `0 < kB * T`).

## Module dependencies

- `PhotoLean.Marcus.Sharp` (M4a): the `InvertedDescriptor` definition chain
  + `inverted_descriptor_holds`;
- `PhotoLean.Marcus.Reorg` (M4b): `lamInner` / `lamOuter` and the three positivity lemmas
  (`lamInner_nonneg` / `lamOuter_pos` / `lam_total_pos`).

## Difference between the two theorems (strength of the geometric hypothesis)

- `descriptor_holds_of_microscopic`: geometric-factor positivity `hgeom` as an **explicit
  hypothesis** (the original version in plan §7.2).
- `descriptor_holds_of_nonoverlap` (the stretched version): replaces `hgeom` by the more
  basic geometric convention `a1 + a2 ≤ R` (the two spheres do not overlap), supplied by
  M4b's `hgeom_of_nonoverlap` — hence on the geometric side only "both sphere radii
  strictly positive + non-overlap" remains, and `hgeom` is no longer an independent
  assumption.

## Physical approximations (all made explicit as theorem hypotheses; none folded into definitions)

| Hypothesis | Physical meaning |
|---|---|
| `0 < A` | pre-exponential factor strictly positive (a necessary condition for rate positivity; M4a's sharpness has already shown it cannot be dropped) |
| `0 < kB` / `0 < T` | the domain of the thermal energy (their product is `kB · T > 0`) |
| `0 ≤ kk` | inner normal-mode force constant nonnegative (`kk = 0` means no inner reorganization, which is physically allowed) |
| `0 < dE` | the transferred charge is nonzero |
| `0 < a1` / `0 < a2` | both sphere radii strictly positive |
| `0 < R` | the center-to-center distance of the two spheres strictly positive |
| `hgeom` / `hRge` | geometric-factor positivity; the stretched version replaces it by "the two spheres do not overlap" `a1 + a2 ≤ R` |
| `0 < nSq` / `0 < epsS` | squared refractive index and static dielectric constant strictly positive (the domain of the Pekar factor) |
| `1 / epsS < 1 / nSq` | Pekar-factor positivity, equivalently `n² < ε_s` (a solvent-side sufficient condition for the existence of the inverted region) |

Note that `dq` **need not** be nonzero: here we take the broad formulation that only
requires the inner part to be nonnegative (`lamInner_nonneg`), which is wider than
`lamInner_pos` (which requires `kk > 0` **and** `dq ≠ 0`) — because the outer part already
supplies strict positivity on its own.

**Statement authority**: the M4b/M4c part of theories/Marcus/plan.md §7.2 plus
`theories/Marcus/probes/marcus-statement-skeleton.lean` (the signatures of the two theorems in this
file agree with it verbatim; `hgeom_of_nonoverlap` appears only at the end of theories/Marcus/plan.md §7.2,
and the M4b section of the skeleton file **has already been backfilled with it**
(backfilled 2026-09-20; recorded in the acceptance table of `theories/Marcus/TASKS.md`) — there too
the signature agrees verbatim).

**Acceptance**: `proofs/scripts/check.sh --strict PhotoLean.Marcus.Compose` **and**
`proofs/scripts/axioms.sh PhotoLean.Marcus.Compose <namespace-qualified theorem name>` —
both are indispensable; passing the build alone does not constitute acceptance.
-/

import PhotoLean.Marcus.Sharp
import PhotoLean.Marcus.Reorg

namespace PhotoLean.Marcus

/-- 复合定理：微观正性（内层非负 + 外层 Pekar 正性）⇒ 反转区描述成立。
    把主定理的前提 `lam > 0` 从"假设"降级为"由微观参数推出"。

    English: composition theorem: microscopic positivity (inner nonnegative + outer Pekar
    positivity) ⇒ the inverted-region descriptor holds. Downgrades the hypothesis
    `lam > 0` of the main theorem from "assumed" to "derived from the microscopic
    parameters".--/
theorem descriptor_holds_of_microscopic {A kB T kk dq dE a1 a2 R nSq epsS : ℝ} (hA : 0 < A)
    (hkB : 0 < kB) (hT : 0 < T) (hkk : 0 ≤ kk) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    InvertedDescriptor A (lamInner kk dq + lamOuter dE a1 a2 R nSq epsS) kB T :=
  -- 三步复合，全部由已验证的引理供给，本定理自身不含任何实质推理：
  -- English: a three-step composition; every ingredient is supplied by an already
  --          verified lemma, and this theorem itself contains no substantive reasoning:
  --   ① `lamInner_nonneg`（`kk ≥ 0`）+ `lamOuter_pos`（几何因子正 ∧ Pekar 因子正）
  -- English:   ① `lamInner_nonneg` (`kk ≥ 0`) + `lamOuter_pos` (geometric factor
  --          positive ∧ Pekar factor positive)
  --      ⇒ `lam_total_pos` 给出总重组能 `lamInner kk dq + lamOuter … > 0`；
  -- English:      ⇒ `lam_total_pos` gives the total reorganization energy
  --          `lamInner kk dq + lamOuter … > 0`;
  --   ② `mul_pos hkB hT` 给出 `kB * T > 0`；
  -- English:   ② `mul_pos hkB hT` gives `kB * T > 0`;
  --   ③ `inverted_descriptor_holds`（M4a）用 ①②与 `0 < A` 得描述。
  -- English:   ③ `inverted_descriptor_holds` (M4a) uses ①② and `0 < A` to obtain the
  --          descriptor.
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

English: ## Stretched version: replacing the geometric hypothesis with "the two spheres
do not overlap"

`descriptor_holds_of_microscopic` takes the geometric-factor positivity `hgeom` as a
hypothesis; the theorem below delegates it to M4b's `hgeom_of_nonoverlap`
(`a1 + a2 ≤ R ⇒ hgeom`). Hence **no "factor positivity"-style hypothesis remains on the
geometric side**: only `0 < a1`, `0 < a2` and the non-overlap condition `a1 + a2 ≤ R` are
left (`0 < R` is likewise downgraded to a conclusion). All other hypotheses are verbatim
identical to those of `descriptor_holds_of_microscopic`.
-/

/-- 复合定理（拉伸）：几何前提换成"两球不重叠" `a1 + a2 ≤ R` 的版本 ——
    `hgeom` 由 `hgeom_of_nonoverlap` 推出，不再是假设。

    English: composition theorem (stretched version): the version whose geometric hypothesis
    is replaced by "the two spheres do not overlap", `a1 + a2 ≤ R` — `hgeom` is then derived
    from `hgeom_of_nonoverlap` and is no longer an assumption.--/
theorem descriptor_holds_of_nonoverlap {A kB T kk dq dE a1 a2 R nSq epsS : ℝ} (hA : 0 < A)
    (hkB : 0 < kB) (hT : 0 < T) (hkk : 0 ≤ kk) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hRge : a1 + a2 ≤ R) (hnSq : 0 < nSq) (hepsS : 0 < epsS) (hPekar : 1 / epsS < 1 / nSq) :
    InvertedDescriptor A (lamInner kk dq + lamOuter dE a1 a2 R nSq epsS) kB T := by
  -- 本定理签名里**没有** `0 < R`（球心间距严格正）：它由 `0 < a1 + a2 ≤ R` 推出，
  -- English: the signature of this theorem does **not** contain `0 < R` (strict
  --          positivity of the center-to-center distance): it is derived from
  --          `0 < a1 + a2 ≤ R`,
  -- 是结论而不是假设 —— 物理上"不重叠 + 半径正"已经把 `R` 限制在正半轴。
  -- English: so it is a conclusion rather than a hypothesis — physically,
  --          "non-overlap + positive radii" already confines `R` to the positive
  --          half-axis.
  have hR : 0 < R := lt_of_lt_of_le (by linarith : (0 : ℝ) < a1 + a2) hRge
  -- 唯一的实质步骤：几何因子正性由"两球不重叠"推出（M4b 的 `hgeom_of_nonoverlap`），
  -- English: the only substantive step: geometric-factor positivity is derived from
  --          "the two spheres do not overlap" (M4b's `hgeom_of_nonoverlap`),
  -- 之后与 `descriptor_holds_of_microscopic` 完全同构。
  -- English: after which it is completely isomorphic to
  --          `descriptor_holds_of_microscopic`.
  exact descriptor_holds_of_microscopic hA hkB hT hkk hdE ha1 ha2 hR
    (hgeom_of_nonoverlap ha1 ha2 hRge) hnSq hepsS hPekar

end PhotoLean.Marcus
