/-
PhotoLean.Marcus.RatModel — M5a：ℚ 上的判定层（可分派的分类器）。

**语句权威**：`proofs/probes/marcus-statement-skeleton.lean` 的 M5a 段（Sprint 0 已编译通过）。
本文件的 2 个定义与 2 条定理的签名与它**逐字一致**。

**为什么要 ℚ 副本**：`ℝ` 上的序经 `Classical`，**不可计算**，因此"某实例属于哪个区"
在 ℝ 上无法由内核算出。`ℚ` 上 `Rat` 的序与相等都可判定，于是判定层的证据链是：
内核计算（`by decide` / `norm_num`）→ 转移引理 `zoneQ_eq_zone` → ℝ 侧 `zone_eq_inverted_iff`。
转移引理就是"ℚ 上的判定对 ℝ 理论有约束力"的依据（plan §2.3）。

**实测边界**（prover_c 探针 `proofs/probes/marcus-prover_c-scratch.lean`）：
`by decide` 只对**整数**字面量可算（如 `zoneQ 1 3`）；对**含除法**的有理字面量
（如 `zoneQ 1 (3/4)`）会卡在 `Rat` 的 gcd/除法归约上，必须改用 `norm_num [zoneQ]`。

**命名约定（工具链硬约束）**：Lean 4 中 `λ` 是 lambda 关键字，不可作标识符，
故物理记号一律 ASCII 化：重组能 `lam`、驱动力 `x`。

验收（契约 `proofs/ENGINE.yml`）：
  proofs/scripts/lake build PhotoLean.Marcus.RatModel
  proofs/scripts/check.sh --strict PhotoLean.Marcus.RatModel
  proofs/scripts/axioms.sh PhotoLean.Marcus.RatModel PhotoLean.Marcus.Rat.<theorem>
-/
import PhotoLean.Marcus.Basic

namespace PhotoLean.Marcus.Rat

/-! ## 定义（plan §2.3 / §8.1） -/

/-- ℚ 上的分类器（可计算：`Rat` 的序与相等都可判定）。--/
def zoneQ (lam x : ℚ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

/-- ℚ 上的马库斯势垒：`(lam - x)^2 / (4 lam)`（与 ℝ 版 `barrier` 同式，供数值判定用）。--/
def barrierQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-! ## 转移引理（plan §2.3 / §8.1）
分类器在两层的 `if` 结构上完全相同，唯一要做的是把 ℚ 的比较/相等搬到 ℝ：
`Rat.cast_lt` / `Rat.cast_inj`（**隐式** `K`，故必须给出目标类型，否则实例求解卡住）。 -/

/-- 转移引理：ℚ 上的判定与 ℝ 上的分类一致。--/
theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ) := by
  unfold zoneQ zone
  by_cases h : x < lam
  · have h' : (x : ℝ) < (lam : ℝ) := Rat.cast_lt.mpr h
    simp [h, h']
  · have h' : ¬ (x : ℝ) < (lam : ℝ) := fun hc => h (Rat.cast_lt.mp hc)
    by_cases h2 : x = lam
    · have h2' : (x : ℝ) = (lam : ℝ) := by exact_mod_cast h2
      simp [h, h2, h', h2']
    · have h2' : ¬ (x : ℝ) = (lam : ℝ) := fun hc => h2 (Rat.cast_inj.mp hc)
      simp [h, h2, h', h2']

/-- 反转区判定：把 ℚ 上的可计算判定接到 ℝ 侧的 `InvertedRegion` 上。
证明是 M1 的 `zone_eq_inverted_iff` 与转移引理的直接拼接（`InvertedRegion` 是 `def`，
故两侧命题在定义层就是同一个）。--/
theorem zoneQ_inverted_iff (lam x : ℚ) : zoneQ lam x = Zone.inverted ↔ (lam : ℝ) < (x : ℝ) := by
  rw [zoneQ_eq_zone, zone_eq_inverted_iff]
  exact Iff.rfl

/-! ## M5a 追加：数值转移引理（补 verifier 在 M3+M5a 验收中的发现 (b)）

分类器有桥（`zoneQ_eq_zone`），但 ℚ 侧势垒 `barrierQ` 此前**没有任何伴随定理** ——
相对 ℝ 理论它是一个未被约束的定义，M5b 若用 ℚ 侧势垒数值取证就会缺乏依据。
下面补上**数值的桥**：ℚ 侧势垒经 cast 与 ℝ 侧 `barrier` 一致。

**不需要任何前提**（含 `lam = 0` 的除零情形）：两侧的除法都走 Lean 的 `x / 0 = 0`
约定，故退化点同样成立。取证见探针 `proofs/probes/marcus-prover_c2-scratch.lean`
的 D 段（`lam = 0` / `lam = 1/2` / `lam = -3` 三条**无前提**版本）与 E 段。

**依赖边界**：本条**不**新增 `import`（M5a 按 plan §S2 只依赖 M1 的 `Basic.lean`）；
因此 `lam = 0` 的 ℝ 侧退化值在证明内用一行 `simp [barrier]` 现算，
而不去引用 M2 的 `barrier_zero_lam`（那会把 M5a 的依赖拉到 M2）。 -/

/-- ℚ 侧势垒与 ℝ 侧势垒经 cast 一致 —— 让 `barrierQ` 与 ℝ 理论层挂上钩
    （`zoneQ_eq_zone` 是分类器的桥；这是数值的桥）。--/
theorem barrierQ_cast (lam x : ℚ) : ((barrierQ lam x : ℚ) : ℝ) = barrier (lam : ℝ) (x : ℝ) := by
  unfold barrierQ barrier
  push_cast
  ring

/-- 退化情形的显式变体：`lam = 0` 时 ℚ 侧势垒恒为 0（`x / 0 = 0` 约定）。
经上面的数值桥退到 ℝ 侧再收，不另起一套计算。--/
theorem barrierQ_zero_lam (x : ℚ) : barrierQ 0 x = 0 := by
  apply (Rat.cast_inj (α := ℝ)).mp
  rw [barrierQ_cast]
  simp [barrier]

end PhotoLean.Marcus.Rat
