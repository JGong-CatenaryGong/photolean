/-
prover_c 探针 2（M5a 追加：`barrierQ_cast` / `barrierQ_zero_lam`）。

**只属 prover_c**（文件名 `marcus-prover_c2-scratch.lean`）。
目的：在动 `PhotoLean/Marcus/RatModel.lean` 之前，先把
  1. cast 引理名（`Rat.cast_pow` / `Rat.cast_mul` / `Rat.cast_sub` / `Rat.cast_ofNat` …）
  2. **`lam = 0` 退化情形是否需要前提**（不给任何假设，直接证）
  3. `barrierQ_zero_lam` 的两条路线（复用 ℝ 侧 / 直接 `simp`）
在本文件实测确认。结论回写报告；本文件本身不参与验收门。

运行：`proofs/scripts/lake env lean proofs/probes/marcus-prover_c2-scratch.lean`
-/
import PhotoLean.Marcus.RatModel

namespace PhotoLean.Marcus.Rat.ProbeC2

/-! ## A — cast 引理名（先 #check，绝不猜名） -/

#check @Rat.cast_pow
#check @Rat.cast_mul
#check @Rat.cast_sub
#check @Rat.cast_div
#check @Rat.cast_ofNat
#check @Rat.cast_natCast
#check @Rat.cast_inv
#check @Rat.cast_zero
#check @Rat.cast_inj
#check @Rat.cast_add

/-! ## B — 主目标：路线 1（`push_cast` + `ring`） -/

/-- 路线 1（**交付采用**）：`push_cast` 把两侧归一到同一个项，再 `ring` 收尾。

实测（本探针 + 最小对照）：`push_cast` **单独不够** —— 它留下目标
`(↑lam - ↑x)^2/(4*↑lam) = (↑lam - ↑x)^2/(4*↑lam)`（不自带 `rfl` 收尾），
必须补 `ring`（或 `rfl`）。**不带任何前提**（含 `lam = 0`）。--/
theorem barrierQ_cast_pushcast (lam x : ℚ) :
    ((barrierQ lam x : ℚ) : ℝ) = barrier (lam : ℝ) (x : ℝ) := by
  unfold barrierQ barrier
  push_cast
  ring

/-! ## C — 主目标：路线 2（显式 `rw` 一串 cast 引理）—— 更可读的退路

实测：`rw` 链**自己就把目标关掉**（`rw` 内建 `rfl` 收尾），后面再写 `ring`
报 `no goals to be solved`。故本路线**不能**有尾巴战术。 -/

/-- 路线 2：显式列出五条 cast 引理，无尾巴战术。--/
theorem barrierQ_cast_rw (lam x : ℚ) :
    ((barrierQ lam x : ℚ) : ℝ) = barrier (lam : ℝ) (x : ℝ) := by
  unfold barrierQ barrier
  rw [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]

/-! ## D — 退化情形取证：`lam = 0` / `lam < 0` 上主目标**无前提**成立

若下面三条任何一条需要额外前提，说明"两侧都走 `x/0 = 0` 约定"的说法不成立。
三条都编译通过 ⇒ 主定理**不需要前提**。
⚠️ 与 API-NOTES C-2 同款坑：`((0 : ℚ) : ℝ)` 与 `(0 : ℝ)` **不是 defeq**，
所以 ℝ 侧参数必须逐字写成 `((0 : ℚ) : ℝ)`（或 `norm_num` 桥接）。 -/

example (x : ℚ) : ((barrierQ 0 x : ℚ) : ℝ) = barrier ((0 : ℚ) : ℝ) (x : ℝ) :=
  barrierQ_cast_pushcast 0 x

example (x : ℚ) : ((barrierQ (1 / 2) x : ℚ) : ℝ) = barrier (((1 : ℚ) / 2 : ℚ) : ℝ) (x : ℝ) :=
  barrierQ_cast_pushcast (1 / 2) x

example (x : ℚ) : ((barrierQ (-3) x : ℚ) : ℝ) = barrier (((-3 : ℚ)) : ℝ) (x : ℝ) :=
  barrierQ_cast_pushcast (-3) x

/-- 数值核对（`lam = 0`）：两侧**都**是 0 —— 除零约定使桥在退化点也成立。--/
example : ((barrierQ 0 (7 / 3) : ℚ) : ℝ) = 0 := by
  rw [barrierQ_cast_pushcast]
  norm_num [barrier]

/-! ## E — `barrierQ_zero_lam`：两条路线 -/

/-- 路线 E1：经 `barrierQ_cast` 桥到 ℝ 侧，再在 ℝ 上算退化值（**不引入 Barrier.lean 依赖**）。
⚠️ `Rat.cast_inj` 的 `α` 在 `apply` 下会卡住（`CharZero ?m` 无法求解）——
必须显式写 `(Rat.cast_inj (α := ℝ))`。--/
theorem barrierQ_zero_lam_via_cast (x : ℚ) : barrierQ 0 x = 0 := by
  apply (Rat.cast_inj (α := ℝ)).mp
  rw [barrierQ_cast_pushcast]
  simp [barrier]

/-- 路线 E2：不经桥，直接在 ℚ 上算（对照用；若 E1 通过则交付用 E1）。--/
theorem barrierQ_zero_lam_direct (x : ℚ) : barrierQ 0 x = 0 := by
  simp [barrierQ]

/-! ## F — 对照：若将来有人试图用 `rw [Rat.cast_lt]` 类**非 cast 消除**引理走这条路会怎样，
此处不改写 —— 只记录本探针 0 error / 0 warning 即可。 -/

end PhotoLean.Marcus.Rat.ProbeC2
