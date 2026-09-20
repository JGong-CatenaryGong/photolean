/-
prover_c 探针 2（M5a 追加：`barrierQ_cast` / `barrierQ_zero_lam`）。

**只属 prover_c**（文件名 `marcus-prover_c2-scratch.lean`）。
目的：在动 `PhotoLean/Marcus/RatModel.lean` 之前，先把
  1. cast 引理名（`Rat.cast_pow` / `Rat.cast_mul` / `Rat.cast_sub` / `Rat.cast_ofNat` …）
  2. **`lam = 0` 退化情形是否需要前提**（不给任何假设，直接证）
  3. `barrierQ_zero_lam` 的两条路线（复用 ℝ 侧 / 直接 `simp`）
在本文件实测确认。结论回写报告；本文件本身不参与验收门。

运行：`proofs/scripts/lake env lean proofs/probes/marcus-prover_c2-scratch.lean`

prover_c probe 2 (M5a addition: `barrierQ_cast` / `barrierQ_zero_lam`).

**Owned by prover_c only** (file name `marcus-prover_c2-scratch.lean`).
Purpose: before touching `PhotoLean/Marcus/RatModel.lean`, first confirm by experiment in this file:
  1. the cast lemma names (`Rat.cast_pow` / `Rat.cast_mul` / `Rat.cast_sub` / `Rat.cast_ofNat` …)
  2. **whether the degenerate case `lam = 0` needs a hypothesis** (no hypothesis given; prove it directly)
  3. the two routes for `barrierQ_zero_lam` (reuse the ℝ side / direct `simp`)
Conclusions are written back into the report; this file itself does not participate in the acceptance gate.

Run: `proofs/scripts/lake env lean proofs/probes/marcus-prover_c2-scratch.lean`
-/
import PhotoLean.Marcus.RatModel

namespace PhotoLean.Marcus.Rat.ProbeC2

/-! ## A — cast 引理名（先 #check，绝不猜名）

## A — cast lemma names (#check first; never guess a name)
-/

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

/-! ## B — 主目标：路线 1（`push_cast` + `ring`）

## B — main goal: route 1 (`push_cast` + `ring`)
-/

/-- 路线 1（**交付采用**）：`push_cast` 把两侧归一到同一个项，再 `ring` 收尾。

实测（本探针 + 最小对照）：`push_cast` **单独不够** —— 它留下目标
`(↑lam - ↑x)^2/(4*↑lam) = (↑lam - ↑x)^2/(4*↑lam)`（不自带 `rfl` 收尾），
必须补 `ring`（或 `rfl`）。**不带任何前提**（含 `lam = 0`）。

Route 1 (**adopted for delivery**): `push_cast` normalizes both sides to the same term, and `ring` finishes it off.

Measured (this probe + a minimal control): `push_cast` **alone is not enough** — it leaves the goal
`(↑lam - ↑x)^2/(4*↑lam) = (↑lam - ↑x)^2/(4*↑lam)` (no built-in `rfl` finish),
so `ring` (or `rfl`) must be added. **With no hypothesis at all** (including `lam = 0`).
-/
theorem barrierQ_cast_pushcast (lam x : ℚ) :
    ((barrierQ lam x : ℚ) : ℝ) = barrier (lam : ℝ) (x : ℝ) := by
  unfold barrierQ barrier
  push_cast
  ring

/-! ## C — 主目标：路线 2（显式 `rw` 一串 cast 引理）—— 更可读的退路

实测：`rw` 链**自己就把目标关掉**（`rw` 内建 `rfl` 收尾），后面再写 `ring`
报 `no goals to be solved`。故本路线**不能**有尾巴战术。

## C — main goal: route 2 (explicit `rw` over a chain of cast lemmas) — the more readable fallback

Measured: the `rw` chain **closes the goal by itself** (`rw` has a built-in `rfl` finish), so writing
`ring` afterwards reports `no goals to be solved`. Hence this route **must not** have a trailing tactic.
-/

/-- 路线 2：显式列出五条 cast 引理，无尾巴战术。

Route 2: explicitly list the five cast lemmas; no trailing tactic.
-/
theorem barrierQ_cast_rw (lam x : ℚ) :
    ((barrierQ lam x : ℚ) : ℝ) = barrier (lam : ℝ) (x : ℝ) := by
  unfold barrierQ barrier
  rw [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]

/-! ## D — 退化情形取证：`lam = 0` / `lam < 0` 上主目标**无前提**成立

若下面三条任何一条需要额外前提，说明"两侧都走 `x/0 = 0` 约定"的说法不成立。
三条都编译通过 ⇒ 主定理**不需要前提**。
⚠️ 与 API-NOTES C-2 同款坑：`((0 : ℚ) : ℝ)` 与 `(0 : ℝ)` **不是 defeq**，
所以 ℝ 侧参数必须逐字写成 `((0 : ℚ) : ℝ)`（或 `norm_num` 桥接）。

## D — evidence on the degenerate cases: on `lam = 0` / `lam < 0` the main goal holds **with no hypothesis**

If any of the three statements below needed an extra hypothesis, the claim that "both sides follow the `x/0 = 0` convention" would fail.
All three compile ⇒ the main theorem **needs no hypothesis**.
⚠️ Same trap as API-NOTES C-2: `((0 : ℚ) : ℝ)` and `(0 : ℝ)` are **not defeq**,
so the ℝ-side argument must be written literally as `((0 : ℚ) : ℝ)` (or bridged with `norm_num`).
-/

example (x : ℚ) : ((barrierQ 0 x : ℚ) : ℝ) = barrier ((0 : ℚ) : ℝ) (x : ℝ) :=
  barrierQ_cast_pushcast 0 x

example (x : ℚ) : ((barrierQ (1 / 2) x : ℚ) : ℝ) = barrier (((1 : ℚ) / 2 : ℚ) : ℝ) (x : ℝ) :=
  barrierQ_cast_pushcast (1 / 2) x

example (x : ℚ) : ((barrierQ (-3) x : ℚ) : ℝ) = barrier (((-3 : ℚ)) : ℝ) (x : ℝ) :=
  barrierQ_cast_pushcast (-3) x

/-- 数值核对（`lam = 0`）：两侧**都**是 0 —— 除零约定使桥在退化点也成立。

Numeric cross-check (`lam = 0`): **both** sides are 0 — the division-by-zero convention makes the bridge hold at the degenerate point as well.
-/
example : ((barrierQ 0 (7 / 3) : ℚ) : ℝ) = 0 := by
  rw [barrierQ_cast_pushcast]
  norm_num [barrier]

/-! ## E — `barrierQ_zero_lam`：两条路线

## E — `barrierQ_zero_lam`: the two routes
-/

/-- 路线 E1：经 `barrierQ_cast` 桥到 ℝ 侧，再在 ℝ 上算退化值（**不引入 Barrier.lean 依赖**）。
⚠️ `Rat.cast_inj` 的 `α` 在 `apply` 下会卡住（`CharZero ?m` 无法求解）——
必须显式写 `(Rat.cast_inj (α := ℝ))`。

Route E1: bridge to the ℝ side via `barrierQ_cast`, then compute the degenerate value over ℝ (**without introducing a Barrier.lean dependency**).
⚠️ Under `apply`, the `α` of `Rat.cast_inj` gets stuck (`CharZero ?m` cannot be solved) —
so it must be written explicitly as `(Rat.cast_inj (α := ℝ))`.
-/
theorem barrierQ_zero_lam_via_cast (x : ℚ) : barrierQ 0 x = 0 := by
  apply (Rat.cast_inj (α := ℝ)).mp
  rw [barrierQ_cast_pushcast]
  simp [barrier]

/-- 路线 E2：不经桥，直接在 ℚ 上算（对照用；若 E1 通过则交付用 E1）。

Route E2: no bridge; compute directly over ℚ (for comparison; if E1 passes, delivery uses E1).
-/
theorem barrierQ_zero_lam_direct (x : ℚ) : barrierQ 0 x = 0 := by
  simp [barrierQ]

/-! ## F — 交付定理的 `#check`（签名逐字取证）+ 数值交叉核对

`G1` 段的 `#check` 是**交付版**（`PhotoLean/Marcus/RatModel.lean` 末尾的追加），
不是本探针的副本 —— 用于证明交付签名与任务书逐字一致。
`G2` 段把交付定理实例化到四个点（含 `lam = 0` 退化点与 `lam < 0`），
两侧都用 `norm_num` 独立算出同一个数：这是"**无前提**"的数值取证。

## F — `#check` of the delivered theorems (verbatim evidence for the signatures) + numeric cross-check

The `#check`s in section `G1` are the **delivered versions** (the additions at the end of `PhotoLean/Marcus/RatModel.lean`),
not copies from this probe — they serve to show that the delivered signatures agree verbatim with the task statement.
Section `G2` instantiates the delivered theorems at four points (including the `lam = 0` degenerate point and `lam < 0`),
and both sides independently compute the same number with `norm_num`: this is the numeric evidence for "**no hypothesis**".
-/

/-! ### G1 — 交付签名

### G1 — delivered signatures
-/

#check PhotoLean.Marcus.Rat.barrierQ_cast
#check PhotoLean.Marcus.Rat.barrierQ_zero_lam

/-! ### G2 — 数值交叉核对（左列 ℚ 侧值，右列经交付定理搬到 ℝ 的值）

### G2 — numeric cross-check (left column: values on the ℚ side; right column: values transported to ℝ by the delivered theorems)
-/

/-- `lam = 1, x = 3`：`(1-3)²/(4·1) = 1`。

`lam = 1, x = 3`: `(1-3)²/(4·1) = 1`.
-/
example : ((barrierQ 1 3 : ℚ) : ℝ) = 1 := by rw [PhotoLean.Marcus.Rat.barrierQ_cast]; norm_num [barrier]

/-- `lam = 1/2, x = 1/4`：`(1/4)²/2 = 1/32`（分数参数，非整数字面量）。

`lam = 1/2, x = 1/4`: `(1/4)²/2 = 1/32` (fractional arguments, not integer literals).
-/
example : ((barrierQ (1 / 2) (1 / 4) : ℚ) : ℝ) = 1 / 32 := by
  rw [PhotoLean.Marcus.Rat.barrierQ_cast]; norm_num [barrier]

/-- `lam = -3, x = 0`：`9/(-12) = -3/4`（**负重组能**，`lam ≠ 0`，非退化）。

`lam = -3, x = 0`: `9/(-12) = -3/4` (**negative reorganization energy**, `lam ≠ 0`, non-degenerate).
-/
example : ((barrierQ (-3) 0 : ℚ) : ℝ) = -3 / 4 := by
  rw [PhotoLean.Marcus.Rat.barrierQ_cast]; norm_num [barrier]

/-- `lam = 0` 退化点：两侧**各自**坍缩为 0（`x/0 = 0`）—— 等式成立但不含数值内容。

The `lam = 0` degenerate point: **each** side collapses to 0 (`x/0 = 0`) — the equality holds but carries no numeric content.
-/
example : ((barrierQ 0 (7 / 3) : ℚ) : ℝ) = 0 := by
  rw [PhotoLean.Marcus.Rat.barrierQ_cast]; norm_num [barrier]

/-- ℚ 侧同点独立计算（不经桥），用于与上面第 4 条对拍。

Independent computation at the same point on the ℚ side (no bridge), used to cross-check against item 4 above.
-/
example : barrierQ 0 (7 / 3) = 0 := PhotoLean.Marcus.Rat.barrierQ_zero_lam (7 / 3)

end PhotoLean.Marcus.Rat.ProbeC2
