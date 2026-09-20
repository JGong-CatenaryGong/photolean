/-
prover_c 探针（M5a / M5b）— 非交付文件，只用于实测 ℚ 上判定（`decide` vs `norm_num`）的真实边界。

**为什么需要**：M5b（Instances.lean）要给每个实例一条"判断"证据，证据形态取决于
哪些 ℚ 目标能被内核算出来。这里逐条实测并把可算/不可算的边界固定下来。

运行：
  proofs/scripts/lake env lean proofs/probes/marcus-prover_c-scratch.lean

期望输出：**只有标记为「预期 ERROR」的若干行报错**，其余全部静默通过。
-/
import PhotoLean.Marcus.Basic

namespace PhotoLean.Marcus.ProbeC

open PhotoLean.Marcus

/-- 与 `RatModel.lean` 中同名定义一致（探针里重复一份，避免依赖尚未提交的文件）。--/
def zoneQ (lam x : ℚ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

def barrierQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-! ## E1 — `decide` 对**整数**字面量：可用 -/

example : zoneQ (1 : ℚ) 3 = Zone.inverted := by decide
example : zoneQ (1 : ℚ) 1 = Zone.barrierless := by decide
example : zoneQ (1 : ℚ) (-3) = Zone.normal := by decide
example : ¬ zoneQ (1 : ℚ) 3 = Zone.normal := by decide

/-! ## E2 — `decide` 对**含除法**的有理字面量：预期 ERROR（内核卡在 Rat 的 gcd/除法归约）

如果不报错，说明本 toolchain 行为与 Sprint 0 记录不同（M5b 需重新评估）。 -/

-- 预期 ERROR: 'Decidable' instance did not reduce to 'isTrue' or 'isFalse'
example : zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by decide
-- 预期 ERROR：根因不是 `zoneQ`，而是 ℚ 上的除法比较本身就不可 `decide`
example : (3 : ℚ) / 4 < 1 := by decide
-- 预期 ERROR：等式形态同样不可 `decide`
example : (4 : ℚ) / 4 = 1 := by decide

/-! ## E3 — `norm_num`：含除法的有理字面量**可以**算 -/

example : zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by norm_num [zoneQ]
example : zoneQ (1 : ℚ) (6 / 8) = Zone.normal := by norm_num [zoneQ]
example : zoneQ ((-1 : ℚ) / 2) (1 : ℚ) = Zone.inverted := by norm_num [zoneQ]
example : zoneQ ((1 : ℚ) / 2) (1 : ℚ) = Zone.inverted := by norm_num [zoneQ]
-- 假语句：`norm_num [zoneQ]` 必须失败（证明确实在判定，而不是放行）
-- 预期 ERROR: norm_num 无法闭合目标
example : zoneQ (1 : ℚ) (3 / 4) = Zone.inverted := by norm_num [zoneQ]

/-! ## E4 — `barrierQ`（含除法）：`decide` 与 `norm_num` 的差别 -/

-- 预期 ERROR：`(4 : ℚ) / 4` 的归约同样卡住
example : barrierQ (1 : ℚ) 3 = 1 := by decide
example : barrierQ (1 : ℚ) 3 = 1 := by norm_num [barrierQ]
example : barrierQ (1 : ℚ) (1 / 2) = (1 : ℚ) / 16 := by norm_num [barrierQ]

/-! ## E5 — 结论性边界：`decide` 可用的 ℚ 目标形态 -/

-- 无除法参与时，`decide` 对 ℚ 的线性序与相等是可算的
example : (3 : ℚ) < 5 := by decide
example : (3 : ℚ) ≠ 5 := by decide
example : (1 : ℚ) = 1 := by decide
-- 十进制字面量本质是有理数除法，同样不可 `decide`
-- 预期 ERROR
example : (0.75 : ℚ) < 1 := by decide

end PhotoLean.Marcus.ProbeC
