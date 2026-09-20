/-
prover_c 探针（M5a 判定层 / M5b 实例判定）— 非交付文件。

**为什么需要**：M5b（`Instances.lean`）要给每个实例一条"判断"证据，证据形态取决于
哪些 ℚ 目标能被内核算出来、以及 ℚ 判定如何搬到 ℝ 侧。本探针把这两件事实测固定下来。

**本探针 `import PhotoLean.Marcus.RatModel`**，测的就是**已交付模块**里的
`zoneQ` / `barrierQ` / `zoneQ_eq_zone` / `zoneQ_inverted_iff`，不是副本。

运行：
  proofs/scripts/lake env lean proofs/probes/marcus-prover_c-scratch.lean

期望：**0 error**（负结果以注释形式登记，附实测报错原文）。
-/
import PhotoLean.Marcus.RatModel

namespace PhotoLean.Marcus.ProbeC

open PhotoLean.Marcus
open PhotoLean.Marcus.Rat

/-! ## E1 — `decide` 对**整数**字面量：可用（内核真算） -/

example : zoneQ (1 : ℚ) 3 = Zone.inverted := by decide
example : zoneQ (1 : ℚ) 1 = Zone.barrierless := by decide
example : zoneQ (1 : ℚ) (-3) = Zone.normal := by decide
example : ¬ zoneQ (1 : ℚ) 3 = Zone.normal := by decide

/-! ## E2 — 【负结果·实测】`decide` 对**含除法**的有理字面量：**不可用**

内核卡在 `Rat` 的 gcd/除法归约上。实测报错（2026-09-20，prover_c）：

  example : zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by decide
  -- error: tactic 'decide' failed for proposition `zoneQ 1 (3 / 4) = Zone.normal`
  --   since its 'Decidable' instance … did not reduce to 'isTrue' or 'isFalse'.
  --   After unfolding … reduction got stuck at the 'Decidable' instance
  --     match (3 / 4).blt 1, true with …
  example : (3 : ℚ) / 4 < 1 := by decide      -- 同样 ERROR（根因不是 zoneQ，而是 ℚ 除法比较）
  example : (4 : ℚ) / 4 = 1 := by decide      -- error: 卡在 `Rat.mul 4 (Rat.inv 4)).num`
  example : barrierQ (1 : ℚ) 3 = 1 := by decide
  -- error: 卡在 `(((1 - 3) ^ 2).mul (4 * 1).inv).num`

结论（已写入 API-NOTES 与 M5b 证据形态）：**含除法的判定一律用 `norm_num`，不用 `decide`**。 -/

/-! ## E3 — `norm_num`：含除法的有理字面量**可以**算（且不是放行假语句） -/

example : zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by norm_num [zoneQ]
example : zoneQ (1 : ℚ) (6 / 8) = Zone.normal := by norm_num [zoneQ]
example : zoneQ ((-1 : ℚ) / 2) (1 : ℚ) = Zone.inverted := by norm_num [zoneQ]
example : zoneQ ((1 : ℚ) / 2) (1 : ℚ) = Zone.inverted := by norm_num [zoneQ]
example : zoneQ ((3 : ℚ) / 2) 2 = Zone.inverted := by norm_num [zoneQ]

-- 负结果·实测：假语句必须证不出，否则说明 `norm_num` 只是放行
--   example : zoneQ (1 : ℚ) (3 / 4) = Zone.inverted := by norm_num [zoneQ]
--   -- error: unsolved goals `⊢ Zone.normal = Zone.inverted`

/-! ## E4 — `barrierQ`（含除法）：同样必须走 `norm_num` -/

example : barrierQ (1 : ℚ) 3 = 1 := by norm_num [barrierQ]
example : barrierQ (1 : ℚ) (1 / 2) = (1 : ℚ) / 16 := by norm_num [barrierQ]

/-! ## E5 — `decide` 可用的 ℚ 目标形态边界（无除法 ⇒ 可算） -/

example : (3 : ℚ) < 5 := by decide
example : (3 : ℚ) ≠ 5 := by decide
example : (1 : ℚ) = 1 := by decide

-- 负结果·实测：十进制字面量本质是有理数除法，不可 `decide`
--   example : (0.75 : ℚ) < 1 := by decide
--   -- error: tactic 'decide' failed … reduction got stuck at `match Rat.blt 0.75 1, true with …`

/-! ## E6 — M5b 证据链形态（用**已交付** RatModel 实测通过）

**关键实测发现（影响 M5b，且 plan §8.2 的示例形态不可编译）**：

1. `rw [← zoneQ_eq_zone] at h`（plan §8.2 写法）**方向相反、必然失败**：
   `← zoneQ_eq_zone` 的改写模式是 `zone ↑?lam ↑?x`，而 `h` 里是 `zoneQ 1 3`，模式对不上。
   实测报错：`tactic 'rewrite' failed, did not find instance of the pattern … zone ↑?lam ↑?x`。
   正确方向是**正向** `rw [zoneQ_eq_zone] at h`（`zoneQ 1 3` → `zone ↑1 ↑3`）。
2. 正向搬过去之后，ℝ 侧参数是 **`Rat.cast` 形态**（`↑(1:ℚ)`），与**数字面量**形态
   （`(1 : ℝ)`，即 `OfNat.ofNat`）在**定义层并不相等**：
   `example : InvertedRegion (1 : ℝ) 3 := (zoneQ_inverted_iff (1 : ℚ) 3).mp (by decide)`
   实测报错 `type mismatch … has type ↑1 < ↑3 : Prop but is expected to have type InvertedRegion 1 3`。
   两条出路（下面 F1/F2 与 F3 各一条）：
   - ℝ 侧参数直接写成 `((· : ℚ) : ℝ)`，与转移引理的结论**逐字对齐**（最省事）；
   - 要真正的 ℝ 数字面量时，用 `show` + `exact_mod_cast` 桥接（F3）。 -/

-- F1：转移引理的直接用法（ℝ 侧参数写成 `((·:ℚ):ℝ)`，与引理结论逐字对齐）
example : InvertedRegion ((1 : ℚ) : ℝ) ((3 : ℚ) : ℝ) :=
  (zoneQ_inverted_iff (1 : ℚ) 3).mp (by decide)

-- F2：分类器等式搬过河（**正向** `rw [zoneQ_eq_zone]`，不是 `←`）
example : zone ((1 : ℚ) : ℝ) ((3 : ℚ) : ℝ) = Zone.inverted := by
  have h : zoneQ (1 : ℚ) 3 = Zone.inverted := by decide
  rwa [zoneQ_eq_zone] at h

-- F3：要 ℝ 数字面量时，用 `show` + `exact_mod_cast` 桥接 cast 与 OfNat
example : InvertedRegion (1 : ℝ) 3 := by
  have h : ((1 : ℚ) : ℝ) < ((3 : ℚ) : ℝ) := (zoneQ_inverted_iff (1 : ℚ) 3).mp (by decide)
  show (1 : ℝ) < 3
  exact_mod_cast h

-- F4：I2 形态 —— 判"**不**在反转区"（含除法的有理参数，走 norm_num）
--
-- **第 3 条实测发现**：`rw [← zoneQ_inverted_iff]` 需要目标里**语法上**出现 `↑?lam < ↑?x`，
-- 而 `rw` 不会展开 `InvertedRegion` 这个 `def`（实测报错：pattern `↑?lam < ↑?x` 找不到，
-- 目标显示为 `¬InvertedRegion ↑1 ↑(3/4)`）。所以先 `show` 出展开形态再 `rw`。
-- （替代写法：`intro hc; exact (by decide : ¬ …) ((zoneQ_inverted_iff _ _).mpr hc ▸ …)`，
--   因为 `exact`/`mpr` 走定义层展开，不受此限制 —— 见 F5 的 `.mp h`。）
example : ¬ InvertedRegion ((1 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) := by
  have h : zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by norm_num [zoneQ]
  show ¬ (((1 : ℚ) : ℝ) < ((3 / 4 : ℚ) : ℝ))
  rw [← zoneQ_inverted_iff, h]
  exact (by decide : ¬ Zone.normal = Zone.inverted)

-- F5：I2 形态 —— 判"正常区"（`NormalRegion`，cast 形态逐字对齐）
example : NormalRegion ((1 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) := by
  have h : zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by norm_num [zoneQ]
  rw [zoneQ_eq_zone] at h
  exact (zone_eq_normal_iff ((1 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ)).mp h

-- F6：I3 形态 —— 无势垒点（`x = lam`，整数参数可 `decide`；同样需要 `show` 展开）
example : ¬ InvertedRegion ((1 : ℚ) : ℝ) ((1 : ℚ) : ℝ) := by
  have h : zoneQ (1 : ℚ) 1 = Zone.barrierless := by decide
  show ¬ (((1 : ℚ) : ℝ) < ((1 : ℚ) : ℝ))
  rw [← zoneQ_inverted_iff, h]
  exact (by decide : ¬ Zone.barrierless = Zone.inverted)

-- F7：三分性由内核直接给出（`Zone` 构造子互异可 `by decide`，M1 交付者已实测）
example : zoneQ (1 : ℚ) 3 ≠ Zone.normal ∧ zoneQ (1 : ℚ) 3 ≠ Zone.barrierless := by
  decide

end PhotoLean.Marcus.ProbeC
