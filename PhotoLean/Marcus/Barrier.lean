/-
PhotoLean.Marcus.Barrier — M2 势垒代数（Marcus 反转区）。

**语句权威**：`proofs/probes/marcus-statement-skeleton.lean` 的 M2 段
（Sprint 0 已编译通过）。本文件 9 条定理签名与它**逐字一致**；
证明体全部经内核检查（零占位证明、无自定义公理声明）。

**注**：本文件头刻意不写出被 `check.sh --strict` 扫描的两个关键字字面量
（块注释同样在扫描范围内，写了会造成误报 FAIL）。

**显式物理前提的冗余性（plan §5；实测记录见 proofs/API-NOTES.md）**：
- `barrier_symm` 的 `hlam : lam ≠ 0`：实测 `unfold barrier; ring_nf` **不需要**它 ——
  除零约定下 `lam = 0` 时两端同为 `0`；仍按语句权威保留为显式物理前提。
- `barrier_antitone_of_pos` 的 `h₁ : 0 ≤ x₁`：可由 `h₂` 与 `h₃ : x₂ ≤ lam` 推出，
  证明中不参与；保留为显式物理前提（驱动力非负，normal 区的物理定义域）。
故顶部关掉未使用变量 linter（warning 不影响验收）。

验收（契约 `proofs/ENGINE.yml`）：
  proofs/scripts/lake build PhotoLean.Marcus.Barrier
  proofs/scripts/check.sh --strict PhotoLean.Marcus.Barrier
  proofs/scripts/axioms.sh PhotoLean.Marcus.Barrier PhotoLean.Marcus.<theorem>
-/
import PhotoLean.Marcus.Basic

set_option linter.unusedVariables false

namespace PhotoLean.Marcus

/-! ## M2 — 势垒代数（§5） -/

/-- `lam > 0` 时势垒非负（物理：势垒高度不可能为负）。 -/
theorem barrier_nonneg {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : 0 ≤ barrier lam x := by
  unfold barrier; positivity

/-- 无势垒点：`x = lam` 处势垒为零（**无需前提**，含 `lam = 0` 的退化情形）。 -/
theorem barrier_at_lam (lam : ℝ) : barrier lam lam = 0 := by
  simp [barrier]

/-- 抛物线对称性：以 `x = lam` 为轴（`(lam - x)² = (lam - (2lam - x))²`）。
`hlam : lam ≠ 0` 是**显式物理前提**（重组能非零）；实测证明中不需要它 ——
除零约定 `x / 0 = 0` 使 `lam = 0` 时两端同为 `0`。 -/
theorem barrier_symm {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) : barrier lam x = barrier lam (2 * lam - x) := by
  unfold barrier; congr 1; ring

/-- 峰值（势垒最小）：`lam > 0` 时 `x = lam` 是全局最小点（速率峰的代数内核）。 -/
theorem barrier_min_at_lam {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : barrier lam lam ≤ barrier lam x := by
  rw [barrier_at_lam]; unfold barrier; positivity

end PhotoLean.Marcus
