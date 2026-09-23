import Mathlib
import PhotoLean.RACI.TwoState

namespace PhotoLean


/-!
# RACI M2 — Accessibility：可容许路径与能量阻断

来源：plan.md §2.3、§5.1。
状态：**SKELETON** —— 语句从 plan.md 转写；与草稿的差异：
plan §5.6 允许 M2 第一版去掉能量字段；骨架保留 `below_energy`（§2.3 原样），
BlockedBelow 对所有 ε 成立与否由 prover_m2 按 plan §5.3 注处理。
属主：prover_m2（独占文件）。
-/

open TwoState

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace RACI

/-- 从 Franck-Condon 区域（fc）到 CI 的可容许连续路径（plan §2.3） -/
structure AdmissiblePath (M : TwoState X) (allowed : Set X) (fc : Set X) (ε : ℝ) where
  path : ℝ → X
  cont : Continuous path
  starts_fc : path 0 ∈ fc
  ends_ci : path 1 ∈ TwoState.conicalSet M
  stays_allowed : ∀ t, path t ∈ allowed
  below_energy : ∀ t, M.H (path t) 0 0 ≤ ε

/-- 在能量 ε 以下不存在可容许 CI 通道（plan §2.3；`∃ A, True` 写作 `Nonempty` 消除 linter 警告） -/
def BlockedBelow (M : TwoState X) (allowed : Set X) (fc : Set X) (ε : ℝ) : Prop :=
  ¬ Nonempty (AdmissiblePath M allowed fc ε)

end RACI


end PhotoLean