/-
PhotoLean — 工具链与 mathlib 联通性冒烟测试（Scaffold smoke test）。

作用：证明 `lake build` 能解析 mathlib、olean 缓存可用、`#print axioms`
输出干净。它不承载任何物理内容，是 Sprint 0 的环境门。

维护约定：本模块只允许保留**已完整证明**的定理。一旦出现未完成证明，
说明环境或工具链被破坏，优先修复而不是绕过 —— 不要在源码注释里写出那个
关键字（行内 `--` 注释除外，扫描器会跳过行内注释）。
-/

import Mathlib

namespace PhotoLean

/-- mathlib 可解析、`ring` 可用。--/
theorem smoke_ring (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

/-- 实分析层可解析、`positivity` 可用（形式化速率常数正性时最常用的一类目标）。--/
theorem smoke_pos {x : ℝ} (hx : 0 < x) : 0 < x ^ 2 + 1 := by
  positivity

end PhotoLean
