# theories/EnergyGapLaw/RESULTS.md — EnergyGapLaw: results and verdicts

> **Status: Phase 2 (proof layer) delivered and independently verified PASS (verifier run 2,
> 2026-09-23).** 17/17 authority theorems (26/26 authority declarations) are proved in `PhotoLean/EnergyGapLaw/`; build green, strict scan clean,
> `#print axioms` within the allowed infrastructure, fidelity 0 differences. The bilingual results
> body below is completed at the Phase-3 close-out.## 1. Status / 现状

**English.** Delivered and verified; the Phase-3 authority revision is recorded in plan §3.1.

**中文。** 已交付并验证；阶段三权威修订记录于 plan §3.1。

## 2. What the theory claims / 理论主张

**English.** the Englman–Jortner energy-gap law in the classical two-parabola model: the exact log-rate law is quadratic (`lnRate_eq`, unconditional in `lam` and `kB·T` after the Phase-3 trim — the degenerate inputs totalize consistently), the decrease direction holds exactly in the inverted region and reverses in the normal region, the textbook affine form is the tangent with the exact quadratic defect `−(x−x*)²/(4λk_BT)` and no affine law is exact on any window (`not_affine_on_window`).

**中文。**经典双抛物面模型中的 Englman–Jortner 能隙律：精确对数速率律是二次的（`lnRate_eq`，阶段三修剪后在 `lam` 与 `kB·T` 上无条件——退化输入在全化除法下自洽），下降方向恰在反转区 成立且在正常区反转，教科书仿射形式是带精确二次亏量 `−(x−x*)²/(4λk_BT)` 的切线，且任何 仿射律在任何窗口上都不精确（`not_affine_on_window`）。

## 3. Machine anchors / 机器锚点

**English.** `PhotoLean.EnergyGapLaw.lnRate_eq`, `lnRate_strictAnti_on_inverted`, `eglTangent_overestimates`, `Relations.eg_barrier_eq_kernel`; all with `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**中文。** `PhotoLean.EnergyGapLaw.lnRate_eq`, `lnRate_strictAnti_on_inverted`, `eglTangent_overestimates`, `Relations.eg_barrier_eq_kernel`；全部 `#print axioms` = `[propext, Classical.choice, Quot.sound]`。
