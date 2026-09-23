# theories/FluorPhos/RESULTS.md — FluorPhos: results and verdicts

> **Status: Phase 2 (proof layer) delivered and independently verified PASS (verifier run 5,
> 2026-09-23).** All 16 theorems (29/29 authority declarations) are proved in `PhotoLean/FluorPhos/`;
> build green, strict scan clean, `#print axioms` within the allowed infrastructure, fidelity 0
> differences. One authority row was re-frozen during the batch (`phiP_strictMono_isc` gained the
> load-bearing premise `0 < kF + kIC`; plan §3.1 entry 2). The bilingual results body is completed at
> the Phase-3 close-out.

## 1. Status / 现状

**English.** Delivered and verified; the Phase-3 authority revision is recorded in plan §3.1.

**中文。** 已交付并验证；阶段三权威修订记录于 plan §3.1。

## 2. What the theory claims / 理论主张

**English.** the fluorescence/phosphorescence competition: the balance `φP/φF = (kISC/kF)·(kP/(kP+kNR))`, the crossover `kF·(kP+kNR) < kISC·kP`, the losslessness boundary `φF + φP = 1 ↔ kIC = 0 ∧ (kISC = 0 ∨ kNR = 0)` (design-time corrected: the naive form is too strong), and the heavy-atom monotonicity with its exactly load-bearing premise `0 < kF + kIC` — whose absence in the first frozen form is now a kernel-checked refutation theorem (`fpC5_firstForm_refuted`).

**中文。**荧光/磷光竞争：平衡 `φP/φF = (kISC/kF)·(kP/(kP+kNR))`、交叉点 `kF·(kP+kNR) < kISC·kP`、无损边界 `φF + φP = 1 ↔ kIC = 0 ∧ (kISC = 0 ∨ kNR = 0)`（设计期修正：朴素形式过强）、以及带恰好承载前提 `0 < kF + kIC` 的重原子单调性——其初式的缺失已成为内核反例定理 （`fpC5_firstForm_refuted`）。

## 3. Machine anchors / 机器锚点

**English.** `PhotoLean.FluorPhos.phiP_div_phiF`, `crossover_isc`, `phiF_add_phiP_eq_one_iff`, `Relations.phiP_eq_yieldOf_cascade`; all with `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**中文。** `PhotoLean.FluorPhos.phiP_div_phiF`, `crossover_isc`, `phiF_add_phiP_eq_one_iff`, `Relations.phiP_eq_yieldOf_cascade`；全部 `#print axioms` = `[propext, Classical.choice, Quot.sound]`。
