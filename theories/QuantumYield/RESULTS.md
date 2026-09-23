# theories/QuantumYield/RESULTS.md — QuantumYield: results and verdicts

> **Status: Phase 2 (proof layer) delivered and independently verified PASS (verifier run 2,
> 2026-09-23).** 19/19 theorems (29/29 authority declarations) are proved in `PhotoLean/QuantumYield/`; build green, strict scan clean,
> `#print axioms` within the allowed infrastructure, fidelity 0 differences. The bilingual results
> body below is completed at the Phase-3 close-out.## 1. Status / 现状

**English.** Delivered and verified; the Phase-3 authority revision is recorded in plan §3.1.

**中文。** 已交付并验证；阶段三权威修订记录于 plan §3.1。

## 2. What the theory claims / 理论主张

**English.** the parallel-channel calculus: yields `kᵢ/Σk` sum to one, share one lifetime `τ = 1/Σk`, and adding a channel rescales every live yield by the same factor `Σk/(Σk+c)` — the dilution law that the Stern–Volmer, FluorPhos, Forster and Einstein edges of `Relations.lean` §15 all reduce to. The load-bearing premise `0 < totalRate` is witnessed by the counterexample row `totalRate_zero_counterexample` (at `k ≡ 0` the conservation fails).

**中文。**并行通道演算：产额 `kᵢ/Σk` 归一、共享同一寿命 `τ = 1/Σk`、加通道以同一因子 `Σk/(Σk+c)` 稀释每个活通道——`Relations.lean` §15 的 Stern–Volmer、FluorPhos、Forster、Einstein 四条边 全部归约到它。承载前提 `0 < totalRate` 由反例行 `totalRate_zero_counterexample` 见证 （`k ≡ 0` 时守恒失效）。

## 3. Machine anchors / 机器锚点

**English.** `PhotoLean.QuantumYield.sum_yieldOf_eq_one`, `yieldOf_cons_succ_factor`, `Relations.kasha_radBranch_eq_yieldOf`; all with `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**中文。** `PhotoLean.QuantumYield.sum_yieldOf_eq_one`, `yieldOf_cons_succ_factor`, `Relations.kasha_radBranch_eq_yieldOf`；全部 `#print axioms` = `[propext, Classical.choice, Quot.sound]`。
