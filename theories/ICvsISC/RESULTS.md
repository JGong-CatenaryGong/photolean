# theories/ICvsISC/RESULTS.md — ICvsISC: results and verdicts

> **Status: Phase 2 (proof layer) delivered and independently verified PASS (verifier run 4,
> 2026-09-23).** All 14 theorems (20/20 authority declarations) are proved in `PhotoLean/ICvsISC/`;
> build green, strict scan clean, `#print axioms` within the allowed infrastructure, fidelity 0
> differences. The bilingual results body is completed at the Phase-3 close-out.

## 1. Status / 现状

**English.** Delivered and verified; the Phase-3 authority revision is recorded in plan §3.1.

**中文。** 已交付并验证；阶段三权威修订记录于 plan §3.1。

## 2. What the theory claims / 理论主张

**English.** the Franck–Condon competition: `log(k_ISC/k_IC) = 2·log H_SO + log(A_S/A_I) + (b_IC − b_ISC)/(k_BT)`; with equal prefactors and unit coupling the race IS the barrier ordering (`equal_prefactors_decision`, kernel-decided at ℚ); the spin discount (`HSO < 1` forces a strictly lower ISC barrier to win) and the El-Sayed boundary (`HSO = 0` ⇒ no ISC, whatever the barriers — witnessed even where the pure barrier race is won).

**中文。**Franck–Condon 竞争：`log(k_ISC/k_IC) = 2·log H_SO + log(A_S/A_I) + (b_IC − b_ISC)/(k_BT)`；等前置因子与单位耦合下竞争就是势垒序（`equal_prefactors_decision`，ℚ 层内核判定）；自旋折扣（`HSO < 1` 迫使 ISC 势垒严格更低才能赢）与 El-Sayed 边界（`HSO = 0` ⇒ 无论势垒如何 ISC 为零——即使在纯势垒赛跑被赢得之处也有见证）。

## 3. Machine anchors / 机器锚点

**English.** `PhotoLean.ICvsISC.log_rate_ratio`, `spin_discount`, `hso_zero_isc_absent`, `Relations.icvscic_icRate_eq_eg_nrRate`; all with `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**中文。** `PhotoLean.ICvsISC.log_rate_ratio`, `spin_discount`, `hso_zero_isc_absent`, `Relations.icvscic_icRate_eq_eg_nrRate`；全部 `#print axioms` = `[propext, Classical.choice, Quot.sound]`。
