# theories/Forster/RESULTS.md — Forster: results and verdicts

> **Status: Phase 2 (proof layer) delivered and independently verified PASS (verifier run 3,
> 2026-09-23).** All 22 theorems (32/32 authority declarations) are proved in `PhotoLean/Forster/`;
> build green, strict scan clean, `#print axioms` within the allowed infrastructure, fidelity 0
> differences; `kappaSq_le_four` independently confirmed sharp (bound 4 attained; no smaller uniform
> bound). The bilingual results body is completed at the Phase-3 close-out.

## 1. Status / 现状

**English.** Delivered and verified; the Phase-3 authority revision is recorded in plan §3.1.

**中文。** 已交付并验证；阶段三权威修订记录于 plan §3.1。

## 2. What the theory claims / 理论主张

**English.** the FRET rate/efficiency laws in `R⁶`-space; the orientation factor `κ² = (sinθ_D·sinθ_A·cosφ − 2cosθ_D·cosθ_A)²` is bounded `0 ≤ κ² ≤ 4` — a SHARP bound (both endpoints attained, no smaller uniform bound exists; verified by grid/random/exact search and a kernel certificate); the `2/3` convention is exactly the orthonormal-frame average; the convention-bias analysis: the tabulated-`R₀⁶` misestimate factor lies in `[0, 6]`, with the blind spot `κ² = 0` (no transfer at any distance while the convention predicts transfer) as the silent failure.

**中文。**`R⁶`-空间中的 FRET 速率/效率律；取向因子 `κ² = (sinθ_D·sinθ_A·cosφ − 2cosθ_D·cosθ_A)²` 满足 `0 ≤ κ² ≤ 4`——紧界（两端点皆可达、不存在更小的统一界；经网格/随机/精确搜索与内核 证书验证）；`2/3` 约定恰为正交标架平均；约定偏差分析：制表 `R₀⁶` 的错估因子落在 `[0, 6]`，盲点 `κ² = 0`（任何距离都不转移而约定预测转移）是静默失效。

## 3. Machine anchors / 机器锚点

**English.** `PhotoLean.Forster.kappaSq_le_four`, `Rat.iso_frame_avg`, `fret_blind_spot`, `r0six_ratio_mem`, `Relations.fretEff6_eq_one_sub_yieldOf`; all with `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**中文。** `PhotoLean.Forster.kappaSq_le_four`, `Rat.iso_frame_avg`, `fret_blind_spot`, `r0six_ratio_mem`, `Relations.fretEff6_eq_one_sub_yieldOf`；全部 `#print axioms` = `[propext, Classical.choice, Quot.sound]`。
