# theories/Einstein/RESULTS.md — Einstein: results and verdicts

> **Status: Phase 1 (statement formalization) of the photophysics batch.** Statements are
> registered in the statement authority `probes/Einstein-statement-skeleton.lean`; no theorem of
> this theory is proved yet. The bilingual results body is delivered in Phase 3.
> Language policy: this file is the bilingual deliverable (English section followed by its
> Chinese rendering); it is filled at delivery time.

## 1. Status / 现状

**English.** Delivered and verified; the Phase-3 authority revision is recorded in plan §3.1.

**中文。** 已交付并验证；阶段三权威修订记录于 plan §3.1。

## 2. What the theory claims / 理论主张

**English.** the A/B/oscillator-strength equivalence chain: every conversion leg (`A = K·B₂₁`, `B₁₂ = (g₂/g₁)·B₂₁`, `f = Cf·(g₂/g₁)·A`, the Strickler–Berg leg) is invertible and every round trip is the identity — knowing any one quantity determines all others; the radiative channel's yield is the QuantumYield of the pair (the §15 anchor), and the physical radiation factor `8πhν³/c³` at unit parameters is irrational (`radFactor_not_rational`, re-frozen to name what it proves).

**中文。**A/B/振子强度等价链：每条转换腿（`A = K·B₂₁`、`B₁₂ = (g₂/g₁)·B₂₁`、`f = Cf·(g₂/g₁)·A`、Strickler–Berg 腿）都可逆且每个往返都是恒等——知道任一量即可决定其余；辐射通道的产额是 该对的 QuantumYield（§15 锚点），而物理辐射因子 `8πhν³/c³` 在单位参数下无理 （`radFactor_not_rational`，重冻结为名副其实）。

## 3. Machine anchors / 机器锚点

**English.** `PhotoLean.Einstein.full_chain_roundtrip`, `detailed_balance`, `radFactor_not_rational`, `Relations.einstein_yield_via_qy`; all with `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**中文。** `PhotoLean.Einstein.full_chain_roundtrip`, `detailed_balance`, `radFactor_not_rational`, `Relations.einstein_yield_via_qy`；全部 `#print axioms` = `[propext, Classical.choice, Quot.sound]`。
