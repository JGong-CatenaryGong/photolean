# theories/StokesShift/RESULTS.md — StokesShift: results and verdicts

> **Status: Phase 1 (statement formalization) of the photophysics batch.** Statements are
> registered in the statement authority `probes/StokesShift-statement-skeleton.lean`; no theorem of
> this theory is proved yet. The bilingual results body is delivered in Phase 3.
> Language policy: this file is the bilingual deliverable (English section followed by its
> Chinese rendering); it is filled at delivery time.

## 1. Status / 现状

**English.** Delivered and verified; the Phase-3 authority revision is recorded in plan §3.1.

**中文。** 已交付并验证；阶段三权威修订记录于 plan §3.1。

## 2. What the theory claims / 理论主张

**English.** the Stokes shift is exactly `2λ`, independent of the 0-0 energy; the emission window (`0 < emEnergy ↔ lam < e00`) IS the Marcus inverted region read at the gap (`emEnergy_pos_iff_inverted`) — the corrected row; the first form's direction error is finalized as the kernel-checked refutation theorem `invertedCorner_firstForm_refuted` (`lam = 1, e00 = 2`).

**中文。**Stokes 位移恰为 `2λ`、与 0-0 能量无关；发射窗（`0 < emEnergy ↔ lam < e00`）正是读在能隙处 的 Marcus 反转区（`emEnergy_pos_iff_inverted`）——修正后的行；初式的方向错误已固化为内核 反例定理 `invertedCorner_firstForm_refuted`（`lam = 1, e00 = 2`）。

## 3. Machine anchors / 机器锚点

**English.** `PhotoLean.StokesShift.stokesShift_eq_two_lam`, `emEnergy_pos_iff_inverted`, `invertedCorner_firstForm_refuted`, `Relations.ss_s0Surface_eq_kernel`; all with `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**中文。** `PhotoLean.StokesShift.stokesShift_eq_two_lam`, `emEnergy_pos_iff_inverted`, `invertedCorner_firstForm_refuted`, `Relations.ss_s0Surface_eq_kernel`；全部 `#print axioms` = `[propext, Classical.choice, Quot.sound]`。
