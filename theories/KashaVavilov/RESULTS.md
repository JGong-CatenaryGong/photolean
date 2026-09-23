# theories/KashaVavilov/RESULTS.md — KashaVavilov: results and verdicts

> **Status: Phase 1 (statement formalization) of the photophysics batch.** Statements are
> registered in the statement authority `probes/KashaVavilov-statement-skeleton.lean`; no theorem of
> this theory is proved yet. The bilingual results body is delivered in Phase 3.
> Language policy: this file is the bilingual deliverable (English section followed by its
> Chinese rendering); it is filled at delivery time.

## 1. Status / 现状

**English.** Delivered and verified: three modules, 20/20 authority theorems proved (29/29
declarations word-for-word), verifier run 1 PASS; the Phase-3 authority revision (plan §3.1
entry 2) dropped the two unconsumed premises.

**中文。** 已交付并验证：三个模块、20/20 权威定理（29/29 声明逐字一致）、verifier run 1
PASS；阶段三权威修订（plan §3.1 条目 2）弃置了两条未被消费的前提。

## 2. The D2 adjudication — Kasha vs Kasha–Vavilov / D2 裁定——Kasha 对 Kasha–Vavilov

**English.** The two rules are run together in the textbooks; the kernel decides their relation
in three parts (`Relations.lean` §13, class A2 — adjudicated independence):

1. **Pointwise independence, both directions.** There are admissible ladders satisfying Kasha's
   rule at level `N` while violating Vavilov's step at `N` (`kashaRule_not_implies_vavilovAt`:
   `rad = 1, 0, 1, …` — the newly excited level is radiative, `fluoYield 1 = 1/2 ≠ 3/4 =
   fluoYield 2`), and admissible ladders doing the converse (`vavilovAt_not_implies_kashaRule`:
   `rad = 1, 1, 0, …` — `fluoYield 1 = fluoYield 2 = 3/4` while level `1` emits). Both witnesses
   sit at the positive excitation level `N = 1` **inside the lossy regime** (`ic 0 = 1 > 0`): the
   independence is not a degenerate-corner artefact.
2. **The exact boundary.** Under the closed quantification the two rules coincide exactly when
   the lowest level has a loss channel: `KashaRule N ↔ VavilovUpTo N` under `RateData` and
   `0 < ic 0` (the delivered `Kasha.kashaRule_iff_vavilovUpTo`, re-stated in `d2_verdict`'s
   third conjunct); at `ic 0 = 0` the lossless corner separates them (`lossless_separates`:
   the yield is identically `1`, Vavilov holds vacuously, Kasha fails) — the loss premise is
   load-bearing. Additionally, an anti-Kasha violation is always *observable* under `RateData`
   (`antiKasha_observable_iff`: the maximal emitter has a clear cascade above it).
3. **Persistence.** Why the identification survives: every ordinary lossy fluorophore sits in the
   regime where the closed forms coincide, so spectroscopists never see the two rules differ —
   they differ only in the degenerate lossless model and in single-step readings, neither of
   which routine spectra resolve.

**中文。** 两条规则在教科书中被并提；内核以三部分裁定其关系（`Relations.lean` §13，A2
类——已裁决独立性）：

1. **逐点独立，双向。** 存在满足 `N` 级 Kasha 规则而违反 `N` 步 Vavilov 规则的容许阶梯
   （`kashaRule_not_implies_vavilovAt`：`rad = 1, 0, 1, …`——新激发能级有辐射性，
   `fluoYield 1 = 1/2 ≠ 3/4 = fluoYield 2`），也存在反向的容许阶梯
   （`vavilovAt_not_implies_kashaRule`：`rad = 1, 1, 0, …`——`fluoYield 1 = fluoYield 2 = 3/4`
   而能级 `1` 发射）。两个见证都处在正激发级 `N = 1` 且**在有损区内**（`ic 0 = 1 > 0`）：
   独立性不是退化角的人为产物。
2. **精确边界。** 闭合量化下两规则恰在最低能级有损失通道时重合：`RateData` 与 `0 < ic 0`
   之下 `KashaRule N ↔ VavilovUpTo N`（已交付的 `Kasha.kashaRule_iff_vavilovUpTo`，
   于 `d2_verdict` 第三合取中重述）；在 `ic 0 = 0` 的无损角二者分离（`lossless_separates`：
   产额恒为 `1`，Vavilov 空洞成立，Kasha 失败）——损失前提是承载的。此外，在 `RateData`
   下 anti-Kasha 违反总是*可观测的*（`antiKasha_observable_iff`：最大发射体上方的级联无阻）。
3. **存续解释。** 同一化为何存活：每个通常的有损荧光体都处在闭合形式重合的机制区，
   光谱学工作者从未见过两条规则相异——它们只在退化无损模型与单步读数中相异，
   而这两者都不是常规光谱所能分辨的。

## 3. Machine anchors / 机器锚点

**English.** `PhotoLean.KashaVavilov.d2_verdict` (four conjuncts),
`PhotoLean.KashaVavilov.antiKasha_observable_iff`,
`PhotoLean.Relations.kv_d2_verdict`, `PhotoLean.Relations.kv_antiKasha_boundary`; all with
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**中文。** `PhotoLean.KashaVavilov.d2_verdict`（四合取）、
`PhotoLean.KashaVavilov.antiKasha_observable_iff`、
`PhotoLean.Relations.kv_d2_verdict`、`PhotoLean.Relations.kv_antiKasha_boundary`；全部
`#print axioms` = `[propext, Classical.choice, Quot.sound]`。
