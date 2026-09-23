# theories/SternVolmer/RESULTS.md — SternVolmer: results and verdicts

> **Status: Phase 1 (statement formalization) of the photophysics batch.** Statements are
> registered in the statement authority `probes/SternVolmer-statement-skeleton.lean`; no theorem of
> this theory is proved yet. The bilingual results body is delivered in Phase 3.
> Language policy: this file is the bilingual deliverable (English section followed by its
> Chinese rendering); it is filled at delivery time.

## 1. Status / 现状

**English.** Delivered and verified: four modules, 27/27 authority theorems proved (46/46
declarations word-for-word), verifier run 1 PASS; the Phase-3 authority revision (plan §3.1
entries 2–4) trimmed the weakest premises and re-froze the mixed witness.

**中文。** 已交付并验证：四个模块、27/27 权威定理（46/46 声明逐字一致）、verifier run 1
PASS；阶段三权威修订（plan §3.1 条目 2–4）完成了最弱前提修剪与混合见证的重冻结。

## 2. The D1 adjudication — static vs dynamic quenching / D1 裁定——静态 vs 动态猝灭

**English.** The question the literature conflates: a *linear* Stern–Volmer plot
(`I₀/I = 1 + K·[Q]`) is routinely read as *dynamic* (collisional) quenching. The kernel decides
the identification in three parts (`Relations.lean` §14, class A3 — identifiability):

1. **Non-injectivity of the intensity-only observation.** Both mechanisms give exactly linear
   intensity plots (`svRatioDyn_linear`, `svRatioStat_linear`), and at matched parameters
   (`Ka = KSV = kq/k0`) the two curves coincide *pointwise at every concentration*
   (`intensity_curve_coincidence`): the intensity-only observation map is not injective on the
   two-mechanism model space — no intensity data can separate them.
2. **The exact boundary.** The lifetime channel separates them: within the model space,
   `LifetimeTracks m k0 kq Ka ↔ m = Mech.dyn` (`sv_identifiability_boundary`; weakest premises
   `0 < Ka` only — the dynamic side tracks definitionally, the static side fails at any positive
   concentration). Upward curvature is the positive witness of *coexistence*: the combined
   mechanism's second difference is the constant `2·KSV·Ka·h² > 0` while each single mechanism's
   vanishes (`svRatioBoth_secondDifference`, `curvature_witnesses_coexistence`), instantiated by
   `mixed_witness` at the model object itself.
3. **Persistence.** Why the conflation survives in practice: routine Stern–Volmer analysis
   measures intensity only; lifetime resolution (the discriminating channel) is a separate
   experiment. In the regime where only intensity is recorded, the two mechanisms are
   observationally identical — the conflation is not an error of reasoning but a property of the
   reduced observation.

**中文。** 文献混同的问题是：*线性* Stern–Volmer 图（`I₀/I = 1 + K·[Q]`）被惯例读作*动态*（碰撞）猝灭。内核以三部分裁定（`Relations.lean` §14，A3 类——可辨识性）：

1. **仅强度观测的非单射性。** 两种机制都给出严格线性的强度图（`svRatioDyn_linear`、
   `svRatioStat_linear`），且在匹配参数（`Ka = KSV = kq/k0`）下两条曲线*在每个浓度处逐点相同*
   （`intensity_curve_coincidence`）：仅强度的观测映射在两机制模型空间上非单射——强度数据无法区分二者。
2. **精确边界。** 寿命通道可以区分：在模型空间内
   `LifetimeTracks m k0 kq Ka ↔ m = Mech.dyn`（`sv_identifiability_boundary`；最弱前提仅
   `0 < Ka`——动态侧按定义跟踪，静态侧在任何正浓度处失败）。向上弯曲是*共存*的正见证：
   组合机制的二阶差分是常数 `2·KSV·Ka·h² > 0` 而每个单机制的二阶差分为零
   （`svRatioBoth_secondDifference`、`curvature_witnesses_coexistence`），由 `mixed_witness`
   在模型对象本身上实例化。
3. **存续解释。** 混同为何在实践中存活：常规 Stern–Volmer 分析只测强度；寿命分辨（区分通道）
   是另一个实验。在只记录强度的机制下，两种机制在观测上同一——混同不是推理错误，而是约化观测的性质。

## 3. Machine anchors / 机器锚点

**English.** `PhotoLean.SternVolmer.d1_verdict` (weakest premises `k0 ≠ 0`, `0 < Ka`),
`PhotoLean.SternVolmer.lifetimeTracks_iff_dyn`, `PhotoLean.SternVolmer.intensity_curve_coincidence`,
`PhotoLean.Relations.sv_d1_verdict`, `PhotoLean.Relations.sv_identifiability_boundary`; all with
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**中文。** `PhotoLean.SternVolmer.d1_verdict`（最弱前提 `k0 ≠ 0`、`0 < Ka`）、
`PhotoLean.SternVolmer.lifetimeTracks_iff_dyn`、`PhotoLean.SternVolmer.intensity_curve_coincidence`、
`PhotoLean.Relations.sv_d1_verdict`、`PhotoLean.Relations.sv_identifiability_boundary`；全部
`#print axioms` = `[propext, Classical.choice, Quot.sound]`。
