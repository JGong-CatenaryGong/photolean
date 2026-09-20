# theories/hammond/RESULTS.md — Hammond postulate formalization: results

> **Status: IN PROGRESS (Sprint 0).** This is the single bilingual deliverable of the Hammond
> theory (English original + Chinese rendering per section, per the contract's language policy).
> It will be rewritten with the final results, evidence tables and honest-boundary sections
> after the verifier passes. Nothing here is a claim yet.
>
> **状态：进行中（Sprint 0）。** 本文件是 Hammond 理论的唯一双语交付物（契约语言政策规定：
> 每节英文原文后紧跟中文对照）。verifier 通过后将以最终结果、证据表与诚实边界重写。
> 当前内容不是任何结论。

## 0. What is being formalized

Hammond's postulate is being formalized inside the two-parabola (Marcus-type) model of an
elementary reaction step: the transition-state coordinate, the barrier, the Leffler/Brønsted
coefficient measured from barrier data, and the exact statement "the transition state resembles
the species to which it is closest in energy", together with a sharp characterization of when
that description holds and kernel-checked verdicts for literature instances.

## 0. 正在形式化的内容

Hammond 假说在基元反应步的**双抛物面（Marcus 型）模型**中被形式化：过渡态坐标、势垒、由
势垒数据测得的 Leffler/Brønsted 系数，以及"过渡态与能量上最接近的物种在结构上相似"的精确
陈述；并给出该描述成立条件的锐利刻画与文献实例的内核可检验判定。

## 1. Plan and statement authority

- Plan (milestones H1–H5, statements, sprint order, modeling-assumption table):
  `theories/hammond/plan.md`.
- Statement authority (compiled skeleton, 0 error):
  `theories/hammond/probes/hammond-statement-skeleton.lean`.
- Risk probe with complete proofs of the core statement forms:
  `theories/hammond/probes/hammond-risk-probe.lean`.

## 1. 规划与语句权威

- 规划（里程碑 H1–H5、语句、sprint 顺序、建模假设表）：`theories/hammond/plan.md`。
- 语句权威（已编译骨架，0 error）：`theories/hammond/probes/hammond-statement-skeleton.lean`。
- 核心语句形态的完整证明探针：`theories/hammond/probes/hammond-risk-probe.lean`。
