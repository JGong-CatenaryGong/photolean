# theories/Sabatier/plan.md — PhotoLean formalization plan: the Sabatier principle and the volcano plot (S1–S5)

> Status: **Sprint 0 in flight** (2026-09-21). This file carries the full record of milestones,
> statements, proof sketches, sprint order and the honesty table; it is written by the lead in the
> same sprint as the statement authority and the risk probe. Statement authority (target):
> `theories/Sabatier/probes/sabatier-statement-skeleton.lean`.
> Contract: `proofs/ENGINE.yml`; board: `theories/Sabatier/TASKS.md`; literature:
> `theories/Sabatier/LITERATURE.md`; experience bank: `proofs/EXPERIENCE.md`.
> Theory direction: the human request of 2026-09-21 (three parts: formal description / proof and
> exact conditions / instance verdicts), carried out under `theories/Sabatier/` with the Lean
> sources under `PhotoLean/Sabatier/` (the contract's `SOURCE_DIRS` is global — see plan §3).

## 1. Overall goal (complete version below, written in Sprint 0)

Turn the **Sabatier principle** ("the optimal catalyst binds the key intermediate neither too
strongly nor too weakly"), in its quantitative form the **volcano plot**, into a machine-checked
theory: a description layer, the exact conditions under which the volcano shape holds, and
kernel-checked instance verdicts.

## 2. Milestones (target)

| Human request | Milestone | Deliverable |
|---|---|---|
| ① formal description | **S1** | `PhotoLean/Sabatier/Basic.lean` |
| ②a prove it | **S2** | `PhotoLean/Sabatier/Criterion.lean` |
| ②b exact conditions | **S3** | `PhotoLean/Sabatier/Sharp.lean` |
| ②c microscopic / cross-theory form | **S4** | `PhotoLean/Sabatier/Compose.lean` |
| ③ instances and verdicts | **S5** | `PhotoLean/Sabatier/RatModel.lean`, `PhotoLean/Sabatier/Instances.lean` |
