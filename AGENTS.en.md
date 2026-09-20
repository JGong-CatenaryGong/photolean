# AGENTS.md — PhotoLean Workspace Rules

> *English translation of `AGENTS.md`. The Chinese original at `AGENTS.md` is authoritative — the formalization engine's contract (`proofs/ENGINE.yml`) reads the Chinese paths.*

This repository is a **Lean 4 formalization project for a phenomenological theory of photochemistry/photophysics**,
driven by the "project-agnostic formalization engine" (a DSH Agent preset). **Read `proofs/ENGINE.md` first** — it defines the contract, the roles, and the acceptance gate.

## Iron Rules (Non-Negotiable)

1. **No placeholder proofs, no custom `axiom` declarations** in delivered theorems. Judgement is by script, not by self-report:
   ```bash
   proofs/scripts/check.sh --strict <Module>
   proofs/scripts/axioms.sh <Module> <theorem>
   ```
2. **statement-first**: a statement must compile in Lean before proof work is allowed to begin.
   Statement changes are only permitted because of API drift, and must be recorded in `proofs/API-NOTES.md`.
3. **Physical approximations made explicit**: positivity, continuity, differentiability, and parameter inequalities are always written as theorem premises;
   hiding them inside definitions is forbidden.
4. **Never guess API names**: when unsure, consult `proofs/API-NOTES.md`; if it isn't there, hand it to `api_researcher`
   to confirm with a `#check` probe.
5. **Exclusive file ownership**: at any one time a file has exactly one owner (see `proofs/TASKS.md`).
6. **Independent acceptance**: the person who writes a proof cannot judge it PASS themselves. The verifier is read-only, runs the gate independently, and returns evidence.
7. **Ticking the box happens only after the verifier passes**, and is performed by the lead.

## Toolchain (easy to trip over — always observe)

```bash
proofs/scripts/lake build                     # use this one, do not call lake directly (not on PATH)
proofs/scripts/lake build PhotoLean.Smoke     # single module
```

- `.toolchain/` and `.lake/packages/` are **symlinks** pointing at an already-built mathlib cache.
- **`lake update` is forbidden** — it rewrites the manifest and triggers a multi-hour full rebuild.
- A cold-start `lake build` taking about 10 seconds is normal (the mathlib oleans are already cached).

## Iteration and Memory

- A batch of independent lemmas → `workflow` fan-out; a single stuck one → `ralph`; a long milestone → the goal tools.
- **Every round must write back to `proofs/EXPERIENCE.md`**, including a "tried and failed" section.
  An entry that records only successes counts as invalid.
- Literature-survey results go into `proofs/LITERATURE.md`, and must include the "formalizable implication".

## Current Status

The theoretical direction is settled: the **Marcus inverted region** (classical Marcus model, `plan.md` M1–M5, confirmed by a human on 2026-09-20).
Deliverables: `PhotoLean/Marcus/{Basic,Barrier,Rate,Sharp,Reorg,Compose,RatModel,Instances}.lean`;
answers to questions asked by humans: `proofs/RESULTS.md`; single source of truth for progress: `proofs/TASKS.md`.

**Before starting work you must read the owner column and the "Acceptance Record" table in `proofs/TASKS.md`** — that table records the
verifier verdict for each milestone, the defects already closed, and several **pits that have actually been hit in practice** (gate decisions inside a
concurrency window, the `git add -A` concurrency incident, "unused" ≠ "derivable", etc.). Do not invent milestones on your own, and do not change statements that have already been accepted.
