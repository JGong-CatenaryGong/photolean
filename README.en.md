# PhotoLean

> *English translation of `README.md`. The Chinese original at `README.md` is authoritative — the formalization engine's contract (`proofs/ENGINE.yml`) reads the Chinese paths.*

A Lean 4 formalization of a **phenomenological theory in photochemistry / photophysics**, driven by DSH's "project-agnostic
formalization engine" Agent preset.

This repository is also the **reference instance** of that engine: it reads only the leaf data plane declared in
`proofs/ENGINE.yml`, so switching theories costs nothing more than a different repository and a rewrite of those few data
files — never a change to the engine.

## Current status

- Lean 4.17.0 + mathlib; toolchain and caches are wired up (`lake build` cold start ~10s)
- Acceptance-gate scripts are usable: `proofs/scripts/check.sh --strict`, `proofs/scripts/axioms.sh`
- The theory direction is settled: the **Marcus inverted region** (classical Marcus model). The plan is in `plan.md` (M1–M5),
  the deliverables are in `PhotoLean/Marcus/` (descriptor layer / barrier algebra / rate layer / sharp validity conditions /
  microscopic reorganization energy / instance decisions), **answers to human questions are in `proofs/RESULTS.md`**
- `PhotoLean/Smoke.lean` is the environment smoke test

### How to re-check

```bash
proofs/scripts/check.sh --strict                                   # whole-tree scan + build (verdict: PASS expected)
proofs/scripts/axioms.sh PhotoLean.Marcus.Sharp PhotoLean.Marcus.descriptor_sharp   # axiom check of the main theorem
proofs/scripts/lake env lean proofs/probes/marcus-statement-skeleton.lean           # authoritative statements (contains an unfinished-proof placeholder; compile only)
```
**`lake build` returning 0 is not acceptance**: placeholder-only proofs and custom axioms both return 0, so all three layers
are required (build + scan + `#print axioms`), executed independently by a role that writes no proofs.

## Quick start

```bash
proofs/scripts/lake build                     # everything (first run ~10s, mathlib is cached)
proofs/scripts/lake build PhotoLean.Smoke     # a single module
proofs/scripts/check.sh --strict              # build + scan for unfinished proofs / custom axioms (mandatory before delivery)
proofs/scripts/axioms.sh PhotoLean.Smoke smoke_ring   # print the axioms a theorem actually depends on
```

> `lake` is not on the PATH — always invoke it through `proofs/scripts/lake`.
> **`lake update` is forbidden** (it rewrites the manifest and triggers a multi-hour full rebuild).

## Discipline

A delivered theorem must not contain an unfinished proof or a custom axiom; `#print axioms` allows only `propext` /
`Classical.choice` / `Quot.sound`. Every physical approximation must be made explicit as a theorem hypothesis. The verdict is
executed by scripts, not left to the model's self-restraint.

## Documentation

| File | Purpose |
|---|---|
| `proofs/ENGINE.md` | **Engine contract**: leaf data plane, roles, acceptance gate, iteration loop |
| `AGENTS.md` | Workspace invariants and toolchain pitfalls |
| `plan.md` | Theory plan (statements, proof sketches, milestones, acceptance criteria) — **to be filled in** |
| `proofs/TASKS.md` | Task board (single source of truth for status) |
| `proofs/EXPERIENCE.md` | Experience bank: success and failure patterns, reused across rounds |
| `proofs/API-NOTES.md` | mathlib API calibration log |
| `proofs/LITERATURE.md` | Literature survey records |

A comparable finished instance (a style template): `[local path removed]` (RACI/AIE, all of M1–M4 + M1* fully
proved, 0 unfinished proofs / 0 custom axioms).

## Bilingual documentation

The Chinese documents stay at the contract paths (the engine reads them via `proofs/ENGINE.yml`);
each has a side-by-side English version (`*.en.md`) for submission and English-language review.
Comments in the Lean sources, scripts and configuration files are **bilingual in place** (Chinese first, English below).

| Chinese (authoritative, contract path) | English |
|---|---|
| `README.md` | [`README.en.md`](README.en.md) |
| `AGENTS.md` | [`AGENTS.en.md`](AGENTS.en.md) |
| `plan.md` | [`plan.en.md`](plan.en.md) |
| `proofs/ENGINE.md` | [`proofs/ENGINE.en.md`](proofs/ENGINE.en.md) |
| `proofs/TASKS.md` | [`proofs/TASKS.en.md`](proofs/TASKS.en.md) |
| `proofs/EXPERIENCE.md` | [`proofs/EXPERIENCE.en.md`](proofs/EXPERIENCE.en.md) |
| `proofs/API-NOTES.md` | [`proofs/API-NOTES.en.md`](proofs/API-NOTES.en.md) |
| `proofs/LITERATURE.md` | [`proofs/LITERATURE.en.md`](proofs/LITERATURE.en.md) |
| `proofs/RESULTS.md` | [`proofs/RESULTS.en.md`](proofs/RESULTS.en.md) |
| `proofs/literature/README.md` | [`proofs/literature/README.en.md`](proofs/literature/README.en.md) |

**Entry points for submission**: `proofs/RESULTS.en.md` (answers to the three questions + evidence tables + honest boundaries),
`plan.en.md` for the mathematical content (milestones and statements), and the "How to re-check" section of `README.en.md` for reproducibility.

## License

Apache-2.0
