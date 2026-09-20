# Formalization Engine Contract

> *English translation of `proofs/ENGINE.md`. The Chinese original at `proofs/ENGINE.md` is authoritative — the formalization engine's contract (`proofs/ENGINE.yml`) reads the Chinese paths.*

> This document defines the interface between the **project-agnostic formalization engine** and a **concrete theory project**.
> The engine is implemented as a DSH Agent preset; this project (PhotoLean) is one instance of it.

## 0. Design Thesis

Making AI useful for the rigorization of phenomenological theories, what is genuinely hard in engineering terms is not "getting a model to write Lean", but three things:

1. **Discipline cannot rest on good intentions** — the absence of unfinished proofs and of custom axioms must be a **script-level, executable criterion**, not a line of friendly advice inside a persona;
2. **Iteration must have memory** — failed paths have to sediment, otherwise every fresh agent in every round re-treads the same dead ends;
3. **Acceptance must be independent** — the role that writes a proof must not itself judge that "the proof is finished".

Hence the engine's architecture is: **role separation (writing) + scripted evidence gate (judging) + experience bank (memory)**.
All three rest on data files, so switching to another theory requires only rewriting the data, not changing the engine.

### Relation to Hyra / AlphaEvolve

| | Mechanism core | Realization in the Lean setting |
|---|---|---|
| **AlphaEvolve** | A candidate **population** + mutation + selection pressure | Multiple tactic paths for one lemma serve as candidates; `workflow` explores them concurrently, then the best is kept |
| **Hyra-1.0** | An **experience bank** + producer–consumer, with the evaluator and the solution **co-evolving** | `EXPERIENCE.md` is the experience bank; `workflow`/`ralph` are the producers |
| **Key simplification** | The evaluator may be reward-hacked, hence an outer refinement loop is needed | **The Lean kernel cannot be hacked**: if `lake build` passes, it is true. The two loops collapse into one: it suffices to accumulate experience, with no need to evolve the evaluator |

This simplification is the engine's structural advantage over generic scientific-discovery agents: **the termination criterion is trustworthy**; there is no failure mode of the kind "the score went up but the solution is fake".

## 1. Leaf Data Plane — the only interface

The engine only reads the **declarations** in these files; their paths are written in `proofs/ENGINE.yml`.
Changing project = changing repository + rewriting these files.

| File | Role | Writer (single source of truth) |
|---|---|---|
| `theories/Marcus/plan.md` | Theory plan: milestones, statements, proof sketches, sprint order, acceptance criteria | human + lead |
| `theories/Marcus/TASKS.md` | Task board: single source of truth for status | **lead only** ticks the boxes |
| `proofs/EXPERIENCE.md` | Experience bank: success and failure patterns, reused across rounds | all roles write back |
| `proofs/API-NOTES.md` | mathlib API calibration log (single source of truth for name drift) | api_researcher |
| `theories/Marcus/LITERATURE.md` | Literature survey log: sources, conclusions, **formalizable implications** | literature_researcher |
| `theories/Marcus/probes/` | `#check` probes, committable | api_researcher |

**Rule: no role may claim that a task is complete while bypassing TASKS.md.**
A worker reporting DONE ≠ the task being DONE; the box is ticked by the lead only after the verifier PASSes it.

## 2. Role Roster (project-agnostic)

The engine's preset registers fixed role names; **each role's concrete responsibilities are read from the leaf data plane**.
A persona describes only "how to do it", and never hard-codes "which file".

| Role | Tool name | Permissions | Responsibilities |
|---|---|---|---|
| `prover_a` … `prover_d` | tool of the same name | read/write source | prove within the assigned area; exclusive file ownership |
| `api_researcher` | `api_researcher` | read/write `API-NOTES.md`/`probes/` | mathlib name calibration; guessing names is forbidden |
| `verifier` | `verifier` | **read-only** | run the evidence gate independently; return PASS/FAIL |
| `literature_researcher` | `literature_researcher` | read/write `LITERATURE.md` | literature survey; produce "formalizable implications" |

`prover_a..d` is a **pool**, not a hard binding: the concrete area split is determined by the milestones in `theories/Marcus/plan.md` and the owner column in `TASKS.md`. If a project has only two areas, only a and b are used.

## 3. Acceptance Gate (scripted; the engine inlines no criteria)

Delivering one lemma must pass, in order:

```bash
lake build <module>                          # 1. compile
proofs/scripts/check.sh --strict <module>    # 2. unfinished-proof / custom-axiom scan + build
proofs/scripts/axioms.sh <Module> <theorem>  # 3. #print axioms contains only infrastructure axioms
git log -1 --oneline                         # 4. commit message matches feat(<area>): <lemma>
```

The pass criterion of step 3 is defined by `ALLOWED_AXIOMS` in `ENGINE.yml`
(default `propext Classical.choice Quot.sound`). **The appearance of `sorryAx`
or of any custom axiom is a FAIL** — this is the executable form of "axiom discipline".

## 4. Iteration Loop (self-reflection)

Tool choice falls into three tiers by task size; **what they share is that the experience bank is written back at the end of every round**:

| Scenario | Tool | Loop shape |
|---|---|---|
| A batch of independent lemmas | `workflow` | a single fan-out, `parallel`/`pipeline` concurrency, structured results collected |
| A single stuck proof | `ralph` | multiple rounds of fresh agents, the workspace as long-term memory, `EXPERIENCE.md` refined round by round |
| A long milestone | the goal tool (`create_goal`) | persists across rounds, with `TASKS.md` as the source of truth for progress |

**Writing back to the experience bank is mandatory**: every BLOCKED or success appends one entry (format in `EXPERIENCE.md`).
The "tried and failed" column must not be empty — an entry with no failure information is regarded as invalid.

### Example experience-bank entry (format reference)

```markdown
## 2026-09-20 — strictMono composition with 1/x — prover_b — DONE
- Goal: monotonicity of `fun x => 1 / f x` under `StrictAntiOn f s`
- Tried and failed:
  - finishing with `positivity` alone → first needs an explicit hypothesis `f x > 0`
  - `linarith [one_div_lt_one_div_of_lt ...]` → missing `0 < f b`, direction reversed
- What worked: first `have hb : 0 < f b := ...`, then `one_div_lt_one_div_of_lt hb h`; commit <hash>
- Reusable pattern: **first establish positivity with a `have`, then invoke `*_div_*`-style lemmas**; do not expect `linarith` to supply the missing hypothesis automatically
```

## 5. Literature Survey Procedure

The output of `literature_researcher` must land in `LITERATURE.md`, and every entry contains:

1. **Source**: DOI / arXiv id / title, checkable;
2. **Conclusion**: what the reference claims about the theory;
3. **Formalizable implication**: which assumptions can be made explicit as Lean hypotheses, which are physical approximations, and which are not expressible under the current mathlib (this column is the **only** part that is useful to the formalization).

Original paper PDFs and LaTeX sources go in `theories/Marcus/literature/`; dumping the full content of a PDF into the context is forbidden.

## 6. Toolchain Environment (machine-specific, must be observed)

- The toolchain is unpacked in `.toolchain/` (Lean 4.17.0) and is **not on PATH**;
  always invoke `lake` through `proofs/scripts/lake`.
- `.lake/packages` and `.toolchain` are **symlinks** to an already-built cache:
  a cold `lake build` takes about 10 seconds (mathlib oleans are cached). **Do not run `lake update`** —
  it rewrites the manifest and triggers a full rebuild lasting hours.
- The mathlib rev must match `lean-toolchain`; upgrading requires changing both together and re-pulling the cache.
