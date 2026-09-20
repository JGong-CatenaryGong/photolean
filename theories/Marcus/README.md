# Marcus theory — data plane

This directory holds **everything specific to the Marcus inverted-region theory** (one theory = one
directory). The engine itself lives in `proofs/` and is theory-agnostic; see `proofs/ENGINE.md`
and the contract `proofs/ENGINE.yml`.

## Layout

| Path | Role |
|---|---|
| `plan.md` | theory plan: milestones, exact Lean statements, proof sketches, sprint order |
| `TASKS.md` | task board — the single source of truth for status (per-lemma owner + verifier verdicts) |
| `RESULTS.md` | **the human-facing deliverable** (bilingual: English original + Chinese rendering) |
| `LITERATURE.md` | literature survey; every source must carry a "formalizable implication" |
| `probes/` | `#check` / risk / cross-check probes and the fidelity checker (evidence trail) |
| `literature/` | source PDFs and page renders (git-ignored; only the READMEs are tracked) |
| `PhotoLean/Marcus/*.lean` | the Lean sources (module `PhotoLean.Marcus.*`) — see below |

### Why the Lean sources are not in this directory

Lean requires a module's name to match its path relative to the library root: the library is
declared in `lakefile.toml` as `[[lean_lib]] name = "PhotoLean"`, so `PhotoLean/Marcus/Basic.lean`
is the module `PhotoLean.Marcus.Basic`. Moving the sources here would rename every module and
invalidate every recorded fully-qualified theorem name. The sources therefore stay at
`PhotoLean/Marcus/`, and this directory holds the rest of the theory.

## Modules

`PhotoLean/Marcus/` — 8 modules, 70 theorems, 0 `sorry` / 0 custom axioms:

| Module | Content |
|---|---|
| `Basic.lean` | barrier `(lam-x)²/(4·lam)`, rate `A·exp(-ΔG‡/(k_B T))`, region predicates, `InvertedDescriptor`, decidable classifier `Zone`/`zone` |
| `Barrier.lean` | barrier algebra: non-negativity, zero barrier at `x = lam`, symmetry, both monotone branches, the `lam < 0` reversal, the `lam = 0` degeneracy |
| `Rate.lean` | the single real-analysis pivot (`rate_gt_of_barrier_lt`) plus normal/inverted monotonicity and the peak at `x = lam` |
| `Sharp.lean` | **main theorem** `descriptor_sharp`: `(∀x, 0 < rate) ∧ InvertedDescriptor ⟺ 0 < A ∧ 0 < lam`, with the necessity split into the `lam < 0` and `lam = 0` branches |
| `Reorg.lean` | `lam = lamIn + lamOut`, Pekar-factor positivity, and `hgeom_of_nonoverlap` (the geometric factor follows from non-overlapping spheres) |
| `Compose.lean` | `descriptor_holds_of_microscopic` / `..._of_nonoverlap`: microscopic positivity ⇒ the descriptor holds |
| `RatModel.lean` | ℚ-side layer: computable `zoneQ` classifier, `zoneQ_eq_zone` transfer lemma, `barrierQ_cast` numeric bridge |
| `Instances.lean` | instance judgments: region classification, descriptor instantiation, and rate comparisons on literature parameters (MCC `lam = 1.20` eV, photosynthetic reaction centre `lam = 0.25` eV) |

## How to re-check

```bash
proofs/scripts/check.sh --strict                                    # build + whole-tree sorry/axiom scan
python3 theories/Marcus/probes/marcus-fidelity.py                   # every statement vs the authoritative skeleton
proofs/scripts/lake env lean theories/Marcus/probes/marcus-all-axioms.lean   # #print axioms for all theorems
proofs/scripts/axioms.sh PhotoLean.Marcus.Sharp PhotoLean.Marcus.descriptor_sharp
```

Read `RESULTS.md` for the answers, the evidence tables, and the honest boundaries (in particular:
the classical model over-predicts the inverted-region drop by ≈3.6 orders of magnitude, so instance
conclusions only claim that the *classical model* satisfies the descriptor).

## Adding another theory

1. `PhotoLean/<Theory>/` — the Lean sources (module `PhotoLean.<Theory>.*`).
2. `theories/<Theory>/` — plan, task board, literature, probes, results.
3. Point the corresponding leaves in `proofs/ENGINE.yml` at the new directories.

Two leaves stay engine-level because they are shared across theories: `proofs/EXPERIENCE.md`
(cross-round experience bank) and `proofs/API-NOTES.md` (mathlib name calibration).
