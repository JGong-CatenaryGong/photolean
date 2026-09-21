# proofs/METHOD.md — the reusable formalization template (distilled from six theories)

> **Status.** This is the goal-③ deliverable of the project: the *reusable* part of what six delivered
> theories have in common. It is written from the delivered tree, not from intentions: every claim
> below names the theories and files that evidence it. Companion documents: the contract
> `proofs/ENGINE.md` (process, roles, gates), the relation graph `theories/RELATIONS.md` (what the
> theories say about each other), and the experience bank `proofs/EXPERIENCE.md` (failure paths).
> Language: English, per the language policy (this is a proof-process artifact).

## 1. What is reusable and what is not

Six theories are delivered: Marcus inverted region, Hammond postulate, Bell–Evans–Polanyi principle
(batch 1, one shared two-parabola kernel), Kasha's rule, Sabatier principle / volcano plot (batch 2),
and the Goldschmidt tolerance factor with Goldschmidt's rules (batch 3). Their module maps are:

| theory | modules | substrate |
|---|---|---|
| Marcus | Basic / **Barrier, Rate** / Sharp / **Reorg, Compose** / RatModel / Instances (8) | two-parabola + `Real.exp` |
| Hammond | Basic / Criterion / Sharp / **Compose** / RatModel / Instances (6) | two-parabola |
| BEP | Basic / Criterion / Sharp / **Compose** / RatModel / Instances (6) | two-parabola |
| Kasha | Basic / Criterion / Sharp / **Compose** / RatModel / Instances (6) | finite rate cascade |
| Sabatier | Basic / Criterion / Sharp / **Compose** / RatModel / Instances (6) | descriptor optimisation |
| Goldschmidt | Basic / **Rules** / Criterion / Sharp / RatModel / Instances (6) | pure geometry |

Two conclusions follow. First, the **stable core** is `Basic` (description) / `Sharp` (exact validity
conditions) / `RatModel` (computable decision layer) / `Instances` (kernel-decided verdicts) — four
slots in all six theories. Second, the **middle slots are theory-specific**: batch 1 needs a law layer
(Marcus splits it into `Barrier`+`Rate`, the other two use `Criterion`), and a composition layer whose
content varies (Marcus: intra-theory microscopic composition; Hammond: reuse of `Marcus.Reorg`; BEP:
cross-module bridges plus abstract inner/outer split; Kasha: the Marcus bridge with a declared
modelling premise; Sabatier: the BEP-tangent/parabola comparison; Goldschmidt: **none** — a pure
geometric criterion has nothing to compose, and it uses a `Rules` slot instead). A new theory should
expect to **mutate the middle** and keep the core.

## 2. The methodology five-piece (the invariants)

1. **Statement authority first.** A skeleton probe under `theories/<theory>/probes/` carries every
   statement with placeholder bodies and must compile before any proof work. Delivery replaces the
   bodies verbatim; a fidelity checker compares the delivered signatures to the authority word for
   word (`python3 theories/BEP/probes/bep-fidelity.py --theory <t> [--milestone <M>]`, one checker for
   all six theories, 51/102/191/151/132/139 as of the 2026-09-21 review-fix round — Kasha's
   authority grew by one row and one statement was strengthened there, see its plan §3.1).
   **Five Goldschmidt authority rows
   were FALSE as first drafted and were caught by the kernel — every one before delivery**; the log
   lives in the theory's `plan.md` §3.1, and the corrections are part of the deliverable's honesty,
   not an embarrassment to hide.
2. **A `ℝ` theory plus a computable `ℚ` shadow.** `ℝ`'s order is not computable, so "which zone is
   this instance in" cannot be decided by the kernel over `ℝ`. Every theory therefore carries a `ℚ`
   copy of its decidable layer and *cast transfer lemmas* proving the copy is the real thing
   (`inBandQ_cast`, `zoneQ_eq_zone`, `qEact_cast`, `zoneQ_eq_zone` (Kasha) …). Measured boundaries are
   recorded, not guessed: `by decide` handles integer `ℚ` literals only; division-bearing literals need
   `norm_num`; `native_decide` is banned (it would import `Lean.ofReduceBool`).
3. **Sharpness as an iff plus explicit failure witnesses.** The validity condition of a description is
   stated as an equivalence (`p ⟺ parameter condition`) and its necessity direction is supported by
   *witnesses*, not by a negated quantifier: `hammond_sharp`, `descriptor_sharp`,
   `conformsOnWindow_iff_radius`, `volcano_descriptor_iff`, `kashaWithin_iff_ladderRatio`,
   `conforms_iff_radius_window`. Where the failure side matters physically it is delivered separately
   (`inverted_descriptor_holds_of_neg`, `perLevel_criterion_insufficient`, `not_descriptor_plateau`).
4. **Non-vacuity in both directions.** Each theory delivers named positives *and* named negatives:
   conforming instance rows and refusing rows, existence lemmas and counter-witnesses
   (`inst_nonvacuous`, `exists_conforming` / `exists_tooSmall` / `exists_tooLarge`,
   `rate_predicate_satisfiable_without_positive_curvature`). A theory whose predicates are inhabited
   only one way cannot support the implication claims the relation graph makes about it.
5. **Physical premises are explicit hypotheses, and they must be load-bearing.** Positivity,
   non-emptiness, and non-degeneracy appear in the statement or in a named premise bundle
   (`RateData`, the `0 < rB + rO` family), never inside a definition. The **weakest-premise standard**
   (set by Goldschmidt, `AGENTS.md` iron rule 3) adds: if the kernel does not consume a hypothesis,
   the statement is revised to drop it and the change is logged. Five Goldschmidt rows were dealt with
   this way — four stripped of an unconsumed premise (`conforms_symmetric_band_iff`, `zoneQ_ideal_iff`,
   `conforms_point_band_iff`, `inBandQ_ideal_iff`) and `radiusMatch_comp_ratchet` re-proved on the
   weakest premise after a verifier's adversarial round showed two of its hypotheses were
   non-load-bearing. The batch-1 theories predate this standard: their decorative premises are
   *documented as decorative* and kept for signature fidelity, and those frozen statements are not
   retro-swept.

## 3. Substrate adaptation patterns (measured, not proposed)

| substrate | the mathematics that works | what was deliberately avoided |
|---|---|---|
| two-parabola (Marcus/Hammond/BEP) | `field_simp` + `ring` for the rational identities, `nlinarith` for order, one `Real.exp` monotonicity point per file | nothing needed beyond elementary real algebra |
| finite rate cascade (Kasha) | finite Markov chain over `Finset` ranges, products/sums of branching probabilities, an **effective two-level reduction** theorem instead of an N-level induction where possible | **measure theory**: the exponential-clock derivation of the branching probabilities types but its bounded proof is out of budget — closed as a documented negative (K4b) |
| descriptor optimisation (Sabatier) | `max` of two affine branches; the volcano's sharpness is a sign condition on the product of slopes | **calculus**: no derivative of the activity is taken anywhere |
| pure geometry (Goldschmidt) | `Real.sqrt` algebra with `√2` pushed into exact rational **squares** for the decision layer; `div_le_iff₀` instead of squaring where possible | a coordination-number *function* over Shannon's table (would need a large finite table or an axiom — excluded by plan) |

The pattern to reuse: **choose the model shape that keeps the sharp condition inside the algebra the
toolchain handles well**, and record explicitly what was excluded and why.

## 4. The relation graph: five edge types plus the registry

`PhotoLean/Relations.lean` (shared kernel `PhotoLean/Kernel.lean`) is the single home of cross-theory
claims, organised by edge type, and `theories/RELATIONS.md` is its bilingual discussion:

* **true equivalence** (`↔`, proved, non-definitional) — e.g. `transfer_eq_tsCoord_bridge`,
  `epBounds_iff_no_inverted_direction`, `hammond_sharp_iff_marcus_sharp`;
* **one-way entailment** (`→`, labelled as such) — `epBounds_of_reactionRegion`,
  `hammondDescriptor_of_epConformsOnWindow`;
* **definitional reuse / certificates** (`rfl`) — the eight kernel certificates, whose purpose is a
  **regression alarm**: a failing `rfl` means definitions drifted, and the response is to investigate,
  never to edit a delivered module to restore the certificate;
* **composition** (a newer theory consumes an older one) — Kasha → Marcus (conditional on the declared
  premise `hic`), Sabatier → BEP;
* **non-relations / look-alikes** — N1–N4: statements that share a *shape* without an edge
  (`hammond_trend_exact_bep_law_inexact`, `rate_predicate_satisfiable_without_positive_curvature`,
  the Sabatier↔Marcus optimum contrasts, the Goldschmidt↔Sabatier band/deviation coincidence);
* **the no-edge registry** (`Relations.lean` §10): every pair without a relation, with its measured
  dependency fact and its modelling reason. An absent edge is a registered fact, not an oversight.

## 5. Verification discipline

Three gates, all scripted (`AGENTS.md` iron rules 1/6/7): build, `check.sh --strict` (sorry / admit /
custom `axiom` / `constant` scan over `SOURCE_DIRS`), and `axioms.sh` per theorem
(`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`). The writer never adjudicates their own
work: a read-only verifier re-runs the gates and writes its own adversarial probes — the delivered
record contains 1000-point exact-rational searches, 248 832-tuple degenerate-input searches,
counterexamples proving named hypotheses load-bearing, and independent recomputations of every
instance row. Milestones are ticked only from a verifier verdict, and the acceptance record table in
each `TASKS.md` is the evidence.

## 6. Measured traps (each cost a round; all are in `EXPERIENCE.md`)

1. A bare `lake build` on an unchanged tree is a cached no-op — "zero warnings" from it is vacuous;
   force re-elaboration when warnings are part of the evidence.
2. The fidelity checker globs `PhotoLean/<Theory>/*.lean`: it does not see `private` helpers, the
   kernel, or the relation module — those need their own authority (the compile-time re-export pin).
3. The strict scan reads block comments too, so a file header may not spell out the forbidden
   keywords.
4. **"Unused" ≠ "implied"**: an unconsumed hypothesis is weaker than the theorem, but it is not
   derivable from the others — say "the proof does not use it" and give a kernel counterexample, or
   drop it (the weakest-premise standard).
5. **The status-flip seam** (four instances: README module count, theory count, Marcus-era documents,
   the Goldschmidt G4–G6 flip): ticking a milestone must be followed by a sweep of the downstream
   status texts — `RESULTS.md`'s verification paragraph, the `TASKS.md` row bodies against their
   headers, and the acceptance table. `AGENTS.md` iron rule 8 item ③ is that checklist.
6. A measurement tool's own correctness must be checked before its verdict is believed: a
   comment-stripping comparison that reset its block-comment depth per line falsely reported a
   declaration plane as changed.

## 7. Limitations of this template

It is distilled from four substrates, all of which are **algebraic** in nature. It has not been tested
on a theory whose sharp condition needs analysis (differential equations, spectral objects), measure
theory, or probabilistic semantics — Kasha's closed negative result (K4b) is the closest the corpus
comes, and it took the measure-theoretic route *out* of scope on purpose. The five-piece methodology
and the edge taxonomy should transfer; the middle module slots should be expected to change.
