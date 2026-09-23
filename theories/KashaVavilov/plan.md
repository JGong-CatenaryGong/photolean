# theories/KashaVavilov/plan.md — PhotoLean formalization plan: the Kasha–Vavilov rule and the D2 adjudication (KV1–KV3)

> Status: **Phase 1 (statement formalization)** — the statement inventory of §4 is the frozen
> design; the statement authority `probes/KashaVavilov-statement-skeleton.lean` transcribes it
> verbatim with placeholder proof bodies. No proof work in Phase 1.
> Authority: contract `proofs/ENGINE.yml`; board `theories/KashaVavilov/TASKS.md`; experience bank
> `proofs/EXPERIENCE.md`; literature `theories/KashaVavilov/LITERATURE.md`.
> Batch: the photophysics subgraph (human request 2026-09-22), group A (rate-cascade basis),
> first theory of the construction order; home of adjudication target **D2** (Kasha vs
> Kasha–Vavilov logical independence).

---

## 1. Overall goal and boundaries

### 1.1 The claim

Vavilov's rule: the fluorescence quantum yield (and, in its spectral form, the emission spectrum)
is **independent of the excitation wavelength**. Kasha's rule (delivered as the fourth theory of
this repository): emission comes only from the lowest excited state of a given multiplicity. The
two rules are run together in the textbooks and are often treated as one statement; the delivered
module `PhotoLean.Kasha.Criterion` already contains the conditional equivalence
`kashaRule_iff_vavilovUpTo` (with a loss channel at the lowest level, the closed rules coincide).
**D2 adjudicates the pair**: pointwise, the two predicates are *logically independent* (each has
admissible witnesses where it holds and the other fails — inside the lossy regime, not only in
degenerate corners); the coincidence holds exactly under the closed quantification plus the loss
premise; and the lossless corner separates the closed forms, so the premise is load-bearing.

### 1.2 The model (chosen, not derived)

The model is the delivered finite excited-state ladder of `PhotoLean.Kasha.Basic` — this theory
**reuses the Kasha basis by import** (hard-constraint reading registered 2026-09-22: constraint 1's
copy-and-pin pattern applies to the two-parabola kernel objects, of which this theory needs none;
the ladder base is imported, and compile-time drift protection comes from the import itself plus
the Relations registration in Phase 3). Level `0` is the lowest excited state of the multiplicity;
`rad n`, `ic n` are the radiative / nonradiative rates; the observables are `Kasha.fluoYield`,
`Kasha.upperYield`, `Kasha.specFrac`. Totalized division throughout; every positivity is an
explicit hypothesis (engine rule 3), and the weakest-premise standard of iron rule 3 applies to
every new row.

### 1.3 Explicit non-goals

* No time-resolved kinetics (the ladder is a branching model, registered in the Kasha plan §1.2).
* No new decision-layer module: the rational layer is inherited from `PhotoLean.Kasha.RatModel`;
  the D2 witnesses are rational-valued ladders whose verdicts close by `norm_num` over ℝ (kernel
  computation on rational literals — no runtime evaluation enters any theorem).
* The `RatModel`/`Sharp`/`Compose` modules are **omitted by decision** (registered here, not
  forgotten): D2 needs no zone classifier beyond `Kasha.Rat.zoneQ`, no sharp threshold beyond the
  delivered `kashaGapThreshold`, and its Relations registration is Phase-3 lead work.

---

## 2. Conventions and symbols

`Kasha.RateData rad ic N` — the delivered premise bundle (positive total decay up to `N`,
nonnegative rates). `KashaRule rad ic N := upperYield rad ic N = 0`;
`VavilovAt rad ic N := fluoYield rad ic (N+1) = fluoYield rad ic N`;
`VavilovUpTo rad ic N := ∀ i < N, VavilovAt rad ic i`. New predicate of this theory:
`SpecSame rad ic M N` — the normalized spectra at two excitation levels agree on the common
levels. Namespace `PhotoLean.KashaVavilov`.

---

## 3. Statement authority and inventory

The authority is `probes/KashaVavilov-statement-skeleton.lean` (Phase-1 placeholder bodies,
sha256 recorded on the board once compiling).

### 3.1 Statement-correction log

* **Entry 2 (KV-B4/KV-C5, 2026-09-23, Phase-3 premise audit, verifier run 1
  findings W4/W5)** — the `RateData` premise of `specFrac_zero_of_kashaRule` and the `i ≤ N`
  premise of `cascade_pos_iff` were dropped: neither proof consumed them (the split identity is
  premise-free; the cascade iff degenerates consistently for `i > N`, both sides trivially
  true). The now-empty linter suppressions were removed; the `d2_verdict` suppression stays with
  an accurate comment (it covers lambda-binder noise, not a premise).

* **Entry 0 (2026-09-22, literature note — no statement change)** — the canonical Vavilov rule
  quantifies over the quantum YIELD only (LITERATURE S3, Birks p. 392); the spectral form
  `SpecSame` is this theory's own predicate and must not be attributed to Vavilov in
  docstrings or RESULTS. No frozen statement is affected.

## 4. Statement inventory

Module plan (Phase 2): `Basic.lean` (KV-B rows), `Criterion.lean` (KV-C rows, the D2 core),
`Instances.lean` (KV-I rows).

**KV-B (description layer; all about `Kasha.*` objects, no new rates):**

* KV-B1 def `SpecSame (rad ic : ℕ → ℝ) (M N : ℕ) : Prop :=
  ∀ i, i ≤ M → i ≤ N → Kasha.specFrac rad ic i M = Kasha.specFrac rad ic i N` — pairwise spectral
  agreement on the common levels.
* KV-B2 `fluoYield_eq_emitYield_zero_add_upperYield (rad ic : ℕ → ℝ) (N : ℕ) :
  Kasha.fluoYield rad ic N = Kasha.emitYield rad ic 0 N + Kasha.upperYield rad ic N` — pure
  `Finset.range`/`Icc` split, no premises (totalized).
* KV-B3 `rateData_mono {rad ic : ℕ → ℝ} {M N : ℕ} (h : Kasha.RateData rad ic N) (hMN : M ≤ N) :
  Kasha.RateData rad ic M` — premise-bundle restriction.
* KV-B4 `specFrac_zero_of_kashaRule {rad ic} {N} (h : Kasha.RateData rad ic N)
  (hK : Kasha.KashaRule rad ic N) (hpos : 0 < Kasha.fluoYield rad ic N) :
  Kasha.specFrac rad ic 0 N = 1`.
* KV-B5 `specFrac_succ_of_kashaRule {rad ic} {N i : ℕ} (h : Kasha.RateData rad ic N)
  (hK : Kasha.KashaRule rad ic N) (hi1 : 1 ≤ i) (hiN : i ≤ N) :
  Kasha.specFrac rad ic i N = 0`.
* KV-B6 `kashaRule_mono {rad ic} {M N : ℕ} (h : Kasha.RateData rad ic N) (hMN : M ≤ N)
  (hK : Kasha.KashaRule rad ic N) : Kasha.KashaRule rad ic M`.
* KV-B7 `specSame_of_kashaRule {rad ic} {N : ℕ} (h : Kasha.RateData rad ic N)
  (hpos : ∀ M, M ≤ N → 0 < Kasha.fluoYield rad ic M) (hK : Kasha.KashaRule rad ic N) :
  ∀ M, M ≤ N → SpecSame rad ic M N` — the exact rule gives the spectral Vavilov rule: under
  Kasha the spectrum is the delta at level `0`, hence excitation-independent.

**KV-C (the D2 core):**

* KV-C1 `kashaRule_not_implies_vavilovAt : ∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 2 ∧
  Kasha.KashaRule rad ic 1 ∧ ¬ Kasha.VavilovAt rad ic 1 ∧ 0 < ic 0` — first independence
  direction. Witness: `rad = fun n => if n = 1 then 0 else 1`, `ic = fun _ => 1`:
  `fluoYield 1 = 1/2`, `fluoYield 2 = 3/4`. The witness sits at the positive excitation level
  `N = 1` **inside the lossy regime** (`ic 0 = 1 > 0`): the independence is not the degenerate
  corner (the M1 lesson applied prospectively).
* KV-C2 `vavilovAt_not_implies_kashaRule : ∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 2 ∧
  Kasha.VavilovAt rad ic 1 ∧ ¬ Kasha.KashaRule rad ic 1 ∧ 0 < ic 0` — second direction.
  Witness: `rad = fun n => if n = 2 then 0 else 1`, `ic = fun _ => 1`: `fluoYield 1 =
  fluoYield 2 = 3/4`, `rad 1 = 1 > 0`.
* KV-C3 `lossless_separates_kasha_vavilov : ∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 1 ∧
  ic 0 = 0 ∧ Kasha.VavilovUpTo rad ic 1 ∧ ¬ Kasha.KashaRule rad ic 1` — the `0 < ic 0` premise
  of the delivered equivalence is load-bearing: at `ic 0 = 0` the yield is identically `1`
  (`Kasha.fluoYield_eq_one_sub_loss`), Vavilov's rule holds vacuously, and Kasha's rule fails.
  Witness: `rad = fun _ => 1`, `ic = fun n => if n = 0 then 0 else 1`.
* KV-C4 `d2_verdict` — the adjudication headline, one row with the four conjuncts: KV-C1, KV-C2,
  the closed-form boundary `∀ rad ic N, Kasha.RateData rad ic N → 0 < ic 0 →
  (Kasha.KashaRule rad ic N ↔ Kasha.VavilovUpTo rad ic N)` (the delivered
  `Kasha.kashaRule_iff_vavilovUpTo` re-stated), and KV-C3.
* KV-C5 `cascade_pos_iff {rad ic} {N i : ℕ} (h : Kasha.RateData rad ic N) (hi : i ≤ N) :
  (0 < Kasha.cascade rad ic i N ↔ ∀ j, i + 1 ≤ j → j ≤ N → 0 < ic j)`.
* KV-C6 `emitYield_pos_iff {rad ic} {N i : ℕ} (h : Kasha.RateData rad ic N) (hi : i ≤ N) :
  (0 < Kasha.emitYield rad ic i N ↔ 0 < rad i ∧ 0 < Kasha.cascade rad ic i N)`.
* KV-C7 `antiKasha_observable_iff {rad ic} {N : ℕ} (h : Kasha.RateData rad ic N) :
  (0 < Kasha.upperYield rad ic N ↔ ¬ Kasha.KashaRule rad ic N)` — the anti-Kasha boundary: a
  violation of the rule is **always observable** in this model. Proof route: `→` is
  `Kasha.upperYield_eq_zero_iff` contraposed with KV-C6; `←` uses the *maximal emitter*: the
  largest `i ∈ [1,N]` with `0 < rad i` has every level above it nonradiative, hence (by
  `decay_pos`) converting with certainty, so its cascade is `1`. Sub-rows as needed:
  KV-C7a `upperYield_pos_of_rad_pos`, KV-C7b `exists_maximal_emitter` (Finset.max', classical).

**KV-I (named witnesses, rational-valued ladders; verdicts close by `norm_num` over ℝ):**

* KV-I1 def `kashaPureLadderRad : ℕ → ℚ := fun n => if n = 0 then 1 else 0`,
  `kashaPureLadderIc : ℕ → ℚ := fun _ => 1`; row: the cast ladders satisfy
  `Kasha.KashaRule · 1 ∧ Kasha.VavilovUpTo · 1` (admissible model).
* KV-I2 def `antiVavilovLadder*` (the KV-C1 witness at ℚ) + verdict row.
* KV-I3 def `vavilovOnlyLadder*` (the KV-C2 witness at ℚ) + verdict row.
* KV-I4 def `losslessLadder*` (the KV-C3 witness at ℚ) + verdict row.
* KV-I5 `instances_distinct`: the four named rad-ladders are pairwise different as functions
  (evaluated on `0,1,2`; `decide`).

## 5. Proof routes

KV-B2: `Finset.sum_range_succ` at `0` + the `Icc 1 N` reindexing (check `Kasha.Criterion` for a
delivered split first — do not re-prove a delivered row). KV-B4/B5: `kashaRule_iff_rad_zero` +
`radBranch = 0` + `zero_div`/`div_self`. KV-C1..C3: unfold `fluoYield_succ` on the literal
witnesses and close the numeric goals by `norm_num`; admissibility by `intro n hn;
interval_cases n`. KV-C7: the max-emitter argument needs a maximal-element API over
`{j ∈ Finset.Icc 1 N | 0 < rad j}` (classical); API-calibrate before proving (iron rule 4).

## 6. Sprint order, ownership, dispatch

Sprint KV0 (Phase 1, this plan + skeleton) → KV1 `Basic` → KV2 `Criterion` (D2, the batch's
headline — dispatch early) → KV3 `Instances` → Phase 3 registration into
`PhotoLean/Relations.lean` (new adjudication section). Owner: prover_b (exclusive file ownership
per module).

## 7. Acceptance criteria and gate commands

    proofs/scripts/lake build PhotoLean.KashaVavilov.Basic   (etc. per module)
    proofs/scripts/check.sh --strict PhotoLean.KashaVavilov.Criterion
    proofs/scripts/axioms.sh PhotoLean.KashaVavilov.Criterion PhotoLean.KashaVavilov.d2_verdict
    python3 theories/BEP/probes/bep-fidelity.py --theory KashaVavilov

## 8. Risks and mitigations

* The delivered `vavilovAt_iff_rad_zero` carries the premise `fluoYield N < 1`; the KV-C1/C2
  witnesses must be checked against it (both have `fluoYield 1 < 1`: `1/2`, `3/4` — fine).
* `specFrac` is totalized division: KV-B4/B5 need the explicit `0 < fluoYield` / range premises;
  do not drop them without a counterexample row (weakest-premise standard with evidence).

## 9. Honesty table

| # | Assumed (declared premise) | Proved (theorem) |
|---|---|---|
| 1 | The ladder model and its branching reading (Kasha plan §1.2, inherited) | all KV rows |
| 2 | `RateData` positivity bundle on every physical row | — |
| 3 | Named instances are representative rational models, not fitted data (LITERATURE) | their verdicts |

## 10. Edge candidates (toward the 7 delivered nodes + the 8 batch siblings)

* **Kasha — D2 adjudication (A-class)**: KV-C1..C4 + KV-C7; the boundary re-export is delivered
  upstream (`kashaRule_iff_vavilovUpTo`). Machine-target.
* **Marcus / BEP / Hammond**: no new direct edge — KV adds no energetic object; the contact runs
  through Kasha's §7 composition (`Kasha.marcusIC`). Absence draft: "the D2 layer is about
  branching laws, not barriers".
* **Sabatier / Goldschmidt / SymmetryFactor**: no edge (volcano geometry / ionic radii / curvature
  pairs share no scalar with spectral-independence laws). Absence drafts registered.
* **SternVolmer**: candidate composition — quenching enters the ladder as an added level-0 loss
  channel; Vavilov preservation under quenching is a checkable row (Phase 2 stretch).
* **QuantumYield / FluorPhos**: candidate compositions — `radBranch` is a two-channel yield;
  phosphorescence is the two-multiplicity cascade (Phase 2/3).
* **EnergyGapLaw**: candidate — the gap ordering of IC rates is the kinetic rationale of the
  funnel (extends Relations §7); one machine-target row.
* **StokesShift / ICvsISC / Forster / Einstein**: no edge candidates (spectral shapes / spin
  channels / transfer geometry / radiative conversions share no object with this layer) —
  absence drafts registered.

## 11. Position in the repository

First theory of the photophysics batch; reuses `PhotoLean.Kasha.Basic/Criterion` by import;
nothing under `PhotoLean/Kasha/*` is modified; the Relations registration is Phase-3 lead work
(iron rule 8②).
