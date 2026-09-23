# theories/FluorPhos/plan.md — PhotoLean formalization plan: fluorescence–phosphorescence competition (FP1–FP4)

> Status: **Phase 1 (statement formalization)** — the statement inventory of §4 is the frozen
> design; the statement authority `probes/FluorPhos-statement-skeleton.lean` transcribes it
> verbatim with placeholder proof bodies. No proof work in Phase 1.
> Authority: contract `proofs/ENGINE.yml`; board `theories/FluorPhos/TASKS.md`.
> Batch: the photophysics subgraph (human request 2026-09-22), group A (rate-cascade basis),
> fourth theory of the construction order.

---

## 1. Overall goal and boundaries

### 1.1 The claim

From `S₁` the molecule fluoresces (rate `kF`), converts to the ground state (`kIC`), or crosses
to the triplet manifold (`kISC`); from `T₁` it phosphoresces (`kP`) or decays nonradiatively
(`kNR`). The competition law: `φP/φF = (kISC/kF)·(kP/(kP+kNR))` — the fluorescence–
phosphorescence balance is the product of the intersystem-crossing branch and the triplet
radiative branch. The heavy-atom effect is the monotonicity of this balance in `kISC`; the
crossover (phosphorescence overtakes fluorescence) has the closed form `kF·(kP+kNR) < kISC·kP`;
and the two yields exhaust unity exactly when there is no loss (`kIC = 0`) and the triplet is
either never populated or perfectly radiative (`kISC = 0 ∨ kNR = 0`).

### 1.2 The model (chosen, not derived)

Two states with first-order branching; no reverse intersystem crossing (T₁→S₁ back-crossing is
out of scope, registered); no delayed fluorescence; no cascade above S₁ (that is Kasha's ladder;
the edge is registered). `phiP` is the cascade product of the S₁→T₁ branch and the T₁ radiative
branch. Totalized division; explicit positivity via the bundle `FPData`.

### 1.3 Explicit non-goals

* El-Sayed's rule (the orbital-character dependence of `kISC`) is a **parameter premise**, not a
  derivable row — registered in the honesty table and in LITERATURE.
* No spin statistics (the 1:3 degeneracy enters only through the rates as given).

## 2. Conventions and symbols

Rates `kF kISC kIC kP kNR : ℝ`; `s1Decay := kF + kISC + kIC`; `t1Decay := kP + kNR`. Namespace
`PhotoLean.FluorPhos`; rational layer `PhotoLean.FluorPhos.Rat`.

## 3. Statement authority and inventory

The authority is `probes/FluorPhos-statement-skeleton.lean` (Phase-1 placeholder bodies; sha256
on the board once compiling).

### 3.1 Statement-correction log

* **Entry 3 (five rows, 2026-09-23, Phase-3 premise audit, verifier run 5)** —
  `crossover_isc` drops `hkF`/`hkP`; `crossover_isc_threshold` drops `hkF` (keeps `hkP` — the
  division needs it); `hso_zero_no_phosphorescence` drops the whole `FPData` bundle (the identity
  is `zero_div` + `zero_mul`); `fpZoneQ_phosphorDominant_iff` drops `hkF`/`hkP`;
  `phiP_strictMono_isc` drops the derivable prime-side bundle `h'` (reconstructed locally from
  `h0`, `hlt` and the nonnegativity fields).
* **Entry 4 (FP-I4, 2026-09-23, Phase-3 negative-result finalization)** — the refutation of the
  FP-C5 first form (entry 2) is delivered as a theorem with its parameter witness:
  `fpC5_firstForm_refuted`, refuted at `kF = kIC = 0, kISC = 1 → 2` (both yields `1/2`). An
  authority ADDITION (row FP-I4); sha256 updated on the board.

* **Entry 0 (FP-C4, design time)** — the losslessness boundary is `kIC = 0 ∧ (kISC = 0 ∨ kNR = 0)`,
  not the naive `kIC = 0 ∧ kNR = 0`: at `kISC = 0` the triplet is never populated and no loss can
  pass through it. Carried by the inventory from the start.
* **Entry 1 (literature note, 2026-09-22, no statement change)** — the named instances are zone
  representatives (the literature's `kISC/kF` for naphthalene is ≈ 3–4, while `naphthaleneLike`
  uses 1); docstrings must say so (LITERATURE.md).
* **Entry 2 (FP-C5 second half, 2026-09-23, re-freeze by the lead; verifier run 5 PASS)** — the
  first frozen form of `phiP_strictMono_isc` (premises `FPData` both sides, `0 < kP`,
  `kISC < kISC'`) is **FALSE**: at `kF = 0, kIC = 0` the bundle is admissible and `phiP` collapses
  to `kP/(kP+kNR)`, independent of `kISC` (kernel counterexample at `kISC = 1 → 2`, both sides
  `1/2`; probe `.lake/tmp/lead_fp_c5_probe.lean`, exit 0). The authority now carries the exactly
  load-bearing premise `0 < kF + kIC` (necessary — the strict inequality cannot be relaxed to
  `0 ≤`; sufficient — the numerator difference is `(kF + kIC)·(kISC' − kISC) > 0`; verifier run 5
  confirmed both halves with its own grid). Authority sha256: Phase-1 `2aa08f1c…` → re-frozen
  `b116addd…`. The row was closed by the lead after the prover's budget was exhausted.
* **Entry 3 (premise residue, verifier run 5)** — `crossover_isc`'s `hkF`/`hkP`,
  `crossover_isc_threshold`'s and `fpZoneQ_phosphorDominant_iff`'s `hkF`, and
  `hso_zero_no_phosphorescence`'s `h` are non-load-bearing (the verifier produced stripped-form
  proofs); FP-C5b's prime-side bundle `h'` is derivable. Queued for the Phase-3 premise audit.

## 4. Statement inventory

Module plan (Phase 2): `Basic.lean` (FP-B), `Criterion.lean` (FP-C), `RatModel.lean` (FP-R),
`Instances.lean` (FP-I).

**FP-B (definitions):**

* FP-B1 `s1Decay (kF kISC kIC : ℝ) : ℝ := kF + kISC + kIC`.
* FP-B2 `phiF (kF kISC kIC : ℝ) : ℝ := kF / s1Decay kF kISC kIC`.
* FP-B3 `iscBranch (kF kISC kIC : ℝ) : ℝ := kISC / s1Decay kF kISC kIC`.
* FP-B4 `t1BranchP (kP kNR : ℝ) : ℝ := kP / (kP + kNR)`.
* FP-B5 `phiP (kF kISC kIC kP kNR : ℝ) : ℝ := iscBranch kF kISC kIC * t1BranchP kP kNR`.
* FP-B6 `structure FPData (kF kISC kIC kP kNR : ℝ) : Prop` with fields `0 ≤` each rate,
  `0 < s1Decay`, `0 < kP + kNR` — the premise bundle.

**FP-C (laws):**

* FP-C1 `phiP_eq (h : FPData ...) : phiP ... = kISC * kP / (s1Decay kF kISC kIC * (kP + kNR))`.
* FP-C2 `phiP_div_phiF (h : FPData ...) (hkF : 0 < kF) :
  phiP ... / phiF kF kISC kIC = (kISC / kF) * t1BranchP kP kNR` — the competition law.
* FP-C3 `phiF_add_phiP_le_one (h : FPData ...) : phiF ... + phiP ... ≤ 1`.
* FP-C4 `phiF_add_phiP_eq_one_iff (h : FPData ...) :
  phiF + phiP = 1 ↔ kIC = 0 ∧ (kISC = 0 ∨ kNR = 0)` — the losslessness boundary, **corrected at
  design time**: the naive `kIC = 0 ∧ kNR = 0` is too strong — with `kISC = 0` the triplet is
  never populated and no loss can pass through it. (Design-time algebra:
  `phiF + phiP = 1 ↔ kISC·kNR + kIC·(kP+kNR) = 0`, and the nonnegativity splits the sum.)
* FP-C5 `phiF_strictAnti_isc (h : FPData ...) (hkF : 0 < kF) (h' : kISC < kISC')
  (the other rates fixed, bundle at kISC' ) : phiF kF kISC' kIC < phiF kF kISC kIC`;
  `phiP_strictMono_isc (h : FPData kF kISC kIC kP kNR) (h' : FPData kF kISC' kIC kP kNR)
  (hkP : 0 < kP) (h0 : 0 < kF + kIC) (hlt : kISC < kISC') :
  phiP kF kISC kIC kP kNR < phiP kF kISC' kIC kP kNR` — the heavy-atom direction, both halves.
  **The `0 < kF + kIC` premise was added in the §3.1 entry 2 re-freeze** (the first frozen form,
  without it, is false at `kF = kIC = 0`). The prime-side `FPData` is an explicit premise (the
  verifier showed it is derivable from the rest, so it is conservative, not load-bearing).
* FP-C6 `crossover_isc (h : FPData ...) (hkF : 0 < kF) (hkP : 0 < kP) :
  (phiF kF kISC kIC < phiP kF kISC kIC kP kNR ↔ kF * (kP + kNR) < kISC * kP)` — the crossover in
  closed form; with `hkP` the equivalent threshold form `kF * (kP + kNR) / kP < kISC` is the
  same row's corollary (state both directions as two rows if the field normal forms differ).
* FP-C7 `hso_zero_no_phosphorescence (h : FPData ...) (h0 : kISC = 0) : phiP ... = 0` — the
  spin-forbiddenness boundary: with the intersystem channel shut, no phosphorescence exists,
  whatever the triplet rates.
* FP-C8 `nonvacuous_competition : ∃ kF kISC kIC kP kNR : ℝ, FPData ... ∧ 0 < phiF ... ∧
  0 < phiP ...` — witness `kF = kISC = kP = 1, kIC = kNR = 1` (`phiF = 1/3`, `phiP = 1/6`); both
  channels live, so the competition is not vacuous (the M1 lesson applied prospectively).

**FP-R (rational decision layer):**

* FP-R1 `Rat.phiF`, `Rat.phiP`, `Rat.FPData` over `ℚ` + cast coherence.
* FP-R2 `inductive FPZone | fluorDominant | balanced | phosphorDominant`;
  `fpZoneQ (params : ℚ ...) : FPZone` via the crossover comparison of FP-C6 at ℚ
  (`kF·(kP+kNR) ? kISC·kP` — decidable); correctness rows tying the zone to the real-side
  inequality at cast parameters.

**FP-I (named instances, representative rational models — LITERATURE pins the ordering):**

* FP-I1 `naphthaleneLike` (kF = 1, kISC = 1, kIC = 1/2, kP = 1/10, kNR = 1; φF = 2/5,
  φP = 2/55) — fluorescence-dominant; zone verdict `fluorDominant`.
* FP-I2 `eosinLike` (heavy-atom: kF = 1, kISC = 10, kIC = 1/2, kP = 1, kNR = 1) —
  phosphorescence-competitive; zone verdict `phosphorDominant` + the FP-C6 premise checked.
* FP-I3 `crossoverWitness`: a parameter pair straddling the FP-C6 threshold with the two zone
  verdicts (`decide` at ℚ).

## 5. Proof routes

All rows are field algebra with the positivity side-conditions from `FPData`: `field_simp` +
`ring` for C1/C2/C4; `div_le_iff` + `nlinarith` for C3; C5 by the `div` antitonicity/monotonicity
in the denominator/numerator respectively; C6 by `div_lt_div_iff` chains. No `exp`, no `Finset`.

## 6. Sprint order, ownership, dispatch

Sprint FP0 (Phase 1) → FP1 `Basic` → FP2 `Criterion` → FP3 `RatModel` → FP4 `Instances`.
Owner: prover_c (group A block with SternVolmer/QuantumYield).

## 7. Acceptance criteria and gate commands

    proofs/scripts/lake build PhotoLean.FluorPhos.Basic   (etc. per module)
    proofs/scripts/check.sh --strict PhotoLean.FluorPhos.Criterion
    proofs/scripts/axioms.sh PhotoLean.FluorPhos.Criterion PhotoLean.FluorPhos.crossover_isc
    python3 theories/BEP/probes/bep-fidelity.py --theory FluorPhos

## 8. Risks and mitigations

* FP-C4 was corrected at design time (see its note); the skeleton must carry the corrected form —
  the correction is logged here prospectively (plan §3.1 entry 0).
* The prime-side premise bookkeeping in FP-C5 (the `FPData` bundle at the shifted parameter) is
  the row most likely to need a statement adjustment; any change goes to §3.1 with evidence.

## 9. Honesty table

| # | Assumed (declared premise) | Proved (theorem) |
|---|---|---|
| 1 | Two-state branching model; no reverse ISC; no delayed fluorescence | FP-C1..C8 |
| 2 | El-Sayed's rule enters only as the parameter `kISC` (LITERATURE) | — |
| 3 | Named instances are representative, not fitted | their zone verdicts |

## 10. Edge candidates (toward the 7 delivered nodes + the 8 batch siblings)

* **QuantumYield — composition (machine target)**: `phiF` is the `Fin 3` `yieldOf` at index 0;
  `phiP` is the cascade product of two yields.
* **SternVolmer — composition (machine target)**: quenching adds `kq·q` to `s1Decay`; the ratio
  `phiP/phiF` is invariant under dynamic quenching (the quench cancels in FP-C2) — one row.
* **ICvsISC — composition (machine target)**: `kISC`'s gap dependence is the ICvsISC rate; the
  crossover moves with the energy gaps.
* **Kasha — composition candidate**: the two-multiplicity ladder projected on `{S₁, T₁}` is this
  model; one-way row (the ladder is finer).
* **Marcus / Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor / KashaVavilov /
  EnergyGapLaw (except via ICvsISC) / StokesShift / Forster / Einstein (except via QY)**: no
  direct edge — absence drafts registered.

## 11. Position in the repository

Fourth theory of the batch; self-contained (`Mathlib` only); completes group A.
