# theories/Einstein/plan.md — PhotoLean formalization plan: the Einstein A/B coefficients and the oscillator-strength equivalence chain (EB1–EB4)

> Status: **Phase 1 (statement formalization)** — the statement inventory of §4 is the frozen
> design; the statement authority `probes/Einstein-statement-skeleton.lean` transcribes it
> verbatim with placeholder proof bodies. No proof work in Phase 1.
> Authority: contract `proofs/ENGINE.yml`; board `theories/Einstein/TASKS.md`.
> Batch: the photophysics subgraph (human request 2026-09-22), group C (pure
> geometric/spectroscopic basis), second theory of the group.

---

## 1. Overall goal and boundaries

### 1.1 The claim

The Einstein coefficients of one transition are related by `A₂₁ = (8πhν³/c³)·B₂₁` and
`g₁·B₁₂ = g₂·B₂₁` (detailed balance); the oscillator strength is proportional to `A₂₁` with the
degeneracy ratio (`f₁₂ ∝ (g₂/g₁)·A₂₁`, collected positive constant); the Strickler–Berg form
writes the radiative rate against the integrated absorption (another collected positive
constant). The theory's content is the **equivalence chain**: each conversion is invertible, and
every round trip around the chain is the identity — knowing any one of `{A, B₂₁, B₁₂, f, ∫ε}`
determines all others. The radiative lifetime is `1/A`, and the fluorescence yield of a two-
channel decay is `A·τ` — the anchor row into QuantumYield.

### 1.2 The model (chosen, not derived)

One electronic transition between levels of degeneracies `g₁, g₂ > 0`; the radiation-density
factor `radFactor h c ν := 8πhν³/c³` kept explicit (with `Real.pi`); the oscillator-strength and
Strickler–Berg proportionality constants collected as single positive parameters `Cf, Ci`
(their internal structure is a registered non-goal — the chain's content is invertibility, not
the constants' anatomy). Totalized division with explicit positivity premises.

### 1.3 Explicit non-goals

* No blackbody radiation theory (the factor is a parameter with its explicit `π h ν³/c³` form).
* No lineshape functions (integrated intensities only).
* The constants' internal structure (`Cf`, `Ci`) is not unfolded — registered.

## 2. Conventions and symbols

`h c ν > 0` (Planck constant, light speed, frequency); `g₁ g₂ > 0` degeneracies; `B21` the
stimulated-emission coefficient. Namespace `PhotoLean.Einstein`; rational layer
`PhotoLean.Einstein.Rat` (rational *surrogate* constants — the physical `radFactor` involves
`π`; the rational layer tests the algebra at rational constants, registered).

## 3. Statement authority and inventory

The authority is `probes/Einstein-statement-skeleton.lean` (Phase-1 placeholder bodies; sha256
on the board once compiling).

### 3.1 Statement-correction log

* **Entry 2 (EB-C8 first form, 2026-09-23, Phase-3 premise audit)** — the premises
  `hA : 0 < A` and `hkNR : 0 ≤ kNR` of `yield_radiative` were dropped: `A * (1 / (A + kNR)) =
  A / (A + kNR)` is `mul_one_div`, unconditional under totalized division (verifier run 1, W6).
* **Entry 3 (EB-R2, 2026-09-23, Phase-3 vacuity/mis-naming audit, verifier run 1 finding M4)** —
  `radFactor_not_rational` was re-frozen from `Irrational Real.pi` (a row that does not mention
  `radFactor` — a re-export of `irrational_pi`) to `Irrational (radFactor 1 1 1)`: the physical
  radiation factor at unit parameters is `8π`, irrational by `irrational_int_mul_iff`
  (`radFactor 1 1 1 = (8 : ℤ) * Real.pi`, probe-verified).

* **Entry 1 (EB-C6, 2026-09-22, detected at Phase 2 by prover_d)** — the §4 text's middle conjunct
  printed `aOfB K (aOfB K A / K) / K = A / K`; the correct identity is `= A`
  (`K·(K·A/K)/K = A`). The statement authority and the delivered proof carry the correct `= A`;
  this entry fixes the plan text of record.

## 4. Statement inventory

Module plan (Phase 2): `Basic.lean` (EB-B), `Criterion.lean` (EB-C), `RatModel.lean` (EB-R),
`Instances.lean` (EB-I).

**EB-B (definitions):**

* EB-B1 `radFactor (h c ν : ℝ) : ℝ := 8 * Real.pi * h * ν ^ 3 / c ^ 3`.
* EB-B2 `aOfB (K B21 : ℝ) : ℝ := K * B21` — the A coefficient from B and the radiation factor.
* EB-B3 `b12OfB21 (g1 g2 B21 : ℝ) : ℝ := (g2 / g1) * B21` — detailed balance.
* EB-B4 `fOfA (Cf g1 g2 A : ℝ) : ℝ := Cf * (g2 / g1) * A` — the oscillator strength.
* EB-B5 `aOfInt (Ci I : ℝ) : ℝ := Ci * I` — the Strickler–Berg form (radiative rate from the
  integrated absorption, collected constant).
* EB-B6 `tauR (A : ℝ) : ℝ := 1 / A` — the radiative lifetime.

**EB-C (the equivalence chain):**

* EB-C1 `radFactor_pos (hh : 0 < h) (hc : 0 < c) (hν : 0 < ν) : 0 < radFactor h c ν`
  (`Real.pi_pos` + positivity).
* EB-C2 `bOfA_roundtrip (hK : K ≠ 0) (B21 : ℝ) : aOfB K B21 / K = B21` and
  `aOfb_roundtrip (hK : K ≠ 0) (A : ℝ) : aOfB K (A / K) = A` — A↔B invertibility.
* EB-C3 `detailed_balance (hg1 : 0 < g1) (g2 B21 B12 : ℝ) :
  (b12OfB21 g1 g2 B21 = B12 ↔ g1 * B12 = g2 * B21)` — the symmetric form; and
  `degeneracy_roundtrip (hg1 : 0 < g1) (hg2 : 0 < g2) (B : ℝ) :
  b12OfB21 g2 g1 (b12OfB21 g1 g2 B) = B` — the double swap is the identity.
* EB-C4 `af_roundtrip (hCf : Cf ≠ 0) (hg1 : 0 < g1) (hg2 : 0 < g2) (A : ℝ) :
  fOfA Cf g1 g2 A / (Cf * (g2 / g1)) = A` and the forward form — A↔f invertibility.
* EB-C5 `int_roundtrip (hCi : Ci ≠ 0) (I : ℝ) : aOfInt Ci I / Ci = I` and forward — the
  Strickler–Berg leg.
* EB-C6 `full_chain_roundtrip (hK : K ≠ 0) (hg1 : 0 < g1) (hg2 : 0 < g2) (hCf : Cf ≠ 0)
  (A B21 : ℝ) : fOfA Cf g1 g2 A / (Cf * (g2 / g1)) = A ∧
  aOfB K (aOfB K A / K) / K = A ∧ b12OfB21 g2 g1 (b12OfB21 g1 g2 B21) = B21` — the chain
  closes around every leg (stated as the conjunction of the legs at shared premises; the point
  is one row naming the whole cycle). **Corrected at Phase 2** (§3.1 entry 1): the middle conjunct
  was printed `= A / K`, which is false (`K = 2, A = 1` gives `1 = 1/2`); `K·(K·A/K)/K = A` is the
  identity the row needs. The statement authority and the delivered proof already carried `= A`.
* EB-C7 `f_pos_iff_a_pos (hCf : 0 < Cf) (hg1 : 0 < g1) (hg2 : 0 < g2) (A : ℝ) :
  (0 < fOfA Cf g1 g2 A ↔ 0 < A)`.
* EB-C8 `fluorescence_lifetime (A kNR : ℝ) : 1 / (A + kNR) = 1 / (A + kNR)`… **corrected at
  design time** — the content row is the yield anchor:
  `yield_radiative (hA : 0 < A) (hkNR : 0 ≤ kNR) :
  A * (1 / (A + kNR)) = A / (A + kNR)` (the fluorescence yield of a two-channel decay is the
  radiative rate times the lifetime — the QuantumYield edge anchor; trivial as algebra, stated
  so the edge has a home) and `lifetime_pos (hA : 0 < A) : 0 < tauR A`.

**EB-R (rational decision layer):**

* EB-R1 `Rat.aOfB`, `Rat.b12OfB21`, `Rat.fOfA`, `Rat.aOfInt`, `Rat.tauR` over `ℚ` + cast
  coherence.
* EB-R2 round-trip verdicts at rational surrogate constants (`K = 3`, `Cf = 5`, `g1 = 1`,
  `g2 = 3`, …) by `decide`; a row registering that the physical `radFactor` is not rational
  (contains `π`) and the ℚ layer tests the algebra at surrogates (honesty, one line).

**EB-I (named instances):**

* EB-I1 `twoLevelDyeLike` (surrogate constants as in EB-R2): the full round-trip computed at ℚ
  by `decide`.
* EB-I2 `degeneracySwap` (`g1 = 1, g2 = 3`): the B12/B21 asymmetry computed both ways and the
  round-trip closed (`decide`).

## 5. Proof routes

All rows are `field_simp` + `ring` with the positivity side-conditions; EB-C1 needs
`Real.pi_pos` and `mul_pos`/`div_pos` chains; EB-C3's iff is `div_mul_eq_mul_div` +
`mul_right_cancel₀`/`div_eq_iff` algebra. No risk beyond `field_simp` normal forms; the lightest
theory of group C.

## 6. Sprint order, ownership, dispatch

Sprint EB0 (Phase 1) → EB1 `Basic` → EB2 `Criterion` → EB3 `RatModel` → EB4 `Instances`.
Owner: prover_d (group C block, after Forster).

## 7. Acceptance criteria and gate commands

    proofs/scripts/lake build PhotoLean.Einstein.Basic   (etc. per module)
    proofs/scripts/check.sh --strict PhotoLean.Einstein.Criterion
    proofs/scripts/axioms.sh PhotoLean.Einstein.Criterion PhotoLean.Einstein.detailed_balance
    python3 theories/BEP/probes/bep-fidelity.py --theory Einstein

## 8. Risks and mitigations

* `radFactor_pos`'s `Real.pi_pos` API name must be probed (it is stable mathlib, low risk).
* The rational layer is explicitly surrogate-based (π is irrational); the honesty row EB-R2
  keeps the gate honest about what the ℚ instances do and do not show.

## 9. Honesty table

| # | Assumed (declared premise) | Proved (theorem) |
|---|---|---|
| 1 | The conversion constants (`K`, `Cf`, `Ci`) are positive parameters | EB-C rows |
| 2 | `Cf`, `Ci` internal structure is out of scope (registered non-goal) | — |
| 3 | The ℚ layer tests the algebra at rational surrogates, not the physical constants | EB-R rows |

## 10. Edge candidates (toward the 7 delivered nodes + the 8 batch siblings)

* **QuantumYield — composition (machine target)**: the radiative channel rate is `A`; EB-C8 is
  the anchor row (`yield = A·τ`).
* **StokesShift — look-alike (N-class candidate)**: detailed balance (intensities) vs mirror
  symmetry (positions) — same slogan, different objects; register the shape.
* **Forster — premise-level**: the overlap integral `J` consumes normalized spectra whose
  intensities are Einstein data; registered as a modelling premise (no Lean row).
* **SternVolmer / FluorPhos / Kasha / KashaVavilov** — via QuantumYield only (the `rad` rates
  are `A` coefficients); registered, no direct rows.
* **Marcus / Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor / EnergyGapLaw /
  ICvsISC**: no edge (radiative conversions share no object with surfaces, barriers, ladders, or
  geometries) — absence drafts registered.

## 11. Position in the repository

Ninth theory of the batch, second of group C; self-contained (`Mathlib` only); completes the
photophysics batch's statement layer.
