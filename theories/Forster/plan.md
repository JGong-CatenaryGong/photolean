# theories/Forster/plan.md — PhotoLean formalization plan: Förster resonance energy transfer and the κ² convention (FO1–FO4)

> Status: **Phase 1 (statement formalization)** — the statement inventory of §4 is the frozen
> design; the statement authority `probes/Forster-statement-skeleton.lean` transcribes it
> verbatim with placeholder proof bodies. No proof work in Phase 1.
> Authority: contract `proofs/ENGINE.yml`; board `theories/Forster/TASKS.md`.
> Batch: the photophysics subgraph (human request 2026-09-22), group C (pure
> geometric/spectroscopic basis, the Goldschmidt pattern), first theory of the group.

---

## 1. Overall goal and boundaries

### 1.1 The claim

Förster resonance energy transfer: the rate is `k_FRET = (1/τ_D)·(R₀/R)⁶`, the efficiency is
`E = R₀⁶/(R₀⁶ + R⁶)`, and the Förster radius obeys `R₀⁶ ∝ κ²·Φ_D·J/n⁴`. The orientation factor
is `κ² = (cosθ_T − 3cosθ_D cosθ_A)²` — with the azimuthal parametrization
`κ² = (sinθ_D·sinθ_A·cosφ − 2·cosθ_D·cosθ_A)²` — bounded by `0 ≤ κ² ≤ 4`, with the isotropic
convention `κ² = 2/3`. **The κ² dependency analysis** (the batch's C-group headline): tabulated
`R₀` values assume the `2/3` convention; the true-geometry `R₀⁶` differs by the factor
`κ²/(2/3) ∈ [0, 6]` — the convention **overestimates without bound in ratio** towards the blind spot
(`κ² → 0`: at `κ² = 0` no transfer happens at any distance while the convention predicts
transfer) and **underestimates** the true `R₀⁶` by at most a factor `6` (at `κ² = 4`).

### 1.2 The model (chosen, not derived)

Point dipoles, the dipole–dipole orientation factor in the azimuthal parametrization (the three
angles `θ_D, θ_A, φ` are *independent* parameters of the model — the spherical-geometry identity
makes this equivalent to the standard three-angle form; registered in LITERATURE), the
sixth-power distance law, and the `R₀⁶` proportionality with a collected positive constant `C`.
Efficiency is formalized **in `R⁶`-space** (`fretEff6 r6 R := r6/(r6 + R^6)`), so no sixth root
ever appears.

### 1.3 Explicit non-goals

* No measure theory: the isotropic average `⟨κ²⟩ = 2/3` is formalized as the **exact average
  over the orthonormal frame** (nine axis-aligned dipole pairs with the separation along an
  axis — a finite ℚ computation), registered as this model's convention; the continuous
  spherical average is a registered non-goal (it needs `MeasureTheory` integration over the
  rotation group, not installed-scope).
* No spectral overlap theory: `J` is a positive parameter.
* No radiative-transfer (trivial) reabsorption channels.

## 2. Conventions and symbols

`θ_D, θ_A` — angles of the donor/acceptor transition dipoles to the separation axis; `φ` — the
azimuthal offset of the two dipoles around that axis; `tauD > 0` donor lifetime; `R > 0`
separation; `r6 > 0` the sixth power of the Förster radius; `C, Φ, J, n` positive parameters.
Namespace `PhotoLean.Forster`; rational layer `PhotoLean.Forster.Rat`.

## 3. Statement authority and inventory

The authority is `probes/Forster-statement-skeleton.lean` (Phase-1 placeholder bodies; sha256 on
the board once compiling). Correction log §3.1 starts empty.

## 4. Statement inventory

Module plan (Phase 2): `Basic.lean` (FO-B), `Criterion.lean` (FO-C), `RatModel.lean` (FO-R),
`Instances.lean` (FO-I).

**FO-B (definitions):**

* FO-B1 `kappaSq (θD θA φ : ℝ) : ℝ :=
  (Real.sin θD * Real.sin θA * Real.cos φ - 2 * Real.cos θD * Real.cos θA) ^ 2` — the
  orientation factor in the azimuthal parametrization.
* FO-B2 `fretRate (tauD r6 R : ℝ) : ℝ := (1 / tauD) * (r6 / R ^ 6)` — the rate, `R⁶`-space form
  of `(1/τ_D)(R₀/R)⁶`.
* FO-B3 `fretEff6 (r6 R : ℝ) : ℝ := r6 / (r6 + R ^ 6)` — the efficiency in `R⁶`-space.
* FO-B4 `fretEff (R0 R : ℝ) : ℝ := 1 / (1 + (R / R0) ^ 6)` — the radius form (for the
  certificate to the textbook form).
* FO-B5 `r0six (C κ² Φ J n : ℝ) : ℝ := C * κ² * Φ * J / n ^ 4` — the Förster radius' sixth
  power.
* FO-B6 `kappaConvention : ℝ := 2 / 3` — the isotropic convention constant.

**FO-C (laws):**

* FO-C1 `kappaSq_nonneg (θD θA φ : ℝ) : 0 ≤ kappaSq θD θA φ` (`sq_nonneg`).
* FO-C2 `kappaSq_le_four (θD θA φ : ℝ) : kappaSq θD θA φ ≤ 4` — the geometric bound. Proof
  route (no eigenvalues, no rotations): with `a := sinθD·sinθA`, `b := 2·cosθD·cosθA`,
  `|a·cosφ − b| ≤ |a|·|cosφ| + |b| ≤ |a| + |b|` (`abs_add`, `abs_mul`, `Real.abs_cos_le_one`);
  then `(|sinθD|·|sinθA| + 2·|cosθD|·|cosθA|)² ≤ (sin²θD + 4·cos²θD)·(sin²θA + cos²θA)`
  (Cauchy–Schwarz on ℝ², discharged by `nlinarith` with the witness term
  `(x₁y₂ − x₂y₁)² ≥ 0`); `sin²θA + cos²θA = 1` (`Real.sin_sq_add_cos_sq`) and
  `sin²θD + 4·cos²θD = 1 + 3·cos²θD ≤ 4` (`Real.cos_sq_le_one`-adjacent). Hence
  `kappaSq ≤ 4`. Then `sq_le_sq`/`abs_le` conversions close it.
* FO-C3 `kappaSq_eq_zero_witness : ∃ θD θA φ, kappaSq θD θA φ = 0` — e.g. `θD = π/2, θA = 0`
  (donor perpendicular, acceptor parallel to the separation); and
  `kappaSq_eq_four_witness : ∃ θD θA φ, kappaSq θD θA φ = 4` — e.g. `θD = θA = 0` (both dipoles
  along the separation). Both witnessed at closed values (`Real.sin_pi_div_two`,
  `Real.sin_zero`, `Real.cos_zero`).
* FO-C4 `fretEff6_eq (h : 0 < R0) (R : ℝ) : fretEff R0 R = fretEff6 (R0 ^ 6) R` — the
  certificate between the radius form and the `R⁶`-space form (field algebra; `(R/R0)^6` to
  `R^6/R0^6` needs `div_pow` and `h.ne'`).
* FO-C5 `fretEff_self (hR0 : 0 < R0) : fretEff R0 R0 = 1 / 2` — the meaning of `R₀`.
* FO-C6 `fretEff6_strictMono_r6 (hR : 0 < R) : StrictMonoOn (fun r6 => fretEff6 r6 R)
  (Set.Ioi 0)` — the efficiency is strictly increasing in `R₀⁶`, hence in `κ²` (FO-C9);
  discharge by `div_lt_div_iff`-style field monotonicity (`a/(a+c)` strictly increasing in
  `a > 0` for `c > 0`).
* FO-C7 (**convention bias, the headline pair**)
  `r0six_ratio (hC : 0 < C) (hΦ : 0 < Φ) (hJ : 0 < J) (hn : 0 < n) (κ² : ℝ) :
  r0six C κ² Φ J n / r0six C (2/3) Φ J n = κ² / (2/3)`;
  `r0six_ratio_mem (hC hΦ hJ hn : 0 < …) (θD θA φ : ℝ) :
  r0six C (kappaSq θD θA φ) Φ J n / r0six C (2/3) Φ J n ∈ Set.Icc (0 : ℝ) 6` — the misestimate
  factor of a tabulated `R₀⁶` lies between `0` and `6` (FO-C1, FO-C2).
* FO-C8 (**the blind spot**) `fret_blind_spot (hC hΦ hJ hn : 0 < …) (hR : 0 < R) :
  fretEff6 (r0six C 0 Φ J n) R = 0 ∧ 0 < fretEff6 (r0six C (2/3) Φ J n) R` — at `κ² = 0` no
  transfer happens at any distance while the convention predicts transfer; the convention's
  silent failure, witnessed.
* FO-C9 `fretEff6_mono_kappa (hC hΦ hJ hn : 0 < …) (hR : 0 < R) {κ₁ κ₂ : ℝ} (h1 : 0 < κ₁)
  (h : κ₁ < κ₂) : fretEff6 (r0six C κ₁ Φ J n) R < fretEff6 (r0six C κ₂ Φ J n) R` — the
  efficiency strictly increases in the orientation factor (the observable's κ² dependency).
* FO-C10 `fretEff_via_lifetime (hkD : 0 < kD) (kF R : ℝ) (hkF : 0 ≤ kF) :
  1 - (1 / (kD + kF)) / (1 / kD) = (kF / kD) / (kF / kD + 1)` and
  `fretEff_via_lifetime' (hkD : 0 < kD) (hR : 0 < R) (r6 : ℝ) :
  1 - (1 / (kD + kD * (r6 / R^6))) / (1 / kD) = fretEff6 r6 R` — the lifetime reading of the
  efficiency (`E = 1 − τ_DA/τ_D`), the QuantumYield/SternVolmer edge anchor.
* FO-C11 `fretEff_at_twoR0 (hR0 : 0 < R0) : fretEff R0 (2 * R0) = 1 / 65` — the sixth-power
  law's steepness, kernel-computed.

**FO-R (rational decision layer):**

* FO-R1 `Rat.fretEff6`, `Rat.r0six`, `Rat.fretRate` over `ℚ` + cast coherence.
* FO-R2 `frameKappa (i j k : Fin 3) : ℚ := ((if i = j then 1 else 0) -
  3 * (if i = k then 1 else 0) * (if j = k then 1 else 0)) ^ 2` — the orientation factor on the
  orthonormal frame (dipoles along axes `i, j`, separation along axis `k`);
  `iso_frame_avg : (∑ i : Fin 3, ∑ j : Fin 3, frameKappa i j 2) / 9 = 2 / 3` — **the `2/3`
  convention, kernel-computed as the exact frame average** (`decide`).
* FO-R3 `Rat` zone rows for the named instances (efficiency verdicts at ℚ, `decide`).

**FO-I (named instances, representative rational models):**

* FO-I1 `cy3cy5Like` (r6 = 1, R = 3/2): E = `1/(1 + (3/2)⁶) = 64/729`… (recompute in the probe;
  the row states the exact rational efficiency).
* FO-I2 `blindSpotGeometry`: the FO-C3 zero witness instantiated (`θD = π/2, θA = 0`) with the
  convention comparison — the dependency-analysis instance.
* FO-I3 `maxGeometry`: the FO-C3 four witness (`θD = θA = 0`) with the factor-`6` verdict.

## 5. Proof routes

FO-C2 is the heavy row of group C: the two-step route of §4 (triangle + ℝ² Cauchy–Schwarz by
`nlinarith` + `Real.sin_sq_add_cos_sq`) avoids eigenvalues and rotations entirely; the API probe
must confirm `Real.abs_cos_le_one` (or `abs_cos_le_one`), `Real.sin_sq_add_cos_sq`,
`sq_le_sq`/`abs_le` and the `nlinarith` certificate shape **before** the skeleton is frozen.
FO-C4/C10: `field_simp` + `ring` with `div_pow`. FO-C11: `norm_num [fretEff]` after `div_pow`
normal forms — calibrate in the probe. If FO-C2 resists the 30-minute budget in Phase 2, the
fallback statement is `kappaSq_le_eight` (the two-step route with the looser CS constant) plus an
escalation note — **never** a silent weakening: the fallback lands only via a plan §3.1 entry
with the failed attempts recorded.

## 6. Sprint order, ownership, dispatch

Sprint FO0 (Phase 1) → FO1 `Basic` → FO2 `Criterion` (FO-C2 first — the riskiest row) →
FO3 `RatModel` → FO4 `Instances`. Owner: prover_d (group C block).

## 7. Acceptance criteria and gate commands

    proofs/scripts/lake build PhotoLean.Forster.Basic   (etc. per module)
    proofs/scripts/check.sh --strict PhotoLean.Forster.Criterion
    proofs/scripts/axioms.sh PhotoLean.Forster.Criterion PhotoLean.Forster.kappaSq_le_four
    python3 theories/BEP/probes/bep-fidelity.py --theory Forster

## 8. Risks and mitigations

* FO-C2 (the bound `4`) is the batch's highest proof risk — the route is pre-derived in §4/§5
  and the fallback is registered in the plan (no silent weakening).
* `div_pow` / `Real.rpow` confusion: the sixth powers are `^ 6` (monoid powers), never `rpow` —
  the skeleton keeps everything in `Monoid.pow` so `norm_num` evaluates numerals.

## 9. Honesty table

| # | Assumed (declared premise) | Proved (theorem) |
|---|---|---|
| 1 | Point-dipole model; azimuthal parametrization of κ² (LITERATURE) | FO-C rows |
| 2 | The `2/3` convention is formalized as the exact frame average (FO-R2), not the continuous one | — |
| 3 | `C, Φ, J, n` are positive parameters (no overlap-integral theory) | — |
| 4 | Named instances are representative rational models | their verdicts |

## 10. Edge candidates (toward the 7 delivered nodes + the 8 batch siblings)

* **QuantumYield — composition (machine target)**: FRET is the added donor channel; FO-C10 is
  the lifetime reading of the QY dilution (one row each way at the definitions).
* **SternVolmer — look-alike (N-class candidate)**: FRET quenching shares the added-channel
  shape; the control variable differs (`R⁶` vs `[Q]`) — register the shape; no theorem
  transfers.
* **Goldschmidt — look-alike (N-class candidate)**: two purely geometric criteria with
  threshold structure (ionic radii vs separation) — no shared scalar; register the shape.
* **Einstein — premise-level dependency**: `J` is defined from normalized spectra whose
  intensities are Einstein-coefficient data; register as a modelling premise (no Lean row).
* **Marcus / Hammond / BEP / Kasha / KashaVavilov / Sabatier / SymmetryFactor / EnergyGapLaw /
  StokesShift / ICvsISC / FluorPhos**: no edge (no surfaces, no ladders, no branching) —
  absence drafts registered.

## 11. Position in the repository

Eighth theory of the batch, first of group C; self-contained (`Mathlib` only); the κ² convention
analysis is registered for the Phase-3 adjudication report alongside D1/D2.
