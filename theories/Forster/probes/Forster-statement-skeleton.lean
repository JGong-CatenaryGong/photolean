/-
Forster-statement-skeleton.lean — the STATEMENT AUTHORITY of the Forster theory (Förster
resonance energy transfer and the κ² orientation-factor convention).

Statement-first (iron rule 2): every declaration below is the agreed statement verbatim from
`theories/Forster/plan.md` §4; theorem bodies are placeholders on purpose (Phase 1). This file
must compile at 0 error
(`proofs/scripts/lake env lean theories/Forster/probes/Forster-statement-skeleton.lean`)
BEFORE any proof work starts; delivery replaces the bodies verbatim and
`python3 theories/BEP/probes/bep-fidelity.py --theory Forster` compares the delivered signatures
to this file word for word.

Plan: `theories/Forster/plan.md`. Milestones: FO1 (Basic), FO2 (Criterion), FO3 (RatModel),
FO4 (Instances). Probe-time corrections recorded here and in the plan §3.1 log:
1. `frameKappa` is ℤ-valued (every axis-aligned pair gives 0, 1 or 4); the isotropic-average
   row is two-step (`decide` the ℤ sum, then `norm_num` the ℚ division) — `decide` does not
   reduce ℚ division (measured boundary, cf. `PhotoLean.Marcus.RatModel`), and `norm_num` with
   `Fin.ext_iff` overflows the recursion depth (both measured 2026-09-22 in
   `Forster-api-probe.lean` and `.lake/tmp` test probes).
2. FO-C10b (the lifetime reading of the efficiency) carries the load-bearing premise
   `0 ≤ r6`: the unpremised form is FALSE under totalized division at `r6 = −R⁶` — a
   probe-proved counterexample, see `Forster-api-probe.lean` (the example proves `¬ ∀ r6, …`).
3. FO-I1's exact rational efficiency is `64/793`, not the plan's printed `64/729`
   (`1/(1+(3/2)⁶) = 64/(64+729)`; probe-recomputed).

This probe lives outside the strict scan range; placeholder bodies are Phase-1 registration,
each recorded on the board `theories/Forster/TASKS.md`.
-/
import Mathlib

set_option autoImplicit false

namespace PhotoLean

namespace Forster

/-! ## FO1 — description layer (`PhotoLean/Forster/Basic.lean`) -/

/-- Plan §4, FO-B1. The orientation factor in the azimuthal parametrization
(LITERATURE S1: the spherical-geometry identity `cosθ_T = cosθ_D·cosθ_A +
sinθ_D·sinθ_A·cosφ` substituted into `κ² = (cosθ_T − 3cosθ_D·cosθ_A)²`). -/
noncomputable def kappaSq (θD θA φ : ℝ) : ℝ :=
  (Real.sin θD * Real.sin θA * Real.cos φ - 2 * Real.cos θD * Real.cos θA) ^ 2

/-- Plan §4, FO-B2. The FRET rate in `R⁶`-space: `(1/τ_D)·(R₀⁶/R⁶)`. -/
noncomputable def fretRate (tauD r6 R : ℝ) : ℝ := (1 / tauD) * (r6 / R ^ 6)

/-- Plan §4, FO-B3. The transfer efficiency in `R⁶`-space: `R₀⁶/(R₀⁶ + R⁶)`. -/
noncomputable def fretEff6 (r6 R : ℝ) : ℝ := r6 / (r6 + R ^ 6)

/-- Plan §4, FO-B4. The textbook radius form `1/(1 + (R/R₀)⁶)` (kept for the FO-C4
certificate). -/
noncomputable def fretEff (R0 R : ℝ) : ℝ := 1 / (1 + (R / R0) ^ 6)

/-- Plan §4, FO-B5. The Förster radius' sixth power: `C·κ²·Φ_D·J/n⁴` with `C` the collected
positive constant (its internal structure is a registered non-goal, plan §1.3). -/
noncomputable def r0six (C kappasq Φ J n : ℝ) : ℝ := C * kappasq * Φ * J / n ^ 4

/-- Plan §4, FO-B6. The isotropic convention constant `2/3`. -/
noncomputable def kappaConvention : ℝ := 2 / 3

/-! ## FO2 — law layer (`PhotoLean/Forster/Criterion.lean`) -/

/-- Plan §4, FO-C1. Nonnegativity of the orientation factor. Route: `sq_nonneg`. -/
theorem kappaSq_nonneg (θD θA φ : ℝ) : 0 ≤ kappaSq θD θA φ := by
  sorry

/-- Plan §4, FO-C2. **The geometric bound** `κ² ≤ 4`. Route (pre-validated in
`Forster-api-probe.lean`): with `a := sinθD·sinθA`, `b := 2·cosθD·cosθA`, the triangle
inequality and `|cosφ| ≤ 1` give `|a·cosφ − b| ≤ |a| + |b|`; Cauchy–Schwarz on ℝ² (closed by
`nlinarith [sq_nonneg (x₁·y₂ − x₂·y₁)]`) bounds `(|sinθD|·|sinθA| + 2|cosθD||cosθA|)²` by
`(sin²θD + 4cos²θD)·(sin²θA + cos²θA) = 1 + 3cos²θD ≤ 4` (`Real.sin_sq_add_cos_sq`,
`Real.cos_sq_le_one`); `sq_le_sq` + `abs_le` finish. -/
theorem kappaSq_le_four (θD θA φ : ℝ) : kappaSq θD θA φ ≤ 4 := by
  sorry

/-- Plan §4, FO-C3 (zero witness). The blind-spot geometry exists: donor perpendicular to the
separation, acceptor along it. Route: `simp [kappaSq, Real.sin_pi_div_two, Real.sin_zero,
Real.cos_zero, Real.cos_pi_div_two]`-style normalization (probed). -/
theorem kappaSq_eq_zero_witness : ∃ θD θA φ : ℝ, kappaSq θD θA φ = 0 := by
  sorry

/-- Plan §4, FO-C3 (maximal witness). Both dipoles along the separation give `κ² = 4`. -/
theorem kappaSq_eq_four_witness : ∃ θD θA φ : ℝ, kappaSq θD θA φ = 4 := by
  sorry

/-- Plan §4, FO-C4. The certificate between the radius form and the `R⁶`-space form. Route:
`div_pow`, `field_simp` (probed; `field_simp` closes the normalized goal). -/
theorem fretEff_eq (R0 R : ℝ) (hR0 : 0 < R0) : fretEff R0 R = fretEff6 (R0 ^ 6) R := by
  sorry

/-- Plan §4, FO-C5. The meaning of `R₀`: efficiency `1/2` at `R = R₀`. Route: FO-C4 +
`norm_num`. -/
theorem fretEff_self (R0 : ℝ) (hR0 : 0 < R0) : fretEff R0 R0 = 1 / 2 := by
  sorry

/-- Plan §4, FO-C6. The efficiency is strictly increasing in `R₀⁶` at any positive separation.
Route (probed): `div_lt_div_iff₀` + `nlinarith [mul_lt_mul_of_pos_right ...]`. -/
theorem fretEff6_strictMono_r6 (R : ℝ) (hR : 0 < R) :
    StrictMonoOn (fun r6 : ℝ => fretEff6 r6 R) (Set.Ioi 0) := by
  sorry

/-- Plan §4, FO-C7 (the convention-bias ratio). The tabulated-`R₀⁶` misestimate factor is
exactly `κ²/(2/3)`. Route (probed): `field_simp` + `ring` with the positivity side-conditions.
-/
theorem r0six_ratio {C Φ J n : ℝ} (hC : 0 < C) (hΦ : 0 < Φ) (hJ : 0 < J) (hn : 0 < n)
    (kappasq : ℝ) : r0six C kappasq Φ J n / r0six C (2 / 3) Φ J n = kappasq / (2 / 3) := by
  sorry

/-- Plan §4, FO-C7 (the misestimate band). The ratio lies in `[0, 6]` — the convention
underestimates the true `R₀⁶` by at most a factor `6` (at `κ² = 4`) and overestimates without
bound in ratio towards the blind spot (`κ² → 0`). Route: FO-C1/FO-C2 + `r0six_ratio` +
positivity. -/
theorem r0six_ratio_mem {C Φ J n : ℝ} (hC : 0 < C) (hΦ : 0 < Φ) (hJ : 0 < J) (hn : 0 < n)
    (θD θA φ : ℝ) :
    r0six C (kappaSq θD θA φ) Φ J n / r0six C (2 / 3) Φ J n ∈ Set.Icc (0 : ℝ) 6 := by
  sorry

/-- Plan §4, FO-C8 (**the blind spot**). At `κ² = 0` no transfer happens at any separation
while the `2/3` convention predicts transfer — the convention's silent failure, witnessed.
Route (probed): `zero_div` and `div_pos`. -/
theorem fret_blind_spot {C Φ J n : ℝ} (hC : 0 < C) (hΦ : 0 < Φ) (hJ : 0 < J) (hn : 0 < n)
    (R : ℝ) :
    fretEff6 (r0six C 0 Φ J n) R = 0 ∧ 0 < fretEff6 (r0six C (2 / 3) Φ J n) R := by
  sorry

/-- Plan §4, FO-C9. The observable's κ² dependency: the efficiency strictly increases in the
orientation factor. Route: `r0six` is strictly monotone in `κ²` (linear, `C·Φ·J/n⁴ > 0`), then
FO-C6. -/
theorem fretEff6_mono_kappa {C Φ J n : ℝ} (hC : 0 < C) (hΦ : 0 < Φ) (hJ : 0 < J) (hn : 0 < n)
    (R : ℝ) (hR : 0 < R) {κ₁ κ₂ : ℝ} (h1 : 0 ≤ κ₁) (h : κ₁ < κ₂) :
    fretEff6 (r0six C κ₁ Φ J n) R < fretEff6 (r0six C κ₂ Φ J n) R := by
  sorry

/-- Plan §4, FO-C10 (first lifetime form). Route (probed): `field_simp`, `ring_nf`, then the
trivial clearance side condition `Or.inl trivial`. -/
theorem fretEff_via_lifetime {kD kF : ℝ} (hkD : 0 < kD) (hkF : 0 ≤ kF) :
    1 - (1 / (kD + kF)) / (1 / kD) = (kF / kD) / (kF / kD + 1) := by
  sorry

/-- Plan §4, FO-C10b (second lifetime form — carries the probe-mandated premise `0 ≤ r6`; the
unpremised form is false at `r6 = −R⁶` under totalized division, counterexample probe-proved in
`Forster-api-probe.lean`). Route: `field_simp` + `ring`. -/
theorem fretEff_via_lifetime' {kD r6 R : ℝ} (hkD : 0 < kD) (hR : 0 < R) (hr6 : 0 ≤ r6) :
    1 - (1 / (kD + kD * (r6 / R ^ 6))) / (1 / kD) = fretEff6 r6 R := by
  sorry

/-- Plan §4, FO-C11. The sixth-power law's steepness, kernel-computed. Route (probed):
`div_pow`, `field_simp`, `norm_num`. -/
theorem fretEff_at_twoR0 (R0 : ℝ) (hR0 : 0 < R0) : fretEff R0 (2 * R0) = 1 / 65 := by
  sorry

/-! ## FO3 — rational decision layer (`PhotoLean/Forster/RatModel.lean`) -/

namespace Rat

/-- Plan §4, FO-R1 (ℚ twin). -/
def fretEff6 (r6 R : ℚ) : ℚ := r6 / (r6 + R ^ 6)

/-- Plan §4, FO-R1 (ℚ twin). -/
def r0six (C kappasq Φ J n : ℚ) : ℚ := C * kappasq * Φ * J / n ^ 4

/-- Plan §4, FO-R1 (ℚ twin). -/
def fretRate (tauD r6 R : ℚ) : ℚ := (1 / tauD) * (r6 / R ^ 6)

/-- Plan §4, FO-R1. Cast coherence for `fretEff6`. Route: `Rat.cast_div` / `Rat.cast_add` /
`Rat.cast_pow` (names confirmed in the api probe). -/
theorem fretEff6_cast (r6 R : ℚ) :
    ((fretEff6 r6 R : ℚ) : ℝ) = Forster.fretEff6 (r6 : ℝ) (R : ℝ) := by
  sorry

/-- Plan §4, FO-R2 (probe-corrected shape). The orientation factor on the orthonormal frame —
**integer-valued** (every axis-aligned pair gives `0`, `1` or `4`), so the kernel decides the
sum over ℤ. -/
def frameKappa (i j k : Fin 3) : ℤ :=
  ((if i = j then 1 else 0) - 3 * (if i = k then 1 else 0) * (if j = k then 1 else 0)) ^ 2

/-- Plan §4, FO-R2 (first step). The nine-pair frame sum, kernel-decided over ℤ. Route:
`decide` (probed green). -/
theorem frame_sum_eq_six : (∑ i : Fin 3, ∑ j : Fin 3, frameKappa i j 2) = 6 := by
  sorry

/-- Plan §4, FO-R2 (**the `2/3` convention**). The isotropic convention is exactly the frame
average: `(Σ frameKappa)/9 = 2/3`. Route: `frame_sum_eq_six` + cast + `norm_num` (probed). -/
theorem iso_frame_avg :
    ((∑ i : Fin 3, ∑ j : Fin 3, frameKappa i j 2 : ℤ) : ℚ) / 9 = 2 / 3 := by
  sorry

/-- Plan §4, FO-R3. The blind-spot comparison at the decision layer: convention-positive,
truth-zero. Route: `norm_num [r0six, fretEff6]` (probed). -/
theorem rat_blind_spot :
    fretEff6 (r0six 1 0 1 1 1) 1 = 0 ∧ 0 < fretEff6 (r0six 1 (2 / 3) 1 1 1) 1 := by
  sorry

/-- Plan §4, FO-R3. The maximal-bias ratio at the decision layer. Route: `norm_num [r0six]`
(probed). -/
theorem rat_max_bias : r0six 1 4 1 1 1 / r0six 1 (2 / 3) 1 1 1 = 6 := by
  sorry

end Rat

/-! ## FO4 — named instances (`PhotoLean/Forster/Instances.lean`) -/

/-- Plan §4, FO-I1. A Cy3–Cy5-like representative pair: `r6 = 1`, `R = 3/2` (representative
rational model, not fitted — LITERATURE.md). The exact efficiency is `64/793`
(probe-recomputed; the plan's first printing `64/729` was the reciprocal-shaped value). -/
theorem cy3cy5Like_verdict :
    fretEff6 (1 : ℝ) (3 / 2) = 64 / 793 ∧ Rat.fretEff6 1 (3 / 2) = 64 / 793 := by
  sorry

/-- Plan §4, FO-I2. The blind-spot geometry instance: `κ² = 0` at `θD = π/2, θA = 0` (any `φ`),
with the convention comparison. Route: FO-C3's witness normalization + FO-C8. -/
theorem blindSpotGeometry_verdict :
    kappaSq (Real.pi / 2) 0 0 = 0 ∧
      fretEff6 (r0six 1 (kappaSq (Real.pi / 2) 0 0) 1 1 1) 1
        < fretEff6 (r0six 1 (2 / 3) 1 1 1) 1 := by
  sorry

/-- Plan §4, FO-I3. The maximal-κ² geometry instance with the factor-`6` verdict. -/
theorem maxGeometry_verdict :
    kappaSq 0 0 0 = 4 ∧ Rat.r0six 1 4 1 1 1 / Rat.r0six 1 (2 / 3) 1 1 1 = 6 := by
  sorry

end Forster

end PhotoLean
