/-
PhotoLean.Forster.Instances — milestone FO4, the named instances.

The theory: Förster resonance energy transfer and the κ² convention dependency analysis (plan
`theories/Forster/plan.md`, §4 FO-I). This module evaluates the law layer at named representative
models and states their verdicts. The instances are **representative rational models, not fitted
data** (plan §9, honesty table row 4): the Cy3–Cy5 pair at `r6 = 1`, `R = 3/2` is chosen so the
kernel can compute an exact efficiency, and the two geometry instances instantiate the FO-C3
witnesses of the orientation factor.

The batch headline lives in `blindSpotGeometry_verdict` and `maxGeometry_verdict`: the tabulated
`R₀⁶` (under the isotropic `2/3` convention) misestimates the true sixth power by the factor
`κ²/(2/3)`, which runs from `0` (donor perpendicular, acceptor parallel — the blind spot, where
no transfer happens at any distance while the convention predicts transfer) to `6` (both dipoles
along the separation). The FO-I1 exact value `64/793` is the probe-recomputed one — the plan's
first printing `64/729` was the reciprocal-shaped value (statement authority §3.1 item 3).

Statement authority: `theories/Forster/probes/Forster-statement-skeleton.lean` § FO-I; every
signature below is identical to its authority row. There is no unproved placeholder and no custom
axiomatic declaration anywhere in this file. Acceptance:
`proofs/scripts/lake build PhotoLean.Forster.Instances` (exit 0);
`proofs/scripts/check.sh --strict`;
`python3 theories/BEP/probes/bep-fidelity.py --theory Forster`.
-/
import PhotoLean.Forster.RatModel

set_option autoImplicit false

namespace PhotoLean

namespace Forster

/-! ## FO-I — named instances -/

/-- Plan §4, FO-I1. A Cy3–Cy5-like representative pair: `r6 = 1`, `R = 3/2` (representative
rational model, not fitted — LITERATURE.md). The exact efficiency is `64/793`
(probe-recomputed; the plan's first printing `64/729` was the reciprocal-shaped value). -/
theorem cy3cy5Like_verdict :
    fretEff6 (1 : ℝ) (3 / 2) = 64 / 793 ∧ Rat.fretEff6 1 (3 / 2) = 64 / 793 := by
  constructor
  · norm_num [fretEff6]
  · norm_num [Rat.fretEff6]

/-- Plan §4, FO-I2. The blind-spot geometry instance: `κ² = 0` at `θD = π/2, θA = 0` (any `φ`),
with the convention comparison. Route: FO-C3's witness normalization + FO-C8. -/
theorem blindSpotGeometry_verdict :
    kappaSq (Real.pi / 2) 0 0 = 0 ∧
      fretEff6 (r0six 1 (kappaSq (Real.pi / 2) 0 0) 1 1 1) 1
        < fretEff6 (r0six 1 (2 / 3) 1 1 1) 1 := by
  have hk : kappaSq (Real.pi / 2) 0 0 = 0 := by
    rw [kappaSq, Real.sin_pi_div_two, Real.sin_zero, Real.cos_zero, Real.cos_pi_div_two]
    norm_num
  constructor
  · exact hk
  · rw [hk]
    rw [show r0six 1 0 1 1 1 = 0 by rw [r0six]; ring]
    rw [show fretEff6 (0 : ℝ) 1 = 0 by rw [fretEff6]; norm_num]
    rw [fretEff6, r0six]
    norm_num

/-- Plan §4, FO-I3. The maximal-κ² geometry instance with the factor-`6` verdict. -/
theorem maxGeometry_verdict :
    kappaSq 0 0 0 = 4 ∧ Rat.r0six 1 4 1 1 1 / Rat.r0six 1 (2 / 3) 1 1 1 = 6 := by
  constructor
  · rw [kappaSq, Real.sin_zero, Real.cos_zero]
    norm_num
  · norm_num [Rat.r0six]

end Forster

end PhotoLean
