/-
PhotoLean.Forster.Basic — milestone FO1, the description layer.

The theory: Förster resonance energy transfer (FRET) and the κ² orientation-factor convention
(plan `theories/Forster/plan.md`, §1.1 and §4).

FRET practice reads a rate `k_FRET = (1/τ_D)·(R₀/R)⁶` and an efficiency `E = R₀⁶/(R₀⁶ + R⁶)` off
a donor–acceptor pair, with the Förster radius obeying `R₀⁶ ∝ κ²·Φ_D·J/n⁴`. This module fixes the
model: the orientation factor in the **azimuthal parametrization**
`κ² = (sinθ_D·sinθ_A·cosφ − 2·cosθ_D·cosθ_A)²` (the spherical-geometry identity
`cosθ_T = cosθ_D·cosθ_A + sinθ_D·sinθ_A·cosφ` substituted into `κ² = (cosθ_T − 3cosθ_D·cosθ_A)²`,
LITERATURE S1), the rate and the efficiency in `R⁶`-space (`fretRate`, `fretEff6`), the textbook
radius form kept for the FO-C4 certificate (`fretEff`), the sixth power of the Förster radius
with its collected positive constant `C` (`r0six`), and the isotropic convention constant `2/3`
(`kappaConvention`).

Honest scope, stated up front:
* everything is algebraic over `ℝ` with totalized division; every positivity premise is an
  explicit hypothesis of the law rows (`Criterion`), never a hidden side condition of a
  definition (engine rule 3);
* `C, Φ, J, n` are free positive parameters — no spectral-overlap theory and no internal
  structure of `C` is derived (plan §1.3);
* the `2/3` convention is formalized as the **exact average over the orthonormal frame**
  (FO-R2 in `RatModel`), not as a continuous spherical average — the latter needs integration
  over the rotation group and is a registered non-goal (plan §1.3);
* the three angles `θ_D, θ_A, φ` are independent parameters of the model; the spherical-geometry
  identity making the azimuthal form equivalent to the standard three-angle form is registered
  in LITERATURE, not re-derived here.

Statement authority: `theories/Forster/probes/Forster-statement-skeleton.lean` § FO-B; every
signature below is identical to its authority row. There is no unproved placeholder and no
custom axiomatic declaration anywhere in this file. Acceptance:
`proofs/scripts/lake build PhotoLean.Forster.Basic` (exit 0);
`proofs/scripts/check.sh --strict`; fidelity
`python3 theories/BEP/probes/bep-fidelity.py --theory Forster`.
-/
import Mathlib

set_option autoImplicit false

namespace PhotoLean

namespace Forster

/-! ## FO-B — description layer -/

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

end Forster

end PhotoLean
