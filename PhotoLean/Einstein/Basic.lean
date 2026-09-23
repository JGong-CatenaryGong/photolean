/-
PhotoLean.Einstein.Basic — milestone EB-B, the definition layer.

The theory: the **Einstein A/B coefficients of one electronic transition and the
oscillator-strength equivalence chain** (plan `theories/Einstein/plan.md` §1.1, §4). One transition
between levels of degeneracies `g₁, g₂ > 0`; the radiation-density factor `8πhν³/c³` kept explicit
(with `Real.pi`); the oscillator-strength and Strickler–Berg proportionality constants collected as
single positive parameters `Cf`, `Ci`.

This module carries the six EB-B rows — `radFactor`, `aOfB`, `b12OfB21`, `fOfA`, `aOfInt`, `tauR` —
the vocabulary the equivalence chain is stated with. The content of the theory is invertibility, and
it lives in the sibling module `PhotoLean/Einstein/Criterion.lean` (EB-C); this layer declares only
the maps. Division is totalized (`tauR A = 1 / A` has no side condition); the physical positivity
premises travel as explicit hypotheses of the EB-C theorems, never inside a definition (engine
rule 3).

Honest scope, stated up front (plan §9):
* `Cf` and `Ci` are *collected* per-transition constants; their internal structure is a registered
  non-goal (plan §1.3). They are never presented as universal constants of nature;
* no blackbody radiation theory is formalized here — the radiation-density factor is an explicit
  parameter with its `8πhν³/c³` form, not a derivation;
* no lineshape functions: integrated intensities only.

Statement authority: `theories/Einstein/probes/Einstein-statement-skeleton.lean` § EB-B; every
signature below is identical to its authority row (checked by
`python3 theories/BEP/probes/bep-fidelity.py --theory Einstein`). There is no unproved placeholder
and no custom axiomatic declaration anywhere in this file.

Acceptance:
    proofs/scripts/lake build PhotoLean.Einstein.Basic
    proofs/scripts/check.sh --strict PhotoLean.Einstein.Basic
-/
import Mathlib

set_option autoImplicit false

namespace PhotoLean

namespace Einstein

/-! ## EB-B — definitions -/

/-- The radiation-density factor `8πhν³/c³` of one transition, kept explicit (with `Real.pi`).
Plan section 4, row EB-B1. -/
noncomputable def radFactor (h c ν : ℝ) : ℝ := 8 * Real.pi * h * ν ^ 3 / c ^ 3

/-- The A coefficient from B and the radiation factor: `A₂₁ = K · B₂₁` (at the physical instance
`K = radFactor h c ν`). Plan section 4, row EB-B2. -/
noncomputable def aOfB (K B21 : ℝ) : ℝ := K * B21

/-- Detailed balance: the absorption coefficient from the stimulated-emission coefficient,
`B₁₂ = (g₂/g₁)·B₂₁`. Plan section 4, row EB-B3. -/
noncomputable def b12OfB21 (g1 g2 B21 : ℝ) : ℝ := (g2 / g1) * B21

/-- The oscillator strength from A with the degeneracy ratio, `Cf` the collected positive constant
(its internal structure is a registered non-goal — plan §1.3). Plan section 4, row EB-B4. -/
noncomputable def fOfA (Cf g1 g2 A : ℝ) : ℝ := Cf * (g2 / g1) * A

/-- The Strickler–Berg form: the radiative rate from the integrated absorption, `Ci` the collected
positive constant (internal structure a registered non-goal — plan §1.3). Plan section 4, row
EB-B5. -/
noncomputable def aOfInt (Ci I : ℝ) : ℝ := Ci * I

/-- The radiative lifetime `τ = 1/A` (totalized division). Plan section 4, row EB-B6. -/
noncomputable def tauR (A : ℝ) : ℝ := 1 / A

end Einstein

end PhotoLean
