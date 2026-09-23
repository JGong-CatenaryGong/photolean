/-
PhotoLean.StokesShift.Basic — milestone SS-B, the description layer.

The theory: the **Stokes shift rule** of the equal-curvature two-parabola model
(plan `theories/StokesShift/plan.md`, photophysics batch 2026-09-22, group B — the second
theory of the group).

The kernel's two surfaces (`PhotoLean.Kernel.reactantSurface` /
`PhotoLean.Kernel.productSurface`) read optically: `q = 0` is the ground-state minimum
geometry, `q = 1` the excited-state minimum geometry, and the transitions are vertical
(Franck–Condon) at those minima. The vertical absorption energy from the ground minimum is
`lam + e00`, the vertical emission energy from the excited minimum is `e00 - lam`, and the
Stokes shift is exactly `2 * lam`, independent of the 0-0 energy — the headline law of the
law layer (milestone SS-C).

This theory carries **its own copies** of the two surfaces, pinned to the shared kernel by
the definitional certificates `cert_s0Surface` / `cert_s1Surface` (hard constraint 1: a
theory that describes the shared model carries the pointer as a theorem rather than as a
redefinition). No division appears anywhere in this layer — every row is pure polynomial
algebra over `ℝ`.

Honest scope, stated up front:
* everything here is a statement **inside the declared model** (single-mode,
  equal-curvature parabolas, vertical transitions at the minima); it is not a claim about a
  measured band position;
* `lam` collects all reorganization (inner + outer) — registered in the plan's honesty
  table, not derived;
* no vibronic structure and no lineshape widths: the rows are about band maxima only.

Statement authority: `theories/StokesShift/probes/StokesShift-statement-skeleton.lean`
§ SS-B; every signature below is identical to its authority row. There is no unproved
placeholder and no custom axiomatic declaration anywhere in this file. The `#print axioms`
gate of the two certificates below lists at most `propext`, `Classical.choice`,
`Quot.sound`.

Acceptance (contract `proofs/ENGINE.yml`):
  proofs/scripts/lake build PhotoLean.StokesShift.Basic
  proofs/scripts/check.sh --strict PhotoLean.StokesShift.Basic
  proofs/scripts/axioms.sh PhotoLean.StokesShift.Basic PhotoLean.StokesShift.cert_s0Surface
-/
import Mathlib
import PhotoLean.Kernel

set_option autoImplicit false

namespace PhotoLean

namespace StokesShift

/-! ## SS-B — description layer -/

/-- Ground-state potential-energy surface with reorganization energy `lam`: minimum at `q = 0`.
Plan section 4, row SS-B1. This theory's own copy, pinned to `PhotoLean.Kernel` by
`cert_s0Surface` (hard constraint 1). -/
noncomputable def s0Surface (lam q : ℝ) : ℝ := lam * q ^ 2

/-- Kernel certificate: the ground surface IS `PhotoLean.Kernel.reactantSurface`.
Plan section 4, row SS-B1. Proof route (plan §4): `rfl` (definitional copy). -/
theorem cert_s0Surface (lam q : ℝ) :
    s0Surface lam q = PhotoLean.Kernel.reactantSurface lam q :=
  rfl

/-- Excited-state potential-energy surface with reorganization energy `lam` and 0-0 energy
`e00`: minimum at `q = 1`, offset by `e00`. Plan section 4, row SS-B2. This theory's own copy,
pinned to `PhotoLean.Kernel` by `cert_s1Surface` (hard constraint 1). -/
noncomputable def s1Surface (lam e00 q : ℝ) : ℝ := lam * (q - 1) ^ 2 + e00

/-- Kernel certificate: the excited surface IS `PhotoLean.Kernel.productSurface`.
Plan section 4, row SS-B2. Proof route (plan §4): `rfl` (definitional copy). -/
theorem cert_s1Surface (lam e00 q : ℝ) :
    s1Surface lam e00 q = PhotoLean.Kernel.productSurface lam e00 q :=
  rfl

/-- Vertical (Franck–Condon) absorption energy from the ground minimum `q = 0`.
Plan section 4, row SS-B3. -/
noncomputable def absEnergy (lam e00 : ℝ) : ℝ := s1Surface lam e00 0 - s0Surface lam 0

/-- Vertical (Franck–Condon) emission energy from the excited minimum `q = 1`.
Plan section 4, row SS-B4. -/
noncomputable def emEnergy (lam e00 : ℝ) : ℝ := s1Surface lam e00 1 - s0Surface lam 1

/-- The Stokes shift: absorption energy minus emission energy. Plan section 4, row SS-B5. -/
noncomputable def stokesShift (lam e00 : ℝ) : ℝ := absEnergy lam e00 - emEnergy lam e00

end StokesShift

end PhotoLean
