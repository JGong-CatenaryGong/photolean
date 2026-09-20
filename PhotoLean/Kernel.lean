/-
PhotoLean.Kernel — the shared kernel of the two-parabola family.

Three phenomenological theories are delivered in this repository: the Marcus inverted region,
the Hammond postulate and the Bell–Evans–Polanyi principle. Each of them describes an elementary
reaction step through the same classical two-parabola model, and each of them had grown its own
copy of the shared objects. This module carries the single definitions of that family: the
reactant and product potential-energy surfaces, the forward barrier, the reverse barrier, the
transition-state coordinate and the transfer (Brønsted/Leffler) coefficient.

The extraction is purely additive. Every theory keeps its own copy untouched: nothing under
`PhotoLean/Marcus`, `PhotoLean/Hammond` or `PhotoLean/BEP` is imported here (this module is the
bottom of the dependency graph and depends on `Mathlib` only), nothing there is modified, and no
delivered statement changes. The regression certificates that pin each theory's own copy to the
kernel definition definitionally live in `PhotoLean/Relations.lean`.

Statement-first: the definitions and the two internal-consistency theorems below are the agreed
statements verbatim. There is no unproved placeholder and no custom axiomatic declaration
anywhere in this file.

Scope of the two theorems, stated honestly. `reverseBarrier_eq_barrier_neg` is an algebraic
identity valid for every `lam`; `transfer_eq_tsCoord` is stated for `lam ≠ 0` only, because at
the degenerate curvature `lam = 0` the two totalised divisions differ — that premise is explicit
in the statement rather than hidden in a definition.
-/
import Mathlib

namespace PhotoLean.Kernel

/-! ## Two-parabola potential-energy surfaces -/

/-- Reactant potential-energy surface: minimum at `q = 0`, curvature `2 * lam`. -/
noncomputable def reactantSurface (lam q : ℝ) : ℝ := lam * q ^ 2

/-- Product potential-energy surface: minimum at `q = 1`, same curvature, offset by the
reaction energy `dG = ΔG°`. -/
noncomputable def productSurface (lam dG q : ℝ) : ℝ := lam * (q - 1) ^ 2 + dG

/-! ## Barriers and transition-state coordinate -/

/-- Forward barrier of the equal-curvature two-parabola model, in the driving-force
convention `x = -ΔG°`: the reactant well up to the crossing point. -/
noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- Reverse barrier of the same step: the product well up to the crossing point. -/
noncomputable def reverseBarrier (lam x : ℝ) : ℝ := (lam + x) ^ 2 / (4 * lam)

/-- Transition-state coordinate on the reaction coordinate. -/
noncomputable def tsCoord (lam x : ℝ) : ℝ := (lam - x) / (2 * lam)

/-- Transfer (Brønsted/Leffler) coefficient of the forward direction, in linear-response
form. -/
noncomputable def transfer (lam x : ℝ) : ℝ := 1 / 2 - x / (2 * lam)

/-! ## Internal consistency of the kernel -/

/-- The reverse barrier is the forward barrier of the reversed step. -/
theorem reverseBarrier_eq_barrier_neg (lam x : ℝ) : reverseBarrier lam x = barrier lam (-x) := by
  unfold reverseBarrier barrier
  ring

/-- The two presentations of the transition-state coefficient agree away from the degenerate
curvature `lam = 0`, where the two totalised divisions differ. -/
theorem transfer_eq_tsCoord {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    transfer lam x = tsCoord lam x := by
  unfold transfer tsCoord
  field_simp

end PhotoLean.Kernel
