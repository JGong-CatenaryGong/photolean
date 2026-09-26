/-
PhotoLean.SymmetryFactor.Basic — milestone F1, the description layer.

The theory: the **symmetry-factor adjudication** of the unequal-curvature two-parabola model
(plan `theories/SymmetryFactor/plan.md`).

The equal-curvature two-parabola model of `PhotoLean.Kernel` (curvature `2*lam` on BOTH surfaces)
is the picture every textbook draws, and in it the thermoneutral crossing coordinate is `1/2` —
which is exactly why the electrochemical working value "the transfer coefficient is 0.5" survives:
it is a theorem of the symmetric picture. This theory generalizes the two surfaces to **unequal**
curvature parameters `kr` (reactant well at `q = 0`) and `kp` (product well at `q = 1`), defines
the thermoneutral crossing coordinate `tsCoordZero` in closed form, and states the β = 1/2 reading
(`BetaHalfReading`) as a claim about it. The adjudication (F2) is the sharp equivalence
`BetaHalfReading kr kp ↔ kr = kp`: the conflated reading holds **exactly** in the equal-curvature
regime, and the kernel-checked witnesses `(1,4) ↦ 2/3`, `(4,1) ↦ 1/3` refute it off that regime.

Honest scope, stated up front:
* everything here is a statement **inside the declared model** (two parabolas, classical crossing
  point, thermoneutrality `x = 0`); it is not a claim about measured electrode kinetics;
* the *kinetic* reading of the transfer coefficient (a derivative of the barrier in the driving
  force) is deliberately out of scope — the same documented-negative discipline as Kasha's K4b
  (plan §13); the structural (crossing-coordinate) reading is what the Leffler/Hammond tradition
  identifies with the observable coefficient, and in the equal-curvature limit that identification
  is the delivered equivalence E1 (`BEP.transfer_eq_tsCoord_bridge`);
* the driving-force convention is the repository's (`x = -ΔG°`); this milestone fixes `x = 0`.

Statement authority: `theories/SymmetryFactor/probes/SymmetryFactor-statement-skeleton.lean` § F1;
every signature below is identical to its authority row. There is no unproved placeholder and no
custom axiomatic declaration anywhere in this file. The `#print axioms` gate of every theorem
below lists at most `propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib

set_option autoImplicit false

namespace PhotoLean

namespace SymmetryFactor

/-! ## F1 — description layer -/

/-- Reactant potential-energy surface with curvature parameter `kr`: minimum at `q = 0`.
The equal-curvature kernel (`PhotoLean.Kernel.reactantSurface`) is the `kr = lam` reading. -/
noncomputable def asymReactantSurface (kr q : ℝ) : ℝ := kr * q ^ 2

/-- Product potential-energy surface with curvature parameter `kp`: minimum at `q = 1`, offset by
the reaction energy `dG = ΔG°`. -/
noncomputable def asymProductSurface (kp dG q : ℝ) : ℝ := kp * (q - 1) ^ 2 + dG

/-- The thermoneutral crossing: at `x = -ΔG° = 0` the two surfaces meet. -/
def CrossesAtThermoneutral (kr kp q : ℝ) : Prop :=
  asymReactantSurface kr q = asymProductSurface kp 0 q

/-- The structural transfer coefficient at thermoneutrality: the crossing coordinate of the
unequal-curvature two-parabola model, in closed form. At `kr = kp = lam` this is
`Kernel.tsCoord lam 0 = 1/2` (the tie-back certificates of F2). -/
noncomputable def tsCoordZero (kr kp : ℝ) : ℝ := Real.sqrt kp / (Real.sqrt kr + Real.sqrt kp)

/-- The β = 1/2 symmetry-factor reading, applied to this step: the working value the
electrochemical literature "usually takes" (LITERATURE S1) — as a claim about the structural
transfer coefficient of the model. -/
def BetaHalfReading (kr kp : ℝ) : Prop := tsCoordZero kr kp = 1 / 2

/-- The crossing predicate unfolds to the plain algebraic form (definitional unfolding row;
`asymProductSurface kp 0 q` carries the totalized `+ 0`). -/
theorem crosses_eq_algebra {kr kp q : ℝ} :
    CrossesAtThermoneutral kr kp q ↔ kr * q ^ 2 = kp * (q - 1) ^ 2 := by
  simp only [CrossesAtThermoneutral, asymReactantSurface, asymProductSurface, add_zero]

end SymmetryFactor

end PhotoLean
