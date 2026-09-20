/-
PhotoLean.Hammond.Basic — H1, the description layer of the Hammond theory.

The two-parabola (Marcus-type) model of an elementary reaction step: a reactant well at `q = 0`,
a product well at `q = 1`, harmonic surfaces of equal curvature `2 * lam`, and the classical
crossing point as the transition state. This module makes "transition-state structure",
"resembles", "Hammond regime" and "Hammond description" Lean objects, and grounds `tsCoord`
in the surface geometry (`crossing_iff`, `gapReactant_eq_crossing_energy`).

Statement authority: every declaration below matches
`theories/hammond/probes/hammond-statement-skeleton.lean` word for word (plan §2.2, §4.2, §4.3).
This file imports `Mathlib` only and is independent of the `PhotoLean.Marcus` modules.
Every physical premise (`lam ≠ 0`, `0 < lam`) is an explicit hypothesis; nothing is hidden in a
definition. There is no unproved placeholder and no custom axiom anywhere in this file.
-/
import Mathlib

namespace PhotoLean

namespace Hammond

/-! ## Definitions (plan §2.2) -/

/-- Reactant potential-energy surface: minimum at `q = 0`, curvature `2*lam`. -/
noncomputable def reactantSurface (lam q : ℝ) : ℝ := lam * q ^ 2

/-- Product potential-energy surface: minimum at `q = 1`, same curvature, offset by the
reaction energy `dG = ΔG°` (exergonic: `dG < 0`). -/
noncomputable def productSurface (lam dG q : ℝ) : ℝ := lam * (q - 1) ^ 2 + dG

/-- Transition-state coordinate on the reaction coordinate, in the driving-force
convention `x = -ΔG°` (exergonic: `x > 0`). -/
noncomputable def tsCoord (lam x : ℝ) : ℝ := (lam - x) / (2 * lam)

/-- Forward barrier: reactant well up to the crossing point. -/
noncomputable def gapReactant (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- Reverse barrier: product well up to the crossing point. -/
noncomputable def gapProduct (lam x : ℝ) : ℝ := (lam + x) ^ 2 / (4 * lam)

/-- Leffler/Brønsted coefficient measured as a finite difference (secant of the barrier
against the driving force) — an observable of the barrier data, not a definitional copy
of the structural coordinate. -/
noncomputable def lefflerSecant (lam x₁ x₂ : ℝ) : ℝ :=
  -(gapReactant lam x₂ - gapReactant lam x₁) / (x₂ - x₁)

/-- The Hammond regime: the crossing point lies strictly between the two wells. -/
def ReactionRegion (lam x : ℝ) : Prop := -lam < x ∧ x < lam

/-- The transition state is reactant-like (exergonic side of thermoneutrality). -/
def ReactantLike (lam x : ℝ) : Prop := tsCoord lam x < 1 / 2

/-- The transition state is product-like (endergonic side of thermoneutrality). -/
def ProductLike (lam x : ℝ) : Prop := 1 / 2 < tsCoord lam x

/-- Point-level verdict of the instance layer: the curvature is physical AND the crossing
point lies strictly between the two wells, so a structural-resemblance verdict is meaningful. -/
def HammondConforms (lam x : ℝ) : Prop := 0 < lam ∧ ReactionRegion lam x

/-- The Hammond descriptor (family-level): the more exergonic the reaction, the earlier
(more reactant-like) the transition state. -/
def HammondDescriptor (lam : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, x₁ < x₂ → tsCoord lam x₂ < tsCoord lam x₁

/-- Structural classification of an instance (the verdict carrier of the instance layer). -/
inductive HZone where
  | early
  | half
  | late
  | atReactant
  | atProduct
  | beyondReactant
  | beyondProduct
  deriving DecidableEq, Repr

/-- Classifier: `0 < x < lam` early; `x = 0` thermoneutral; `-lam < x < 0` late;
`x = lam` / `x = -lam` barrierless; `lam < x` / `x < -lam` outside the structural interval. -/
noncomputable def hammondZone (lam x : ℝ) : HZone :=
  if x = lam then HZone.atReactant
  else if x = -lam then HZone.atProduct
  else if x < -lam then HZone.beyondProduct
  else if lam < x then HZone.beyondReactant
  else if x = 0 then HZone.half
  else if 0 < x then HZone.early
  else HZone.late

/-! ## Crossing geometry (plan §4.2) -/

/-- The crossing point is unique and equals `tsCoord`. -/
theorem crossing_iff {lam dG q : ℝ} (hlam : lam ≠ 0) :
    reactantSurface lam q = productSurface lam dG q ↔ q = tsCoord lam (-dG) := by
  unfold reactantSurface productSurface tsCoord
  constructor
  · intro h
    rw [eq_div_iff (mul_ne_zero (by norm_num) hlam)]
    nlinarith [h]
  · intro h
    rw [h]
    field_simp
    ring

/-- The forward barrier is the reactant-surface energy at the crossing point. -/
theorem gapReactant_eq_crossing_energy {lam dG : ℝ} (hlam : lam ≠ 0) :
    gapReactant lam (-dG) = reactantSurface lam (tsCoord lam (-dG)) := by
  have h4 : (4 * lam : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hlam
  have h2 : (2 * lam : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hlam
  unfold gapReactant reactantSurface tsCoord
  field_simp
  ring

/-- The reverse barrier is the product-surface energy at the crossing point **measured from the
product well** (whose energy is `dG`): the well-referenced form is the correct one, since the
product well is not the zero of energy. -/
theorem gapProduct_eq_crossing_energy {lam dG : ℝ} (hlam : lam ≠ 0) :
    gapProduct lam (-dG) = productSurface lam dG (tsCoord lam (-dG)) - dG := by
  have h4 : (4 * lam : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hlam
  have h2 : (2 * lam : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hlam
  unfold gapProduct productSurface tsCoord
  field_simp
  ring

/-- The two barriers differ exactly by the driving force (reverse-barrier identity). -/
theorem gapProduct_sub_gapReactant {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    gapProduct lam x - gapReactant lam x = x := by
  have h4 : (4 * lam : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hlam
  unfold gapProduct gapReactant
  field_simp
  ring

/-- Reverse-reaction symmetry: the reverse of driving force `x` is the forward reaction
of driving force `-x`. -/
theorem gapProduct_eq_gapReactant_neg (lam x : ℝ) : gapProduct lam x = gapReactant lam (-x) := by
  unfold gapProduct gapReactant
  ring

/-- The reverse-reaction transition state mirrors the forward one about `q = 1/2`. -/
theorem tsCoord_neg {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    tsCoord lam (-x) = 1 - tsCoord lam x := by
  unfold tsCoord
  field_simp
  ring

/-- Thermoneutrality puts the transition state exactly halfway. -/
theorem tsCoord_zero {lam : ℝ} (hlam : lam ≠ 0) : tsCoord lam 0 = 1 / 2 := by
  unfold tsCoord
  field_simp
  ring

/-- Degenerate zero curvature: the coordinate is constant (division-by-zero convention). -/
theorem tsCoord_zero_lam (x : ℝ) : tsCoord 0 x = 0 := by
  unfold tsCoord
  norm_num

/- Note on `set_option linter.unusedVariables false in`: four declarations below carry an
explicit premise (`hlam : lam ≠ 0` or `hlam : 0 < lam`) that the corresponding proof does not
consume — `tsCoord_at_lam` because Lean fixes `x / 0 = 0`, and three classifier lemmas because
their branch guards already force the sign information. The premises remain in the statements
(they belong to the description layer and keep signature fidelity with the statement skeleton);
the unused-variable linter is disabled locally so that a warning-free build still surfaces any
real warning elsewhere in the file. -/
