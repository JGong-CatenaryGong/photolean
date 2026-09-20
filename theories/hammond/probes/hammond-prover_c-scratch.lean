/-
Scratch probe for prover_c — H5a (`PhotoLean/Hammond/RatModel.lean`).

Purpose: develop and kernel-check the 4 definitions and 13 theorems of the rational decision
layer *before* writing them into the delivered file. It imports exactly the two upstream
modules the delivered file imports (`PhotoLean.Hammond.Basic`, `PhotoLean.Marcus.RatModel`),
so every recipe measured here transfers verbatim.

The declaration bodies below are byte-identical to the delivered file (doc comments included).
Not a deliverable; lives outside `SOURCE_DIRS`, which is why the placeholder keyword is
tolerated here (there is none in this file: every declaration below is complete).

Running:  proofs/scripts/lake env lean theories/hammond/probes/hammond-prover_c-scratch.lean
-/
import PhotoLean.Hammond.Basic
import PhotoLean.Marcus.RatModel

namespace PhotoLean

namespace Hammond

namespace Rat

/-! ## Definitions (plan §8.1) -/

/-- Rational transition-state coordinate (computable). -/
def tsCoordQ (lam x : ℚ) : ℚ := (lam - x) / (2 * lam)

/-- Rational forward barrier. -/
def gapReactantQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- Rational Leffler secant. -/
def lefflerSecantQ (lam x₁ x₂ : ℚ) : ℚ :=
  -(gapReactantQ lam x₂ - gapReactantQ lam x₁) / (x₂ - x₁)

/-- Rational structural classifier. -/
def hammondZoneQ (lam x : ℚ) : HZone :=
  if x = lam then HZone.atReactant
  else if x = -lam then HZone.atProduct
  else if x < -lam then HZone.beyondProduct
  else if lam < x then HZone.beyondReactant
  else if x = 0 then HZone.half
  else if 0 < x then HZone.early
  else HZone.late

/-! ## Transfer lemmas -/

/-- Transfer: the rational coordinate casts to the real one. -/
theorem tsCoordQ_cast (lam x : ℚ) :
    ((tsCoordQ lam x : ℚ) : ℝ) = tsCoord (lam : ℝ) (x : ℝ) := by
  unfold tsCoordQ tsCoord
  push_cast
  ring

/-- Transfer: the rational barrier casts to the real one. -/
theorem gapReactantQ_cast (lam x : ℚ) :
    ((gapReactantQ lam x : ℚ) : ℝ) = gapReactant (lam : ℝ) (x : ℝ) := by
  unfold gapReactantQ gapReactant
  push_cast
  ring

set_option linter.unusedVariables false in
/-- Transfer: the rational Leffler secant casts to the real one.

The hypothesis `x₁ ≠ x₂` is the explicit mathematical premise of a secant and is mandated by the
statement authority; it is *not used by the proof*, because `Rat.cast_div` commutes the cast with
division unconditionally (the `x / 0 = 0` convention collapses both sides at `x₁ = x₂`). It is kept
as an explicit premise rather than dropped, and the unused-variable linter is switched off for this
declaration only. -/
theorem lefflerSecantQ_cast {lam x₁ x₂ : ℚ} (h : x₁ ≠ x₂) :
    ((lefflerSecantQ lam x₁ x₂ : ℚ) : ℝ) = lefflerSecant (lam : ℝ) (x₁ : ℝ) (x₂ : ℝ) := by
  unfold lefflerSecantQ lefflerSecant
  push_cast
  rw [gapReactantQ_cast, gapReactantQ_cast]

/-- Transfer: the rational classifier agrees with the real one — this is what makes an
instance verdict binding for the real theory.

Both sides are the same seven-branch `if`-chain, so the only work is moving the six tests
(`↑x = ↑lam`, `↑x = -↑lam`, `↑x < -↑lam`, `↑lam < ↑x`, `↑x = 0`, `0 < ↑x`) back to ℚ: `unfold`
the two definitions and run `norm_cast`, which includes the literal `0` and normalises `-↑lam`
through `Rat.cast_neg`. No hypotheses are needed: the degenerate `lam = 0` branch transfers too. -/
theorem hammondZoneQ_eq_hammondZone (lam x : ℚ) :
    hammondZoneQ lam x = hammondZone (lam : ℝ) (x : ℝ) := by
  unfold hammondZoneQ hammondZone
  norm_cast

/-! ## Zone characterization lemmas (the ℚ-side semantic content of the classifier) -/

/-- Rational zone characterization, early branch. -/
theorem hammondZoneQ_eq_early_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.early ↔ 0 < x ∧ x < lam := by
  unfold hammondZoneQ
  split_ifs with h1 h2 h3 h4 h5 h6 <;>
    first
      | exact iff_of_true rfl ⟨h6, lt_of_le_of_ne (le_of_not_gt h4) h1⟩
      | exact iff_of_false (by decide) (by rintro ⟨hx, hy⟩; linarith)

/-- Rational zone characterization, thermoneutral branch. -/
theorem hammondZoneQ_eq_half_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.half ↔ x = 0 := by
  unfold hammondZoneQ
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_true rfl h5
  · exact iff_of_false (by decide) (ne_of_gt h6)
  · exact iff_of_false (by decide) h5

/-- Rational zone characterization, late branch. -/
theorem hammondZoneQ_eq_late_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.late ↔ x < 0 ∧ -lam < x := by
  unfold hammondZoneQ
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨-, hy⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨-, hy⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_true rfl
      ⟨lt_of_le_of_ne (le_of_not_gt h6) h5, lt_of_le_of_ne (le_of_not_gt h3) (Ne.symm h2)⟩

set_option linter.unusedVariables false in
/-- Rational zone characterization, barrierless forward branch.

The hypothesis `0 < lam` is mandated by the statement authority (uniformity with the other six
characterizations) and is *not needed by the proof*: the statement is true for every `lam`, since
at `lam = 0` the first branch already absorbs `x = lam = 0`. It is kept as an explicit premise
rather than dropped, and the unused-variable linter is switched off for this declaration only. -/
theorem hammondZoneQ_eq_atReactant_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.atReactant ↔ x = lam := by
  unfold hammondZoneQ
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_true rfl h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1

/-- Rational zone characterization, barrierless reverse branch. -/
theorem hammondZoneQ_eq_atProduct_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.atProduct ↔ x = -lam := by
  unfold hammondZoneQ
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rw [h1]; linarith)
  · exact iff_of_true rfl h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2

/-- Rational zone characterization, inverted-region branch. -/
theorem hammondZoneQ_eq_beyondReactant_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.beyondReactant ↔ lam < x := by
  unfold hammondZoneQ
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rw [h1]; linarith)
  · exact iff_of_false (by decide) (by rw [h2]; linarith)
  · exact iff_of_false (by decide) (by linarith)
  · exact iff_of_true rfl h4
  · exact iff_of_false (by decide) h4
  · exact iff_of_false (by decide) h4
  · exact iff_of_false (by decide) h4

/-- Rational zone characterization, deep endergonic branch. -/
theorem hammondZoneQ_eq_beyondProduct_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.beyondProduct ↔ x < -lam := by
  unfold hammondZoneQ
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rw [h1]; linarith)
  · exact iff_of_false (by decide) (by rw [h2]; linarith)
  · exact iff_of_true rfl h3
  · exact iff_of_false (by decide) h3
  · exact iff_of_false (by decide) h3
  · exact iff_of_false (by decide) h3
  · exact iff_of_false (by decide) h3

/-- Cross-link to the Marcus inverted region on the rational side: the two classifiers single out
the same instances. Proof: the ℚ-side characterization above, composed with the delivered bridge
`Marcus.Rat.zoneQ_inverted_iff` (`↔ (lam : ℝ) < (x : ℝ)`) and `Rat.cast_lt`. -/
theorem hammondZoneQ_beyondReactant_iff_inverted {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.beyondReactant ↔ Marcus.Rat.zoneQ lam x = Marcus.Zone.inverted := by
  rw [hammondZoneQ_eq_beyondReactant_iff hlam, Marcus.Rat.zoneQ_inverted_iff, Rat.cast_lt]

end Rat

end Hammond

end PhotoLean
