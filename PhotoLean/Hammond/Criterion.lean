/-
PhotoLean.Hammond.Criterion — H2, the Hammond criterion.

The content of the postulate inside the two-parabola model of `PhotoLean.Hammond.Basic`:
the transition-state coordinate is strictly decreasing in the driving force
(`tsCoord_antitone`, `hammond_descriptor_holds`), the energy-structure equivalence
(`gap_compare_iff`), Leffler's relation as an exact identity between a barrier-data observable
and the structural coordinate (`lefflerSecant_eq_midpoint`, `lefflerSecant_symm`,
`lefflerSecant_mem_iff`), the cross-link to the Marcus inverted region
(`tsCoord_lt_zero_iff_inverted`, `lefflerSecant_neg_iff_inverted`), the classifier
characterization of the instance verdict (`conforms_iff_zone`), non-vacuity of the predicates,
and the definitional bridge to `Marcus.barrier`.

Statement authority: every declaration below matches
`theories/hammond/probes/hammond-statement-skeleton.lean` (H2 section) word for word
(plan §5). Every physical premise (`0 < lam`, `x₁ ≠ x₂`) is an explicit hypothesis. There is no
unproved placeholder and no custom axiom anywhere in this file.
-/
import PhotoLean.Hammond.Basic
import PhotoLean.Marcus.Basic

namespace PhotoLean

namespace Hammond

/-- Hammond monotonicity: more driving force, earlier transition state. -/
theorem tsCoord_antitone {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ} (h : x₁ < x₂) :
    tsCoord lam x₂ < tsCoord lam x₁ := by
  unfold tsCoord
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 2 * lam)]
  linarith

/-- The Hammond descriptor holds whenever the curvature is positive. -/
theorem hammond_descriptor_holds {lam : ℝ} (hlam : 0 < lam) : HammondDescriptor lam := by
  intro x₁ x₂ h
  exact tsCoord_antitone hlam h

/-- Exergonic reactions have reactant-like transition states. -/
theorem reactantLike_iff {lam x : ℝ} (hlam : 0 < lam) : ReactantLike lam x ↔ 0 < x := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  unfold ReactantLike tsCoord
  rw [div_lt_iff₀ h2]
  constructor <;> intro h <;> linarith

/-- Endergonic reactions have product-like transition states. -/
theorem productLike_iff {lam x : ℝ} (hlam : 0 < lam) : ProductLike lam x ↔ x < 0 := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  unfold ProductLike tsCoord
  rw [lt_div_iff₀ h2]
  constructor <;> intro h <;> linarith

/-- Energy–structure correspondence: the transition state is closer in energy to the
reactant well exactly when it is reactant-like. -/
theorem gap_compare_iff {lam x : ℝ} (hlam : 0 < lam) :
    gapReactant lam x < gapProduct lam x ↔ 0 < x := by
  have hsub : gapProduct lam x - gapReactant lam x = x :=
    gapProduct_sub_gapReactant (ne_of_gt hlam) x
  constructor <;> intro h <;> linarith

/-- Leffler's relation, exact: the measured Brønsted slope equals the transition-state
coordinate at the midpoint (no mean value theorem: the barrier is a quadratic). -/
theorem lefflerSecant_eq_midpoint {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h : x₁ ≠ x₂) :
    lefflerSecant lam x₁ x₂ = tsCoord lam ((x₁ + x₂) / 2) := by
  have h4 : (4 * lam : ℝ) ≠ 0 := by positivity
  have h2 : (2 * lam : ℝ) ≠ 0 := by positivity
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  unfold lefflerSecant tsCoord gapReactant
  field_simp
  ring

/-- The Brønsted coefficient lies strictly between 0 and 1 exactly in the Hammond regime. -/
theorem lefflerSecant_mem_iff {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h : x₁ ≠ x₂) :
    0 < lefflerSecant lam x₁ x₂ ∧ lefflerSecant lam x₁ x₂ < 1 ↔
      ReactionRegion lam ((x₁ + x₂) / 2) := by
  rw [lefflerSecant_eq_midpoint hlam h]
  exact tsCoord_mem_iff hlam

/-- Pointwise Brønsted coefficient via a symmetric finite difference. -/
theorem lefflerSecant_symm {lam x : ℝ} (hlam : 0 < lam) :
    lefflerSecant lam (x - 1) (x + 1) = tsCoord lam x := by
  rw [lefflerSecant_eq_midpoint hlam (by linarith : x - 1 ≠ x + 1)]
  ring_nf

