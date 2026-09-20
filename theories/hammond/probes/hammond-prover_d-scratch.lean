/-
PhotoLean.Hammond.Sharp — H3, sharp conditions for the Hammond description.

The Hammond descriptor (`HammondDescriptor lam`, H1) says that the transition-state coordinate
is strictly decreasing in the driving force. This module proves that the descriptor holds
**if and only if the curvature is positive** (`hammond_sharp`), i.e. `0 < lam` is the exact
validity condition of the description — and that both failure branches are exhibited by
explicit two-point counter-witnesses rather than by a negated quantifier
(`exists_direction_reversal_of_neg` for `lam < 0`, `exists_direction_reversal_of_eq` for
`lam = 0`, both at the pair `x₁ = 0 < x₂ = 1`).

Declaration order: the two witness theorems are stated before
`hammond_lam_pos_of_descriptor`, which consumes them in the two non-positive branches of
`lt_trichotomy lam 0` (the third branch is the conclusion itself). The order is the proof
dependency order; each signature is verbatim from the H3 section of
`theories/hammond/probes/hammond-statement-skeleton.lean` (plan §6).

Every physical premise (`lam < 0`, `lam ≤ 0`) is an explicit hypothesis. The `lam = 0` witness
uses the division-by-zero convention `x / 0 = 0` of `tsCoord` (plan §13, assumption 5): it is a
formal convention of the model, not a physical statement. There is no unproved placeholder and
no custom axiom anywhere in this file.
-/
import PhotoLean.Hammond.Criterion

namespace PhotoLean

namespace Hammond

/-- Explicit direction-reversal witness for negative curvature: with `lam < 0` the coordinate
is *increasing* in the driving force (the reverse of `tsCoord_antitone`), so the pair
`x₁ = 0 < x₂ = 1` satisfies the opposite inequality. -/
theorem exists_direction_reversal_of_neg {lam : ℝ} (hlam : lam < 0) :
    ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧ tsCoord lam x₁ < tsCoord lam x₂ := by
  refine ⟨0, 1, by norm_num, ?_⟩
  unfold tsCoord
  rw [div_lt_div_right_of_neg (by linarith : (2 : ℝ) * lam < 0)]
  linarith

/-- Explicit direction-reversal witness for zero curvature (degenerate division): with
`lam = 0` the coordinate is constant (`tsCoord_zero_lam`), so the pair `x₁ = 0 < x₂ = 1`
fails the strict decrease required by the descriptor. -/
theorem exists_direction_reversal_of_eq :
    ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧ ¬ (tsCoord 0 x₂ < tsCoord 0 x₁) := by
  refine ⟨0, 1, by norm_num, ?_⟩
  rw [tsCoord_zero_lam, tsCoord_zero_lam]
  norm_num

/-- Necessity kernel: the Hammond descriptor forces a positive curvature. All three branches of
`lt_trichotomy lam 0` are consumed: `lam < 0` and `lam = 0` contradict the descriptor at the
explicit two-point witnesses above, and `0 < lam` is the conclusion. -/
theorem hammond_lam_pos_of_descriptor {lam : ℝ} (h : HammondDescriptor lam) : 0 < lam := by
  rcases lt_trichotomy lam 0 with hneg | hzero | hpos
  · obtain ⟨x₁, x₂, hlt, hrev⟩ := exists_direction_reversal_of_neg hneg
    have hdesc : tsCoord lam x₂ < tsCoord lam x₁ := h x₁ x₂ hlt
    linarith
  · subst hzero
    obtain ⟨x₁, x₂, hlt, hnot⟩ := exists_direction_reversal_of_eq
    exact absurd (h x₁ x₂ hlt) hnot
  · exact hpos

/-- Sharp characterization of the validity condition of the Hammond descriptor: the description
holds exactly for positive curvature (`hammond_descriptor_holds` is H2's sufficiency). -/
theorem hammond_sharp (lam : ℝ) : HammondDescriptor lam ↔ 0 < lam :=
  ⟨hammond_lam_pos_of_descriptor, hammond_descriptor_holds⟩

/-- Failure form: non-positive curvature kills the descriptor. -/
theorem hammond_fails_of_nonpos {lam : ℝ} (hlam : lam ≤ 0) : ¬ HammondDescriptor lam := by
  intro h
  linarith [hammond_lam_pos_of_descriptor h]

/-- The instance-level verdict also forces a positive curvature (it is the first component of
`HammondConforms`). -/
theorem conforms_requires_pos {lam x : ℝ} (h : HammondConforms lam x) : 0 < lam := h.1

end Hammond

end PhotoLean
