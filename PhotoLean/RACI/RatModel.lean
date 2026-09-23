/-
PhotoLean.RACI.RatModel — the rational decision layer of the RACI theory (integration addition).

The ℝ discriminant `(a − d)² + 4·b²` is a pure polynomial, so the conical-intersection condition
decides exactly over ℚ with no transcendental in sight — the EnergyGapLaw precedent: the decision
stays at the discriminant level, never evaluating `Real.exp` or `Real.sqrt`. This module carries
the ℚ shadow of the CI condition, the `conical | gapped` zone classifier with its correctness
rows, and the instance verdicts used by `Instances.lean`.

NOTE (integration record, plan §3.1): the ported RACI files keep the upstream default
autoImplicit; this addition follows the PhotoLean style (`set_option autoImplicit false`).
-/
import Mathlib
import PhotoLean.RACI.TwoState

set_option autoImplicit false

namespace PhotoLean

namespace RACI

namespace Rat

/-- The rational-layer discriminant of a 2×2 entry triple: `(a − d)² + 4·b²`. Pure rational
arithmetic — the decision layer for the CI condition. -/
def discrQ (a b d : ℚ) : ℚ := (a - d) ^ 2 + 4 * b ^ 2

/-- The conical-intersection zone of an entry triple. -/
inductive CIZone where
  | conical
  | gapped
  deriving DecidableEq, Repr

/-- The zone classifier at the rational layer (decidable over ℚ). -/
def ciZoneQ (a b d : ℚ) : CIZone :=
  if discrQ a b d = 0 then .conical else .gapped

/-- Correctness: the ℚ zone decides the vanishing discriminant. -/
theorem ciZoneQ_conical_iff (a b d : ℚ) :
    ciZoneQ a b d = .conical ↔ discrQ a b d = 0 := by
  unfold ciZoneQ
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun hbad => absurd hbad (by decide), fun hd => absurd hd h⟩

/-- Correctness: the conical zone is the entry condition `a = d ∧ b = 0` — the ℚ form of the
TwoState CI algebra, mirrored without casting through ℝ. -/
theorem ciZoneQ_conical_iff_entries (a b d : ℚ) :
    ciZoneQ a b d = .conical ↔ a = d ∧ b = 0 := by
  rw [ciZoneQ_conical_iff]
  constructor
  · intro h
    unfold discrQ at h
    have h1 : 0 ≤ (a - d) ^ 2 := sq_nonneg (a - d)
    have h2 : 0 ≤ 4 * b ^ 2 := mul_nonneg (by norm_num) (sq_nonneg b)
    have hsq1 : (a - d) ^ 2 = 0 := by nlinarith
    have hsq2 : 4 * b ^ 2 = 0 := by nlinarith
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hsq1), by
      rcases mul_eq_zero.mp hsq2 with h4 | hb2
      · norm_num at h4
      · exact sq_eq_zero_iff.mp hb2⟩
  · rintro ⟨had, hb⟩
    unfold discrQ
    simp [had, hb]

/-- Cast coherence: the real discriminant at rational entries is the cast of the ℚ discriminant. -/
theorem discrQ_cast (a b d : ℚ) :
    ((discrQ a b d : ℚ) : ℝ) = ((a : ℝ) - (d : ℝ)) ^ 2 + 4 * ((b : ℝ)) ^ 2 := by
  unfold discrQ
  push_cast
  ring

/-- The torsion model's conical entry `(0, 0, 0)` decides `conical` at ℚ (integer literals —
the measured `decide` boundary is not hit here). -/
theorem ciZoneQ_conical_entry_verdict : ciZoneQ 0 0 0 = .conical := by
  norm_num [ciZoneQ, discrQ]

/-- The non-model's entry `(1, 0, 2)` decides `gapped` at ℚ. -/
theorem ciZoneQ_nonModel_gapped_verdict : ciZoneQ 1 0 2 = .gapped := by
  norm_num [ciZoneQ, discrQ]

/-- An off-diagonal perturbation gaps the crossing: `(1, 1, 1)` decides `gapped` — the
codimension-2 nature of the CI at the decision layer (both conditions must fail together). -/
theorem ciZoneQ_offdiagonal_gapped_verdict : ciZoneQ 1 1 1 = .gapped := by
  norm_num [ciZoneQ, discrQ]

/-- The discriminant is nonnegative at ℚ (the classifier never sees a negative discriminant). -/
theorem discrQ_nonneg (a b d : ℚ) : 0 ≤ discrQ a b d := by
  unfold discrQ
  exact add_nonneg (sq_nonneg (a - d)) (mul_nonneg (by norm_num) (sq_nonneg b))

end Rat

end RACI

end PhotoLean
