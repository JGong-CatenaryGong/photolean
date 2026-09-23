/-
PhotoLean.StokesShift.RatModel — milestone SS-R, the rational decision layer.

The order of `ℝ` is not computable, so instance verdicts about band positions cannot be decided
by the kernel over `ℝ` directly (the repository's standing structural solution: an `ℝ` theory
plus a `ℚ` shadow plus cast bridges — METHOD.md five-piece item 2). For this theory the shadow
is **exact and complete**: every object of the layer is a polynomial with rational
coefficients, so the `ℚ` twins need no square roots, no clearing of denominators and no
side conditions — the cast-coherence rows prove that the shadow computes the real object at
cast parameters, i.e. that the copy is the real thing and not an analogy.

The classifier `SSZone` carries the three physical regimes of the model:
`normalEmission` (a positive vertical photon, `lam < e00`), `zeroPhoton` (the window edge,
`lam = e00`) and `invertedEmission` (negative vertical emission, `e00 < lam`). The three
correctness rows identify each constructor with the corresponding **strict/weak relation on the
real parameters** under the casts, so a zone verdict on printed rationals is a verdict about the
real model.

Measured boundary (API round): `decide` does not reduce `ℚ` division, so the instance rows are
decided by `norm_num`, never by `decide` on a division-bearing literal; the classifier rows
themselves are `ℚ` *comparisons*, which `norm_num`/`split_ifs` handle.

Statement authority: `theories/StokesShift/probes/StokesShift-statement-skeleton.lean` § SS-R;
every signature below is identical to its authority row. There is no unproved placeholder and no
custom axiomatic declaration anywhere in this file. The `#print axioms` gate of every theorem
below lists at most `propext`, `Classical.choice`, `Quot.sound`.

Acceptance (contract `proofs/ENGINE.yml`):
  proofs/scripts/lake build PhotoLean.StokesShift.RatModel
  proofs/scripts/check.sh --strict PhotoLean.StokesShift.RatModel
  proofs/scripts/axioms.sh PhotoLean.StokesShift.RatModel PhotoLean.StokesShift.ssZoneQ_eq_invertedEmission_iff
-/
import PhotoLean.StokesShift.Basic

set_option autoImplicit false

namespace PhotoLean

namespace StokesShift

/-! ## SS-R — the rational decision layer -/

namespace Rat

/-- The computable ℚ shadow of the ground surface. Plan section 4, row SS-R1.
Pure polynomial — no transcendentals anywhere in the layer. -/
def s0Surface (lam q : ℚ) : ℚ := lam * q ^ 2

/-- The computable ℚ shadow of the excited surface. Plan section 4, row SS-R1. -/
def s1Surface (lam e00 q : ℚ) : ℚ := lam * (q - 1) ^ 2 + e00

/-- The computable ℚ shadow of the absorption energy. Plan section 4, row SS-R1. -/
def absEnergy (lam e00 : ℚ) : ℚ := s1Surface lam e00 0 - s0Surface lam 0

/-- The computable ℚ shadow of the emission energy. Plan section 4, row SS-R1. -/
def emEnergy (lam e00 : ℚ) : ℚ := s1Surface lam e00 1 - s0Surface lam 1

/-- The computable ℚ shadow of the Stokes shift. Plan section 4, row SS-R1. -/
def stokesShift (lam e00 : ℚ) : ℚ := absEnergy lam e00 - emEnergy lam e00

/-- Cast coherence: the ℚ shadow computes the real ground surface at cast parameters.
Plan section 4, row SS-R1 (cast-coherence row; name assigned in Sprint 0).
Proof route: `unfold` + cast simp (`norm_cast`, dry-run in the api-probe). -/
theorem s0Surface_cast (lam q : ℚ) :
    (s0Surface lam q : ℝ) = PhotoLean.StokesShift.s0Surface (lam : ℝ) (q : ℝ) := by
  unfold s0Surface PhotoLean.StokesShift.s0Surface
  push_cast
  ring

/-- Cast coherence: the ℚ shadow computes the real excited surface at cast parameters.
Plan section 4, row SS-R1 (cast-coherence row; name assigned in Sprint 0). -/
theorem s1Surface_cast (lam e00 q : ℚ) :
    (s1Surface lam e00 q : ℝ) = PhotoLean.StokesShift.s1Surface (lam : ℝ) (e00 : ℝ) (q : ℝ) := by
  unfold s1Surface PhotoLean.StokesShift.s1Surface
  push_cast
  ring

/-- Cast coherence: the ℚ shadow computes the real absorption energy at cast parameters.
Plan section 4, row SS-R1 (cast-coherence row; name assigned in Sprint 0). -/
theorem absEnergy_cast (lam e00 : ℚ) :
    (absEnergy lam e00 : ℝ) = PhotoLean.StokesShift.absEnergy (lam : ℝ) (e00 : ℝ) := by
  unfold absEnergy PhotoLean.StokesShift.absEnergy PhotoLean.StokesShift.s1Surface
    PhotoLean.StokesShift.s0Surface s1Surface s0Surface
  norm_cast

/-- Cast coherence: the ℚ shadow computes the real emission energy at cast parameters.
Plan section 4, row SS-R1 (cast-coherence row; name assigned in Sprint 0). -/
theorem emEnergy_cast (lam e00 : ℚ) :
    (emEnergy lam e00 : ℝ) = PhotoLean.StokesShift.emEnergy (lam : ℝ) (e00 : ℝ) := by
  unfold emEnergy PhotoLean.StokesShift.emEnergy PhotoLean.StokesShift.s1Surface
    PhotoLean.StokesShift.s0Surface s1Surface s0Surface
  norm_cast

/-- Cast coherence: the ℚ shadow computes the real Stokes shift at cast parameters.
Plan section 4, row SS-R1 (cast-coherence row; name assigned in Sprint 0). -/
theorem stokesShift_cast (lam e00 : ℚ) :
    (stokesShift lam e00 : ℝ) = PhotoLean.StokesShift.stokesShift (lam : ℝ) (e00 : ℝ) := by
  unfold stokesShift PhotoLean.StokesShift.stokesShift
  push_cast
  rw [absEnergy_cast, emEnergy_cast]

end Rat

/-- The three-zone verdict of the Stokes-shift model. Plan section 4, row SS-R2. -/
inductive SSZone | normalEmission | zeroPhoton | invertedEmission
  deriving DecidableEq

/-- The zone classifier at rational parameters: positive emission (`lam < e00`) is
`normalEmission`, vanishing emission (`lam = e00`) is `zeroPhoton`, negative emission
(`e00 < lam`) is `invertedEmission`. Plan section 4, row SS-R2 (comparisons decidable on ℚ;
instance verdicts by `decide`). -/
def ssZoneQ (lam e00 : ℚ) : SSZone :=
  if lam < e00 then SSZone.normalEmission
  else if e00 < lam then SSZone.invertedEmission
  else SSZone.zeroPhoton

/-- Zone correctness at cast parameters, `normalEmission` row. Plan section 4, row SS-R2
(the plan's "correctness rows" pattern instantiated per constructor; name assigned in
Sprint 0). Proof route: unfold the classifier, then `Rat.cast_lt`. -/
theorem ssZoneQ_eq_normalEmission_iff (lam e00 : ℚ) :
    ssZoneQ lam e00 = .normalEmission ↔ (lam : ℝ) < (e00 : ℝ) := by
  unfold ssZoneQ
  split_ifs with h1 h2
  · exact iff_of_true rfl (by exact_mod_cast h1)
  · exact iff_of_false (by decide) (fun hR => h1 (Rat.cast_lt.mp hR))
  · exact iff_of_false (by decide) (fun hR => h1 (Rat.cast_lt.mp hR))

/-- Zone correctness at cast parameters, `zeroPhoton` row. Plan section 4, row SS-R2
(the plan's "correctness rows" pattern instantiated per constructor; name assigned in
Sprint 0). Proof route: unfold the classifier, then `Rat.cast_inj`. -/
theorem ssZoneQ_eq_zeroPhoton_iff (lam e00 : ℚ) :
    ssZoneQ lam e00 = .zeroPhoton ↔ (lam : ℝ) = (e00 : ℝ) := by
  unfold ssZoneQ
  split_ifs with h1 h2
  · exact iff_of_false (by decide) (fun hR => absurd hR (ne_of_lt (by exact_mod_cast h1)))
  · exact iff_of_false (by decide) (fun hR => absurd hR (ne_of_gt (by exact_mod_cast h2)))
  · refine iff_of_true rfl ?_
    have heq : lam = e00 := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
    rw [heq]

/-- Zone correctness at cast parameters, `invertedEmission` row — the row shape the plan
writes explicitly. Plan section 4, row SS-R2. Proof route: unfold the classifier, then
`Rat.cast_lt`. -/
theorem ssZoneQ_eq_invertedEmission_iff (lam e00 : ℚ) :
    ssZoneQ lam e00 = .invertedEmission ↔ (e00 : ℝ) < (lam : ℝ) := by
  unfold ssZoneQ
  split_ifs with h1 h2
  · exact iff_of_false (by decide) (fun hR => absurd (by exact_mod_cast h1) (not_lt.mpr (le_of_lt hR)))
  · exact iff_of_true rfl (by exact_mod_cast h2)
  · exact iff_of_false (by decide) (fun hR => h2 (Rat.cast_lt.mp hR))

end StokesShift

end PhotoLean
