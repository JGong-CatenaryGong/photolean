/-
Statement skeleton for the Hammond theory — the **authority for all delivered signatures**.
English: Every declaration in `PhotoLean/Hammond/*.lean` must match the corresponding
signature here word for word (the fidelity check reads this file). It lives under
`theories/hammond/probes/`, i.e. OUTSIDE `SOURCE_DIRS`, because the source tree has zero
tolerance for the unfinished-proof placeholder keyword; statement-first requires the
signatures to elaborate before any proof work starts. 0 error is the Sprint 0 gate.
-/
import Mathlib
import PhotoLean.Marcus.Basic
import PhotoLean.Marcus.Reorg
import PhotoLean.Marcus.RatModel

namespace PhotoLean

namespace Hammond

/-! ## H1 — description layer (`PhotoLean/Hammond/Basic.lean`) -/

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

/-- The crossing point is unique and equals `tsCoord`. -/
theorem crossing_iff {lam dG q : ℝ} (hlam : lam ≠ 0) :
    reactantSurface lam q = productSurface lam dG q ↔ q = tsCoord lam (-dG) := by
  sorry

/-- The forward barrier is the reactant-surface energy at the crossing point. -/
theorem gapReactant_eq_crossing_energy {lam dG : ℝ} (hlam : lam ≠ 0) :
    gapReactant lam (-dG) = reactantSurface lam (tsCoord lam (-dG)) := by
  sorry

/-- The reverse barrier is the product-surface energy at the crossing point **measured from the
product well** (whose energy is `dG`): the well-referenced form is the correct one, since the
product well is not the zero of energy. -/
theorem gapProduct_eq_crossing_energy {lam dG : ℝ} (hlam : lam ≠ 0) :
    gapProduct lam (-dG) = productSurface lam dG (tsCoord lam (-dG)) - dG := by
  sorry

/-- The two barriers differ exactly by the driving force (reverse-barrier identity). -/
theorem gapProduct_sub_gapReactant {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    gapProduct lam x - gapReactant lam x = x := by
  sorry

/-- Reverse-reaction symmetry: the reverse of driving force `x` is the forward reaction
of driving force `-x`. -/
theorem gapProduct_eq_gapReactant_neg (lam x : ℝ) : gapProduct lam x = gapReactant lam (-x) := by
  sorry

/-- The reverse-reaction transition state mirrors the forward one about `q = 1/2`. -/
theorem tsCoord_neg {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    tsCoord lam (-x) = 1 - tsCoord lam x := by
  sorry

/-- Thermoneutrality puts the transition state exactly halfway. -/
theorem tsCoord_zero {lam : ℝ} (hlam : lam ≠ 0) : tsCoord lam 0 = 1 / 2 := by
  sorry

/-- Degenerate zero curvature: the coordinate is constant (division-by-zero convention). -/
theorem tsCoord_zero_lam (x : ℝ) : tsCoord 0 x = 0 := by
  sorry

/-- The rate-maximizing driving force `x = lam` puts the transition state exactly at the
reactant geometry. -/
theorem tsCoord_at_lam {lam : ℝ} (hlam : lam ≠ 0) : tsCoord lam lam = 0 := by
  sorry

/-- Structural regime: the transition state lies strictly between the two wells. -/
theorem tsCoord_mem_iff {lam x : ℝ} (hlam : 0 < lam) :
    0 < tsCoord lam x ∧ tsCoord lam x < 1 ↔ ReactionRegion lam x := by
  sorry

/-- The Hammond regime forces a positive curvature: the geometric prerequisite is not free. -/
theorem reactionRegion_pos {lam x : ℝ} (h : ReactionRegion lam x) : 0 < lam := by
  sorry

/-- With non-positive curvature there is no driving force in the Hammond regime. -/
theorem not_reactionRegion_of_nonpos {lam x : ℝ} (hlam : lam ≤ 0) :
    ¬ ReactionRegion lam x := by
  sorry

/-- Zone characterization, early branch. -/
theorem hammondZone_eq_early_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.early ↔ 0 < x ∧ x < lam := by
  sorry

/-- Zone characterization, thermoneutral branch. -/
theorem hammondZone_eq_half_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.half ↔ x = 0 := by
  sorry

/-- Zone characterization, late branch. -/
theorem hammondZone_eq_late_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.late ↔ x < 0 ∧ -lam < x := by
  sorry

/-- Zone characterization, barrierless forward branch. -/
theorem hammondZone_eq_atReactant_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.atReactant ↔ x = lam := by
  sorry

/-- Zone characterization, barrierless reverse branch. -/
theorem hammondZone_eq_atProduct_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.atProduct ↔ x = -lam := by
  sorry

/-- Zone characterization, inverted-region branch. -/
theorem hammondZone_eq_beyondReactant_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.beyondReactant ↔ lam < x := by
  sorry

/-- Zone characterization, deep endergonic branch. -/
theorem hammondZone_eq_beyondProduct_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.beyondProduct ↔ x < -lam := by
  sorry

end Hammond

/-! ## H2 — Hammond criterion (`PhotoLean/Hammond/Criterion.lean`) -/

namespace Hammond

/-- Hammond monotonicity: more driving force, earlier transition state. -/
theorem tsCoord_antitone {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ} (h : x₁ < x₂) :
    tsCoord lam x₂ < tsCoord lam x₁ := by
  sorry

/-- The Hammond descriptor holds whenever the curvature is positive. -/
theorem hammond_descriptor_holds {lam : ℝ} (hlam : 0 < lam) : HammondDescriptor lam := by
  sorry

/-- Exergonic reactions have reactant-like transition states. -/
theorem reactantLike_iff {lam x : ℝ} (hlam : 0 < lam) : ReactantLike lam x ↔ 0 < x := by
  sorry

/-- Endergonic reactions have product-like transition states. -/
theorem productLike_iff {lam x : ℝ} (hlam : 0 < lam) : ProductLike lam x ↔ x < 0 := by
  sorry

/-- Energy–structure correspondence: the transition state is closer in energy to the
reactant well exactly when it is reactant-like. -/
theorem gap_compare_iff {lam x : ℝ} (hlam : 0 < lam) :
    gapReactant lam x < gapProduct lam x ↔ 0 < x := by
  sorry

/-- Leffler's relation, exact: the measured Brønsted slope equals the transition-state
coordinate at the midpoint (no mean value theorem: the barrier is a quadratic). -/
theorem lefflerSecant_eq_midpoint {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h : x₁ ≠ x₂) :
    lefflerSecant lam x₁ x₂ = tsCoord lam ((x₁ + x₂) / 2) := by
  sorry

/-- The Brønsted coefficient lies strictly between 0 and 1 exactly in the Hammond regime. -/
theorem lefflerSecant_mem_iff {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h : x₁ ≠ x₂) :
    0 < lefflerSecant lam x₁ x₂ ∧ lefflerSecant lam x₁ x₂ < 1 ↔
      ReactionRegion lam ((x₁ + x₂) / 2) := by
  sorry

/-- Pointwise Brønsted coefficient via a symmetric finite difference. -/
theorem lefflerSecant_symm {lam x : ℝ} (hlam : 0 < lam) :
    lefflerSecant lam (x - 1) (x + 1) = tsCoord lam x := by
  sorry

/-- The transition state leaves the reactant side of the interval exactly in the Marcus
inverted region. -/
theorem tsCoord_lt_zero_iff_inverted {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x < 0 ↔ Marcus.InvertedRegion lam x := by
  sorry

/-- A negative Brønsted coefficient is exactly the Marcus inverted region, seen from the
barrier data. -/
theorem lefflerSecant_neg_iff_inverted {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h : x₁ ≠ x₂) :
    lefflerSecant lam x₁ x₂ < 0 ↔ Marcus.InvertedRegion lam ((x₁ + x₂) / 2) := by
  sorry

/-- The instance-level verdict, characterized by the classifier: conforming means the instance is
classified early, thermoneutral or late (the three branches strictly between the two wells). -/
theorem conforms_iff_zone {lam x : ℝ} (hlam : 0 < lam) :
    HammondConforms lam x ↔
      hammondZone lam x = HZone.early ∨ hammondZone lam x = HZone.half ∨
        hammondZone lam x = HZone.late := by
  sorry

/-- Non-vacuity: reactant-like transition states exist. -/
theorem exists_reactantLike {lam : ℝ} (hlam : 0 < lam) : ∃ x : ℝ, ReactantLike lam x := by
  sorry

/-- Non-vacuity: product-like transition states exist. -/
theorem exists_productLike {lam : ℝ} (hlam : 0 < lam) : ∃ x : ℝ, ProductLike lam x := by
  sorry

/-- Non-vacuity: the Hammond regime is non-empty. -/
theorem exists_reactionRegion {lam : ℝ} (hlam : 0 < lam) : ∃ x : ℝ, ReactionRegion lam x := by
  sorry

/-- Bridge to the Marcus barrier: the forward barrier is literally the Marcus `barrier`. -/
theorem barrier_eq_gapReactant (lam x : ℝ) : Marcus.barrier lam x = gapReactant lam x := by
  sorry

end Hammond

/-! ## H3 — sharp conditions (`PhotoLean/Hammond/Sharp.lean`) -/

namespace Hammond

/-- Necessity kernel: the Hammond descriptor forces a positive curvature. -/
theorem hammond_lam_pos_of_descriptor {lam : ℝ} (h : HammondDescriptor lam) : 0 < lam := by
  sorry

/-- Sharp characterization of the validity condition of the Hammond descriptor. -/
theorem hammond_sharp (lam : ℝ) : HammondDescriptor lam ↔ 0 < lam := by
  sorry

/-- Failure form: non-positive curvature kills the descriptor. -/
theorem hammond_fails_of_nonpos {lam : ℝ} (hlam : lam ≤ 0) : ¬ HammondDescriptor lam := by
  sorry

/-- Explicit direction-reversal witness for negative curvature. -/
theorem exists_direction_reversal_of_neg {lam : ℝ} (hlam : lam < 0) :
    ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧ tsCoord lam x₁ < tsCoord lam x₂ := by
  sorry

/-- Explicit direction-reversal witness for zero curvature (degenerate division). -/
theorem exists_direction_reversal_of_eq :
    ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧ ¬ (tsCoord 0 x₂ < tsCoord 0 x₁) := by
  sorry

/-- The instance-level verdict also forces a positive curvature. -/
theorem conforms_requires_pos {lam x : ℝ} (h : HammondConforms lam x) : 0 < lam := by
  sorry

end Hammond

/-! ## H4 — microscopic conditions (`PhotoLean/Hammond/Compose.lean`) -/

namespace Hammond

/-- A positive molecular force constant with a non-zero geometry change yields the Hammond
descriptor for the inner-sphere reorganization energy. -/
theorem hammond_descriptor_of_inner {kk dq : ℝ} (hkk : 0 < kk) (hdq : dq ≠ 0) :
    HammondDescriptor (Marcus.lamInner kk dq) := by
  sorry

/-- Microscopic sufficiency: the Pekar factor and the geometric factor (explicit physical
premises) make the total reorganization energy positive, hence the descriptor holds. -/
theorem hammond_descriptor_of_microscopic {kk dq dE a1 a2 R nSq epsS : ℝ} (hkk : 0 ≤ kk)
    (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2) (hR : 0 < R)
    (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    HammondDescriptor (Marcus.lamInner kk dq + Marcus.lamOuter dE a1 a2 R nSq epsS) := by
  sorry

/-- Stretch: the geometric premise is derivable from non-overlapping spheres. -/
theorem hammond_descriptor_of_nonoverlap {kk dq dE a1 a2 R nSq epsS : ℝ} (hkk : 0 ≤ kk)
    (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2) (hRge : a1 + a2 ≤ R) (hnSq : 0 < nSq)
    (hepsS : 0 < epsS) (hPekar : 1 / epsS < 1 / nSq) :
    HammondDescriptor (Marcus.lamInner kk dq + Marcus.lamOuter dE a1 a2 R nSq epsS) := by
  sorry

/-- Non-vacuity from microscopic premises: the Hammond regime is non-empty for physical
parameters. -/
theorem exists_reactionRegion_of_microscopic {kk dq dE a1 a2 R nSq epsS : ℝ} (hkk : 0 < kk)
    (hdq : dq ≠ 0) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2) (hR : 0 < R)
    (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    ∃ x : ℝ, ReactionRegion (Marcus.lamInner kk dq + Marcus.lamOuter dE a1 a2 R nSq epsS) x := by
  sorry

end Hammond

/-! ## H5a — rational decision layer (`PhotoLean/Hammond/RatModel.lean`) -/

namespace Hammond

namespace Rat

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

/-- Transfer: the rational coordinate casts to the real one. -/
theorem tsCoordQ_cast (lam x : ℚ) :
    ((tsCoordQ lam x : ℚ) : ℝ) = tsCoord (lam : ℝ) (x : ℝ) := by
  sorry

/-- Transfer: the rational barrier casts to the real one. -/
theorem gapReactantQ_cast (lam x : ℚ) :
    ((gapReactantQ lam x : ℚ) : ℝ) = gapReactant (lam : ℝ) (x : ℝ) := by
  sorry

/-- Transfer: the rational Leffler secant casts to the real one. -/
theorem lefflerSecantQ_cast {lam x₁ x₂ : ℚ} (h : x₁ ≠ x₂) :
    ((lefflerSecantQ lam x₁ x₂ : ℚ) : ℝ) = lefflerSecant (lam : ℝ) (x₁ : ℝ) (x₂ : ℝ) := by
  sorry

/-- Transfer: the rational classifier agrees with the real one — this is what makes an
instance verdict binding for the real theory. -/
theorem hammondZoneQ_eq_hammondZone (lam x : ℚ) :
    hammondZoneQ lam x = hammondZone (lam : ℝ) (x : ℝ) := by
  sorry

/-- Rational zone characterization, early branch. -/
theorem hammondZoneQ_eq_early_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.early ↔ 0 < x ∧ x < lam := by
  sorry

/-- Rational zone characterization, thermoneutral branch. -/
theorem hammondZoneQ_eq_half_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.half ↔ x = 0 := by
  sorry

/-- Rational zone characterization, late branch. -/
theorem hammondZoneQ_eq_late_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.late ↔ x < 0 ∧ -lam < x := by
  sorry

/-- Rational zone characterization, barrierless forward branch. -/
theorem hammondZoneQ_eq_atReactant_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.atReactant ↔ x = lam := by
  sorry

/-- Rational zone characterization, barrierless reverse branch. -/
theorem hammondZoneQ_eq_atProduct_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.atProduct ↔ x = -lam := by
  sorry

/-- Rational zone characterization, inverted-region branch. -/
theorem hammondZoneQ_eq_beyondReactant_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.beyondReactant ↔ lam < x := by
  sorry

/-- Rational zone characterization, deep endergonic branch. -/
theorem hammondZoneQ_eq_beyondProduct_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.beyondProduct ↔ x < -lam := by
  sorry

/-- Cross-link to the Marcus inverted region on the rational side. -/
theorem hammondZoneQ_beyondReactant_iff_inverted {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.beyondReactant ↔ Marcus.Rat.zoneQ lam x = Marcus.Zone.inverted := by
  sorry

end Rat

end Hammond

/-! ## H5b — instances and verdicts (`PhotoLean/Hammond/Instances.lean`) -/

namespace Hammond

/-- I1: thermoneutral textbook instance `lam = 1`, `x = 0` (verdict carrier). -/
theorem inst_I1_thermoneutral_zone : Rat.hammondZoneQ (1 : ℚ) 0 = HZone.half := by
  sorry

/-- I1: the thermoneutral instance conforms to the Hammond description. -/
theorem inst_I1_thermoneutral_conforms : HammondConforms 1 0 := by
  sorry

/-- I1: its transition state is exactly halfway. -/
theorem inst_I1_thermoneutral_coord : tsCoord 1 0 = 1 / 2 := by
  sorry

/-- I2: mildly exergonic textbook instance `lam = 1`, `x = 3/4`. -/
theorem inst_I2_exergonic_zone : Rat.hammondZoneQ (1 : ℚ) (3 / 4) = HZone.early := by
  sorry

/-- I2: it is reactant-like. -/
theorem inst_I2_exergonic_reactantLike : ReactantLike 1 (3 / 4) := by
  sorry

/-- I2: it conforms to the Hammond description. -/
theorem inst_I2_exergonic_conforms : HammondConforms 1 (3 / 4) := by
  sorry

/-- I3: endergonic textbook instance `lam = 1`, `x = -1/2`. -/
theorem inst_I3_endergonic_zone : Rat.hammondZoneQ (1 : ℚ) (-(1 / 2)) = HZone.late := by
  sorry

/-- I3: it is product-like. -/
theorem inst_I3_endergonic_productLike : ProductLike 1 (-(1 / 2)) := by
  sorry

/-- I3: it conforms to the Hammond description. -/
theorem inst_I3_endergonic_conforms : HammondConforms 1 (-(1 / 2)) := by
  sorry

/-- I4: the barrierless instance `lam = 1`, `x = 1` sits on the boundary of the regime. -/
theorem inst_I4_barrierless_zone : Rat.hammondZoneQ (1 : ℚ) 1 = HZone.atReactant := by
  sorry

/-- I4: its transition state is exactly at the reactant geometry. -/
theorem inst_I4_barrierless_coord : tsCoord 1 1 = 0 := by
  sorry

/-- I4: the point-level verdict FAILS at the boundary (the crossing point is not strictly
between the wells, so the resemblance reading is degenerate). -/
theorem inst_I4_barrierless_notConforms : ¬ HammondConforms 1 1 := by
  sorry

/-- I4: the family-level descriptor nevertheless holds (it is a statement about `lam` alone). -/
theorem inst_I4_family_descriptor : HammondDescriptor 1 := by
  sorry

/-- I5: literature MCC normal-region instance `lam = 6/5`, `x = 1/20`. -/
theorem inst_I5_mcc_normal_zone : Rat.hammondZoneQ (6 / 5) (1 / 20) = HZone.early := by
  sorry

/-- I5: its transition state coordinate is `23/48`. -/
theorem inst_I5_mcc_normal_coord : tsCoord (6 / 5) (1 / 20) = 23 / 48 := by
  sorry

/-- I5: it conforms to the Hammond description. -/
theorem inst_I5_mcc_normal_conforms : HammondConforms (6 / 5) (1 / 20) := by
  sorry

/-- I6: literature MCC inverted-region instance `lam = 6/5`, `x = 12/5`. -/
theorem inst_I6_mcc_inverted_zone : Rat.hammondZoneQ (6 / 5) (12 / 5) = HZone.beyondReactant := by
  sorry

/-- I6: its transition state coordinate is `-1/2` (outside the structural interval). -/
theorem inst_I6_mcc_inverted_coord : tsCoord (6 / 5) (12 / 5) = -(1 / 2) := by
  sorry

/-- I6: it does NOT conform to the Hammond description. -/
theorem inst_I6_mcc_inverted_notConforms : ¬ HammondConforms (6 / 5) (12 / 5) := by
  sorry

/-- I6: it is exactly the Marcus inverted region. -/
theorem inst_I6_mcc_inverted_region : Marcus.InvertedRegion (6 / 5) (12 / 5) := by
  sorry

/-- I6: the Brønsted coefficient measured from the barrier data is negative. -/
theorem inst_I6_mcc_leffler_negative : Rat.lefflerSecantQ (6 / 5) (3 / 5) (12 / 5) = -(1 / 8) := by
  sorry

/-- I7: literature reaction-centre inverted instance `lam = 1/4`, `x = 11/10`. -/
theorem inst_I7_rc_inverted_zone : Rat.hammondZoneQ (1 / 4) (11 / 10) = HZone.beyondReactant := by
  sorry

/-- I7: its transition state coordinate is `-17/10`. -/
theorem inst_I7_rc_inverted_coord : tsCoord (1 / 4) (11 / 10) = -(17 / 10) := by
  sorry

/-- I7: it does NOT conform to the Hammond description. -/
theorem inst_I7_rc_inverted_notConforms : ¬ HammondConforms (1 / 4) (11 / 10) := by
  sorry

/-- I8: a non-physical negative curvature instance is rejected (descriptor fails). -/
theorem inst_I8_nonphysical_fails_neg : ¬ HammondDescriptor (-(1 / 2)) := by
  sorry

/-- I8: zero curvature is rejected as well (degenerate division). -/
theorem inst_I8_nonphysical_fails_zero : ¬ HammondDescriptor 0 := by
  sorry

/-- I8: no driving force satisfies the Hammond regime at non-positive curvature. -/
theorem inst_I8_nonphysical_no_region : ¬ ReactionRegion (-(1 / 2)) 1 := by
  sorry

/-- I9: the Hammond direction on the literature MCC pair (structural monotonicity). -/
theorem inst_I9_mcc_structural_monotone : tsCoord (6 / 5) (12 / 5) < tsCoord (6 / 5) (3 / 5) := by
  sorry

/-- I10: non-vacuity of the instance layer on literature parameters. -/
theorem inst_I10_nonvacuous : ReactantLike (6 / 5) (1 / 20) ∧ ProductLike (6 / 5) (-(1 / 20)) := by
  sorry

end Hammond

end PhotoLean
