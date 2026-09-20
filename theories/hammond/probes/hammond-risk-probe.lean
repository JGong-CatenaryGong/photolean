/-
Hammond theory — lead risk probe (Sprint 0).
English: validates the *statement forms* the plan commits to: two-parabola model,
transition-state coordinate, energy-gap comparison, and the sharpness branches.
It is NOT a deliverable and lives outside SOURCE_DIRS, so the placeholder keyword is
tolerated here; the goal is to prove everything, so the plan's proof sketches are
backed by kernel evidence.
-/
import Mathlib

namespace PhotoLean.Hammond

/-- Reactant potential-energy surface: minimum at `q = 0`, curvature `2*lam`. -/
noncomputable def reactantSurface (lam q : ℝ) : ℝ := lam * q ^ 2

/-- Product surface: minimum at `q = 1`, same curvature, offset by the reaction energy `dG`.
    Sign convention: `dG = ΔG°`; exergonic reactions have `dG < 0`; driving force `x = -dG`. -/
noncomputable def productSurface (lam dG q : ℝ) : ℝ := lam * (q - 1) ^ 2 + dG

/-- Transition-state coordinate along the reaction coordinate, in the driving-force
    convention `x = -ΔG°` (exergonic: `x > 0`). -/
noncomputable def tsCoord (lam x : ℝ) : ℝ := (lam - x) / (2 * lam)

/-- Brønsted / Leffler coefficient `α` (driving-force convention). -/
noncomputable def bronsted (lam x : ℝ) : ℝ := (lam - x) / (2 * lam)

/-- Forward barrier (from the reactant well up to the crossing point). -/
noncomputable def gapReactant (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- Reverse barrier (from the product well up to the crossing point). -/
noncomputable def gapProduct (lam x : ℝ) : ℝ := (lam + x) ^ 2 / (4 * lam)

-- R1: crossing point is unique and equals `tsCoord`.
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

-- R2: the forward gap equals the reactant-surface energy at the crossing point.
theorem gapReactant_eq_surface {lam dG : ℝ} (hlam : lam ≠ 0) :
    gapReactant lam (-dG) = reactantSurface lam (tsCoord lam (-dG)) := by
  have h4 : (4 * lam : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hlam
  have h2 : (2 * lam : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hlam
  unfold gapReactant reactantSurface tsCoord
  field_simp
  ring

-- R3: the two gaps differ exactly by the driving force (reverse-barrier identity).
theorem gapProduct_sub_gapReactant {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    gapProduct lam x - gapReactant lam x = x := by
  have h4 : (4 * lam : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hlam
  unfold gapProduct gapReactant
  field_simp
  ring

-- R4: Hammond monotonicity — more driving force, earlier (more reactant-like) TS.
theorem tsCoord_antitone {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ} (h : x₁ < x₂) :
    tsCoord lam x₂ < tsCoord lam x₁ := by
  unfold tsCoord
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 2 * lam)]
  linarith

-- R5: degenerate curvature zero: the coordinate is constant (division-by-zero convention).
theorem tsCoord_zero_lam (x : ℝ) : tsCoord 0 x = 0 := by unfold tsCoord; norm_num

-- R6: negative curvature reverses the direction (sharpness witness, first branch).
theorem tsCoord_increasing_of_neg {lam : ℝ} (hlam : lam < 0) {x₁ x₂ : ℝ} (h : x₁ < x₂) :
    tsCoord lam x₁ < tsCoord lam x₂ := by
  unfold tsCoord
  rw [div_lt_div_right_of_neg (by linarith : (2 : ℝ) * lam < 0)]
  linarith

-- R7: sharpness witnesses in explicit existential form.
theorem exists_direction_reversal_of_neg {lam : ℝ} (hlam : lam < 0) :
    ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧ tsCoord lam x₁ < tsCoord lam x₂ :=
  ⟨0, 1, by norm_num, tsCoord_increasing_of_neg hlam (by norm_num)⟩

theorem exists_direction_reversal_of_eq :
    ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧ ¬ (tsCoord 0 x₂ < tsCoord 0 x₁) := by
  refine ⟨0, 1, by norm_num, ?_⟩
  rw [tsCoord_zero_lam, tsCoord_zero_lam]
  norm_num

-- R8: structural regime — the TS lies strictly between the two wells.
theorem tsCoord_mem_iff {lam x : ℝ} (hlam : 0 < lam) :
    0 < tsCoord lam x ∧ tsCoord lam x < 1 ↔ -lam < x ∧ x < lam := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  unfold tsCoord
  rw [div_pos_iff_of_pos_right h2, div_lt_one h2]
  constructor
  · intro ⟨h₁, h₂⟩; exact ⟨by linarith, by linarith⟩
  · intro ⟨h₁, h₂⟩; exact ⟨by linarith, by linarith⟩

-- R9: Brønsted sign characterizes the regime.
theorem bronsted_pos_iff {lam x : ℝ} (hlam : 0 < lam) : 0 < bronsted lam x ↔ x < lam := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  unfold bronsted
  rw [div_pos_iff_of_pos_right h2]
  constructor <;> intro h <;> linarith

theorem bronsted_neg_iff {lam x : ℝ} (hlam : 0 < lam) : bronsted lam x < 0 ↔ lam < x := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  unfold bronsted
  rw [div_lt_iff₀ h2]
  constructor <;> intro h <;> linarith

-- R10: exact Leffler finite-difference identity (no mean value theorem: it is a quadratic).
theorem leffler_finite_difference {lam x₁ x₂ : ℝ} (hlam : 0 < lam) :
    gapReactant lam x₂ - gapReactant lam x₁
      = -bronsted lam ((x₁ + x₂) / 2) * (x₂ - x₁) := by
  have h4 : (4 * lam : ℝ) ≠ 0 := by positivity
  have h2 : (2 * lam : ℝ) ≠ 0 := by positivity
  unfold gapReactant bronsted
  field_simp
  ring

-- R11: energy–structure correspondence: TS closer in energy to the reactant well
--      exactly when it is reactant-like (exergonic).
theorem gap_compare_iff {lam x : ℝ} (hlam : 0 < lam) :
    gapReactant lam x < gapProduct lam x ↔ 0 < x := by
  have h : gapProduct lam x - gapReactant lam x = x :=
    gapProduct_sub_gapReactant (ne_of_gt hlam) x
  constructor
  · intro hlt; linarith
  · intro hlt; linarith

-- R12: reverse-reaction symmetry: the reverse reaction of driving force `x` is the
--      forward reaction of driving force `-x`, and the coordinate mirrors about `1/2`.
theorem tsCoord_neg {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    tsCoord lam (-x) = 1 - tsCoord lam x := by
  unfold tsCoord
  field_simp
  ring

theorem gapProduct_eq_gapReactant_neg (lam x : ℝ) :
    gapProduct lam x = gapReactant lam (-x) := by
  unfold gapProduct gapReactant; ring

-- R13: thermoneutral point.
theorem tsCoord_zero {lam : ℝ} (hlam : lam ≠ 0) : tsCoord lam 0 = 1 / 2 := by
  unfold tsCoord
  field_simp
  ring

-- R14: rational-side computable classifier for instances.
def tsCoordQ (lam x : ℚ) : ℚ := (lam - x) / (2 * lam)

inductive HZone where
  | early | half | late | atReactant | atProduct | beyondReactant | beyondProduct
  deriving DecidableEq, Repr

def hammondZoneQ (lam x : ℚ) : HZone :=
  if x = lam then HZone.atReactant
  else if x = -lam then HZone.atProduct
  else if x < -lam then HZone.beyondProduct
  else if lam < x then HZone.beyondReactant
  else if x = 0 then HZone.half
  else if 0 < x then HZone.early
  else HZone.late

example : tsCoordQ 1 0 = 1 / 2 := by norm_num [tsCoordQ]
example : hammondZoneQ 1 (3 / 4) = HZone.early := by norm_num [hammondZoneQ]
example : hammondZoneQ 1 (-1 / 2) = HZone.late := by norm_num [hammondZoneQ]
example : hammondZoneQ 1 1 = HZone.atReactant := by norm_num [hammondZoneQ]
example : hammondZoneQ (6 / 5) (12 / 5) = HZone.beyondReactant := by
  norm_num [hammondZoneQ]

-- R15: transfer lemma shape for the ℚ classifier (cast to ℝ).
theorem tsCoordQ_cast (lam x : ℚ) :
    ((tsCoordQ lam x : ℚ) : ℝ) = tsCoord (lam : ℝ) (x : ℝ) := by
  unfold tsCoordQ tsCoord
  push_cast
  ring

end PhotoLean.Hammond
