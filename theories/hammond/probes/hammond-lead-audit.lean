/-
Lead statement audit for the Hammond skeleton (Sprint 1).
English: after two false statements were caught in the first skeleton draft, this probe spot-checks
EVERY non-definitional skeleton statement at concrete rational values, including the *negative*
controls (the "iff"/predicate statements are checked at a point where they must fail, so that a
tautology cannot pass). Definitions are copied inline so the probe stays self-contained.
-/
import Mathlib

namespace PhotoLean.Hammond

noncomputable def reactantSurface (lam q : ℝ) : ℝ := lam * q ^ 2
noncomputable def productSurface (lam dG q : ℝ) : ℝ := lam * (q - 1) ^ 2 + dG
noncomputable def tsCoord (lam x : ℝ) : ℝ := (lam - x) / (2 * lam)
noncomputable def gapReactant (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)
noncomputable def gapProduct (lam x : ℝ) : ℝ := (lam + x) ^ 2 / (4 * lam)
noncomputable def lefflerSecant (lam x₁ x₂ : ℝ) : ℝ :=
  -(gapReactant lam x₂ - gapReactant lam x₁) / (x₂ - x₁)
def ReactionRegion (lam x : ℝ) : Prop := -lam < x ∧ x < lam
def ReactantLike (lam x : ℝ) : Prop := tsCoord lam x < 1 / 2
def ProductLike (lam x : ℝ) : Prop := 1 / 2 < tsCoord lam x
def HammondConforms (lam x : ℝ) : Prop := 0 < lam ∧ ReactionRegion lam x
def HammondDescriptor (lam : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, x₁ < x₂ → tsCoord lam x₂ < tsCoord lam x₁

inductive HZone where
  | early | half | late | atReactant | atProduct | beyondReactant | beyondProduct
  deriving DecidableEq, Repr

noncomputable def hammondZone (lam x : ℝ) : HZone :=
  if x = lam then HZone.atReactant
  else if x = -lam then HZone.atProduct
  else if x < -lam then HZone.beyondProduct
  else if lam < x then HZone.beyondReactant
  else if x = 0 then HZone.half
  else if 0 < x then HZone.early
  else HZone.late

-- ── H1: crossing geometry at `lam = 3`, `dG = 1` (i.e. `x = -1`) ──
example : reactantSurface 3 (tsCoord 3 (-1)) = productSurface 3 1 (tsCoord 3 (-1)) := by
  norm_num [reactantSurface, productSurface, tsCoord]
example : gapReactant 3 (-1) = reactantSurface 3 (tsCoord 3 (-1)) := by
  norm_num [gapReactant, reactantSurface, tsCoord]
-- corrected (well-referenced) form: the reverse barrier is measured from the product well
example : gapProduct 3 (-1) = productSurface 3 1 (tsCoord 3 (-1)) - 1 := by
  norm_num [gapProduct, productSurface, tsCoord]
-- negative control: the surfaces differ away from the crossing point
example : ¬ (reactantSurface 3 0 = productSurface 3 1 0) := by
  norm_num [reactantSurface, productSurface]
example : gapProduct 3 1 - gapReactant 3 1 = 1 := by norm_num [gapProduct, gapReactant]
example : gapProduct 3 1 = gapReactant 3 (-1) := by norm_num [gapProduct, gapReactant]
example : tsCoord 3 (-1) = 1 - tsCoord 3 1 := by norm_num [tsCoord]
example : tsCoord 3 0 = 1 / 2 := by norm_num [tsCoord]
example : tsCoord 0 5 = 0 := by norm_num [tsCoord]
example : tsCoord 3 3 = 0 := by norm_num [tsCoord]

-- ── H1: regime predicate, with both directions ──
example : (0 < tsCoord 3 1 ∧ tsCoord 3 1 < 1) ↔ ReactionRegion 3 1 := by
  norm_num [tsCoord, ReactionRegion]
example : ¬ (0 < tsCoord 3 5 ∧ tsCoord 3 5 < 1) ∧ ¬ ReactionRegion 3 5 := by
  norm_num [tsCoord, ReactionRegion]
example : ¬ ReactionRegion (-1) 0 := by norm_num [ReactionRegion]

-- ── H1: classifier semantics at `lam = 3`, one witness plus one negative control per zone ──
example : hammondZone 3 1 = HZone.early := by
  simp only [hammondZone, if_neg (by norm_num : ¬((1 : ℝ) = 3)),
    if_neg (by norm_num : ¬((1 : ℝ) = -3)), if_neg (by norm_num : ¬((1 : ℝ) < -3)),
    if_neg (by norm_num : ¬((3 : ℝ) < 1)), if_neg (by norm_num : ¬((1 : ℝ) = 0)), if_pos (by norm_num : (0 : ℝ) < 1)]
example : hammondZone 3 0 = HZone.half := by
  unfold hammondZone
  split_ifs <;> first | rfl | decide | norm_num at *
example : hammondZone 3 (-1) = HZone.late := by
  simp only [hammondZone, if_neg (by norm_num : ¬((-1 : ℝ) = 3)),
    if_neg (by norm_num : ¬((-1 : ℝ) = -3)), if_neg (by norm_num : ¬((-1 : ℝ) < -3)),
    if_neg (by norm_num : ¬((3 : ℝ) < -1)), if_neg (by norm_num : ¬((-1 : ℝ) = 0)),
    if_neg (by norm_num : ¬((0 : ℝ) < -1))]
example : hammondZone 3 3 = HZone.atReactant := by
  unfold hammondZone
  split_ifs <;> first | rfl | decide | norm_num at *
example : hammondZone 3 (-3) = HZone.atProduct := by
  unfold hammondZone
  split_ifs <;> first | rfl | decide | norm_num at *
example : hammondZone 3 5 = HZone.beyondReactant := by
  simp only [hammondZone, if_neg (by norm_num : ¬((5 : ℝ) = 3)),
    if_neg (by norm_num : ¬((5 : ℝ) = -3)), if_neg (by norm_num : ¬((5 : ℝ) < -3)),
    if_pos (by norm_num : (3 : ℝ) < 5)]
example : hammondZone 3 (-5) = HZone.beyondProduct := by
  simp only [hammondZone, if_neg (by norm_num : ¬((-5 : ℝ) = 3)),
    if_neg (by norm_num : ¬((-5 : ℝ) = -3)), if_pos (by norm_num : (-5 : ℝ) < -3)]
-- negative controls for the zone iff-lemmas: these points must NOT be classified as early
example : ¬ (hammondZone 3 5 = HZone.early) := by
  unfold hammondZone
  split_ifs <;> first | rfl | decide | norm_num at *
example : ¬ (hammondZone 3 (-1) = HZone.early) := by
  unfold hammondZone
  split_ifs <;> first | rfl | decide | norm_num at *

-- ── H2: the criterion statements ──
example : tsCoord 3 5 < tsCoord 3 1 := by norm_num [tsCoord]
example : ReactantLike 3 1 ↔ (0 : ℝ) < 1 := by norm_num [ReactantLike, tsCoord]
example : ProductLike 3 (-1) ↔ (-1 : ℝ) < 0 := by norm_num [ProductLike, tsCoord]
example : gapReactant 3 1 < gapProduct 3 1 ↔ (0 : ℝ) < 1 := by
  norm_num [gapReactant, gapProduct]
-- negative control for the energy–structure correspondence (exergonic side is the relevant one)
example : ¬ (gapReactant 3 (-1) < gapProduct 3 (-1)) := by norm_num [gapReactant, gapProduct]
example : lefflerSecant 3 1 5 = tsCoord 3 3 := by norm_num [lefflerSecant, gapReactant, tsCoord]
example : lefflerSecant 3 (-1) 1 = tsCoord 3 0 := by norm_num [lefflerSecant, gapReactant, tsCoord]
example : (0 < lefflerSecant 3 1 5 ∧ lefflerSecant 3 1 5 < 1) ↔ ReactionRegion 3 3 := by
  norm_num [lefflerSecant, gapReactant, ReactionRegion]
example : tsCoord 3 5 < 0 ↔ (3 : ℝ) < 5 := by norm_num [tsCoord]
example : ¬ (0 < lefflerSecant 3 (5 / 2) 5 ∧ lefflerSecant 3 (5 / 2) 5 < 1) := by
  norm_num [lefflerSecant, gapReactant]
-- verdict characterized by the classifier (the corrected statement), both directions
example : HammondConforms 3 1 ↔
    (hammondZone 3 1 = HZone.early ∨ hammondZone 3 1 = HZone.half ∨
      hammondZone 3 1 = HZone.late) := by
  have hz : hammondZone 3 1 = HZone.early := by
    unfold hammondZone
    split_ifs <;> first | rfl | decide | norm_num at *
  rw [hz]
  norm_num [HammondConforms, ReactionRegion]
example : ¬ HammondConforms 3 5 := by norm_num [HammondConforms, ReactionRegion]

-- ── H3: sharpness witnesses and the failure directions ──
example : ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧ tsCoord (-3) x₁ < tsCoord (-3) x₂ :=
  ⟨0, 1, by norm_num, by norm_num [tsCoord]⟩
example : ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧ ¬ (tsCoord 0 x₂ < tsCoord 0 x₁) := by
  refine ⟨0, 1, by norm_num, ?_⟩
  norm_num [tsCoord]
example : ¬ HammondDescriptor (-3) := by
  intro h
  have := h 0 1 (by norm_num)
  norm_num [tsCoord] at this
example : ¬ HammondDescriptor 0 := by
  intro h
  have := h 0 1 (by norm_num)
  norm_num [tsCoord] at this

-- ── H5b: instance verdicts (exact rationals, independent of the delivered theorems) ──
example : tsCoord (6 / 5) (1 / 20) = 23 / 48 := by norm_num [tsCoord]
example : tsCoord (6 / 5) (12 / 5) = -(1 / 2) := by norm_num [tsCoord]
example : tsCoord (1 / 4) (11 / 10) = -(17 / 10) := by norm_num [tsCoord]
example : lefflerSecant (6 / 5) (3 / 5) (12 / 5) = -(1 / 8) := by
  norm_num [lefflerSecant, gapReactant]
example : tsCoord (6 / 5) (12 / 5) < tsCoord (6 / 5) (3 / 5) := by norm_num [tsCoord]
example : HammondConforms (6 / 5) (1 / 20) := by norm_num [HammondConforms, ReactionRegion]
example : ¬ HammondConforms (6 / 5) (12 / 5) := by norm_num [HammondConforms, ReactionRegion]
example : ¬ HammondConforms (1 / 4) (11 / 10) := by norm_num [HammondConforms, ReactionRegion]
example : ¬ HammondConforms 1 1 := by norm_num [HammondConforms, ReactionRegion]
example : ¬ ReactionRegion (-(1 / 2)) 1 := by norm_num [ReactionRegion]

end PhotoLean.Hammond
