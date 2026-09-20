/-
Hammond milestone — API probe (topic D+G): characterizing the seven zones of the `if`-chain
classifier, and non-vacuity witnesses for the milestone's central definitions.

Recipe (uniform, and the reason it works): `unfold hammondZone`, then
`split_ifs with h1 h2 h3 h4 h5 h6`, which produces exactly the seven leaves of the chain and
hands each leaf the accumulated (negated) branch tests.  Every leaf is then closed by one of

    exact iff_of_true rfl <proof of the characterization>
    exact iff_of_false (by decide) <proof of its negation>

`by decide` discharges the constructor inequality (`HZone.atReactant ≠ HZone.early` &c.)
from the derived `DecidableEq`; the arithmetic side is `linarith`.

Measured: `unfold; split_ifs <;> simp_all <;> linarith` FAILS (`linarith` cannot see through
the `False ↔ …` shape that `simp_all` leaves), `unfold; split_ifs <;> simp_all <;> omega`
FAILS (`omega` does not support `ℝ`), and `simp [hammondZone]` alone FAILS (it leaves the
whole `if`-chain untouched).  `decide` cannot help on the ℝ side at all (no computable
`Decidable` instance for `ℝ`'s order); on the ℚ side it needs `norm_num` — see
`hammond-api-rat-compute.lean`.

Running:  proofs/scripts/lake env lean theories/hammond/probes/hammond-api-zone-char.lean
Status:   0 errors / 0 warnings.
-/
import Mathlib

namespace PhotoLean.Hammond.ProbeZone

noncomputable def tsCoord (lam x : ℝ) : ℝ := (lam - x) / (2 * lam)

/-- The reaction region: driving force strictly between the two wells. -/
def ReactionRegion (lam x : ℝ) : Prop := -lam < x ∧ x < lam

/-- Reactant-like: transition-state coordinate below the thermoneutral value `1 / 2`. -/
def ReactantLike (lam x : ℝ) : Prop := tsCoord lam x < 1 / 2

/-- Product-like: transition-state coordinate above `1 / 2`. -/
def ProductLike (lam x : ℝ) : Prop := 1 / 2 < tsCoord lam x

/-- The Hammond descriptor: the coordinate is strictly antitone in the driving force. -/
def HammondDescriptor (lam : ℝ) : Prop := ∀ x₁ x₂ : ℝ, x₁ < x₂ → tsCoord lam x₂ < tsCoord lam x₁

/-- Zone classification of the reaction-coordinate picture. -/
inductive HZone where
  | early | half | late | atReactant | atProduct | beyondReactant | beyondProduct
  deriving DecidableEq, Repr

/-- The seven-branch classifier. -/
noncomputable def hammondZone (lam x : ℝ) : HZone :=
  if x = lam then HZone.atReactant
  else if x = -lam then HZone.atProduct
  else if x < -lam then HZone.beyondProduct
  else if lam < x then HZone.beyondReactant
  else if x = 0 then HZone.half
  else if 0 < x then HZone.early
  else HZone.late

/-! ## Supporting names used by the leaf closures (all `#check`ed) -/

#check @iff_of_true
#check @iff_of_false
#check @le_of_not_gt
#check @lt_of_le_of_ne
#check @Ne.symm

/-! ## Task D — the zone characterization lemmas (all seven, `0 < lam`) -/

/-- The requested instance: `early` is exactly the open interval `(0, lam)`. -/
theorem hammondZone_eq_early_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.early ↔ 0 < x ∧ x < lam := by
  unfold hammondZone
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rintro ⟨-, hx⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨-, hx⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_true rfl ⟨h6, lt_of_le_of_ne (le_of_not_gt h4) h1⟩
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)

/-- The `early` characterization, shortest form: the same proof with the two leaf closures
factored out through `first` (28 lines -> 7). -/
theorem hammondZone_eq_early_iff_shortest {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.early ↔ 0 < x ∧ x < lam := by
  unfold hammondZone
  split_ifs with h1 h2 h3 h4 h5 h6 <;>
    first
      | exact iff_of_true rfl ⟨h6, lt_of_le_of_ne (le_of_not_gt h4) h1⟩
      | exact iff_of_false (by decide) (by rintro ⟨hx, hy⟩; linarith)

/-- The `late` zone is exactly `(-lam, 0)`.  In the last leaf both strictness steps come from
a "≤ + ≠" splitting: `-lam < x` from `h3 : ¬ x < -lam` plus `h2 : ¬ x = -lam`, and
`x < 0` from `h6 : ¬ 0 < x` plus `h5 : ¬ x = 0`. -/
theorem hammondZone_eq_late_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.late ↔ -lam < x ∧ x < 0 := by
  unfold hammondZone
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rintro ⟨-, hx⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨-, hx⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨-, hx⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨-, hx⟩; linarith)
  · exact iff_of_true rfl
      ⟨lt_of_le_of_ne (le_of_not_gt h3) (Ne.symm h2), lt_of_le_of_ne (le_of_not_gt h6) h5⟩

/-- The thermoneutral point.  Note the last leaf: `h5 : ¬ x = 0` is *already* the negation of
the characterization, so it is used directly — a `rintro rfl; linarith` there fails, because
after the substitution the hypothesis becomes `¬ (0 : ℝ) < 0`, which `linarith` cannot turn
into a contradiction (it is a propositional, not a linear, absurdity). -/
theorem hammondZone_eq_half_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.half ↔ x = 0 := by
  unfold hammondZone
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_true rfl h5
  · exact iff_of_false (by decide) (ne_of_gt h6)
  · exact iff_of_false (by decide) h5

/-- The reactant well itself.  **No hypothesis**: the statement is true for every `lam`
(at `lam = 0` the first branch still absorbs `x = 0 = lam`).  Adding `(hlam : 0 < lam)`
here would be flagged by `linter.unusedVariables` — measured, see the API notes. -/
theorem hammondZone_eq_atReactant_iff (lam x : ℝ) :
    hammondZone lam x = HZone.atReactant ↔ x = lam := by
  unfold hammondZone
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_true rfl h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1

/-- The product well itself.  Needs `0 < lam` (at `lam = 0` the wells coincide with the
`atReactant` branch, so the statement would be false). -/
theorem hammondZone_eq_atProduct_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.atProduct ↔ x = -lam := by
  unfold hammondZone
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rw [h1]; linarith)
  · exact iff_of_true rfl h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2

/-- Beyond the product well. -/
theorem hammondZone_eq_beyondProduct_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.beyondProduct ↔ x < -lam := by
  unfold hammondZone
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rw [h1]; linarith)
  · exact iff_of_false (by decide) (by rw [h2]; linarith)
  · exact iff_of_true rfl h3
  · exact iff_of_false (by decide) h3
  · exact iff_of_false (by decide) h3
  · exact iff_of_false (by decide) h3
  · exact iff_of_false (by decide) h3

/-- Beyond the reactant well. -/
theorem hammondZone_eq_beyondReactant_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.beyondReactant ↔ lam < x := by
  unfold hammondZone
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rw [h1]; linarith)
  · exact iff_of_false (by decide) (by rw [h2]; linarith)
  · exact iff_of_false (by decide) (by linarith)
  · exact iff_of_true rfl h4
  · exact iff_of_false (by decide) h4
  · exact iff_of_false (by decide) h4
  · exact iff_of_false (by decide) h4

/-! ## Reactant-like / product-like in driving-force coordinates -/

/-- `ReactantLike` is exactly "positive driving force". -/
theorem reactantLike_iff {lam x : ℝ} (hlam : 0 < lam) :
    ReactantLike lam x ↔ 0 < x := by
  unfold ReactantLike tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_lt_iff₀ h2]
  constructor <;> intro h <;> linarith

/-- `ProductLike` is exactly "negative driving force". -/
theorem productLike_iff {lam x : ℝ} (hlam : 0 < lam) :
    ProductLike lam x ↔ x < 0 := by
  unfold ProductLike tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [lt_div_iff₀ h2]
  constructor <;> intro h <;> linarith

/-- The descriptor holds on a positive-curvature surface (this is the Hammond claim). -/
theorem hammondDescriptor_of_pos {lam : ℝ} (hlam : 0 < lam) : HammondDescriptor lam := by
  intro x₁ x₂ h
  unfold tsCoord
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 2 * lam)]
  linarith

/-! ## Structural-regime lemmas committed to by the statement skeleton -/

/-- The coordinate lies strictly between the two wells exactly in the reaction region.
Recipe: `div_pos_iff_of_pos_right` (for `0 < tsCoord`) + `div_lt_one` (for `tsCoord < 1`),
both with the positive denominator `2 * lam`. -/
theorem tsCoord_mem_iff {lam x : ℝ} (hlam : 0 < lam) :
    0 < tsCoord lam x ∧ tsCoord lam x < 1 ↔ ReactionRegion lam x := by
  unfold ReactionRegion tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_pos_iff_of_pos_right h2, div_lt_one h2]
  constructor <;> intro h <;> exact ⟨by linarith, by linarith⟩

/-- The Hammond regime forces a positive curvature. -/
theorem reactionRegion_pos {lam x : ℝ} (h : ReactionRegion lam x) : 0 < lam := by
  unfold ReactionRegion at h
  linarith [h.1, h.2]

/-- With non-positive curvature the reaction region is empty. -/
theorem not_reactionRegion_of_nonpos {lam x : ℝ} (hlam : lam ≤ 0) :
    ¬ ReactionRegion lam x := by
  intro h
  unfold ReactionRegion at h
  linarith [h.1, h.2]

/-! ## Task G — non-vacuity witnesses -/

/-- `tsCoord 0 x = 0` (the `x / 0 = 0` convention), used by the failure-branch witnesses. -/
theorem tsCoord_zero_lam (x : ℝ) : tsCoord 0 x = 0 := by
  unfold tsCoord
  norm_num

/-- There is a reactant-like driving force.  Witness `x = lam / 2`, where
`tsCoord lam (lam / 2) = 1 / 4 < 1 / 2`. -/
theorem exists_reactantLike {lam : ℝ} (hlam : 0 < lam) :
    ∃ x : ℝ, tsCoord lam x < 1 / 2 := by
  refine ⟨lam / 2, ?_⟩
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_lt_iff₀ h2]
  linarith

/-- There is a product-like driving force (witness `x = -lam / 2`). -/
theorem exists_productLike {lam : ℝ} (hlam : 0 < lam) :
    ∃ x : ℝ, 1 / 2 < tsCoord lam x := by
  refine ⟨-lam / 2, ?_⟩
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [lt_div_iff₀ h2]
  linarith

/-- The reaction region is inhabited (witness `x = 0`). -/
theorem exists_reactionRegion {lam : ℝ} (hlam : 0 < lam) : ∃ x : ℝ, ReactionRegion lam x :=
  ⟨0, by unfold ReactionRegion; constructor <;> linarith⟩

/-- The same, in the expanded (non-`def`) form required by the plan. -/
theorem exists_in_reactionRegion {lam : ℝ} (hlam : 0 < lam) :
    ∃ x : ℝ, -lam < x ∧ x < lam :=
  ⟨0, by constructor <;> linarith⟩

/-- The descriptor is not vacuous: it has an instance of its conclusion (witnesses `0, 1`). -/
theorem exists_descriptor_witness {lam : ℝ} (hlam : 0 < lam) :
    ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧ tsCoord lam x₂ < tsCoord lam x₁ :=
  ⟨0, 1, by norm_num, hammondDescriptor_of_pos hlam 0 1 (by norm_num)⟩

/-- The failure branch: at `lam = 0` the coordinate is constant, so the descriptor's
conclusion already fails for the witnesses `0 < 1`. -/
theorem exists_direction_reversal_at_zero :
    ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧ ¬ (tsCoord 0 x₂ < tsCoord 0 x₁) := by
  refine ⟨0, 1, by norm_num, ?_⟩
  rw [tsCoord_zero_lam, tsCoord_zero_lam]
  norm_num

/-- Sharper form: `HammondDescriptor 0` is outright false (the direction-reversal witness
is not an isolated accident). -/
theorem not_hammondDescriptor_zero : ¬ HammondDescriptor 0 := by
  intro h
  have h01 : tsCoord 0 1 < tsCoord 0 0 := h 0 1 (by norm_num)
  rw [tsCoord_zero_lam, tsCoord_zero_lam] at h01
  norm_num at h01

end PhotoLean.Hammond.ProbeZone
