/-
PhotoLean.SymmetryFactor.Instances — milestone F4, the instance / verdict layer.

Named verdict rows at concrete parameters, decided by the kernel through the ℚ layer
(`norm_num [tsCoordZeroQ]`) and tied to the ℝ closed form by the F3 cast bridges. As everywhere in
this repository, an instance row is a statement **about the printed numbers** under the declared
model — nothing here measures an electrode, and a row is only as good as the reading of the model
it instantiates (plan §13).

The two honest headlines:
* `inst_conflation_falsified` — the adjudication as ONE kernel fact: the β = 1/2 reading fails at
  `(kr, kp) = (1², 2²) = (1, 4)` in both layers (ℚ decision and ℝ closed form) while the force
  constants are positive and unequal. This is the row the H1 verdict cites, with the literature
  anchors in its docstring (LITERATURE S1 practice locus, S2 IUPAC warning).
* `inst_symmetric_half` — the same reading HOLDS at `(1², 1²)`, and by the F2 sharp equivalence it
  holds throughout the equal-curvature family: the conflated reading is a special case, and the
  special case is exactly the textbook picture. That is why it survives.

Non-vacuity discipline (the M1 lesson of the 2026-09-21 review-fix round, applied prospectively):
`inst_nonvacuous_both_readings` pins BOTH readings at concrete positive curvatures in one row —
no bare `∃`-row here that a degenerate parameter could satisfy for free (at `kr = kp = 0` the
totalized closed form is `0`, and `BetaHalfReading 0 0` is FALSE — the verdicts are pinned where
the physics is).

Statement authority: `theories/SymmetryFactor/probes/SymmetryFactor-statement-skeleton.lean` § F4.
There is no unproved placeholder and no custom axiomatic declaration anywhere in this file; no
runtime evaluation command appears in it — every row is a proof term closed by `norm_num` or by
the delivered theorems. The `#print axioms` gate of every theorem below lists at most `propext`,
`Classical.choice`, `Quot.sound`.
-/
import PhotoLean.SymmetryFactor.RatModel
import PhotoLean.SymmetryFactor.Sharp

set_option autoImplicit false

namespace PhotoLean

namespace SymmetryFactor

/-! ## F4 — instances and verdicts -/

/-- Verdict row, product well stiffer (`kr, kp = 1², 2²`): `q‡₀ = 2/3`, late side. A fact about
the printed numbers, decided by `norm_num`. -/
theorem inst_stiffProduct_lateTS :
    tsCoordZeroQ 1 2 = 2 / 3 ∧ (1 : ℚ) / 2 < tsCoordZeroQ 1 2 := by
  constructor <;> norm_num [tsCoordZeroQ]

/-- Verdict row, reactant well stiffer (`kr, kp = 2², 1²`): `q‡₀ = 1/3`, early side. -/
theorem inst_stiffReactant_earlyTS :
    tsCoordZeroQ 2 1 = 1 / 3 ∧ tsCoordZeroQ 2 1 < (1 : ℚ) / 2 := by
  constructor <;> norm_num [tsCoordZeroQ]

/-- Verdict row, symmetric (`kr = kp = 1²`): `q‡₀ = 1/2` — the conflated reading holds here, and
this is the whole equal-curvature family by the F2 iff. -/
theorem inst_symmetric_half : tsCoordZeroQ 1 1 = 1 / 2 ∧ BetaHalfQ 1 1 := by
  constructor
  · norm_num [tsCoordZeroQ]
  · rw [betaHalfQ_iff (by norm_num) (by norm_num)]

/-- **The adjudication as one kernel fact**: the β = 1/2 reading fails at `(1², 2²)` in BOTH
layers (ℚ decision and ℝ closed form) while the force constants are positive and unequal. This is
the row the H1 verdict cites.

Literature anchors (`theories/SymmetryFactor/LITERATURE.md`): S1 — the working value "usually both
taken to be equal to 0.5" (Cabras–Oancea–Salvadori, arXiv 2104.05424 §2.1 after eq. (8), full text
read first-hand); S2 — IUPAC Technical Report 2014, printed pp. 255–256, predicting "large
deviations of β from 0.5" when the two force constants differ, and p. 257, "the numerical value of
the transfer coefficient α can by no means be assumed". The refuted object is the UNQUALIFIED
reading; the verdict boundary (`↔ kr = kp`) is `betaHalf_iff_equalForceConstants`. -/
theorem inst_conflation_falsified :
    ¬ BetaHalfQ 1 2 ∧ ¬ BetaHalfReading (1 : ℝ) 4 := by
  constructor
  · intro h
    rw [betaHalfQ_iff (by norm_num) (by norm_num)] at h
    norm_num at h
  · exact betaHalf_falsified_by_unequal

/-- Non-vacuity of both readings, pinned at concrete positive curvatures (the M1 lesson: no
bare `∃`-row that a degenerate parameter satisfies for free): the conflated reading holds at
`(1,1)` and fails at `(1,4)`. -/
theorem inst_nonvacuous_both_readings :
    BetaHalfReading (1 : ℝ) 1 ∧ ¬ BetaHalfReading (1 : ℝ) 4 := by
  constructor
  · have h : BetaHalfReading 1 1 ↔ (1 : ℝ) = 1 :=
      betaHalf_iff_equalForceConstants (by norm_num) (by norm_num)
    exact h.mpr rfl
  · exact betaHalf_falsified_by_unequal

end SymmetryFactor

end PhotoLean
