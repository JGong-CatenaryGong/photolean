/-
PhotoLean.SymmetryFactor.Sharp — milestone F2, the sharp conditions: **the adjudication**.

The headline is the sharp equivalence

    BetaHalfReading kr kp ↔ kr = kp        (0 < kr, 0 < kp)

the machine-checked content of the IUPAC Technical Report's warning that the Butler–Volmer
symmetry factor deviates from `1/2` when the two force constants differ (LITERATURE S2, printed
pp. 255–256), against the unqualified working value "usually both taken to be equal to 0.5"
(LITERATURE S1). The falsification side is delivered as kernel-checked witnesses, not as a
negated quantifier alone: `(kr,kp) = (1,4) ↦ 2/3 ≠ 1/2` and `(4,1) ↦ 1/3` — the crossing sits on
the side of the SOFTER well, a late transition state at zero driving force when the product well
is stiffer (`tsCoordZero_gt_half_iff_stiffProduct`).

The three tie-back rows put this theory on the shared kernel: at equal curvature the closed form
IS `Kernel.tsCoord lam 0` and IS `BEP.transfer lam 0` (both `= 1/2`, the latter by the delivered
`BEP.transfer_thermoneutral`), and `BetaHalfReading` holds throughout the equal-curvature family —
so the conflated reading is not a mistake but a **special case**, and the special case is exactly
the picture every textbook draws. That is the adjudication: the identification is decided, with
its exact validity boundary.

Statement authority: `theories/SymmetryFactor/probes/SymmetryFactor-statement-skeleton.lean` § F2.
There is no unproved placeholder and no custom axiomatic declaration anywhere in this file. The
`#print axioms` gate of every theorem below lists at most `propext`, `Classical.choice`,
`Quot.sound`.
-/
import PhotoLean.SymmetryFactor.Criterion
import PhotoLean.Kernel
import PhotoLean.BEP.Criterion

set_option autoImplicit false

namespace PhotoLean

namespace SymmetryFactor

/-! ## F2 — sharp conditions and the verdicts -/

/-- **The verdict (headline).** The β = 1/2 symmetry-factor reading coincides with the structural
transfer coefficient at thermoneutrality **exactly when the two force constants are equal**. The
equal-curvature Marcus picture is precisely the regime where the conflated reading survives —
which is why it survives (IUPAC TR 2014 pp. 255–256 predicts the deviation; LITERATURE S2). -/
theorem betaHalf_iff_equalForceConstants {kr kp : ℝ} (hkr : 0 < kr) (hkp : 0 < kp) :
    BetaHalfReading kr kp ↔ kr = kp := by
  unfold BetaHalfReading tsCoordZero
  have hne : Real.sqrt kr + Real.sqrt kp ≠ 0 :=
    ne_of_gt (add_pos (Real.sqrt_pos.mpr hkr) (Real.sqrt_pos.mpr hkp))
  rw [div_eq_iff hne]
  constructor
  · intro h
    have h' : Real.sqrt kr = Real.sqrt kp := by linarith
    rw [← Real.sq_sqrt (le_of_lt hkr), ← Real.sq_sqrt (le_of_lt hkp), h']
  · intro h
    rw [h]
    ring

/-- Kernel-checked witness, product well stiffer: `(kr, kp) = (1, 4)` gives `q‡₀ = 2/3`. -/
theorem tsCoordZero_one_four : tsCoordZero 1 4 = 2 / 3 := by
  unfold tsCoordZero
  rw [Real.sqrt_one, show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Kernel-checked witness, reactant well stiffer: `(kr, kp) = (4, 1)` gives `q‡₀ = 1/3` — the
direction asymmetry: the crossing sits on the side of the *softer* well. -/
theorem tsCoordZero_four_one : tsCoordZero 4 1 = 1 / 3 := by
  unfold tsCoordZero
  rw [Real.sqrt_one, show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The conflated reading, refuted at a kernel-checked parameter pair. -/
theorem betaHalf_falsified_by_unequal : ¬ BetaHalfReading 1 4 := by
  intro h
  rw [BetaHalfReading, tsCoordZero_one_four] at h
  norm_num at h

/-- The conflated reading is not a theorem of the model class: it fails for some admissible
positive force constants. -/
theorem not_betaHalf_universal :
    ¬ ∀ kr kp : ℝ, 0 < kr → 0 < kp → BetaHalfReading kr kp :=
  fun h => betaHalf_falsified_by_unequal (h 1 4 (by norm_num) (by norm_num))

/-- Late transition state at ZERO driving force, exactly when the product well is stiffer — a
Hammond-style structural verdict that needs no driving force at all. -/
theorem tsCoordZero_gt_half_iff_stiffProduct {kr kp : ℝ} (hkr : 0 < kr) (hkp : 0 < kp) :
    (1 : ℝ) / 2 < tsCoordZero kr kp ↔ kr < kp := by
  unfold tsCoordZero
  have hne : 0 < Real.sqrt kr + Real.sqrt kp :=
    add_pos (Real.sqrt_pos.mpr hkr) (Real.sqrt_pos.mpr hkp)
  rw [lt_div_iff₀ hne]
  have h1 : (1 : ℝ) / 2 * (Real.sqrt kr + Real.sqrt kp) < Real.sqrt kp ↔
      Real.sqrt kr < Real.sqrt kp := by
    constructor <;> intro h <;> linarith
  rw [h1, Real.sqrt_lt_sqrt_iff (le_of_lt hkr)]

/-- Early transition state at zero driving force, exactly when the reactant well is stiffer. -/
theorem tsCoordZero_lt_half_iff_stiffReactant {kr kp : ℝ} (hkr : 0 < kr) (hkp : 0 < kp) :
    tsCoordZero kr kp < (1 : ℝ) / 2 ↔ kp < kr := by
  unfold tsCoordZero
  have hne : 0 < Real.sqrt kr + Real.sqrt kp :=
    add_pos (Real.sqrt_pos.mpr hkr) (Real.sqrt_pos.mpr hkp)
  rw [div_lt_iff₀ hne]
  have h1 : Real.sqrt kp < (1 : ℝ) / 2 * (Real.sqrt kr + Real.sqrt kp) ↔
      Real.sqrt kp < Real.sqrt kr := by
    constructor <;> intro h <;> linarith
  rw [h1, Real.sqrt_lt_sqrt_iff (le_of_lt hkp)]

/-- Tie-back certificate: at equal curvature the closed form is the delivered kernel coordinate at
thermoneutrality. -/
theorem tsCoordZero_eq_kernel_thermoneutral {lam : ℝ} (hlam : 0 < lam) :
    tsCoordZero lam lam = PhotoLean.Kernel.tsCoord lam 0 := by
  have hsq : Real.sqrt lam ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlam)
  have h1 : tsCoordZero lam lam = 1 / 2 := by
    show Real.sqrt lam / (Real.sqrt lam + Real.sqrt lam) = 1 / 2
    have hsum : Real.sqrt lam + Real.sqrt lam = 2 * Real.sqrt lam := by ring
    rw [hsum, div_eq_iff (mul_ne_zero two_ne_zero hsq)]
    ring
  have h2 : PhotoLean.Kernel.tsCoord lam 0 = 1 / 2 := by
    show (lam - 0) / (2 * lam) = 1 / 2
    rw [sub_zero, div_eq_iff (mul_ne_zero two_ne_zero (ne_of_gt hlam))]
    ring
  linarith

/-- The conflated reading HOLDS in the equal-curvature kernel model — the regime every textbook
picture draws. -/
theorem betaHalf_holds_in_kernel {lam : ℝ} (hlam : 0 < lam) : BetaHalfReading lam lam :=
  (betaHalf_iff_equalForceConstants hlam hlam).mpr rfl

/-- Tie-back certificate: at equal curvature the closed form is the delivered BEP transfer
coefficient at thermoneutrality (`BEP.transfer_thermoneutral`). -/
theorem betaHalf_eq_transfer_thermoneutral {lam : ℝ} (hlam : 0 < lam) :
    tsCoordZero lam lam = PhotoLean.BEP.transfer lam 0 := by
  rw [PhotoLean.BEP.transfer_thermoneutral]
  exact betaHalf_holds_in_kernel hlam

end SymmetryFactor

end PhotoLean
