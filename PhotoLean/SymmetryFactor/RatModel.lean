/-
PhotoLean.SymmetryFactor.RatModel — milestone F3, the computable rational decision layer.

The order of `ℝ` is not computable, so instance verdicts about the closed form cannot be decided
by the kernel over `ℝ` directly (the repository's standing structural solution: an `ℝ` theory plus
a `ℚ` shadow plus cast bridges — METHOD.md five-piece item 2). For this theory the shadow is
exact at **perfect-square curvatures**: writing `kr = a²`, `kp = b²` with `a, b` positive
rationals, the square roots disappear and the crossing coordinate is the rational `b / (a + b)`
(the Goldschmidt "push the root into exact rational squares" pattern). The cast bridges
(`tsCoordZeroQ_cast`, `betaHalfQ_cast`) prove the shadow computes the real closed form and decides
the real reading — the copy is the real thing, not an analogy.

Measured boundaries (API round): `by decide` handles integer `ℚ` literals only — division-bearing
literals go through `norm_num` (the repository's thrice-measured rule); `native_decide` is banned
by the axiom discipline (`Lean.ofReduceBool` is not in `ALLOWED_AXIOMS`, `proofs/ENGINE.yml`).

Statement authority: `theories/SymmetryFactor/probes/SymmetryFactor-statement-skeleton.lean` § F3.
There is no unproved placeholder and no custom axiomatic declaration anywhere in this file. The
`#print axioms` gate of every theorem below lists at most `propext`, `Classical.choice`,
`Quot.sound`.
-/
import PhotoLean.SymmetryFactor.Basic

set_option autoImplicit false

namespace PhotoLean

namespace SymmetryFactor

/-! ## F3 — the rational decision layer -/

/-- The computable ℚ shadow at perfect-square curvatures: for `kr = a²`, `kp = b²` (positive
rationals) the crossing coordinate is the rational `b/(a+b)` — no `Real.sqrt` in the decision
layer (the Goldschmidt √-free-squares pattern). -/
def tsCoordZeroQ (a b : ℚ) : ℚ := b / (a + b)

/-- The β = 1/2 reading in the decision layer. -/
def BetaHalfQ (a b : ℚ) : Prop := tsCoordZeroQ a b = 1 / 2

/-- Cast bridge: the ℚ shadow computes the real closed form at perfect-square curvatures. -/
theorem tsCoordZeroQ_cast {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    tsCoordZero ((a : ℝ) * (a : ℝ)) ((b : ℝ) * (b : ℝ)) = (tsCoordZeroQ a b : ℝ) := by
  have hasqrt : Real.sqrt ((a : ℝ) * (a : ℝ)) = (a : ℝ) :=
    Real.sqrt_mul_self (le_of_lt (Rat.cast_pos.mpr ha))
  have hbsqrt : Real.sqrt ((b : ℝ) * (b : ℝ)) = (b : ℝ) :=
    Real.sqrt_mul_self (le_of_lt (Rat.cast_pos.mpr hb))
  unfold tsCoordZero tsCoordZeroQ
  rw [hasqrt, hbsqrt, Rat.cast_div, Rat.cast_add]

/-- The decision-layer verdict: `BetaHalfQ a b ↔ a = b` — decidable by `norm_num` per instance. -/
theorem betaHalfQ_iff {a b : ℚ} (ha : 0 < a) (hb : 0 < b) : BetaHalfQ a b ↔ a = b := by
  have hab : (a + b : ℚ) ≠ 0 := ne_of_gt (add_pos ha hb)
  unfold BetaHalfQ tsCoordZeroQ
  rw [div_eq_iff hab]
  constructor <;> intro h <;> linarith

/-- Cast bridge for the reading: the ℚ verdict is the real verdict at the corresponding
perfect-square curvatures. -/
theorem betaHalfQ_cast {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    BetaHalfQ a b ↔ BetaHalfReading ((a : ℝ) * (a : ℝ)) ((b : ℝ) * (b : ℝ)) := by
  have hcast : tsCoordZero ((a : ℝ) * (a : ℝ)) ((b : ℝ) * (b : ℝ)) = (tsCoordZeroQ a b : ℝ) :=
    tsCoordZeroQ_cast ha hb
  have hone : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by norm_num
  constructor
  · intro h
    rw [BetaHalfQ] at h
    rw [BetaHalfReading, hcast, h]
    exact hone
  · intro h
    rw [BetaHalfReading] at h
    rw [hcast] at h
    rw [← hone] at h
    rw [BetaHalfQ]
    exact Rat.cast_inj.mp h

end SymmetryFactor

end PhotoLean
