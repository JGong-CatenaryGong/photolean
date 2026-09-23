/-
PhotoLean.Einstein.RatModel — milestone EB-R, the rational decision layer.

Why the layer exists: the physical radiation-density factor
`radFactor h c ν = 8πhν³/c³` contains `π`, and `π` is irrational (`radFactor_not_rational`), so
the equivalence chain cannot be *decided* at the physical constants by exact arithmetic. The
rational surrogate layer repeats the five EB-B maps over `ℚ` (`Rat.aOfB`, `Rat.b12OfB21`,
`Rat.fOfA`, `Rat.aOfInt`, `Rat.tauR`) and computes the round trips there; `rat_roundtrip_verdicts`
is the verdict row at the surrogate constants `K = 3`, `Cf = 5`, `g₁ = 1`, `g₂ = 3`, `Ci = 7`.

Honest scope, stated up front (plan §2, §8, §9):
* the `ℚ` rows test the **algebra** of the chain at rational *surrogate* constants; they say
  nothing about the physical constants of a real transition;
* `π` is irrational in mathlib's sense (`Irrational Real.pi`), so "the chain is decidable at the
  physical constants" is not available even in principle at this layer;
* the cast-coherence rows (`aOfB_cast`, `b12OfB21_cast`, `fOfA_cast`, `aOfInt_cast`, `tauR_cast`)
  are what keeps the surrogate honest: each `ℚ` map, pushed into `ℝ`, computes exactly the real map
  of the pushed constants — so the rational layer is a *model* of the real chain, not a rewrite of it.

Measured tactic boundary (plan §4's "by `decide`" route, corrected at delivery): `decide` does not
reduce `ℚ` division/multiplication in mathlib v4.17.0, so the verdict rows are closed by
`norm_num [Rat.…]` instead — the same boundary already recorded for `Marcus.RatModel` and Forster's
FO-R2. The row docstrings keep the authority's wording verbatim; the tactic that actually closes
them is the one above.

Statement authority: `theories/Einstein/probes/Einstein-statement-skeleton.lean` § EB-R; every
signature below is identical to its authority row. There is no unproved placeholder and no custom
axiomatic declaration anywhere in this file.

Acceptance:
    proofs/scripts/lake build PhotoLean.Einstein.RatModel
    proofs/scripts/axioms.sh PhotoLean.Einstein.RatModel PhotoLean.Einstein.radFactor_not_rational
    proofs/scripts/check.sh --strict PhotoLean.Einstein.RatModel
-/
import PhotoLean.Einstein.Criterion

set_option autoImplicit false

namespace PhotoLean

namespace Einstein

/-! ## EB-R — the rational decision layer -/

namespace Rat

/-- Rational surrogate of `aOfB` (the physical `radFactor` contains `π`; the ℚ layer tests the
algebra at rational constants — plan §2). Plan section 4, row EB-R1. -/
def aOfB (K B21 : ℚ) : ℚ := K * B21

/-- Rational surrogate of `b12OfB21`. Plan section 4, row EB-R1. -/
def b12OfB21 (g1 g2 B21 : ℚ) : ℚ := (g2 / g1) * B21

/-- Rational surrogate of `fOfA`. Plan section 4, row EB-R1. -/
def fOfA (Cf g1 g2 A : ℚ) : ℚ := Cf * (g2 / g1) * A

/-- Rational surrogate of `aOfInt`. Plan section 4, row EB-R1. -/
def aOfInt (Ci I : ℚ) : ℚ := Ci * I

/-- Rational surrogate of `tauR`. Plan section 4, row EB-R1. -/
def tauR (A : ℚ) : ℚ := 1 / A

/-- Cast coherence: the ℚ surrogate of `aOfB` computes the real `aOfB`. Plan section 4, row EB-R1
(cast coherence). Proof route: `Rat.cast_mul`. -/
theorem aOfB_cast (K B21 : ℚ) : (aOfB K B21 : ℝ) = Einstein.aOfB (K : ℝ) (B21 : ℝ) := by
  simp only [aOfB, Einstein.aOfB, Rat.cast_mul]

/-- Cast coherence: the ℚ surrogate of `b12OfB21` computes the real `b12OfB21`. Plan section 4,
row EB-R1 (cast coherence). Proof route: `Rat.cast_div`, `Rat.cast_mul`. -/
theorem b12OfB21_cast (g1 g2 B21 : ℚ) :
    (b12OfB21 g1 g2 B21 : ℝ) = Einstein.b12OfB21 (g1 : ℝ) (g2 : ℝ) (B21 : ℝ) := by
  simp only [b12OfB21, Einstein.b12OfB21, Rat.cast_mul, Rat.cast_div]

/-- Cast coherence: the ℚ surrogate of `fOfA` computes the real `fOfA`. Plan section 4, row EB-R1
(cast coherence). Proof route: `Rat.cast_div`, `Rat.cast_mul`. -/
theorem fOfA_cast (Cf g1 g2 A : ℚ) :
    (fOfA Cf g1 g2 A : ℝ) = Einstein.fOfA (Cf : ℝ) (g1 : ℝ) (g2 : ℝ) (A : ℝ) := by
  simp only [fOfA, Einstein.fOfA, Rat.cast_mul, Rat.cast_div]

/-- Cast coherence: the ℚ surrogate of `aOfInt` computes the real `aOfInt`. Plan section 4, row
EB-R1 (cast coherence). Proof route: `Rat.cast_mul`. -/
theorem aOfInt_cast (Ci I : ℚ) : (aOfInt Ci I : ℝ) = Einstein.aOfInt (Ci : ℝ) (I : ℝ) := by
  simp only [aOfInt, Einstein.aOfInt, Rat.cast_mul]

/-- Cast coherence: the ℚ surrogate of `tauR` computes the real `tauR`. Plan section 4, row EB-R1
(cast coherence). Proof route: `Rat.cast_div`, `Rat.cast_one`. -/
theorem tauR_cast (A : ℚ) : (tauR A : ℝ) = Einstein.tauR (A : ℝ) := by
  simp only [tauR, Einstein.tauR, Rat.cast_div, Rat.cast_one]

end Rat

/-- Round-trip verdicts at the rational surrogate constants (`K = 3`, `Cf = 5`, `g1 = 1`,
`g2 = 3`, `Ci = 7`): every leg of the chain closes, computed in the ℚ decision layer at the
surrogate transition values `B21 = 2`, `A = 2`, `I = 9`. Plan section 4, row EB-R2. Proof route
(plan §4): `decide`. -/
theorem rat_roundtrip_verdicts :
    Rat.aOfB 3 (Rat.aOfB 3 2 / 3) / 3 = 2 ∧
    Rat.b12OfB21 3 1 (Rat.b12OfB21 1 3 2) = 2 ∧
    Rat.fOfA 5 1 3 2 / (5 * (3 / 1)) = 2 ∧
    Rat.aOfInt 7 9 / 7 = 9 := by
  norm_num [Rat.aOfB, Rat.b12OfB21, Rat.fOfA, Rat.aOfInt]

/-- Honesty row: the physical `radFactor` is not rational — it contains `π`, and `π` is irrational.
The ℚ layer therefore tests the algebra at rational surrogate constants only and says nothing about
the physical constants (plan §2, §8). Plan section 4, row EB-R2 (honesty). Proof route: mathlib's
irrationality of `π` (`irrational_pi`, calibrated in the API probe). -/
theorem radFactor_not_rational : Irrational (radFactor 1 1 1) := by
  have hrw : radFactor 1 1 1 = (8 : ℤ) * Real.pi := by
    unfold radFactor
    norm_num
  rw [hrw]
  exact irrational_int_mul_iff.mpr ⟨by norm_num, irrational_pi⟩

end Einstein

end PhotoLean
