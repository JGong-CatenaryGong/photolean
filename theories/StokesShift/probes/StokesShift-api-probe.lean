/-
StokesShift-api-probe.lean — API calibration probe for the StokesShift theory (Phase 1).

Run: proofs/scripts/lake env lean theories/StokesShift/probes/StokesShift-api-probe.lean
Expected: exit 0, no placeholder proofs in this file (probes are calibration tools and may
carry proved examples). Every `#check` confirms a name the statement skeleton uses in a proof
route; the findings are appended to proofs/API-NOTES.md at delivery.

Coverage: the kernel certificate targets (`PhotoLean.Kernel.reactantSurface` /
`productSurface`), the Marcus `InvertedRegion` body (the SS-C9 correction — plan §3.1 entry 1
— was caught HERE: the first form `e00 < lam ↔ InvertedRegion lam e00` is false, with the
kernel-checked counterexample below), the instance arithmetic of SS-I, and the cast names of
the rational layer.
-/
import Mathlib
import PhotoLean.Kernel
import PhotoLean.Marcus.Basic

-- kernel certificate targets
#check @PhotoLean.Kernel.reactantSurface
#check @PhotoLean.Kernel.productSurface
#check @PhotoLean.Marcus.InvertedRegion

-- cast names of the rational layer
#check @Rat.cast_add
#check @Rat.cast_mul
#check @Rat.cast_pow
#check @Rat.cast_sub
#check @Rat.cast_lt
#check @Rat.cast_le

set_option autoImplicit false

namespace PhotoLean

/-- The kernel certificates of SS-B1/B2 close by `rfl` (dry run at the definitions' bodies). -/
example (lam q : ℝ) : lam * q ^ 2 = PhotoLean.Kernel.reactantSurface lam q := rfl
example (lam e00 q : ℝ) : lam * (q - 1) ^ 2 + e00 = PhotoLean.Kernel.productSurface lam e00 q := rfl

/-- The SS-C9 counterexample (plan §3.1 entry 1): the first form `e00 < lam ↔
InvertedRegion lam e00` is false at `lam = 1, e00 = 2` — there `InvertedRegion 1 2` holds
(`1 < 2`) while `2 < 1` fails. -/
example : ¬ ((2 : ℝ) < 1 ↔ PhotoLean.Marcus.InvertedRegion 1 2) := by
  have h : PhotoLean.Marcus.InvertedRegion 1 2 := by
    unfold PhotoLean.Marcus.InvertedRegion; norm_num
  intro hiff
  exact absurd (hiff.mpr h) (by norm_num)

/-- The corrected SS-C9's two sides both reduce to `lam < e00` (dry run of the `↔` at a
numeral pair): the emission energy `lam·(1−1)² + e00 − lam·1² = e00 − lam` is positive exactly
when `lam < e00`. -/
example (lam e00 : ℝ) :
    (0 < (lam * (1 - 1) ^ 2 + e00) - lam * 1 ^ 2) ↔ lam < e00 := by
  constructor <;> intro h <;> linarith

/-- SS-I1 arithmetic: the mirror-symmetric dye (probe-checked values). -/
example : ((1 / 2 : ℝ) * (0 - 1) ^ 2 + 2) - (1 / 2) * 0 ^ 2 = 5 / 2 ∧
    ((1 / 2 : ℝ) * (1 - 1) ^ 2 + 2) - (1 / 2) * 1 ^ 2 = 3 / 2 ∧
      (5 / 2 : ℝ) - 3 / 2 = 1 := by norm_num

/-- SS-R cast-coherence route dry run: a polynomial cast commutes. -/
example (lam e00 : ℚ) :
    ((lam * 2 + e00 : ℚ) : ℝ) = (lam : ℝ) * 2 + (e00 : ℝ) := by
  norm_cast

end PhotoLean
