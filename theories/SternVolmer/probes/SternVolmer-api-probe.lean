/-
SternVolmer API-calibration probe (SV0, iron rule 4: no guessed names).
Run: proofs/scripts/lake env lean theories/SternVolmer/probes/SternVolmer-api-probe.lean
Expected: exit 0. Every `#check` output is recorded in proofs/API-NOTES.md §SternVolmer.

The skeleton `SternVolmer-statement-skeleton.lean` imports `Mathlib` only and uses no
delivered-PhotoLean names (plan §11: self-contained at the Basic layer), so this probe
calibrates (i) the mathlib lemma names the plan §5 proof routes consume, (ii) the cast API the
SV-R1 cast-coherence rows consume, (iii) kernel-checked pre-computations of the plan's
witnesses (the four SV-R3 zone rows, the SV-I3 conflation witness, the SV-I4 mixed witness),
and (iv) dry-runs of the SV-C proof shapes (linearity, second differences, curvature
positivity). The zone classifier is restated verbatim from the skeleton so the `decide`/`rfl`
verdicts of SV-R3/SV-I4 are measured against the real cascade.
-/
import Mathlib

set_option autoImplicit false

namespace PhotoLean

namespace SternVolmer

-- plan §5 monotonicity routes
#check @add_lt_add_left
#check @mul_lt_mul_of_pos_left

-- positivity routes for the curvature witness (SV-C9)
#check @mul_pos
#check @div_pos
#check @pow_pos
#check @sq_nonneg
#check @sq_pos_of_ne_zero

-- division-algebra routes for the linearity rows (SV-C3/C5/C7/C9)
#check @div_eq_iff
#check @eq_div_iff
#check @div_self

-- SV-R1 cast-coherence routes
#check @Rat.cast_div
#check @Rat.cast_add
#check @Rat.cast_mul
#check @Rat.cast_one
#check @Rat.cast_zero
#check @Rat.cast_pow
#check @Rat.cast_inj

-- decidability the svZoneQ if-cascade consumes
#check (inferInstance : Decidable ((0 : ℚ) < 2))
#check (inferInstance : Decidable ((2 : ℚ) = 2))
#check (inferInstance : Decidable ((0 : ℚ) < 2 ∧ (2 : ℚ) = 2))

-- the zone classifier, verbatim from the skeleton (SV-R2), so the witness rows below measure
-- the real cascade
/-- The four verdict zones of a measured slope pair. Plan section 4, row SV-R2 (probe copy). -/
inductive SVZone | dynLike | statLike | mixedLike | inconsistent
  deriving DecidableEq

/-- Classify a measured slope pair `(slopeI, slopeTau)`. Plan section 4, row SV-R2
(probe copy, body verbatim from the skeleton). -/
def svZoneQ (slopeI slopeTau : ℚ) : SVZone :=
  if 0 < slopeI ∧ slopeTau = slopeI then SVZone.dynLike
  else if 0 < slopeI ∧ slopeTau = 0 then SVZone.statLike
  else if 0 < slopeTau ∧ slopeTau < slopeI then SVZone.mixedLike
  else SVZone.inconsistent

-- SV-R3 zone-correctness witnesses, kernel-checked (integer ℚ literals: `decide` reduces)
example : svZoneQ 2 2 = SVZone.dynLike := by decide
example : svZoneQ 1 0 = SVZone.statLike := by decide
example : svZoneQ 2 1 = SVZone.mixedLike := by decide
example : svZoneQ 0 1 = SVZone.inconsistent := by decide

-- SV-I4 zone row at the exact mixed slopes `(1/2 + 1, 1/2)`: `decide` does NOT reduce
-- /-literals (the thrice-measured repository boundary — `Nat.gcd` is well-founded), so the
-- delivered row needs the if_neg/if_pos route below, not `decide`.
example : svZoneQ (1 / 2 + 1 : ℚ) (1 / 2) = SVZone.mixedLike := by
  have c1 : ¬ (0 < (1 / 2 + 1 : ℚ) ∧ (1 / 2 : ℚ) = 1 / 2 + 1) := by norm_num
  have c2 : ¬ (0 < (1 / 2 + 1 : ℚ) ∧ (1 / 2 : ℚ) = 0) := by norm_num
  have c3 : 0 < (1 / 2 : ℚ) ∧ (1 / 2 : ℚ) < 1 / 2 + 1 := by norm_num
  unfold svZoneQ
  rw [if_neg c1, if_neg c2, if_pos c3]

-- SV-I4 second difference at `(x, h) = (0, 1)` over ℚ: `2·KSV·Ka·h² = 1 > 0` at `KSV = 1/2`,
-- `Ka = 1` (norm_num, not decide — same /-literal boundary)
example : 2 * ((1 : ℚ) / 2) * 1 * (1 : ℚ) ^ 2 = 1 ∧ (0 : ℚ) < 1 := by norm_num

-- SV-I3 conflation witness, kernel-checked (the delivered row quantifies over the unfolded
-- bodies `svRatioDyn 2 2 q = (2 + 2·q)/2` and `svRatioStat 1 q = 1 + 1·q`)
example : ∀ q : ℝ, (2 + 2 * q) / 2 = 1 + 1 * q := by
  intro q
  field_simp
  ring

-- SV-C3/C7 proof shape: the dynamic ratio is linear with slope `kq/k0`.
-- Measured: `field_simp` ALONE closes this shape — a following `ring` errors "no goals to be
-- solved" (unlike the numeral instance above, where `field_simp` leaves a `ring` goal).
example (k0 kq q : ℝ) (hk0 : k0 ≠ 0) : (k0 + kq * q) / k0 = 1 + (kq / k0) * q := by
  field_simp

-- SV-C5 proof shape: the dynamic ratio at zero quencher
example (k0 kq : ℝ) (hk0 : k0 ≠ 0) : (k0 + kq * 0) / k0 = 1 := by
  field_simp

-- SV-C6 proof shape (static side): the plan §5 monotonicity pair closes the row directly
example (Ka q₁ q₂ : ℝ) (hKa : 0 < Ka) (h : q₁ < q₂) :
    1 + Ka * q₁ < 1 + Ka * q₂ := by
  exact add_lt_add_left (mul_lt_mul_of_pos_left h hKa) 1

-- SV-C6 proof shape (dynamic side): the quotient form via the same monotonicity pair
example (k0 kq q₁ q₂ : ℝ) (hk0 : 0 < k0) (hkq : 0 < kq) (h : q₁ < q₂) :
    (k0 + kq * q₁) / k0 < (k0 + kq * q₂) / k0 := by
  have h1 : k0 + kq * q₁ < k0 + kq * q₂ :=
    add_lt_add_left (mul_lt_mul_of_pos_left h hkq) k0
  exact (div_lt_div_iff_of_pos_right hk0).mpr h1

-- SV-C9 proof shape: the static second difference vanishes (`ring`)
example (Ka x h : ℝ) :
    (1 + Ka * (x + h)) - 2 * (1 + Ka * x) + (1 + Ka * (x - h)) = 0 := by ring

-- SV-C9 proof shape: the combined second difference is `2·(kq/k0)·Ka·h²` (field_simp + ring)
example (k0 kq Ka x h : ℝ) (hk0 : k0 ≠ 0) :
    ((k0 + kq * (x + h)) / k0) * (1 + Ka * (x + h)) -
      2 * (((k0 + kq * x) / k0) * (1 + Ka * x)) +
        ((k0 + kq * (x - h)) / k0) * (1 + Ka * (x - h)) = 2 * (kq / k0) * Ka * h ^ 2 := by
  field_simp
  ring

-- SV-C9 curvature positivity: `div_pos` + `mul_pos` + `sq_pos_of_ne_zero`, closed by
-- `positivity` on the atoms in context
example (k0 kq Ka h : ℝ) (hk0 : 0 < k0) (hkq : 0 < kq) (hKa : 0 < Ka) (hh : h ≠ 0) :
    0 < 2 * (kq / k0) * Ka * h ^ 2 := by
  have hksv : 0 < kq / k0 := div_pos hkq hk0
  have hh2 : 0 < h ^ 2 := sq_pos_of_ne_zero hh
  positivity

-- SV-C2 static separation shape: `1 ≠ 1 + Ka·q` from `0 < Ka`, `0 < q`
example (Ka q : ℝ) (hKa : 0 < Ka) (hq : 0 < q) : (1 : ℝ) ≠ 1 + Ka * q := by
  have hpos : 0 < Ka * q := mul_pos hKa hq
  linarith

-- SV-R1 cast-coherence shapes: `norm_cast` moves the cast through `+`, `*`, `/` on ℚ → ℝ
example (a b q : ℚ) :
    (((a + b * q) / a : ℚ) : ℝ) = ((a : ℝ) + (b : ℝ) * (q : ℝ)) / (a : ℝ) := by
  norm_cast
example (a q : ℚ) :
    ((1 + a * q : ℚ) : ℝ) = (1 : ℝ) + (a : ℝ) * (q : ℝ) := by
  norm_cast

end SternVolmer

end PhotoLean
