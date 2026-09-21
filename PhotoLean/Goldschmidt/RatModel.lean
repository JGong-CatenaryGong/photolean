/-
PhotoLean — PhotoLean/Goldschmidt/RatModel.lean

Milestone G5 (plan §8): the **rational decision layer** of the Goldschmidt theory — the `√2`-free
criterion on `ℚ`, and the transfer theorems showing that the rational decision reproduces the real
verdict.

Why the layer exists: `tolFac rA rB rO = (rA + rO) / (√2 * (rB + rO))` is *irrational* at rational
radii, so the real band verdict is not decidable by exact rational arithmetic. Squaring removes the
`√2` (`(√2 (rB+rO))² = 2 (rB+rO)²`), and the resulting criterion `inBandQ` is a pure `ℚ` predicate on
squared quantities; `inBandQ_cast` is the correctness theorem that the `ℚ` decision and the real
verdict agree, and `zoneQ_eq_zone` is the same transfer for the computable classifier. The constants
of the theory are carried into `ℚ` (`classicLoQ`, …) with their cast rows.

Statement authority: `theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean` § G5; every
signature below matches it word for word (check with
`python3 theories/BEP/probes/bep-fidelity.py --theory goldschmidt --milestone G5`). The `Rat`
sub-namespace is the authority's own layout (`namespace Rat` inside `PhotoLean.Goldschmidt`), and
the layer is downstream of G1 (`Basic.lean`) and G3 (`Criterion.lean`) — `inBandQ_cast` is proved
from `Criterion.conforms_iff_sq`, so the `√2` bookkeeping is done once, in the law layer, and the
rational layer only moves it across the cast.

The file also imports `PhotoLean.Goldschmidt.Rules` (G2): the authority's `radiusMatchQ_cast` is
stated in terms of `RadiusMatch`, which G2 declares; `Criterion.lean` imports only `Basic.lean`, so
without that import the statement would not elaborate. Nothing else of G2 is used.

Two shape traps of this milestone, both settled by the authority (plan §3.1 item 5):
`zoneQ_ideal_iff` is **unconditional** (its four physical premises were removed as non-load-bearing),
while `zoneQ_eq_zone` keeps the four premises — they are load-bearing there, because the transfer
between the `ℚ` squared comparisons and the real comparisons of `tolFac` needs exactly the
non-negativity of the band edges and the radii.

Every physical premise is an explicit hypothesis and none is hidden in a definition (engine rule 3);
the `ℚ` definitions carry no side condition at all, since `ℚ` division is total.
-/
import PhotoLean.Goldschmidt.Basic

import PhotoLean.Goldschmidt.Criterion

import PhotoLean.Goldschmidt.Rules

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Goldschmidt

namespace Rat

/-! ## G5 definitions — the `√2`-free decision objects (plan §8) -/

/-- The square of the tolerance factor: rational whenever the radii are rational, unlike `t` itself
(`√2` is irrational). -/
noncomputable def tolFacSq (rA rB rO : ℚ) : ℚ := (rA + rO) ^ 2 / (2 * (rB + rO) ^ 2)

/-- The `√2`-free band criterion on `ℚ`: the squared window on `(rA + rO)`. -/
def inBandQ (lo hi rA rB rO : ℚ) : Prop :=
  2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 ∧ (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2

/-- The radius rule on `ℚ`. -/
def radiusMatchQ (tau r r' : ℚ) : Prop := |r - r'| ≤ tau * r

/-- The electronegativity-dressed tolerance on `ℚ`. -/
noncomputable def chiTolQ (tol0 k chi chi' : ℚ) : ℚ := tol0 - k * |chi - chi'|

/-- The chemical rule composed with the radius rule on `ℚ`. -/
def substitutableQ (tol0 k chi chi' r r' : ℚ) : Prop := radiusMatchQ (chiTolQ tol0 k chi chi') r r'

/-- Computable three-way classifier on `ℚ`, comparing the squared quantities. -/
def zoneQ (lo hi rA rB rO : ℚ) : GoldschmidtZone :=
  if (rA + rO) ^ 2 < 2 * lo ^ 2 * (rB + rO) ^ 2 then GoldschmidtZone.tooSmall
  else if (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2 then GoldschmidtZone.ideal
  else GoldschmidtZone.tooLarge

/-- `ℚ` mirror of the classic band's lower edge. -/
def classicLoQ : ℚ := 4 / 5

/-- `ℚ` mirror of the classic band's upper edge. -/
def classicHiQ : ℚ := 1

/-- `ℚ` mirror of the tetragonal band's upper edge. -/
def tetragonalHiQ : ℚ := 11 / 10

/-- `ℚ` mirror of the printed "15 %" figure. -/
def tauGoldschmidtQ : ℚ := 3 / 20

/-! ## G5 cast-transfer rows (plan §8) -/

/-- `tolFacSq` really is the square of the real tolerance factor: the cast push-through of
`(rA+rO)²/(2(rB+rO)²)` is `((rA+rO)/(√2(rB+rO)))²`, because `(√2)² = 2`.

Proof: `unfold`, `push_cast`, then the two power rewrites and `Real.sq_sqrt`. Rational division and
real division are both total, and the identity holds at `rB + rO = 0` as well (both sides are `0`),
so **no** case split on `rB + rO = 0` is needed — the cast lemmas are unconditional. -/
theorem tolFacSq_cast (rA rB rO : ℚ) :
    ((tolFacSq rA rB rO : ℚ) : ℝ) = (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)) ^ 2 := by
  unfold tolFacSq tolFac
  push_cast
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]

/-- **The correctness theorem of the rational decision layer**: the `ℚ` squared criterion decides
the real band verdict. Proof: the two halves of the `ℚ` conjunction transfer to `ℝ` by
`(Rat.cast_le (K := ℝ)).symm` + `push_cast` (the casts of `+`, `*`, `^`), and the `ℝ` side is exactly
`Criterion.conforms_iff_sq` — the four hypotheses are its hypotheses. -/
theorem inBandQ_cast {lo hi rA rB rO : ℚ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hB : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) : inBandQ lo hi rA rB rO ↔
      GoldschmidtConforms (lo : ℝ) (hi : ℝ) (rA : ℝ) (rB : ℝ) (rO : ℝ) := by
  have hlo' : (0 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hlo
  have hhi' : (0 : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hhi
  have hB' : (0 : ℝ) < (rB : ℝ) + (rO : ℝ) := by exact_mod_cast hB
  have hA' : (0 : ℝ) ≤ (rA : ℝ) + (rO : ℝ) := by exact_mod_cast hA
  have hcast1 : (2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2) ↔
      (2 * (lo : ℝ) ^ 2 * ((rB : ℝ) + (rO : ℝ)) ^ 2 ≤ ((rA : ℝ) + (rO : ℝ)) ^ 2) := by
    rw [(Rat.cast_le (K := ℝ)).symm]
    push_cast
    rfl
  have hcast2 : ((rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2) ↔
      (((rA : ℝ) + (rO : ℝ)) ^ 2 ≤ 2 * (hi : ℝ) ^ 2 * ((rB : ℝ) + (rO : ℝ)) ^ 2) := by
    rw [(Rat.cast_le (K := ℝ)).symm]
    push_cast
    rfl
  rw [conforms_iff_sq hlo' hhi' hB' hA']
  unfold inBandQ
  exact and_congr hcast1 hcast2

/-- The **point band** `[1, 1]` on `ℚ`: the squared criterion is the ideal-packing equation
`(rA + rO)² = 2 (rB + rO)²`, i.e. `t² = 1`.

The two physical premises are the authority's; the row is a pure `ℚ` statement about the squared
criterion, and it is proved through the layer's correctness theorem (`inBandQ_cast` with the band
edges `1`, `1`, then `conforms_iff_sq`), which is where they are consumed. -/
theorem inBandQ_ideal_iff {rA rB rO : ℚ} (hB : 0 < rB + rO) (hA : 0 ≤ rA + rO) :
    inBandQ 1 1 rA rB rO ↔ (rA + rO) ^ 2 = 2 * (rB + rO) ^ 2 := by
  have hB' : (0 : ℝ) < (rB : ℝ) + (rO : ℝ) := by exact_mod_cast hB
  have hA' : (0 : ℝ) ≤ (rA : ℝ) + (rO : ℝ) := by exact_mod_cast hA
  have hcast : ((rA + rO) ^ 2 = 2 * (rB + rO) ^ 2 : Prop) ↔
      (((rA : ℝ) + (rO : ℝ)) ^ 2 = 2 * ((rB : ℝ) + (rO : ℝ)) ^ 2) := by
    constructor <;> intro h <;> exact_mod_cast h
  rw [inBandQ_cast (lo := 1) (hi := 1) (by norm_num) (by norm_num) hB hA]
  push_cast
  rw [conforms_iff_sq (lo := 1) (hi := 1) (by norm_num) (by norm_num) hB' hA', hcast]
  constructor
  · rintro ⟨h1, h2⟩
    linarith
  · intro h
    constructor <;> linarith

/-- The `ℚ` radius rule is the `ℝ` radius rule under the cast: the cast pushes through the absolute
value, the subtraction and the product. -/
theorem radiusMatchQ_cast {tau r r' : ℚ} :
    radiusMatchQ tau r r' ↔ RadiusMatch (tau : ℝ) (r : ℝ) (r' : ℝ) := by
  unfold radiusMatchQ RadiusMatch
  rw [(Rat.cast_le (K := ℝ)).symm]
  push_cast
  rfl

/-- The `ℚ` radius rule as the same two-sided window as its `ℝ` twin — the G2 row
`Rules.radiusMatch_iff_window` read along the cast. -/
theorem radiusMatchQ_iff_window {tau r r' : ℚ} :
    radiusMatchQ tau r r' ↔ (1 - tau) * r ≤ r' ∧ r' ≤ (1 + tau) * r := by
  rw [radiusMatchQ_cast, radiusMatch_iff_window]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- The printed "15 %" rule on `ℚ`, in the clearing-denominators arithmetic form
`17 r ≤ 20 r' ∧ 20 r' ≤ 23 r` — `radiusMatchQ_iff_window` at `τ = 3/20` with the positive factor
`20` cleared. -/
theorem radiusMatchQ_fifteen {r r' : ℚ} :
    radiusMatchQ (3 / 20) r r' ↔ 17 * r ≤ 20 * r' ∧ 20 * r' ≤ 23 * r := by
  rw [radiusMatchQ_iff_window]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- **The classifier transfer**: the computable `ℚ` classifier of the squared criterion agrees with
the real classifier of the tolerance factor.

Proof: after unfolding both cascades, it suffices to identify the two branch tests. The bridges are
`lo ≤ t ↔ 2 lo² (rB+rO)² ≤ (rA+rO)²` (and its `hi`/`≤` mirror), proved by the sprint-0 recipe
`le_div_iff₀`/`div_le_iff₀` + `sq_le_sq₀` with the non-negativity supplied by the four premises, and
carried across the cast by `(Rat.cast_le (K := ℝ)).symm` + `push_cast`; the strict branch test is the
negation of the non-strict one (`not_le`). This is where the four hypotheses are load-bearing: the
`sq_le_sq₀` step needs `0 ≤ lo` (resp. `0 ≤ hi`), `0 ≤ rA + rO`, and `0 < rB + rO` makes
`√2 (rB + rO) > 0`. -/
theorem zoneQ_eq_zone {lo hi rA rB rO : ℚ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hB : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) : zoneQ lo hi rA rB rO =
      goldschmidtZone (lo : ℝ) (hi : ℝ) (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)) := by
  have hlo' : (0 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hlo
  have hhi' : (0 : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hhi
  have hB' : (0 : ℝ) < (rB : ℝ) + (rO : ℝ) := by exact_mod_cast hB
  have hA' : (0 : ℝ) ≤ (rA : ℝ) + (rO : ℝ) := by exact_mod_cast hA
  have hd : 0 < Real.sqrt 2 * ((rB : ℝ) + (rO : ℝ)) :=
    mul_pos (Real.sqrt_pos_of_pos (by norm_num)) hB'
  have hsqlo : ((lo : ℝ) * (Real.sqrt 2 * ((rB : ℝ) + (rO : ℝ)))) ^ 2 =
      2 * (lo : ℝ) ^ 2 * ((rB : ℝ) + (rO : ℝ)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  have hsphi : ((hi : ℝ) * (Real.sqrt 2 * ((rB : ℝ) + (rO : ℝ)))) ^ 2 =
      2 * (hi : ℝ) ^ 2 * ((rB : ℝ) + (rO : ℝ)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  have hle : (lo : ℝ) ≤ tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ) ↔
      2 * (lo : ℝ) ^ 2 * ((rB : ℝ) + (rO : ℝ)) ^ 2 ≤ ((rA : ℝ) + (rO : ℝ)) ^ 2 := by
    unfold tolFac
    rw [le_div_iff₀ hd, ← hsqlo]
    exact (sq_le_sq₀ (mul_nonneg hlo' hd.le) hA').symm
  have hge : tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ) ≤ (hi : ℝ) ↔
      ((rA : ℝ) + (rO : ℝ)) ^ 2 ≤ 2 * (hi : ℝ) ^ 2 * ((rB : ℝ) + (rO : ℝ)) ^ 2 := by
    unfold tolFac
    rw [div_le_iff₀ hd, ← hsphi]
    exact (sq_le_sq₀ hA' (mul_nonneg hhi' hd.le)).symm
  have hcastLt : ((rA + rO) ^ 2 : ℚ) < 2 * lo ^ 2 * (rB + rO) ^ 2 ↔
      ((rA : ℝ) + (rO : ℝ)) ^ 2 < 2 * (lo : ℝ) ^ 2 * ((rB : ℝ) + (rO : ℝ)) ^ 2 := by
    rw [(Rat.cast_lt (K := ℝ)).symm]
    push_cast
    rfl
  have hcastLe : ((rA + rO) ^ 2 : ℚ) ≤ 2 * hi ^ 2 * (rB + rO) ^ 2 ↔
      ((rA : ℝ) + (rO : ℝ)) ^ 2 ≤ 2 * (hi : ℝ) ^ 2 * ((rB : ℝ) + (rO : ℝ)) ^ 2 := by
    rw [(Rat.cast_le (K := ℝ)).symm]
    push_cast
    rfl
  have hlt : (rA + rO) ^ 2 < 2 * lo ^ 2 * (rB + rO) ^ 2 ↔
      tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ) < (lo : ℝ) := by
    rw [hcastLt, ← not_le, ← hle, not_le]
  have hcle : (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2 ↔
      tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ) ≤ (hi : ℝ) := by
    rw [hcastLe, ← hge]
  unfold zoneQ goldschmidtZone
  by_cases h1 : tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ) < (lo : ℝ)
  · rw [if_pos (hlt.mpr h1), if_pos h1]
  · rw [if_neg (fun hc => h1 (hlt.mp hc)), if_neg h1]
    by_cases h2 : tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ) ≤ (hi : ℝ)
    · rw [if_pos (hcle.mpr h2), if_pos h2]
    · rw [if_neg (fun hc => h2 (hcle.mp hc)), if_neg h2]

/-- The `ℚ` classifier's **ideal** branch is exactly the `ℚ` band criterion. The row is
**unconditional** (plan §3.1 item 5): it is a statement about the squared criterion alone, and the
three branches are discharged by the trichotomy of `(rA + rO)²` against `2 lo² (rB + rO)²` and
`2 hi² (rB + rO)²`, so no physical premise is needed — and none is carried. -/
theorem zoneQ_ideal_iff (lo hi rA rB rO : ℚ) :
    zoneQ lo hi rA rB rO = GoldschmidtZone.ideal ↔ inBandQ lo hi rA rB rO := by
  unfold zoneQ inBandQ
  split_ifs with h1 h2
  · exact iff_of_false (by decide) (fun hc => (not_le.mpr h1) hc.1)
  · exact iff_of_true rfl ⟨le_of_not_gt h1, h2⟩
  · exact iff_of_false (by decide) (fun hc => h2 hc.2)

/-! ## G5 constant cast rows (plan §8) — the `ℚ` mirrors of the band constants -/

/-- The `ℚ` classic lower edge casts to the real one. -/
theorem classicLoQ_cast : (classicLoQ : ℝ) = classicLo := by
  unfold classicLoQ classicLo
  norm_num

/-- The `ℚ` classic upper edge casts to the real one. -/
theorem classicHiQ_cast : (classicHiQ : ℝ) = classicHi := by
  unfold classicHiQ classicHi
  norm_num

/-- The `ℚ` tetragonal upper edge casts to the real one. -/
theorem tetragonalHiQ_cast : (tetragonalHiQ : ℝ) = tetragonalHi := by
  unfold tetragonalHiQ tetragonalHi
  norm_num

/-- The `ℚ` printed "15 %" figure casts to the real one — so the rational instance layer and the
real statements of the rules layer speak about the same `τ`. -/
theorem tauGoldschmidtQ_cast : (tauGoldschmidtQ : ℝ) = tauGoldschmidt := by
  unfold tauGoldschmidtQ tauGoldschmidt
  norm_num

end Rat

end Goldschmidt

end PhotoLean
