/-
  PhotoLean — PhotoLean/Goldschmidt/Sharp.lean

  The Goldschmidt theory, milestone G4 (the **sharp conditions**): what failing the band verdict means
  exactly, the point band as the ideal case, the irrationality of the tolerance factor at rational
  radii (the reason the rational layer G5 decides on the square), the transfer of Goldschmidt's 15 %
  radius rule to a bound on the *tolerance factor*, and the kernel-checked failure witnesses.

  Design of record: `theories/goldschmidt/plan.md` §7 (the G4 row table), §9 families I1/I3/I4 (the
  instance roster) and §12 (honesty table).  Statement authority:
  `theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean` § `## G4`, which every signature
  below matches word for word (checked by
  `python3 theories/BEP/probes/bep-fidelity.py --theory goldschmidt --milestone G4`).

  Content.  `not_conforms_of_band_empty`: an inverted band has no conforming triple (the sharpness
  companion of G3's `exists_conforming`, which needs `lo ≤ hi`).  `conforms_point_band_iff`: the
  point band `[lo, lo]` is exactly the equation `t = lo`.  `not_conforms_of_lt_rAMin` /
  `not_conforms_of_rAMax_lt`: the two *one-sided* failure characterizations — below the window's lower
  edge, above its upper edge — obtained from the G3 radius-window equivalence without squaring.
  `tolFac_irrational`: at rational radii the factor is irrational, so no rational computation can
  decide by comparing `t`; G5 compares `t²` instead.  `tolFacFifteen_le`: the 15 % radius rule bounds
  the *shift* of the tolerance factor — the bridge from Goldschmidt's radius rule to the band verdict.
  `conforms_of_radiusMatch_window`: a substitution inside the 15 % window of a radius whose whole
  window already conforms cannot leave the band.  The five `witness_*` rows are the concrete positives
  and negatives, each decided by the kernel.

  Proof routes (all measured on the pinned toolchain): the two failure characterizations and the
  substitution transfer consume G3's `conforms_iff_radius_window` and Rules' `radiusMatch_iff_window`;
  `tolFacFifteen_le` rewrites through `tolFac_abs_shift_eq` with `d = rA' - rA` and divides by the
  positive denominator; the four rational witnesses go through G3's `√2`-free `conforms_iff_sq`, which
  turns them into exact rational comparisons for `norm_num` (no `Real.sqrt` algebra anywhere), and
  `witness_ideal_packing` reuses G3's `conforms_at_idealA_classic`.

  Statement correction (plan §3.1 item 9).  The first draft of `conforms_point_band_iff` carried
  `(h : 0 < rB + rO)`, which the row does not consume: `GoldschmidtConforms lo lo rA rB rO` unfolds to
  `lo ≤ t ∧ t ≤ lo`, pure antisymmetry for the *number* `tolFac rA rB rO`, with no division algebra in
  sight.  The premise is dropped in the authority (found during G4; the draft's own warning
  `unused variable h` is the measurement), so the file needs no local lint suppression and every
  hypothesis of every G4 row below is consumed.  No other G4 row had a non-load-bearing hypothesis.
-/
import PhotoLean.Goldschmidt.Basic
import PhotoLean.Goldschmidt.Rules
import PhotoLean.Goldschmidt.Criterion

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Goldschmidt

/-! ## G4 — sharp conditions (`PhotoLean/Goldschmidt/Sharp.lean`) -/

/-- An inverted band (`hi < lo`) has no conforming triple: the verdict demands `lo ≤ t ≤ hi`, which
`hi < lo` makes impossible. This is the sharp companion of G3's `exists_conforming`, whose hypothesis
is exactly the band non-emptiness this row negates (plan §7). -/
theorem not_conforms_of_band_empty {lo hi rA rB rO : ℝ} (h : hi < lo) :
    ¬ GoldschmidtConforms lo hi rA rB rO := by
  unfold GoldschmidtConforms InBand
  rintro ⟨h1, h2⟩
  linarith

/-- The **point band** `[lo, lo]` is exactly the ideal-type equation `t = lo`: the two-sided band
predicate `lo ≤ t ∧ t ≤ lo` collapses by antisymmetry. This is the sharp form behind the model's ideal
case at `lo = 1` (plan §7, §9 family I1).

No physical premise is needed and none is carried: the equivalence is antisymmetry of the order on the
*number* `tolFac rA rB rO`, so it holds for every band edge and every triple, including a vanishing
denominator. The authority's first draft carried `0 < rB + rO`; it was dropped as non-load-bearing
(plan §3.1 item 9). -/
theorem conforms_point_band_iff (lo rA rB rO : ℝ) :
    GoldschmidtConforms lo lo rA rB rO ↔ tolFac rA rB rO = lo := by
  unfold GoldschmidtConforms InBand
  exact ⟨fun hk => le_antisymm hk.2 hk.1, fun hk => ⟨hk.ge, hk.le⟩⟩

/-- Sharp failure below the window: an A radius strictly under `rAMin lo rB rO` violates the lower
band edge, so the triple cannot conform — with no hypothesis on the band itself. Read through the G3
radius-window equivalence, this is the contrapositive of its first conjunct (plan §7). -/
theorem not_conforms_of_lt_rAMin {lo hi rA rB rO : ℝ} (h : 0 < rB + rO)
    (h' : rA < rAMin lo rB rO) : ¬ GoldschmidtConforms lo hi rA rB rO := by
  intro hc
  have hw := (conforms_iff_radius_window h).mp hc
  linarith [hw.1]

/-- Sharp failure above the window, the mirror of `not_conforms_of_lt_rAMin`: an A radius strictly
above `rAMax hi rB rO` violates the upper band edge (plan §7). -/
theorem not_conforms_of_rAMax_lt {lo hi rA rB rO : ℝ} (h : 0 < rB + rO)
    (h' : rAMax hi rB rO < rA) : ¬ GoldschmidtConforms lo hi rA rB rO := by
  intro hc
  have hw := (conforms_iff_radius_window h).mp hc
  linarith [hw.2]

/-- **The tolerance factor is irrational at rational radii** (given `√2 ∉ ℚ`): for rational `rA rB rO`
with non-vanishing numerator sum and denominator sum, `tolFac ↑rA ↑rB ↑rO` is irrational.

Both hypotheses are load-bearing, not cosmetic: `rB + rO = 0` makes the denominator `0` (and the
factor `0`), `rA + rO = 0` makes the numerator `0` — either way the value is rational. The proof
factors the rational ratio out of the factor (`↑((rA+rO)/(rB+rO)) / √2`, the algebraic step
`unfold; push_cast; field_simp; ring`) and applies `Irrational.rat_mul` to `Irrational.inv` of
`irrational_sqrt_two` (plan §7, §12 row 10). This is why the decision layer G5 compares `t²` and not
`t` — stated in plan §9 as the reason for the `√2`-free form. -/
theorem tolFac_irrational {rA rB rO : ℚ} (hB : rB + rO ≠ 0) (hA : rA + rO ≠ 0) :
    Irrational (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)) := by
  have hq : (rA + rO) / (rB + rO) ≠ 0 := div_ne_zero hA hB
  have key : tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)
      = ((rA + rO) / (rB + rO) : ℚ) / Real.sqrt 2 := by
    have h2 : (Real.sqrt 2 : ℝ) ≠ 0 := (Real.sqrt_ne_zero').mpr (by norm_num)
    have hb : ((rB + rO : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hB
    unfold tolFac
    push_cast
    field_simp
    ring
  rw [key]
  have h : Irrational ((((rA + rO) / (rB + rO) : ℚ) : ℝ) * (Real.sqrt 2)⁻¹) :=
    (irrational_sqrt_two.inv).rat_mul hq
  simpa only [div_eq_mul_inv] using h

/-- **Goldschmidt's 15 % radius rule bounds the shift of the tolerance factor**: if `rA'` is within the
fraction `tauGoldschmidt = 3/20` of `rA` (the radius rule, `RadiusMatch`), the factor moves by at most
`tauGoldschmidt * rA` over the positive denominator `√2 (rB + rO)`.

Proof: the exact affine shift law `tolFac_abs_shift_eq` with `d = rA' - rA` turns the left-hand side
into `|rA' - rA| / (√2 (rB + rO))`, `abs_sub_comm` matches the radius rule's orientation, and the two
sides are compared by division with the positive denominator. This is the bridge from rule 1 of
Goldschmidt's rules to the band verdict of G3 (plan §7, §12 row 6). -/
theorem tolFacFifteen_le {rA rA' rB rO : ℝ} (h : 0 < rB + rO)
    (hm : RadiusMatch tauGoldschmidt rA rA') : |tolFac rA' rB rO - tolFac rA rB rO| ≤
      tauGoldschmidt * rA / (Real.sqrt 2 * (rB + rO)) := by
  have hD : (0 : ℝ) < Real.sqrt 2 * (rB + rO) :=
    mul_pos (Real.sqrt_pos_of_pos (by norm_num)) h
  rw [RadiusMatch] at hm
  have h' : |rA' - rA| ≤ tauGoldschmidt * rA := by
    rw [abs_sub_comm]
    exact hm
  rw [show rA' = rA + (rA' - rA) by ring,
    tolFac_abs_shift_eq (rA := rA) (rB := rB) (rO := rO) (d := rA' - rA) h]
  exact div_le_div_of_nonneg_right h' hD.le

/-- **The band verdict survives a substitution inside the 15 % window** (when the *whole* radius
window of `rA` conforms): if `RadiusMatch tau rA rA'` and the two window edges of `rA` already lie
inside `[rAMin lo rB rO, rAMax hi rB rO]`, then the substituted triple conforms to the same band.

Proof: `radiusMatch_iff_window` bounds `rA'` by `(1 ∓ tau) * rA`, and the G3 radius-window equivalence
converts the band verdict into the two edge inequalities, which `le_trans` chains. This is rule 1 of
Goldschmidt's rules as a *preservation* theorem — the honest form, since the rule alone does not
preserve conformance of a triple that merely conforms (plan §7, §11's risk note on the substitution
rows; the counterexample family is G6's `inst_radius_ok_but_band_lost`). -/
theorem conforms_of_radiusMatch_window {lo hi tau rA rA' rB rO : ℝ} (h : 0 < rB + rO)
    (hm : RadiusMatch tau rA rA') (hlo : rAMin lo rB rO ≤ (1 - tau) * rA)
    (hhi : (1 + tau) * rA ≤ rAMax hi rB rO) : GoldschmidtConforms lo hi rA' rB rO := by
  rw [conforms_iff_radius_window h]
  rw [radiusMatch_iff_window] at hm
  exact ⟨le_trans hlo hm.1, le_trans hm.2 hhi⟩

/-- Failure witness for the **too-small** zone of the classic band (`rA = -1`, normalized
`rB = rO = 1`): the squared decision form `conforms_iff_sq` reduces the verdict to the exact rational
comparison `2*(4/5)²*2² = 128/25 ≤ 0`, which fails. No `Real.sqrt` algebra enters (plan §7 witnesses,
§9 family I8 non-vacuity: the classifier is total). -/
theorem witness_tooSmall : ¬ GoldschmidtConforms classicLo classicHi (-1) 1 1 := by
  rw [conforms_iff_sq (by unfold classicLo; norm_num) (by unfold classicHi; norm_num)
    (by norm_num : (0 : ℝ) < 1 + 1) (by norm_num : (0 : ℝ) ≤ -1 + 1)]
  norm_num [classicLo, classicHi]

/-- Failure witness for the **too-large** zone of the classic band (`rA = 3`, `rB = rO = 1`): the
upper squared comparison reads `(3+1)² = 16 ≤ 2*1²*2² = 8`, which fails. Note the asymmetry visible
here — with normalized radii the classic band is narrow around `t = 1` (plan §7 witnesses, §9 I8). -/
theorem witness_tooLarge : ¬ GoldschmidtConforms classicLo classicHi 3 1 1 := by
  rw [conforms_iff_sq (by unfold classicLo; norm_num) (by unfold classicHi; norm_num)
    (by norm_num : (0 : ℝ) < 1 + 1) (by norm_num : (0 : ℝ) ≤ 3 + 1)]
  norm_num [classicLo, classicHi]

/-- The **inverted band** `[1, 4/5]` has no conforming triple, instantiated at the normalized model
row: an immediate corollary of this milestone's `not_conforms_of_band_empty`, which is exactly the
sharpness companion of G3's `exists_conforming` (plan §7 witnesses). -/
theorem witness_inverted_band : ¬ GoldschmidtConforms 1 classicLo 0 1 1 :=
  not_conforms_of_band_empty (by unfold classicLo; norm_num)

/-- The model's positive row: the ideal A radius `idealA 1 1` conforms to the classic band, because it
puts the factor at exactly `1`. Reuses G3's `conforms_at_idealA_classic` — the ideal-packing
identification `contact_iff_tolFac_one` is what makes `t = 1` land on the band's upper edge
(plan §7 witnesses, §9 family I1). -/
theorem witness_ideal_packing : GoldschmidtConforms classicLo classicHi (idealA 1 1) 1 1 :=
  conforms_at_idealA_classic (by norm_num : (0 : ℝ) < 1 + 1)

/-- The **band flip** with Shannon's printed radii for `BaTiO₃` (`rA = 1.61`, `rB = 0.605`,
`rO = 1.40` Å; plan §9 family I3): the triple conforms to the tetragonal band `[1, 11/10]` but **not**
to the classic cubic band `[4/5, 1]`. Both halves are exact rational comparisons through G3's
`conforms_iff_sq` (`t² = 181202/160801` for this row, plan §3.1's cross-check section), so the flip is
a theorem about a *band convention*, not prose: `2*(401/200)² ≤ (301/100)² ≤ 2*(11/10)²*(401/200)²`
holds, while `(301/100)² ≤ 2*1²*(401/200)²` fails (plan §7 witnesses, §9 I3, §11 risk row 6). -/
theorem witness_band_flip : GoldschmidtConforms classicHi tetragonalHi (161 / 100) (121 / 200)
    (7 / 5) ∧ ¬ GoldschmidtConforms classicLo classicHi (161 / 100) (121 / 200) (7 / 5) := by
  constructor
  · rw [conforms_iff_sq (by unfold classicHi; norm_num) (by unfold tetragonalHi; norm_num)
      (by norm_num : (0 : ℝ) < 121 / 200 + 7 / 5)
      (by norm_num : (0 : ℝ) ≤ 161 / 100 + 7 / 5)]
    norm_num [classicHi, tetragonalHi]
  · rw [conforms_iff_sq (by unfold classicLo; norm_num) (by unfold classicHi; norm_num)
      (by norm_num : (0 : ℝ) < 121 / 200 + 7 / 5)
      (by norm_num : (0 : ℝ) ≤ 161 / 100 + 7 / 5)]
    norm_num [classicLo, classicHi]

end Goldschmidt

end PhotoLean
