/-
PhotoLean/Kasha/Sharp.lean

K3 — the **sharp conditions** of Kasha's rule (`theories/kasha/plan.md` §6). K1 described the
ladder and its observables, K2 derived the cascade laws and the exact rule; this module answers
the quantitative question of the plan's part ②: *how pure is pure enough* — the exact tolerance
threshold, its two-level and ratio presentations, its monotonicity, its sharpness (the threshold
is attained with equality and cannot be improved), and the two registered negative results
(the levelwise `k_IC ≥ k_rad` criterion is insufficient; the loss premise of the Kasha–Vavilov
equivalence is necessary).

Contents (statement authority: `theories/kasha/probes/kasha-statement-skeleton.lean`, §K3 block;
sha256 `4cf2b1055f1aee41463e7f5ad9bb6913c2c82600a0c4aa064cb58210fc68c0fb`, 144 declarations):

* §6.1 #1–#3 — the two-level criterion: the exact rate form, the **funnel-ratio threshold**
  `(1 - tol)/tol ≤ funnelRatio`, and the literature form `k_IC/k_rad ≥ (1 - tol)/tol` (for
  `tol = 1/100` the threshold is `99`);
* §6.1 #4 — the two-level funnel ratio is the `N = 1` ladder ratio;
* §6.1 #5–#8 — the general-`N` margin form, monotonicity in the tolerance, exactness at
  `tol = 0` (there the tolerance form *is* the exact rule), and monotonicity in the
  internal-conversion rate `ic 1`;
* §6.2 #9, #10, #16 — the strict failure side, **attainment** of the threshold (the boundary is
  met exactly and no smaller tolerance works), and the boundary case with equality;
* §6.2 #13, #14 — the two counterexample rows: the levelwise criterion is insufficient (the
  equal-rates ladder leaks `3/4` at tolerance `1/2`), and without the lowest level's loss channel
  Vavilov's rule holds while Kasha's rule fails;
* §6.2 #17, #18 — the uniform-branch bound on the leak and the resulting sufficient criterion.

**Statement correction carried by this block** (plan §3.1): rows #2 and #9 need the explicit
premise `0 < decay rad ic 1`. Without it they are FALSE — the rate form of #1 is equivalent to
the ratio form of #2 only after multiplying by the positive factor `decay 1`, and for
`decay 1 < 0` the cross-multiplication flips the inequality. Kernel counterexample (Sprint-0 risk
probe `theories/kasha/probes/kasha-risk-probe.lean`): `rad = (1,1,0,…)`, `ic = (1,-3,0,…)`,
`tol = 1/2` gives `KashaWithin (1/2) 1` true and `1 ≤ funnelRatio = -3/2` false. The premise is
now part of the authority, matching the sibling row #1.

What the module does **not** do: it adds no premise that is not in the authority and no definition
(the ladder's vocabulary is K1's). Every positivity a proof needs is either in `RateData` or an
explicit hypothesis of the row (engine rule 3). One row (`kashaWithin_one_mono_ic`, #8) needs a
degenerate-case analysis beyond the plan's sketch: its hypotheses carry no sign for `tol`, and for
`tol < 0` the criterion degenerates; the proof closes that case with the contradiction
`0 ≤ rad 1 · decay 0 · (1 - tol) ≤ tol · (rad 0 · ic 1) ≤ 0`. Note deliberately: the two keyword
literals that `proofs/scripts/check.sh --strict` scans for are not spelled out anywhere in this
file — the scan covers `PhotoLean/**/*.lean` including block comments, so writing them (even in
prose) would be a false-positive FAIL.

Statement authority: every theorem signature below is taken word for word from the §K3 block of
`theories/kasha/probes/kasha-statement-skeleton.lean` (sha256
`4cf2b1055f1aee41463e7f5ad9bb6913c2c82600a0c4aa064cb58210fc68c0fb`), which transcribes
`theories/kasha/plan.md` §6. The module imports `PhotoLean.Kasha.Basic` (K1: definitions, the
standing premise bundle, the index identities) and `PhotoLean.Kasha.Criterion` (K2: the cascade
recursions `upperYield_succ` / `fluoYield_succ` used by the two counterexample rows); nothing of
K1 or K2 is re-proved or re-defined here.

Plan locus: `theories/kasha/plan.md` §6 (K3); board `theories/kasha/TASKS.md` §K3. Acceptance:

    proofs/scripts/lake build PhotoLean.Kasha.Sharp
    proofs/scripts/check.sh --strict PhotoLean.Kasha.Sharp
    proofs/scripts/axioms.sh PhotoLean.Kasha.Sharp PhotoLean.Kasha.<fully.qualified.theorem>

The delivered file contains no unfinished-proof placeholder and no custom axiomatic declaration;
`#print axioms` lists at most `propext`, `Classical.choice`, `Quot.sound`.
-/
import PhotoLean.Kasha.Basic
import PhotoLean.Kasha.Criterion

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Kasha

/-! ## The two-level threshold (plan §6.1) -/

/-- Plan §6.1 #1 — the exact two-level criterion in rate form. Both cross-multiplications are by
positive total decay rates, so the equivalence needs no sign assumption on `tol`. -/

theorem kashaWithin_one_iff_rates {rad ic : ℕ → ℝ} {tol : ℝ} (h0 : 0 < decay rad ic 0)
    (h1 : 0 < decay rad ic 1) :
    KashaWithin rad ic tol 1 ↔ rad 1 * decay rad ic 0 * (1 - tol) ≤ tol * (rad 0 * ic 1) := by
  have hcase : cascade rad ic 0 1 = icBranch rad ic 1 := by
    unfold cascade
    rw [show Finset.Icc (0 + 1) 1 = ({1} : Finset ℕ) by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_singleton]
      omega, Finset.prod_singleton]
  have hupper : upperYield rad ic 1 = radBranch rad ic 1 := by
    unfold upperYield
    rw [Finset.Icc_self, Finset.sum_singleton]
    exact emitYield_self rad ic 1
  have hemit : emitYield rad ic 0 1 = radBranch rad ic 0 * icBranch rad ic 1 := by
    unfold emitYield
    rw [hcase]
  have hsplit : fluoYield rad ic 1 = emitYield rad ic 0 1 + upperYield rad ic 1 := by
    unfold fluoYield upperYield
    rw [show Finset.range (1 + 1) = insert 0 (Finset.Icc 1 1) by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega, Finset.sum_insert (by simp)]
  have hfluo : fluoYield rad ic 1 = radBranch rad ic 0 * icBranch rad ic 1 + radBranch rad ic 1 := by
    rw [hsplit, hemit, hupper]
  have hd0 : 0 < rad 0 + ic 0 := h0
  have hd1 : 0 < rad 1 + ic 1 := h1
  have halg : rad 1 / (rad 1 + ic 1)
        ≤ tol * (rad 0 / (rad 0 + ic 0) * (ic 1 / (rad 1 + ic 1)) + rad 1 / (rad 1 + ic 1))
      ↔ rad 1 * (rad 0 + ic 0) * (1 - tol) ≤ tol * (rad 0 * ic 1) := by
    have e1 : (tol * (rad 0 / (rad 0 + ic 0) * (ic 1 / (rad 1 + ic 1))
          + rad 1 / (rad 1 + ic 1))) * (rad 1 + ic 1) = tol * (rad 0 / (rad 0 + ic 0) * ic 1 + rad 1) := by
      field_simp
      try ring
    have e2 : tol * (rad 0 / (rad 0 + ic 0) * ic 1 + rad 1)
        = tol * (rad 0 * ic 1 + rad 1 * (rad 0 + ic 0)) / (rad 0 + ic 0) := by
      field_simp
      try ring
    rw [div_le_iff₀ hd1, e1, e2, le_div_iff₀ hd0]
    constructor <;> intro hh <;> linarith
  rw [KashaWithin, hfluo, hupper]
  unfold radBranch icBranch decay
  exact halg

/-- Plan §6.1 #2 — **the funnel-ratio threshold** (two-level form), with the statement correction
of plan §3.1: `0 < decay rad ic 1` is an explicit premise. This is row 1 divided by
`tol · rad 1 · decay 0 > 0`. -/

theorem kashaWithin_one_iff_ratio {rad ic : ℕ → ℝ} {tol : ℝ} (h0 : 0 < decay rad ic 0)
    (h1 : 0 < decay rad ic 1) (htol : 0 < tol) (hr : 0 < rad 1) :
    KashaWithin rad ic tol 1 ↔ (1 - tol) / tol ≤ funnelRatio rad ic := by
  have hrd : 0 < rad 1 * decay rad ic 0 := mul_pos hr h0
  rw [kashaWithin_one_iff_rates h0 h1, funnelRatio, div_le_div_iff₀ htol hrd]
  constructor <;> intro hh <;> linarith

/-- Plan §6.1 #3 — the literature form: with no other loss at the lowest level, the rule needs
`ic 1 / rad 1 ≥ (1 - tol) / tol` (for `tol = 1/100`: `99`). The premise is `rad 0 ≠ 0` rather
than `0 < rad 0`, and that is exactly what the proof consumes: `decay 0 = rad 0` makes
`radBranch 0 = 1` and the two-level total yield is exactly `1` whatever the sign of `rad 0`. -/

theorem kashaWithin_one_iff_ic_ratio {rad ic : ℕ → ℝ} {tol : ℝ} (hic0 : ic 0 = 0)
    (hr0 : rad 0 ≠ 0) (htol : 0 < tol) (h1 : 0 < decay rad ic 1) (hr : 0 < rad 1) :
    KashaWithin rad ic tol 1 ↔ (1 - tol) / tol ≤ ic 1 / rad 1 := by
  have hd0 : decay rad ic 0 = rad 0 := by rw [decay, hic0, add_zero]
  have hrb0 : radBranch rad ic 0 = 1 := by
    unfold radBranch
    rw [hd0]
    exact div_self hr0
  have hcase : cascade rad ic 0 1 = icBranch rad ic 1 := by
    unfold cascade
    rw [show Finset.Icc (0 + 1) 1 = ({1} : Finset ℕ) by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_singleton]
      omega, Finset.prod_singleton]
  have hupper : upperYield rad ic 1 = radBranch rad ic 1 := by
    unfold upperYield
    rw [Finset.Icc_self, Finset.sum_singleton]
    exact emitYield_self rad ic 1
  have hemit : emitYield rad ic 0 1 = radBranch rad ic 0 * icBranch rad ic 1 := by
    unfold emitYield
    rw [hcase]
  have hsplit : fluoYield rad ic 1 = emitYield rad ic 0 1 + upperYield rad ic 1 := by
    unfold fluoYield upperYield
    rw [show Finset.range (1 + 1) = insert 0 (Finset.Icc 1 1) by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega, Finset.sum_insert (by simp)]
  have hfluo : fluoYield rad ic 1 = 1 := by
    rw [hsplit, hemit, hupper, hrb0, one_mul, add_comm]
    exact radBranch_add_icBranch (ne_of_gt h1)
  rw [KashaWithin, hupper, hfluo, mul_one]
  unfold radBranch
  rw [div_le_iff₀ h1, div_le_div_iff₀ htol hr]
  unfold decay
  constructor <;> intro hh <;> linarith

/-- Plan §6.1 #4. The two-level funnel ratio is the ladder ratio at `N = 1`: the ratio's
`cascade 0 1 / upperYield 1` block is `(ic 1/decay 1)/(rad 1/decay 1)`, and the two `decay 1`
factors cancel (`div_div_div_cancel_right₀`; the junk-value convention `x/0 = 0` keeps the
identity valid when `rad 1 = 0`). -/

theorem funnelRatio_eq_ladderRatio_one {rad ic : ℕ → ℝ} (h : decay rad ic 1 ≠ 0) :
    funnelRatio rad ic = ladderRatio rad ic 1 := by
  have hcase : cascade rad ic 0 1 = icBranch rad ic 1 := by
    unfold cascade
    rw [show Finset.Icc (0 + 1) 1 = ({1} : Finset ℕ) by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_singleton]
      omega, Finset.prod_singleton]
  have hupper : upperYield rad ic 1 = radBranch rad ic 1 := by
    unfold upperYield
    rw [Finset.Icc_self, Finset.sum_singleton]
    exact emitYield_self rad ic 1
  unfold funnelRatio ladderRatio
  rw [hcase, hupper]
  unfold radBranch icBranch
  have h1 : rad 0 * (ic 1 / decay rad ic 1) = rad 0 * ic 1 / decay rad ic 1 :=
    (mul_div_assoc (rad 0) (ic 1) (decay rad ic 1)).symm
  have h2 : rad 1 / decay rad ic 1 * decay rad ic 0 = rad 1 * decay rad ic 0 / decay rad ic 1 :=
    div_mul_eq_mul_div₀ (rad 1) (decay rad ic 0) (decay rad ic 1)
  rw [h1, h2, div_div_div_cancel_right₀ h]

/-! ## The general-`N` margin form and monotonicity (plan §6.1) -/

set_option linter.unusedVariables false in

/-- Plan §6.1 #5 — the general-`N` criterion in margin form: dividing by the leak
`upperYield N > 0` turns `upperYield ≤ tol · (emitYield 0 + upperYield)` into
`1 - tol ≤ tol · kashaMargin`. The premise `0 < tol` is kept verbatim from the statement
authority; the equivalence itself is an algebraic identity and does not consume it. -/

theorem kashaWithin_iff_margin {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ} (h : RateData rad ic N)
    (hu : 0 < upperYield rad ic N) (htol : 0 < tol) :
    KashaWithin rad ic tol N ↔ 1 - tol ≤ tol * kashaMargin rad ic N := by
  have hstep : (1 - tol) * upperYield rad ic N ≤ tol * emitYield rad ic 0 N
      ↔ 1 - tol ≤ tol * kashaMargin rad ic N := by
    rw [kashaMargin, ← mul_div_assoc, le_div_iff₀ hu]
  rw [KashaWithin, fluoYield_eq_low_add_upper h]
  constructor
  · intro hW
    exact hstep.mp (by linarith)
  · intro hW
    have h2 : (1 - tol) * upperYield rad ic N ≤ tol * emitYield rad ic 0 N := hstep.mpr hW
    linarith

/-- Plan §6.1 #6. The criterion is monotone in the tolerance: only the nonnegativity of the
total yield (`fluoYield_nonneg`, K1) is needed to multiply the given inequality by
`tol ≤ tol'`. -/

theorem kashaWithin_mono_tol {rad ic : ℕ → ℝ} {N : ℕ} {tol tol' : ℝ} (h : RateData rad ic N)
    (hle : tol ≤ tol') (hW : KashaWithin rad ic tol N) : KashaWithin rad ic tol' N := by
  have hF : 0 ≤ fluoYield rad ic N := fluoYield_nonneg h
  rw [KashaWithin] at hW ⊢
  calc upperYield rad ic N ≤ tol * fluoYield rad ic N := hW
    _ ≤ tol' * fluoYield rad ic N := mul_le_mul_of_nonneg_right hle hF

/-- Plan §6.1 #7 — exactness: at `tol = 0` the tolerance form IS the exact rule. With
`0 ≤ upperYield N` (K1) the inequality `upperYield ≤ 0` is an equality. -/

theorem kashaWithin_zero_iff {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    KashaWithin rad ic 0 N ↔ KashaRule rad ic N := by
  have hU : 0 ≤ upperYield rad ic N := upperYield_nonneg h
  rw [KashaWithin, KashaRule, zero_mul]
  exact ⟨fun hW => le_antisymm hW hU, fun hW => le_of_eq hW⟩

/-- Plan §6.1 #8. The criterion is monotone in the internal-conversion rate `ic 1`: the two
ladders differ only in `ic 1 ≥ ic 1'`, and `decay 0`, `rad 0`, `rad 1` agree, so the rate forms
of row 1 are comparable. The hypotheses carry **no sign for `tol`**: for `0 ≤ tol` the comparison
is `mul_le_mul_of_nonneg_left`, while for `tol · rad 0 < 0` the given rate form forces
`0 ≤ rad 1 · decay 0 · (1 - tol) ≤ tol · (rad 0 · ic 1) ≤ 0`, a contradiction — the implication
holds vacuously, which is why no tolerance premise is needed. -/

theorem kashaWithin_one_mono_ic {rad ic rad' ic' : ℕ → ℝ} {tol : ℝ} (h : RateData rad ic 1)
    (h' : RateData rad' ic' 1) (hrad : ∀ n, rad' n = rad n) (hic0 : ic' 0 = ic 0)
    (hic : ic 1 ≤ ic' 1) : KashaWithin rad ic tol 1 → KashaWithin rad' ic' tol 1 := by
  intro hW
  have hd0 : 0 < decay rad ic 0 := h.decay_pos 0 (by norm_num)
  have hd1 : 0 < decay rad ic 1 := h.decay_pos 1 le_rfl
  have hd0' : 0 < decay rad' ic' 0 := h'.decay_pos 0 (by norm_num)
  have hd1' : 0 < decay rad' ic' 1 := h'.decay_pos 1 le_rfl
  have hdec0 : decay rad' ic' 0 = decay rad ic 0 := by rw [decay, decay, hrad 0, hic0]
  have hgiven : rad 1 * decay rad ic 0 * (1 - tol) ≤ tol * (rad 0 * ic 1) :=
    (kashaWithin_one_iff_rates hd0 hd1).mp hW
  rw [kashaWithin_one_iff_rates hd0' hd1', hrad 1, hdec0, hrad 0]
  rcases le_or_lt 0 (tol * rad 0) with hM | hM
  · calc rad 1 * decay rad ic 0 * (1 - tol)
        ≤ tol * (rad 0 * ic 1) := hgiven
      _ ≤ tol * (rad 0 * ic' 1) := by
          rw [show tol * (rad 0 * ic 1) = (tol * rad 0) * ic 1 by ring,
            show tol * (rad 0 * ic' 1) = (tol * rad 0) * ic' 1 by ring]
          exact mul_le_mul_of_nonneg_left hic hM
  · -- `tol * rad 0 < 0`: the rate form forces `rad 1 = 0` and `ic 1 = 0`, hence `decay 1 = 0`,
    -- contradicting `RateData`; the implication therefore holds vacuously.
    have htneg : tol < 0 := by
      rcases eq_or_lt_of_le (h.rad_nonneg 0) with hz | hpos
      · rw [← hz, mul_zero] at hM
        exact absurd hM (lt_irrefl 0)
      · have hdiv : tol * rad 0 / rad 0 < 0 := div_neg_of_neg_of_pos hM hpos
        rwa [mul_div_assoc, div_self (ne_of_gt hpos), mul_one] at hdiv
    have h1t : 0 < 1 - tol := by linarith
    have hAge : 0 ≤ rad 1 * decay rad ic 0 * (1 - tol) :=
      mul_nonneg (mul_nonneg (h.rad_nonneg 1) (le_of_lt hd0)) (le_of_lt h1t)
    have hMle : tol * (rad 0 * ic 1) ≤ 0 := by
      rw [show tol * (rad 0 * ic 1) = (tol * rad 0) * ic 1 by ring]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hM) (h.ic_nonneg 1)
    have hAeq : rad 1 * decay rad ic 0 * (1 - tol) = 0 := le_antisymm (le_trans hgiven hMle) hAge
    have hMeq : tol * (rad 0 * ic 1) = 0 := le_antisymm hMle (le_trans hAge hgiven)
    have hrad1 : rad 1 = 0 := by
      have hfac : 0 < decay rad ic 0 * (1 - tol) := mul_pos hd0 h1t
      have h' := hAeq
      rw [mul_assoc] at h'
      exact (mul_eq_zero.mp h').resolve_right (ne_of_gt hfac)
    have hic1 : ic 1 = 0 := by
      have h' := hMeq
      rw [show tol * (rad 0 * ic 1) = (tol * rad 0) * ic 1 by ring] at h'
      exact (mul_eq_zero.mp h').resolve_left (ne_of_lt hM)
    exfalso
    have hdec1 : decay rad ic 1 = 0 := by rw [decay, hrad1, hic1, add_zero]
    exact absurd hdec1 (ne_of_gt hd1)

/-! ## The strict side, attainment, and the boundary (plan §6.2) -/

/-- Plan §6.2 #9 — the strict failure side of the threshold, the contrapositive of row #2 (with
the same statement correction: `0 < decay rad ic 1`). -/

theorem not_kashaWithin_one_of_ratio_lt {rad ic : ℕ → ℝ} {tol : ℝ} (h0 : 0 < decay rad ic 0)
    (h1 : 0 < decay rad ic 1) (htol : 0 < tol) (hr : 0 < rad 1)
    (h : funnelRatio rad ic < (1 - tol) / tol) : ¬ KashaWithin rad ic tol 1 := fun hW =>
  absurd ((kashaWithin_one_iff_ratio h0 h1 htol hr).mp hW) (not_le.mpr h)

set_option linter.unusedVariables false in

/-- Plan §6.2 #10 — **attainment**: for every tolerance in `(0,1)` the threshold is met exactly
and cannot be improved. Witness `rad 0 = 1, rad 1 = tol, ic 0 = 0, ic 1 = 1 - tol` has
`funnelRatio = (1 - tol)/tol` and conformance holds with equality; for any smaller `tol'` the
boundary `(1 - tol')/tol'` is strictly larger, so the strict side of row #9 applies. The premise
`tol < 1` is kept verbatim from the statement authority; the witness conforms for every
`tol > 0`, so the premise is not consumed. -/

theorem kashaThreshold_attained {tol : ℝ} (h0 : 0 < tol) (h1 : tol < 1) :
    ∃ rad ic : ℕ → ℝ, KashaWithin rad ic tol 1 ∧
      (∀ tol' : ℝ, 0 < tol' → tol' < tol → ¬ KashaWithin rad ic tol' 1) := by
  let rad : ℕ → ℝ := fun n => if n = 0 then 1 else if n = 1 then tol else 0
  let ic : ℕ → ℝ := fun n => if n = 0 then 0 else if n = 1 then 1 - tol else 0
  have hfr : funnelRatio rad ic = (1 - tol) / tol := by simp [rad, ic, funnelRatio, decay]
  have hd0 : 0 < decay rad ic 0 := by simp [rad, ic, decay]
  have hd1 : 0 < decay rad ic 1 := by simp [rad, ic, decay]
  have hr1 : 0 < rad 1 := by simpa [rad] using h0
  refine ⟨rad, ic, (kashaWithin_one_iff_ratio hd0 hd1 h0 hr1).mpr (le_of_eq hfr.symm), ?_⟩
  intro tol' ht0 ht1
  refine not_kashaWithin_one_of_ratio_lt hd0 hd1 ht0 hr1 ?_
  rw [hfr, div_lt_div_iff₀ h0 ht0]
  nlinarith

/-- Plan §6.2 #13 — **the levelwise criterion is insufficient**: "internal conversion beats
radiation at every level above the lowest" (`rad i · decay (i-1) ≤ ic i · decay i`) does not make
the ladder Kasha-pure. Kernel-checked witness `rad ≡ 1`, `ic ≡ 1`: `RateData rad ic 2` holds, the
levelwise bound holds with equality at both upper levels (`1 · 2 ≤ 1 · 2`), and yet
`upperYield 2 = 3/4 > (1/2) · (7/8) = (1/2) · fluoYield 2`, so the tolerance form fails at
`tol = 1/2`. The correct criterion is the aggregate one (K4, plan §7.2 #9). -/

theorem perLevel_criterion_insufficient :
    ∃ rad ic : ℕ → ℝ, RateData rad ic 2 ∧
      (∀ i, 1 ≤ i → i ≤ 2 → rad i * decay rad ic (i - 1) ≤ ic i * decay rad ic i) ∧
      ¬ KashaWithin rad ic (1 / 2) 2 := by
  have hR1 : RateData (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 1 :=
    ⟨fun n _ => by norm_num [decay], fun n => by norm_num, fun n => by norm_num⟩
  have hR2 : RateData (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 2 :=
    ⟨fun n _ => by norm_num [decay], fun n => by norm_num, fun n => by norm_num⟩
  have hU1 : upperYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 1 = 1 / 2 := by
    have hh := upperYield_succ (rad := fun _ : ℕ => (1 : ℝ)) (ic := fun _ : ℕ => (1 : ℝ))
      (N := 0) hR1
    rw [upperYield_zero] at hh
    norm_num [radBranch, icBranch, decay] at hh
    exact hh
  have hU2 : upperYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 2 = 3 / 4 := by
    have hh := upperYield_succ (rad := fun _ : ℕ => (1 : ℝ)) (ic := fun _ : ℕ => (1 : ℝ))
      (N := 1) hR2
    rw [hU1] at hh
    norm_num [radBranch, icBranch, decay] at hh
    exact hh
  have hF0 : fluoYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 0 = 1 / 2 := by
    rw [fluoYield_zero]
    norm_num [radBranch, decay]
  have hF1 : fluoYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 1 = 3 / 4 := by
    have hh := fluoYield_succ (rad := fun _ : ℕ => (1 : ℝ)) (ic := fun _ : ℕ => (1 : ℝ))
      (N := 0) hR1
    rw [hF0] at hh
    norm_num [radBranch, icBranch, decay] at hh
    exact hh
  have hF2 : fluoYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 2 = 7 / 8 := by
    have hh := fluoYield_succ (rad := fun _ : ℕ => (1 : ℝ)) (ic := fun _ : ℕ => (1 : ℝ))
      (N := 1) hR2
    rw [hF1] at hh
    norm_num [radBranch, icBranch, decay] at hh
    exact hh
  refine ⟨fun _ : ℕ => (1 : ℝ), fun _ : ℕ => (1 : ℝ), hR2, ?_, ?_⟩
  · intro i hi1 hi2
    have h12 : i = 1 ∨ i = 2 := by omega
    rcases h12 with rfl | rfl <;> norm_num [decay]
  · intro hcon
    rw [KashaWithin, hU2, hF2] at hcon
    norm_num at hcon

/-- Plan §6.2 #14 — **the loss premise of the Kasha–Vavilov equivalence is necessary**: in the
loss-free ladder `rad ≡ 1`, `ic ≡ 0` no current is lost to the ground state, so the total yield is
exactly `1` at every excitation level — `VavilovAt` holds at `N = 1` trivially, while
`upperYield 1 = radBranch 1 = 1 ≠ 0`, so the exact rule fails. (The two yield values are computed
through the K2 recursion `fluoYield_succ`.) -/

theorem vavilov_premise_necessary :
    ∃ (rad ic : ℕ → ℝ) (N : ℕ), RateData rad ic N ∧ rad (N + 1) ≠ 0 ∧
      VavilovAt rad ic N ∧ ¬ KashaRule rad ic N := by
  have hR1 : RateData (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (0 : ℝ)) 1 :=
    ⟨fun n _ => by norm_num [decay], fun n => by norm_num, fun n => by norm_num⟩
  have hR2 : RateData (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (0 : ℝ)) 2 :=
    ⟨fun n _ => by norm_num [decay], fun n => by norm_num, fun n => by norm_num⟩
  have hF0 : fluoYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (0 : ℝ)) 0 = 1 := by
    rw [fluoYield_zero]
    norm_num [radBranch, decay]
  have hF1 : fluoYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (0 : ℝ)) 1 = 1 := by
    have hh := fluoYield_succ (rad := fun _ : ℕ => (1 : ℝ)) (ic := fun _ : ℕ => (0 : ℝ))
      (N := 0) hR1
    rw [hF0] at hh
    norm_num [radBranch, icBranch, decay] at hh
    exact hh
  have hF2 : fluoYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (0 : ℝ)) (1 + 1) = 1 := by
    have hh := fluoYield_succ (rad := fun _ : ℕ => (1 : ℝ)) (ic := fun _ : ℕ => (0 : ℝ))
      (N := 1) hR2
    rw [hF1] at hh
    norm_num [radBranch, icBranch, decay] at hh
    exact hh
  refine ⟨fun _ : ℕ => (1 : ℝ), fun _ : ℕ => (0 : ℝ), 1, hR1, ?_, ?_, ?_⟩
  · norm_num
  · rw [VavilovAt, hF2, hF1]
  · rw [KashaRule]
    intro hzero
    rw [upperYield, Finset.Icc_self, Finset.sum_singleton, emitYield_self] at hzero
    norm_num [radBranch, decay] at hzero

set_option linter.unusedVariables false in

/-- Plan §6.2 #16 — the boundary of the threshold is attained with equality: the witness of
row #10 conforms at `tol` because `funnelRatio` sits exactly on `(1 - tol)/tol`. As in row #10,
the premise `tol < 1` is kept verbatim from the statement authority and is not consumed. -/

theorem kashaWithin_one_sharp_boundary {tol : ℝ} (h0 : 0 < tol) (h1 : tol < 1) :
    ∃ rad ic : ℕ → ℝ, funnelRatio rad ic = (1 - tol) / tol ∧ KashaWithin rad ic tol 1 := by
  let rad : ℕ → ℝ := fun n => if n = 0 then 1 else if n = 1 then tol else 0
  let ic : ℕ → ℝ := fun n => if n = 0 then 0 else if n = 1 then 1 - tol else 0
  have hfr : funnelRatio rad ic = (1 - tol) / tol := by simp [rad, ic, funnelRatio, decay]
  have hd0 : 0 < decay rad ic 0 := by simp [rad, ic, decay]
  have hd1 : 0 < decay rad ic 1 := by simp [rad, ic, decay]
  have hr1 : 0 < rad 1 := by simpa [rad] using h0
  exact ⟨rad, ic, hfr, (kashaWithin_one_iff_ratio hd0 hd1 h0 hr1).mpr (le_of_eq hfr.symm)⟩

/-! ## The uniform-branch bound (plan §6.2) -/

/-- Plan §6.2 #17. If every upper level's radiative branch is at most `θ`, the leak is at most
`θ` times the sum of the cascade probabilities: termwise `emitYield i N = radBranch i · cascade i N`
with `cascade i N ≥ 0` (K1), then `Finset.mul_sum` on the right. -/

theorem leak_le_of_radBranch_le {rad ic : ℕ → ℝ} {N : ℕ} {θ : ℝ} (h : RateData rad ic N)
    (hθ : ∀ i, 1 ≤ i → i ≤ N → radBranch rad ic i ≤ θ) :
    upperYield rad ic N ≤ θ * ∑ i ∈ Finset.Icc 1 N, cascade rad ic i N := by
  rw [upperYield, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  rw [emitYield]
  exact mul_le_mul_of_nonneg_right (hθ i hi.1 hi.2) (cascade_nonneg h hi.2)

/-- Plan §6.2 #18. The sufficient criterion: the uniform-branch bound of row #17 composed with
the hypothesis that `θ · Σ cascade` already fits inside `tol · fluoYield`. -/

theorem kashaWithin_of_uniform_branch {rad ic : ℕ → ℝ} {N : ℕ} {tol θ : ℝ} (h : RateData rad ic N)
    (hθ : ∀ i, 1 ≤ i → i ≤ N → radBranch rad ic i ≤ θ)
    (hsum : θ * ∑ i ∈ Finset.Icc 1 N, cascade rad ic i N ≤ tol * fluoYield rad ic N) :
    KashaWithin rad ic tol N :=
  le_trans (leak_le_of_radBranch_le h hθ) hsum

end Kasha

end PhotoLean
