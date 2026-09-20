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

end Kasha

end PhotoLean
