/-
Kernel counterexample to plan §4.2 row 24 (`kashaZone_eq_violating_iff`) of the Kasha theory,
raised by prover_a while delivering K1 (`PhotoLean/Kasha/Basic.lean`). The statement authority
`theories/kasha/probes/kasha-statement-skeleton.lean` handed over, with no premise on `tol`:

    theorem kashaZone_eq_violating_iff {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ} (h : RateData rad ic N) :
        kashaZone rad ic tol N = KashaZone.violating ↔ ¬ KashaWithin rad ic tol N

The forward direction is fine (the third branch of the classifier means both guards failed, so the
tolerance is exceeded). The backward direction is FALSE: the classifier tests the vanishing of the
leak *first*, and

    upperYield = 0  →  kashaZone = pure  →  kashaZone ≠ violating,

so `¬ KashaWithin` can hold with the classifier parked in `pure`, namely when the leak vanishes and
`tol * fluoYield < 0` (then `0 ≤ upperYield ≤ tol * fluoYield` fails, yet the first guard fires).
The `RateData` premise does not exclude that: it bounds `decay`/`rad`/`ic`, not `tol`.

Witness (the equal-rates ladder at excitation level 0): `rad ≡ 1`, `ic ≡ 1`, `N = 0`, `tol = -1`.
Then `decay 0 = 2 > 0` and the rates are nonnegative (so `RateData rad ic 0`), `upperYield = 0`
(empty `Icc 1 0`), so `kashaZone = pure`, while `KashaWithin rad ic (-1) 0` is `0 ≤ -1 * (1/2)`,
which is false — hence the right-hand side is true and the left-hand side is false.

THEOREM `kashaZone_eq_violating_iff_counterexample` below states exactly that, with the witness
values substituted into the skeleton's signature; every ingredient is proved, not assumed, and the
module `PhotoLean.Kasha.Basic` supplies the definitions (so the evidence is about the delivered
description layer, not about a private copy).

Consequence for the milestone: the row is **withheld** from `PhotoLean/Kasha/Basic.lean` until the
statement authority carries a corrected form (statement changes go through the authority). Two
minimal corrections keep the skeleton's right-hand side and restore provability:

  (a) add `(htol : 0 < tol)` to the hypotheses — under `RateData`, `upperYield = 0` then gives
      `KashaWithin`, because `0 ≤ tol * fluoYield`; or
  (b) restate the right-hand side as `¬ KashaRule rad ic N ∧ ¬ KashaWithin rad ic tol N`, which
      mirrors the two failing guards of the classifier (`¬ KashaRule` supplies exactly the
      `upperYield ≠ 0` that the vanishing-leak branch would otherwise pre-empt).

Twin row in ℚ (K5a, `PhotoLean/Kasha/RatModel.lean`): `kashaQVerdict_eq_violating_iff` has the same
shape with `QRateData` and breaks at the same witness (`rad ≡ 1`, `ic ≡ 1`, `N = 0`, `tol = -1`),
so it needs the same correction; the ℚ classifier's first guard is likewise the vanishing leak.

Owner of this probe: prover_a (K1). It lives outside `SOURCE_DIRS` (`PhotoLean`), like the
statement skeleton itself.
-/
import PhotoLean.Kasha.Basic

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Kasha

/-- The witness ladder at level 0: `upperYield (1, 1) 0 = 0` (the empty sum over `Icc 1 0`). -/
theorem upperYield_witness : upperYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => 1) 0 = 0 := by
  unfold upperYield
  simp

/-- The witness ladder at level 0: `fluoYield (1, 1) 0 = radBranch 0 = 1 / (1 + 1) = 1 / 2`. -/
theorem fluoYield_witness : fluoYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => 1) 0 = 1 / 2 := by
  unfold fluoYield emitYield radBranch cascade decay
  rw [Finset.sum_range_one, Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 by omega)]
  norm_num

/-- The witness ladder satisfies the standing premise bundle. -/
theorem rateData_witness : RateData (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => 1) 0 := by
  refine ⟨fun n hn => ?_, fun n => by norm_num, fun n => by norm_num⟩
  unfold decay
  norm_num

/-- The classifier returns `pure` on the witness: the first guard fires. -/
theorem kashaZone_witness :
    kashaZone (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => 1) (-1) 0 = KashaZone.pure := by
  unfold kashaZone
  rw [upperYield_witness]
  norm_num

/-- The tolerance predicate fails on the witness at `tol = -1`, although the leak vanishes. -/
theorem not_kashaWithin_witness :
    ¬ KashaWithin (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => 1) (-1) 0 := by
  unfold KashaWithin
  rw [upperYield_witness, fluoYield_witness]
  norm_num

/-- **The row as handed over is false.** The negation of `kashaZone_eq_violating_iff` at the
witness `rad ≡ 1`, `ic ≡ 1`, `N = 0`, `tol = -1`, together with the proof that this witness
satisfies its hypothesis `RateData rad ic 0`. -/
theorem kashaZone_eq_violating_iff_counterexample :
    RateData (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => 1) 0 ∧
      ¬ (kashaZone (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => 1) (-1) 0 = KashaZone.violating ↔
          ¬ KashaWithin (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => 1) (-1) 0) := by
  refine ⟨rateData_witness, fun h => ?_⟩
  have hviol : kashaZone (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => 1) (-1) 0 = KashaZone.violating :=
    h.mpr not_kashaWithin_witness
  rw [kashaZone_witness] at hviol
  exact absurd hviol (by intro hh; cases hh)

end Kasha

end PhotoLean
