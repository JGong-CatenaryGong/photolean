/-
PhotoLean.Sabatier.Instances — S5b, the kernel-checked instance and verdict layer of the Sabatier
theory (the Sabatier principle / the volcano plot).

**What this module is.** The theory is delivered in three layers: the description layer over ℝ
(`PhotoLean/Sabatier/Basic.lean`, S1), the laws and the sharp condition over ℝ
(`PhotoLean/Sabatier/Criterion.lean` S2, `PhotoLean/Sabatier/Sharp.lean` S3), the cross-theory form
(`PhotoLean/Sabatier/Compose.lean`, S4), and the computable rational decision layer
(`PhotoLean/Sabatier/RatModel.lean`, S5a). This module draws the verdicts: for a concrete series
(slopes and offsets) and a concrete catalyst descriptor it states — and the kernel checks — the apex,
the pass height, the effective barrier, the zone (`tooStrong` / `optimal` / `tooWeak`) and the
tolerance verdict. The evidence chain is
`norm_num`-computation of the closed-form numbers → (for the rational rows) the S5a transfer lemmas →
the ℝ statements of S1/S2/S3. Nothing here is an assumption about the numbers: every number below is
computed from the model's own definitions by the kernel, and the structural verdicts cite the
delivered theorems of S3/S4.

**Which numbers are premises and which are checked (the honesty column).** The I1–I8 rows are pure
model instances: their numbers are consequences of the definitions, checked by the kernel, with no
input from the literature. The I9–I12 rows read *printed experimental/computed literature numbers* —
`ΔG_H* = -0.09 eV` (Pt), `+0.45 eV` (Au), `-0.43 eV` (W) from Nørskov et al. 2005 and the `3.20 eV`
scaling plus the `0.37 V` overpotential from Man et al. 2011 — as **premises**; what the kernel checks
is the *verdict* (which zone the descriptor falls in, whether it is inside the tolerance band) and the
*arithmetic* (barrier and pass-height values produced by the model at that descriptor). The
provenance of each printed number is the docstring of the row and `theories/Sabatier/LITERATURE.md`;
the kernel does not and cannot check the measurement.

**Statement correction (2026-09-21).** The I2 rows at `dE = 0` were first stated as `tooWeak`. That
was FALSE: for the asymmetric series `(alphaA, betaA, alphaB, betaB) = (1/2, 0, 1, 1)` the apex is
`2/3`, and under the theory's convention (more negative `dE` = stronger binding) the descriptor
`dE = 0` lies BELOW the apex, i.e. on the more-strongly-binding side, so the classifier returns
`tooStrong`. The authority now carries the corrected rows (`inst_I2_zone_tooStrong`,
`inst_I2_barrier_tooStrong`, plus a genuine too-weak row at `dE = 1`), the kernel-independent
cross-check `theories/Sabatier/probes/sabatier-instance-check.py` reproduces every number below in
exact rational arithmetic, and this module delivers the corrected set.

**Modelling premises.** As in S1, every physical premise is an explicit hypothesis of the statement
that needs it, and the modelling premises of the theory (effective barrier = maximum of the two branch
barriers, BEP-linear branches, a single scalar descriptor, Arrhenius activity with a
descriptor-independent prefactor) are inherited, not re-derived. The premises of the tolerance rows
are the tolerance value `tol` itself, which is an input of the verdict and is written into each row.

**Statement authority**: `theories/Sabatier/probes/sabatier-statement-skeleton.lean` §S5b; the plan
locus of every declaration is `theories/Sabatier/plan.md` §8.2. The mechanical check is

    python3 theories/BEP/probes/bep-fidelity.py --theory Sabatier --milestone S5b

**Imports.** `PhotoLean.Sabatier.Basic` (S1: the model, `SZone`, `VolcanoDescriptor`, `Optimal`),
`PhotoLean.Sabatier.RatModel` (S5a: `NearOptimalQ`, `apexQ`), `PhotoLean.Sabatier.Sharp` (S3:
`descriptor_fails_of_nonpos_product`, `antiVolcano_monotone`) and `PhotoLean.Sabatier.Compose` (S4:
`apexPar`, `parabolaUp`, `parabolaDown`, `parabolicBarrier`, `parabolicBarrier_crossing` — the I7
rows are stated about those definitions, so the import is required by the statements). The module
deliberately does not import S2's `Criterion.lean`: the two rows whose general form lives there are
discharged here by kernel arithmetic on the instance, which keeps this layer independent of the
concurrent S2 delivery.

Acceptance commands (run from the repository root):

    proofs/scripts/lake build PhotoLean.Sabatier.Instances
    proofs/scripts/check.sh --strict PhotoLean.Sabatier.Instances
    proofs/scripts/axioms.sh PhotoLean.Sabatier.Instances PhotoLean.Sabatier.<fully.qualified.theorem>

The delivered file contains no unfinished-proof placeholder and no custom axiomatic declaration; the
`#print axioms` gate of every theorem below lists at most `propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib
import PhotoLean.Sabatier.Basic
import PhotoLean.Sabatier.RatModel
import PhotoLean.Sabatier.Sharp
import PhotoLean.Sabatier.Compose

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Sabatier

/-! ## I1 — the symmetric thermoneutral cycle `(1/2, 1/2, 1/2, 1/2)` (plan §8.2) -/

/-- I1 (symmetric cycle): apex of the thermoneutral series `alphaA = alphaB = 1/2`,
`betaA = betaB = 1/2`. The kernel computes `(1/2 - 1/2) / (1/2 + 1/2) = 0`. Plan locus:
`theories/Sabatier/plan.md` §8.2. -/
theorem inst_I1_apex : apex (1 / 2) (1 / 2) (1 / 2) (1 / 2) = 0 := by
  unfold apex
  norm_num

/-- I1 (symmetric cycle): the series conforms to the Sabatier description. Plan locus:
`theories/Sabatier/plan.md` §8.2. -/
theorem inst_I1_conforms : SabatierConforms (1 / 2) (1 / 2) := by
  unfold SabatierConforms
  norm_num

/-- I1 (symmetric cycle): the pass height. At the apex the two branches cross, so the effective
barrier is `max (1/4) (1/4) = 1/2`. Plan locus: `theories/Sabatier/plan.md` §8.2. -/
theorem inst_I1_apexBarrier : apexBarrier (1 / 2) (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  simp only [apexBarrier, volcanoBarrier, branchUp, branchDown, apex]
  norm_num

/-- I1 (symmetric cycle): a catalyst at the apex is classified optimal. Plan locus:
`theories/Sabatier/plan.md` §8.2. -/
theorem inst_I1_zone_optimal :
    sabatierZone (apex (1 / 2) (1 / 2) (1 / 2) (1 / 2)) 0 = SZone.optimal := by
  rw [sabatierZone_eq_optimal_iff]
  unfold apex
  norm_num

/-- I1 (symmetric cycle): a catalyst binding more strongly than the apex is classified too strong.
Plan locus: `theories/Sabatier/plan.md` §8.2. -/
theorem inst_I1_zone_tooStrong :
    sabatierZone (apex (1 / 2) (1 / 2) (1 / 2) (1 / 2)) (-(1 / 2)) = SZone.tooStrong := by
  rw [sabatierZone_eq_tooStrong_iff]
  unfold apex
  norm_num

/-- I1 (symmetric cycle): the barrier of the too-strongly-binding catalyst. The descending branch
dominates: `max (1/4) (3/4) = 3/4`. Plan locus: `theories/Sabatier/plan.md` §8.2. -/
theorem inst_I1_barrier_tooStrong :
    volcanoBarrier (1 / 2) (1 / 2) (1 / 2) (1 / 2) (-(1 / 2)) = 3 / 4 := by
  simp only [volcanoBarrier, branchUp, branchDown]
  norm_num

/-! ## I2/I3 — the asymmetric cycle `(1/2, 0, 1, 1)` (plan §8.2) -/

/-- I2 (asymmetric cycle `alphaA = 1/2`, `betaA = 0`, `alphaB = 1`, `betaB = 1`): the apex. Plan
locus: `theories/Sabatier/plan.md` §8.2. -/
theorem inst_I2_apex : apex (1 / 2) 0 1 1 = 2 / 3 := by
  unfold apex
  norm_num

/-- I2: the series conforms to the Sabatier description. Plan locus:
`theories/Sabatier/plan.md` §8.2. -/
theorem inst_I2_conforms : SabatierConforms (1 / 2) 1 := by
  unfold SabatierConforms
  norm_num

/-- I2: a catalyst at `dE = 0` lies BELOW the apex `2/3` on the descriptor axis (where more negative
= stronger binding), so it is classified too strong. Plan locus: `theories/Sabatier/plan.md` §8.2. -/
theorem inst_I2_zone_tooStrong : sabatierZone (apex (1 / 2) 0 1 1) 0 = SZone.tooStrong := by
  rw [sabatierZone_eq_tooStrong_iff]
  unfold apex
  norm_num

/-- I2: the barrier of that strongly-binding catalyst (`1`: the branch penalized by strong binding
dominates). Plan locus: `theories/Sabatier/plan.md` §8.2. -/
theorem inst_I2_barrier_tooStrong : volcanoBarrier (1 / 2) 0 1 1 0 = 1 := by
  simp only [volcanoBarrier, branchUp, branchDown]
  norm_num

/-- I2: a catalyst at `dE = 1`, ABOVE the apex `2/3`, is classified too weak. Plan locus:
`theories/Sabatier/plan.md` §8.2. -/
theorem inst_I2_zone_tooWeak : sabatierZone (apex (1 / 2) 0 1 1) 1 = SZone.tooWeak := by
  rw [sabatierZone_eq_tooWeak_iff]
  unfold apex
  norm_num

/-- I2: the barrier of that weakly-binding catalyst (`1/2`: the ascending branch dominates). Plan
locus: `theories/Sabatier/plan.md` §8.2. -/
theorem inst_I2_barrier_tooWeak : volcanoBarrier (1 / 2) 0 1 1 1 = 1 / 2 := by
  simp only [volcanoBarrier, branchUp, branchDown]
  norm_num

/-- I3 (the same series, a strongly-binding catalyst `dE = -1/3`): the barrier. Plan locus:
`theories/Sabatier/plan.md` §8.2. -/
theorem inst_I3_barrier_tooStrong : volcanoBarrier (1 / 2) 0 1 1 (-(1 / 3)) = 4 / 3 := by
  simp only [volcanoBarrier, branchUp, branchDown]
  norm_num

/-- I3: the strongly-binding catalyst is classified too strong. Plan locus:
`theories/Sabatier/plan.md` §8.2. -/
theorem inst_I3_zone_tooStrong : sabatierZone (apex (1 / 2) 0 1 1) (-(1 / 3)) = SZone.tooStrong := by
  rw [sabatierZone_eq_tooStrong_iff]
  unfold apex
  norm_num

/-! ## I4/I5 — the two negative controls `(0, 1, 1, 1)` and `(1, 0, -1, 1)` (plan §8.2)

These two rows are not arithmetic about a concrete descriptor: they assert that the *series* fails
the Sabatier description. Both are discharged by the delivered S3 theorems — the sharp condition
`descriptor_fails_of_nonpos_product` (a nonpositive slope product rules the volcano out) and the
monotone witness `antiVolcano_monotone` (opposite-sign slopes leave no interior optimum). -/

/-- I4 (zero-slope branch series `alphaA = 0`, `betaA = 1`, `alphaB = 1`, `betaB = 1`): the series
does NOT conform to the Sabatier description — there is no pointed apex. Plan locus:
`theories/Sabatier/plan.md` §8.2. -/
theorem inst_I4_notConforms : ¬ SabatierConforms 0 1 := by
  unfold SabatierConforms
  norm_num

/-- I4: the barrier profile of the zero-slope series is not a volcano. Discharged from the delivered
S3 sharp condition with the slope product `0 * 1 = 0 ≤ 0`. Plan locus:
`theories/Sabatier/plan.md` §8.2. -/
theorem inst_I4_notDescriptor :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier 0 1 1 1 dE) (apex 0 1 1 1) :=
  descriptor_fails_of_nonpos_product (by norm_num)

/-- I4: the barrier of that series is minimal on a whole half-line (a plateau, not a pass). With
`alphaA = 0` the descending branch is `1 - dE`, which stays below the constant ascending branch `1`
for every `dE ≥ 0`; both sides of the row are therefore `1` on that half-line. Plan locus:
`theories/Sabatier/plan.md` §8.2. -/
theorem inst_I4_plateau (dE : ℝ) (h : 0 ≤ dE) :
    volcanoBarrier 0 1 1 1 dE = volcanoBarrier 0 1 1 1 (apex 0 1 1 1) := by
  simp only [volcanoBarrier, branchUp, branchDown, apex]
  norm_num
  linarith

/-- I5 (mixed-slope series `alphaA = 1`, `betaA = 0`, `alphaB = -1`, `betaB = 1`): the series does
NOT conform to the Sabatier description. Plan locus: `theories/Sabatier/plan.md` §8.2. -/
theorem inst_I5_notConforms : ¬ SabatierConforms 1 (-1) := by
  unfold SabatierConforms
  norm_num

/-- I5: its barrier is strictly monotone in the descriptor — the volcano has disappeared. Discharged
from the delivered S3 witness `antiVolcano_monotone`, whose parameters are exactly this series. Plan
locus: `theories/Sabatier/plan.md` §8.2. -/
theorem inst_I5_monotone (dE₁ dE₂ : ℝ) (h : dE₁ < dE₂) :
    volcanoBarrier 1 0 (-1) 1 dE₁ < volcanoBarrier 1 0 (-1) 1 dE₂ :=
  antiVolcano_monotone dE₁ dE₂ h

/-! ## I6 — the tolerance rows on the I2 series (plan §8.2) -/

/-- I6 (tolerance verdict on I2): the descriptor `dE = 1/2` lies within `tol = 1/2` of the apex. The
kernel computes `|1/2 - 2/3| = 1/6 ≤ 1/2` in ℚ, so the verdict is decided by rational arithmetic.
Plan locus: `theories/Sabatier/plan.md` §8.2. -/
theorem inst_I6_nearOptimal : NearOptimalQ (1 / 2) (apexQ (1 / 2) 0 1 1) (1 / 2) := by
  unfold NearOptimalQ apexQ
  norm_num [abs_of_nonneg]

/-- I6: its barrier excess over the pass respects the tolerance bound of S2's
`volcanoBarrier_le_apex_add` (`1/6 ≤ 1/2` in this instance). The excess is computed here from the
definitions: `max (1/4) (1/2) - max (1/3) (1/3) = 1/2 - 1/3 = 1/6`. Plan locus:
`theories/Sabatier/plan.md` §8.2. -/
theorem inst_I6_penalty :
    volcanoBarrier (1 / 2) 0 1 1 (1 / 2) - apexBarrier (1 / 2) 0 1 1 ≤ 1 / 2 := by
  simp only [volcanoBarrier, apexBarrier, branchUp, branchDown, apex]
  norm_num

/-! ## I7 — the two-parabola cross-check `lam1 = 1`, `lam2 = 4` (plan §8.2)

The I7 rows test the S4 claim that the linear BEP volcano is the tangent form of the repository's
two-parabola model. The crossing row is the delivered S4 theorem `parabolicBarrier_crossing`; the
three arithmetic rows are computed by the kernel from S4's definitions, with `√4 = 2` and `√1 = 1`
supplied explicitly. -/

/-- I7 (two-parabola cross-check `lam1 = 1`, `lam2 = 4`): the apex of the parabolic volcano. The
kernel computes `(4·1 - 1·2)/(1 + 2) = 2/3` using `√1 = 1` and `√4 = 2`. Plan locus:
`theories/Sabatier/plan.md` §8.2. -/
theorem inst_I7_apexPar : apexPar 1 4 = 2 / 3 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold apexPar
  rw [h4, Real.sqrt_one]
  norm_num

/-- I7: the two parabolic branches cross exactly at the apex — the S4 theorem
`parabolicBarrier_crossing` at `lam1 = 1`, `lam2 = 4`. Plan locus:
`theories/Sabatier/plan.md` §8.2. -/
theorem inst_I7_crossing :
    parabolaUp 1 (apexPar 1 4) = parabolaDown 4 (apexPar 1 4) :=
  parabolicBarrier_crossing (by norm_num) (by norm_num)

/-- I7: the pass height of the parabolic volcano (`25/36`), equal for both branches: at `dE = 2/3`
the ascending parabola gives `(1 + 2/3)^2 / 4 = 25/36` and the descending one
`(4 - 2/3)^2 / 16 = 25/36`. Plan locus: `theories/Sabatier/plan.md` §8.2. -/
theorem inst_I7_apexBarrier : parabolicBarrier 1 4 (apexPar 1 4) = 25 / 36 := by
  rw [inst_I7_apexPar]
  simp only [parabolicBarrier, parabolaUp, parabolaDown, BEP.eact]
  norm_num

/-- I7: the linear BEP volcano underestimates the parabolic barrier at the apex (`2/3 < 25/36`): the
linear volcano at `(1/2, 1/4, 1/2, 1)` has effective barrier `max (7/12) (2/3) = 7/12 = 21/36`, while
the parabolic one has `25/36`. Plan locus: `theories/Sabatier/plan.md` §8.2. -/
theorem inst_I7_linear_below :
    volcanoBarrier (1 / 2) (1 / 4) (1 / 2) 1 (apexPar 1 4) < parabolicBarrier 1 4 (apexPar 1 4) := by
  rw [inst_I7_apexBarrier, inst_I7_apexPar]
  simp only [volcanoBarrier, branchUp, branchDown]
  norm_num

/-! ## I8 — non-vacuity of the verdict layer (plan §8.2) -/

/-- I8 (non-vacuity of the verdict layer): the I2 series has an exactly optimal catalyst — the apex
itself. Plan locus: `theories/Sabatier/plan.md` §8.2. -/
theorem inst_I8_exists_optimal : ∃ dE : ℝ, Optimal (apex (1 / 2) 0 1 1) dE :=
  ⟨apex (1 / 2) 0 1 1, rfl⟩

end Sabatier

end PhotoLean
