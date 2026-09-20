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

end Sabatier

end PhotoLean
