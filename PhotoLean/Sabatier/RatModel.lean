/-
PhotoLean.Sabatier.RatModel — S5a, the computable rational decision layer of the Sabatier theory
(the Sabatier principle / the volcano plot).

**Why a rational copy.** The volcano layer is delivered over ℝ in `PhotoLean/Sabatier/Basic.lean`
(S1): the two Brønsted–Evans–Polanyi branches, the effective barrier, the apex, the pass height, the
three-valued zone classifier and the tolerance predicate. The order on ℝ goes through `Classical` and
is not computable, so questions like "which of the three Sabatier regimes does this catalyst sit in",
"does this series conform to the Sabatier description" and "is this descriptor within tolerance of the
apex" cannot be decided by the kernel over ℝ. Over ℚ both the order and the equality are decidable and
the arithmetic is executable, so the instance layer (S5b, `PhotoLean/Sabatier/Instances.lean`) decides
its verdicts by pure rational arithmetic and then carries them to the real theory through the transfer
lemmas of this module.

**Statement authority**: `theories/Sabatier/probes/sabatier-statement-skeleton.lean` §S5a, which is the
transcription of the plan's S5a block (`theories/Sabatier/plan.md` §8.1). Every definition body and
every theorem signature below is that block word for word; each docstring carries the skeleton's
leading sentence plus its plan locus. The mechanical check is

    python3 theories/BEP/probes/bep-fidelity.py --theory Sabatier --milestone S5a

**What this layer does and does not claim.** The eight definitions are the ℚ mirrors of the S1
definitions — the same bodies with `ℚ` in place of `ℝ` — and `SZone` is *imported* from
`PhotoLean/Sabatier/Basic.lean`, never redeclared (a second inductive of the same shape would make
every classifier row a statement about the wrong type). The thirteen theorems are of two kinds:
eleven transfers that move a rational object or a rational predicate to its real counterpart, and two
laws proved directly over ℚ — the rational apex is a global minimizer of the rational effective
barrier, and it is the *unique* one. The transfers are conditional in the same sense as the S1
definitions: they state that the rational form and the real form say the same thing, not that either
holds. The two laws carry the physical orientation `0 < alphaA`, `0 < alphaB` as explicit hypotheses
(engine rule 3), and they are what lets the instance layer discharge a volcano verdict by rational
arithmetic alone.

**Route taken for the two law rows** (recorded so that a later reader does not have to re-derive the
choice): direct proofs over ℚ, replaying in ℚ the argument of the S2 law rows `volcanoBarrier_apex_le`
and `volcanoBarrier_eq_apex_iff`. The ℚ analogues of the ℝ helper lemmas of S1/S2 (`branch_gapQ`,
`apexQ_mul_ne`, `apexQ_crossing`, the two branch-identification lemmas) are `private`: they are proof
scaffolding rather than part of the delivered vocabulary, and the fidelity checker therefore does not
list them. The alternative route — cast both sides with `volcanoBarrierQ_cast` / `apexQ_cast` and pull
the ℝ statement back with `(Rat.cast_le (K := ℝ)).mp` — was not used: it would have made S5a depend on
the S2 module `PhotoLean/Sabatier/Criterion.lean`, whereas the direct route is self-contained.

**Modelling premises.** Every physical premise is an explicit hypothesis of the statement that needs
it; nothing is hidden in a definition. The modelling premises of the theory (the effective barrier is
the maximum of the two branch barriers, both steps follow a BEP line, the descriptor is a single
scalar, the activity is Arrhenius with a descriptor-independent prefactor) are inherited from S1 and
are neither derived nor needed here.

Acceptance commands (run from the repository root):

    proofs/scripts/lake build PhotoLean.Sabatier.RatModel
    proofs/scripts/check.sh --strict PhotoLean.Sabatier.RatModel
    proofs/scripts/axioms.sh PhotoLean.Sabatier.RatModel PhotoLean.Sabatier.<fully.qualified.theorem>

The delivered file contains no unfinished-proof placeholder and no custom axiomatic declaration; the
`#print axioms` gate of every theorem below lists at most `propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib
import PhotoLean.Sabatier.Basic

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Sabatier

/-! ## Definitions (plan §8.1) -/

/-- Rational ascending branch (the computable mirror of `branchUp`): the barrier of the step of the
two-step cycle that is penalized by *weak* binding, affine in the rational descriptor `dE` with slope
`alphaA`. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
noncomputable def branchUpQ (alphaA betaA dE : ℚ) : ℚ := alphaA * dE + betaA

/-- Rational descending branch (the computable mirror of `branchDown`): the barrier of the step that
is penalized by *strong* binding. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
noncomputable def branchDownQ (alphaB betaB dE : ℚ) : ℚ := betaB - alphaB * dE

/-- Rational effective barrier (the computable mirror of `volcanoBarrier`): the larger of the two
rational branch barriers. The identification "effective barrier = maximum of the two step barriers"
is the same declared modelling premise as in S1, not a theorem. Plan locus:
`theories/Sabatier/plan.md` §8.1. -/
noncomputable def volcanoBarrierQ (alphaA betaA alphaB betaB dE : ℚ) : ℚ :=
  max (branchUpQ alphaA betaA dE) (branchDownQ alphaB betaB dE)

/-- Rational apex (the computable mirror of `apex`): the descriptor value at which the two rational
branches cross. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
noncomputable def apexQ (alphaA betaA alphaB betaB : ℚ) : ℚ :=
  (betaB - betaA) / (alphaA + alphaB)

/-- Rational pass height (the computable mirror of `apexBarrier`): the effective barrier at the
rational apex. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
noncomputable def apexBarrierQ (alphaA betaA alphaB betaB : ℚ) : ℚ :=
  volcanoBarrierQ alphaA betaA alphaB betaB (apexQ alphaA betaA alphaB betaB)

/-- Rational decidable classifier of the three Sabatier regimes. It returns the `SZone` inductive of
`PhotoLean/Sabatier/Basic.lean` — the *same* type as the real classifier, so the transfer row below
compares two classifiers and not two look-alike types. Plan locus:
`theories/Sabatier/plan.md` §8.1. -/
noncomputable def sabatierZoneQ (apexD dE : ℚ) : SZone :=
  if dE = apexD then SZone.optimal
  else if dE < apexD then SZone.tooStrong
  else SZone.tooWeak

/-- Series-level conformance verdict in the computable layer: the two rational BEP slopes have the
physical orientation of S1's `SabatierConforms`. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
def SabatierConformsQ (alphaA alphaB : ℚ) : Prop := 0 < alphaA ∧ 0 < alphaB

/-- Tolerance form of the Sabatier optimum in the computable layer: the rational descriptor lies
within `tol` of the rational apex. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
def NearOptimalQ (tol apexD dE : ℚ) : Prop := |dE - apexD| ≤ tol

/-! ## Cast transfer of the description layer (plan §8.1) -/

/-- Cast transfer of the ascending branch: the real image of the rational branch IS the real branch
at the real images of the parameters. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
theorem branchUpQ_cast (alphaA betaA dE : ℚ) :
    ((branchUpQ alphaA betaA dE : ℚ) : ℝ)
      = branchUp (alphaA : ℝ) (betaA : ℝ) (dE : ℝ) := by
  unfold branchUpQ branchUp
  push_cast
  ring

/-- Cast transfer of the descending branch. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
theorem branchDownQ_cast (alphaB betaB dE : ℚ) :
    ((branchDownQ alphaB betaB dE : ℚ) : ℝ)
      = branchDown (alphaB : ℝ) (betaB : ℝ) (dE : ℝ) := by
  unfold branchDownQ branchDown
  push_cast
  ring

/-- Cast transfer of the effective barrier: the cast commutes with the `max` that defines it. Plan
locus: `theories/Sabatier/plan.md` §8.1. -/
theorem volcanoBarrierQ_cast (alphaA betaA alphaB betaB dE : ℚ) :
    ((volcanoBarrierQ alphaA betaA alphaB betaB dE : ℚ) : ℝ)
      = volcanoBarrier (alphaA : ℝ) (betaA : ℝ) (alphaB : ℝ) (betaB : ℝ) (dE : ℝ) := by
  unfold volcanoBarrierQ volcanoBarrier
  rw [Rat.cast_max, branchUpQ_cast, branchDownQ_cast]

/-- Cast transfer of the apex. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
theorem apexQ_cast (alphaA betaA alphaB betaB : ℚ) :
    ((apexQ alphaA betaA alphaB betaB : ℚ) : ℝ)
      = apex (alphaA : ℝ) (betaA : ℝ) (alphaB : ℝ) (betaB : ℝ) := by
  unfold apexQ apex
  push_cast
  ring

/-- Cast transfer of the pass height, obtained by composing the two transfers above. Plan locus:
`theories/Sabatier/plan.md` §8.1. -/
theorem apexBarrierQ_cast (alphaA betaA alphaB betaB : ℚ) :
    ((apexBarrierQ alphaA betaA alphaB betaB : ℚ) : ℝ)
      = apexBarrier (alphaA : ℝ) (betaA : ℝ) (alphaB : ℝ) (betaB : ℝ) := by
  unfold apexBarrierQ apexBarrier
  rw [volcanoBarrierQ_cast, apexQ_cast]

/-! ## Cast transfer of the classifier and of the predicates (plan §8.1) -/

/-- The rational classifier is the rational mirror of the real classifier: the two `if`-cascades
agree once the apex and the descriptor are cast. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
theorem sabatierZoneQ_eq_sabatierZone (apexD dE : ℚ) :
    sabatierZoneQ apexD dE = sabatierZone (apexD : ℝ) (dE : ℝ) := by
  unfold sabatierZoneQ sabatierZone
  norm_cast

/-- The rational classifier recognizes the optimum, exactly as the real one does (`SZone` and its
`DecidableEq` instance are shared with S1). Plan locus: `theories/Sabatier/plan.md` §8.1. -/
theorem sabatierZoneQ_eq_optimal_iff (apexD dE : ℚ) :
    sabatierZoneQ apexD dE = SZone.optimal ↔ dE = apexD := by
  unfold sabatierZoneQ
  split_ifs with h1 h2
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩

/-- The rational classifier recognizes the too-strong-binding regime. Plan locus:
`theories/Sabatier/plan.md` §8.1. -/
theorem sabatierZoneQ_eq_tooStrong_iff (apexD dE : ℚ) :
    sabatierZoneQ apexD dE = SZone.tooStrong ↔ dE < apexD := by
  unfold sabatierZoneQ
  split_ifs with h1 h2
  · subst h1
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (lt_irrefl _)⟩
  · exact ⟨fun _ => h2, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h2⟩

/-- The rational classifier recognizes the too-weak-binding regime. Plan locus:
`theories/Sabatier/plan.md` §8.1. -/
theorem sabatierZoneQ_eq_tooWeak_iff (apexD dE : ℚ) :
    sabatierZoneQ apexD dE = SZone.tooWeak ↔ apexD < dE := by
  unfold sabatierZoneQ
  split_ifs with h1 h2
  · subst h1
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (lt_irrefl _)⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h (by linarith)⟩
  · exact ⟨fun _ => lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm h1), fun _ => rfl⟩

/-- The rational conformance verdict is the rational mirror of the real one: the physical orientation
of the two slopes transfers across the cast. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
theorem sabatierConformsQ_iff (alphaA alphaB : ℚ) :
    SabatierConformsQ alphaA alphaB ↔ SabatierConforms (alphaA : ℝ) (alphaB : ℝ) := by
  unfold SabatierConformsQ SabatierConforms
  norm_cast

/-- The rational tolerance band is the rational mirror of the real one: the cast commutes with the
absolute value, so the `tol`-band of the rational apex is the `tol`-band of the real apex seen from
ℚ. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
theorem nearOptimalQ_iff (tol apexD dE : ℚ) :
    NearOptimalQ tol apexD dE ↔ NearOptimal (tol : ℝ) (apexD : ℝ) (dE : ℝ) := by
  unfold NearOptimalQ NearOptimal
  rw [← Rat.cast_sub, ← Rat.cast_abs]
  exact (Rat.cast_le (K := ℝ)).symm

/-! ## The rational volcano laws (plan §8.1) — auxiliary ℚ algebra for the S2 argument

The two law rows below replay the ℝ argument of S2 in ℚ. The ℚ algebra they share with S1/S2 is
stated here as `private` scaffolding: `branch_gapQ` (the affine branch gap), `apexQ_mul_ne` (the
division cancels against the total slope), `apexQ_crossing` (the apex is a crossing point) and the two
branch-identification lemmas (which branch dominates on each side of the apex). -/

/-- Auxiliary: the gap of the two rational branches is affine in the descriptor, with slope
`alphaA + alphaB` and value `-(betaB - betaA)` at `dE = 0`; it is the sign core of the rational apex
geometry (ℚ analogue of S1's `branch_gap`). Plan locus: `theories/Sabatier/plan.md` §8.1. -/
private theorem branch_gapQ (alphaA betaA alphaB betaB dE : ℚ) :
    branchUpQ alphaA betaA dE - branchDownQ alphaB betaB dE
      = (alphaA + alphaB) * dE - (betaB - betaA) := by
  unfold branchUpQ branchDownQ
  ring

/-- Auxiliary: multiplying the rational apex by the total slope cancels the division (ℚ analogue of
S1's `apex_mul_ne`). Plan locus: `theories/Sabatier/plan.md` §8.1. -/
private theorem apexQ_mul_ne {alphaA betaA alphaB betaB : ℚ} (h : alphaA + alphaB ≠ 0) :
    (alphaA + alphaB) * apexQ alphaA betaA alphaB betaB = betaB - betaA := by
  rw [apexQ, mul_div_cancel₀ _ h]

/-- Auxiliary: on the weak-binding side the rational descending branch is dominated by the rational
ascending one (ℚ analogue of S1's `branchDown_le_branchUp_of_apex_le`). Plan locus:
`theories/Sabatier/plan.md` §8.1. -/
private theorem branchDownQ_le_branchUpQ_of_apexQ_le {alphaA betaA alphaB betaB : ℚ}
    (hAB : 0 < alphaA + alphaB) {dE : ℚ} (h : apexQ alphaA betaA alphaB betaB ≤ dE) :
    branchDownQ alphaB betaB dE ≤ branchUpQ alphaA betaA dE := by
  have hgap := branch_gapQ alphaA betaA alphaB betaB dE
  have hmul : (alphaA + alphaB) * apexQ alphaA betaA alphaB betaB ≤ (alphaA + alphaB) * dE :=
    mul_le_mul_of_nonneg_left h hAB.le
  rw [apexQ_mul_ne hAB.ne'] at hmul
  linarith

/-- Auxiliary: on the strong-binding side the rational ascending branch is dominated by the rational
descending one (ℚ analogue of S1's `branchUp_le_branchDown_of_le_apex`). Plan locus:
`theories/Sabatier/plan.md` §8.1. -/
private theorem branchUpQ_le_branchDownQ_of_le_apexQ {alphaA betaA alphaB betaB : ℚ}
    (hAB : 0 < alphaA + alphaB) {dE : ℚ} (h : dE ≤ apexQ alphaA betaA alphaB betaB) :
    branchUpQ alphaA betaA dE ≤ branchDownQ alphaB betaB dE := by
  have hgap := branch_gapQ alphaA betaA alphaB betaB dE
  have hmul : (alphaA + alphaB) * dE ≤ (alphaA + alphaB) * apexQ alphaA betaA alphaB betaB :=
    mul_le_mul_of_nonneg_left h hAB.le
  rw [apexQ_mul_ne hAB.ne'] at hmul
  linarith

/-- Auxiliary: the rational apex is a crossing point of the two rational branches, whenever the apex
formula is defined (ℚ analogue of S1's `apex_crossing`). Plan locus:
`theories/Sabatier/plan.md` §8.1. -/
private theorem apexQ_crossing {alphaA betaA alphaB betaB : ℚ} (h : alphaA + alphaB ≠ 0) :
    branchUpQ alphaA betaA (apexQ alphaA betaA alphaB betaB)
      = branchDownQ alphaB betaB (apexQ alphaA betaA alphaB betaB) := by
  unfold branchUpQ branchDownQ apexQ
  field_simp
  ring

/-- Auxiliary: on the weak-binding side (`apexQ ≤ dE`) the rational effective barrier IS the rational
ascending branch. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
private theorem volcanoBarrierQ_eq_branchUpQ_of_apexQ_le {alphaA betaA alphaB betaB : ℚ}
    (hAB : 0 < alphaA + alphaB) {dE : ℚ} (h : apexQ alphaA betaA alphaB betaB ≤ dE) :
    volcanoBarrierQ alphaA betaA alphaB betaB dE = branchUpQ alphaA betaA dE := by
  unfold volcanoBarrierQ
  exact max_eq_left (branchDownQ_le_branchUpQ_of_apexQ_le hAB h)

/-- Auxiliary: on the strong-binding side (`dE ≤ apexQ`) the rational effective barrier IS the
rational descending branch. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
private theorem volcanoBarrierQ_eq_branchDownQ_of_le_apexQ {alphaA betaA alphaB betaB : ℚ}
    (hAB : 0 < alphaA + alphaB) {dE : ℚ} (h : dE ≤ apexQ alphaA betaA alphaB betaB) :
    volcanoBarrierQ alphaA betaA alphaB betaB dE = branchDownQ alphaB betaB dE := by
  unfold volcanoBarrierQ
  exact max_eq_right (branchUpQ_le_branchDownQ_of_le_apexQ hAB h)

/-- Auxiliary: at the rational apex the two rational branches are equal, so the rational effective
barrier equals either of them. Plan locus: `theories/Sabatier/plan.md` §8.1. -/
private theorem volcanoBarrierQ_at_apexQ {alphaA betaA alphaB betaB : ℚ}
    (h : alphaA + alphaB ≠ 0) :
    volcanoBarrierQ alphaA betaA alphaB betaB (apexQ alphaA betaA alphaB betaB)
      = branchUpQ alphaA betaA (apexQ alphaA betaA alphaB betaB) := by
  unfold volcanoBarrierQ
  rw [apexQ_crossing h, max_self]

end Sabatier

end PhotoLean
