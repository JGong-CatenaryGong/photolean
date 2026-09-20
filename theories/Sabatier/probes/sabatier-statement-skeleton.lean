/-
Statement skeleton for the Sabatier theory (the Sabatier principle / the volcano plot) — the
**authority for all delivered signatures** of `PhotoLean/Sabatier/*.lean`. Every delivered
declaration must match the corresponding signature here word for word (the mechanical check is
`theories/BEP/probes/bep-fidelity.py --theory Sabatier`, which is theory-generic). It lives under
`theories/Sabatier/probes/`, i.e. OUTSIDE `SOURCE_DIRS` (`PhotoLean`), because the source tree has
zero tolerance for the unfinished-proof placeholder keyword; statement-first requires the signatures
to elaborate before any proof work starts. 0 error is the Sprint-0 gate.

Model (plan §1.2). A two-step catalytic cycle on a single descriptor `dE` — the binding energy of the
key intermediate on the catalyst surface, in the convention "more negative = stronger binding". The
effective (rate-limiting) barrier is taken as the MAXIMUM of two Brønsted–Evans–Polanyi branches:

  branchUp   alphaA betaA dE = alphaA * dE + betaA        (step penalized by weak binding)
  branchDown alphaB betaB dE = betaB - alphaB * dE        (step penalized by strong binding)
  volcanoBarrier .. dE       = max (branchUp .. dE) (branchDown .. dE)     <- the model's premise
  apex   alphaA betaA alphaB betaB = (betaB - betaA) / (alphaA + alphaB)   <- the crossing point
  activity f kB T dE         = exp (-(f dE) / (kB * T))                    <- Arrhenius form

`VolcanoDescriptor f de0` is the family-level Sabatier description: `de0` is the *unique* global
minimizer of the barrier profile `f`; the volcano shape of the barrier is therefore equivalent to a
unique maximum of the activity (the volcano plot of `log (activity)` against `dE`).
`SabatierConforms alphaA alphaB` is the series-level verdict (`0 < alphaA ∧ 0 < alphaB`, the physical
orientation of the two branches); `SZone` / `sabatierZone` classify a catalyst's descriptor against
the apex; `NearOptimal tol apexD dE` is the tolerance form of "not too strong, not too weak".

Every physical premise is an explicit hypothesis — nothing is hidden in a definition (engine rule 3).
The identification "effective barrier = maximum of the two branch barriers" is a DECLARED modelling
premise of the theory (plan §12 honesty table), not a theorem of it; the sharpness conditions of the
volcano shape are the theorems (S3).

Provenance of the rows below: `theories/Sabatier/plan.md` §4 (S1), §5 (S2), §6 (S3), §7 (S4), §8
(S5a); each delivered docstring carries its plan locus. The literature rows of §S5b (I6–I8) are
appended when `theories/Sabatier/LITERATURE.md` round 1 lands the printed numbers (the append is
recorded in `proofs/API-NOTES.md` / plan §3.1).
-/
import Mathlib
import PhotoLean.BEP.Basic

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Sabatier

/-! ## S1 — description layer (`PhotoLean/Sabatier/Basic.lean`) -/

/-- Ascending Brønsted–Evans–Polanyi branch: the barrier of the step of a two-step catalytic cycle
that is penalized by *weak* binding of the key intermediate, affine in the descriptor `dE` with
slope `alphaA`. In the physical orientation `0 < alphaA` the branch grows with `dE`. -/
noncomputable def branchUp (alphaA betaA dE : ℝ) : ℝ := alphaA * dE + betaA

/-- Descending Brønsted–Evans–Polanyi branch: the barrier of the step penalized by *strong* binding.
In the physical orientation `0 < alphaB` the branch grows as `dE` decreases. -/
noncomputable def branchDown (alphaB betaB dE : ℝ) : ℝ := betaB - alphaB * dE

/-- Effective (rate-limiting) barrier of the two-step cycle: the larger of the two branch barriers.
The identification "effective barrier = maximum of the two step barriers" is a **modelling premise**
of this theory (plan §12), not a theorem of it. -/
noncomputable def volcanoBarrier (alphaA betaA alphaB betaB dE : ℝ) : ℝ :=
  max (branchUp alphaA betaA dE) (branchDown alphaB betaB dE)

/-- The volcano apex: the descriptor value at which the two branches cross. A derived quantity of
the model, not a definitional copy of the optimum. -/
noncomputable def apex (alphaA betaA alphaB betaB : ℝ) : ℝ :=
  (betaB - betaA) / (alphaA + alphaB)

/-- The effective barrier at the apex — the height of the volcano's pass. -/
noncomputable def apexBarrier (alphaA betaA alphaB betaB : ℝ) : ℝ :=
  volcanoBarrier alphaA betaA alphaB betaB (apex alphaA betaA alphaB betaB)

/-- The volcano (Sabatier) description of a barrier profile `f` with claimed apex `de0`: `de0` is
the *unique* global minimizer of `f`. Family-level predicate, independent of the height scale. -/
def VolcanoDescriptor (f : ℝ → ℝ) (de0 : ℝ) : Prop :=
  (∀ dE : ℝ, f de0 ≤ f dE) ∧ (∀ dE : ℝ, f dE = f de0 → dE = de0)

/-- The dual (anti-volcano) description: `de0` is the *unique* global maximizer of `f`. It is the
form in which the volcano plot of the ACTIVITY is stated: a volcano in the barrier is a peak in the
activity, so `VolcanoDescriptor f de0` is equivalent to `AntiVolcanoDescriptor (activity f kB T) de0`
(`antiDescriptor_activity_iff`, S2). -/
def AntiVolcanoDescriptor (f : ℝ → ℝ) (de0 : ℝ) : Prop :=
  (∀ dE : ℝ, f dE ≤ f de0) ∧ (∀ dE : ℝ, f dE = f de0 → dE = de0)

/-- Activity (turnover-frequency proxy) of a barrier profile: the Arrhenius / transition-state form
`exp (-Ea / (kB * T))`. The volcano plot is the graph of `log` of this quantity against `dE`. -/
noncomputable def activity (f : ℝ → ℝ) (kB T : ℝ) : ℝ → ℝ :=
  fun dE => Real.exp (-(f dE) / (kB * T))

/-- The physical orientation of the two branches: the ascending branch is the one penalized by weak
binding (`0 < alphaA`) and the descending branch the one penalized by strong binding
(`0 < alphaB`). Series-level verdict of the instance layer: "does this series conform to the
Sabatier description?" -/
def SabatierConforms (alphaA alphaB : ℝ) : Prop := 0 < alphaA ∧ 0 < alphaB

/-- The catalyst binds the key intermediate too strongly: its descriptor lies below the apex. -/
def TooStrong (apexD dE : ℝ) : Prop := dE < apexD

/-- The catalyst sits exactly at the volcano apex — the Sabatier optimum. -/
def Optimal (apexD dE : ℝ) : Prop := dE = apexD

/-- The catalyst binds the key intermediate too weakly: its descriptor lies above the apex. -/
def TooWeak (apexD dE : ℝ) : Prop := apexD < dE

/-- Within-tolerance reading of the Sabatier optimum: the descriptor is within `tol` of the apex.
This is the tolerance form of "not too strong, not too weak" (plan §6). -/
def NearOptimal (tol apexD dE : ℝ) : Prop := |dE - apexD| ≤ tol

/-- Position of a catalyst's descriptor relative to the volcano apex. -/
inductive SZone where
  | tooStrong
  | optimal
  | tooWeak
  deriving DecidableEq, Repr

/-- Decidable classifier of the three Sabatier regimes. -/
noncomputable def sabatierZone (apexD dE : ℝ) : SZone :=
  if dE = apexD then SZone.optimal
  else if dE < apexD then SZone.tooStrong
  else SZone.tooWeak

/-! ### S1 lemmas (plan §4.2, §4.3) -/

/-- The gap between the two branches is affine in the descriptor, with slope `alphaA + alphaB` and
value `-(betaB - betaA)` at `dE = 0`; it is the sign core of the apex geometry. -/
theorem branch_gap (alphaA betaA alphaB betaB dE : ℝ) :
    branchUp alphaA betaA dE - branchDown alphaB betaB dE
      = (alphaA + alphaB) * dE - (betaB - betaA) := by sorry

/-- The apex is a crossing point of the two branches (when the apex formula is defined). -/
theorem apex_crossing {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    branchUp alphaA betaA (apex alphaA betaA alphaB betaB)
      = branchDown alphaB betaB (apex alphaA betaA alphaB betaB) := by sorry

/-- The apex is the *unique* crossing point of the two branches. -/
theorem apex_unique_crossing {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) (dE : ℝ) :
    (branchUp alphaA betaA dE = branchDown alphaB betaB dE)
      ↔ dE = apex alphaA betaA alphaB betaB := by sorry

/-- The apex sits at the thermoneutral descriptor value `dE = 0` exactly for a balanced cycle
(equal branch offsets). -/
theorem apex_eq_zero_iff {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    apex alphaA betaA alphaB betaB = 0 ↔ betaA = betaB := by sorry

/-- Apex under the label swap: passing the two branches through the relabelling identity
(`volcanoBarrier_relabel`) changes the second slope's sign as well, so the apex is NOT invariant
under a naive parameter swap; it is invariant under this relabelling. -/
theorem apex_relabel (alphaA betaA alphaB betaB : ℝ) :
    apex alphaA betaA alphaB betaB = apex (-alphaB) betaB (-alphaA) betaA := by sorry

/-- Relabelling identity of the barrier profile: a model whose ascending/descending slopes are both
negative is the same volcano with the two branches interchanged. -/
theorem volcanoBarrier_relabel (alphaA betaA alphaB betaB dE : ℝ) :
    volcanoBarrier alphaA betaA alphaB betaB dE
      = volcanoBarrier (-alphaB) betaB (-alphaA) betaA dE := by sorry

/-- At the apex the two branches are equal, so the effective barrier equals either of them. -/
theorem volcanoBarrier_at_apex {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    volcanoBarrier alphaA betaA alphaB betaB (apex alphaA betaA alphaB betaB)
      = branchUp alphaA betaA (apex alphaA betaA alphaB betaB) := by sorry

/-- Below the apex the descending branch dominates. -/
theorem branchUp_lt_branchDown_of_lt_apex {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : dE < apex alphaA betaA alphaB betaB) :
    branchUp alphaA betaA dE < branchDown alphaB betaB dE := by sorry

/-- Above the apex the ascending branch dominates. -/
theorem branchDown_lt_branchUp_of_apex_lt {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : apex alphaA betaA alphaB betaB < dE) :
    branchDown alphaB betaB dE < branchUp alphaA betaA dE := by sorry

/-- On the weak-binding side (`apex ≤ dE`) the effective barrier IS the ascending branch. -/
theorem volcanoBarrier_eq_branchUp_of_apex_le {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : apex alphaA betaA alphaB betaB ≤ dE) :
    volcanoBarrier alphaA betaA alphaB betaB dE = branchUp alphaA betaA dE := by sorry

/-- On the strong-binding side (`dE ≤ apex`) the effective barrier IS the descending branch. -/
theorem volcanoBarrier_eq_branchDown_of_le_apex {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : dE ≤ apex alphaA betaA alphaB betaB) :
    volcanoBarrier alphaA betaA alphaB betaB dE = branchDown alphaB betaB dE := by sorry

/-- The classifier recognizes the optimum. -/
theorem sabatierZone_eq_optimal_iff (apexD dE : ℝ) :
    sabatierZone apexD dE = SZone.optimal ↔ dE = apexD := by sorry

/-- The classifier recognizes the too-strong-binding regime. -/
theorem sabatierZone_eq_tooStrong_iff (apexD dE : ℝ) :
    sabatierZone apexD dE = SZone.tooStrong ↔ dE < apexD := by sorry

/-- The classifier recognizes the too-weak-binding regime. -/
theorem sabatierZone_eq_tooWeak_iff (apexD dE : ℝ) :
    sabatierZone apexD dE = SZone.tooWeak ↔ apexD < dE := by sorry

/-- The tolerance form is the closed band around the apex (no hypothesis on the sign of `tol`). -/
theorem nearOptimal_iff_band (apexD dE tol : ℝ) :
    NearOptimal tol apexD dE ↔ apexD - tol ≤ dE ∧ dE ≤ apexD + tol := by sorry

/-! ## S2 — law layer (`PhotoLean/Sabatier/Criterion.lean`) -/

/-- The apex is a global minimizer of the effective barrier (physical orientation). -/
theorem volcanoBarrier_apex_le {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA) (hB : 0 < alphaB)
    (dE : ℝ) :
    volcanoBarrier alphaA betaA alphaB betaB (apex alphaA betaA alphaB betaB)
      ≤ volcanoBarrier alphaA betaA alphaB betaB dE := by sorry

/-- The apex is the *unique* global minimizer: the volcano has a pointed pass, not a plateau. -/
theorem volcanoBarrier_eq_apex_iff {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) (dE : ℝ) :
    volcanoBarrier alphaA betaA alphaB betaB dE
        = volcanoBarrier alphaA betaA alphaB betaB (apex alphaA betaA alphaB betaB)
      ↔ dE = apex alphaA betaA alphaB betaB := by sorry

/-- Weak-binding side: the effective barrier strictly increases with `dE`. -/
theorem volcanoBarrier_strictMono_of_apex_le {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) {dE₁ dE₂ : ℝ} (h₁ : apex alphaA betaA alphaB betaB ≤ dE₁)
    (h₂ : dE₁ < dE₂) :
    volcanoBarrier alphaA betaA alphaB betaB dE₁ < volcanoBarrier alphaA betaA alphaB betaB dE₂ := by
  sorry

/-- Strong-binding side: the effective barrier strictly increases as `dE` decreases. -/
theorem volcanoBarrier_strictAnti_of_le_apex {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) {dE₁ dE₂ : ℝ} (h₂ : dE₂ ≤ apex alphaA betaA alphaB betaB) (h₁ : dE₁ < dE₂) :
    volcanoBarrier alphaA betaA alphaB betaB dE₂ < volcanoBarrier alphaA betaA alphaB betaB dE₁ := by
  sorry

/-- Quantitative tolerance form of "not too strong, not too weak": within `tol` of the apex the
activity loss is at most `max alphaA alphaB * tol` in barrier units. -/
theorem volcanoBarrier_le_apex_add {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) {tol dE : ℝ} (h : NearOptimal tol (apex alphaA betaA alphaB betaB) dE) :
    volcanoBarrier alphaA betaA alphaB betaB dE
      ≤ apexBarrier alphaA betaA alphaB betaB + max alphaA alphaB * tol := by sorry

/-- Apex-centred form of the barrier: the excess over the pass is the maximum of two linear
penalties, one for each end of the descriptor axis. -/
theorem volcanoBarrier_apex_form {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) (dE : ℝ) :
    volcanoBarrier alphaA betaA alphaB betaB dE
      = apexBarrier alphaA betaA alphaB betaB
        + max (alphaA * (dE - apex alphaA betaA alphaB betaB))
            (alphaB * (apex alphaA betaA alphaB betaB - dE)) := by sorry

/-- Observable slope of the weak-binding volcano leg: its finite differences are the BEP slope
`alphaA` — the literature's "the volcano legs have slopes ±α", made exact. -/
theorem volcanoBarrier_secSlope_of_apex_le {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE₁ dE₂ : ℝ} (h₁ : apex alphaA betaA alphaB betaB ≤ dE₁)
    (h₂ : dE₁ < dE₂) :
    (volcanoBarrier alphaA betaA alphaB betaB dE₂ - volcanoBarrier alphaA betaA alphaB betaB dE₁)
        / (dE₂ - dE₁) = alphaA := by sorry

/-- Observable slope of the strong-binding volcano leg: its finite differences are `-alphaB`. -/
theorem volcanoBarrier_secSlope_of_le_apex {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE₁ dE₂ : ℝ} (h₂ : dE₂ ≤ apex alphaA betaA alphaB betaB)
    (h₁ : dE₁ < dE₂) :
    (volcanoBarrier alphaA betaA alphaB betaB dE₂ - volcanoBarrier alphaA betaA alphaB betaB dE₁)
        / (dE₂ - dE₁) = -alphaB := by sorry

/-- Value form of the pass height, used by the instance rows. -/
theorem apexBarrier_eq {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    apexBarrier alphaA betaA alphaB betaB = alphaA * apex alphaA betaA alphaB betaB + betaA := by
  sorry

/-- Main positive statement: in the physical orientation the two-branch barrier profile IS a volcano
with apex `apex` — the Sabatier description holds at the family level. -/
theorem volcano_descriptor_of_physical {alphaA betaA alphaB betaB : ℝ}
    (h : SabatierConforms alphaA alphaB) :
    VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
      (apex alphaA betaA alphaB betaB) := by sorry

/-- The activity of any barrier profile is positive. -/
theorem activity_pos (f : ℝ → ℝ) (kB T dE : ℝ) : 0 < activity f kB T dE := by sorry

/-- If the barrier profile is a volcano, the apex is a global maximizer of the activity. -/
theorem activity_le_apex {f : ℝ → ℝ} {de0 kB T : ℝ} (hkT : 0 < kB * T)
    (h : VolcanoDescriptor f de0) (dE : ℝ) :
    activity f kB T dE ≤ activity f kB T de0 := by sorry

/-- If the barrier profile is a volcano, the activity is maximized at the apex and only there. -/
theorem activity_eq_apex_iff {f : ℝ → ℝ} {de0 kB T : ℝ} (hkT : 0 < kB * T)
    (h : VolcanoDescriptor f de0) (dE : ℝ) :
    activity f kB T dE = activity f kB T de0 ↔ dE = de0 := by sorry

/-- **The volcano plot.** The barrier profile is a volcano (unique minimizer at `de0`) iff the
activity has its unique global maximum at `de0` — the activity is a strictly decreasing function of
the barrier. This is the form the volcano plot is drawn in. -/
theorem antiDescriptor_activity_iff {f : ℝ → ℝ} {de0 kB T : ℝ} (hkT : 0 < kB * T) :
    AntiVolcanoDescriptor (activity f kB T) de0 ↔ VolcanoDescriptor f de0 := by sorry

/-- The activity ratio depends only on the barrier difference — the finite-difference form used by
the instance layer and consistent with the repository's Marcus rate ratio. -/
theorem activity_ratio (f : ℝ → ℝ) {kB T dE₁ dE₂ : ℝ} (hkT : kB * T ≠ 0) :
    activity f kB T dE₂ / activity f kB T dE₁ = Real.exp ((f dE₁ - f dE₂) / (kB * T)) := by sorry

/-- Non-vacuity: an exactly optimal catalyst exists for every claimed apex. -/
theorem exists_optimal (apexD : ℝ) : ∃ dE : ℝ, Optimal apexD dE := by sorry

/-- Non-vacuity: a too-weakly-binding catalyst exists for every claimed apex. -/
theorem exists_tooWeak (apexD : ℝ) : ∃ dE : ℝ, TooWeak apexD dE := by sorry

/-- Non-vacuity: a too-strongly-binding catalyst exists for every claimed apex. -/
theorem exists_tooStrong (apexD : ℝ) : ∃ dE : ℝ, TooStrong apexD dE := by sorry

/-- Non-vacuity: the tolerance band is inhabited whenever the tolerance is nonnegative. -/
theorem exists_nearOptimal {apexD tol : ℝ} (htol : 0 ≤ tol) : ∃ dE : ℝ, NearOptimal tol apexD dE := by
  sorry

/-! ## S3 — sharp conditions (`PhotoLean/Sabatier/Sharp.lean`) -/

/-- **The sharp condition of the Sabatier description.** The two-branch barrier profile is a volcano
at its apex (unique global minimizer) **iff** the two BEP slopes have the same nonzero sign — i.e.
iff the two branches penalize opposite ends of the descriptor axis. -/
theorem volcano_descriptor_iff (alphaA betaA alphaB betaB : ℝ) :
    VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
        (apex alphaA betaA alphaB betaB)
      ↔ 0 < alphaA * alphaB := by sorry

/-- Contrapositive form of the sharp condition. -/
theorem descriptor_fails_of_nonpos_product {alphaA betaA alphaB betaB : ℝ}
    (h : alphaA * alphaB ≤ 0) :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
        (apex alphaA betaA alphaB betaB) := by sorry

/-- The sharp condition in the instance layer's vocabulary: the volcano holds iff the series
conforms to the physical orientation, up to the interchange of the two branch labels. -/
theorem volcano_descriptor_iff_labels {alphaA betaA alphaB betaB : ℝ} :
    VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
        (apex alphaA betaA alphaB betaB)
      ↔ (SabatierConforms alphaA alphaB ∨ SabatierConforms (-alphaB) (-alphaA)) := by sorry

/-- The volcano shape is label-invariant: a series whose two branches are both "descending" is still
a volcano, read with the two branches interchanged. -/
theorem volcano_descriptor_of_neg {alphaA betaA alphaB betaB : ℝ} (hA : alphaA < 0)
    (hB : alphaB < 0) :
    VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
      (apex alphaA betaA alphaB betaB) := by sorry

/-- **The volcano plot** of the two-branch model. The activity has its unique global maximum at
the apex iff the two BEP slopes have the same nonzero sign. -/
theorem volcanoActivity_peak_iff {alphaA betaA alphaB betaB kB T : ℝ} (hkT : 0 < kB * T) :
    AntiVolcanoDescriptor (activity (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE) kB T)
        (apex alphaA betaA alphaB betaB)
      ↔ 0 < alphaA * alphaB := by sorry

/-- Degenerate witness: two slope-zero branches give a constant barrier — no optimum at all. -/
theorem flat_witness (dE : ℝ) :
    volcanoBarrier 0 0 0 0 dE = volcanoBarrier 0 0 0 0 (apex 0 0 0 0) := by sorry

/-- The constant profile is not a volcano (uniqueness of the minimizer fails). -/
theorem not_descriptor_flat :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier 0 0 0 0 dE) (apex 0 0 0 0) := by sorry

/-- Zero-slope witness: one insensitive branch turns the apex into a half-line plateau. -/
theorem plateau_witness (dE : ℝ) (h : 0 ≤ dE) :
    volcanoBarrier 0 0 1 0 dE = volcanoBarrier 0 0 1 0 (apex 0 0 1 0) := by sorry

/-- A plateau is not a volcano: the minimizer is not unique, so there is no pointed apex. -/
theorem not_descriptor_plateau :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier 0 0 1 0 dE) (apex 0 0 1 0) := by sorry

/-- Mixed-sign witness: two branches of opposite slope give a monotone barrier — the activity has no
interior maximum, the volcano has disappeared. -/
theorem antiVolcano_monotone (dE₁ dE₂ : ℝ) (h : dE₁ < dE₂) :
    volcanoBarrier 1 0 (-1) 1 dE₁ < volcanoBarrier 1 0 (-1) 1 dE₂ := by sorry

/-- The mixed-sign model is not a volcano. -/
theorem not_descriptor_mixedSign :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier 1 0 (-1) 1 dE) (apex 1 0 (-1) 1) := by sorry

/-! ## S4 — microscopic / cross-theory form (`PhotoLean/Sabatier/Compose.lean`) -/

/-- Ascending branch of the two-parabola volcano: the repository's two-parabola barrier of the step
whose reaction energy is the descriptor `dE` (`PhotoLean.BEP.eact` at driving force `-dE`). -/
noncomputable def parabolaUp (lam1 dE : ℝ) : ℝ := BEP.eact lam1 (-dE)

/-- Descending branch of the two-parabola volcano: the two-parabola barrier of the reverse step
(`PhotoLean.BEP.eact` at driving force `dE`). -/
noncomputable def parabolaDown (lam2 dE : ℝ) : ℝ := BEP.eact lam2 dE

/-- Effective barrier when both steps are described by the repository's two-parabola model. -/
noncomputable def parabolicBarrier (lam1 lam2 dE : ℝ) : ℝ :=
  max (parabolaUp lam1 dE) (parabolaDown lam2 dE)

/-- Apex of the two-parabola volcano: the descriptor value where the two Marcus-type parabolas cross,
`√(λ₁λ₂)(√λ₂ - √λ₁)/(√λ₁ + √λ₂)`. -/
noncomputable def apexPar (lam1 lam2 : ℝ) : ℝ :=
  (lam2 * Real.sqrt lam1 - lam1 * Real.sqrt lam2) / (Real.sqrt lam1 + Real.sqrt lam2)

/-- The BEP-linear volcano is the maximum of the two tangent lines of the parabolic branches: the
literature's linear volcano, read as the tangent (linear-response) form of the repository's model. -/
theorem linearVolcano_eq_bepTangent (lam1 lam2 dE : ℝ) :
    volcanoBarrier (1 / 2) (lam1 / 4) (1 / 2) (lam2 / 4) dE
      = max (BEP.bepLine lam1 (-dE)) (BEP.bepLine lam2 dE) := by sorry

/-- The BEP tangent line lies below the parabola it is tangent to (the linear-response direction). -/
theorem bepLine_le_eact {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    BEP.bepLine lam x ≤ BEP.eact lam x := by sorry

/-- The BEP-linear volcano is a pointwise LOWER BOUND on the two-parabola volcano: the linear model
optimistically underestimates the barrier away from the apex. -/
theorem linearVolcano_le_parabolic {lam1 lam2 : ℝ} (h1 : 0 < lam1) (h2 : 0 < lam2) (dE : ℝ) :
    volcanoBarrier (1 / 2) (lam1 / 4) (1 / 2) (lam2 / 4) dE ≤ parabolicBarrier lam1 lam2 dE := by
  sorry

/-- The two Marcus-type parabolas cross at `apexPar`. -/
theorem parabolicBarrier_crossing {lam1 lam2 : ℝ} (h1 : 0 < lam1) (h2 : 0 < lam2) :
    parabolaUp lam1 (apexPar lam1 lam2) = parabolaDown lam2 (apexPar lam1 lam2) := by sorry

/-- The crossing point of the two parabolas is a global minimizer of their maximum. -/
theorem parabolicBarrier_apex_le {lam1 lam2 : ℝ} (h1 : 0 < lam1) (h2 : 0 < lam2) (dE : ℝ) :
    parabolicBarrier lam1 lam2 (apexPar lam1 lam2) ≤ parabolicBarrier lam1 lam2 dE := by sorry

/-- The crossing point is the unique global minimizer of the parabolic effective barrier. -/
theorem parabolicBarrier_eq_apex_iff {lam1 lam2 : ℝ} (h1 : 0 < lam1) (h2 : 0 < lam2) (dE : ℝ) :
    parabolicBarrier lam1 lam2 dE = parabolicBarrier lam1 lam2 (apexPar lam1 lam2)
      ↔ dE = apexPar lam1 lam2 := by sorry

/-- The two-parabola model is a volcano whenever both curvatures are physical — no BEP linearization
is needed for the Sabatier description. -/
theorem parabolic_descriptor {lam1 lam2 : ℝ} (h1 : 0 < lam1) (h2 : 0 < lam2) :
    VolcanoDescriptor (fun dE => parabolicBarrier lam1 lam2 dE) (apexPar lam1 lam2) := by sorry

/-- A symmetric two-parabola cycle has its apex at the thermoneutral descriptor value `dE = 0`. -/
theorem apexPar_self {lam : ℝ} (h : 0 < lam) : apexPar lam lam = 0 := by sorry

/-- At a symmetric cycle's apex the linear volcano is exact: the tangent-line model and the parabola
model agree at the pass. -/
theorem linearVolcano_apex_exact {lam : ℝ} (h : 0 < lam) :
    volcanoBarrier (1 / 2) (lam / 4) (1 / 2) (lam / 4) 0 = parabolicBarrier lam lam 0 := by sorry

/-! ## S5a — rational decision layer (`PhotoLean/Sabatier/RatModel.lean`) -/

/-- Rational ascending branch (the computable mirror of `branchUp`). -/
noncomputable def branchUpQ (alphaA betaA dE : ℚ) : ℚ := alphaA * dE + betaA

/-- Rational descending branch (the computable mirror of `branchDown`). -/
noncomputable def branchDownQ (alphaB betaB dE : ℚ) : ℚ := betaB - alphaB * dE

/-- Rational effective barrier (the computable mirror of `volcanoBarrier`). -/
noncomputable def volcanoBarrierQ (alphaA betaA alphaB betaB dE : ℚ) : ℚ :=
  max (branchUpQ alphaA betaA dE) (branchDownQ alphaB betaB dE)

/-- Rational apex (the computable mirror of `apex`). -/
noncomputable def apexQ (alphaA betaA alphaB betaB : ℚ) : ℚ :=
  (betaB - betaA) / (alphaA + alphaB)

/-- Rational pass height (the computable mirror of `apexBarrier`). -/
noncomputable def apexBarrierQ (alphaA betaA alphaB betaB : ℚ) : ℚ :=
  volcanoBarrierQ alphaA betaA alphaB betaB (apexQ alphaA betaA alphaB betaB)

/-- Rational decidable classifier of the three Sabatier regimes. -/
noncomputable def sabatierZoneQ (apexD dE : ℚ) : SZone :=
  if dE = apexD then SZone.optimal
  else if dE < apexD then SZone.tooStrong
  else SZone.tooWeak

/-- Series-level conformance verdict in the computable layer. -/
def SabatierConformsQ (alphaA alphaB : ℚ) : Prop := 0 < alphaA ∧ 0 < alphaB

/-- Tolerance form of the Sabatier optimum in the computable layer. -/
def NearOptimalQ (tol apexD dE : ℚ) : Prop := |dE - apexD| ≤ tol

/-- Cast transfer of the ascending branch. -/
theorem branchUpQ_cast (alphaA betaA dE : ℚ) :
    ((branchUpQ alphaA betaA dE : ℚ) : ℝ)
      = branchUp (alphaA : ℝ) (betaA : ℝ) (dE : ℝ) := by sorry

/-- Cast transfer of the descending branch. -/
theorem branchDownQ_cast (alphaB betaB dE : ℚ) :
    ((branchDownQ alphaB betaB dE : ℚ) : ℝ)
      = branchDown (alphaB : ℝ) (betaB : ℝ) (dE : ℝ) := by sorry

/-- Cast transfer of the effective barrier. -/
theorem volcanoBarrierQ_cast (alphaA betaA alphaB betaB dE : ℚ) :
    ((volcanoBarrierQ alphaA betaA alphaB betaB dE : ℚ) : ℝ)
      = volcanoBarrier (alphaA : ℝ) (betaA : ℝ) (alphaB : ℝ) (betaB : ℝ) (dE : ℝ) := by sorry

/-- Cast transfer of the apex. -/
theorem apexQ_cast (alphaA betaA alphaB betaB : ℚ) :
    ((apexQ alphaA betaA alphaB betaB : ℚ) : ℝ)
      = apex (alphaA : ℝ) (betaA : ℝ) (alphaB : ℝ) (betaB : ℝ) := by sorry

/-- Cast transfer of the pass height. -/
theorem apexBarrierQ_cast (alphaA betaA alphaB betaB : ℚ) :
    ((apexBarrierQ alphaA betaA alphaB betaB : ℚ) : ℝ)
      = apexBarrier (alphaA : ℝ) (betaA : ℝ) (alphaB : ℝ) (betaB : ℝ) := by sorry

/-- The rational classifier is the rational mirror of the real classifier. -/
theorem sabatierZoneQ_eq_sabatierZone (apexD dE : ℚ) :
    sabatierZoneQ apexD dE = sabatierZone (apexD : ℝ) (dE : ℝ) := by sorry

/-- The rational classifier recognizes the optimum. -/
theorem sabatierZoneQ_eq_optimal_iff (apexD dE : ℚ) :
    sabatierZoneQ apexD dE = SZone.optimal ↔ dE = apexD := by sorry

/-- The rational classifier recognizes the too-strong-binding regime. -/
theorem sabatierZoneQ_eq_tooStrong_iff (apexD dE : ℚ) :
    sabatierZoneQ apexD dE = SZone.tooStrong ↔ dE < apexD := by sorry

/-- The rational classifier recognizes the too-weak-binding regime. -/
theorem sabatierZoneQ_eq_tooWeak_iff (apexD dE : ℚ) :
    sabatierZoneQ apexD dE = SZone.tooWeak ↔ apexD < dE := by sorry

/-- The rational conformance verdict is the rational mirror of the real one. -/
theorem sabatierConformsQ_iff (alphaA alphaB : ℚ) :
    SabatierConformsQ alphaA alphaB ↔ SabatierConforms (alphaA : ℝ) (alphaB : ℝ) := by sorry

/-- The rational tolerance band is the rational mirror of the real one. -/
theorem nearOptimalQ_iff (tol apexD dE : ℚ) :
    NearOptimalQ tol apexD dE ↔ NearOptimal (tol : ℝ) (apexD : ℝ) (dE : ℝ) := by sorry

/-- The rational apex is a global minimizer of the rational effective barrier. -/
theorem volcanoBarrierQ_apex_le {alphaA betaA alphaB betaB : ℚ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) (dE : ℚ) :
    volcanoBarrierQ alphaA betaA alphaB betaB (apexQ alphaA betaA alphaB betaB)
      ≤ volcanoBarrierQ alphaA betaA alphaB betaB dE := by sorry

/-- The rational apex is the unique global minimizer of the rational effective barrier. -/
theorem volcanoBarrierQ_eq_apex_iff {alphaA betaA alphaB betaB : ℚ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) (dE : ℚ) :
    volcanoBarrierQ alphaA betaA alphaB betaB dE
        = volcanoBarrierQ alphaA betaA alphaB betaB (apexQ alphaA betaA alphaB betaB)
      ↔ dE = apexQ alphaA betaA alphaB betaB := by sorry

/-! ## S5b — instance verdicts (`PhotoLean/Sabatier/Instances.lean`) -/

/-- I1 (symmetric cycle): apex of the thermoneutral series `alphaA = alphaB = 1/2`,
`betaA = betaB = 1/2`. -/
theorem inst_I1_apex : apex (1 / 2) (1 / 2) (1 / 2) (1 / 2) = 0 := by sorry

/-- I1 (symmetric cycle): the series conforms to the Sabatier description. -/
theorem inst_I1_conforms : SabatierConforms (1 / 2) (1 / 2) := by sorry

/-- I1 (symmetric cycle): the pass height. -/
theorem inst_I1_apexBarrier : apexBarrier (1 / 2) (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by sorry

/-- I1 (symmetric cycle): a catalyst at the apex is classified optimal. -/
theorem inst_I1_zone_optimal :
    sabatierZone (apex (1 / 2) (1 / 2) (1 / 2) (1 / 2)) 0 = SZone.optimal := by sorry

/-- I1 (symmetric cycle): a catalyst binding more strongly than the apex is classified too strong. -/
theorem inst_I1_zone_tooStrong :
    sabatierZone (apex (1 / 2) (1 / 2) (1 / 2) (1 / 2)) (-(1 / 2)) = SZone.tooStrong := by sorry

/-- I1 (symmetric cycle): the barrier of the too-strongly-binding catalyst. -/
theorem inst_I1_barrier_tooStrong :
    volcanoBarrier (1 / 2) (1 / 2) (1 / 2) (1 / 2) (-(1 / 2)) = 3 / 4 := by sorry

/-- I2 (asymmetric cycle `alphaA = 1/2`, `betaA = 0`, `alphaB = 1`, `betaB = 1`): the apex. -/
theorem inst_I2_apex : apex (1 / 2) 0 1 1 = 2 / 3 := by sorry

/-- I2: the series conforms to the Sabatier description. -/
theorem inst_I2_conforms : SabatierConforms (1 / 2) 1 := by sorry

/-- I2: a catalyst at `dE = 0` lies BELOW the apex `2/3` on the descriptor axis (where more negative
= stronger binding), so it is classified too strong. -/
theorem inst_I2_zone_tooStrong : sabatierZone (apex (1 / 2) 0 1 1) 0 = SZone.tooStrong := by sorry

/-- I2: the barrier of that strongly-binding catalyst (`1`: the branch penalized by strong binding
dominates). -/
theorem inst_I2_barrier_tooStrong : volcanoBarrier (1 / 2) 0 1 1 0 = 1 := by sorry

/-- I2: a catalyst at `dE = 1`, ABOVE the apex `2/3`, is classified too weak. -/
theorem inst_I2_zone_tooWeak : sabatierZone (apex (1 / 2) 0 1 1) 1 = SZone.tooWeak := by sorry

/-- I2: the barrier of that weakly-binding catalyst (`1/2`: the ascending branch dominates). -/
theorem inst_I2_barrier_tooWeak : volcanoBarrier (1 / 2) 0 1 1 1 = 1 / 2 := by sorry

/-- I3 (the same series, a strongly-binding catalyst `dE = -1/3`): the barrier. -/
theorem inst_I3_barrier_tooStrong : volcanoBarrier (1 / 2) 0 1 1 (-(1 / 3)) = 4 / 3 := by sorry

/-- I3: the strongly-binding catalyst is classified too strong. -/
theorem inst_I3_zone_tooStrong : sabatierZone (apex (1 / 2) 0 1 1) (-(1 / 3)) = SZone.tooStrong := by
  sorry

/-- I4 (zero-slope branch series `alphaA = 0`, `betaA = 1`, `alphaB = 1`, `betaB = 1`): the series
does NOT conform to the Sabatier description — there is no pointed apex. -/
theorem inst_I4_notConforms : ¬ SabatierConforms 0 1 := by sorry

/-- I4: the barrier profile of the zero-slope series is not a volcano. -/
theorem inst_I4_notDescriptor :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier 0 1 1 1 dE) (apex 0 1 1 1) := by sorry

/-- I4: the barrier of that series is minimal on a whole half-line (a plateau, not a pass). -/
theorem inst_I4_plateau (dE : ℝ) (h : 0 ≤ dE) :
    volcanoBarrier 0 1 1 1 dE = volcanoBarrier 0 1 1 1 (apex 0 1 1 1) := by sorry

/-- I5 (mixed-slope series `alphaA = 1`, `betaA = 0`, `alphaB = -1`, `betaB = 1`): the series does
NOT conform to the Sabatier description. -/
theorem inst_I5_notConforms : ¬ SabatierConforms 1 (-1) := by sorry

/-- I5: its barrier is strictly monotone in the descriptor — the volcano has disappeared. -/
theorem inst_I5_monotone (dE₁ dE₂ : ℝ) (h : dE₁ < dE₂) :
    volcanoBarrier 1 0 (-1) 1 dE₁ < volcanoBarrier 1 0 (-1) 1 dE₂ := by sorry

/-- I6 (tolerance verdict on I2): the descriptor `dE = 1/2` lies within `tol = 1/2` of the apex. -/
theorem inst_I6_nearOptimal : NearOptimalQ (1 / 2) (apexQ (1 / 2) 0 1 1) (1 / 2) := by sorry

/-- I6: its barrier excess over the pass respects the tolerance bound of `volcanoBarrier_le_apex_add`
(`1/6 ≤ 1/2` in this instance). -/
theorem inst_I6_penalty :
    volcanoBarrier (1 / 2) 0 1 1 (1 / 2) - apexBarrier (1 / 2) 0 1 1 ≤ 1 / 2 := by sorry

/-- I7 (two-parabola cross-check `lam1 = 1`, `lam2 = 4`): the apex of the parabolic volcano. -/
theorem inst_I7_apexPar : apexPar 1 4 = 2 / 3 := by sorry

/-- I7: the two parabolic branches cross exactly at the apex. -/
theorem inst_I7_crossing :
    parabolaUp 1 (apexPar 1 4) = parabolaDown 4 (apexPar 1 4) := by sorry

/-- I7: the pass height of the parabolic volcano (`25/36`), equal for both branches. -/
theorem inst_I7_apexBarrier : parabolicBarrier 1 4 (apexPar 1 4) = 25 / 36 := by sorry

/-- I7: the linear BEP volcano underestimates the parabolic barrier at the apex (`2/3 < 25/36`). -/
theorem inst_I7_linear_below :
    volcanoBarrier (1 / 2) (1 / 4) (1 / 2) 1 (apexPar 1 4) < parabolicBarrier 1 4 (apexPar 1 4) := by
  sorry

/-- I8 (non-vacuity of the verdict layer): the I2 series has an exactly optimal catalyst. -/
theorem inst_I8_exists_optimal : ∃ dE : ℝ, Optimal (apex (1 / 2) 0 1 1) dE := by sorry

/-- I9 (literature row, HER — the number is a premise, the verdict is kernel-checked): the reported
`ΔG_H*` of Pt is `-0.09` eV (Nørskov et al. 2005, Table I with Eq. [8] `ΔG_H* = ΔE_H + 0.24 eV`;
`[arith]` in `theories/Sabatier/LITERATURE.md` §R2.1; the axis convention is plan §2). Read against
the symmetric reference volcano (apex at `dE = 0`, the literature's own reading "ΔG_H* = 0 separates
the two legs"), Pt binds too strongly. -/
theorem inst_I9_zone_Pt :
    sabatierZone (apex (1 / 2) (1 / 2) (1 / 2) (1 / 2)) (-(9 / 100)) = SZone.tooStrong := by sorry

/-- I9: Pt is within the 10 %-of-1 tolerance band of the apex (`9/100 ≤ 1/10`). -/
theorem inst_I9_nearOptimal_Pt :
    NearOptimalQ (1 / 10) (apexQ (1 / 2) (1 / 2) (1 / 2) (1 / 2)) (-(9 / 100)) := by sorry

/-- I9: the barrier of Pt on the reference volcano (`109/200` — the pass height `1/2` plus `9/200`,
i.e. half of the descriptor's distance from the apex). -/
theorem inst_I9_barrier_Pt :
    volcanoBarrier (1 / 2) (1 / 2) (1 / 2) (1 / 2) (-(9 / 100)) = 109 / 200 := by sorry

/-- I10 (literature row, HER): the reported `ΔG_H*` of Au is `+0.45` eV (same provenance) — too weak,
and outside the 10 % band. -/
theorem inst_I10_zone_Au :
    sabatierZone (apex (1 / 2) (1 / 2) (1 / 2) (1 / 2)) (45 / 100) = SZone.tooWeak := by sorry

/-- I10: Au is outside the 10 % tolerance band (`45/100 > 1/10`). -/
theorem inst_I10_notNearOptimal_Au :
    ¬ NearOptimalQ (1 / 10) (apexQ (1 / 2) (1 / 2) (1 / 2) (1 / 2)) (45 / 100) := by sorry

/-- I10: the barrier of Au on the reference volcano (`29/40`). -/
theorem inst_I10_barrier_Au :
    volcanoBarrier (1 / 2) (1 / 2) (1 / 2) (1 / 2) (45 / 100) = 29 / 40 := by sorry

/-- I11 (literature row, HER): the reported `ΔG_H*` of W is `-0.43` eV (Table I, bcc(110); the source
itself warns that the measured value for W/Mo/Nb is probably not representative of the metallic
state — the caveat travels with the number). Too strong; inside a `1/2` band, which is the
tolerance sensitivity the verdict layer exists to expose. -/
theorem inst_I11_zone_W :
    sabatierZone (apex (1 / 2) (1 / 2) (1 / 2) (1 / 2)) (-(43 / 100)) = SZone.tooStrong := by sorry

/-- I11: W is inside the `1/2` tolerance band. -/
theorem inst_I11_nearOptimal_W :
    NearOptimalQ (1 / 2) (apexQ (1 / 2) (1 / 2) (1 / 2) (1 / 2)) (-(43 / 100)) := by sorry

/-- I12 (literature row, OER — DERIVABLE from the stated premise): the printed OER volcano of Man et
al. 2011 (Eq. 4.16–4.18), `max (ΔG_O - ΔG_OH, 3.20 - (ΔG_O - ΔG_OH))`, IS the two-branch model with
`alphaA = alphaB = 1`, `betaA = 0`, `betaB = 16/5` (the printed `3.20 eV` scaling premise). Apex. -/
theorem inst_I12_OER_apex : apex 1 0 1 (16 / 5) = 8 / 5 := by sorry

/-- I12: the pass height of the OER volcano is `8/5` eV — the literature's printed optimal descriptor
`1.60 eV`. -/
theorem inst_I12_OER_apexBarrier : apexBarrier 1 0 1 (16 / 5) = 8 / 5 := by sorry

/-- I12: the OER series conforms to the Sabatier description. -/
theorem inst_I12_OER_conforms : SabatierConforms 1 1 := by sorry

/-- I12: the OER overpotential at the apex, `8/5 - 123/100 = 37/100` V — the literature's printed
`0.37 V` (LITERATURE.md §R2.2). -/
theorem inst_I12_OER_overpotential :
    apexBarrier 1 0 1 (16 / 5) - 123 / 100 = 37 / 100 := by sorry

end Sabatier

end PhotoLean
