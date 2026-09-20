/-
PhotoLean.Sabatier.Basic — S1, the description layer of the Sabatier theory (the volcano plot).

The model (plan §1.2, §2): a two-step catalytic cycle on ONE descriptor `dE`, the binding energy of
the key intermediate on the catalyst surface in the convention "more negative = stronger binding".
The effective (rate-limiting) barrier is the maximum of two Brønsted–Evans–Polanyi branches —
`branchUp` (the step penalized by weak binding, slope `alphaA`) and `branchDown` (the step penalized
by strong binding, slope `-alphaB`). The apex is the crossing point of the two branches, a DERIVED
quantity (`apex`); the activity is the Arrhenius form `exp (-Ea/(kB*T))` and the volcano plot is the
graph of the activity against `dE`.

Model assumptions that are NOT derived here (plan §12, honesty table): the effective barrier of the
two-step cycle is the MAXIMUM of the two branch barriers (the literature's rate-determining-step
argument, made an explicit premise, not a theorem — `Ea = max` is not a kinetic law of the
literature); both steps follow a BEP line in the descriptor; the descriptor is a single scalar; the
activity is the Arrhenius form with a descriptor-independent prefactor. Every physical premise is an
explicit hypothesis of the statements; nothing is hidden in a definition.

There is no unproved placeholder and no custom axiom anywhere in this file.

Statement authority: every authority declaration below matches
`theories/Sabatier/probes/sabatier-statement-skeleton.lean` §S1 word for word (plan §3). Sprint-0
kernel evidence for the statement forms: `theories/Sabatier/probes/sabatier-risk-probe.lean`.
-/
import Mathlib

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

/-- The effective barrier at the apex (the height of the volcano's pass in the physical
orientation; that the apex is a MINIMIZER is the S2/S3 content, not this definition). -/
noncomputable def apexBarrier (alphaA betaA alphaB betaB : ℝ) : ℝ :=
  volcanoBarrier alphaA betaA alphaB betaB (apex alphaA betaA alphaB betaB)

/-- The volcano (Sabatier) description of a barrier profile `f` with claimed apex `de0`: `de0` is
the *unique* global minimizer of `f`. Family-level predicate, independent of the height scale. -/
def VolcanoDescriptor (f : ℝ → ℝ) (de0 : ℝ) : Prop :=
  (∀ dE : ℝ, f de0 ≤ f dE) ∧ (∀ dE : ℝ, f dE = f de0 → dE = de0)

/-- The dual (anti-volcano) description: `de0` is the *unique* global maximizer of `f`. It is the
form in which the volcano plot of the ACTIVITY is stated: a volcano in the barrier is a peak in the
activity, so — for `0 < kB*T` — `VolcanoDescriptor f de0` is equivalent to
`AntiVolcanoDescriptor (activity f kB T) de0` (`antiDescriptor_activity_iff`, S2, which carries the
`0 < kB*T` premise; at `kB*T = 0` the activity is the constant `1` and has no unique maximizer, a
counterexample kernel-checked in `theories/Sabatier/probes/sabatier-risk-probe.lean`). -/
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

/-- Auxiliary: multiplying the apex by the total slope cancels the division. -/
private theorem apex_mul_ne {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    (alphaA + alphaB) * apex alphaA betaA alphaB betaB = betaB - betaA := by
  rw [apex, mul_div_cancel₀ _ h]

/-! ## Lemmas (plan §4.2, §4.3) -/

/-- The gap between the two branches is affine in the descriptor, with slope `alphaA + alphaB` and
value `-(betaB - betaA)` at `dE = 0`; it is the sign core of the apex geometry. -/
theorem branch_gap (alphaA betaA alphaB betaB dE : ℝ) :
    branchUp alphaA betaA dE - branchDown alphaB betaB dE
      = (alphaA + alphaB) * dE - (betaB - betaA) := by
  unfold branchUp branchDown
  ring

/-- Auxiliary form used by the branch-identification lemmas: on the weak-binding side the descending
branch is dominated by the ascending one. -/
theorem branchDown_le_branchUp_of_apex_le {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : apex alphaA betaA alphaB betaB ≤ dE) :
    branchDown alphaB betaB dE ≤ branchUp alphaA betaA dE := by
  have hgap := branch_gap alphaA betaA alphaB betaB dE
  have hmul : (alphaA + alphaB) * apex alphaA betaA alphaB betaB ≤ (alphaA + alphaB) * dE :=
    mul_le_mul_of_nonneg_left h hAB.le
  rw [apex_mul_ne hAB.ne'] at hmul
  linarith

/-- Auxiliary form used by the branch-identification lemmas: on the strong-binding side the ascending
branch is dominated by the descending one. -/
theorem branchUp_le_branchDown_of_le_apex {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : dE ≤ apex alphaA betaA alphaB betaB) :
    branchUp alphaA betaA dE ≤ branchDown alphaB betaB dE := by
  have hgap := branch_gap alphaA betaA alphaB betaB dE
  have hmul : (alphaA + alphaB) * dE ≤ (alphaA + alphaB) * apex alphaA betaA alphaB betaB :=
    mul_le_mul_of_nonneg_left h hAB.le
  rw [apex_mul_ne hAB.ne'] at hmul
  linarith

/-- The apex is a crossing point of the two branches (when the apex formula is defined). -/
theorem apex_crossing {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    branchUp alphaA betaA (apex alphaA betaA alphaB betaB)
      = branchDown alphaB betaB (apex alphaA betaA alphaB betaB) := by
  unfold branchUp branchDown apex
  field_simp
  ring

/-- The apex is the *unique* crossing point of the two branches. -/
theorem apex_unique_crossing {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) (dE : ℝ) :
    (branchUp alphaA betaA dE = branchDown alphaB betaB dE)
      ↔ dE = apex alphaA betaA alphaB betaB := by
  constructor
  · intro hh
    unfold branchUp branchDown at hh
    rw [apex, eq_div_iff h]
    linarith
  · intro hh
    rw [hh]
    exact apex_crossing h

/-- The apex sits at the thermoneutral descriptor value `dE = 0` exactly for a balanced cycle
(equal branch offsets). -/
theorem apex_eq_zero_iff {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    apex alphaA betaA alphaB betaB = 0 ↔ betaA = betaB := by
  rw [apex, div_eq_zero_iff]
  constructor
  · rintro (h1 | h1)
    · linarith
    · exact absurd h1 h
  · intro h1
    left
    linarith

/-- Apex under the label swap: passing the two branches through the relabelling identity
(`volcanoBarrier_relabel`) changes the second slope's sign as well, so the apex is NOT invariant
under a naive parameter swap; it is invariant under this relabelling. -/
theorem apex_relabel (alphaA betaA alphaB betaB : ℝ) :
    apex alphaA betaA alphaB betaB = apex (-alphaB) betaB (-alphaA) betaA := by
  unfold apex
  rw [show betaA - betaB = -(betaB - betaA) by ring,
    show -alphaB + -alphaA = -(alphaA + alphaB) by ring, neg_div_neg_eq]

/-- Relabelling identity of the barrier profile: a model whose ascending/descending slopes are both
negative is the same volcano with the two branches interchanged. -/
theorem volcanoBarrier_relabel (alphaA betaA alphaB betaB dE : ℝ) :
    volcanoBarrier alphaA betaA alphaB betaB dE
      = volcanoBarrier (-alphaB) betaB (-alphaA) betaA dE := by
  unfold volcanoBarrier branchUp branchDown
  rw [show (betaB - alphaB * dE) = (-alphaB * dE + betaB) by ring,
    show (alphaA * dE + betaA) = (betaA - -alphaA * dE) by ring]
  exact max_comm _ _

/-- At the apex the two branches are equal, so the effective barrier equals either of them. -/
theorem volcanoBarrier_at_apex {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    volcanoBarrier alphaA betaA alphaB betaB (apex alphaA betaA alphaB betaB)
      = branchUp alphaA betaA (apex alphaA betaA alphaB betaB) := by
  unfold volcanoBarrier
  rw [apex_crossing h, max_self]

/-- Below the apex the descending branch dominates. -/
theorem branchUp_lt_branchDown_of_lt_apex {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : dE < apex alphaA betaA alphaB betaB) :
    branchUp alphaA betaA dE < branchDown alphaB betaB dE := by
  have hgap := branch_gap alphaA betaA alphaB betaB dE
  have hmul : (alphaA + alphaB) * dE < (alphaA + alphaB) * apex alphaA betaA alphaB betaB :=
    mul_lt_mul_of_pos_left h hAB
  rw [apex_mul_ne hAB.ne'] at hmul
  linarith

/-- Above the apex the ascending branch dominates. -/
theorem branchDown_lt_branchUp_of_apex_lt {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : apex alphaA betaA alphaB betaB < dE) :
    branchDown alphaB betaB dE < branchUp alphaA betaA dE := by
  have hgap := branch_gap alphaA betaA alphaB betaB dE
  have hmul : (alphaA + alphaB) * apex alphaA betaA alphaB betaB < (alphaA + alphaB) * dE :=
    mul_lt_mul_of_pos_left h hAB
  rw [apex_mul_ne hAB.ne'] at hmul
  linarith

/-- On the weak-binding side (`apex ≤ dE`) the effective barrier IS the ascending branch. -/
theorem volcanoBarrier_eq_branchUp_of_apex_le {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : apex alphaA betaA alphaB betaB ≤ dE) :
    volcanoBarrier alphaA betaA alphaB betaB dE = branchUp alphaA betaA dE := by
  unfold volcanoBarrier
  exact max_eq_left (branchDown_le_branchUp_of_apex_le hAB h)

/-- On the strong-binding side (`dE ≤ apex`) the effective barrier IS the descending branch. -/
theorem volcanoBarrier_eq_branchDown_of_le_apex {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : dE ≤ apex alphaA betaA alphaB betaB) :
    volcanoBarrier alphaA betaA alphaB betaB dE = branchDown alphaB betaB dE := by
  unfold volcanoBarrier
  exact max_eq_right (branchUp_le_branchDown_of_le_apex hAB h)

/-- The classifier recognizes the optimum. -/
theorem sabatierZone_eq_optimal_iff (apexD dE : ℝ) :
    sabatierZone apexD dE = SZone.optimal ↔ dE = apexD := by
  unfold sabatierZone
  split_ifs with h1 h2
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩

/-- The classifier recognizes the too-strong-binding regime. -/
theorem sabatierZone_eq_tooStrong_iff (apexD dE : ℝ) :
    sabatierZone apexD dE = SZone.tooStrong ↔ dE < apexD := by
  unfold sabatierZone
  split_ifs with h1 h2
  · subst h1
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (lt_irrefl _)⟩
  · exact ⟨fun _ => h2, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h2⟩

/-- The classifier recognizes the too-weak-binding regime. -/
theorem sabatierZone_eq_tooWeak_iff (apexD dE : ℝ) :
    sabatierZone apexD dE = SZone.tooWeak ↔ apexD < dE := by
  unfold sabatierZone
  split_ifs with h1 h2
  · subst h1
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (lt_irrefl _)⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h (by linarith)⟩
  · exact ⟨fun _ => lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm h1), fun _ => rfl⟩

/-- The tolerance form is the closed band around the apex (no hypothesis on the sign of `tol`). -/
theorem nearOptimal_iff_band (apexD dE tol : ℝ) :
    NearOptimal tol apexD dE ↔ apexD - tol ≤ dE ∧ dE ≤ apexD + tol := by
  unfold NearOptimal
  rw [abs_le]
  constructor
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

end Sabatier

end PhotoLean
