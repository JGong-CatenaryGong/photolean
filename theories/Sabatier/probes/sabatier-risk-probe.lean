/-
Lead risk probe for the Sabatier theory — Sprint 0. Proves the *critical-path statement forms* of
`theories/Sabatier/probes/sabatier-statement-skeleton.lean` BEFORE the plan is frozen and the
milestones are dispatched (engine protocol §2: statement-first). Definitions below are copied
verbatim from the skeleton. The probe already caught two FALSE skeleton rows (the label-swap "comm"
identities and the activity-descriptor direction); both were corrected in the authority and the
correction is logged in `theories/Sabatier/plan.md` §3.1.

Evidence: `proofs/scripts/lake env lean theories/Sabatier/probes/sabatier-risk-probe.lean` → 0 error.
-/
import Mathlib
import PhotoLean.BEP.Basic

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Sabatier

/-! ## Definitions (verbatim from the statement skeleton) -/

noncomputable def branchUp (alphaA betaA dE : ℝ) : ℝ := alphaA * dE + betaA

noncomputable def branchDown (alphaB betaB dE : ℝ) : ℝ := betaB - alphaB * dE

noncomputable def volcanoBarrier (alphaA betaA alphaB betaB dE : ℝ) : ℝ :=
  max (branchUp alphaA betaA dE) (branchDown alphaB betaB dE)

noncomputable def apex (alphaA betaA alphaB betaB : ℝ) : ℝ :=
  (betaB - betaA) / (alphaA + alphaB)

noncomputable def apexBarrier (alphaA betaA alphaB betaB : ℝ) : ℝ :=
  volcanoBarrier alphaA betaA alphaB betaB (apex alphaA betaA alphaB betaB)

def VolcanoDescriptor (f : ℝ → ℝ) (de0 : ℝ) : Prop :=
  (∀ dE : ℝ, f de0 ≤ f dE) ∧ (∀ dE : ℝ, f dE = f de0 → dE = de0)

def AntiVolcanoDescriptor (f : ℝ → ℝ) (de0 : ℝ) : Prop :=
  (∀ dE : ℝ, f dE ≤ f de0) ∧ (∀ dE : ℝ, f dE = f de0 → dE = de0)

noncomputable def activity (f : ℝ → ℝ) (kB T : ℝ) : ℝ → ℝ :=
  fun dE => Real.exp (-(f dE) / (kB * T))

def SabatierConforms (alphaA alphaB : ℝ) : Prop := 0 < alphaA ∧ 0 < alphaB

def TooStrong (apexD dE : ℝ) : Prop := dE < apexD

def Optimal (apexD dE : ℝ) : Prop := dE = apexD

def TooWeak (apexD dE : ℝ) : Prop := apexD < dE

def NearOptimal (tol apexD dE : ℝ) : Prop := |dE - apexD| ≤ tol

inductive SZone where
  | tooStrong
  | optimal
  | tooWeak
  deriving DecidableEq, Repr

noncomputable def sabatierZone (apexD dE : ℝ) : SZone :=
  if dE = apexD then SZone.optimal
  else if dE < apexD then SZone.tooStrong
  else SZone.tooWeak

noncomputable def apexPar (lam1 lam2 : ℝ) : ℝ :=
  (lam2 * Real.sqrt lam1 - lam1 * Real.sqrt lam2) / (Real.sqrt lam1 + Real.sqrt lam2)

/-! ## Probe-local helpers -/

private theorem max_lt_max_aux {a b c d : ℝ} (h1 : a < c) (h2 : b < d) : max a b < max c d := by
  rw [max_lt_iff]
  exact ⟨lt_of_lt_of_le h1 (le_max_left c d), lt_of_lt_of_le h2 (le_max_right c d)⟩

private theorem apex_mul_ne {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    (alphaA + alphaB) * apex alphaA betaA alphaB betaB = betaB - betaA := by
  rw [apex, mul_div_cancel₀ _ h]

/-! ## S1 — description layer -/

theorem branch_gap (alphaA betaA alphaB betaB dE : ℝ) :
    branchUp alphaA betaA dE - branchDown alphaB betaB dE
      = (alphaA + alphaB) * dE - (betaB - betaA) := by
  unfold branchUp branchDown
  ring

theorem apex_crossing {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    branchUp alphaA betaA (apex alphaA betaA alphaB betaB)
      = branchDown alphaB betaB (apex alphaA betaA alphaB betaB) := by
  unfold branchUp branchDown apex
  field_simp
  ring

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

theorem apex_relabel (alphaA betaA alphaB betaB : ℝ) :
    apex alphaA betaA alphaB betaB = apex (-alphaB) betaB (-alphaA) betaA := by
  unfold apex
  rw [show betaA - betaB = -(betaB - betaA) by ring,
    show -alphaB + -alphaA = -(alphaA + alphaB) by ring, neg_div_neg_eq]

theorem volcanoBarrier_relabel (alphaA betaA alphaB betaB dE : ℝ) :
    volcanoBarrier alphaA betaA alphaB betaB dE
      = volcanoBarrier (-alphaB) betaB (-alphaA) betaA dE := by
  unfold volcanoBarrier branchUp branchDown
  rw [show (betaB - alphaB * dE) = (-alphaB * dE + betaB) by ring,
    show (alphaA * dE + betaA) = (betaA - -alphaA * dE) by ring]
  exact max_comm _ _

theorem volcanoBarrier_at_apex {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    volcanoBarrier alphaA betaA alphaB betaB (apex alphaA betaA alphaB betaB)
      = branchUp alphaA betaA (apex alphaA betaA alphaB betaB) := by
  unfold volcanoBarrier
  rw [apex_crossing h, max_self]

theorem branchDown_le_branchUp_of_apex_le {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : apex alphaA betaA alphaB betaB ≤ dE) :
    branchDown alphaB betaB dE ≤ branchUp alphaA betaA dE := by
  have hgap := branch_gap alphaA betaA alphaB betaB dE
  have hmul : (alphaA + alphaB) * apex alphaA betaA alphaB betaB ≤ (alphaA + alphaB) * dE :=
    mul_le_mul_of_nonneg_left h hAB.le
  rw [apex_mul_ne hAB.ne'] at hmul
  linarith

theorem branchUp_lt_branchDown_of_lt_apex {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : dE < apex alphaA betaA alphaB betaB) :
    branchUp alphaA betaA dE < branchDown alphaB betaB dE := by
  have hgap := branch_gap alphaA betaA alphaB betaB dE
  have hmul : (alphaA + alphaB) * dE < (alphaA + alphaB) * apex alphaA betaA alphaB betaB :=
    mul_lt_mul_of_pos_left h hAB
  rw [apex_mul_ne hAB.ne'] at hmul
  linarith

theorem branchDown_lt_branchUp_of_apex_lt {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : apex alphaA betaA alphaB betaB < dE) :
    branchDown alphaB betaB dE < branchUp alphaA betaA dE := by
  have hgap := branch_gap alphaA betaA alphaB betaB dE
  have hmul : (alphaA + alphaB) * apex alphaA betaA alphaB betaB < (alphaA + alphaB) * dE :=
    mul_lt_mul_of_pos_left h hAB
  rw [apex_mul_ne hAB.ne'] at hmul
  linarith

theorem volcanoBarrier_eq_branchUp_of_apex_le {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : apex alphaA betaA alphaB betaB ≤ dE) :
    volcanoBarrier alphaA betaA alphaB betaB dE = branchUp alphaA betaA dE := by
  unfold volcanoBarrier
  exact max_eq_left (branchDown_le_branchUp_of_apex_le hAB h)

theorem branchUp_le_branchDown_of_le_apex {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : dE ≤ apex alphaA betaA alphaB betaB) :
    branchUp alphaA betaA dE ≤ branchDown alphaB betaB dE := by
  have hgap := branch_gap alphaA betaA alphaB betaB dE
  have hmul : (alphaA + alphaB) * dE ≤ (alphaA + alphaB) * apex alphaA betaA alphaB betaB :=
    mul_le_mul_of_nonneg_left h hAB.le
  rw [apex_mul_ne hAB.ne'] at hmul
  linarith

theorem volcanoBarrier_eq_branchDown_of_le_apex {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE : ℝ} (h : dE ≤ apex alphaA betaA alphaB betaB) :
    volcanoBarrier alphaA betaA alphaB betaB dE = branchDown alphaB betaB dE := by
  unfold volcanoBarrier
  exact max_eq_right (branchUp_le_branchDown_of_le_apex hAB h)

theorem sabatierZone_eq_optimal_iff (apexD dE : ℝ) :
    sabatierZone apexD dE = SZone.optimal ↔ dE = apexD := by
  unfold sabatierZone
  split_ifs with h1 h2
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩

theorem sabatierZone_eq_tooStrong_iff (apexD dE : ℝ) :
    sabatierZone apexD dE = SZone.tooStrong ↔ dE < apexD := by
  unfold sabatierZone
  split_ifs with h1 h2
  · subst h1
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (lt_irrefl _)⟩
  · exact ⟨fun _ => h2, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h2⟩

theorem sabatierZone_eq_tooWeak_iff (apexD dE : ℝ) :
    sabatierZone apexD dE = SZone.tooWeak ↔ apexD < dE := by
  unfold sabatierZone
  split_ifs with h1 h2
  · subst h1
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (lt_irrefl _)⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h (by linarith)⟩
  · exact ⟨fun _ => lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm h1), fun _ => rfl⟩

theorem nearOptimal_iff_band (apexD dE tol : ℝ) :
    NearOptimal tol apexD dE ↔ apexD - tol ≤ dE ∧ dE ≤ apexD + tol := by
  unfold NearOptimal
  rw [abs_le]
  constructor
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ## S2 — law layer -/

theorem volcanoBarrier_apex_le {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA) (hB : 0 < alphaB)
    (dE : ℝ) :
    volcanoBarrier alphaA betaA alphaB betaB (apex alphaA betaA alphaB betaB)
      ≤ volcanoBarrier alphaA betaA alphaB betaB dE := by
  have hAB : 0 < alphaA + alphaB := by linarith
  have hne : alphaA + alphaB ≠ 0 := hAB.ne'
  rcases le_total dE (apex alphaA betaA alphaB betaB) with h | h
  · rw [volcanoBarrier_eq_branchDown_of_le_apex hAB h, volcanoBarrier_at_apex hne,
      apex_crossing hne]
    unfold branchDown
    nlinarith [hB, h]
  · rw [volcanoBarrier_at_apex hne, volcanoBarrier_eq_branchUp_of_apex_le hAB h]
    unfold branchUp
    nlinarith [hA, h]

theorem volcanoBarrier_eq_apex_iff {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) (dE : ℝ) :
    volcanoBarrier alphaA betaA alphaB betaB dE
        = volcanoBarrier alphaA betaA alphaB betaB (apex alphaA betaA alphaB betaB)
      ↔ dE = apex alphaA betaA alphaB betaB := by
  have hAB : 0 < alphaA + alphaB := by linarith
  have hne : alphaA + alphaB ≠ 0 := hAB.ne'
  constructor
  · intro heq
    rcases lt_trichotomy dE (apex alphaA betaA alphaB betaB) with h | h | h
    · rw [volcanoBarrier_eq_branchDown_of_le_apex hAB h.le, volcanoBarrier_at_apex hne,
        apex_crossing hne] at heq
      unfold branchDown at heq
      nlinarith [hB, h]
    · exact h
    · rw [volcanoBarrier_eq_branchUp_of_apex_le hAB h.le, volcanoBarrier_at_apex hne] at heq
      unfold branchUp at heq
      nlinarith [hA, h]
  · intro h
    rw [h]

theorem volcanoBarrier_strictMono_of_apex_le {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) {dE₁ dE₂ : ℝ} (h₁ : apex alphaA betaA alphaB betaB ≤ dE₁)
    (h₂ : dE₁ < dE₂) :
    volcanoBarrier alphaA betaA alphaB betaB dE₁ < volcanoBarrier alphaA betaA alphaB betaB dE₂ := by
  have hAB : 0 < alphaA + alphaB := by linarith
  rw [volcanoBarrier_eq_branchUp_of_apex_le hAB h₁,
    volcanoBarrier_eq_branchUp_of_apex_le hAB (le_trans h₁ h₂.le)]
  unfold branchUp
  nlinarith [hA, h₂]

theorem volcanoBarrier_strictAnti_of_le_apex {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) {dE₁ dE₂ : ℝ} (h₂ : dE₂ ≤ apex alphaA betaA alphaB betaB) (h₁ : dE₁ < dE₂) :
    volcanoBarrier alphaA betaA alphaB betaB dE₂ < volcanoBarrier alphaA betaA alphaB betaB dE₁ := by
  have hAB : 0 < alphaA + alphaB := by linarith
  rw [volcanoBarrier_eq_branchDown_of_le_apex hAB h₂,
    volcanoBarrier_eq_branchDown_of_le_apex hAB (le_trans h₁.le h₂)]
  unfold branchDown
  nlinarith [hB, h₁]

theorem apexBarrier_eq {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    apexBarrier alphaA betaA alphaB betaB = alphaA * apex alphaA betaA alphaB betaB + betaA := by
  unfold apexBarrier
  rw [volcanoBarrier_at_apex h]
  unfold branchUp
  ring

theorem apexBarrier_eq_branchDown {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    apexBarrier alphaA betaA alphaB betaB
      = branchDown alphaB betaB (apex alphaA betaA alphaB betaB) := by
  unfold apexBarrier
  rw [volcanoBarrier_at_apex h, apex_crossing h]

theorem volcanoBarrier_le_apex_add {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) {tol dE : ℝ} (h : NearOptimal tol (apex alphaA betaA alphaB betaB) dE) :
    volcanoBarrier alphaA betaA alphaB betaB dE
      ≤ apexBarrier alphaA betaA alphaB betaB + max alphaA alphaB * tol := by
  have hAB : 0 < alphaA + alphaB := by linarith
  have hne : alphaA + alphaB ≠ 0 := hAB.ne'
  have hband : |dE - apex alphaA betaA alphaB betaB| ≤ tol := h
  have hlo : apex alphaA betaA alphaB betaB - tol ≤ dE := by
    have := (abs_le.mp hband).1; linarith
  have hhi : dE ≤ apex alphaA betaA alphaB betaB + tol := by
    have := (abs_le.mp hband).2; linarith
  have htol : 0 ≤ tol := by
    have h0 := abs_nonneg (dE - apex alphaA betaA alphaB betaB); linarith
  rcases le_total dE (apex alphaA betaA alphaB betaB) with hcase | hcase
  · rw [volcanoBarrier_eq_branchDown_of_le_apex hAB hcase]
    have hrewrite : branchDown alphaB betaB dE
        = apexBarrier alphaA betaA alphaB betaB
          + alphaB * (apex alphaA betaA alphaB betaB - dE) := by
      rw [apexBarrier_eq_branchDown hne]
      unfold branchDown
      ring
    rw [hrewrite]
    have hbound : alphaB * (apex alphaA betaA alphaB betaB - dE) ≤ max alphaA alphaB * tol := by
      have h1 : apex alphaA betaA alphaB betaB - dE ≤ tol := by linarith
      calc alphaB * (apex alphaA betaA alphaB betaB - dE) ≤ alphaB * tol :=
            mul_le_mul_of_nonneg_left h1 hB.le
        _ ≤ max alphaA alphaB * tol := mul_le_mul_of_nonneg_right (le_max_right _ _) htol
    linarith
  · rw [volcanoBarrier_eq_branchUp_of_apex_le hAB hcase]
    have hrewrite : branchUp alphaA betaA dE
        = apexBarrier alphaA betaA alphaB betaB
          + alphaA * (dE - apex alphaA betaA alphaB betaB) := by
      rw [apexBarrier_eq hne]
      unfold branchUp
      ring
    rw [hrewrite]
    have hbound : alphaA * (dE - apex alphaA betaA alphaB betaB) ≤ max alphaA alphaB * tol := by
      have h1 : dE - apex alphaA betaA alphaB betaB ≤ tol := by linarith
      calc alphaA * (dE - apex alphaA betaA alphaB betaB) ≤ alphaA * tol :=
            mul_le_mul_of_nonneg_left h1 hA.le
        _ ≤ max alphaA alphaB * tol := mul_le_mul_of_nonneg_right (le_max_left _ _) htol
    linarith

theorem volcano_descriptor_of_physical {alphaA betaA alphaB betaB : ℝ}
    (h : SabatierConforms alphaA alphaB) :
    VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
      (apex alphaA betaA alphaB betaB) := by
  refine ⟨fun dE => volcanoBarrier_apex_le h.1 h.2 dE, fun dE hd => ?_⟩
  exact (volcanoBarrier_eq_apex_iff h.1 h.2 dE).mp hd

theorem activity_pos (f : ℝ → ℝ) (kB T dE : ℝ) : 0 < activity f kB T dE :=
  Real.exp_pos _

private theorem exp_neg_div_inj {a b kB T : ℝ} (hkT : kB * T ≠ 0)
    (h : -(a) / (kB * T) = -(b) / (kB * T)) : a = b := by
  have h3 : -(a) / (kB * T) * (kB * T) = -(b) / (kB * T) * (kB * T) := by rw [h]
  rw [div_mul_cancel₀ _ hkT, div_mul_cancel₀ _ hkT] at h3
  linarith

theorem activity_le_apex {f : ℝ → ℝ} {de0 kB T : ℝ} (hkT : 0 < kB * T)
    (h : VolcanoDescriptor f de0) (dE : ℝ) :
    activity f kB T dE ≤ activity f kB T de0 := by
  have hle : f de0 ≤ f dE := h.1 dE
  unfold activity
  rw [Real.exp_le_exp, div_le_div_iff_of_pos_right hkT, neg_le_neg_iff]
  exact hle

theorem activity_eq_apex_iff {f : ℝ → ℝ} {de0 kB T : ℝ} (hkT : 0 < kB * T)
    (h : VolcanoDescriptor f de0) (dE : ℝ) :
    activity f kB T dE = activity f kB T de0 ↔ dE = de0 := by
  have hkT' : kB * T ≠ 0 := hkT.ne'
  constructor
  · intro heq
    have h1 : -(f dE) / (kB * T) = -(f de0) / (kB * T) := Real.exp_injective heq
    exact h.2 dE (exp_neg_div_inj hkT' h1)
  · intro h'
    rw [h']

theorem antiDescriptor_activity_iff {f : ℝ → ℝ} {de0 kB T : ℝ} (hkT : 0 < kB * T) :
    AntiVolcanoDescriptor (activity f kB T) de0 ↔ VolcanoDescriptor f de0 := by
  have hkT' : kB * T ≠ 0 := hkT.ne'
  constructor
  · intro hA
    refine ⟨fun dE => ?_, fun dE heq => ?_⟩
    · have h := hA.1 dE
      unfold activity at h
      rw [Real.exp_le_exp, div_le_div_iff_of_pos_right hkT, neg_le_neg_iff] at h
      exact h
    · have h1 : activity f kB T dE = activity f kB T de0 := by
        unfold activity
        rw [heq]
      exact hA.2 dE h1
  · intro hD
    refine ⟨fun dE => ?_, fun dE heq => ?_⟩
    · have h := hD.1 dE
      unfold activity
      rw [Real.exp_le_exp, div_le_div_iff_of_pos_right hkT, neg_le_neg_iff]
      exact h
    · have h1 : -(f dE) / (kB * T) = -(f de0) / (kB * T) := Real.exp_injective heq
      exact hD.2 dE (exp_neg_div_inj hkT' h1)

theorem activity_ratio (f : ℝ → ℝ) {kB T dE₁ dE₂ : ℝ} (hkT : kB * T ≠ 0) :
    activity f kB T dE₂ / activity f kB T dE₁ = Real.exp ((f dE₁ - f dE₂) / (kB * T)) := by
  unfold activity
  rw [← Real.exp_sub]
  congr 1
  field_simp
  ring

theorem exists_optimal (apexD : ℝ) : ∃ dE : ℝ, Optimal apexD dE := ⟨apexD, rfl⟩

theorem exists_tooWeak (apexD : ℝ) : ∃ dE : ℝ, TooWeak apexD dE :=
  ⟨apexD + 1, by unfold TooWeak; linarith⟩

theorem exists_tooStrong (apexD : ℝ) : ∃ dE : ℝ, TooStrong apexD dE :=
  ⟨apexD - 1, by unfold TooStrong; linarith⟩

theorem exists_nearOptimal {apexD tol : ℝ} (htol : 0 ≤ tol) : ∃ dE : ℝ, NearOptimal tol apexD dE :=
  ⟨apexD, by unfold NearOptimal; simpa using htol⟩

/-! ## S3 — sharp conditions -/

private theorem descriptor_relabel {alphaA betaA alphaB betaB : ℝ} :
    VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
        (apex alphaA betaA alphaB betaB)
      ↔ VolcanoDescriptor (fun dE => volcanoBarrier (-alphaB) betaB (-alphaA) betaA dE)
          (apex (-alphaB) betaB (-alphaA) betaA) := by
  have hf : (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
      = (fun dE => volcanoBarrier (-alphaB) betaB (-alphaA) betaA dE) := by
    funext dE
    exact volcanoBarrier_relabel alphaA betaA alphaB betaB dE
  have ha : apex alphaA betaA alphaB betaB = apex (-alphaB) betaB (-alphaA) betaA :=
    apex_relabel alphaA betaA alphaB betaB
  rw [hf, ha]

private theorem barrier_strictMono_of_slopes_up (alphaA betaA alphaB betaB : ℝ)
    (hA : 0 < alphaA) (hB : alphaB < 0) :
    ∀ x y : ℝ, x < y →
      volcanoBarrier alphaA betaA alphaB betaB x < volcanoBarrier alphaA betaA alphaB betaB y := by
  intro x y hxy
  have h1 : branchUp alphaA betaA x < branchUp alphaA betaA y := by
    unfold branchUp; nlinarith [hA, hxy]
  have h2 : branchDown alphaB betaB x < branchDown alphaB betaB y := by
    unfold branchDown; nlinarith [hB, hxy]
  unfold volcanoBarrier
  exact max_lt_max_aux h1 h2

private theorem notDescriptor_of_slopes_up {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : alphaB < 0) :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
      (apex alphaA betaA alphaB betaB) := by
  intro hD
  have h1 := hD.1 (apex alphaA betaA alphaB betaB - 1)
  have h2 := barrier_strictMono_of_slopes_up alphaA betaA alphaB betaB hA hB _ _
    (by linarith : apex alphaA betaA alphaB betaB - 1 < apex alphaA betaA alphaB betaB)
  linarith

private theorem notDescriptor_of_slopes_down {alphaA betaA alphaB betaB : ℝ} (hA : alphaA < 0)
    (hB : 0 < alphaB) :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
      (apex alphaA betaA alphaB betaB) := by
  intro hD
  have h1 := hD.1 (apex alphaA betaA alphaB betaB + 1)
  have h2 : volcanoBarrier alphaA betaA alphaB betaB (apex alphaA betaA alphaB betaB + 1)
      < volcanoBarrier alphaA betaA alphaB betaB (apex alphaA betaA alphaB betaB) := by
    have hu : branchUp alphaA betaA (apex alphaA betaA alphaB betaB + 1)
        < branchUp alphaA betaA (apex alphaA betaA alphaB betaB) := by
      unfold branchUp; nlinarith [hA]
    have hd : branchDown alphaB betaB (apex alphaA betaA alphaB betaB + 1)
        < branchDown alphaB betaB (apex alphaA betaA alphaB betaB) := by
      unfold branchDown; nlinarith [hB]
    unfold volcanoBarrier
    exact max_lt_max_aux hu hd
  linarith

private theorem notDescriptor_of_zero_slope_A {betaA alphaB betaB : ℝ} (hB : alphaB ≠ 0) :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier 0 betaA alphaB betaB dE)
      (apex 0 betaA alphaB betaB) := by
  intro hD
  have hne : (0:ℝ) + alphaB ≠ 0 := by simpa using hB
  have hcross : branchDown alphaB betaB (apex 0 betaA alphaB betaB) = betaA := by
    have hc := apex_crossing (alphaA := 0) (betaA := betaA) (alphaB := alphaB) (betaB := betaB) hne
    rw [← hc]
    unfold branchUp
    ring
  have hfapex : volcanoBarrier 0 betaA alphaB betaB (apex 0 betaA alphaB betaB) = betaA := by
    unfold volcanoBarrier
    have h1 : branchUp 0 betaA (apex 0 betaA alphaB betaB) = betaA := by
      unfold branchUp; ring
    rw [h1, hcross, max_self]
  rcases lt_trichotomy alphaB 0 with hB' | hB' | hB'
  · have hw : volcanoBarrier 0 betaA alphaB betaB (apex 0 betaA alphaB betaB - 1)
        = volcanoBarrier 0 betaA alphaB betaB (apex 0 betaA alphaB betaB) := by
      rw [hfapex]
      unfold volcanoBarrier
      have h1 : branchUp 0 betaA (apex 0 betaA alphaB betaB - 1) = betaA := by
        unfold branchUp; ring
      have h2 : branchDown alphaB betaB (apex 0 betaA alphaB betaB - 1) = betaA + alphaB := by
        calc branchDown alphaB betaB (apex 0 betaA alphaB betaB - 1)
            = branchDown alphaB betaB (apex 0 betaA alphaB betaB) + alphaB := by
              unfold branchDown; ring
          _ = betaA + alphaB := by rw [hcross]
      rw [h1, h2, max_eq_left]
      linarith
    exact (by linarith : apex 0 betaA alphaB betaB - 1 ≠ apex 0 betaA alphaB betaB) (hD.2 _ hw)
  · exact absurd hB' hB
  · have hw : volcanoBarrier 0 betaA alphaB betaB (apex 0 betaA alphaB betaB + 1)
        = volcanoBarrier 0 betaA alphaB betaB (apex 0 betaA alphaB betaB) := by
      rw [hfapex]
      unfold volcanoBarrier
      have h1 : branchUp 0 betaA (apex 0 betaA alphaB betaB + 1) = betaA := by
        unfold branchUp; ring
      have h2 : branchDown alphaB betaB (apex 0 betaA alphaB betaB + 1) = betaA - alphaB := by
        calc branchDown alphaB betaB (apex 0 betaA alphaB betaB + 1)
            = branchDown alphaB betaB (apex 0 betaA alphaB betaB) - alphaB := by
              unfold branchDown; ring
          _ = betaA - alphaB := by rw [hcross]
      rw [h1, h2, max_eq_left]
      linarith
    exact (by linarith : apex 0 betaA alphaB betaB + 1 ≠ apex 0 betaA alphaB betaB) (hD.2 _ hw)

private theorem notDescriptor_of_zero_slope_B {alphaA betaA betaB : ℝ} (hA : alphaA ≠ 0) :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA 0 betaB dE)
      (apex alphaA betaA 0 betaB) := by
  intro hD
  have hne : alphaA + (0:ℝ) ≠ 0 := by simpa using hA
  have hcross : branchUp alphaA betaA (apex alphaA betaA 0 betaB) = betaB := by
    have hc := apex_crossing (alphaA := alphaA) (betaA := betaA) (alphaB := 0) (betaB := betaB) hne
    rw [hc]
    unfold branchDown
    ring
  have hfapex : volcanoBarrier alphaA betaA 0 betaB (apex alphaA betaA 0 betaB) = betaB := by
    unfold volcanoBarrier
    have h1 : branchDown (0:ℝ) betaB (apex alphaA betaA 0 betaB) = betaB := by
      unfold branchDown; ring
    rw [h1, hcross, max_self]
  rcases lt_trichotomy alphaA 0 with hA' | hA' | hA'
  · have hw : volcanoBarrier alphaA betaA 0 betaB (apex alphaA betaA 0 betaB + 1)
        = volcanoBarrier alphaA betaA 0 betaB (apex alphaA betaA 0 betaB) := by
      rw [hfapex]
      unfold volcanoBarrier
      have h1 : branchDown (0:ℝ) betaB (apex alphaA betaA 0 betaB + 1) = betaB := by
        unfold branchDown; ring
      have h2 : branchUp alphaA betaA (apex alphaA betaA 0 betaB + 1) = betaB + alphaA := by
        calc branchUp alphaA betaA (apex alphaA betaA 0 betaB + 1)
            = branchUp alphaA betaA (apex alphaA betaA 0 betaB) + alphaA := by
              unfold branchUp; ring
          _ = betaB + alphaA := by rw [hcross]
      rw [h1, h2, max_eq_right]
      linarith
    exact (by linarith : apex alphaA betaA 0 betaB + 1 ≠ apex alphaA betaA 0 betaB) (hD.2 _ hw)
  · exact absurd hA' hA
  · have hw : volcanoBarrier alphaA betaA 0 betaB (apex alphaA betaA 0 betaB - 1)
        = volcanoBarrier alphaA betaA 0 betaB (apex alphaA betaA 0 betaB) := by
      rw [hfapex]
      unfold volcanoBarrier
      have h1 : branchDown (0:ℝ) betaB (apex alphaA betaA 0 betaB - 1) = betaB := by
        unfold branchDown; ring
      have h2 : branchUp alphaA betaA (apex alphaA betaA 0 betaB - 1) = betaB - alphaA := by
        calc branchUp alphaA betaA (apex alphaA betaA 0 betaB - 1)
            = branchUp alphaA betaA (apex alphaA betaA 0 betaB) - alphaA := by
              unfold branchUp; ring
          _ = betaB - alphaA := by rw [hcross]
      rw [h1, h2, max_eq_right]
      linarith
    exact (by linarith : apex alphaA betaA 0 betaB - 1 ≠ apex alphaA betaA 0 betaB) (hD.2 _ hw)

private theorem notDescriptor_both_zero {betaA betaB : ℝ} :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier 0 betaA 0 betaB dE) (apex 0 betaA 0 betaB) := by
  intro hD
  have hw : volcanoBarrier 0 betaA 0 betaB 1 = volcanoBarrier 0 betaA 0 betaB (apex 0 betaA 0 betaB) := by
    unfold volcanoBarrier branchUp branchDown apex
    norm_num
  have hne : (1:ℝ) ≠ apex 0 betaA 0 betaB := by
    simp [apex]
  exact hne (hD.2 1 hw)

/-- **The sharp condition of the Sabatier description** — the headline of the theory. -/
theorem volcano_descriptor_iff (alphaA betaA alphaB betaB : ℝ) :
    VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
        (apex alphaA betaA alphaB betaB)
      ↔ 0 < alphaA * alphaB := by
  constructor
  · intro hD
    by_contra hle
    push_neg at hle
    rcases lt_trichotomy alphaA 0 with hA | hA | hA
    · rcases lt_trichotomy alphaB 0 with hB | hB | hB
      · exact absurd (mul_pos_of_neg_of_neg hA hB) (not_lt.mpr hle)
      · subst hB
        exact notDescriptor_of_zero_slope_B (ne_of_lt hA) hD
      · exact notDescriptor_of_slopes_down hA hB hD
    · subst hA
      rcases eq_or_ne alphaB 0 with hB0 | hB0
      · subst hB0
        exact notDescriptor_both_zero hD
      · exact notDescriptor_of_zero_slope_A hB0 hD
    · rcases lt_trichotomy alphaB 0 with hB | hB | hB
      · exact notDescriptor_of_slopes_up hA hB hD
      · subst hB
        exact notDescriptor_of_zero_slope_B (ne_of_gt hA) hD
      · exact absurd (mul_pos hA hB) (not_lt.mpr hle)
  · intro h
    rcases mul_pos_iff.mp h with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact volcano_descriptor_of_physical ⟨hA, hB⟩
    · exact descriptor_relabel.mpr
        (volcano_descriptor_of_physical (alphaA := -alphaB) (betaA := betaB) (alphaB := -alphaA)
          (betaB := betaA) ⟨by linarith, by linarith⟩)

theorem descriptor_fails_of_nonpos_product {alphaA betaA alphaB betaB : ℝ}
    (h : alphaA * alphaB ≤ 0) :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
        (apex alphaA betaA alphaB betaB) := by
  intro hD
  exact absurd ((volcano_descriptor_iff alphaA betaA alphaB betaB).mp hD) (not_lt.mpr h)

theorem volcano_descriptor_iff_labels {alphaA betaA alphaB betaB : ℝ} :
    VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
        (apex alphaA betaA alphaB betaB)
      ↔ (SabatierConforms alphaA alphaB ∨ SabatierConforms (-alphaB) (-alphaA)) := by
  rw [volcano_descriptor_iff]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact Or.inl ⟨hA, hB⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  · intro h
    rcases h with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact mul_pos hA hB
    · exact mul_pos_of_neg_of_neg (by linarith : alphaA < 0) (by linarith : alphaB < 0)

theorem volcano_descriptor_of_neg {alphaA betaA alphaB betaB : ℝ} (hA : alphaA < 0)
    (hB : alphaB < 0) :
    VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
      (apex alphaA betaA alphaB betaB) := by
  exact descriptor_relabel.mpr
    (volcano_descriptor_of_physical (alphaA := -alphaB) (betaA := betaB) (alphaB := -alphaA)
      (betaB := betaA) ⟨by linarith, by linarith⟩)

theorem volcanoActivity_peak_iff {alphaA betaA alphaB betaB kB T : ℝ} (hkT : 0 < kB * T) :
    AntiVolcanoDescriptor (activity (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE) kB T)
        (apex alphaA betaA alphaB betaB)
      ↔ 0 < alphaA * alphaB := by
  rw [antiDescriptor_activity_iff hkT, volcano_descriptor_iff]

theorem flat_witness (dE : ℝ) :
    volcanoBarrier 0 0 0 0 dE = volcanoBarrier 0 0 0 0 (apex 0 0 0 0) := by
  simp [volcanoBarrier, branchUp, branchDown, apex]

theorem not_descriptor_flat :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier 0 0 0 0 dE) (apex 0 0 0 0) := by
  intro hD
  have hw : volcanoBarrier 0 0 0 0 1 = volcanoBarrier 0 0 0 0 (apex 0 0 0 0) := by
    simp [volcanoBarrier, branchUp, branchDown, apex]
  have hne : (1:ℝ) ≠ apex 0 0 0 0 := by
    simp [apex]
  exact hne (hD.2 1 hw)

theorem plateau_witness (dE : ℝ) (h : 0 ≤ dE) :
    volcanoBarrier 0 0 1 0 dE = volcanoBarrier 0 0 1 0 (apex 0 0 1 0) := by
  have hmax : max (0:ℝ) (-dE) = 0 := max_eq_left (by linarith)
  simp only [volcanoBarrier, branchUp, branchDown, apex, zero_mul, one_mul, zero_add, zero_sub,
    sub_zero, div_one, neg_zero]
  rw [hmax, max_self]

theorem not_descriptor_plateau :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier 0 0 1 0 dE) (apex 0 0 1 0) := by
  intro hD
  have hw : volcanoBarrier 0 0 1 0 1 = volcanoBarrier 0 0 1 0 (apex 0 0 1 0) := by
    simp [volcanoBarrier, branchUp, branchDown, apex]
  have hne : (1:ℝ) ≠ apex 0 0 1 0 := by
    simp [apex]
  exact hne (hD.2 1 hw)

theorem antiVolcano_monotone (dE₁ dE₂ : ℝ) (h : dE₁ < dE₂) :
    volcanoBarrier 1 0 (-1) 1 dE₁ < volcanoBarrier 1 0 (-1) 1 dE₂ :=
  barrier_strictMono_of_slopes_up (1:ℝ) (0:ℝ) (-1:ℝ) (1:ℝ) (by norm_num) (by norm_num) dE₁ dE₂ h

theorem not_descriptor_mixedSign :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier 1 0 (-1) 1 dE) (apex 1 0 (-1) 1) :=
  notDescriptor_of_slopes_up (alphaA := 1) (betaA := 0) (alphaB := -1) (betaB := 1)
    (by norm_num) (by norm_num)

/-! ## S5b — instance rows (spot checks) -/

theorem inst_I1_apex : apex (1 / 2) (1 / 2) (1 / 2) (1 / 2) = 0 := by
  unfold apex
  norm_num

theorem inst_I1_apexBarrier : apexBarrier (1 / 2) (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  unfold apexBarrier volcanoBarrier branchUp branchDown apex
  norm_num

theorem inst_I1_barrier_tooStrong :
    volcanoBarrier (1 / 2) (1 / 2) (1 / 2) (1 / 2) (-(1 / 2)) = 3 / 4 := by
  unfold volcanoBarrier branchUp branchDown
  norm_num

theorem inst_I2_apex : apex (1 / 2) 0 1 1 = 2 / 3 := by
  unfold apex
  norm_num

theorem inst_I2_barrier_tooWeak : volcanoBarrier (1 / 2) 0 1 1 0 = 1 := by
  unfold volcanoBarrier branchUp branchDown
  norm_num

theorem inst_I3_barrier_tooStrong : volcanoBarrier (1 / 2) 0 1 1 (-(1 / 3)) = 4 / 3 := by
  unfold volcanoBarrier branchUp branchDown
  norm_num

/-! ## S4 — cross-theory spot checks -/

theorem apexPar_self {lam : ℝ} (_h : 0 < lam) : apexPar lam lam = 0 := by
  unfold apexPar
  rw [sub_self, zero_div]

theorem linearVolcano_eq_bepTangent (lam1 lam2 dE : ℝ) :
    volcanoBarrier (1 / 2) (lam1 / 4) (1 / 2) (lam2 / 4) dE
      = max (BEP.bepLine lam1 (-dE)) (BEP.bepLine lam2 dE) := by
  unfold volcanoBarrier branchUp branchDown BEP.bepLine
  have h1 : (1:ℝ) / 2 * dE + lam1 / 4 = lam1 / 4 - -dE / 2 := by ring
  have h2 : lam2 / 4 - 1 / 2 * dE = lam2 / 4 - dE / 2 := by ring
  rw [h1, h2]

theorem bepLine_le_eact {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    BEP.bepLine lam x ≤ BEP.eact lam x := by
  have h : BEP.eact lam x - BEP.bepLine lam x = x ^ 2 / (4 * lam) := by
    unfold BEP.eact BEP.bepLine
    field_simp
    ring
  have hnonneg : 0 ≤ x ^ 2 / (4 * lam) := by positivity
  linarith


/-! ## Sprint-0 witnesses for the deleted false rows (plan §3.1, F1 of verifier run 1) -/

/-- Kernel witness for the deleted `apex_comm`: the naive label swap
(`(alphaA,betaA,alphaB,betaB) ↦ (alphaB,betaB,alphaA,betaA)`) does NOT preserve the apex — it
negates it, because the second branch enters with slope `-alphaB`. -/
theorem apex_naive_swap_values : apex 1 0 1 2 = 1 ∧ apex 1 2 1 0 = -1 := by
  constructor <;> (unfold apex; norm_num)

/-- The two values differ, so no "commutativity" of the naive swap can hold. -/
theorem apex_naive_swap_ne : apex 1 0 1 2 ≠ apex 1 2 1 0 := by
  unfold apex
  norm_num

/-- Kernel witness for the scope of `antiDescriptor_activity_iff` (the corrected replacement of the
false `activity_descriptor_iff`): at `kB * T = 0` the activity is the constant `1`, which has no
unique maximizer, while `fun dE => dE^2` is a volcano at `0` — hence the `0 < kB * T` premise of the
delivered statement is necessary. -/
theorem activity_zero_kT_witness :
    VolcanoDescriptor (fun dE => dE ^ 2) 0
      ∧ ¬ AntiVolcanoDescriptor (activity (fun dE => dE ^ 2) 0 0) 0 := by
  constructor
  · constructor
    · intro dE; dsimp only; nlinarith [sq_nonneg dE]
    · intro dE h; dsimp only at h; nlinarith [sq_nonneg dE, h]
  · intro h
    have h1 := h.2 1
    have h2 : activity (fun dE => dE ^ 2) 0 0 1 = activity (fun dE => dE ^ 2) 0 0 0 := by
      unfold activity
      norm_num
    exact absurd (h1 h2) (by norm_num)

end Sabatier

end PhotoLean
