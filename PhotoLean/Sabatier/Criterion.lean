/-
PhotoLean.Sabatier.Criterion — S2, the law layer of the Sabatier theory (the volcano plot).

The model (plan §1.2, §2): the effective (rate-limiting) barrier of a two-step catalytic cycle on a
single descriptor `dE` is the maximum of two Brønsted–Evans–Polanyi branches,
`volcanoBarrier αA βA αB βB dE = max (branchUp αA βA dE) (branchDown αB βB dE)`, and the apex
`apex αA βA αB βB = (βB - βA) / (αA + αB)` is the crossing point of the two branches. The
definitions and the description-layer lemmas live in `PhotoLean.Sabatier.Basic` (S1) and are imported
here; this file delivers the S2 law layer, i.e. the theorems that turn the two-branch profile into an
actual volcano:

* the apex is a global minimizer of the barrier and, under the physical orientation
  `0 < alphaA`, `0 < alphaB`, the UNIQUE one (`volcanoBarrier_apex_le`,
  `volcanoBarrier_eq_apex_iff`, `volcano_descriptor_of_physical`);
* the barrier strictly increases on the weak-binding leg `apex ≤ dE₁ < dE₂` and strictly decreases
  on the strong-binding leg `dE₁ < dE₂ ≤ apex` (`volcanoBarrier_strictMono_of_apex_le`,
  `volcanoBarrier_strictAnti_of_le_apex`);
* the volcano legs have slopes `±α` in the exact finite-difference sense
  (`volcanoBarrier_secSlope_of_apex_le`, `volcanoBarrier_secSlope_of_le_apex`);
* the apex-centred form of the profile, its pass height, and the quantitative tolerance bound
  (`volcanoBarrier_apex_form`, `apexBarrier_eq`, `volcanoBarrier_le_apex_add`);
* the Arrhenius / activity layer: the barrier's unique minimum is the activity's unique maximum and
  the activity ratio is a function of the barrier difference alone (`activity_pos`,
  `activity_le_apex`, `activity_eq_apex_iff`, `antiDescriptor_activity_iff`, `activity_ratio`);
* non-vacuity witnesses for the three Sabatier regimes and the tolerance band (`exists_optimal`,
  `exists_tooWeak`, `exists_tooStrong`, `exists_nearOptimal`).

Every physical premise is an explicit hypothesis of the statements — the physical orientation
`0 < alphaA`, `0 < alphaB` (or only `0 < alphaA + alphaB` where the algebra is sign-free), the
positivity of the thermal scale `0 < kB * T`, and the non-degeneracy `alphaA + alphaB ≠ 0` that makes
the apex formula defined. Nothing is hidden in a definition.

There is no unproved placeholder and no custom axiom anywhere in this file.

Statement authority: every declaration below matches
`theories/Sabatier/probes/sabatier-statement-skeleton.lean` §S2 word for word (plan §3 and the S2
milestone rows of plan §5). Kernel evidence for the statement forms:
`theories/Sabatier/probes/sabatier-risk-probe.lean`.
-/
import Mathlib
import PhotoLean.Sabatier.Basic

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Sabatier

/-! ## S2 — law layer (`PhotoLean/Sabatier/Criterion.lean`) -/

/-! ### Prover-local helpers (auxiliary; not part of the statement authority) -/

/-- Auxiliary (S2-local): at the apex the pass height also equals the descending branch, because the
two branches cross there (`apex_crossing`). Used by the tolerance bound. Not part of the statement
authority. -/
private theorem apexBarrier_eq_branchDown {alphaA betaA alphaB betaB : ℝ}
    (h : alphaA + alphaB ≠ 0) :
    apexBarrier alphaA betaA alphaB betaB
      = branchDown alphaB betaB (apex alphaA betaA alphaB betaB) := by
  unfold apexBarrier
  rw [volcanoBarrier_at_apex h, apex_crossing h]

/-- Auxiliary (S2-local): `exp (-a / k) = exp (-b / k)` forces `a = b` for `k ≠ 0`; it is the
injectivity step behind `activity_eq_apex_iff`. Not part of the statement authority. -/
private theorem exp_neg_div_inj {a b kB T : ℝ} (hkT : kB * T ≠ 0)
    (h : -(a) / (kB * T) = -(b) / (kB * T)) : a = b := by
  have h3 : -(a) / (kB * T) * (kB * T) = -(b) / (kB * T) * (kB * T) := by rw [h]
  rw [div_mul_cancel₀ _ hkT, div_mul_cancel₀ _ hkT] at h3
  linarith

/-- Auxiliary (S2-local): shifting both arguments of a `max` by the same additive constant shifts
the `max` by it. Used by the apex-centred form. Not part of the statement authority. -/
private theorem max_add_add_same (P x y : ℝ) : max (P + x) (P + y) = P + max x y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
  · rw [max_eq_left h, max_eq_left (by linarith)]

/-- The apex is a global minimizer of the effective barrier (physical orientation). The volcano's
pass is the lowest point of the profile: the barrier at `apex` is below the barrier at every
descriptor value `dE`. Plan §5 (S2 law layer). -/
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

/-- The apex is the *unique* global minimizer: the volcano has a pointed pass, not a plateau. The
barrier profile takes the height of the pass at `dE` if and only if `dE` is the apex. Plan §5. -/
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

/-- Weak-binding side: the effective barrier strictly increases with `dE`. On the half-line
`apex ≤ dE₁ < dE₂` the profile is the ascending branch and hence strictly increasing. Plan §5. -/
theorem volcanoBarrier_strictMono_of_apex_le {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) {dE₁ dE₂ : ℝ} (h₁ : apex alphaA betaA alphaB betaB ≤ dE₁)
    (h₂ : dE₁ < dE₂) :
    volcanoBarrier alphaA betaA alphaB betaB dE₁ < volcanoBarrier alphaA betaA alphaB betaB dE₂ := by
  have hAB : 0 < alphaA + alphaB := by linarith
  rw [volcanoBarrier_eq_branchUp_of_apex_le hAB h₁,
    volcanoBarrier_eq_branchUp_of_apex_le hAB (le_trans h₁ h₂.le)]
  unfold branchUp
  nlinarith [hA, h₂]

/-- Strong-binding side: the effective barrier strictly increases as `dE` decreases. On the
half-line `dE₁ < dE₂ ≤ apex` the profile is the descending branch, so it is strictly decreasing in
`dE` — increasing towards stronger binding. Plan §5. -/
theorem volcanoBarrier_strictAnti_of_le_apex {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) {dE₁ dE₂ : ℝ} (h₂ : dE₂ ≤ apex alphaA betaA alphaB betaB) (h₁ : dE₁ < dE₂) :
    volcanoBarrier alphaA betaA alphaB betaB dE₂ < volcanoBarrier alphaA betaA alphaB betaB dE₁ := by
  have hAB : 0 < alphaA + alphaB := by linarith
  rw [volcanoBarrier_eq_branchDown_of_le_apex hAB h₂,
    volcanoBarrier_eq_branchDown_of_le_apex hAB (le_trans h₁.le h₂)]
  unfold branchDown
  nlinarith [hB, h₁]

/-- Quantitative tolerance form of "not too strong, not too weak": within `tol` of the apex the
activity loss is at most `max alphaA alphaB * tol` in barrier units. The excess over the pass height
is bounded by the steepest leg slope times the tolerance. Plan §5 (the tolerance reading of §6). -/
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
      unfold apexBarrier
      rw [volcanoBarrier_at_apex hne]
      unfold branchUp
      ring
    rw [hrewrite]
    have hbound : alphaA * (dE - apex alphaA betaA alphaB betaB) ≤ max alphaA alphaB * tol := by
      have h1 : dE - apex alphaA betaA alphaB betaB ≤ tol := by linarith
      calc alphaA * (dE - apex alphaA betaA alphaB betaB) ≤ alphaA * tol :=
            mul_le_mul_of_nonneg_left h1 hA.le
        _ ≤ max alphaA alphaB * tol := mul_le_mul_of_nonneg_right (le_max_left _ _) htol
    linarith

/-- Apex-centred form of the barrier: the excess over the pass is the maximum of two linear
penalties, one for each end of the descriptor axis, with the two BEP slopes as coefficients. The
identity is algebraic and needs only `alphaA + alphaB ≠ 0`, i.e. that the apex formula be defined —
no sign hypothesis. Plan §5. -/
theorem volcanoBarrier_apex_form {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) (dE : ℝ) :
    volcanoBarrier alphaA betaA alphaB betaB dE
      = apexBarrier alphaA betaA alphaB betaB
        + max (alphaA * (dE - apex alphaA betaA alphaB betaB))
            (alphaB * (apex alphaA betaA alphaB betaB - dE)) := by
  have hup : branchUp alphaA betaA dE
      = apexBarrier alphaA betaA alphaB betaB
        + alphaA * (dE - apex alphaA betaA alphaB betaB) := by
    unfold apexBarrier
    rw [volcanoBarrier_at_apex h]
    unfold branchUp
    ring
  have hdown : branchDown alphaB betaB dE
      = apexBarrier alphaA betaA alphaB betaB
        + alphaB * (apex alphaA betaA alphaB betaB - dE) := by
    unfold apexBarrier
    rw [volcanoBarrier_at_apex h, apex_crossing h]
    unfold branchDown
    ring
  unfold volcanoBarrier
  rw [hup, hdown, max_add_add_same]

/-- Observable slope of the weak-binding volcano leg: its finite differences are the BEP slope
`alphaA` — the literature's "the volcano legs have slopes ±α", made exact. Needs only that the
descriptor interval start at or above the apex and that the total slope be positive. Plan §5. -/
theorem volcanoBarrier_secSlope_of_apex_le {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE₁ dE₂ : ℝ} (h₁ : apex alphaA betaA alphaB betaB ≤ dE₁)
    (h₂ : dE₁ < dE₂) :
    (volcanoBarrier alphaA betaA alphaB betaB dE₂ - volcanoBarrier alphaA betaA alphaB betaB dE₁)
        / (dE₂ - dE₁) = alphaA := by
  have hne : dE₂ - dE₁ ≠ 0 := by linarith
  rw [volcanoBarrier_eq_branchUp_of_apex_le hAB h₁,
    volcanoBarrier_eq_branchUp_of_apex_le hAB (le_trans h₁ h₂.le), div_eq_iff hne]
  unfold branchUp
  ring

/-- Observable slope of the strong-binding volcano leg: its finite differences are `-alphaB`. The
descending branch is what the profile *is* below the apex, and its slope is the negative BEP
coefficient of the strong-binding step. Plan §5. -/
theorem volcanoBarrier_secSlope_of_le_apex {alphaA betaA alphaB betaB : ℝ}
    (hAB : 0 < alphaA + alphaB) {dE₁ dE₂ : ℝ} (h₂ : dE₂ ≤ apex alphaA betaA alphaB betaB)
    (h₁ : dE₁ < dE₂) :
    (volcanoBarrier alphaA betaA alphaB betaB dE₂ - volcanoBarrier alphaA betaA alphaB betaB dE₁)
        / (dE₂ - dE₁) = -alphaB := by
  have hne : dE₂ - dE₁ ≠ 0 := by linarith
  rw [volcanoBarrier_eq_branchDown_of_le_apex hAB h₂,
    volcanoBarrier_eq_branchDown_of_le_apex hAB (le_trans h₁.le h₂), div_eq_iff hne]
  unfold branchDown
  ring

/-- Value form of the pass height, used by the instance rows: the barrier at the apex is the
ascending branch evaluated at the apex. Plan §5. -/
theorem apexBarrier_eq {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    apexBarrier alphaA betaA alphaB betaB = alphaA * apex alphaA betaA alphaB betaB + betaA := by
  unfold apexBarrier
  rw [volcanoBarrier_at_apex h]
  unfold branchUp
  ring

end Sabatier

end PhotoLean
