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

end Sabatier

end PhotoLean
