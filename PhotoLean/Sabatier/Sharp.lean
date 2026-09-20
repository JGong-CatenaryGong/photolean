/-
PhotoLean.Sabatier.Sharp — S3, the exact (sharp) conditions of the Sabatier theory (the volcano plot).

The sharpness layer answers the question the S2 law layer leaves open: the physical orientation of
the two Brønsted–Evans–Polanyi slopes (`SabatierConforms`, i.e. `0 < alphaA ∧ 0 < alphaB`) is
SUFFICIENT for the volcano shape (`volcano_descriptor_of_physical`, S2); here it is proved to be
necessary as well, up to the interchange of the two branch labels. The two-branch barrier profile is
a volcano at its apex iff `0 < alphaA * alphaB`, i.e. iff the two BEP slopes have the same nonzero
sign — the two branches penalize opposite ends of the descriptor axis (plan §6). The product
condition is the label-free form of that statement: `0 < alphaA * alphaB` covers both the physical
orientation and its relabelled mirror, and the label-swap identities of the apex and of the profile
(`apex_relabel`, `volcanoBarrier_relabel`, S1) are what make the two readings the same volcano
(`descriptor_relabel`, `volcano_descriptor_of_neg`).

The degenerate and mixed-sign rows exhibit the failure modes explicitly: two zero slopes give a
constant profile whose claimed minimizer is not unique (`flat_witness`, `not_descriptor_flat`); one
zero slope turns the apex into a half-line plateau (`plateau_witness`, `not_descriptor_plateau`); two
slopes of opposite sign give a barrier that is strictly increasing in the descriptor, so the volcano
has no interior optimum at all (`antiVolcano_monotone`, `not_descriptor_mixedSign`).

The volcano plot itself is the activity row: the Arrhenius activity `exp (-Ea / (kB * T))` has its
unique global maximum at the apex iff `0 < alphaA * alphaB` (`volcanoActivity_peak_iff`), so the peak
of the plotted activity and the pass of the barrier are sharp under exactly the same condition.

Model premises and honesty table: plan §12. Every physical premise (the sign conditions on the
slopes, the thermal energy hypothesis `0 < kB * T`) is an explicit hypothesis of the statements
below, and nothing is hidden in a definition. The identification "effective barrier = maximum of the
two branch barriers" is a declared modelling premise of the theory (plan §12), not a theorem of it.

There is no unproved placeholder and no custom axiom anywhere in this file.

Statement authority: every declaration below matches
`theories/Sabatier/probes/sabatier-statement-skeleton.lean` §S3 word for word (plan §3). Sprint-0
kernel evidence for these statement forms: `theories/Sabatier/probes/sabatier-risk-probe.lean` §S3.
This module imports `PhotoLean.Sabatier.Basic` only: the S2 rows it needs are re-proved here as
private auxiliaries, so this file carries no dependency on a concurrently delivered module.
-/
import PhotoLean.Sabatier.Basic

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Sabatier

/-! ## S3 — sharp conditions (`PhotoLean/Sabatier/Sharp.lean`) -/

/-- Auxiliary (plan §6): the pointwise maximum of two strictly smaller values is strictly smaller.
The strictness engine of the mixed-sign monotonicity rows below. -/
private theorem max_lt_max_aux {a b c d : ℝ} (h1 : a < c) (h2 : b < d) : max a b < max c d := by
  rw [max_lt_iff]
  exact ⟨lt_of_lt_of_le h1 (le_max_left c d), lt_of_lt_of_le h2 (le_max_right c d)⟩

/-- Auxiliary (plan §6): multiplying the apex by its denominator cancels the division. `Basic.lean`
keeps its own copy private, so the identity is re-proved here for the sharpness layer. -/
private theorem apex_mul_ne {alphaA betaA alphaB betaB : ℝ} (h : alphaA + alphaB ≠ 0) :
    (alphaA + alphaB) * apex alphaA betaA alphaB betaB = betaB - betaA := by
  rw [apex, mul_div_cancel₀ _ h]

/-- Auxiliary (plan §6, S2 row of the law layer): in the physical orientation the apex is a global
minimizer of the effective barrier. Re-proved here so that S3 depends on `Basic` only. -/
private theorem barrier_apex_le_aux {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) (dE : ℝ) :
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

/-- Auxiliary (plan §6, S2 row of the law layer): in the physical orientation the apex is the
*unique* global minimizer, i.e. only the apex attains the minimal value. -/
private theorem barrier_eq_apex_iff_aux {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
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

/-- Auxiliary (plan §6, S2 row of the law layer): in the physical orientation the two-branch
profile is a volcano with apex `apex`. -/
private theorem descriptor_of_physical_aux {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : 0 < alphaB) :
    VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
      (apex alphaA betaA alphaB betaB) :=
  ⟨fun dE => barrier_apex_le_aux hA hB dE,
    fun dE hd => (barrier_eq_apex_iff_aux hA hB dE).mp hd⟩

/-- Auxiliary (plan §6): the label-swap identity of the apex and of the profile transported to the
volcano predicate. It is the bridge that makes `0 < alphaA * alphaB` (a label-free condition) the
exact sharp condition: the relabelled model has the same profile and the same apex. -/
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

/-- Auxiliary (plan §6): with `alphaA > 0 > alphaB` BOTH branches are strictly increasing in the
descriptor, hence so is their maximum: the mixed-sign model has no interior optimum and its barrier
is a monotone function of `dE`. -/
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

/-- Auxiliary (plan §6): the mixed-sign model (`alphaA > 0 > alphaB`, hence `alphaA * alphaB < 0`)
is not a volcano — the barrier strictly increases in `dE`, so no point can be a global minimizer. -/
private theorem notDescriptor_of_slopes_up {alphaA betaA alphaB betaB : ℝ} (hA : 0 < alphaA)
    (hB : alphaB < 0) :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
      (apex alphaA betaA alphaB betaB) := by
  intro hD
  have h1 := hD.1 (apex alphaA betaA alphaB betaB - 1)
  have h2 := barrier_strictMono_of_slopes_up alphaA betaA alphaB betaB hA hB _ _
    (by linarith : apex alphaA betaA alphaB betaB - 1 < apex alphaA betaA alphaB betaB)
  linarith

/-- Auxiliary (plan §6): the mirror mixed-sign model (`alphaA < 0 < alphaB`) is not a volcano
either — both branches strictly decrease in `dE`. -/
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

/-- Auxiliary (plan §6): a zero slope in the FIRST slot (with a nonzero second slope) turns the
apex into the endpoint of a half-line of minimizers: the profile is constant on the side of the
apex that the insensitive branch controls, so the minimizer is not unique. -/
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

/-- Auxiliary (plan §6): the mirror of `notDescriptor_of_zero_slope_A` — a zero slope in the SECOND
slot (with a nonzero first slope) again destroys uniqueness of the minimizer. -/
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

/-- Auxiliary (plan §6): two zero slopes give a constant profile, so no claimed apex can be the
unique minimizer — the totally degenerate model is never a volcano. -/
private theorem notDescriptor_both_zero {betaA betaB : ℝ} :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier 0 betaA 0 betaB dE) (apex 0 betaA 0 betaB) := by
  intro hD
  have hw : volcanoBarrier 0 betaA 0 betaB 1
      = volcanoBarrier 0 betaA 0 betaB (apex 0 betaA 0 betaB) := by
    unfold volcanoBarrier branchUp branchDown apex
    norm_num
  have hne : (1:ℝ) ≠ apex 0 betaA 0 betaB := by
    simp [apex]
  exact hne (hD.2 1 hw)

/-- **The sharp condition of the Sabatier description** (plan §6) — the headline of the theory. The
two-branch barrier profile is a volcano at its apex (unique global minimizer) **iff** the two BEP
slopes have the same nonzero sign — i.e. iff the two branches penalize opposite ends of the
descriptor axis. -/
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
    · exact descriptor_of_physical_aux hA hB
    · exact descriptor_relabel.mpr
        (descriptor_of_physical_aux (alphaA := -alphaB) (betaA := betaB) (alphaB := -alphaA)
          (betaB := betaA) (by linarith) (by linarith))

/-- Contrapositive form of the sharp condition (plan §6): a nonpositive slope product — zero
included — rules the volcano out, so the physical orientation cannot be relaxed to weak
inequalities. -/
theorem descriptor_fails_of_nonpos_product {alphaA betaA alphaB betaB : ℝ}
    (h : alphaA * alphaB ≤ 0) :
    ¬ VolcanoDescriptor (fun dE => volcanoBarrier alphaA betaA alphaB betaB dE)
        (apex alphaA betaA alphaB betaB) := by
  intro hD
  exact absurd ((volcano_descriptor_iff alphaA betaA alphaB betaB).mp hD) (not_lt.mpr h)

/-- The sharp condition in the instance layer's vocabulary (plan §6): the volcano holds iff the
series conforms to the physical orientation, up to the interchange of the two branch labels. -/
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

end Sabatier

end PhotoLean
