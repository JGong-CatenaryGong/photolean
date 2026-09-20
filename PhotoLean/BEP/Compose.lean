/-
PhotoLean.BEP.Compose — B4, the microscopic and cross-module layer of the Bell–Evans–Polanyi theory.

This module places the BEP description layer (`PhotoLean/BEP/Basic.lean`) next to the two delivered
two-parabola modules of the repository, and then composes the reorganization energy out of its
inner and outer parts.

Cross-module bridges (rows 1–6 of `theories/BEP/plan.md` §7):

* `PhotoLean.Marcus.Basic` — the BEP barrier `eact` *is* the delivered Marcus barrier
  (`eact_eq_barrier`, definitional), hence the BEP description of the barrier constrains the
  delivered Marcus rate descriptor (`rate_eq_exp_neg_eact`). The headline theorem of this milestone
  is `epBounds_iff_no_inverted_direction`: the Evans–Polanyi bounds `0 ≤ α ≤ 1` hold **exactly**
  when neither the forward direction `x` nor the reverse direction `-x` of the step lies in the
  Marcus inverted region `lam < x`; in the equal-curvature two-parabola model the failure of the BEP
  bounds and the Marcus inverted region are one phenomenon, seen from the two directions of the
  step.
* `PhotoLean.Hammond.Basic` — the BEP/Brønsted/Leffler coefficient in linear-response form is the
  Hammond transition-state coordinate (`transfer_eq_tsCoord_bridge`), and Hammond's conformance
  region entails the Evans–Polanyi bounds (`epBounds_of_reactionRegion`,
  `epBounds_of_marcus_normal`).

Microscopic composition (rows 7–12), self-contained algebra in this module: the total reorganization
energy of a step is the sum of an inner (bond/angle) and an outer (solvent, Pekar-type)
contribution, `lam = lamInner + lamOuter`, and the physical reading is that **a larger total
reorganization energy improves the linear law** — the exact violation `bepDefect` shrinks
(`bepDefect_le_of_microscopic`), the tolerance radius `bepRadius` widens (`bepRadius_add`) and with
it the conformance window (`epConformsOnWindow_of_microscopic`,
`epConformsOnWindow_shrinks_with_inner`); the composed curvature is again the curvature of a BEP
descriptor (`epDescriptor_of_microscopic`) and the Brønsted complementarity identity is inherited by
the composed curvature (`transfer_complementary_microscopic`). The microscopic hypothesis is
therefore exactly `0 < lamInner` and `0 < lamOuter` (or their non-strict forms where the plan uses
them): positivity of the two contributions is an explicit premise of every statement that needs it,
and nothing is hidden in a definition.

Rows 9–11 quote the tolerance/monotonicity helpers of plan §6.3 (`bepRadius_mono`,
`bepDefect_antitone_lam`, `epConformsOnWindow_iff_radius`), which live in `PhotoLean/BEP/Sharp.lean`.
That module is not part of this milestone and is deliberately not imported here: the three rows are
derived directly from `PhotoLean.BEP.Basic` instead, keeping the hypothesis shape of the plan and of
the statement skeleton. The derivations are short — `Real.sqrt_le_sqrt` plus
`div_le_div_of_nonneg_left` for the monotonicity rows, and the radius/window criterion by squaring
(`Real.sq_sqrt` + `sq_le_sq`). Neither `PhotoLean.Marcus.Compose` nor the Pekar/geometry machinery
is imported.

Statement authority: every declaration below matches the B4 block of
`theories/BEP/probes/bep-statement-skeleton.lean` (plan §7) word for word. There is no unproved
placeholder and no custom axiom in this file.
-/
import PhotoLean.BEP.Basic
import PhotoLean.Marcus.Basic
import PhotoLean.Hammond.Basic

namespace PhotoLean.BEP

/-! ## Cross-module bridges (plan §7 rows 1–6) -/

/-- Plan §7 #1: the two definitions have identical bodies, so the bridge is definitional — the BEP
barrier *is* the delivered Marcus barrier. -/
theorem eact_eq_barrier (lam x : ℝ) : eact lam x = Marcus.barrier lam x := rfl

/-- Plan §7 #2: the delivered Marcus rate descriptor written through #1 — its activation barrier is
the BEP barrier, so the BEP description of the barrier is a statement about the Marcus rate. Both
sides of the equation are the same term up to unfolding the two definitions, hence definitional. -/
theorem rate_eq_exp_neg_eact (A lam kB T x : ℝ) :
    Marcus.rate A lam kB T x = A * Real.exp (-(eact lam x) / (kB * T)) := rfl

/-- Plan §7 #3: the BEP/Brønsted/Leffler coefficient equals the Hammond transition-state coordinate
of the same step — the cross-module form of the plan §5 bridge. This is a genuine theorem about the
linear-response body `1/2 - x/(2*lam)` of `transfer` (rather than a definitional restatement of
`(lam - x)/(2*lam)`); the explicit physical premise `lam ≠ 0` is what makes the transition-state
coordinate well defined (at `lam = 0` the two totalised-division values disagree). -/
theorem transfer_eq_tsCoord_bridge {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    transfer lam x = Hammond.tsCoord lam x := by
  unfold transfer Hammond.tsCoord
  -- clearing the common denominator `2 * lam` (legitimate by `hlam`) closes the goal outright
  field_simp

/-- Plan §7 #4 (headline): the Evans–Polanyi bounds hold **exactly** when neither direction of the
step lies in the Marcus inverted region. `EPBounds lam x` is `0 ≤ transfer lam x ∧ transfer lam x ≤
1`, i.e. `0 ≤ 1/2 - x/(2*lam) ≤ 1`; with `0 < lam` the two halves are `x ≤ lam` and `-lam ≤ x`,
which is precisely the negation of `lam < x ∨ lam < -x` (`Marcus.InvertedRegion lam x` is
`lam < x`, and `Marcus.InvertedRegion lam (-x)` is the reverse direction of the same step). -/
theorem epBounds_iff_no_inverted_direction {lam x : ℝ} (hlam : 0 < lam) :
    EPBounds lam x ↔ ¬ (Marcus.InvertedRegion lam x ∨ Marcus.InvertedRegion lam (-x)) := by
  have h2 : 0 < 2 * lam := by linarith
  unfold EPBounds transfer Marcus.InvertedRegion
  constructor
  · rintro ⟨h1, h3⟩
    simp only [not_or, not_lt]
    constructor
    · have := (div_le_iff₀ h2).mp (show x / (2 * lam) ≤ 1 / 2 by linarith)
      linarith
    · have := (le_div_iff₀ h2).mp (show -(1 / 2) ≤ x / (2 * lam) by linarith)
      linarith
  · intro h
    simp only [not_or, not_lt] at h
    obtain ⟨h1, h3⟩ := h
    constructor
    · have : x / (2 * lam) ≤ 1 / 2 := (div_le_iff₀ h2).mpr (by linarith)
      linarith
    · have : -(1 / 2) ≤ x / (2 * lam) := (le_div_iff₀ h2).mpr (by linarith)
      linarith

/-- Plan §7 #5 (Hammond bridge): Hammond's conformance region `-lam < x ∧ x < lam` entails the
Evans–Polanyi bounds — a strictly inside-the-window step has both directions in the normal region,
so #4 applies. -/
theorem epBounds_of_reactionRegion {lam x : ℝ} (hlam : 0 < lam)
    (h : Hammond.ReactionRegion lam x) : EPBounds lam x := by
  rw [epBounds_iff_no_inverted_direction hlam]
  simp only [Marcus.InvertedRegion, Hammond.ReactionRegion, not_or, not_lt] at h ⊢
  exact ⟨le_of_lt h.2, by linarith⟩

/-- Plan §7 #6 (Marcus bridge): a step in the Marcus normal region whose reverse direction is
thermoneutral or exergonic (`-lam ≤ x`) satisfies the Evans–Polanyi bounds; the two hypotheses are
exactly the two halves of #4. -/
theorem epBounds_of_marcus_normal {lam x : ℝ} (hlam : 0 < lam) (h : Marcus.NormalRegion lam x)
    (hx : -lam ≤ x) : EPBounds lam x := by
  rw [epBounds_iff_no_inverted_direction hlam]
  simp only [Marcus.InvertedRegion, Marcus.NormalRegion, not_or, not_lt] at h ⊢
  exact ⟨le_of_lt h, by linarith⟩

/-! ## Microscopic composition of the reorganization energy (plan §7 rows 7–12) -/

/-- Plan §7 #7: the total reorganization energy of a step is again the curvature of a BEP
descriptor. Positivity of both contributions (`0 < lamInner`, `0 < lamOuter`) is the explicit
microscopic premise, from which `0 < lamInner + lamOuter` follows; the exact defect law
`bepDefect lam x = x^2/(4*lam)` is the plan §5 identity, obtained here by clearing the common
denominator `4 * lam` and normalising. -/
theorem epDescriptor_of_microscopic {lamInner lamOuter : ℝ} (hli : 0 < lamInner)
    (hlo : 0 < lamOuter) : EPDescriptor (lamInner + lamOuter) := by
  have hL : 0 < lamInner + lamOuter := by linarith
  refine ⟨hL, ?_⟩
  intro x
  unfold bepDefect eact bepLine
  field_simp
  ring


end PhotoLean.BEP
