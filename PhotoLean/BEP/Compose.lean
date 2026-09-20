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

Post-verification addition (2026-09-20, prover_b): the B4 block's AUX declaration
`secSlope_eq_lefflerSecant` — absent from the delivered B4 set — is added at the end of the file, so
this file's hash differs from the snapshot the independent B4 verifier PASSed; the twelve plan §7
rows are untouched by the addition.
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

/-- Plan §7 #8: adding outer reorganization energy shrinks the exact violation of the BEP line —
`bepDefect` is antitone in `lam` away from thermoneutrality (`x ≠ 0`). Derived here directly from
the defect identity `x^2/(4*lam)` and `div_le_div_of_nonneg_left`, because the plan §6.3 helper
`bepDefect_antitone_lam` (`PhotoLean/BEP/Sharp.lean`) is not part of this milestone. -/
theorem bepDefect_le_of_microscopic {lamInner lamOuter x : ℝ} (hli : 0 < lamInner)
    (hlo : 0 < lamOuter) (hx : x ≠ 0) :
    bepDefect (lamInner + lamOuter) x ≤ bepDefect lamInner x := by
  have hL : 0 < lamInner + lamOuter := by linarith
  have key : ∀ L : ℝ, L ≠ 0 → bepDefect L x = x ^ 2 / (4 * L) := by
    intro L hL0
    unfold bepDefect eact bepLine
    field_simp
    ring
  rw [key (lamInner + lamOuter) (ne_of_gt hL), key lamInner (ne_of_gt hli)]
  exact div_le_div_of_nonneg_left (le_of_lt (sq_pos_of_ne_zero hx)) (by linarith) (by linarith)

set_option linter.unusedVariables false in
/-- Plan §7 #9: the tolerance radius grows with the total reorganization energy (the plan §6.3
`bepRadius_mono`, derived here from `Real.sqrt_le_sqrt` because `Sharp.lean` is not imported). The
hypothesis `hli : 0 ≤ lamInner` is kept for signature fidelity with plan §6.3 and the statement
skeleton; the proof does not consume it, since `lamInner ≤ lamInner + lamOuter` already follows from
`hlo` alone. -/
theorem bepRadius_add {lamInner lamOuter tol : ℝ} (hli : 0 ≤ lamInner) (hlo : 0 ≤ lamOuter)
    (htol : 0 ≤ tol) : bepRadius lamInner tol ≤ bepRadius (lamInner + lamOuter) tol := by
  unfold bepRadius
  have hmul : lamInner * tol ≤ (lamInner + lamOuter) * tol :=
    mul_le_mul_of_nonneg_right (by linarith) htol
  have hsqrt := Real.sqrt_le_sqrt hmul
  linarith

/-- Plan §7 #10: microscopic conformance — for positive inner and outer reorganization energies,
every symmetric window whose half-width is at most the tolerance radius `2√(lam*tol)` of the *total*
curvature conforms to the BEP line within `tol`. The half-width is deliberately not assumed
nonnegative: for `w < 0` the window `[-w, w]` is empty and the statement holds vacuously, and for
`0 ≤ w` this is the radius criterion of plan §6.2, established here by squaring (`Real.sq_sqrt` +
`sq_le_sq`) instead of through the not-yet-available `epConformsOnWindow_iff_radius`. -/
theorem epConformsOnWindow_of_microscopic {lamInner lamOuter tol w : ℝ} (hli : 0 < lamInner)
    (hlo : 0 < lamOuter) (htol : 0 < tol) (hw : w ≤ bepRadius (lamInner + lamOuter) tol) :
    EPConformsOnWindow (lamInner + lamOuter) tol (-w) w := by
  have hL : 0 < lamInner + lamOuter := by linarith
  have h4 : (0 : ℝ) < 4 * (lamInner + lamOuter) := by linarith
  have hprod : 0 ≤ (lamInner + lamOuter) * tol := mul_nonneg (le_of_lt hL) (le_of_lt htol)
  have htwo : 0 ≤ 2 * Real.sqrt ((lamInner + lamOuter) * tol) := by positivity
  have hsq : (2 * Real.sqrt ((lamInner + lamOuter) * tol)) ^ 2
      = 4 * ((lamInner + lamOuter) * tol) := by
    rw [mul_pow, Real.sq_sqrt hprod]
    norm_num
  have key : ∀ L x : ℝ, L ≠ 0 → bepDefect L x = x ^ 2 / (4 * L) := by
    intro L x hL0
    unfold bepDefect eact bepLine
    field_simp
    ring
  refine ⟨hL, htol, ?_⟩
  intro x hx
  rcases le_or_lt 0 w with hw0 | hwn
  · -- nonnegative half-width: the radius bound is the squared bound `w^2/(4*L) ≤ tol`
    have hrad : w ^ 2 / (4 * (lamInner + lamOuter)) ≤ tol := by
      rw [bepRadius] at hw
      rw [div_le_iff₀ h4]
      calc w ^ 2 ≤ (2 * Real.sqrt ((lamInner + lamOuter) * tol)) ^ 2 := by
            rw [sq_le_sq, abs_of_nonneg hw0, abs_of_nonneg htwo]
            exact hw
        _ = tol * (4 * (lamInner + lamOuter)) := by rw [hsq]; ring
    have hx2 : x ^ 2 ≤ w ^ 2 := by
      rw [Set.mem_Icc] at hx
      have habs : |x| ≤ w := abs_le.mpr hx
      rw [sq_le_sq, abs_of_nonneg hw0]
      exact habs
    rw [key (lamInner + lamOuter) x (ne_of_gt hL), abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ h4]
    rw [div_le_iff₀ h4] at hrad
    linarith
  · -- negative half-width: `[-w, w]` is empty
    exfalso
    rw [Set.mem_Icc] at hx
    linarith [hx.1, hx.2]

/-- Plan §7 #11: conformance on a window transfers from the inner curvature to the larger total
curvature on the same window — the absolute violation `|bepDefect lam x|` is antitone in `lam`
(plan §6.3 shape). At `x = 0` both defects vanish, so the antitone identity of #8 — whose premise
`x ≠ 0` is a statement of the plan and not a mathematical necessity here — is not needed. -/
theorem epConformsOnWindow_shrinks_with_inner {lamInner lamOuter tol w : ℝ} (hli : 0 < lamInner)
    (hlo : 0 < lamOuter) (htol : 0 < tol) :
    EPConformsOnWindow lamInner tol (-w) w → EPConformsOnWindow (lamInner + lamOuter) tol (-w) w := by
  intro h
  have hL : 0 < lamInner + lamOuter := by linarith
  have key : ∀ L x : ℝ, L ≠ 0 → bepDefect L x = x ^ 2 / (4 * L) := by
    intro L x hL0
    unfold bepDefect eact bepLine
    field_simp
    ring
  refine ⟨hL, htol, ?_⟩
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · -- thermoneutral driving force: both violations vanish
    rw [key (lamInner + lamOuter) 0 (ne_of_gt hL)]
    simpa using le_of_lt htol
  · -- non-thermoneutral: the total violation is at most the inner one
    have hmono : |bepDefect (lamInner + lamOuter) x| ≤ |bepDefect lamInner x| := by
      rw [key (lamInner + lamOuter) x (ne_of_gt hL), key lamInner x (ne_of_gt hli),
        abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_left (le_of_lt (sq_pos_of_ne_zero hx0)) (by linarith) (by linarith)
    exact le_trans hmono (h.2.2 x hx)

set_option linter.unusedVariables false in
/-- Plan §7 #12: Brønsted complementarity survives microscopic composition — at the total
reorganization energy the forward and reverse coefficients still add up to one. The hypothesis
`lamInner + lamOuter ≠ 0` is kept for signature fidelity (plan §5 #8 carries it); the identity is
the algebraic one `(1/2 - x/(2L)) + (1/2 + x/(2L)) = 1` in the field `ℝ` and holds by `ring`
without it. -/
theorem transfer_complementary_microscopic {lamInner lamOuter x : ℝ}
    (hlam : lamInner + lamOuter ≠ 0) :
    transfer (lamInner + lamOuter) x + reverseTransfer (lamInner + lamOuter) x = 1 := by
  unfold transfer reverseTransfer
  ring

/-! ## Cross-theory dictionary link (statement-authority AUX of the B4 block, after plan §7 #12) -/

/-- Statement-authority AUX (no plan §7 row): the BEP *observable* window slope is Hammond's Leffler
secant over the same pair of driving forces. Unfolding the four bodies turns the goal into
`(eact lam x - eact lam (x + h)) / h = -((lam - (x + h)) ^ 2 / (4 * lam) - (lam - x) ^ 2 / (4 * lam))
/ ((x + h) - x)`, i.e. the same term up to `-(b - a) = a - b` and `(x + h) - x = h`; no
non-degeneracy premise is needed because both sides are totalised divisions and agree at `h = 0`
(`0 = 0`). The link is not definitional — the two bodies differ in sign convention and in the pair
indexing — hence it is proved rather than closed by `rfl`. -/
theorem secSlope_eq_lefflerSecant (lam x h : ℝ) :
    secSlope lam x h = Hammond.lefflerSecant lam x (x + h) := by
  unfold secSlope Hammond.lefflerSecant Hammond.gapReactant eact
  -- reindex Hammond's pair `(x, x + h)` to the BEP denominator `h`, then normalise in `ℝ`
  rw [show x + h - x = h by ring]
  ring

end PhotoLean.BEP
