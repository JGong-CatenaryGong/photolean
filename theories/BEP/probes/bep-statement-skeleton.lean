/-
Statement skeleton for the BEP theory (Bell–Evans–Polanyi) — the **authority for all delivered
signatures** of `PhotoLean/BEP/*.lean`. Every delivered declaration must match the corresponding
signature here word for word (plan §10.5, the mechanical fidelity check reads this file). It lives
under `theories/BEP/probes/`, i.e. OUTSIDE `SOURCE_DIRS` (`PhotoLean`), because the source tree has
zero tolerance for the unfinished-proof placeholder keyword; statement-first requires the signatures
to elaborate before any proof work starts. 0 error is the Sprint-0 gate.

Model. Equal-curvature two-parabola model of an elementary step in the driving-force convention
`x = -ΔG°` (exergonic: `x > 0`): barrier `eact lam x = (lam - x)^2/(4*lam)`, BEP line
`bepLine lam x = lam/4 - x/2`, transfer coefficient `transfer lam x = 1/2 - x/(2*lam)` in
**linear-response form** (so `α = q‡` and `α(0) = 1/2` are theorems, not definitions — plan §2,
§4.1), reverse coefficient `reverseTransfer lam x = 1/2 + x/(2*lam)`, observable secant
`secSlope lam x h = (eact lam x - eact lam (x+h))/h`, tolerance radius
`bepRadius lam tol = 2*√(lam*tol)`, minimax line `bepBestLine lam w x = lam/4 + w^2/(8*lam) - x/2`.
Every physical premise (`lam ≠ 0`, `0 < lam`, `0 < tol`, `h ≠ 0`, `w`-conditions) is an explicit
hypothesis — nothing is hidden in a definition (engine rule 3).

Provenance of the rows below: this file follows `theories/BEP/plan.md` §4.1/§4.2 (B1), §5 (B2),
§6.1–§6.5 (B3), §7 (B4), §8.1 (B5a) row by row; each docstring carries its plan locus. Statements
marked `AUX` are additions of the API round (verified in the probes) that the plan does not name;
the lead may keep or drop them.

Two corrections folded in from the Sprint-0 risk probes (plan §8.1, §11; lead 2026-09-20):
`transfer`/`reverseTransfer` carry the linear-response bodies above (the TS-coordinate body
`(lam - x)/(2*lam)` is now the *theorem* `transfer_eq_tsCoord`), and `qLamOfPair` uses the numerator
`x₂^2 - x₁^2` with the reconstruction premise `lam ≠ 0` (the literal `x₁^2 - x₂^2` returns `-λ`).

Plan §8.2 (`PhotoLean/BEP/Instances.lean`, rows I1–I12) is covered by the B5b block below; its
literature rows carry the kcal/mol numbers verbatim from `theories/BEP/LITERATURE.md` §R1.10 (the
source locus and the model's `x = -ΔG°` sign convention are in each docstring). Family **F4**
(Table 2 "PE") has **no per-row numbers** in §R1.10 — only family aggregates — so it carries no
statement here; that gap is reported in `proofs/API-NOTES.md`.

API calibration for this file: `proofs/API-NOTES.md` §"BEP round"; kernel evidence for every recipe:
`theories/BEP/probes/bep-api-{algebra,abs-sqrt,rat,minimax,zone}.lean`.
-/
import Mathlib
import PhotoLean.Marcus.Basic
import PhotoLean.Hammond.Basic

namespace PhotoLean

namespace BEP

/-! ## B1 — description layer (`PhotoLean/BEP/Basic.lean`; plan §4.1, 18 declarations) -/

/-- Forward activation barrier in the equal-curvature two-parabola model; `x = -ΔG°`. -/
noncomputable def eact (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- The Bell–Evans–Polanyi line: the linear free-energy law tangent at thermoneutrality. -/
noncomputable def bepLine (lam x : ℝ) : ℝ := lam / 4 - x / 2

/-- Exact violation of the BEP line law. -/
noncomputable def bepDefect (lam x : ℝ) : ℝ := eact lam x - bepLine lam x

/-- BEP / Brønsted / Leffler coefficient of the forward direction, in linear-response form. -/
noncomputable def transfer (lam x : ℝ) : ℝ := 1 / 2 - x / (2 * lam)

/-- Coefficient of the reverse direction of the same step (driving force `-x`). -/
noncomputable def reverseTransfer (lam x : ℝ) : ℝ := 1 / 2 + x / (2 * lam)

/-- Observable BEP slope: a finite difference of barrier data over the window `[x, x+h]`. -/
noncomputable def secSlope (lam x h : ℝ) : ℝ := (eact lam x - eact lam (x + h)) / h

/-- Half-width of the driving-force window on which the line law holds within `tol`. -/
noncomputable def bepRadius (lam tol : ℝ) : ℝ := 2 * Real.sqrt (lam * tol)

/-- Minimax affine BEP law on a symmetric window of half-width `w`. -/
noncomputable def bepBestLine (lam w x : ℝ) : ℝ := lam / 4 + w ^ 2 / (8 * lam) - x / 2

/-- Evans–Polanyi bounds on the transfer coefficient. -/
def EPBounds (lam x : ℝ) : Prop := 0 ≤ transfer lam x ∧ transfer lam x ≤ 1

/-- `eact` agrees with some affine function of the driving force on the set `s`. -/
def EPLinearOn (lam : ℝ) (s : Set ℝ) : Prop := ∃ c a : ℝ, ∀ x ∈ s, eact lam x = c + a * x

/-- The BEP line law holds exactly on every driving force. -/
def EPExact (lam : ℝ) : Prop := EPLinearOn lam Set.univ

/-- The line law holds on the window `[a,b]` within tolerance `tol`. -/
def EPConformsOnWindow (lam tol a b : ℝ) : Prop :=
  0 < lam ∧ 0 < tol ∧ ∀ x ∈ Set.Icc a b, |bepDefect lam x| ≤ tol

/-- Optimality form: no affine law does better than `w^2/(8λ)` on `[-w,w]`. -/
def EPBestOnWindow (lam w : ℝ) : Prop :=
  0 < lam ∧ 0 < w ∧ ∀ c a : ℝ, ∃ x ∈ Set.Icc (-w) w,
    w ^ 2 / (8 * lam) ≤ |eact lam x - (c + a * x)|

/-- Regimes of the transfer coefficient (decidable classifier). -/
inductive EPZone where
  | degenerate
  | unphysical
  | thermoneutral
  | exergonic
  | endergonic
  | atForwardLimit
  | atReverseLimit
  | beyondForward
  | beyondReverse
  deriving DecidableEq, Repr

/-- Regime classifier, in the style of `Hammond.hammondZone` / `Marcus.zone`. -/
noncomputable def epZone (lam x : ℝ) : EPZone :=
  if lam = 0 then EPZone.degenerate
  else if lam < 0 then EPZone.unphysical
  else if x = 0 then EPZone.thermoneutral
  else if x = lam then EPZone.atForwardLimit
  else if x = -lam then EPZone.atReverseLimit
  else if lam < x then EPZone.beyondForward
  else if x < -lam then EPZone.beyondReverse
  else if 0 < x then EPZone.exergonic
  else EPZone.endergonic

/-- Open regime in which the transfer coefficient is strictly inside `(0,1)`. -/
def EPRegime (lam x : ℝ) : Prop := -lam < x ∧ x < lam

/-- Pointwise conformance to the BEP description. -/
def EPConforms (lam x : ℝ) : Prop := 0 < lam ∧ EPBounds lam x

/-- The exact defect law of the model (the descriptor of the BEP description). -/
def EPDescriptor (lam : ℝ) : Prop := 0 < lam ∧ ∀ x : ℝ, bepDefect lam x = x ^ 2 / (4 * lam)

/-! ### AUX — ℝ observation layer (transfer targets of the B5a cast lemmas) -/

/-- Two-point α observable: the finite-difference slope measured from two barrier data points. -/
noncomputable def alphaObs (x₁ ea₁ x₂ ea₂ : ℝ) : ℝ := (ea₁ - ea₂) / (x₂ - x₁)

/-- Two-point reorganization-energy estimator on the real side (the form the ℚ solver
`qLamOfPair` casts to). -/
noncomputable def lamOfPair (x₁ ea₁ x₂ ea₂ : ℝ) : ℝ :=
  (x₂ ^ 2 - x₁ ^ 2) / (2 * (x₂ - x₁) - 4 * (ea₁ - ea₂))

/-! ## B1 theorems (plan §4.2) -/

/-- Plan §4.2 #1. -/
theorem eact_at_zero {lam : ℝ} (hlam : lam ≠ 0) : eact lam 0 = lam / 4 := by
  sorry

/-- Plan §4.2 #2. -/
theorem eact_at_lam {lam : ℝ} (hlam : lam ≠ 0) : eact lam lam = 0 := by
  sorry

/-- Plan §4.2 #3. -/
theorem eact_zero_lam (x : ℝ) : eact 0 x = 0 := by
  sorry

/-- Plan §4.2 #4: degenerate value of the linear-response coefficient (totalised division). -/
theorem transfer_zero_lam (x : ℝ) : transfer 0 x = 1 / 2 := by
  sorry

/-- Plan §4.2 #5. -/
theorem bepLine_at_zero (lam : ℝ) : bepLine lam 0 = lam / 4 := by
  sorry

/-- Plan §4.2 #6. -/
theorem secSlope_zero_h (lam x : ℝ) : secSlope lam x 0 = 0 := by
  sorry

/-- Plan §4.2 #7. -/
theorem epZone_eq_degenerate_iff (lam x : ℝ) : epZone lam x = EPZone.degenerate ↔ lam = 0 := by
  sorry

/-- Plan §4.2 #8. -/
theorem epZone_eq_unphysical_iff {lam x : ℝ} (hlam : lam ≠ 0) :
    epZone lam x = EPZone.unphysical ↔ lam < 0 := by
  sorry

/-- Plan §4.2 #9. -/
theorem epZone_eq_thermoneutral_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.thermoneutral ↔ x = 0 := by
  sorry

/-- Plan §4.2 #10. -/
theorem epZone_eq_exergonic_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.exergonic ↔ 0 < x ∧ x < lam := by
  sorry

/-- Plan §4.2 #11. -/
theorem epZone_eq_endergonic_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.endergonic ↔ -lam < x ∧ x < 0 := by
  sorry

/-- Plan §4.2 #12. -/
theorem epZone_eq_atForwardLimit_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.atForwardLimit ↔ x = lam := by
  sorry

/-- Plan §4.2 #13. -/
theorem epZone_eq_atReverseLimit_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.atReverseLimit ↔ x = -lam := by
  sorry

/-- Plan §4.2 #14. -/
theorem epZone_eq_beyondForward_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.beyondForward ↔ lam < x := by
  sorry

/-- Plan §4.2 #15. -/
theorem epZone_eq_beyondReverse_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.beyondReverse ↔ x < -lam := by
  sorry

/-! ## B2 — law layer (`PhotoLean/BEP/Criterion.lean`; plan §5) -/

/-- Plan §5 #1. -/
theorem eact_expansion {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    eact lam x = lam / 4 - x / 2 + x ^ 2 / (4 * lam) := by
  sorry

/-- Plan §5 #2. -/
theorem bepDefect_eq {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    bepDefect lam x = x ^ 2 / (4 * lam) := by
  sorry

/-- Plan §5 #3. -/
theorem bepLine_exact_at_thermoneutrality {lam : ℝ} (hlam : lam ≠ 0) :
    bepLine lam 0 = eact lam 0 := by
  sorry

/-- Plan §5 #4. -/
theorem bepDefect_at_thermoneutrality {lam : ℝ} (hlam : lam ≠ 0) : bepDefect lam 0 = 0 := by
  sorry

/-- Plan §5 #5: the Leffler/Brønsted identification (the linear-response body equals the
transition-state coordinate). -/
theorem transfer_eq_tsCoord {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    transfer lam x = (lam - x) / (2 * lam) := by
  sorry

/-- Plan §5 #6. -/
theorem transfer_thermoneutral (lam : ℝ) : transfer lam 0 = 1 / 2 := by
  sorry

/-- Plan §5 #7. -/
theorem reverseTransfer_thermoneutral (lam : ℝ) : reverseTransfer lam 0 = 1 / 2 := by
  sorry

/-- Plan §5 #8: Brønsted complementarity. -/
theorem transfer_add_reverse {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    transfer lam x + reverseTransfer lam x = 1 := by
  sorry

/-- Plan §5 #9. -/
theorem reverseTransfer_eq_transfer_neg (lam x : ℝ) : reverseTransfer lam x = transfer lam (-x) := by
  sorry

/-- Plan §5 #10: the mean-value identity of the parabola. -/
theorem secSlope_eq_transfer_mid {lam : ℝ} (hlam : lam ≠ 0) {x h : ℝ} (hh : h ≠ 0) :
    secSlope lam x h = transfer lam (x + h / 2) := by
  sorry

/-- Plan §5 #11: the observed slope depends only on the midpoint of the observed window. -/
theorem secSlope_midpoint_invariant {lam x y h k : ℝ} (hlam : lam ≠ 0) (hh : h ≠ 0) (hk : k ≠ 0)
    (hmid : x + h / 2 = y + k / 2) : secSlope lam x h = secSlope lam y k := by
  sorry

/-- Plan §5 #12: barrier-reversal identity. -/
theorem eact_neg_eq_add {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) : eact lam (-x) = eact lam x + x := by
  sorry

/-- Plan §5 #13: monotonicity on the normal-region side of the parabola. -/
theorem eact_antitone {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h₁ : x₁ < x₂) (h₂ : x₂ ≤ lam) :
    eact lam x₂ < eact lam x₁ := by
  sorry

/-- Plan §5 #14. -/
theorem bepDefect_nonneg {lam x : ℝ} (hlam : 0 < lam) : 0 ≤ bepDefect lam x := by
  sorry

/-- Plan §5 #15. -/
theorem bepDefect_pos_iff {lam x : ℝ} (hlam : 0 < lam) : 0 < bepDefect lam x ↔ x ≠ 0 := by
  sorry

/-- Plan §5 #16. -/
theorem epDescriptor_holds {lam : ℝ} (hlam : 0 < lam) : EPDescriptor lam := by
  sorry

/-- Plan §5 #17. -/
theorem epDescriptor_conforms {lam x : ℝ} (h : EPDescriptor lam) (hx : x ≠ 0) :
    0 < bepDefect lam x := by
  sorry

/-- Plan §5 #18. -/
theorem epConforms_iff_bounds {lam x : ℝ} (hlam : 0 < lam) :
    EPConforms lam x ↔ EPBounds lam x := by
  sorry

/-- Plan §5 #19. -/
theorem exists_epDescriptor : ∃ lam : ℝ, EPDescriptor lam := by
  sorry

/-- Plan §5 #20–26 (non-vacuity of the regimes, one per constructor). -/
theorem exists_thermoneutral : ∃ lam x : ℝ, epZone lam x = EPZone.thermoneutral := by
  sorry

theorem exists_exergonic : ∃ lam x : ℝ, epZone lam x = EPZone.exergonic := by
  sorry

theorem exists_endergonic : ∃ lam x : ℝ, epZone lam x = EPZone.endergonic := by
  sorry

theorem exists_atForwardLimit : ∃ lam x : ℝ, epZone lam x = EPZone.atForwardLimit := by
  sorry

theorem exists_atReverseLimit : ∃ lam x : ℝ, epZone lam x = EPZone.atReverseLimit := by
  sorry

theorem exists_beyondForward : ∃ lam x : ℝ, epZone lam x = EPZone.beyondForward := by
  sorry

theorem exists_beyondReverse : ∃ lam x : ℝ, epZone lam x = EPZone.beyondReverse := by
  sorry

theorem exists_unphysical : ∃ lam x : ℝ, epZone lam x = EPZone.unphysical := by
  sorry

theorem exists_degenerate : ∃ lam x : ℝ, epZone lam x = EPZone.degenerate := by
  sorry

/-! ## B3 — sharp conditions (`PhotoLean/BEP/Sharp.lean`; plan §6.1–§6.5) -/

/-- Plan §6.1 #1. -/
theorem epBounds_iff_region {lam x : ℝ} (hlam : 0 < lam) :
    EPBounds lam x ↔ -lam ≤ x ∧ x ≤ lam := by
  sorry

/-- Plan §6.1 #2. -/
theorem epRegime_iff_strict {lam x : ℝ} (hlam : 0 < lam) :
    EPRegime lam x ↔ 0 < transfer lam x ∧ transfer lam x < 1 := by
  sorry

/-- Plan §6.1 #3. -/
theorem transfer_at_lam {lam : ℝ} (hlam : 0 < lam) : transfer lam lam = 0 := by
  sorry

/-- Plan §6.1 #4. -/
theorem transfer_at_neg_lam {lam : ℝ} (hlam : 0 < lam) : transfer lam (-lam) = 1 := by
  sorry

/-- Plan §6.1 #5: α > 1 — the reverse direction is in the inverted region. -/
theorem not_epBounds_of_lt_neg {lam x : ℝ} (hlam : 0 < lam) (hx : x < -lam) :
    ¬ EPBounds lam x := by
  sorry

/-- Plan §6.1 #6: α < 0 — the forward direction is in the inverted region. -/
theorem not_epBounds_of_gt {lam x : ℝ} (hlam : 0 < lam) (hx : lam < x) : ¬ EPBounds lam x := by
  sorry

/-- Plan §6.1 #7. -/
theorem epExact_iff_degenerate (lam : ℝ) : EPExact lam ↔ lam = 0 := by
  sorry

/-- Plan §6.1 #8. -/
theorem not_epLinearOn_of_ne_zero {lam a b : ℝ} (hlam : lam ≠ 0) (hab : a < b) :
    ¬ EPLinearOn lam (Set.Icc a b) := by
  sorry

/-- Plan §6.1 #9. -/
theorem exists_conforms_fails : ∃ lam tol w : ℝ, 0 < lam ∧ 0 < tol ∧
    ¬ EPConformsOnWindow lam tol (-w) w := by
  sorry

/-- Plan §6.2 #10. -/
theorem bepDefect_abs_eq {lam x : ℝ} (hlam : lam ≠ 0) :
    |bepDefect lam x| = x ^ 2 / (4 * |lam|) := by
  sorry

/-- Plan §6.2 #11: **the tolerance/radius theorem** (sharp validity condition). -/
theorem epConformsOnWindow_iff_radius {lam tol w : ℝ} (hlam : 0 < lam) (htol : 0 < tol)
    (hw : 0 ≤ w) : EPConformsOnWindow lam tol (-w) w ↔ w ≤ bepRadius lam tol := by
  sorry

/-- Plan §6.2 #12: the radius is attained, not an estimate. -/
theorem epConformsOnWindow_at_radius {lam tol : ℝ} (hlam : 0 < lam) (htol : 0 < tol) :
    EPConformsOnWindow lam tol (-(bepRadius lam tol)) (bepRadius lam tol) := by
  sorry

/-- Plan §6.2 #13: shrinking the window preserves conformance. -/
theorem epConformsOnWindow_mono {lam tol a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    EPConformsOnWindow lam tol a b → EPConformsOnWindow lam tol a' b' := by
  sorry

/-- Plan §6.2 #14. -/
theorem epConformsOnWindow_symm {lam tol a b : ℝ} :
    EPConformsOnWindow lam tol a b ↔ EPConformsOnWindow lam tol (-b) (-a) := by
  sorry

/-- Plan §6.3 #15. -/
theorem bepDefect_antitone_lam {lam₁ lam₂ x : ℝ} (h0 : 0 < lam₁) (hle : lam₁ ≤ lam₂)
    (hx : x ≠ 0) : bepDefect lam₂ x ≤ bepDefect lam₁ x := by
  sorry

/-- Plan §6.3 #16. -/
theorem bepRadius_mono {lam₁ lam₂ tol : ℝ} (h0 : 0 ≤ lam₁) (hle : lam₁ ≤ lam₂) (htol : 0 ≤ tol) :
    bepRadius lam₁ tol ≤ bepRadius lam₂ tol := by
  sorry

/-- Plan §6.3 #17 (the plan leaves the hypotheses as `(…)`; resolved as positivity of `lam₁`
plus `lam₁ ≤ lam₂`, which is what the proof of #15/#16 consumes). -/
theorem epConformsOnWindow_mono_lam {lam₁ lam₂ tol a b : ℝ} (h0 : 0 < lam₁) (hle : lam₁ ≤ lam₂) :
    EPConformsOnWindow lam₁ tol a b → EPConformsOnWindow lam₂ tol a b := by
  sorry

/-- Plan §6.4 #18: the error bound of the minimax line. -/
theorem bepBestLine_error {lam w : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    ∀ x ∈ Set.Icc (-w) w, |eact lam x - bepBestLine lam w x| ≤ w ^ 2 / (8 * lam) := by
  sorry

/-- Plan §6.4 #19: **the minimax optimality statement** (three-point equioscillation). -/
theorem epBestOnWindow_holds {lam w : ℝ} (hlam : 0 < lam) (hw : 0 < w) :
    EPBestOnWindow lam w := by
  sorry

/-- Plan §6.4 #20: the tangent line's worst case on the window. -/
theorem bepLine_worst_case {lam w : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    ∃ x ∈ Set.Icc (-w) w, |bepDefect lam x| = w ^ 2 / (4 * lam) := by
  sorry

/-- Plan §6.4 #21: the best line halves the tangent line's worst case. -/
theorem bepBestLine_halves {lam w : ℝ} (hlam : 0 < lam) (hw : 0 < w) :
    w ^ 2 / (8 * lam) = (w ^ 2 / (4 * lam)) / 2 ∧ w ^ 2 / (8 * lam) < w ^ 2 / (4 * lam) := by
  sorry

/-- Plan §6.5 #22. -/
theorem bepDefect_zero_lam_witness : bepDefect 0 1 = 1 / 2 ∧ ((1 : ℝ) ^ 2 / (4 * 0)) = 0 := by
  sorry

/-- Plan §6.5 #23. -/
theorem bepDefect_neg_lam_witness : bepDefect (-1) 1 = -(1 / 4) := by
  sorry

/-- Plan §6.5 #24. -/
theorem bepDefect_sign_flips {lam x : ℝ} (hlam : lam < 0) (hx : x ≠ 0) : bepDefect lam x < 0 := by
  sorry

/-- Plan §6.5 #25. -/
theorem secSlope_needs_h_ne_zero : secSlope 1 0 0 = 0 ∧ transfer 1 0 ≠ 0 := by
  sorry

/-! ### AUX — literal sup-norm form of the minimax block (verified in
`theories/BEP/probes/bep-api-minimax.lean`; plan §6.4 states the ε-free form
`EPBestOnWindow`, this is its `sSup` twin) -/

/-- Uniform (sup-norm) error of the affine model `c + a * x` on the window `[-w, w]`. -/
noncomputable def epSupError (lam w c a : ℝ) : ℝ :=
  sSup ((fun x => |eact lam x - (c + a * x)|) '' Set.Icc (-w) w)

/-- AUX: an upper bound plus an attained value pin down a supremum (the `sSup` recipe). -/
theorem sSup_eq_of_le_of_mem {s : Set ℝ} {b : ℝ} (hne : s.Nonempty) (hbdd : BddAbove s)
    (hle : ∀ a ∈ s, a ≤ b) (hmem : b ∈ s) : sSup s = b := by
  sorry

/-- AUX: the symmetric three-point identity quoted by plan §6.4 #19, with
`f y = eact lam y - (c + a * y)`. -/
theorem bep_error_three_point {lam c a w : ℝ} (hlam : lam ≠ 0) :
    (eact lam (-w) - (c + a * (-w))) + (eact lam w - (c + a * w)) -
        2 * (eact lam 0 - (c + a * 0)) = w ^ 2 / (2 * lam) := by
  sorry

/-- AUX: the general second-difference identity behind `not_epLinearOn_of_ne_zero` and the
minimax lower bound. -/
theorem eact_second_difference {lam c a x₁ x₂ : ℝ} (hlam : lam ≠ 0) :
    (eact lam x₁ - (c + a * x₁)) + (eact lam x₂ - (c + a * x₂)) -
        2 * (eact lam ((x₁ + x₂) / 2) - (c + a * ((x₁ + x₂) / 2))) =
      (x₁ - x₂) ^ 2 / (8 * lam) := by
  sorry

/-- AUX: the error set of the sup-norm is bounded above (side condition of `le_csSup`). -/
theorem epSupError_bddAbove {lam w c a : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    BddAbove ((fun x => |eact lam x - (c + a * x)|) '' Set.Icc (-w) w) := by
  sorry

/-- AUX: the sup-norm error of `bepBestLine` is exactly `w^2/(8*lam)`. -/
theorem epSupError_bestLine {lam w : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    epSupError lam w (lam / 4 + w ^ 2 / (8 * lam)) (-(1 / 2)) = w ^ 2 / (8 * lam) := by
  sorry

/-- AUX: every affine model has sup-norm error at least `w^2/(8*lam)` (the `sSup` form of
`epBestOnWindow_holds`). -/
theorem epSupError_sharp {lam w c a : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    w ^ 2 / (8 * lam) ≤ epSupError lam w c a := by
  sorry

/-! ## B4 — microscopic and cross-module layer (`PhotoLean/BEP/Compose.lean`; plan §7) -/

/-- Plan §7 #1: the BEP barrier is the Marcus barrier (identical bodies, independent
statements — `rfl`). -/
theorem eact_eq_barrier (lam x : ℝ) : eact lam x = Marcus.barrier lam x := by
  sorry

/-- Plan §7 #2 (the plan writes the hypothesis as `(h : Marcus.rate A lam kB T x = …)`, an
ellipsis; resolved here as the identity itself, which is what `eact_eq_barrier` makes `rfl`-true
up to `Marcus.rate`'s body). -/
theorem rate_eq_exp_neg_eact (A lam kB T x : ℝ) :
    Marcus.rate A lam kB T x = A * Real.exp (-(eact lam x) / (kB * T)) := by
  sorry

/-- Plan §7 #3: cross-module form of §5 #5 (`transfer = Hammond.tsCoord`). -/
theorem transfer_eq_tsCoord_bridge {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    transfer lam x = Hammond.tsCoord lam x := by
  sorry

/-- Plan §7 #4. -/
theorem epBounds_iff_no_inverted_direction {lam x : ℝ} (hlam : 0 < lam) :
    EPBounds lam x ↔ ¬ (Marcus.InvertedRegion lam x ∨ Marcus.InvertedRegion lam (-x)) := by
  sorry

/-- Plan §7 #5. -/
theorem epBounds_of_reactionRegion {lam x : ℝ} (hlam : 0 < lam)
    (h : Hammond.ReactionRegion lam x) : EPBounds lam x := by
  sorry

/-- Plan §7 #6. -/
theorem epBounds_of_marcus_normal {lam x : ℝ} (hlam : 0 < lam) (h : Marcus.NormalRegion lam x)
    (hx : -lam ≤ x) : EPBounds lam x := by
  sorry

/-- Plan §7 #7. -/
theorem epDescriptor_of_microscopic {lamInner lamOuter : ℝ} (hli : 0 < lamInner)
    (hlo : 0 < lamOuter) : EPDescriptor (lamInner + lamOuter) := by
  sorry

/-- Plan §7 #8. -/
theorem bepDefect_le_of_microscopic {lamInner lamOuter x : ℝ} (hli : 0 < lamInner)
    (hlo : 0 < lamOuter) (hx : x ≠ 0) :
    bepDefect (lamInner + lamOuter) x ≤ bepDefect lamInner x := by
  sorry

/-- Plan §7 #9. -/
theorem bepRadius_add {lamInner lamOuter tol : ℝ} (hli : 0 ≤ lamInner) (hlo : 0 ≤ lamOuter)
    (htol : 0 ≤ tol) : bepRadius lamInner tol ≤ bepRadius (lamInner + lamOuter) tol := by
  sorry

/-- Plan §7 #10. -/
theorem epConformsOnWindow_of_microscopic {lamInner lamOuter tol w : ℝ} (hli : 0 < lamInner)
    (hlo : 0 < lamOuter) (htol : 0 < tol) (hw : w ≤ bepRadius (lamInner + lamOuter) tol) :
    EPConformsOnWindow (lamInner + lamOuter) tol (-w) w := by
  sorry

/-- Plan §7 #11 (the plan leaves the hypotheses as `(…)`; resolved as positivity of both
curvatures and of the tolerance, matching #7/#8). -/
theorem epConformsOnWindow_shrinks_with_inner {lamInner lamOuter tol w : ℝ} (hli : 0 < lamInner)
    (hlo : 0 < lamOuter) (htol : 0 < tol) :
    EPConformsOnWindow lamInner tol (-w) w → EPConformsOnWindow (lamInner + lamOuter) tol (-w) w := by
  sorry

/-- Plan §7 #12. -/
theorem transfer_complementary_microscopic {lamInner lamOuter x : ℝ}
    (hlam : lamInner + lamOuter ≠ 0) :
    transfer (lamInner + lamOuter) x + reverseTransfer (lamInner + lamOuter) x = 1 := by
  sorry

/-- AUX: the observable BEP secant is the Hammond Leffler secant at the pair `(x, x + h)`. -/
theorem secSlope_eq_lefflerSecant (lam x h : ℝ) :
    secSlope lam x h = Hammond.lefflerSecant lam x (x + h) := by
  sorry

/-! ## B5a — computable decision layer (`PhotoLean/BEP/RatModel.lean`; plan §8.1) -/

namespace Rat

/-! Definitions verbatim from plan §8.1 (`EPQVerdict` and `epQVerdict` bodies are supplied here:
the plan writes `…` for `epQVerdict`). -/

def qEact (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

def qBepLine (lam x : ℚ) : ℚ := lam / 4 - x / 2

def qBepDefect (lam x : ℚ) : ℚ := qEact lam x - qBepLine lam x

def qTransfer (lam x : ℚ) : ℚ := 1 / 2 - x / (2 * lam)

def qReverseTransfer (lam x : ℚ) : ℚ := 1 / 2 + x / (2 * lam)

def qSecSlope (lam x h : ℚ) : ℚ := (qEact lam x - qEact lam (x + h)) / h

/-- Two-point observable BEP slope from data `(x₁,Ea₁)`, `(x₂,Ea₂)`. -/
def qAlphaObs (x₁ ea₁ x₂ ea₂ : ℚ) : ℚ := (ea₁ - ea₂) / (x₂ - x₁)

/-- Two-point reorganization-energy solver (the model's λ from two data points).
Numerator `x₂² - x₁²` and the premise `lam ≠ 0` are **required** (plan §8.1). -/
def qLamOfPair (x₁ ea₁ x₂ ea₂ : ℚ) : ℚ := (x₂ ^ 2 - x₁ ^ 2) / (2 * (x₂ - x₁) - 4 * (ea₁ - ea₂))

/-- Window conformance, in squared form so that it is decided without square roots. -/
def qConformsWindow (lam tol w : ℚ) : Prop := 0 < lam ∧ 0 < tol ∧ w ^ 2 ≤ 4 * lam * tol

inductive EPQVerdict where
  | degenerate
  | unphysical
  | conforming
  | boundary
  | superLinear
  | subLinear
  deriving DecidableEq, Repr

/-- Verdict on a *single* family point (the regime of its coefficient). The plan writes `…`: the
cascade below resolves it as `degenerate` (`λ = 0`), `unphysical` (`λ < 0`), `boundary`
(`x = ±λ`, i.e. α = 0 or 1), `conforming` (α strictly inside `(0,1)`), `superLinear` (α above the
Evans–Polanyi band, `1 < α`) and `subLinear` (α below it, `α < 0`). -/
def epQVerdict (lam x : ℚ) : EPQVerdict :=
  if lam = 0 then EPQVerdict.degenerate
  else if lam < 0 then EPQVerdict.unphysical
  else if x = lam then EPQVerdict.boundary
  else if x = -lam then EPQVerdict.boundary
  else if 0 < qTransfer lam x ∧ qTransfer lam x < 1 then EPQVerdict.conforming
  else if 1 < qTransfer lam x then EPQVerdict.superLinear
  else EPQVerdict.subLinear

/-! ### Theorems of plan §8.1 -/

theorem qEact_cast (lam x : ℚ) : ((qEact lam x : ℚ) : ℝ) = eact (lam : ℝ) (x : ℝ) := by
  sorry

theorem qBepLine_cast (lam x : ℚ) :
    ((qBepLine lam x : ℚ) : ℝ) = bepLine (lam : ℝ) (x : ℝ) := by
  sorry

theorem qBepDefect_cast (lam x : ℚ) :
    ((qBepDefect lam x : ℚ) : ℝ) = bepDefect (lam : ℝ) (x : ℝ) := by
  sorry

theorem qTransfer_cast (lam x : ℚ) :
    ((qTransfer lam x : ℚ) : ℝ) = transfer (lam : ℝ) (x : ℝ) := by
  sorry

/-- Transfer: the rational reverse coefficient casts to the real one (the mirror of
`qTransfer_cast`; added 2026-09-20 so that `qReverseTransfer` is not an unconstrained definition). -/
theorem qReverseTransfer_cast (lam x : ℚ) :
    ((qReverseTransfer lam x : ℚ) : ℝ) = reverseTransfer (lam : ℝ) (x : ℝ) := by
  sorry

theorem qSecSlope_cast {lam x h : ℚ} (hh : h ≠ 0) :
    ((qSecSlope lam x h : ℚ) : ℝ) = secSlope (lam : ℝ) (x : ℝ) (h : ℝ) := by
  sorry

theorem qAlphaObs_cast {x₁ ea₁ x₂ ea₂ : ℚ} (h : x₂ ≠ x₁) :
    ((qAlphaObs x₁ ea₁ x₂ ea₂ : ℚ) : ℝ) = alphaObs (x₁ : ℝ) (ea₁ : ℝ) (x₂ : ℝ) (ea₂ : ℝ) := by
  sorry

theorem qLamOfPair_cast {x₁ ea₁ x₂ ea₂ : ℚ} (h : x₁ ≠ x₂) :
    ((qLamOfPair x₁ ea₁ x₂ ea₂ : ℚ) : ℝ) =
      lamOfPair (x₁ : ℝ) (ea₁ : ℝ) (x₂ : ℝ) (ea₂ : ℝ) := by
  sorry

theorem qSecSlope_eq_qTransfer_mid {lam : ℚ} (hlam : lam ≠ 0) {x h : ℚ} (hh : h ≠ 0) :
    qSecSlope lam x h = qTransfer lam (x + h / 2) := by
  sorry

/-- Plan §8.1: two-point data → structural coefficient (the observed slope is the coefficient at
the data midpoint). -/
theorem qAlphaObs_eq_qTransfer_mid {lam x₁ x₂ : ℚ} (hlam : lam ≠ 0) (h : x₁ ≠ x₂) :
    qAlphaObs x₁ (qEact lam x₁) x₂ (qEact lam x₂) = qTransfer lam ((x₁ + x₂) / 2) := by
  sorry

/-- Plan §8.1: two model-consistent data points determine λ uniquely. The premise `lam ≠ 0` is
necessary — at `lam = 0` the totalised division makes `qEact 0 x` constant `0` while the solver's
linear relation still requires `λ ≠ 0` (kernel counterexample in `bep-api-rat.lean`). -/
theorem qLamOfPair_reconstructs {lam x₁ ea₁ x₂ ea₂ : ℚ} (hlam : lam ≠ 0) (hx : x₁ ≠ x₂)
    (hden : 2 * (x₂ - x₁) - 4 * (ea₁ - ea₂) ≠ 0) (h₁ : ea₁ = qEact lam x₁)
    (h₂ : ea₂ = qEact lam x₂) : qLamOfPair x₁ ea₁ x₂ ea₂ = lam := by
  sorry

/-- The ℝ-side counterpart of the reconstruction theorem (lead 2026-09-20). -/
theorem lamOfPair_reconstructs {lam x₁ ea₁ x₂ ea₂ : ℝ} (hlam : lam ≠ 0) (hx : x₁ ≠ x₂)
    (hden : 2 * (x₂ - x₁) - 4 * (ea₁ - ea₂) ≠ 0) (h₁ : ea₁ = eact lam x₁)
    (h₂ : ea₂ = eact lam x₂) : lamOfPair x₁ ea₁ x₂ ea₂ = lam := by
  sorry

/-- Plan §8.1: the squared conformance predicate is the radius condition (the `↔` that makes the
kernel computation binding for the real tolerance theorem §6.2 #11). -/
theorem qConformsWindow_iff_radius_sq {lam tol w : ℚ} (hlam : 0 < lam) (htol : 0 < tol)
    (hw : 0 ≤ w) : qConformsWindow lam tol w ↔ ((w : ℚ) : ℝ) ≤ bepRadius (lam : ℝ) (tol : ℝ) := by
  sorry

/-- Plan §8.1: verdict characterizations. -/
theorem epQVerdict_conforming_iff {lam x : ℚ} (hlam : 0 < lam) :
    epQVerdict lam x = EPQVerdict.conforming ↔ 0 < qTransfer lam x ∧ qTransfer lam x < 1 := by
  sorry

theorem epQVerdict_boundary_iff {lam x : ℚ} (hlam : 0 < lam) :
    epQVerdict lam x = EPQVerdict.boundary ↔ x = lam ∨ x = -lam := by
  sorry

theorem epQVerdict_superLinear_iff {lam x : ℚ} (hlam : 0 < lam) :
    epQVerdict lam x = EPQVerdict.superLinear ↔ 1 < qTransfer lam x := by
  sorry

theorem epQVerdict_subLinear_iff {lam x : ℚ} (hlam : 0 < lam) :
    epQVerdict lam x = EPQVerdict.subLinear ↔ qTransfer lam x < 0 := by
  sorry

/-- Second divided difference of three family points: the model's curvature witness. -/
def qSecondDividedDiff (x₁ e₁ x₂ e₂ x₃ e₃ : ℚ) : ℚ :=
  ((e₃ - e₂) / (x₃ - x₂) - (e₂ - e₁) / (x₂ - x₁)) / (x₃ - x₁)

/-- Three family points are consistent with the equal-curvature two-parabola model. -/
def qModelConsistent3 (lam x₁ x₂ x₃ e₁ e₂ e₃ : ℚ) : Prop :=
  0 < lam ∧ e₁ = qEact lam x₁ ∧ e₂ = qEact lam x₂ ∧ e₃ = qEact lam x₃

/-- Plan §8.1: the second divided difference of three model points is the curvature `1/(4λ)`. The
three abscissae must be pairwise distinct — at `x₁ = x₃` the outer denominator is `0` and the
totalised division gives `0`, not `1/(4λ)` (kernel-measured). Recipe: restate the three `≠` facts
as `xᵢ - xⱼ ≠ 0` for `field_simp`, then `unfold qSecondDividedDiff qEact; field_simp; ring`. -/
theorem qSecondDividedDiff_model {lam x₁ x₂ x₃ : ℚ} (hlam : lam ≠ 0) (h₁₂ : x₁ ≠ x₂)
    (h₂₃ : x₂ ≠ x₃) (h₁₃ : x₁ ≠ x₃) :
    qSecondDividedDiff x₁ (qEact lam x₁) x₂ (qEact lam x₂) x₃ (qEact lam x₃) = 1 / (4 * lam) := by
  sorry

/-- Plan §8.1: with `λ > 0` the model forces the second divided difference to be positive — the
λ-independent test that refutes the literature families. -/
theorem qModelConsistent3_curvature_pos {lam x₁ x₂ x₃ e₁ e₂ e₃ : ℚ}
    (h : qModelConsistent3 lam x₁ x₂ x₃ e₁ e₂ e₃) (h₁₂ : x₁ ≠ x₂) (h₂₃ : x₂ ≠ x₃)
    (h₁₃ : x₁ ≠ x₃) : 0 < qSecondDividedDiff x₁ e₁ x₂ e₂ x₃ e₃ := by
  sorry

/-- Plan §8.1: three model-consistent points determine λ from their curvature. -/
theorem qModelConsistent3_lam_eq {lam x₁ x₂ x₃ e₁ e₂ e₃ : ℚ}
    (h : qModelConsistent3 lam x₁ x₂ x₃ e₁ e₂ e₃) (h₁₂ : x₁ ≠ x₂) (h₂₃ : x₂ ≠ x₃)
    (h₁₃ : x₁ ≠ x₃) : lam = 1 / (4 * qSecondDividedDiff x₁ e₁ x₂ e₂ x₃ e₃) := by
  sorry

/-- AUX decision witnesses of the plan's `decide`-checkable layer (positive + negative control).
The delivered proofs use `norm_num` with an `abs`-free normal form of the defect: `by decide` cannot
close ℚ goals containing `/`-literals in this toolchain, and `native_decide` is banned by the
contract (kernel evidence: `theories/BEP/probes/bep-api-rat.lean`). -/
theorem qConformsWindow_witness : qConformsWindow 1 (1 / 4) 0 := by
  sorry

theorem qConformsWindow_negativeControl : ¬ qConformsWindow 1 (1 / 16) 1 := by
  sorry


end Rat

/-! ## B5b — instance verdicts (`PhotoLean/BEP/Instances.lean`; plan §8.2)

Every row is a kernel computation in ℚ (the `norm_num` domain calibrated in
`theories/BEP/probes/bep-api-instances.lean`: `unfold …; norm_num`, decimal literals included); the
ℝ spellings follow through the B5a transfer lemmas. Provenance is `model-constructed` for I1–I10 and
`literature` for I11/I12, whose numbers are the sources' own **kcal/mol** values quoted verbatim
from `theories/BEP/LITERATURE.md` §R1.10 (locus in each docstring, all `first-hand`), with the
model's `x = -ΔG°` sign convention applied explicitly. Each verdict is a statement about the model
family *instantiated by those numbers*, never about the experiment.

The ℚ-layer declarations live in `PhotoLean.BEP.Rat`, hence the `Rat.` qualification — the sibling
layout of `PhotoLean/Hammond/Instances.lean`. Family **F4** of §R1.10 (Table 2, PE column) prints
only family aggregates (mean `λ̂`, range, curvature, fit, R²) and no per-row `(x, Ea)` pairs, so no
statement of this block can be built on it; the gap is recorded in `proofs/API-NOTES.md` and must
not be filled by inventing rows. -/

/-! ### I1–I10 — model-constructed families -/

/-- I1: thermoneutral family `λ = 2`, `x = 0` (`model-constructed`). -/
theorem inst_I1_thermoneutral_zone : Rat.epQVerdict (2 : ℚ) 0 = Rat.EPQVerdict.conforming := by
  sorry

theorem inst_I1_thermoneutral_transfer : Rat.qTransfer (2 : ℚ) 0 = 1 / 2 := by
  sorry

theorem inst_I1_thermoneutral_conforms : Rat.qConformsWindow (2 : ℚ) (1 / 4) 0 := by
  sorry

/-- I2: mildly exergonic family `λ = 2`, `x = 1/2` (`model-constructed`). -/
theorem inst_I2_exergonic_zone : Rat.epQVerdict (2 : ℚ) (1 / 2) = Rat.EPQVerdict.conforming := by
  sorry

theorem inst_I2_exergonic_transfer : Rat.qTransfer (2 : ℚ) (1 / 2) = 3 / 8 := by
  sorry

theorem inst_I2_exergonic_conforms : Rat.qConformsWindow (2 : ℚ) (1 / 4) (1 / 2) := by
  sorry

/-- I3: mildly endergonic family `λ = 2`, `x = -1/2` (`model-constructed`). -/
theorem inst_I3_endergonic_zone : Rat.epQVerdict (2 : ℚ) (-(1 / 2)) = Rat.EPQVerdict.conforming := by
  sorry

theorem inst_I3_endergonic_transfer : Rat.qTransfer (2 : ℚ) (-(1 / 2)) = 5 / 8 := by
  sorry

theorem inst_I3_endergonic_conforms : Rat.qConformsWindow (2 : ℚ) (1 / 4) (1 / 2) := by
  sorry

/-- I4: forward barrierless limit `λ = 2`, `x = 2` (`model-constructed`). -/
theorem inst_I4_forwardLimit_zone : Rat.epQVerdict (2 : ℚ) 2 = Rat.EPQVerdict.boundary := by
  sorry

theorem inst_I4_forwardLimit_transfer : Rat.qTransfer (2 : ℚ) 2 = 0 := by
  sorry

/-- I4: the limit sits on the edge of the Evans–Polanyi band — the *open* regime `0 < α < 1` fails
there, so `EPRegime`-style conformance is not a closed condition. -/
theorem inst_I4_forwardLimit_boundary :
    ¬ (0 < Rat.qTransfer (2 : ℚ) 2 ∧ Rat.qTransfer (2 : ℚ) 2 < 1) := by
  sorry

/-- I5: reverse barrierless limit `λ = 2`, `x = -2` (`model-constructed`). -/
theorem inst_I5_reverseLimit_zone : Rat.epQVerdict (2 : ℚ) (-2) = Rat.EPQVerdict.boundary := by
  sorry

theorem inst_I5_reverseLimit_transfer : Rat.qTransfer (2 : ℚ) (-2) = 1 := by
  sorry

theorem inst_I5_reverseLimit_boundary :
    ¬ (0 < Rat.qTransfer (2 : ℚ) (-2) ∧ Rat.qTransfer (2 : ℚ) (-2) < 1) := by
  sorry

/-- I6: strongly exergonic, forward inverted region `λ = 2`, `x = 3`; α = -1/4 < 0
(`model-constructed`). -/
theorem inst_I6_inverted_zone : Rat.epQVerdict (2 : ℚ) 3 = Rat.EPQVerdict.subLinear := by
  sorry

theorem inst_I6_inverted_transfer : Rat.qTransfer (2 : ℚ) 3 = -(1 / 4) := by
  sorry

theorem inst_I6_inverted_notBounds :
    ¬ (0 ≤ Rat.qTransfer (2 : ℚ) 3 ∧ Rat.qTransfer (2 : ℚ) 3 ≤ 1) := by
  sorry

/-- I7: strongly endergonic, reverse inverted region `λ = 2`, `x = -3`; α = 5/4 > 1
(`model-constructed`). -/
theorem inst_I7_reverseInverted_zone : Rat.epQVerdict (2 : ℚ) (-3) = Rat.EPQVerdict.superLinear := by
  sorry

theorem inst_I7_reverseInverted_transfer : Rat.qTransfer (2 : ℚ) (-3) = 5 / 4 := by
  sorry

theorem inst_I7_reverseInverted_notBounds :
    ¬ (0 ≤ Rat.qTransfer (2 : ℚ) (-3) ∧ Rat.qTransfer (2 : ℚ) (-3) ≤ 1) := by
  sorry

/-- I8: degenerate family `λ = 0`, `x = 1` (`model-constructed`): the barrier collapses
(`qEact 0 1 = 0` by totalised division) and the coefficient takes its degenerate value. The I8 row of
plan §8.2 still prints `α = 0`, which belonged to the discarded transition-state body; the
**linear-response** body gives `1/2` (plan §4.2 #4). -/
theorem inst_I8_degenerate_zone : Rat.epQVerdict (0 : ℚ) 1 = Rat.EPQVerdict.degenerate := by
  sorry

theorem inst_I8_degenerate_exact : Rat.qEact (0 : ℚ) 1 = 0 := by
  sorry

theorem inst_I8_degenerate_transfer : Rat.qTransfer (0 : ℚ) 1 = 1 / 2 := by
  sorry

/-- I9: unphysical curvature `λ = -2`, `x = 1` (`model-constructed`). The Evans–Polanyi bounds are
**blind** to it (α = 3/4 ∈ [0,1]); the *sign* of the defect detects it. -/
theorem inst_I9_unphysical_zone : Rat.epQVerdict (-2 : ℚ) 1 = Rat.EPQVerdict.unphysical := by
  sorry

theorem inst_I9_unphysical_transfer : Rat.qTransfer (-2 : ℚ) 1 = 3 / 4 := by
  sorry

theorem inst_I9_unphysical_defect_negative : Rat.qBepDefect (-2 : ℚ) 1 = -(1 / 8) := by
  sorry

theorem inst_I9_unphysical_bounds_blind :
    0 ≤ Rat.qTransfer (-2 : ℚ) 1 ∧ Rat.qTransfer (-2 : ℚ) 1 ≤ 1 := by
  sorry

/-- I10: tolerance threshold `λ = 2`, `w = 1`: the window conforms at `tol = 1/8` and fails at
`tol = 1/16` (`w* = 2√(λ·tol)`; in the ℚ squared form the threshold is exactly `w^2 = 4*λ*tol`) -/
theorem inst_I10_threshold_conforms : Rat.qConformsWindow (2 : ℚ) (1 / 8) 1 := by
  sorry

theorem inst_I10_threshold_fails : ¬ Rat.qConformsWindow (2 : ℚ) (1 / 16) 1 := by
  sorry

/-! ### I11 — the first-hand literature families (`LITERATURE.md` §R1.10, kcal/mol, verbatim)

The Lean literals are the sources' printed kcal/mol values; the model's driving force is
`x = -ΔG°` (F5 prints a classical `ΔE`, so `x = -ΔE`, with the ΔE-vs-ΔG caveat of §R1.10.5).
`_alphaObs` uses the widest printed pair of the family, `_lamHat` two adjacent printed pairs, and
`_curvature_negative` three printed rows whose second divided difference is negative; the
falsification row is the λ-independent consequence. -/

/-- F1 — source: *Antioxidants* **15**(7), 840–860 (2026), DOI `10.3390/antiox15070868` (OA,
`PMC13405240`), "Computational Study of the Peroxyl Radical Scavenging Ability of Phenolic
Antioxidants"; locus: **Table 1**, "Water" columns, 298.15 K; status `first-hand`; reaction family:
f-HAT from a phenolic O–H to `•OOH`. Rows used (kcal/mol, verbatim): `16(2)` `ΔG° = -0.3`,
`ΔG‡ = 15.6`; `16(1)` `ΔG° = -0.9`, `ΔG‡ = 15.7`; `14(1)` `ΔG° = -2.3`, `ΔG‡ = 15.7`;
`12` `ΔG° = -4.9`, `ΔG‡ = 13.9`; `8` `ΔG° = -12.9`, `ΔG‡ = 8.8`. -/
theorem inst_I11_F1_alphaObs :
    Rat.qAlphaObs (0.3 : ℚ) 15.6 12.9 8.8 = 34 / 63 := by
  sorry

theorem inst_I11_F1_lamHat : Rat.qLamOfPair (0.3 : ℚ) 15.6 0.9 15.7 = 9 / 20 := by
  sorry

theorem inst_I11_F1_curvature_negative :
    Rat.qSecondDividedDiff (0.9 : ℚ) 15.7 2.3 15.7 4.9 13.9 = -(9 / 52) := by
  sorry

/-- F1: **no** positive-λ equal-curvature two-parabola law reproduces the three printed rows. -/
theorem inst_I11_F1_not_model_consistent :
    ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (0.9 : ℚ) 2.3 4.9 15.7 15.7 13.9 := by
  sorry

/-- F2 — same source and status as F1; locus: **Table 1**, "PE" (pentyl ethanoate) columns. Rows
used (kcal/mol, verbatim): `16(2)` `ΔG° = +1.0`, `ΔG‡ = 14.0`; `13` `ΔG° = -2.2`, `ΔG‡ = 13.3`;
`2` `ΔG° = -4.6`, `ΔG‡ = 10.0`; `10` `ΔG° = -14.3`, `ΔG‡ = 5.1`. -/
theorem inst_I11_F2_alphaObs :
    Rat.qAlphaObs (-(1.0) : ℚ) 14.0 14.3 5.1 = 89 / 153 := by
  sorry

theorem inst_I11_F2_lamHat : Rat.qLamOfPair (-(1.0) : ℚ) 14.0 2.2 13.3 = 16 / 15 := by
  sorry

theorem inst_I11_F2_curvature_negative :
    Rat.qSecondDividedDiff (-(1.0) : ℚ) 14.0 2.2 13.3 4.6 10.0 = -(185 / 896) := by
  sorry

/-- F2: falsification (the PE column of the same paper is inconsistent for a *different* reason than
the water column — the family must be indexed by solvent as well as by the reacting pair). -/
theorem inst_I11_F2_not_model_consistent :
    ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (-(1.0) : ℚ) 2.2 4.6 14.0 13.3 10.0 := by
  sorry

/-- F3 — same source and status as F1; locus: **Table 2**, "Water" columns (`•OOCH₃` as the
abstracting radical). Rows used (kcal/mol, verbatim): `16(1)` `ΔG° = +0.8`, `ΔG‡ = 15.6`;
`19(2)` `ΔG° = +3.6`, `ΔG‡ = 17.7`; `1` `ΔG° = -7.1`, `ΔG‡ = 11.0`; `7` `ΔG° = -9.9`,
`ΔG‡ = 7.3`. -/
theorem inst_I11_F3_alphaObs :
    Rat.qAlphaObs (-(0.8) : ℚ) 15.6 9.9 7.3 = 83 / 107 := by
  sorry

theorem inst_I11_F3_lamHat : Rat.qLamOfPair (-(0.8) : ℚ) 15.6 (-(3.6)) 17.7 = 22 / 5 := by
  sorry

theorem inst_I11_F3_curvature_negative :
    Rat.qSecondDividedDiff (-(0.8) : ℚ) 15.6 7.1 11.0 9.9 7.3 = -(8175 / 118342) := by
  sorry

/-- F3: falsification. -/
theorem inst_I11_F3_not_model_consistent :
    ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (-(0.8) : ℚ) 7.1 9.9 15.6 11.0 7.3 := by
  sorry

/-- F5 — source: *Chem. Sci.* **6**(10), 5866–5881 (2015), DOI `10.1039/c5sc01848j` (OA,
`PMC5950756`); locus: **Table 1**, row `CCSD(T)-F12a/jun-cc-pVTZ`; status `first-hand`; reaction
family: H abstraction from the five distinct C–H sites of 2-butanol by `•OOH`. The table prints a
**classical** reaction energy `ΔE` and forward barrier `V‡f` (kcal/mol, verbatim) — an energy, not a
Gibbs energy, so the §R1.10.5 `ΔE`-vs-`ΔG` caveat applies to every row. Rows used: `R2`
`7.62 / 12.38`; `R3` `13.14 / 17.57`; `R4` `14.56 / 17.47`; `R1` `15.80 / 20.32`; `R5`
`19.82 / 21.72`. -/
theorem inst_I11_F5_alphaObs :
    Rat.qAlphaObs (-(7.62) : ℚ) 12.38 (-(19.82)) 21.72 = 467 / 610 := by
  sorry

theorem inst_I11_F5_lamHat :
    Rat.qLamOfPair (-(7.62) : ℚ) 12.38 (-(13.14)) 17.57 = 7958 / 675 := by
  sorry

theorem inst_I11_F5_curvature_negative :
    Rat.qSecondDividedDiff (-(14.56) : ℚ) 17.47 (-(15.8)) 20.32 (-(19.82)) 21.72 =
      -(1215125 / 3277506) := by
  sorry

/-- F5: falsification. -/
theorem inst_I11_F5_not_model_consistent :
    ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (-(14.56) : ℚ) (-(15.8)) (-(19.82)) 17.47 20.32 21.72 := by
  sorry

/-! ### I12 — the summary, and non-vacuity of the instance layer -/

/-- I12 (plan §8.2): for each of the four families with per-row data, the affine (BEP) side is a
decent description — the observed two-point slope lies strictly inside `(0,1)` — while the family's
second divided difference is negative, so **no** positive-λ equal-curvature two-parabola law
reproduces those printed rows. This is the falsification shape the plan asks for
(`¬ ∃ lam : ℚ, qModelConsistent3 lam …`) applied per family. -/
theorem inst_I12_affine_conforms_model_refuted :
    (0 < Rat.qAlphaObs (0.3 : ℚ) 15.6 12.9 8.8 ∧
        Rat.qAlphaObs (0.3 : ℚ) 15.6 12.9 8.8 < 1 ∧
        ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (0.9 : ℚ) 2.3 4.9 15.7 15.7 13.9) ∧
      (0 < Rat.qAlphaObs (-(1.0) : ℚ) 14.0 14.3 5.1 ∧
        Rat.qAlphaObs (-(1.0) : ℚ) 14.0 14.3 5.1 < 1 ∧
        ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (-(1.0) : ℚ) 2.2 4.6 14.0 13.3 10.0) ∧
      (0 < Rat.qAlphaObs (-(0.8) : ℚ) 15.6 9.9 7.3 ∧
        Rat.qAlphaObs (-(0.8) : ℚ) 15.6 9.9 7.3 < 1 ∧
        ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (-(0.8) : ℚ) 7.1 9.9 15.6 11.0 7.3) ∧
      (0 < Rat.qAlphaObs (-(7.62) : ℚ) 12.38 (-(19.82)) 21.72 ∧
        Rat.qAlphaObs (-(7.62) : ℚ) 12.38 (-(19.82)) 21.72 < 1 ∧
        ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (-(14.56) : ℚ) (-(15.8)) (-(19.82)) 17.47 20.32 21.72) := by
  sorry

/-- Non-vacuity of the instance layer (plan §8.2, last requirement): a conforming verdict, a
non-conforming verdict, a conforming window and a failing window all exist. -/
theorem inst_nonvacuous :
    (∃ lam x : ℚ, Rat.epQVerdict lam x = Rat.EPQVerdict.conforming) ∧
      (∃ lam x : ℚ, Rat.epQVerdict lam x = Rat.EPQVerdict.subLinear) ∧
      (∃ lam tol w : ℚ, Rat.qConformsWindow lam tol w) ∧
      (∃ lam tol w : ℚ, ¬ Rat.qConformsWindow lam tol w) := by
  sorry

end BEP

end PhotoLean
