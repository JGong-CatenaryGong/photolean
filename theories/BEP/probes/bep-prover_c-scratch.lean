/-
Scratch calibration for milestone B5a (`PhotoLean/BEP/RatModel.lean`) — owner `prover_c`.

This probe lives OUTSIDE `SOURCE_DIRS` (the strict scan range), as the engine's statement-first rule
requires (plan §10.5). Its body is the intended content of the delivered file declaration for
declaration, so delivery is a verbatim transcription. Running:
  proofs/scripts/lake env lean theories/BEP/probes/bep-prover_c-scratch.lean

Statement authority: the B5a block of `theories/BEP/probes/bep-statement-skeleton.lean`.
Two ℝ AUX twins (`alphaObs`, `lamOfPair`) are defined here because the skeleton's cast lemmas
`qAlphaObs_cast` / `qLamOfPair_cast` name them as transfer targets and **no delivered module
declares them** (`PhotoLean/BEP/Basic.lean` has neither; the plan's B1 inventory is complete at
17 defs + 1 inductive). They are reproduced verbatim from the skeleton's AUX block.
-/
import Mathlib
import PhotoLean.BEP.Basic

namespace PhotoLean

namespace BEP

/-! ### AUX — ℝ observation layer (transfer targets of the B5a cast lemmas) -/

/-- Two-point α observable: the finite-difference slope measured from two barrier data points. -/
noncomputable def alphaObs (x₁ ea₁ x₂ ea₂ : ℝ) : ℝ := (ea₁ - ea₂) / (x₂ - x₁)

/-- Two-point reorganization-energy estimator on the real side (the form the ℚ solver
`qLamOfPair` casts to). -/
noncomputable def lamOfPair (x₁ ea₁ x₂ ea₂ : ℝ) : ℝ :=
  (x₂ ^ 2 - x₁ ^ 2) / (2 * (x₂ - x₁) - 4 * (ea₁ - ea₂))

namespace Rat

/-! ## Definitions (plan §8.1) -/

/-- Rational forward activation barrier. -/
def qEact (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- Rational BEP line. -/
def qBepLine (lam x : ℚ) : ℚ := lam / 4 - x / 2

/-- Rational exact violation of the BEP line law. -/
def qBepDefect (lam x : ℚ) : ℚ := qEact lam x - qBepLine lam x

/-- Rational BEP / Brønsted / Leffler coefficient (linear-response form). -/
def qTransfer (lam x : ℚ) : ℚ := 1 / 2 - x / (2 * lam)

/-- Rational coefficient of the reverse direction. -/
def qReverseTransfer (lam x : ℚ) : ℚ := 1 / 2 + x / (2 * lam)

/-- Rational observable BEP secant over the window `[x, x+h]`. -/
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

/-! ## Model-consistency block (plan §8.1 amendment, literature round 1c, lead 2026-09-20) -/

/-- Second divided difference of three family points: the model's curvature witness. -/
def qSecondDividedDiff (x₁ e₁ x₂ e₂ x₃ e₃ : ℚ) : ℚ :=
  ((e₃ - e₂) / (x₃ - x₂) - (e₂ - e₁) / (x₂ - x₁)) / (x₃ - x₁)

/-- Three family points are consistent with the equal-curvature two-parabola model. -/
def qModelConsistent3 (lam x₁ x₂ x₃ e₁ e₂ e₃ : ℚ) : Prop :=
  0 < lam ∧ e₁ = qEact lam x₁ ∧ e₂ = qEact lam x₂ ∧ e₃ = qEact lam x₃

/-! ## Theorems of plan §8.1 -/

theorem qEact_cast (lam x : ℚ) : ((qEact lam x : ℚ) : ℝ) = eact (lam : ℝ) (x : ℝ) := by
  unfold qEact eact
  push_cast
  ring

theorem qBepLine_cast (lam x : ℚ) :
    ((qBepLine lam x : ℚ) : ℝ) = bepLine (lam : ℝ) (x : ℝ) := by
  unfold qBepLine bepLine
  push_cast
  ring

theorem qBepDefect_cast (lam x : ℚ) :
    ((qBepDefect lam x : ℚ) : ℝ) = bepDefect (lam : ℝ) (x : ℝ) := by
  unfold qBepDefect bepDefect qEact qBepLine eact bepLine
  push_cast
  ring

theorem qTransfer_cast (lam x : ℚ) :
    ((qTransfer lam x : ℚ) : ℝ) = transfer (lam : ℝ) (x : ℝ) := by
  unfold qTransfer transfer
  push_cast
  ring

set_option linter.unusedVariables false in
/-- The `≠ 0` premise is the mathematical premise of a finite difference and is *not* consumed by
the cast: `Rat.cast_div` moves the cast through division unconditionally. -/
theorem qSecSlope_cast {lam x h : ℚ} (hh : h ≠ 0) :
    ((qSecSlope lam x h : ℚ) : ℝ) = secSlope (lam : ℝ) (x : ℝ) (h : ℝ) := by
  unfold qSecSlope secSlope qEact eact
  push_cast
  ring

set_option linter.unusedVariables false in
/-- The two-point observable casts to the ℝ twin of the skeleton's AUX layer; `x₂ ≠ x₁` is the
statement-authority premise and is not consumed by the cast. -/
theorem qAlphaObs_cast {x₁ ea₁ x₂ ea₂ : ℚ} (h : x₂ ≠ x₁) :
    ((qAlphaObs x₁ ea₁ x₂ ea₂ : ℚ) : ℝ) = alphaObs (x₁ : ℝ) (ea₁ : ℝ) (x₂ : ℝ) (ea₂ : ℝ) := by
  unfold qAlphaObs alphaObs
  push_cast
  ring

set_option linter.unusedVariables false in
/-- The two-point λ solver casts to the ℝ twin; `x₁ ≠ x₂` is the statement-authority premise and is
not consumed by the cast. -/
theorem qLamOfPair_cast {x₁ ea₁ x₂ ea₂ : ℚ} (h : x₁ ≠ x₂) :
    ((qLamOfPair x₁ ea₁ x₂ ea₂ : ℚ) : ℝ) =
      lamOfPair (x₁ : ℝ) (ea₁ : ℝ) (x₂ : ℝ) (ea₂ : ℝ) := by
  unfold qLamOfPair lamOfPair
  push_cast
  ring

/-- Plan §8.1: ℚ mean-value identity — the secant over `[x, x+h]` is the coefficient at the
midpoint `x + h/2`. -/
theorem qSecSlope_eq_qTransfer_mid {lam : ℚ} (hlam : lam ≠ 0) {x h : ℚ} (hh : h ≠ 0) :
    qSecSlope lam x h = qTransfer lam (x + h / 2) := by
  unfold qSecSlope qTransfer qEact
  field_simp
  ring

/-- Plan §8.1: two-point data → structural coefficient (the observed slope is the coefficient at
the data midpoint). -/
theorem qAlphaObs_eq_qTransfer_mid {lam x₁ x₂ : ℚ} (hlam : lam ≠ 0) (h : x₁ ≠ x₂) :
    qAlphaObs x₁ (qEact lam x₁) x₂ (qEact lam x₂) = qTransfer lam ((x₁ + x₂) / 2) := by
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hkey : qEact lam x₁ - qEact lam x₂
      = (x₂ - x₁) * (2 * lam - x₁ - x₂) / (4 * lam) := by
    unfold qEact
    field_simp
    ring
  unfold qAlphaObs qTransfer
  rw [hkey]
  field_simp
  ring

set_option linter.unusedVariables false in
/-- Plan §8.1: two model-consistent data points determine λ uniquely. The premise `lam ≠ 0` is
necessary (at `λ = 0` the totalised division makes `qEact 0 x` constant, so the data stop implying
the solver's linear relation; kernel counterexample in `bep-api-rat.lean`). `hx` is the
statement-authority premise of a two-point estimator and is not consumed (the denominator premise
already carries the non-degeneracy); the linter is switched off for this declaration only. -/
theorem qLamOfPair_reconstructs {lam x₁ ea₁ x₂ ea₂ : ℚ} (hlam : lam ≠ 0) (hx : x₁ ≠ x₂)
    (hden : 2 * (x₂ - x₁) - 4 * (ea₁ - ea₂) ≠ 0) (h₁ : ea₁ = qEact lam x₁)
    (h₂ : ea₂ = qEact lam x₂) : qLamOfPair x₁ ea₁ x₂ ea₂ = lam := by
  subst h₁
  subst h₂
  unfold qLamOfPair
  rw [div_eq_iff hden]
  unfold qEact at *
  field_simp
  ring

set_option linter.unusedVariables false in
/-- The ℝ-side counterpart of the reconstruction theorem (skeleton AUX, lead 2026-09-20). -/
theorem lamOfPair_reconstructs {lam x₁ ea₁ x₂ ea₂ : ℝ} (hlam : lam ≠ 0) (hx : x₁ ≠ x₂)
    (hden : 2 * (x₂ - x₁) - 4 * (ea₁ - ea₂) ≠ 0) (h₁ : ea₁ = eact lam x₁)
    (h₂ : ea₂ = eact lam x₂) : lamOfPair x₁ ea₁ x₂ ea₂ = lam := by
  subst h₁
  subst h₂
  unfold lamOfPair
  rw [div_eq_iff hden]
  unfold eact at *
  field_simp
  ring

/-- Plan §8.1: the squared conformance predicate is the radius condition — the `↔` that makes the
kernel computation binding for the real tolerance theorem. -/
theorem qConformsWindow_iff_radius_sq {lam tol w : ℚ} (hlam : 0 < lam) (htol : 0 < tol)
    (hw : 0 ≤ w) : qConformsWindow lam tol w ↔ ((w : ℚ) : ℝ) ≤ bepRadius (lam : ℝ) (tol : ℝ) := by
  have hwR : (0 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have h4nonneg : (0 : ℝ) ≤ 4 * ((lam : ℝ) * (tol : ℝ)) := by positivity
  have hsqrt4 : Real.sqrt (4 * ((lam : ℝ) * (tol : ℝ)))
      = 2 * Real.sqrt ((lam : ℝ) * (tol : ℝ)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hreal : (w : ℝ) ≤ 2 * Real.sqrt ((lam : ℝ) * (tol : ℝ))
      ↔ (w : ℝ) ^ 2 ≤ 4 * (lam : ℝ) * (tol : ℝ) := by
    rw [← hsqrt4, Real.le_sqrt hwR h4nonneg]
    ring_nf
  have hq : ((w : ℝ) ^ 2 ≤ 4 * (lam : ℝ) * (tol : ℝ)) ↔ w ^ 2 ≤ 4 * lam * tol := by
    have h1 : ((w ^ 2 : ℚ) : ℝ) = (w : ℝ) ^ 2 := by push_cast; ring
    have h2 : ((4 * lam * tol : ℚ) : ℝ) = 4 * (lam : ℝ) * (tol : ℝ) := by push_cast; ring
    rw [← h1, ← h2, Rat.cast_le]
  unfold qConformsWindow bepRadius
  rw [hreal, hq]
  exact ⟨fun h => h.2.2, fun h => ⟨hlam, htol, h⟩⟩

/-! ### The verdict cascade (plan §8.1) -/

theorem epQVerdict_conforming_iff {lam x : ℚ} (hlam : 0 < lam) :
    epQVerdict lam x = EPQVerdict.conforming ↔ 0 < qTransfer lam x ∧ qTransfer lam x < 1 := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hat : qTransfer lam lam = 0 := by
    unfold qTransfer
    field_simp
  have hatneg : qTransfer lam (-lam) = 1 := by
    unfold qTransfer
    field_simp
    ring
  unfold epQVerdict
  rw [if_neg hlam', if_neg (by linarith : ¬ lam < 0)]
  by_cases h2 : x = lam
  · rw [if_pos h2]
    exact iff_of_false (by decide) (by
      rintro ⟨h1, -⟩
      rw [h2, hat] at h1
      exact absurd h1 (lt_irrefl 0))
  rw [if_neg h2]
  by_cases h3 : x = -lam
  · rw [if_pos h3]
    exact iff_of_false (by decide) (by
      rintro ⟨-, h2'⟩
      rw [h3, hatneg] at h2'
      exact absurd h2' (lt_irrefl 1))
  rw [if_neg h3]
  by_cases h4 : 0 < qTransfer lam x ∧ qTransfer lam x < 1
  · rw [if_pos h4]
    exact iff_of_true rfl h4
  · rw [if_neg h4]
    by_cases h5 : 1 < qTransfer lam x
    · rw [if_pos h5]
      exact iff_of_false (by decide) (by rintro ⟨-, hlt⟩; linarith)
    · rw [if_neg h5]
      exact iff_of_false (by decide) (fun h => h4 h)

theorem epQVerdict_boundary_iff {lam x : ℚ} (hlam : 0 < lam) :
    epQVerdict lam x = EPQVerdict.boundary ↔ x = lam ∨ x = -lam := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  unfold epQVerdict
  rw [if_neg hlam', if_neg (by linarith : ¬ lam < 0)]
  by_cases h2 : x = lam
  · rw [if_pos h2]
    exact iff_of_true rfl (Or.inl h2)
  rw [if_neg h2]
  by_cases h3 : x = -lam
  · rw [if_pos h3]
    exact iff_of_true rfl (Or.inr h3)
  rw [if_neg h3]
  by_cases h4 : 0 < qTransfer lam x ∧ qTransfer lam x < 1
  · rw [if_pos h4]
    exact iff_of_false (by decide) (by rintro (h | h); exact h2 h; exact h3 h)
  · rw [if_neg h4]
    by_cases h5 : 1 < qTransfer lam x
    · rw [if_pos h5]
      exact iff_of_false (by decide) (by rintro (h | h); exact h2 h; exact h3 h)
    · rw [if_neg h5]
      exact iff_of_false (by decide) (by rintro (h | h); exact h2 h; exact h3 h)

theorem epQVerdict_superLinear_iff {lam x : ℚ} (hlam : 0 < lam) :
    epQVerdict lam x = EPQVerdict.superLinear ↔ 1 < qTransfer lam x := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hat : qTransfer lam lam = 0 := by
    unfold qTransfer
    field_simp
  have hatneg : qTransfer lam (-lam) = 1 := by
    unfold qTransfer
    field_simp
    ring
  unfold epQVerdict
  rw [if_neg hlam', if_neg (by linarith : ¬ lam < 0)]
  by_cases h2 : x = lam
  · rw [if_pos h2]
    exact iff_of_false (by decide) (by
      rintro h
      rw [h2, hat] at h
      exact absurd h (by norm_num))
  rw [if_neg h2]
  by_cases h3 : x = -lam
  · rw [if_pos h3]
    exact iff_of_false (by decide) (by
      rintro h
      rw [h3, hatneg] at h
      exact absurd h (lt_irrefl 1))
  rw [if_neg h3]
  by_cases h4 : 0 < qTransfer lam x ∧ qTransfer lam x < 1
  · rw [if_pos h4]
    exact iff_of_false (by decide) (by rintro h; linarith [h4.2])
  · rw [if_neg h4]
    by_cases h5 : 1 < qTransfer lam x
    · rw [if_pos h5]
      exact iff_of_true rfl h5
    · rw [if_neg h5]
      exact iff_of_false (by decide) h5

theorem epQVerdict_subLinear_iff {lam x : ℚ} (hlam : 0 < lam) :
    epQVerdict lam x = EPQVerdict.subLinear ↔ qTransfer lam x < 0 := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hat : qTransfer lam lam = 0 := by
    unfold qTransfer
    field_simp
  have hatneg : qTransfer lam (-lam) = 1 := by
    unfold qTransfer
    field_simp
    ring
  unfold epQVerdict
  rw [if_neg hlam', if_neg (by linarith : ¬ lam < 0)]
  by_cases h2 : x = lam
  · rw [if_pos h2]
    exact iff_of_false (by decide) (by
      rw [h2, hat]
      exact lt_irrefl 0)
  rw [if_neg h2]
  by_cases h3 : x = -lam
  · rw [if_pos h3]
    exact iff_of_false (by decide) (by
      rw [h3, hatneg]
      norm_num)
  rw [if_neg h3]
  have hne0' : qTransfer lam x ≠ 0 := by
    intro hz
    unfold qTransfer at hz
    field_simp at hz
    exact h2 (by linarith)
  have hne1 : qTransfer lam x ≠ 1 := by
    intro hz
    unfold qTransfer at hz
    field_simp at hz
    exact h3 (by linarith)
  by_cases h4 : 0 < qTransfer lam x ∧ qTransfer lam x < 1
  · rw [if_pos h4]
    exact iff_of_false (by decide) (by rintro h; linarith [h4.1])
  · rw [if_neg h4]
    by_cases h5 : 1 < qTransfer lam x
    · rw [if_pos h5]
      exact iff_of_false (by decide) (by rintro h; linarith)
    · rw [if_neg h5]
      constructor
      · intro _
        have hα : qTransfer lam x ≤ 0 := by
          by_contra hc
          exact h4 ⟨lt_of_not_ge hc, lt_of_le_of_ne (le_of_not_gt h5) hne1⟩
        exact lt_of_le_of_ne hα hne0'
      · intro _
        rfl

/-! ### AUX decision witnesses (positive + negative control) -/

theorem qConformsWindow_witness : qConformsWindow 1 (1 / 4) 0 := by
  unfold qConformsWindow
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num

theorem qConformsWindow_negativeControl : ¬ qConformsWindow 1 (1 / 16) 1 := by
  unfold qConformsWindow
  rintro ⟨-, -, h⟩
  norm_num at h

/-! ### Model-consistency theorems (plan §8.1 amendment)

The three abscissae must be **pairwise distinct** (`h₁₂`, `h₂₃`, `h₁₃`): at `x₂ = x₃` the totalised
division makes the first inner quotient `0`, the second divided difference degenerates to the
first-order slope and the identity `qSecondDividedDiff = 1/(4λ)` fails. The kernel counterexamples of
the un-premised forms are recorded in the probe-only section at the end of
`theories/BEP/probes/bep-prover_c-scratch.lean`. -/

theorem qSecondDividedDiff_model {lam x₁ x₂ x₃ : ℚ} (hlam : lam ≠ 0) (h₁₂ : x₁ ≠ x₂)
    (h₂₃ : x₂ ≠ x₃) (h₁₃ : x₁ ≠ x₃) :
    qSecondDividedDiff x₁ (qEact lam x₁) x₂ (qEact lam x₂) x₃ (qEact lam x₃) = 1 / (4 * lam) := by
  have hd12 : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁₂)
  have hd23 : x₃ - x₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₂₃)
  have hd13 : x₃ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁₃)
  have h4 : (4 : ℚ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
  unfold qSecondDividedDiff qEact
  field_simp
  ring

theorem qModelConsistent3_curvature_pos {lam x₁ x₂ x₃ e₁ e₂ e₃ : ℚ}
    (h : qModelConsistent3 lam x₁ x₂ x₃ e₁ e₂ e₃) (h₁₂ : x₁ ≠ x₂) (h₂₃ : x₂ ≠ x₃)
    (h₁₃ : x₁ ≠ x₃) : 0 < qSecondDividedDiff x₁ e₁ x₂ e₂ x₃ e₃ := by
  obtain ⟨hlam, h₁, h₂, h₃⟩ := h
  rw [h₁, h₂, h₃, qSecondDividedDiff_model (ne_of_gt hlam) h₁₂ h₂₃ h₁₃]
  positivity

theorem qModelConsistent3_lam_eq {lam x₁ x₂ x₃ e₁ e₂ e₃ : ℚ}
    (h : qModelConsistent3 lam x₁ x₂ x₃ e₁ e₂ e₃) (h₁₂ : x₁ ≠ x₂) (h₂₃ : x₂ ≠ x₃)
    (h₁₃ : x₁ ≠ x₃) : lam = 1 / (4 * qSecondDividedDiff x₁ e₁ x₂ e₂ x₃ e₃) := by
  obtain ⟨hlam, h₁, h₂, h₃⟩ := h
  rw [h₁, h₂, h₃, qSecondDividedDiff_model (ne_of_gt hlam) h₁₂ h₂₃ h₁₃]
  field_simp

end Rat

end BEP

end PhotoLean

/-! ## API calibration used by the proofs above (probe-only, not part of the delivered file) -/

#check @Real.le_sqrt
#check @Real.sq_sqrt
#check @Real.sqrt_sq
#check @Real.sqrt_mul
#check @Real.sqrt_nonneg
#check @sq_le_sq
#check @Rat.cast_le
#check @Rat.cast_pow
#check @Rat.cast_div
#check @Rat.cast_mul
#check @Rat.cast_sub
#check @Rat.cast_inj
#check @Rat.cast_lt
#check @Rat.cast_pos
#check @Rat.instDecidableLt
#check @Rat.instDecidableLe

/-! ## Probe-only refutation witnesses (statement defects of the handed-over amendment block)

The three model-consistency statements as first handed over (without `x₃ ≠ x₂`) are **false**: with
`λ = 1`, `x₁ = 0`, `x₂ = x₃ = 2` every handed hypothesis holds (`1 ≠ 0`, `2 ≠ 0`, `2 ≠ 0`, and the
data `1/4, 1/4, 1/4` are the true model barriers), yet the second divided difference is `0` while
`1/(4λ) = 1/4`. -/

namespace PhotoLean.BEP.Rat

/-- Refutation of the handed form of `qSecondDividedDiff_model` (missing `x₃ ≠ x₂`). -/
example : qSecondDividedDiff 0 (qEact 1 0) 2 (qEact 1 2) 2 (qEact 1 2) ≠ 1 / (4 * 1) := by
  norm_num [qSecondDividedDiff, qEact]

/-- The hypotheses of that refutation are satisfiable (non-vacuity of the counterexample): the data
`1/4, 1/4, 1/4` really are the model barriers, so `qModelConsistent3` holds for them. -/
example : qModelConsistent3 1 0 2 2 (1 / 4) (1 / 4) (1 / 4) := by
  unfold qModelConsistent3
  refine ⟨by norm_num, ?_, ?_, ?_⟩ <;> norm_num [qEact]

/-- Refutation of the handed form of `qModelConsistent3_curvature_pos` (missing `x₃ ≠ x₂`). -/
example : ¬ (0 < qSecondDividedDiff 0 (1 / 4) 2 (1 / 4) 2 (1 / 4)) := by
  norm_num [qSecondDividedDiff]

/-- Refutation of the handed form of `qModelConsistent3_lam_eq` (missing `x₃ ≠ x₂`). -/
example : ¬ (1 = 1 / (4 * qSecondDividedDiff 0 (1 / 4) 2 (1 / 4) 2 (1 / 4))) := by
  norm_num [qSecondDividedDiff]

/-- The repaired statements are not vacuous: a non-degenerate model triple (`λ = 1`, `x = 0, 1, 2`)
satisfies the identity of the corrected `qSecondDividedDiff_model`. -/
example : qSecondDividedDiff 0 (qEact 1 0) 1 (qEact 1 1) 2 (qEact 1 2) = 1 / (4 * 1) := by
  norm_num [qSecondDividedDiff, qEact]

end PhotoLean.BEP.Rat

/-! ## Measured `decide` / `norm_num` / `native_decide` boundary (B5a round, verbatim)

The target goals of the delivered file are ℚ comparisons that contain division, so `by decide` cannot
close them and `norm_num` is the working recipe; `native_decide` is banned by the axiom discipline.
Measured on standalone probes with `proofs/scripts/lake env lean` (each item verbatim):

* `by decide` **works**: `(1 : ℚ) < 3`; `Rat.divInt 1 4 ≤ Rat.divInt 1 1`;
  `EPQVerdict.conforming ≠ EPQVerdict.boundary` (constructor distinctness from `deriving DecidableEq`);
  `epQVerdict 0 1 = EPQVerdict.degenerate`; `epQVerdict 1 1 = EPQVerdict.boundary`;
  `epQVerdict 1 (-1) = EPQVerdict.boundary` — the cascade reaches an `=`-guard before any division.
* `by decide` **fails** on `(1 : ℚ) / 2 ≤ 3 / 4`:
  ```
  tactic 'decide' failed for proposition
    1 / 2 ≤ 3 / 4
  since its 'Decidable' instance
    (1 / 2).instDecidableLe (3 / 4)
  did not reduce to 'isTrue' or 'isFalse'.
  After unfolding the instances 'instDecidableEqBool', 'Bool.decEq', 'Int.decLt',
  'Rat.instDecidableLe' and 'Int.decNonneg✝', reduction got stuck at the 'Decidable' instance
    match (3 / 4).blt (1 / 2), false with
  ```
* `by decide` **fails** on a `def`-headed goal before unfolding:
  `failed to synthesize Decidable (qConformsWindow 1 (1 / 4) 0)` (type-class search does not unfold a
  plain `def`).
* `by decide` **fails** on `epQVerdict 1 2 = EPQVerdict.subLinear`: the cascade reduces, but the
  `qTransfer` guard divides — `did not reduce to 'isTrue' or 'isFalse'`, stuck at
  `(epQVerdict 1 2).toCtorIdx.beq EPQVerdict.subLinear.toCtorIdx` after unfolding
  `decEqRat✝`, `instDecidableAnd`, `Rat.instDecidableLt`, `Int.decNonneg✝`, `instDecidableEqEPQVerdict`.
* `norm_num` **works** on the same goals (the B5b computation recipe):
  `norm_num [epQVerdict, qTransfer]` closes `epQVerdict 2 3 = EPQVerdict.subLinear`,
  `epQVerdict 2 1 = EPQVerdict.conforming`, `epQVerdict 2 2 = EPQVerdict.boundary`,
  `epQVerdict 0 1 = EPQVerdict.degenerate`, `epQVerdict (-2) 1 = EPQVerdict.unphysical`, and
  `norm_num [qLamOfPair, qEact]` closes `qLamOfPair 0 (qEact 2 0) 1 (qEact 2 1) = 2`;
  `unfold qConformsWindow; norm_num` closes both `qConformsWindow_witness` and its negative control.
* `by native_decide` closes `(1 : ℚ) < 3` but `#print axioms` reports
  `[propext, Lean.ofReduceBool]`, so any delivered use FAILs `axioms.sh`.

Two more measured failures of this round (tactic combinations, kept for the next worker):

* `field_simp` sometimes closes a field goal by itself; the trailing `ring` then reports
  `no goals to be solved` (measured on `qModelConsistent3_lam_eq` after the rewrite by
  `qSecondDividedDiff_model`, and on `transfer_at_lam`/`eact_at_lam` in the API probe).
* `field_simp at hz; linarith` does not turn a *negated equality* into a contradiction: on
  `h2 : ¬ x = lam, hz : lam - x = 0 ⊢ False` it reports `linarith failed to find a contradiction`.
  Close such leaves propositionally, `exact h2 (by linarith)`.
-/
