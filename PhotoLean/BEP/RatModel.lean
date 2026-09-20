/-
PhotoLean.BEP.RatModel — B5a: the computable rational decision layer of the BEP theory.

**Statement authority**: the B5a block of `theories/BEP/probes/bep-statement-skeleton.lean`
(plan §8.1). Every declaration below matches that block word for word, and every declaration of
that block is delivered here. The file was calibrated first in
`theories/BEP/probes/bep-prover_c-scratch.lean` (0 error / 0 warning) before delivery.

**Why a ℚ copy**: the order on `ℝ` goes through `Classical` and is not computable, so "which BEP
regime a given family point sits in" cannot be computed by the kernel over `ℝ`. Over `ℚ` both the
order and the equality are decidable, so the evidence chain of the instance layer (B5b) is: kernel
computation of the rational verdict (`norm_num`) → the transfer lemmas `qX_cast` below → the ℝ
theory of `PhotoLean/BEP/Basic.lean`. `decide` alone cannot close the target goals of this file: it
reduces only for division-free `ℚ` literals, while `qEact`, `qTransfer`, `qConformsWindow` and
`qLamOfPair` all divide (measured failures: `theories/BEP/probes/bep-api-rat.lean`,
`proofs/API-NOTES.md` §"BEP round"); `native_decide` is banned by the axiom discipline
(`Lean.ofReduceBool` is not in `ALLOWED_AXIOMS`).

**Two corrections carried by this layer** (kernel counterexamples from the Sprint-0 risk probe,
plan §8.1 and §11; the forms below are the corrected ones):
* the two-point solver `qLamOfPair` uses the numerator `x₂² - x₁²`; the literal `x₁² - x₂²` pairs a
  numerator and a denominator of opposite sign and returns `-λ` (counterexample `λ=2, x₁=0, x₂=1`,
  `theories/BEP/probes/bep-api-rat.lean`);
* `qLamOfPair_reconstructs` carries the explicit premise `lam ≠ 0`; at `λ = 0` the totalised
  division `y / 0 = 0` makes `qEact 0 x` constantly `0`, so model data stop implying the solver's
  linear relation (counterexample `λ=0, x₁=0, x₂=1`, denominator `2`, solver value `1/2 ≠ 0`).
Without both corrections the reconstruction theorem is false as written; neither premise is hidden
in a definition.

**AUX ℝ twins**: the cast lemmas of the two-point data layer name `alphaObs` / `lamOfPair` as their
transfer targets. Neither is declared by any delivered module — `PhotoLean/BEP/Basic.lean` is
complete at 17 defs + 1 inductive and has neither, and plan §12 assigns no module to them — so they
are reproduced here verbatim from the skeleton's AUX block, at `PhotoLean.BEP.*` exactly as in the
authority. If they are ever moved upstream, these two definitions must be deleted in the same commit
or the build fails on a duplicate declaration.

Every physical premise (`lam ≠ 0`, `0 < lam`, `0 < tol`, `h ≠ 0`, `x₁ ≠ x₂`, `hden ≠ 0`) is an
explicit hypothesis of the statement that needs it; nothing is hidden in a definition. There is no
unproved placeholder and no custom axiom anywhere in this file. Imports: `PhotoLean.BEP.Basic` +
Mathlib only — B5a is deliberately independent of B2/B3 (plan §9).

Acceptance (contract `proofs/ENGINE.yml`, plan §10):
  proofs/scripts/lake build PhotoLean.BEP.RatModel
  proofs/scripts/check.sh --strict PhotoLean.BEP.RatModel
  proofs/scripts/axioms.sh PhotoLean.BEP.RatModel PhotoLean.BEP.Rat.<theorem>
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

end Rat

end BEP

end PhotoLean
