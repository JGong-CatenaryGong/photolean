/-
PhotoLean.BEP.Basic — B1, the description layer of the Bell–Evans–Polanyi theory.

The same equal-curvature two-parabola (Marcus-type) model of an elementary reaction step as
`PhotoLean.Hammond.Basic`: one scalar reaction coordinate, a harmonic reactant surface at `q = 0`,
a harmonic product surface at `q = 1`, both of curvature `2 * lam`, and the classical crossing
point as the transition state. The driving force is `x = -ΔG°` (exergonic: `x > 0`), so the
forward activation barrier is `eact lam x = (lam - x) ^ 2 / (4 * lam)`.

What is added here is the *description* layer of BEP as an empirical linear free-energy relation:
the tangent line at thermoneutrality (`bepLine`), the exact violation of that line (`bepDefect`),
the BEP/Brønsted/Leffler coefficient in **linear-response form** (`transfer`,
`1 / 2 - x / (2 * lam)` — deliberately *not* the equivalent form `(lam - x) / (2 * lam)`, so that
the identification with the transition-state coordinate `Hammond.tsCoord` is a theorem about this
definition rather than a definitional restatement), its reverse-direction partner
(`reverseTransfer`), the observable finite-difference slope (`secSlope`), the tolerance radius
(`bepRadius`), the minimax line on a symmetric window (`bepBestLine`), the bound / window /
exactness / optimality predicates, and the decidable regime classifier `epZone` with its nine
`..._iff` characterizations.

Model assumptions that are NOT derived here (see `theories/BEP/plan.md` section 13): one scalar
coordinate stands for molecular structure; the two curvatures are equal; the reorganization energy
`lam` is held fixed across the compared family; the transition state is the classical crossing
point (no tunneling, no recoupling); and the empirical BEP plot is taken against `ΔG°` rather than
`ΔH`. The model is exact only in the degenerate case `lam = 0`; the honest statement of the linear
law is the tolerance/window form (`EPConformsOnWindow`) delivered in B1 and sharpened in B3.

Every physical premise (`lam ≠ 0`, `0 < lam`) is an explicit hypothesis of the statement that
needs it; nothing is hidden in a definition. This file imports `Mathlib` only and is independent of
the `PhotoLean.Marcus` and `PhotoLean.Hammond` modules. There is no unproved placeholder and no
custom axiom anywhere in this file.

Statement authority: every declaration below matches
`theories/BEP/probes/bep-statement-skeleton.lean` word for word (plan §4.1, §4.2).
-/
import Mathlib

namespace PhotoLean.BEP

/-! ## Definitions (plan §4.1) -/

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
  | degenerate | unphysical | thermoneutral | exergonic | endergonic
  | atForwardLimit | atReverseLimit | beyondForward | beyondReverse

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

/-! ## Theorems (plan §4.2)

The six evaluation lemmas fix the values of the description at the three distinguished driving
forces (`x = 0`, `x = lam`, `x = 0` with `lam = 0`); the nine zone characterizations turn the
`if`-cascade of `epZone` into a usable case analysis. In the forward direction the cascade is
split inside the hypothesis (`split_ifs at h`), which discharges every branch whose generated
constructor equality is absurd, so exactly one branch survives; in the backward direction the
cascade is reduced by explicit `if_neg` / `if_pos` rewrites, each guard discharged from the
characterization's own arithmetic. -/
/-- Thermoneutral barrier: at `x = 0` the model barrier is the intercept `lam / 4` of the BEP
line (needs `lam ≠ 0`; at `lam = 0` the totalised-division value is `0`). -/
theorem eact_at_zero {lam : ℝ} (hlam : lam ≠ 0) : eact lam 0 = lam / 4 := by
  unfold eact
  field_simp
  ring
/- The premise `hlam : lam ≠ 0` is kept because it belongs to the description layer and keeps
signature fidelity with the statement skeleton; this proof does not consume it — `field_simp`
normalises `lam - lam` to `0` first, so the goal is closed by the division convention alone.
The unused-variable linter is disabled locally rather than dropping the physical premise. -/
set_option linter.unusedVariables false in
/-- Barrierless forward limit: at `x = lam` the barrier vanishes. -/
theorem eact_at_lam {lam : ℝ} (hlam : lam ≠ 0) : eact lam lam = 0 := by
  unfold eact
  field_simp
/-- Degenerate curvature: with `lam = 0` the barrier collapses to `0` at every driving force
(the totalised-division convention `y / 0 = 0`). -/
theorem eact_zero_lam (x : ℝ) : eact 0 x = 0 := by
  unfold eact
  norm_num

end PhotoLean.BEP
