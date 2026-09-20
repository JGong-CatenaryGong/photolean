/-
BEP milestone — API probe (topic A): real-field algebra on the BEP identities.

Scope. This probe answers, for each BEP identity that is pure field algebra,
(i) the exact tactic sequence that closes it with kernel evidence,
(ii) which hypotheses that sequence consumes, and (iii) whether a bare `ring` / `ring_nf`
(which never reads the context) suffices.

**Body correction of 2026-09-20 (lead / Sprint-0 risk probe, mirrored from `theories/BEP/plan.md`
§4.1).** The delivered `transfer` is the **linear-response** body `1/2 - x/(2*lam)`, NOT the
transition-state body `(lam - x)/(2*lam)`. The TS body is now the *theorem* `transfer_eq_tsCoord`;
its old identity proofs are kept below in the marked `DISCARDED body` section so that no prover
copies a recipe against the wrong definition. The probe-local `#check` list is unchanged.

Running:  proofs/scripts/lake env lean theories/BEP/probes/bep-api-algebra.lean
Status:   0 errors / 0 warnings.
-/
import Mathlib
import PhotoLean.Hammond.Basic
import PhotoLean.Marcus.Basic

namespace PhotoLean.BEP.ProbeAlgebra

/-! ## Local copies of the B1 definitions (verbatim from the plan §4.1 / statement skeleton) -/

/-- Equal-curvature two-parabola activation energy, driving force `x = -ΔG°`. -/
noncomputable def eact (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- The tangent (linear free-energy) line through the thermoneutral barrier. -/
noncomputable def bepLine (lam x : ℝ) : ℝ := lam / 4 - x / 2

/-- Defect of the barrier from the BEP line. -/
noncomputable def bepDefect (lam x : ℝ) : ℝ := eact lam x - bepLine lam x

/-- BEP/Brønsted/Leffler coefficient, **linear-response body** (authoritative). -/
noncomputable def transfer (lam x : ℝ) : ℝ := 1 / 2 - x / (2 * lam)

/-- Reverse-direction coefficient, linear-response body (authoritative). -/
noncomputable def reverseTransfer (lam x : ℝ) : ℝ := 1 / 2 + x / (2 * lam)

/-- Observable finite-difference slope of the barrier against the driving force. -/
noncomputable def secSlope (lam x h : ℝ) : ℝ := (eact lam x - eact lam (x + h)) / h

/-- The **discarded** transition-state body of the coefficient (Sprint-0 probe artefact). -/
noncomputable def transferTS (lam x : ℝ) : ℝ := (lam - x) / (2 * lam)

/-- One-step two-point α observable. -/
noncomputable def alphaObs (x₁ ea₁ x₂ ea₂ : ℝ) : ℝ := (ea₁ - ea₂) / (x₂ - x₁)

/-! ## `#check` — the names used by the recipes below -/

#check @div_eq_iff
#check @eq_div_iff
#check @div_mul_eq_mul_div
#check @pow_two
#check @sq_nonneg
#check @sq_pos_of_ne_zero
#check @div_nonneg
#check @div_pos
#check @div_le_div_of_nonneg_right
#check @div_le_div_of_nonneg_left
#check @div_le_div_iff₀
#check @div_le_div_iff_of_pos_right
#check @mul_le_mul_of_nonneg_left
#check @mul_le_mul_of_nonneg_right
#check @div_le_iff₀
#check @le_div_iff₀
#check @div_le_one
#check @one_div_le_one_div_of_le
#check @sub_ne_zero
#check @div_ne_zero
#check @pow_ne_zero
#check @mul_ne_zero
#check @two_ne_zero
#check @zero_div
#check @div_zero
#check @sub_zero
#check @abs_mul
#check @abs_div
#check @abs_sq
#check @sq_abs
#check @abs_pow

/-! ## Tactic availability (kernel evidence, not documentation) -/

/-- `ring` closes a genuine ring identity with no hypotheses. -/
example (a b : ℝ) : a * b - b * a = 0 := by ring

/-- `ring_nf` closes a genuine ring identity with no hypotheses. -/
example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring_nf

/-- `linarith` on a pure linear goal. -/
example (a b : ℝ) (h : a ≤ b) : a - 1 ≤ b + 2 := by linarith

/-- `nlinarith` needs its nonlinear hints to be *supplied*: the same goal fails for
`linarith` alone (the goal is not linear in `b`). -/
example (a b : ℝ) (h : 0 ≤ a) : 0 ≤ a * b ^ 2 := by nlinarith [sq_nonneg b]

/-- `positivity` discharges `0 < 4 * lam` from `0 < lam` in the local context. -/
example {lam : ℝ} (hlam : 0 < lam) : (0 : ℝ) < 4 * lam := by positivity

/-- `field_simp` discharges the `≠ 0` side conditions from the local context (here `hlam`),
then `ring` closes the polynomial goal. -/
example {lam x : ℝ} (hlam : lam ≠ 0) : (lam - x) / (4 * lam) + x / (4 * lam) = 1 / 4 := by
  field_simp
  ring

/-! ## The authoritative linear-response body — recipes for plan §4.2 #4, §5 #5–#10, §6.1 #3–#4 -/

/-- `transfer lam 0 = 1 / 2` with **no** hypothesis (degenerate branch included). -/
theorem transfer_thermoneutral (lam : ℝ) : transfer lam 0 = 1 / 2 := by
  unfold transfer
  rw [zero_div, sub_zero]

/-- The degenerate value at `lam = 0` is `1/2`, NOT `0` (plan §4.2 #4, corrected row). -/
theorem transfer_zero_lam (x : ℝ) : transfer 0 x = 1 / 2 := by
  unfold transfer
  rw [mul_zero, div_zero, sub_zero]

/-- The Leffler/Brønsted identification (plan §5 #5): the linear-response body equals the
transition-state coordinate when `lam ≠ 0`. -/
theorem transfer_eq_tsCoord {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    transfer lam x = (lam - x) / (2 * lam) := by
  unfold transfer
  field_simp

/-- Cross-module form `transfer = Hammond.tsCoord` (plan §7 #3). -/
theorem transfer_eq_tsCoord_bridge {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    transfer lam x = Hammond.tsCoord lam x := by
  unfold transfer Hammond.tsCoord
  field_simp

/-- `transfer = transferTS` — the discarded body is recovered as a theorem, not as a definition. -/
theorem transfer_eq_transferTS {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    transfer lam x = transferTS lam x := by
  unfold transfer transferTS
  field_simp

set_option linter.unusedVariables false in
/-- Brønsted complementarity (plan §5 #8). `hlam` is the plan's physical premise; the identity is a
pure ring identity (the two `x/(2*lam)` terms cancel even at `lam = 0`, `x / 0 = 0`), so the linter
is off locally. The skeleton keeps the premise for signature fidelity. -/
theorem transfer_add_reverse {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    transfer lam x + reverseTransfer lam x = 1 := by
  unfold transfer reverseTransfer
  ring

/-- (plan §5 #9) -/
theorem reverseTransfer_eq_transfer_neg (lam x : ℝ) : reverseTransfer lam x = transfer lam (-x) := by
  unfold transfer reverseTransfer
  ring

/-- (plan §4.2 #5 analogue) -/
theorem reverseTransfer_thermoneutral (lam : ℝ) : reverseTransfer lam 0 = 1 / 2 := by
  unfold reverseTransfer
  rw [zero_div, add_zero]

/-- (plan §6.1 #3) -/
theorem transfer_at_lam {lam : ℝ} (hlam : 0 < lam) : transfer lam lam = 0 := by
  unfold transfer
  field_simp

/-- (plan §6.1 #4) -/
theorem transfer_at_neg_lam {lam : ℝ} (hlam : 0 < lam) : transfer lam (-lam) = 1 := by
  unfold transfer
  field_simp
  ring

set_option linter.unusedVariables false in
/-- (plan §7 #12; the premise is a physical bookkeeping convention — the identity is a ring
identity, see `transfer_add_reverse`.) -/
theorem transfer_complementary_microscopic {lamInner lamOuter x : ℝ}
    (hlam : lamInner + lamOuter ≠ 0) :
    transfer (lamInner + lamOuter) x + reverseTransfer (lamInner + lamOuter) x = 1 := by
  unfold transfer reverseTransfer
  ring

/-! ## The barrier identities of plan §5 #1, #2, #12 -/

/-- Plan §5 #1: barrier = line + quadratic defect, explicit form. -/
theorem eact_expansion {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    eact lam x = lam / 4 - x / 2 + x ^ 2 / (4 * lam) := by
  unfold eact
  field_simp
  ring

/-- Plan §5 #2: the defect is exactly `x ^ 2 / (4 * lam)`. -/
theorem bepDefect_eq {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    bepDefect lam x = x ^ 2 / (4 * lam) := by
  unfold bepDefect bepLine eact
  field_simp
  ring

/-- Plan §5 #12: barrier-reversal identity. -/
theorem eact_neg_eq_add {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) : eact lam (-x) = eact lam x + x := by
  unfold eact
  field_simp
  ring

/-- Plan §5 #10, mean-value identity, with the **authoritative** body: the secant equals the
linear-response coefficient at the midpoint (the proof needs both `lam ≠ 0` and `h ≠ 0`). -/
theorem secSlope_eq_transfer_mid {lam : ℝ} (hlam : lam ≠ 0) {x h : ℝ} (hh : h ≠ 0) :
    secSlope lam x h = transfer lam (x + h / 2) := by
  unfold secSlope transfer eact
  field_simp
  ring

/-- Plan §5 #6/#7 of the older numbering: the step must be nonzero — dropping `h ≠ 0` breaks the
identity (witness: `secSlope 1 0 0 = 0` but `transfer 1 0 = 1/2`). -/
theorem secSlope_zero_h (lam x : ℝ) : secSlope lam x 0 = 0 := by
  unfold secSlope
  rw [add_zero, sub_self, zero_div]

/-! ## Cross-module bridge of plan §7 (observable secant vs Hammond Leffler secant) -/

/-- `secSlope lam x h = Hammond.lefflerSecant lam x (x + h)` — a pure `ring` identity. -/
theorem secSlope_eq_lefflerSecant (lam x h : ℝ) :
    secSlope lam x h = Hammond.lefflerSecant lam x (x + h) := by
  unfold secSlope Hammond.lefflerSecant Hammond.gapReactant eact
  ring

/-- The BEP barrier *is* the Marcus barrier (`rfl`, plan §7 #1) and the Hammond forward gap. -/
theorem eact_eq_barrier (lam x : ℝ) : eact lam x = Marcus.barrier lam x := rfl

theorem eact_eq_gapReactant (lam x : ℝ) : eact lam x = Hammond.gapReactant lam x := rfl

/-! ## DISCARDED body — the transition-state form `(lam - x)/(2*lam)` (Sprint-0 artefact)

The proofs below are the ones the first probe round calibrated. They are correct **for the
discarded definition** `transferTS`; they must not be copied against `transfer`. Kept as evidence
for the sign/shape bookkeeping of §5 #10 of the old plan. -/

theorem secSlope_eq_transferTS_mid {lam : ℝ} (hlam : lam ≠ 0) {x h : ℝ} (hh : h ≠ 0) :
    secSlope lam x h = transferTS lam (x + h / 2) := by
  unfold secSlope transferTS eact
  field_simp
  ring

theorem transferTS_add_reverseTS {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    transferTS lam x + transferTS lam (-x) = 1 := by
  unfold transferTS
  field_simp
  ring

/-! ## Measured failures of this topic (kept as evidence; do not retry)

* Bare `ring` / `ring_nf` with **no** hypothesis on `eact_expansion`, `bepDefect_eq`,
  `eact_neg_eq_add`, `secSlope_eq_transfer_mid` and `transfer_eq_tsCoord`: all fail, because the
  goals are false at `lam = 0` (totalised division) or at `h = 0` (the secant).
  The two exceptions are `transfer_add_reverse` and `reverseTransfer_eq_transfer_neg`, which are
  pure ring identities and hold at every `lam` (hence the local `unusedVariables` option).
* `#check @push_cast` — `error: unknown identifier 'push_cast'` (`push_cast` is a tactic, not a
  lemma; the ℚ side of it is calibrated in `bep-api-rat.lean`).
* `exact_mod_cast` does not apply to any ℝ-only goal here (it is a ℚ/ℤ ↔ ℝ tool).
* `field_simp` does **not** turn `hh : h ≠ 0` into a usable fact for the denominator `(x + h) - x`
  of `secSlope_eq_lefflerSecant`; that bridge is closed by `ring` directly.
-/

end PhotoLean.BEP.ProbeAlgebra
