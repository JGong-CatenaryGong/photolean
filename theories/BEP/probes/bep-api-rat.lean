/-
BEP milestone — API probe (topic C): the ℚ decision layer and the ℚ → ℝ transfer.

Scope. (i) `Decidable` instances for the order on `ℚ` and what `by decide` can actually close in
Lean 4.17.0 / mathlib v4.17.0; (ii) the `Rat.cast_*` family and the `unfold; push_cast; ring`
recipe of `PhotoLean/Hammond/RatModel.lean`; (iii) the two-point data layer (plan §8.1) — the α
observable, the solver `qLamOfPair`, its **corrected numerator** and its reconstruction theorem
with the necessary premises, all checked by kernel counterexamples.

Running:  proofs/scripts/lake env lean theories/BEP/probes/bep-api-rat.lean
Status:   0 errors / 0 warnings.

Local copies are character-for-character the plan §8.1 / statement-skeleton bodies.
`qLamOfPairLiteral` below is the *discarded* numerator `x₁^2 - x₂^2` kept only as evidence.
-/
import Mathlib

namespace PhotoLean.BEP.ProbeRat

/-! ## Local copies of the ℝ theory -/

noncomputable def eact (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)
noncomputable def bepLine (lam x : ℝ) : ℝ := lam / 4 - x / 2
noncomputable def bepDefect (lam x : ℝ) : ℝ := eact lam x - bepLine lam x
noncomputable def transfer (lam x : ℝ) : ℝ := 1 / 2 - x / (2 * lam)
noncomputable def reverseTransfer (lam x : ℝ) : ℝ := 1 / 2 + x / (2 * lam)
noncomputable def secSlope (lam x h : ℝ) : ℝ := (eact lam x - eact lam (x + h)) / h
noncomputable def alphaObs (x₁ ea₁ x₂ ea₂ : ℝ) : ℝ := (ea₁ - ea₂) / (x₂ - x₁)
noncomputable def lamOfPair (x₁ ea₁ x₂ ea₂ : ℝ) : ℝ :=
  (x₂ ^ 2 - x₁ ^ 2) / (2 * (x₂ - x₁) - 4 * (ea₁ - ea₂))

/-! ## Local copies of the ℚ layer (plan §8.1) — computable, no `noncomputable` -/

def qEact (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)
def qBepLine (lam x : ℚ) : ℚ := lam / 4 - x / 2
def qBepDefect (lam x : ℚ) : ℚ := qEact lam x - qBepLine lam x
def qTransfer (lam x : ℚ) : ℚ := 1 / 2 - x / (2 * lam)
def qReverseTransfer (lam x : ℚ) : ℚ := 1 / 2 + x / (2 * lam)
def qSecSlope (lam x h : ℚ) : ℚ := (qEact lam x - qEact lam (x + h)) / h
def qAlphaObs (x₁ ea₁ x₂ ea₂ : ℚ) : ℚ := (ea₁ - ea₂) / (x₂ - x₁)
def qLamOfPair (x₁ ea₁ x₂ ea₂ : ℚ) : ℚ := (x₂ ^ 2 - x₁ ^ 2) / (2 * (x₂ - x₁) - 4 * (ea₁ - ea₂))
def qConformsWindow (lam tol w : ℚ) : Prop := 0 < lam ∧ 0 < tol ∧ w ^ 2 ≤ 4 * lam * tol

/-- The **discarded literal numerator** `x₁^2 - x₂^2` (Sprint-0 artefact): returns `-λ`. -/
def qLamOfPairLiteral (x₁ ea₁ x₂ ea₂ : ℚ) : ℚ :=
  (x₁ ^ 2 - x₂ ^ 2) / (2 * (x₂ - x₁) - 4 * (ea₁ - ea₂))

inductive EPQVerdict where
  | degenerate
  | unphysical
  | conforming
  | boundary
  | superLinear
  | subLinear
  deriving DecidableEq, Repr

/-- Verdict cascade (the plan writes `…`; this is the resolution recorded in the skeleton). -/
def epQVerdict (lam x : ℚ) : EPQVerdict :=
  if lam = 0 then EPQVerdict.degenerate
  else if lam < 0 then EPQVerdict.unphysical
  else if x = lam then EPQVerdict.boundary
  else if x = -lam then EPQVerdict.boundary
  else if 0 < qTransfer lam x ∧ qTransfer lam x < 1 then EPQVerdict.conforming
  else if 1 < qTransfer lam x then EPQVerdict.superLinear
  else EPQVerdict.subLinear

/-! ## 0. Two ℚ-side helpers (mirrors of the ℝ lemmas) -/

/-- ℚ twin of `bepDefect_eq`. -/
theorem qBepDefect_eq_quadratic {lam x : ℚ} (hlam : lam ≠ 0) :
    qBepDefect lam x = x ^ 2 / (4 * lam) := by
  unfold qBepDefect qBepLine qEact
  field_simp
  ring

/-- ℚ twin of `bepDefect_nonneg`: with it the `abs` of the conformance predicate can be
discharged before any normalisation. -/
theorem qBepDefect_nonneg {lam x : ℚ} (hlam : 0 < lam) : 0 ≤ qBepDefect lam x := by
  rw [qBepDefect_eq_quadratic (ne_of_gt hlam)]
  exact div_nonneg (sq_nonneg x) (by positivity)

/-! ## A. `Decidable` on ℚ — the instances and their names -/

#synth Ord ℚ
#synth DecidableRel (· ≤ · : ℚ → ℚ → Prop)
#synth DecidableRel (· < · : ℚ → ℚ → Prop)
#check @instDecidableRelLe
#check @Rat.instDecidableLe
#check @Rat.instDecidableLt
#check @decide_eq_true_iff
#check @of_decide_eq_true

/-- `by decide` works on ℚ **integer literals**. -/
example : (1 : ℚ) ≤ 3 := by decide

/-- `by decide` works on `Rat.divInt` literals (the constructor form is kernel-reducible). -/
example : Rat.divInt 1 4 ≤ Rat.divInt 1 1 := by decide

/-- `by norm_num` (NOT `decide`) closes ℚ comparisons that involve `/`. -/
example : (1 : ℚ) / 2 ≤ 3 / 4 := by norm_num

example : ¬ ((1 : ℚ) / 2 ≤ 1 / 4) := by norm_num
example : (1 : ℚ) / 2 ≠ 3 / 4 := by norm_num
example : |(1 : ℚ) / 2| = 1 / 2 := by norm_num

/-- `norm_num` does **not** push through `|·|` on ℚ: `abs_of_nonneg` must be applied first. -/
example : |(1 : ℚ) / 2| ≤ 3 / 4 := by
  rw [abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2)]
  norm_num

/-- The verified witness recipe for the `qConformsWindow` layer (positive control). -/
example : qConformsWindow 1 (1 / 4) 0 := by
  unfold qConformsWindow
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num

/-- Negative control for the witness (mandatory in this repository). -/
example : ¬ qConformsWindow 1 (1 / 16) 1 := by
  unfold qConformsWindow
  rintro ⟨-, -, h⟩
  norm_num at h

/-- `by decide` closes such a predicate **only** once every comparison is between
kernel-reducible rationals; any comparison containing a `/`-literal makes it fail (failure log). -/
example : qBepDefect 1 0 = 0 := by
  rw [qBepDefect_eq_quadratic (by norm_num : (1 : ℚ) ≠ 0)]
  norm_num

/-! ## B. The `Rat.cast_*` family and the ℚ → ℝ transfer lemmas (plan §8.1) -/

#check @Rat.cast_div
#check @Rat.cast_add
#check @Rat.cast_sub
#check @Rat.cast_mul
#check @Rat.cast_pow
#check @Rat.cast_neg
#check @Rat.cast_inv
#check @Rat.cast_lt
#check @Rat.cast_le
#check @Rat.cast_abs
#check @Rat.cast_one
#check @Rat.cast_zero
#check @Rat.cast_mk

theorem qEact_cast (lam x : ℚ) : ((qEact lam x : ℚ) : ℝ) = eact (lam : ℝ) (x : ℝ) := by
  unfold qEact eact
  push_cast
  ring

theorem qBepLine_cast (lam x : ℚ) : ((qBepLine lam x : ℚ) : ℝ) = bepLine (lam : ℝ) (x : ℝ) := by
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

theorem qReverseTransfer_cast (lam x : ℚ) :
    ((qReverseTransfer lam x : ℚ) : ℝ) = reverseTransfer (lam : ℝ) (x : ℝ) := by
  unfold qReverseTransfer reverseTransfer
  push_cast
  ring

set_option linter.unusedVariables false in
/-- The `≠ 0` premise is the mathematical premise of a finite difference and is *not* consumed by
the cast: `Rat.cast_div` moves the cast through division unconditionally (the situation recorded
for `lefflerSecantQ_cast` in the Hammond round). -/
theorem qSecSlope_cast {lam x h : ℚ} (hh : h ≠ 0) :
    ((qSecSlope lam x h : ℚ) : ℝ) = secSlope (lam : ℝ) (x : ℝ) (h : ℝ) := by
  unfold qSecSlope secSlope qEact eact
  push_cast
  ring

set_option linter.unusedVariables false in
theorem qAlphaObs_cast {x₁ ea₁ x₂ ea₂ : ℚ} (h : x₂ ≠ x₁) :
    ((qAlphaObs x₁ ea₁ x₂ ea₂ : ℚ) : ℝ) = alphaObs (x₁ : ℝ) (ea₁ : ℝ) (x₂ : ℝ) (ea₂ : ℝ) := by
  unfold qAlphaObs alphaObs
  push_cast
  ring

set_option linter.unusedVariables false in
theorem qLamOfPair_cast {x₁ ea₁ x₂ ea₂ : ℚ} (h : x₁ ≠ x₂) :
    ((qLamOfPair x₁ ea₁ x₂ ea₂ : ℚ) : ℝ) =
      lamOfPair (x₁ : ℝ) (ea₁ : ℝ) (x₂ : ℝ) (ea₂ : ℝ) := by
  unfold qLamOfPair lamOfPair
  push_cast
  ring

/-- `exact_mod_cast` moves ℚ comparisons to ℝ (and back). -/
example {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
example {a b : ℚ} (h : a < b) : (a : ℝ) < (b : ℝ) := by exact_mod_cast h

/-! ## C. The two-point data layer — the corrected solver (plan §8.1) -/

/-- The ℚ mean-value identity. -/
theorem qSecSlope_eq_qTransfer_mid {lam : ℚ} (hlam : lam ≠ 0) {x h : ℚ} (hh : h ≠ 0) :
    qSecSlope lam x h = qTransfer lam (x + h / 2) := by
  unfold qSecSlope qTransfer qEact
  field_simp
  ring

/-- Two-point data → structural coefficient. -/
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
/-- **The reconstruction theorem** (plan §8.1): two model-consistent data points determine λ.
`hx` is not consumed by the proof (the denominator premise `hden` already carries the needed
non-degeneracy), but it is the mathematical premise of a two-point estimator and the plan keeps it.
Verified recipe: substitute the two data hypotheses, `div_eq_iff hden`, then `field_simp; ring`. -/
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
/-- The ℝ-side counterpart of the reconstruction theorem. -/
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

/-- **Drift evidence 1** (discarded numerator): with `λ = 2` and the data `x = 0, 1` (barriers
`1/2`, `1/8`) the literal numerator returns `-2 = -λ`. -/
example : qLamOfPairLiteral 0 (qEact 2 0) 1 (qEact 2 1) = -2 := by
  norm_num [qLamOfPairLiteral, qEact]

/-- The corrected numerator recovers `λ = 2` on the same data. -/
example : qLamOfPair 0 (qEact 2 0) 1 (qEact 2 1) = 2 := by
  norm_num [qLamOfPair, qEact]

/-- The two numerators are exact negatives of each other — that is the whole content of the drift. -/
example (x₁ ea₁ x₂ ea₂ : ℚ) :
    qLamOfPairLiteral x₁ ea₁ x₂ ea₂ = -qLamOfPair x₁ ea₁ x₂ ea₂ := by
  unfold qLamOfPairLiteral qLamOfPair
  rw [← neg_div]
  ring

/-- **Drift evidence 2** (the necessity of `lam ≠ 0`): at `λ = 0` the totalised division makes
`qEact 0 x` constant `0`, the denominator `2*(1-0) - 4*(0-0) = 2` is nonzero, and the solver
returns `1/2 ≠ 0`. -/
example : qEact 0 0 = 0 ∧ qEact 0 1 = 0 := by
  constructor <;> norm_num [qEact]

example : qLamOfPair 0 (qEact 0 0) 1 (qEact 0 1) = 1 / 2 := by
  norm_num [qLamOfPair, qEact]

/-- **Drift evidence 3** (well-posedness): the symmetric pair `(x, -x)` is blind to λ — the
numerator and the denominator vanish together, so `hden` cannot be dropped. -/
example : qLamOfPair 1 (qEact 2 1) (-1) (qEact 2 (-1)) = 0 := by
  norm_num [qLamOfPair, qEact]

example : eact 2 1 - eact 2 (-1) = eact 5 1 - eact 5 (-1) := by
  norm_num [eact]

/-! ## D. The verdict cascade (plan §8.1) — the plan writes `…` for `epQVerdict`

The four characterizations below are the resolution recorded in the statement skeleton: `boundary`
at `x = ±λ` (α = 0 or 1), `conforming` strictly inside `(0,1)`, `superLinear` above the
Evans–Polanyi band (`1 < α`), `subLinear` below it (`α < 0`). The uniform recipe is
`unfold epQVerdict`, kill the first two guards with `if_neg`, `by_cases` on the remaining ones, and
close each leaf with `iff_of_true rfl _` / `iff_of_false (by decide) _`. The two limit values of
`qTransfer` (they are the only solutions of α = 0 and α = 1) make every refutation one line. -/

theorem qTransfer_at_lam {lam : ℚ} (hlam : lam ≠ 0) : qTransfer lam lam = 0 := by
  unfold qTransfer
  field_simp

theorem qTransfer_at_neg_lam {lam : ℚ} (hlam : lam ≠ 0) : qTransfer lam (-lam) = 1 := by
  unfold qTransfer
  field_simp
  ring

theorem qTransfer_eq_zero_iff {lam x : ℚ} (hlam : lam ≠ 0) : qTransfer lam x = 0 ↔ x = lam := by
  constructor
  · intro hz
    unfold qTransfer at hz
    field_simp at hz
    linarith
  · intro hx
    rw [hx, qTransfer_at_lam hlam]

theorem qTransfer_eq_one_iff {lam x : ℚ} (hlam : lam ≠ 0) : qTransfer lam x = 1 ↔ x = -lam := by
  constructor
  · intro hz
    unfold qTransfer at hz
    field_simp at hz
    linarith
  · intro hx
    rw [hx, qTransfer_at_neg_lam hlam]

theorem epQVerdict_conforming_iff {lam x : ℚ} (hlam : 0 < lam) :
    epQVerdict lam x = EPQVerdict.conforming ↔ 0 < qTransfer lam x ∧ qTransfer lam x < 1 := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  unfold epQVerdict
  rw [if_neg hlam', if_neg (by linarith : ¬ lam < 0)]
  by_cases h2 : x = lam
  · rw [if_pos h2]
    exact iff_of_false (by decide) (by
      rintro ⟨h1, -⟩
      rw [h2, qTransfer_at_lam hlam'] at h1
      exact absurd h1 (lt_irrefl 0))
  rw [if_neg h2]
  by_cases h3 : x = -lam
  · rw [if_pos h3]
    exact iff_of_false (by decide) (by
      rintro ⟨-, h2'⟩
      rw [h3, qTransfer_at_neg_lam hlam'] at h2'
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
  unfold epQVerdict
  rw [if_neg hlam', if_neg (by linarith : ¬ lam < 0)]
  by_cases h2 : x = lam
  · rw [if_pos h2]
    exact iff_of_false (by decide) (by
      rintro h
      rw [h2, qTransfer_at_lam hlam'] at h
      exact absurd h (by norm_num))
  rw [if_neg h2]
  by_cases h3 : x = -lam
  · rw [if_pos h3]
    exact iff_of_false (by decide) (by
      rintro h
      rw [h3, qTransfer_at_neg_lam hlam'] at h
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
  unfold epQVerdict
  rw [if_neg hlam', if_neg (by linarith : ¬ lam < 0)]
  by_cases h2 : x = lam
  · rw [if_pos h2]
    exact iff_of_false (by decide) (by
      rw [h2, qTransfer_at_lam hlam']
      exact lt_irrefl 0)
  rw [if_neg h2]
  by_cases h3 : x = -lam
  · rw [if_pos h3]
    exact iff_of_false (by decide) (by
      rw [h3, qTransfer_at_neg_lam hlam']
      norm_num)
  rw [if_neg h3]
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
        have hne0 : qTransfer lam x ≠ 0 := fun hz => h2 ((qTransfer_eq_zero_iff hlam').mp hz)
        have hne1 : qTransfer lam x ≠ 1 := fun hz => h3 ((qTransfer_eq_one_iff hlam').mp hz)
        have hα : qTransfer lam x ≤ 0 := by
          by_contra hc
          exact h4 ⟨lt_of_not_ge hc, lt_of_le_of_ne (le_of_not_gt h5) hne1⟩
        exact lt_of_le_of_ne hα hne0
      · intro _
        rfl

/-! ## Measured failures of this topic (verbatim, do not retry)

1. `by decide` on any ℚ comparison whose arguments contain `/`:

   ```
   error: tactic 'decide' failed for proposition
     1 / 2 ≤ 3 / 4
   since its 'Decidable' instance
     (1 / 2).instDecidableLe (3 / 4)
   did not reduce to 'isTrue' or 'isFalse'.

   After unfolding the instances 'instDecidableEqBool', 'Bool.decEq', 'Int.decLt',
   'Rat.instDecidableLe' and 'Int.decNonneg✝', reduction got stuck at the 'Decidable' instance
     match (3 / 4).blt (1 / 2), false with
   ```
   `Int.decNonneg✝` is not kernel-reducible, so `Rat.blt` never reduces on `/`-literals.

2. `by decide` on a *defined* predicate before unfolding:

   ```
   error: failed to synthesize
     Decidable (qConformsWindow 1 (1 / 4) 0)
   ```
   Type-class search does not unfold a plain `def` (semireducible) — and after `unfold` the tactic
   still hits failure 1.

3. `norm_num [qBepDefect, qBepLine, qEact]` alone leaves `⊢ |1 / 4| ≤ 1 / 4` (`norm_num` has no
   `abs` support on ℚ); then `rw [abs_of_nonneg (by norm_num : 0 ≤ 1 / 4)]` fails with

   ```
   error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression
     |1 / 4|
   ```
   because the argument of `abs` is still `(1 - 0) ^ 2 / (4 * 1) - (1 / 4 - 0 / 2)`. Write the side
   condition on the un-normalised argument, or rewrite the defect first with
   `qBepDefect_eq_quadratic`.

4. `Rat.castRat` does not exist (measured: `error: unknown constant 'Rat.castRat'`); the ℚ → ℝ cast
   family is `Rat.cast_{div,add,sub,mul,pow,neg,inv,lt,le,abs,one,zero}` (+ `Rat.cast_mk` for
   `Rat.divInt` literals).

5. `native_decide` is **banned**: it closes the ℚ goal, but

   ```
   'nativeDecideWitness' depends on axioms: [propext, Lean.ofReduceBool]
   ```

   and `Lean.ofReduceBool` is not in the contract's `ALLOWED_AXIOMS`, so any delivered use fails
   `proofs/scripts/axioms.sh`. Use `norm_num` (or `decide` on integer literals only).

6. `div_nonneg_iff_of_pos_right` does not exist (only the strict `div_pos_iff_of_pos_right` from the
   Hammond round); use `div_nonneg_iff` or multiply through with `div_le_iff₀`.

7. `field_simp` sometimes closes a BEP field identity by itself; appending `ring` then fails with
   `error: no goals to be solved`. Measured on `transfer_eq_tsCoord`, `transfer_eq_tsCoord_bridge`,
   `transfer_eq_transferTS` and `transfer_at_lam` in `bep-api-algebra.lean`; `transfer_at_neg_lam`,
   `secSlope_eq_transfer_mid` and `eact_expansion` still need the trailing `ring`.
-/

end PhotoLean.BEP.ProbeRat
