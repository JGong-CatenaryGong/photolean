/-
BEP milestone — API probe (topic F): the model-consistency block (plan §8.1) and the instance
verdicts I1–I12 (plan §8.2).

Scope. (i) The five new `RatModel` declarations of the plan's §8.1 addition — second divided
difference, three-point model consistency, and the three theorems that turn a *negative* family
curvature into a *falsification* of every positive-λ two-parabola law. (ii) The whole instance table:
I1–I10 are model-constructed families at `λ = 2` (plus the degenerate `λ = 0` and the unphysical
`λ = -2` rows), I11 quotes the first-hand `(driving force, barrier)` pairs of
`theories/BEP/LITERATURE.md` §R1.10 (kcal/mol, source locus in the docstrings, the model's
`x = -ΔG°` sign convention applied explicitly), I12 is the summary.

**Constraint measured first**: every I-row below is closed by `norm_num` (with `unfold`, and with
`qSecondDividedDiff`/`qEact` passed as simp lemmas for the literature rows) or by `decide` on
integer-only goals. `by decide` on comparisons containing `/`-literals and `native_decide` are both
unusable (see `bep-api-rat.lean`); the falsification rows need `qModelConsistent3_curvature_pos`
plus the computed negativity.

Running:  proofs/scripts/lake env lean theories/BEP/probes/bep-api-instances.lean
Status:   0 errors / 0 warnings.
-/
import Mathlib

namespace PhotoLean.BEP.ProbeInstances

/-! ## Local copies of the ℚ layer (plan §8.1 verbatim) -/

def qEact (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)
def qBepLine (lam x : ℚ) : ℚ := lam / 4 - x / 2
def qBepDefect (lam x : ℚ) : ℚ := qEact lam x - qBepLine lam x
def qTransfer (lam x : ℚ) : ℚ := 1 / 2 - x / (2 * lam)
def qAlphaObs (x₁ ea₁ x₂ ea₂ : ℚ) : ℚ := (ea₁ - ea₂) / (x₂ - x₁)
def qLamOfPair (x₁ ea₁ x₂ ea₂ : ℚ) : ℚ := (x₂ ^ 2 - x₁ ^ 2) / (2 * (x₂ - x₁) - 4 * (ea₁ - ea₂))
def qConformsWindow (lam tol w : ℚ) : Prop := 0 < lam ∧ 0 < tol ∧ w ^ 2 ≤ 4 * lam * tol
def qSecondDividedDiff (x₁ e₁ x₂ e₂ x₃ e₃ : ℚ) : ℚ :=
  ((e₃ - e₂) / (x₃ - x₂) - (e₂ - e₁) / (x₂ - x₁)) / (x₃ - x₁)
def qModelConsistent3 (lam x₁ x₂ x₃ e₁ e₂ e₃ : ℚ) : Prop :=
  0 < lam ∧ e₁ = qEact lam x₁ ∧ e₂ = qEact lam x₂ ∧ e₃ = qEact lam x₃

inductive EPQVerdict where
  | degenerate
  | unphysical
  | conforming
  | boundary
  | superLinear
  | subLinear
  deriving DecidableEq, Repr

def epQVerdict (lam x : ℚ) : EPQVerdict :=
  if lam = 0 then EPQVerdict.degenerate
  else if lam < 0 then EPQVerdict.unphysical
  else if x = lam then EPQVerdict.boundary
  else if x = -lam then EPQVerdict.boundary
  else if 0 < qTransfer lam x ∧ qTransfer lam x < 1 then EPQVerdict.conforming
  else if 1 < qTransfer lam x then EPQVerdict.superLinear
  else EPQVerdict.subLinear

/-! ## Plan §8.1 addition — the model-consistency block -/

/-- The second divided difference of three model points is the curvature `1/(4λ)`; the three
abscissae must be pairwise distinct (at `x₁ = x₃` the outer denominator is `0` and the totalised
division gives `0`, not `1/(4λ)`). -/
theorem qSecondDividedDiff_model {lam x₁ x₂ x₃ : ℚ} (hlam : lam ≠ 0) (h₁₂ : x₁ ≠ x₂)
    (h₂₃ : x₂ ≠ x₃) (h₁₃ : x₁ ≠ x₃) :
    qSecondDividedDiff x₁ (qEact lam x₁) x₂ (qEact lam x₂) x₃ (qEact lam x₃) = 1 / (4 * lam) := by
  have h12 : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁₂)
  have h23 : x₃ - x₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₂₃)
  have h13 : x₃ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁₃)
  unfold qSecondDividedDiff qEact
  field_simp
  ring

/-- With `λ > 0` the model forces the second divided difference to be positive — the
λ-independent test that refutes the literature families. -/
theorem qModelConsistent3_curvature_pos {lam x₁ x₂ x₃ e₁ e₂ e₃ : ℚ}
    (h : qModelConsistent3 lam x₁ x₂ x₃ e₁ e₂ e₃) (h₁₂ : x₁ ≠ x₂) (h₂₃ : x₂ ≠ x₃)
    (h₁₃ : x₁ ≠ x₃) : 0 < qSecondDividedDiff x₁ e₁ x₂ e₂ x₃ e₃ := by
  obtain ⟨hlam, h₁, h₂, h₃⟩ := h
  rw [h₁, h₂, h₃, qSecondDividedDiff_model (ne_of_gt hlam) h₁₂ h₂₃ h₁₃]
  positivity

/-- Three model-consistent points determine λ from their curvature. -/
theorem qModelConsistent3_lam_eq {lam x₁ x₂ x₃ e₁ e₂ e₃ : ℚ}
    (h : qModelConsistent3 lam x₁ x₂ x₃ e₁ e₂ e₃) (h₁₂ : x₁ ≠ x₂) (h₂₃ : x₂ ≠ x₃)
    (h₁₃ : x₁ ≠ x₃) : lam = 1 / (4 * qSecondDividedDiff x₁ e₁ x₂ e₂ x₃ e₃) := by
  obtain ⟨hlam, h₁, h₂, h₃⟩ := h
  rw [h₁, h₂, h₃, qSecondDividedDiff_model (ne_of_gt hlam) h₁₂ h₂₃ h₁₃]
  field_simp

/-! ## Plan §8.2 — I1…I10 (model-constructed families; all `norm_num`-closed) -/

theorem inst_I1_thermoneutral_zone : epQVerdict (2 : ℚ) 0 = EPQVerdict.conforming := by
  unfold epQVerdict qTransfer
  norm_num

theorem inst_I1_thermoneutral_transfer : qTransfer (2 : ℚ) 0 = 1 / 2 := by
  unfold qTransfer
  norm_num

theorem inst_I1_thermoneutral_conforms : qConformsWindow (2 : ℚ) (1 / 4) 0 := by
  unfold qConformsWindow
  norm_num

theorem inst_I2_exergonic_zone : epQVerdict (2 : ℚ) (1 / 2) = EPQVerdict.conforming := by
  unfold epQVerdict qTransfer
  norm_num

theorem inst_I2_exergonic_transfer : qTransfer (2 : ℚ) (1 / 2) = 3 / 8 := by
  unfold qTransfer
  norm_num

theorem inst_I2_exergonic_conforms : qConformsWindow (2 : ℚ) (1 / 4) (1 / 2) := by
  unfold qConformsWindow
  norm_num

theorem inst_I3_endergonic_zone : epQVerdict (2 : ℚ) (-(1 / 2)) = EPQVerdict.conforming := by
  unfold epQVerdict qTransfer
  norm_num

theorem inst_I3_endergonic_transfer : qTransfer (2 : ℚ) (-(1 / 2)) = 5 / 8 := by
  unfold qTransfer
  norm_num

theorem inst_I3_endergonic_conforms : qConformsWindow (2 : ℚ) (1 / 4) (1 / 2) := by
  unfold qConformsWindow
  norm_num

theorem inst_I4_forwardLimit_zone : epQVerdict (2 : ℚ) 2 = EPQVerdict.boundary := by
  unfold epQVerdict qTransfer
  norm_num

theorem inst_I4_forwardLimit_transfer : qTransfer (2 : ℚ) 2 = 0 := by
  unfold qTransfer
  norm_num

/-- The forward barrierless limit sits on the edge of the Evans–Polanyi band: the *open* regime
`0 < α < 1` already fails there. -/
theorem inst_I4_forwardLimit_boundary :
    ¬ (0 < qTransfer (2 : ℚ) 2 ∧ qTransfer (2 : ℚ) 2 < 1) := by
  unfold qTransfer
  norm_num

theorem inst_I5_reverseLimit_zone : epQVerdict (2 : ℚ) (-2) = EPQVerdict.boundary := by
  unfold epQVerdict qTransfer
  norm_num

theorem inst_I5_reverseLimit_transfer : qTransfer (2 : ℚ) (-2) = 1 := by
  unfold qTransfer
  norm_num

theorem inst_I5_reverseLimit_boundary :
    ¬ (0 < qTransfer (2 : ℚ) (-2) ∧ qTransfer (2 : ℚ) (-2) < 1) := by
  unfold qTransfer
  norm_num

theorem inst_I6_inverted_zone : epQVerdict (2 : ℚ) 3 = EPQVerdict.subLinear := by
  unfold epQVerdict qTransfer
  norm_num

theorem inst_I6_inverted_transfer : qTransfer (2 : ℚ) 3 = -(1 / 4) := by
  unfold qTransfer
  norm_num

theorem inst_I6_inverted_notBounds :
    ¬ (0 ≤ qTransfer (2 : ℚ) 3 ∧ qTransfer (2 : ℚ) 3 ≤ 1) := by
  unfold qTransfer
  norm_num

theorem inst_I7_reverseInverted_zone : epQVerdict (2 : ℚ) (-3) = EPQVerdict.superLinear := by
  unfold epQVerdict qTransfer
  norm_num

theorem inst_I7_reverseInverted_transfer : qTransfer (2 : ℚ) (-3) = 5 / 4 := by
  unfold qTransfer
  norm_num

theorem inst_I7_reverseInverted_notBounds :
    ¬ (0 ≤ qTransfer (2 : ℚ) (-3) ∧ qTransfer (2 : ℚ) (-3) ≤ 1) := by
  unfold qTransfer
  norm_num

theorem inst_I8_degenerate_zone : epQVerdict (0 : ℚ) 1 = EPQVerdict.degenerate := by
  unfold epQVerdict
  norm_num

theorem inst_I8_degenerate_exact : qEact (0 : ℚ) 1 = 0 := by
  unfold qEact
  norm_num

/-- The degenerate value of the **linear-response** body is `1/2` (plan §4.2 #4) — the I8 row of
plan §8.2 still prints the discarded TS-coordinate value `α = 0`; the corrected value is below. -/
theorem inst_I8_degenerate_transfer : qTransfer (0 : ℚ) 1 = 1 / 2 := by
  unfold qTransfer
  norm_num

theorem inst_I9_unphysical_zone : epQVerdict (-2 : ℚ) 1 = EPQVerdict.unphysical := by
  unfold epQVerdict qTransfer
  norm_num

theorem inst_I9_unphysical_transfer : qTransfer (-2 : ℚ) 1 = 3 / 4 := by
  unfold qTransfer
  norm_num

/-- The Evans–Polanyi bounds do **not** detect the unphysical curvature (`α = 3/4 ∈ [0,1]`); the
sign of the defect does. -/
theorem inst_I9_unphysical_defect_negative : qBepDefect (-2 : ℚ) 1 = -(1 / 8) := by
  unfold qBepDefect qBepLine qEact
  norm_num

theorem inst_I9_unphysical_bounds_blind :
    0 ≤ qTransfer (-2 : ℚ) 1 ∧ qTransfer (-2 : ℚ) 1 ≤ 1 := by
  unfold qTransfer
  norm_num

theorem inst_I10_threshold_conforms : qConformsWindow (2 : ℚ) (1 / 8) 1 := by
  unfold qConformsWindow
  norm_num

theorem inst_I10_threshold_fails : ¬ qConformsWindow (2 : ℚ) (1 / 16) 1 := by
  unfold qConformsWindow
  norm_num

/-! ## Plan §8.2 — I11: the first-hand literature families (`LITERATURE.md` §R1.10)

Literals are the sources' **kcal/mol** numbers, verbatim from the §R1.10 tables; the model's
driving force is `x = -ΔG°` (F5 prints a classical `ΔE`, so `x = -ΔE`, with the ΔE-vs-ΔG caveat of
§R1.10.5). Each family gets: the two-point α observable at the widest printed pair, the model's
two-point solver at two adjacent printed pairs, the second divided difference over three printed
rows (negative), and the falsification it entails.

F4 (Table 2, PE column) has **no per-row numbers** in §R1.10 (only aggregate statistics), so it
cannot carry any of these four rows — see the report of this round. -/

/-- F1 = *Antioxidants* 15(7) 840–860 (2026), Table 1 "Water", f-HAT → `•OOH`.
Rows used (kcal/mol, verbatim): `16(2)` `ΔG° = -0.3`, `ΔG‡ = 15.6`; `16(1)` `ΔG° = -0.9`,
`ΔG‡ = 15.7`; `14(1)` `ΔG° = -2.3`, `ΔG‡ = 15.7`; `12` `ΔG° = -4.9`, `ΔG‡ = 13.9`;
`8` `ΔG° = -12.9`, `ΔG‡ = 8.8`. Model `x = -ΔG°`. -/
theorem inst_I11_F1_alphaObs :
    qAlphaObs (0.3 : ℚ) 15.6 12.9 8.8 = 34 / 63 := by
  unfold qAlphaObs
  norm_num

theorem inst_I11_F1_lamHat : qLamOfPair (0.3 : ℚ) 15.6 0.9 15.7 = 9 / 20 := by
  unfold qLamOfPair
  norm_num

theorem inst_I11_F1_curvature_negative :
    qSecondDividedDiff (0.9 : ℚ) 15.7 2.3 15.7 4.9 13.9 = -(9 / 52) := by
  unfold qSecondDividedDiff
  norm_num

theorem inst_I11_F1_not_model_consistent :
    ¬ ∃ lam : ℚ, qModelConsistent3 lam (0.9 : ℚ) 2.3 4.9 15.7 15.7 13.9 := by
  rintro ⟨lam, hlam, h₁, h₂, h₃⟩
  have hpos := qModelConsistent3_curvature_pos ⟨hlam, h₁, h₂, h₃⟩
    (by norm_num : (0.9 : ℚ) ≠ 2.3) (by norm_num : (2.3 : ℚ) ≠ 4.9) (by norm_num : (0.9 : ℚ) ≠ 4.9)
  rw [show qSecondDividedDiff (0.9 : ℚ) 15.7 2.3 15.7 4.9 13.9 = -(9 / 52) by
    unfold qSecondDividedDiff
    norm_num] at hpos
  norm_num at hpos

/-- F2 = same paper, Table 1 "PE" (pentyl ethanoate). Rows (kcal/mol, verbatim): `16(2)`
`ΔG° = +1.0`, `ΔG‡ = 14.0`; `13` `ΔG° = -2.2`, `ΔG‡ = 13.3`; `2` `ΔG° = -4.6`, `ΔG‡ = 10.0`;
`10` `ΔG° = -14.3`, `ΔG‡ = 5.1`. -/
theorem inst_I11_F2_alphaObs :
    qAlphaObs (-(1.0) : ℚ) 14.0 14.3 5.1 = 89 / 153 := by
  unfold qAlphaObs
  norm_num

theorem inst_I11_F2_lamHat : qLamOfPair (-(1.0) : ℚ) 14.0 2.2 13.3 = 16 / 15 := by
  unfold qLamOfPair
  norm_num

theorem inst_I11_F2_curvature_negative :
    qSecondDividedDiff (-(1.0) : ℚ) 14.0 2.2 13.3 4.6 10.0 = -(185 / 896) := by
  unfold qSecondDividedDiff
  norm_num

theorem inst_I11_F2_not_model_consistent :
    ¬ ∃ lam : ℚ, qModelConsistent3 lam (-(1.0) : ℚ) 2.2 4.6 14.0 13.3 10.0 := by
  rintro ⟨lam, hlam, h₁, h₂, h₃⟩
  have hpos := qModelConsistent3_curvature_pos ⟨hlam, h₁, h₂, h₃⟩
    (by norm_num : (-(1.0) : ℚ) ≠ 2.2) (by norm_num : (2.2 : ℚ) ≠ 4.6)
    (by norm_num : (-(1.0) : ℚ) ≠ 4.6)
  rw [show qSecondDividedDiff (-(1.0) : ℚ) 14.0 2.2 13.3 4.6 10.0 = -(185 / 896) by
    unfold qSecondDividedDiff
    norm_num] at hpos
  norm_num at hpos

/-- F3 = same paper, Table 2 "Water" (`•OOCH₃`). Rows (kcal/mol, verbatim): `16(1)` `ΔG° = +0.8`,
`ΔG‡ = 15.6`; `19(2)` `ΔG° = +3.6`, `ΔG‡ = 17.7`; `1` `ΔG° = -7.1`, `ΔG‡ = 11.0`; `7` `ΔG° = -9.9`,
`ΔG‡ = 7.3`. -/
theorem inst_I11_F3_alphaObs :
    qAlphaObs (-(0.8) : ℚ) 15.6 9.9 7.3 = 83 / 107 := by
  unfold qAlphaObs
  norm_num

theorem inst_I11_F3_lamHat : qLamOfPair (-(0.8) : ℚ) 15.6 (-(3.6)) 17.7 = 22 / 5 := by
  unfold qLamOfPair
  norm_num

theorem inst_I11_F3_curvature_negative :
    qSecondDividedDiff (-(0.8) : ℚ) 15.6 7.1 11.0 9.9 7.3 = -(8175 / 118342) := by
  unfold qSecondDividedDiff
  norm_num

theorem inst_I11_F3_not_model_consistent :
    ¬ ∃ lam : ℚ, qModelConsistent3 lam (-(0.8) : ℚ) 7.1 9.9 15.6 11.0 7.3 := by
  rintro ⟨lam, hlam, h₁, h₂, h₃⟩
  have hpos := qModelConsistent3_curvature_pos ⟨hlam, h₁, h₂, h₃⟩
    (by norm_num : (-(0.8) : ℚ) ≠ 7.1) (by norm_num : (7.1 : ℚ) ≠ 9.9)
    (by norm_num : (-(0.8) : ℚ) ≠ 9.9)
  rw [show qSecondDividedDiff (-(0.8) : ℚ) 15.6 7.1 11.0 9.9 7.3 = -(8175 / 118342) by
    unfold qSecondDividedDiff
    norm_num] at hpos
  norm_num at hpos

/-- F5 = *Chem. Sci.* 6(10) 5866–5881 (2015), Table 1 `CCSD(T)-F12a/jun-cc-pVTZ`, H abstraction from
2-butanol by `•OOH`. The table prints a **classical** `ΔE` and `V‡f` (kcal/mol, verbatim) — an
energy, not a Gibbs energy — so `x = -ΔE`. Rows: `R2` `7.62 / 12.38`; `R3` `13.14 / 17.57`;
`R4` `14.56 / 17.47`; `R1` `15.80 / 20.32`; `R5` `19.82 / 21.72`. -/
theorem inst_I11_F5_alphaObs :
    qAlphaObs (-(7.62) : ℚ) 12.38 (-(19.82)) 21.72 = 467 / 610 := by
  unfold qAlphaObs
  norm_num

theorem inst_I11_F5_lamHat :
    qLamOfPair (-(7.62) : ℚ) 12.38 (-(13.14)) 17.57 = 7958 / 675 := by
  unfold qLamOfPair
  norm_num

theorem inst_I11_F5_curvature_negative :
    qSecondDividedDiff (-(14.56) : ℚ) 17.47 (-(15.8)) 20.32 (-(19.82)) 21.72 =
      -(1215125 / 3277506) := by
  unfold qSecondDividedDiff
  norm_num

theorem inst_I11_F5_not_model_consistent :
    ¬ ∃ lam : ℚ, qModelConsistent3 lam (-(14.56) : ℚ) (-(15.8)) (-(19.82)) 17.47 20.32 21.72 := by
  rintro ⟨lam, hlam, h₁, h₂, h₃⟩
  have hpos := qModelConsistent3_curvature_pos ⟨hlam, h₁, h₂, h₃⟩
    (by norm_num : (-(14.56) : ℚ) ≠ -(15.8)) (by norm_num : (-(15.8) : ℚ) ≠ -(19.82))
    (by norm_num : (-(14.56) : ℚ) ≠ -(19.82))
  rw [show qSecondDividedDiff (-(14.56) : ℚ) 17.47 (-(15.8)) 20.32 (-(19.82)) 21.72 =
      -(1215125 / 3277506) by
    unfold qSecondDividedDiff
    norm_num] at hpos
  norm_num at hpos

/-! ## Plan §8.2 — I12 (summary) and the non-vacuity instance -/

/-- I12: for each of the four families with per-row data, the affine (BEP) side is a decent
description — the observed slope lies strictly inside `(0,1)` — while the family curvature is
negative, so **no** positive-λ equal-curvature two-parabola law reproduces those rows. -/
theorem inst_I12_affine_conforms_model_refuted :
    (0 < qAlphaObs (0.3 : ℚ) 15.6 12.9 8.8 ∧ qAlphaObs (0.3 : ℚ) 15.6 12.9 8.8 < 1 ∧
        ¬ ∃ lam : ℚ, qModelConsistent3 lam (0.9 : ℚ) 2.3 4.9 15.7 15.7 13.9) ∧
      (0 < qAlphaObs (-(1.0) : ℚ) 14.0 14.3 5.1 ∧ qAlphaObs (-(1.0) : ℚ) 14.0 14.3 5.1 < 1 ∧
        ¬ ∃ lam : ℚ, qModelConsistent3 lam (-(1.0) : ℚ) 2.2 4.6 14.0 13.3 10.0) ∧
      (0 < qAlphaObs (-(0.8) : ℚ) 15.6 9.9 7.3 ∧ qAlphaObs (-(0.8) : ℚ) 15.6 9.9 7.3 < 1 ∧
        ¬ ∃ lam : ℚ, qModelConsistent3 lam (-(0.8) : ℚ) 7.1 9.9 15.6 11.0 7.3) ∧
      (0 < qAlphaObs (-(7.62) : ℚ) 12.38 (-(19.82)) 21.72 ∧
        qAlphaObs (-(7.62) : ℚ) 12.38 (-(19.82)) 21.72 < 1 ∧
        ¬ ∃ lam : ℚ, qModelConsistent3 lam (-(14.56) : ℚ) (-(15.8)) (-(19.82)) 17.47 20.32 21.72) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    first
      | (unfold qAlphaObs; norm_num)
      | exact inst_I11_F1_not_model_consistent
      | exact inst_I11_F2_not_model_consistent
      | exact inst_I11_F3_not_model_consistent
      | exact inst_I11_F5_not_model_consistent

/-- Non-vacuity of the instance layer: a conforming verdict and a non-conforming one both exist. -/
theorem inst_nonvacuous :
    (∃ lam x : ℚ, epQVerdict lam x = EPQVerdict.conforming) ∧
      (∃ lam x : ℚ, epQVerdict lam x = EPQVerdict.subLinear) ∧
      (∃ lam tol w : ℚ, qConformsWindow lam tol w) ∧
      (∃ lam tol w : ℚ, ¬ qConformsWindow lam tol w) :=
  ⟨⟨2, 0, inst_I1_thermoneutral_zone⟩, ⟨2, 3, inst_I6_inverted_zone⟩,
    ⟨2, 1 / 4, 0, inst_I1_thermoneutral_conforms⟩, ⟨2, 1 / 16, 1, inst_I10_threshold_fails⟩⟩

/-! ## Measured notes of this topic

* `norm_num` **does** close the `epQVerdict` cascade: `unfold epQVerdict qTransfer; norm_num`
  evaluates the whole `if`-chain of concrete rational comparisons (measured on all six verdicts of
  I1, I4–I9). No `split_ifs`/`decide` case bash is needed.
* Decimal ℚ literals are first-class: `(15.6 : ℚ)`, `(0.3 : ℚ)`, `(7.62 : ℚ)` all normalise by
  `norm_num` (used for the verbatim literature rows).
* `qSecondDividedDiff` must be passed to `norm_num` as a simp lemma (or `unfold`ed) — it is not a
  `norm_num` extension; with the `unfold` form the literal arithmetic is still one `norm_num` call.
* The falsification rows need no new machinery: `qModelConsistent3_curvature_pos` + the computed
  negative value + `norm_num at hpos` is the whole proof.
* F4 (Table 2 "PE") cannot be stated: §R1.10 prints only family aggregates for it.
-/

end PhotoLean.BEP.ProbeInstances
