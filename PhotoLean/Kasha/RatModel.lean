/-
PhotoLean.Kasha.RatModel — K5a, the computable rational verdict layer of the Kasha theory.

**Why a rational copy.** Kasha's rule is delivered over ℝ in `PhotoLean/Kasha/Basic.lean` (K1)
and its laws in `PhotoLean/Kasha/Criterion.lean` (K2). The order on ℝ goes through `Classical`
and is not computable, so "which regime does this rate data sit in" cannot be decided by the
kernel over ℝ; over ℚ both the order and the equality are decidable and the arithmetic is
executable. This module is therefore the ℚ mirror of K1's definitions — the same bodies with `ℚ`
in place of `ℝ` — plus the eight transfer lemmas that carry a rational verdict to the real theory.
The evidence chain of the instance layer (K5b, `PhotoLean/Kasha/Instances.lean`) is: kernel
computation of the rational verdict → these transfer lemmas → K1/K2/K3 over ℝ. Nothing below
involves ℝ except the transfer lemmas, and nothing below is `noncomputable`: every declaration in
this layer is a computable rational function, so `kashaQVerdict` is a genuine decision procedure.

**Measured recipe** (K-PROBE-2, kernel evidence `theories/kasha/probes/kasha-rat-probe.lean`):
the concrete instance rows are closed by
`norm_num [<definitions>, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]`.
`by decide` cannot close them: the `Decidable` instance of an equality of division-bearing `ℚ`
terms does not reduce (`instDecidableEqRat` gets stuck on a non-reducing `.num`), and a goal
stated through a `Prop`-valued definition gets no instance at all before the definition is
unfolded. The alternative decision procedure that does evaluate them through the compiler is
excluded by the axiom discipline (`Lean.ofReduceBool` is not among `ALLOWED_AXIOMS`). The generic
rows below do not rely on the `simp` discharger for the empty-`Icc` side condition: they use
`rw [Finset.Icc_eq_empty_iff.mpr (by omega), Finset.prod_empty]`, as calibrated in
`theories/kasha/probes/kasha-api-cascade.lean`.

**Statement authority**: the K5a section of
`theories/kasha/probes/kasha-statement-skeleton.lean` (frozen state, sha256
`b645cbfbf61ecf08a7c5dbe3a5e5f8f8874e50cbc806e994ea53823dbf63aa17`, 150 declarations), which transcribes
`theories/kasha/plan.md` §8.1. Every definition body, every theorem signature and every leading
docstring below is that block word for word, including the two statement corrections of
2026-09-20 recorded in the plan's §3.1 correction log:
* `kashaWithinQ_iff_funnelRatioQ` carries `(h1 : 0 < decayQ rad ic 1)`. Without it the row is
  FALSE — at `rad = twoRad 1 1`, `ic = twoIc 0 (-1)`, `tol = 1/2` every premise holds, yet
  `decayQ rad ic 1 = 0` makes `upperYieldQ` and `fluoYieldQ` vanish (left side `0 ≤ 0`, true)
  while `funnelRatioQ = -1` (right side `1 ≤ -1`, false). Kernel witness:
  `probe_criterion_premises_insufficient` in `theories/kasha/probes/kasha-rat-probe.lean`.
* `kashaQVerdict_eq_violating_iff` carries `(htol : 0 < tol)`. Without it the row is FALSE — the
  classifier tests the vanishing leak first, so `upperYieldQ = 0` parks the verdict in `pure`
  while `¬ KashaWithinQ` can still hold when the tolerance is negative (witness `rad ≡ 1`,
  `ic ≡ 1`, `N = 0`, `tol = -1`; the ℝ-side twin is
  `theories/kasha/probes/kasha-k1-counterexample.lean`).

**What is NOT derived here** (plan §12, §13): the ladder model itself, the identification of the
branching probabilities with competing exponential clocks, the reading of the time-integrated
yields as spectroscopic observables, and the interpretation of `ic 0` as the lowest state's loss
channel. They are modelling assumptions of K1 and are inherited by this layer, not re-proved. The
transfer lemmas below are *conditional*: they say that if the rational predicate holds, then the
real one does — they do not assert that either holds.

Every physical premise is an explicit hypothesis of the statement that needs it (`QRateData` is
the ℚ mirror of `RateData`); nothing is hidden in a definition. Plan locus: `theories/kasha/plan.md`
§8.1; board `theories/kasha/TASKS.md` §K5a. Imports: `Mathlib` + `PhotoLean.Kasha.Basic` only —
this layer is deliberately independent of K2/K3/K4.

Acceptance commands (run on a clean tree):

    proofs/scripts/lake build PhotoLean.Kasha.RatModel
    proofs/scripts/check.sh --strict PhotoLean.Kasha.RatModel
    proofs/scripts/axioms.sh PhotoLean.Kasha.RatModel PhotoLean.Kasha.<fully.qualified.theorem>

The delivered file contains no unfinished-proof placeholder and no custom axiomatic declaration;
the `#print axioms` gate of every theorem below lists at most `propext`, `Classical.choice`,
`Quot.sound`.
-/
import Mathlib
import PhotoLean.Kasha.Basic

open scoped BigOperators

set_option autoImplicit false

namespace PhotoLean

namespace Kasha

/-! ## Definitions (plan §8.1) -/

/-- Rational total decay rate (plan §8.1). -/
def decayQ (rad ic : ℕ → ℚ) (n : ℕ) : ℚ := rad n + ic n

/-- Rational radiative branch (plan §8.1). -/
def radBranchQ (rad ic : ℕ → ℚ) (n : ℕ) : ℚ := rad n / decayQ rad ic n

/-- Rational nonradiative branch (plan §8.1). -/
def icBranchQ (rad ic : ℕ → ℚ) (n : ℕ) : ℚ := ic n / decayQ rad ic n

/-- Rational cascade probability (plan §8.1). -/
def cascadeQ (rad ic : ℕ → ℚ) (i N : ℕ) : ℚ := ∏ j ∈ Finset.Icc (i + 1) N, icBranchQ rad ic j

/-- Rational level-resolved emission yield (plan §8.1). -/
def emitYieldQ (rad ic : ℕ → ℚ) (i N : ℕ) : ℚ := radBranchQ rad ic i * cascadeQ rad ic i N

/-- Rational total emission yield (plan §8.1). -/
def fluoYieldQ (rad ic : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (N + 1), emitYieldQ rad ic i N

/-- Rational leak (plan §8.1). -/
def upperYieldQ (rad ic : ℕ → ℚ) (N : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 N, emitYieldQ rad ic i N

/-- Rational two-level funnel ratio (plan §8.1). -/
def funnelRatioQ (rad ic : ℕ → ℚ) : ℚ := rad 0 * ic 1 / (rad 1 * decayQ rad ic 0)

/-- Rational N-level funnel ratio (plan §8.1). -/
def ladderRatioQ (rad ic : ℕ → ℚ) (N : ℕ) : ℚ :=
  rad 0 * cascadeQ rad ic 0 N / (upperYieldQ rad ic N * decayQ rad ic 0)

/-- Rational tolerance predicate (plan §8.1). -/
def KashaWithinQ (rad ic : ℕ → ℚ) (tol : ℚ) (N : ℕ) : Prop :=
  upperYieldQ rad ic N ≤ tol * fluoYieldQ rad ic N

/-- Rational standing premise bundle (plan §8.1). -/
def QRateData (rad ic : ℕ → ℚ) (N : ℕ) : Prop :=
  (∀ n, n ≤ N → 0 < decayQ rad ic n) ∧ (∀ n, 0 ≤ rad n) ∧ (∀ n, 0 ≤ ic n)

/-- Three-valued rational verdict (plan §8.1). -/
inductive KashaQVerdict where
  | pure
  | withinTol
  | violating

/-- The rational verdict classifier (plan §8.1). -/
def kashaQVerdict (rad ic : ℕ → ℚ) (tol : ℚ) (N : ℕ) : KashaQVerdict :=
  if upperYieldQ rad ic N = 0 then KashaQVerdict.pure
  else if upperYieldQ rad ic N ≤ tol * fluoYieldQ rad ic N then KashaQVerdict.withinTol
  else KashaQVerdict.violating

/-- Two-level radiative data `(rad 0, rad 1)` written as a ladder (plan §8.2). -/
def twoRad (r0 r1 : ℚ) : ℕ → ℚ := fun n => if n = 0 then r0 else if n = 1 then r1 else 0

/-- Two-level nonradiative data `(ic 0, ic 1)` written as a ladder (plan §8.2). -/
def twoIc (i0 i1 : ℚ) : ℕ → ℚ := fun n => if n = 0 then i0 else if n = 1 then i1 else 0

/-- Three-level radiative data (plan §8.2). -/
def threeRad (r0 r1 r2 : ℚ) : ℕ → ℚ :=
  fun n => if n = 0 then r0 else if n = 1 then r1 else if n = 2 then r2 else 0

/-- Three-level nonradiative data (plan §8.2). -/
def threeIc (i0 i1 i2 : ℚ) : ℕ → ℚ :=
  fun n => if n = 0 then i0 else if n = 1 then i1 else if n = 2 then i2 else 0

/-- Plan §8.1 cast bridge. -/
theorem decayQ_cast (rad ic : ℕ → ℚ) (n : ℕ) :
    ((decayQ rad ic n : ℚ) : ℝ) = decay (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) n := by
  unfold decayQ decay
  push_cast
  ring

/-- Plan §8.1 cast bridge. -/
theorem radBranchQ_cast (rad ic : ℕ → ℚ) (n : ℕ) :
    ((radBranchQ rad ic n : ℚ) : ℝ)
      = radBranch (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) n := by
  unfold radBranchQ radBranch
  rw [Rat.cast_div, decayQ_cast]

/-- Plan §8.1 cast bridge. -/
theorem icBranchQ_cast (rad ic : ℕ → ℚ) (n : ℕ) :
    ((icBranchQ rad ic n : ℚ) : ℝ)
      = icBranch (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) n := by
  unfold icBranchQ icBranch
  rw [Rat.cast_div, decayQ_cast]

/-- Plan §8.1 cast bridge. -/
theorem cascadeQ_cast (rad ic : ℕ → ℚ) (i N : ℕ) :
    ((cascadeQ rad ic i N : ℚ) : ℝ)
      = cascade (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) i N := by
  unfold cascadeQ cascade
  rw [Rat.cast_prod]
  exact Finset.prod_congr rfl fun j _ => icBranchQ_cast rad ic j

/-- Plan §8.1 cast bridge. -/
theorem emitYieldQ_cast (rad ic : ℕ → ℚ) (i N : ℕ) :
    ((emitYieldQ rad ic i N : ℚ) : ℝ)
      = emitYield (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) i N := by
  unfold emitYieldQ emitYield
  rw [Rat.cast_mul, radBranchQ_cast, cascadeQ_cast]

/-- Plan §8.1 cast bridge. -/
theorem fluoYieldQ_cast (rad ic : ℕ → ℚ) (N : ℕ) :
    ((fluoYieldQ rad ic N : ℚ) : ℝ)
      = fluoYield (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) N := by
  unfold fluoYieldQ fluoYield
  rw [Rat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => emitYieldQ_cast rad ic i N

/-- Plan §8.1 cast bridge. -/
theorem upperYieldQ_cast (rad ic : ℕ → ℚ) (N : ℕ) :
    ((upperYieldQ rad ic N : ℚ) : ℝ)
      = upperYield (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) N := by
  unfold upperYieldQ upperYield
  rw [Rat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => emitYieldQ_cast rad ic i N

/-- Plan §8.1 cast bridge: the rational criterion transfers to the real one. -/
theorem kashaWithinQ_iff_cast {rad ic : ℕ → ℚ} {tol : ℚ} {N : ℕ} :
    KashaWithinQ rad ic tol N ↔
      KashaWithin (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) (tol : ℝ) N := by
  unfold KashaWithinQ KashaWithin
  rw [← upperYieldQ_cast, ← fluoYieldQ_cast, ← Rat.cast_mul]
  exact (Rat.cast_le (K := ℝ)).symm

/-- Plan §8.1 — the rational threshold. **Corrected 2026-09-20** (prover_c's kernel counterexample
`probe_criterion_premises_insufficient`, found independently of prover_b's ℝ-side witness): without
`0 < decayQ rad ic 1` the row is FALSE at `rad = twoRad 1 1`, `ic = twoIc 0 (-1)`, `tol = 1/2`. -/
theorem kashaWithinQ_iff_funnelRatioQ {rad ic : ℕ → ℚ} {tol : ℚ} (h0 : 0 < decayQ rad ic 0)
    (h1 : 0 < decayQ rad ic 1) (htol : 0 < tol) (hr : 0 < rad 1) :
    KashaWithinQ rad ic tol 1 ↔ (1 - tol) / tol ≤ funnelRatioQ rad ic := by
  have hp : 0 < rad 1 * decayQ rad ic 0 := mul_pos hr h0
  have hc0 : cascadeQ rad ic 0 1 = ic 1 / decayQ rad ic 1 := by
    unfold cascadeQ icBranchQ
    rw [Finset.Icc_self, Finset.prod_singleton]
  have hc1 : cascadeQ rad ic 1 1 = 1 := by
    unfold cascadeQ
    rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ ((1 : ℕ) + 1 ≤ 1)), Finset.prod_empty]
  have hfl : fluoYieldQ rad ic 1 =
      rad 0 / decayQ rad ic 0 * (ic 1 / decayQ rad ic 1) + rad 1 / decayQ rad ic 1 := by
    unfold fluoYieldQ emitYieldQ radBranchQ
    rw [Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1, mul_one]
  have hup : upperYieldQ rad ic 1 = rad 1 / decayQ rad ic 1 := by
    unfold upperYieldQ emitYieldQ radBranchQ
    rw [Finset.Icc_self, Finset.sum_singleton, hc1, mul_one]
  have h2 : tol * (rad 0 / decayQ rad ic 0 * (ic 1 / decayQ rad ic 1) + rad 1 / decayQ rad ic 1)
        * decayQ rad ic 1 = tol * (rad 0 * ic 1 / decayQ rad ic 0) + tol * rad 1 := by
    field_simp
    ring
  have h5 : rad 0 * ic 1 / (rad 1 * decayQ rad ic 0) * tol * (rad 1 * decayQ rad ic 0)
      = tol * (rad 0 * ic 1) := by
    field_simp
    ring
  simp only [KashaWithinQ, hfl, hup, funnelRatioQ]
  constructor
  · intro h
    rw [div_le_iff₀ h1] at h
    rw [h2, ← mul_div_assoc] at h
    have h3 : rad 1 * (1 - tol) ≤ tol * (rad 0 * ic 1) / decayQ rad ic 0 := by nlinarith [h]
    have h4 : rad 1 * (1 - tol) * decayQ rad ic 0 ≤ tol * (rad 0 * ic 1) :=
      (le_div_iff₀ h0).mp h3
    rw [div_le_iff₀ htol, ← mul_le_mul_right hp, h5]
    nlinarith [h4]
  · intro h
    rw [div_le_iff₀ htol, ← mul_le_mul_right hp, h5] at h
    have h3 : rad 1 * (1 - tol) ≤ tol * (rad 0 * ic 1) / decayQ rad ic 0 := by
      refine (le_div_iff₀ h0).mpr ?_
      nlinarith [h]
    rw [div_le_iff₀ h1, h2, ← mul_div_assoc]
    nlinarith [h3]

set_option linter.unusedVariables false in

/-- Plan §8.1 classifier row. -/
theorem kashaQVerdict_eq_pure_iff {rad ic : ℕ → ℚ} {tol : ℚ} {N : ℕ}
    (h : QRateData rad ic N) :
    kashaQVerdict rad ic tol N = KashaQVerdict.pure ↔ upperYieldQ rad ic N = 0 := by
  constructor
  · intro hv
    unfold kashaQVerdict at hv
    split_ifs at hv with h1 h2
    exact h1
  · intro h0
    unfold kashaQVerdict
    exact if_pos h0

set_option linter.unusedVariables false in

/-- Plan §8.1 classifier row. -/
theorem kashaQVerdict_eq_withinTol_iff {rad ic : ℕ → ℚ} {tol : ℚ} {N : ℕ}
    (h : QRateData rad ic N) :
    kashaQVerdict rad ic tol N = KashaQVerdict.withinTol ↔
      upperYieldQ rad ic N ≠ 0 ∧ KashaWithinQ rad ic tol N := by
  unfold kashaQVerdict KashaWithinQ
  split_ifs with h1 h2 <;>
    first
      | exact iff_of_true rfl ⟨h1, h2⟩
      | exact iff_of_false (by intro hh; cases hh) (by rintro ⟨hK, -⟩; exact hK h1)
      | exact iff_of_false (by intro hh; cases hh) (by rintro ⟨-, hw⟩; exact h2 hw)

/-- Plan §8.1 classifier row. **Corrected 2026-09-20** together with its ℝ-side twin
`kashaZone_eq_violating_iff`: without `0 < tol` the row is FALSE at `rad ≡ 1`, `ic ≡ 1`, `N = 0`,
`tol = -1` (the vanishing-leak branch parks the verdict in `pure` while `¬ KashaWithinQ` holds). -/
theorem kashaQVerdict_eq_violating_iff {rad ic : ℕ → ℚ} {tol : ℚ} {N : ℕ}
    (h : QRateData rad ic N) (htol : 0 < tol) :
    kashaQVerdict rad ic tol N = KashaQVerdict.violating ↔ ¬ KashaWithinQ rad ic tol N := by
  have hfl : 0 ≤ fluoYieldQ rad ic N := by
    unfold fluoYieldQ
    refine Finset.sum_nonneg fun i hi => ?_
    rw [Finset.mem_range] at hi
    unfold emitYieldQ
    refine mul_nonneg (div_nonneg (h.2.1 i) (le_of_lt (h.1 i (Nat.le_of_lt_succ hi)))) ?_
    unfold cascadeQ
    refine Finset.prod_nonneg fun j hj => ?_
    exact div_nonneg (h.2.2 j) (le_of_lt (h.1 j (Finset.mem_Icc.mp hj).2))
  constructor
  · intro hv
    unfold kashaQVerdict at hv
    split_ifs at hv with h1 h2
    exact h2
  · intro hw
    have hw' : ¬ (upperYieldQ rad ic N ≤ tol * fluoYieldQ rad ic N) := hw
    have hne : upperYieldQ rad ic N ≠ 0 := by
      intro h0
      exact hw' (by rw [h0]; exact mul_nonneg (le_of_lt htol) hfl)
    unfold kashaQVerdict
    rw [if_neg hne, if_neg hw']

end Kasha

end PhotoLean
