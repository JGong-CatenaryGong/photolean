/-
Statement skeleton for the Kasha theory (Kasha's rule) — the **authority for all delivered
signatures** of `PhotoLean/Kasha/*.lean`. Every delivered declaration must match the corresponding
signature here word for word (plan §3; the mechanical check is
`theories/BEP/probes/bep-fidelity.py --theory kasha`, which is theory-generic). It lives under
`theories/kasha/probes/`, i.e. OUTSIDE `SOURCE_DIRS` (`PhotoLean`), because the source tree has zero
tolerance for the unfinished-proof placeholder keyword; statement-first requires the signatures to
elaborate before any proof work starts. 0 error is the Sprint-0 gate.

Model (plan §1.2). A finite excited-state ladder; level `0` is the lowest excited state of the
multiplicity under consideration (`S₁`), level `n ≥ 1` is the n-th state above it. Each level has a
radiative rate `rad n ≥ 0` and a nonradiative rate `ic n ≥ 0`; for `n ≥ 1` the latter is internal
conversion `n → n-1`, for `n = 0` it is the nonradiative loss to the ground state. The branching
probabilities are `rad n / decay n` and `ic n / decay n` with `decay n = rad n + ic n > 0`
(`RateData`). With excitation at level `N`:

  emitYield i N = (rad i / decay i) · ∏_{j ∈ [i+1, N]} (ic j / decay j)    emission from level i
  fluoYield N   = Σ_{i ∈ [0, N]} emitYield i N                             total emission probability
  upperYield N  = Σ_{i ∈ [1, N]} emitYield i N                             emission from above the lowest

`KashaRule rad ic N` is `upperYield rad ic N = 0` (the exact rule), `KashaWithin rad ic tol N` is
`upperYield ≤ tol · fluoYield` (its tolerance form), `VavilovAt rad ic N` is the excitation-level
invariance of the total yield (Vavilov's rule).

Every physical premise is an explicit hypothesis — nothing is hidden in a definition (engine rule 3).

Provenance of the rows below: `theories/kasha/plan.md` §4 (K1), §5 (K2), §6 (K3), §7 (K4), §8 (K5);
each docstring carries its plan locus. The literature rows of §K5b (I10–I12) are **not** in this
version: they are appended when `theories/kasha/LITERATURE.md` round 1 lands the printed numbers
(the api-researcher/lead append records the change in `proofs/API-NOTES.md`).

API calibration for this file: `proofs/API-NOTES.md` §kasha; kernel evidence for every recipe:
`theories/kasha/probes/kasha-api-*.lean`.
-/
import Mathlib
import PhotoLean.Marcus.Basic

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Kasha

/-! ## K1 — description layer (`PhotoLean/Kasha/Basic.lean`; plan §4) -/

/-- Total decay rate of level `n`: the sum of its radiative and its nonradiative channel. -/
noncomputable def decay (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := rad n + ic n

/-- Probability that level `n` decays radiatively (emits a photon). -/
noncomputable def radBranch (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := rad n / decay rad ic n

/-- Probability that level `n` decays nonradiatively: internal conversion `n → n-1` for `n ≥ 1`,
loss to the ground state for `n = 0`. -/
noncomputable def icBranch (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := ic n / decay rad ic n

/-- Probability that, starting at level `N`, the molecule reaches level `i` without having emitted
(plan §1.2). -/
noncomputable def cascade (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (i + 1) N, icBranch rad ic j

/-- Time-integrated emission yield of level `i` under excitation at level `N`. -/
noncomputable def emitYield (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ := radBranch rad ic i * cascade rad ic i N

/-- Total fluorescence quantum yield under excitation at level `N` (plan §1.2). -/
noncomputable def fluoYield (rad ic : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), emitYield rad ic i N

/-- Emission from levels **above** the lowest one — the leak past the funnel of Kasha's rule. -/
noncomputable def upperYield (rad ic : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 N, emitYield rad ic i N

/-- The normalized emission spectrum: the fraction of the emitted photons that comes from level
`i` (plan §1.2). -/
noncomputable def specFrac (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ := emitYield rad ic i N / fluoYield rad ic N

/-- Funnel margin of the N-level ladder: how much emission from the lowest level accompanies one
unit of leak (plan §2, §6.1 #5). -/
noncomputable def kashaMargin (rad ic : ℕ → ℝ) (N : ℕ) : ℝ :=
  emitYield rad ic 0 N / upperYield rad ic N

/-- The two-level funnel ratio: the `k_IC / k_rad`-shaped quantity whose threshold is the sharp
criterion (plan §1.3, §6.1 #2). -/
noncomputable def funnelRatio (rad ic : ℕ → ℝ) : ℝ := rad 0 * ic 1 / (rad 1 * decay rad ic 0)

/-- The N-level funnel ratio: the quantity the general threshold tests (plan §6.1 #5, §7.2 #9). -/
noncomputable def ladderRatio (rad ic : ℕ → ℝ) (N : ℕ) : ℝ :=
  rad 0 * cascade rad ic 0 N / (upperYield rad ic N * decay rad ic 0)

/-- The exact Kasha rule: no emission from above the lowest excited state (plan §4.1). -/
def KashaRule (rad ic : ℕ → ℝ) (N : ℕ) : Prop := upperYield rad ic N = 0

/-- The tolerance form of the rule: the fraction of emitted photons that does not come from the
lowest state is at most `tol` (plan §4.1). -/
def KashaWithin (rad ic : ℕ → ℝ) (tol : ℝ) (N : ℕ) : Prop :=
  upperYield rad ic N ≤ tol * fluoYield rad ic N

/-- Vavilov's rule at one step: raising the excitation level from `N` to `N+1` leaves the total
fluorescence yield unchanged (plan §4.1). -/
def VavilovAt (rad ic : ℕ → ℝ) (N : ℕ) : Prop := fluoYield rad ic (N + 1) = fluoYield rad ic N

/-- Vavilov's rule up to level `N` (plan §4.1). -/
def VavilovUpTo (rad ic : ℕ → ℝ) (N : ℕ) : Prop := ∀ i, i < N → VavilovAt rad ic i

/-- The Kasha description is realized by this ladder data: some excitation level satisfies the exact
rule (non-vacuity, plan §4.1). -/
def KashaDescriptor (rad ic : ℕ → ℝ) : Prop := ∃ N, KashaRule rad ic N

/-- The standing physical premise bundle: positive total decay rates up to the excitation level,
nonnegative radiative and nonradiative rates (plan §2, §4.1). -/
structure RateData (rad ic : ℕ → ℝ) (N : ℕ) : Prop where
  decay_pos : ∀ n, n ≤ N → 0 < decay rad ic n
  rad_nonneg : ∀ n, 0 ≤ rad n
  ic_nonneg : ∀ n, 0 ≤ ic n

/-- Decidable regime classifier of a ladder at tolerance `tol` and excitation level `N` (plan §4.1). -/
inductive KashaZone where
  | pure
  | withinTol
  | violating

/-- The classifier: `pure` for the exact rule, `withinTol` inside the tolerance, `violating`
outside it (plan §4.1). -/
noncomputable def kashaZone (rad ic : ℕ → ℝ) (tol : ℝ) (N : ℕ) : KashaZone :=
  if upperYield rad ic N = 0 then KashaZone.pure
  else if upperYield rad ic N ≤ tol * fluoYield rad ic N then KashaZone.withinTol
  else KashaZone.violating

/-! ### K1 theorems (plan §4.2) -/

/-- Plan §4.2 #1. -/
theorem decay_eq_rad_add_ic (rad ic : ℕ → ℝ) (n : ℕ) : decay rad ic n = rad n + ic n := by
  sorry

/-- Plan §4.2 #2. -/
theorem radBranch_add_icBranch {rad ic : ℕ → ℝ} {n : ℕ} (h : decay rad ic n ≠ 0) :
    radBranch rad ic n + icBranch rad ic n = 1 := by
  sorry

/-- Plan §4.2 #3. -/
theorem radBranch_nonneg {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    0 ≤ radBranch rad ic n := by
  sorry

/-- Plan §4.2 #4. -/
theorem icBranch_nonneg {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    0 ≤ icBranch rad ic n := by
  sorry

/-- Plan §4.2 #5. -/
theorem radBranch_le_one {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    radBranch rad ic n ≤ 1 := by
  sorry

/-- Plan §4.2 #6. -/
theorem icBranch_le_one {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    icBranch rad ic n ≤ 1 := by
  sorry

/-- Plan §4.2 #7. -/
theorem cascade_self (rad ic : ℕ → ℝ) (i : ℕ) : cascade rad ic i i = 1 := by
  sorry

/-- Plan §4.2 #8. -/
theorem cascade_nonneg {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N) (h1 : i ≤ N) :
    0 ≤ cascade rad ic i N := by
  sorry

/-- Plan §4.2 #9. -/
theorem cascade_le_one {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N) (h1 : i ≤ N) :
    cascade rad ic i N ≤ 1 := by
  sorry

/-- Plan §4.2 #10. -/
theorem emitYield_self (rad ic : ℕ → ℝ) (i : ℕ) : emitYield rad ic i i = radBranch rad ic i := by
  sorry

/-- Plan §4.2 #11. -/
theorem emitYield_nonneg {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N) (h1 : i ≤ N) :
    0 ≤ emitYield rad ic i N := by
  sorry

/-- Plan §4.2 #12. -/
theorem emitYield_le_radBranch {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N) (h1 : i ≤ N) :
    emitYield rad ic i N ≤ radBranch rad ic i := by
  sorry

/-- Plan §4.2 #13. -/
theorem fluoYield_eq_low_add_upper {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    fluoYield rad ic N = emitYield rad ic 0 N + upperYield rad ic N := by
  sorry

/-- Plan §4.2 #14. -/
theorem fluoYield_zero (rad ic : ℕ → ℝ) : fluoYield rad ic 0 = radBranch rad ic 0 := by
  sorry

/-- Plan §4.2 #15. -/
theorem upperYield_zero (rad ic : ℕ → ℝ) : upperYield rad ic 0 = 0 := by
  sorry

/-- Plan §4.2 #16. -/
theorem fluoYield_nonneg {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    0 ≤ fluoYield rad ic N := by
  sorry

/-- Plan §4.2 #17. -/
theorem upperYield_nonneg {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    0 ≤ upperYield rad ic N := by
  sorry

/-- Plan §4.2 #18. -/
theorem upperYield_le_fluoYield {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    upperYield rad ic N ≤ fluoYield rad ic N := by
  sorry

/-- Plan §4.2 #19. -/
theorem kashaRule_iff_upperYield_zero (rad ic : ℕ → ℝ) (N : ℕ) :
    KashaRule rad ic N ↔ upperYield rad ic N = 0 := by
  sorry

/-- Plan §4.2 #20. -/
theorem specFrac_sum {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N)
    (hF : fluoYield rad ic N ≠ 0) :
    ∑ i ∈ Finset.range (N + 1), specFrac rad ic i N = 1 := by
  sorry

/-- Plan §4.2 #21. -/
theorem kashaWithin_iff_specFrac {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ} (h : RateData rad ic N)
    (hF : fluoYield rad ic N ≠ 0) :
    KashaWithin rad ic tol N ↔ 1 - specFrac rad ic 0 N ≤ tol := by
  sorry

/-- Plan §4.2 #22. -/
theorem kashaZone_eq_pure_iff {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ} (h : RateData rad ic N) :
    kashaZone rad ic tol N = KashaZone.pure ↔ KashaRule rad ic N := by
  sorry

/-- Plan §4.2 #23. -/
theorem kashaZone_eq_withinTol_iff {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ} (h : RateData rad ic N) :
    kashaZone rad ic tol N = KashaZone.withinTol ↔
      ¬ KashaRule rad ic N ∧ KashaWithin rad ic tol N := by
  sorry

/-- Plan §4.2 #24. **Corrected 2026-09-20** (prover_a's kernel counterexample
`theories/kasha/probes/kasha-k1-counterexample.lean`): as first handed over, without the tolerance
premise, this row was FALSE — the classifier tests the vanishing leak first, so `upperYield = 0`
parks it in `pure` and `¬ KashaWithin` can hold there whenever `tol < 0`. The premise `0 < tol` (the
physical range of the tolerance) restores it: `upperYield = 0` then implies `KashaWithin`. -/
theorem kashaZone_eq_violating_iff {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ} (h : RateData rad ic N)
    (htol : 0 < tol) :
    kashaZone rad ic tol N = KashaZone.violating ↔ ¬ KashaWithin rad ic tol N := by
  sorry

/-- Plan §4.2 #25. -/
theorem kashaRule_of_rad_zero {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N)
    (hzero : ∀ i, 1 ≤ i → i ≤ N → rad i = 0) : KashaRule rad ic N := by
  sorry

/-! ## K2 — law layer (`PhotoLean/Kasha/Criterion.lean`; plan §5) -/

/-- Plan §5.1 #1. -/
theorem cascade_succ {rad ic : ℕ → ℝ} {i N : ℕ} (h : i ≤ N) :
    cascade rad ic i (N + 1) = icBranch rad ic (N + 1) * cascade rad ic i N := by
  sorry

/-- Plan §5.1 #2. -/
theorem emitYield_succ {rad ic : ℕ → ℝ} {i N : ℕ} (h : i ≤ N) :
    emitYield rad ic i (N + 1) = icBranch rad ic (N + 1) * emitYield rad ic i N := by
  sorry

/-- Plan §5.1 #3. -/
theorem emitYield_succ_self (rad ic : ℕ → ℝ) (N : ℕ) :
    emitYield rad ic (N + 1) (N + 1) = radBranch rad ic (N + 1) := by
  sorry

/-- Plan §5.1 #4 — the Markov recursion of the total yield. -/
theorem fluoYield_succ {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1)) :
    fluoYield rad ic (N + 1) =
      radBranch rad ic (N + 1) + icBranch rad ic (N + 1) * fluoYield rad ic N := by
  sorry

/-- Plan §5.1 #5 — the Markov recursion of the leak. -/
theorem upperYield_succ {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1)) :
    upperYield rad ic (N + 1) =
      radBranch rad ic (N + 1) + icBranch rad ic (N + 1) * upperYield rad ic N := by
  sorry

/-- Plan §5.1 #6 — probability conservation: the cascade probability plus the leak is one. -/
theorem cascade_add_upperYield {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    cascade rad ic 0 N + upperYield rad ic N = 1 := by
  sorry

/-- Plan §5.1 #7 — the total yield is one minus the ground-state loss. -/
theorem fluoYield_eq_one_sub_loss {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    fluoYield rad ic N = 1 - icBranch rad ic 0 * cascade rad ic 0 N := by
  sorry

/-- Plan §5.1 #8. -/
theorem fluoYield_le_one {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    fluoYield rad ic N ≤ 1 := by
  sorry

/-- Plan §5.1 #9. -/
theorem fluoYield_mono_succ {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1)) :
    fluoYield rad ic N ≤ fluoYield rad ic (N + 1) := by
  sorry

/-- Plan §5.1 #10. -/
theorem fluoYield_lt_succ_of_rad_pos {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1))
    (hr : 0 < rad (N + 1)) (h1 : fluoYield rad ic N < 1) :
    fluoYield rad ic N < fluoYield rad ic (N + 1) := by
  sorry

/-- Plan §5.1 #11. -/
theorem fluoYield_eq_iff_rad_zero {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1))
    (h1 : fluoYield rad ic N < 1) :
    fluoYield rad ic (N + 1) = fluoYield rad ic N ↔ rad (N + 1) = 0 := by
  sorry

/-- Plan §5.1 #12. -/
theorem fluoYield_lt_one_iff_loss {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    fluoYield rad ic N < 1 ↔ 0 < icBranch rad ic 0 * cascade rad ic 0 N := by
  sorry

/-- Plan §5.2 #13. -/
theorem upperYield_eq_zero_iff {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    upperYield rad ic N = 0 ↔ ∀ i, 1 ≤ i → i ≤ N → emitYield rad ic i N = 0 := by
  sorry

/-- Plan §5.2 #14 — **the exact rule**: Kasha's rule holds iff no level above the lowest one
emits at all. -/
theorem kashaRule_iff_rad_zero {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    KashaRule rad ic N ↔ ∀ i, 1 ≤ i → i ≤ N → rad i = 0 := by
  sorry

/-- Plan §5.2 #15. -/
theorem not_kashaRule_of_rad_pos {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N)
    (h1 : 1 ≤ i) (h2 : i ≤ N) (hr : 0 < rad i) : ¬ KashaRule rad ic N := by
  sorry

/-- Plan §5.2 #16. -/
theorem vavilovAt_iff_rad_zero {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1))
    (h1 : fluoYield rad ic N < 1) : VavilovAt rad ic N ↔ rad (N + 1) = 0 := by
  sorry

/-- Plan §5.2 #17. -/
theorem vavilovUpTo_iff_rad_zero {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N)
    (h1 : ∀ i, i < N → fluoYield rad ic i < 1) :
    VavilovUpTo rad ic N ↔ ∀ i, i < N → rad (i + 1) = 0 := by
  sorry

/-- Plan §5.2 #18 — **the Kasha–Vavilov equivalence**: with a loss channel at the lowest level, the
spectral rule and the excitation-independence of the yield are the same condition. -/
theorem kashaRule_iff_vavilovUpTo {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N)
    (hloss : 0 < ic 0) : KashaRule rad ic N ↔ VavilovUpTo rad ic N := by
  sorry

/-- Plan §5.2 #19 — **the rule is not a theorem of the model**: there is admissible rate data that
violates it. -/
theorem not_kasha_universal :
    ∃ (rad ic : ℕ → ℝ) (N : ℕ), RateData rad ic N ∧ ¬ KashaRule rad ic N := by
  sorry

/-- Plan §5.2 #20 — non-vacuity of the description. -/
theorem kashaDescriptor_nonvacuous : ∃ rad ic : ℕ → ℝ, KashaDescriptor rad ic := by
  sorry

/-- Plan §5.2 #21. -/
theorem kashaWithin_of_kashaRule {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ} (h : RateData rad ic N)
    (htol : 0 ≤ tol) (hK : KashaRule rad ic N) : KashaWithin rad ic tol N := by
  sorry

/-- Plan §5.2 #22. -/
theorem upperYield_le_sum_radBranch {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    upperYield rad ic N ≤ ∑ i ∈ Finset.Icc 1 N, radBranch rad ic i := by
  sorry

/-! ## K3 — sharp conditions (`PhotoLean/Kasha/Sharp.lean`; plan §6) -/

/-- Plan §6.1 #1 — the exact two-level criterion in rate form. -/
theorem kashaWithin_one_iff_rates {rad ic : ℕ → ℝ} {tol : ℝ} (h0 : 0 < decay rad ic 0)
    (h1 : 0 < decay rad ic 1) :
    KashaWithin rad ic tol 1 ↔ rad 1 * decay rad ic 0 * (1 - tol) ≤ tol * (rad 0 * ic 1) := by
  sorry

/-- Plan §6.1 #2 — **the funnel-ratio threshold** (two-level form). **Corrected 2026-09-20**
(prover_b's kernel counterexample `risk_kashaWithin_one_iff_ratio_refuted`): without
`0 < decay rad ic 1` the row is FALSE — the rate-form criterion is equivalent to the ratio form
only after multiplying by the positive factor `decay 1`, and with `decay 1 < 0` the cross
multiplication flips the inequality (witness `rad = (1,1,0,…)`, `ic = (1,-3,0,…)`, `tol = 1/2`).
The premise is now explicit, matching its sibling row K3 #1. -/
theorem kashaWithin_one_iff_ratio {rad ic : ℕ → ℝ} {tol : ℝ} (h0 : 0 < decay rad ic 0)
    (h1 : 0 < decay rad ic 1) (htol : 0 < tol) (hr : 0 < rad 1) :
    KashaWithin rad ic tol 1 ↔ (1 - tol) / tol ≤ funnelRatio rad ic := by
  sorry

/-- Plan §6.1 #3 — the literature form: with no other loss at the lowest level, the rule needs
`ic 1 / rad 1 ≥ (1 - tol) / tol` (for `tol = 1/100`: `99`). -/
theorem kashaWithin_one_iff_ic_ratio {rad ic : ℕ → ℝ} {tol : ℝ} (hic0 : ic 0 = 0)
    (hr0 : rad 0 ≠ 0) (htol : 0 < tol) (h1 : 0 < decay rad ic 1) (hr : 0 < rad 1) :
    KashaWithin rad ic tol 1 ↔ (1 - tol) / tol ≤ ic 1 / rad 1 := by
  sorry

/-- Plan §6.1 #4. -/
theorem funnelRatio_eq_ladderRatio_one {rad ic : ℕ → ℝ} (h : decay rad ic 1 ≠ 0) :
    funnelRatio rad ic = ladderRatio rad ic 1 := by
  sorry

/-- Plan §6.1 #5 — the general-N criterion in margin form. -/
theorem kashaWithin_iff_margin {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ} (h : RateData rad ic N)
    (hu : 0 < upperYield rad ic N) (htol : 0 < tol) :
    KashaWithin rad ic tol N ↔ 1 - tol ≤ tol * kashaMargin rad ic N := by
  sorry

/-- Plan §6.1 #6. -/
theorem kashaWithin_mono_tol {rad ic : ℕ → ℝ} {N : ℕ} {tol tol' : ℝ} (h : RateData rad ic N)
    (hle : tol ≤ tol') (hW : KashaWithin rad ic tol N) : KashaWithin rad ic tol' N := by
  sorry

/-- Plan §6.1 #7 — exactness: at zero tolerance the rule is the exact rule. -/
theorem kashaWithin_zero_iff {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    KashaWithin rad ic 0 N ↔ KashaRule rad ic N := by
  sorry

/-- Plan §6.1 #8 — the criterion is monotone in the internal-conversion rate. -/
theorem kashaWithin_one_mono_ic {rad ic rad' ic' : ℕ → ℝ} {tol : ℝ} (h : RateData rad ic 1)
    (h' : RateData rad' ic' 1) (hrad : ∀ n, rad' n = rad n) (hic0 : ic' 0 = ic 0)
    (hic : ic 1 ≤ ic' 1) : KashaWithin rad ic tol 1 → KashaWithin rad' ic' tol 1 := by
  sorry

/-- Plan §6.2 #9 — the strict failure side of the threshold. **Corrected 2026-09-20** together with
its sibling row K3 #2: it needs the same explicit `0 < decay rad ic 1` (otherwise the ratio form is
not equivalent to the criterion and the claim fails on the same witness). -/
theorem not_kashaWithin_one_of_ratio_lt {rad ic : ℕ → ℝ} {tol : ℝ} (h0 : 0 < decay rad ic 0)
    (h1 : 0 < decay rad ic 1) (htol : 0 < tol) (hr : 0 < rad 1)
    (h : funnelRatio rad ic < (1 - tol) / tol) : ¬ KashaWithin rad ic tol 1 := by
  sorry

/-- Plan §6.2 #10 — **attainment**: for every tolerance in `(0,1)` the threshold is met exactly
and cannot be improved. -/
theorem kashaThreshold_attained {tol : ℝ} (h0 : 0 < tol) (h1 : tol < 1) :
    ∃ rad ic : ℕ → ℝ, KashaWithin rad ic tol 1 ∧
      (∀ tol' : ℝ, 0 < tol' → tol' < tol → ¬ KashaWithin rad ic tol' 1) := by
  sorry

/-- Plan §6.2 #13 — **the levelwise criterion is insufficient**: an admissible ladder in which
internal conversion beats radiation at every level above the lowest one, and yet three quarters of
the emitted photons come from those levels. -/
theorem perLevel_criterion_insufficient :
    ∃ rad ic : ℕ → ℝ, RateData rad ic 2 ∧
      (∀ i, 1 ≤ i → i ≤ 2 → rad i * decay rad ic (i - 1) ≤ ic i * decay rad ic i) ∧
      ¬ KashaWithin rad ic (1 / 2) 2 := by
  sorry

/-- Plan §6.2 #14 — **the loss premise of the Kasha–Vavilov equivalence is necessary**: with no
loss channel at the lowest level the yield is one at every excitation level, so Vavilov's rule
holds trivially while Kasha's rule fails. -/
theorem vavilov_premise_necessary :
    ∃ (rad ic : ℕ → ℝ) (N : ℕ), RateData rad ic N ∧ rad (N + 1) ≠ 0 ∧
      VavilovAt rad ic N ∧ ¬ KashaRule rad ic N := by
  sorry

/-- Plan §6.2 #16 — the boundary of the threshold is attained with equality. -/
theorem kashaWithin_one_sharp_boundary {tol : ℝ} (h0 : 0 < tol) (h1 : tol < 1) :
    ∃ rad ic : ℕ → ℝ, funnelRatio rad ic = (1 - tol) / tol ∧ KashaWithin rad ic tol 1 := by
  sorry

/-- Plan §6.2 #17. -/
theorem leak_le_of_radBranch_le {rad ic : ℕ → ℝ} {N : ℕ} {θ : ℝ} (h : RateData rad ic N)
    (hθ : ∀ i, 1 ≤ i → i ≤ N → radBranch rad ic i ≤ θ) :
    upperYield rad ic N ≤ θ * ∑ i ∈ Finset.Icc 1 N, cascade rad ic i N := by
  sorry

/-- Plan §6.2 #18. -/
theorem kashaWithin_of_uniform_branch {rad ic : ℕ → ℝ} {N : ℕ} {tol θ : ℝ} (h : RateData rad ic N)
    (hθ : ∀ i, 1 ≤ i → i ≤ N → radBranch rad ic i ≤ θ)
    (hsum : θ * ∑ i ∈ Finset.Icc 1 N, cascade rad ic i N ≤ tol * fluoYield rad ic N) :
    KashaWithin rad ic tol N := by
  sorry

/-! ## K4 — composition and bridges (`PhotoLean/Kasha/Compose.lean`; plan §7) -/

/-- Effective two-level radiative data of the ladder at excitation level `N` (plan §7.1). -/
noncomputable def effRad (rad ic : ℕ → ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n => if n = 0 then rad 0 else if n = 1 then upperYield rad ic N else 0

/-- Effective two-level nonradiative data of the ladder at excitation level `N` (plan §7.1). -/
noncomputable def effIc (rad ic : ℕ → ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n => if n = 0 then ic 0 else if n = 1 then cascade rad ic 0 N else 0

/-- The internal-conversion rate in the Marcus form of `PhotoLean.Marcus`: driving force equal to
the energy gap `x`, reorganization energy `lam`, pre-exponential `A` (plan §7.1). -/
noncomputable def marcusIC (A lam kB T x : ℝ) : ℝ :=
  A * Real.exp (-(PhotoLean.Marcus.barrier lam x) / (kB * T))

/-- The gap threshold of the Marcus bridge: the multiplicative constant `K` whose logarithm is the
half-width of the Kasha window (plan §7.1). -/
noncomputable def kashaGapThreshold (A rad0 dec0 rad1 tol : ℝ) : ℝ :=
  A * rad0 * tol / (rad1 * dec0 * (1 - tol))

/-- Plan §7.2 #1. -/
theorem cascade_compose {rad ic : ℕ → ℝ} {i M N : ℕ} (h1 : i ≤ M) (h2 : M ≤ N) :
    cascade rad ic i N = cascade rad ic i M * cascade rad ic M N := by
  sorry

/-- Plan §7.2 #2. -/
theorem emitYield_compose {rad ic : ℕ → ℝ} {i M N : ℕ} (h1 : i ≤ M) (h2 : M ≤ N) :
    emitYield rad ic i N = cascade rad ic M N * emitYield rad ic i M := by
  sorry

/-- Plan §7.2 #3. -/
theorem effDecay_zero (rad ic : ℕ → ℝ) (N : ℕ) :
    decay (effRad rad ic N) (effIc rad ic N) 0 = decay rad ic 0 := by
  sorry

/-- Plan §7.2 #4. -/
theorem effDecay_one (rad ic : ℕ → ℝ) (N : ℕ) :
    decay (effRad rad ic N) (effIc rad ic N) 1
      = upperYield rad ic N + cascade rad ic 0 N := by
  sorry

/-- Plan §7.2 #5. -/
theorem effUpperYield_one {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    upperYield (effRad rad ic N) (effIc rad ic N) 1
      = upperYield rad ic N / (upperYield rad ic N + cascade rad ic 0 N) := by
  sorry

/-- Plan §7.2 #6. -/
theorem effEmitYield_zero_one {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    emitYield (effRad rad ic N) (effIc rad ic N) 0 1
      = emitYield rad ic 0 N / (upperYield rad ic N + cascade rad ic 0 N) := by
  sorry

/-- Plan §7.2 #7 — **the ladder's margin is a two-level margin**. -/
theorem kashaMargin_effective {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N)
    (hu : 0 < upperYield rad ic N) :
    kashaMargin (effRad rad ic N) (effIc rad ic N) 1 = kashaMargin rad ic N := by
  sorry

/-- Plan §7.2 #8 — **every ladder is a two-level model in disguise**: the tolerance criterion of
the N-level ladder is the tolerance criterion of its effective two-level data. -/
theorem kashaWithin_iff_effective {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ} (h : RateData rad ic N)
    (hpos : 0 < upperYield rad ic N + cascade rad ic 0 N) :
    KashaWithin rad ic tol N ↔ KashaWithin (effRad rad ic N) (effIc rad ic N) tol 1 := by
  sorry

/-- Plan §7.2 #9 — **the N-level threshold**: the general answer to "when does the rule hold". -/
theorem kashaWithin_iff_ladderRatio {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ} (h : RateData rad ic N)
    (hu : 0 < upperYield rad ic N) (htol : 0 < tol) (h0 : 0 < decay rad ic 0) :
    KashaWithin rad ic tol N ↔ (1 - tol) / tol ≤ ladderRatio rad ic N := by
  sorry

/-- Plan §7.2 #10. -/
theorem ladderRatio_one {rad ic : ℕ → ℝ} (h : decay rad ic 1 ≠ 0) :
    ladderRatio rad ic 1 = funnelRatio rad ic := by
  sorry

/-- Plan §7.2 #11. -/
theorem not_kashaWithin_of_ladderRatio_lt {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ}
    (h : RateData rad ic N) (hu : 0 < upperYield rad ic N) (htol : 0 < tol)
    (h0 : 0 < decay rad ic 0) (hlt : ladderRatio rad ic N < (1 - tol) / tol) :
    ¬ KashaWithin rad ic tol N := by
  sorry

/-- Plan §7.2 #12 — **the Marcus bridge**: if the `S₂ → S₁` internal conversion follows the Marcus
rate law of this repository, the rule holds iff the energy gap lies below an explicit threshold
(plan §1.3 #5, §7.2). -/
theorem kashaWithin_one_marcus {rad ic : ℕ → ℝ} {A lam kB T x tol : ℝ} (h : RateData rad ic 1)
    (htol0 : 0 < tol) (htol1 : tol < 1) (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    (hr0 : 0 < rad 0) (hr1 : 0 < rad 1) (hic : ic 1 = marcusIC A lam kB T x) :
    KashaWithin rad ic tol 1 ↔
      (lam - x) ^ 2 ≤ 4 * lam * (kB * T) * Real.log (kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol) := by
  sorry

/-- Plan §7.2 #13 — the anti-Kasha direction of the bridge. -/
theorem not_kashaWithin_of_gap_far {rad ic : ℕ → ℝ} {A lam kB T x tol : ℝ} (h : RateData rad ic 1)
    (htol0 : 0 < tol) (htol1 : tol < 1) (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    (hr0 : 0 < rad 0) (hr1 : 0 < rad 1) (hic : ic 1 = marcusIC A lam kB T x)
    (hfar : 4 * lam * (kB * T) * Real.log (kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol) < (lam - x) ^ 2) :
    ¬ KashaWithin rad ic tol 1 := by
  sorry

/-- Plan §7.2 #14 — the same criterion as a window around the reorganization energy. -/
theorem kashaWindow_halfWidth {rad ic : ℕ → ℝ} {A lam kB T x tol : ℝ} (h : RateData rad ic 1)
    (htol0 : 0 < tol) (htol1 : tol < 1) (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    (hr0 : 0 < rad 0) (hr1 : 0 < rad 1) (hic : ic 1 = marcusIC A lam kB T x)
    (h0 : 0 ≤ 4 * lam * (kB * T) * Real.log (kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol)) :
    KashaWithin rad ic tol 1 ↔
      |lam - x| ≤ Real.sqrt (4 * lam * (kB * T) * Real.log (kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol)) := by
  sorry

/-- Plan §7.2 #15. -/
theorem kashaGapThreshold_pos {A rad0 dec0 rad1 tol : ℝ} (hA : 0 < A) (hr0 : 0 < rad0)
    (hdec : 0 < dec0) (hr1 : 0 < rad1) (htol0 : 0 < tol) (htol1 : tol < 1) :
    0 < kashaGapThreshold A rad0 dec0 rad1 tol := by
  sorry

/-- Plan §7.2 #16. -/
theorem marcusIC_pos {A lam kB T x : ℝ} (hA : 0 < A) : 0 < marcusIC A lam kB T x := by
  sorry

/-! ## K5a — computable rational verdict layer (`PhotoLean/Kasha/RatModel.lean`; plan §8.1) -/

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
  sorry

/-- Plan §8.1 cast bridge. -/
theorem radBranchQ_cast (rad ic : ℕ → ℚ) (n : ℕ) :
    ((radBranchQ rad ic n : ℚ) : ℝ)
      = radBranch (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) n := by
  sorry

/-- Plan §8.1 cast bridge. -/
theorem icBranchQ_cast (rad ic : ℕ → ℚ) (n : ℕ) :
    ((icBranchQ rad ic n : ℚ) : ℝ)
      = icBranch (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) n := by
  sorry

/-- Plan §8.1 cast bridge. -/
theorem cascadeQ_cast (rad ic : ℕ → ℚ) (i N : ℕ) :
    ((cascadeQ rad ic i N : ℚ) : ℝ)
      = cascade (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) i N := by
  sorry

/-- Plan §8.1 cast bridge. -/
theorem emitYieldQ_cast (rad ic : ℕ → ℚ) (i N : ℕ) :
    ((emitYieldQ rad ic i N : ℚ) : ℝ)
      = emitYield (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) i N := by
  sorry

/-- Plan §8.1 cast bridge. -/
theorem fluoYieldQ_cast (rad ic : ℕ → ℚ) (N : ℕ) :
    ((fluoYieldQ rad ic N : ℚ) : ℝ)
      = fluoYield (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) N := by
  sorry

/-- Plan §8.1 cast bridge. -/
theorem upperYieldQ_cast (rad ic : ℕ → ℚ) (N : ℕ) :
    ((upperYieldQ rad ic N : ℚ) : ℝ)
      = upperYield (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) N := by
  sorry

/-- Plan §8.1 cast bridge: the rational criterion transfers to the real one. -/
theorem kashaWithinQ_iff_cast {rad ic : ℕ → ℚ} {tol : ℚ} {N : ℕ} :
    KashaWithinQ rad ic tol N ↔
      KashaWithin (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) (tol : ℝ) N := by
  sorry

/-- Plan §8.1 — the rational threshold. **Corrected 2026-09-20** (prover_c's kernel counterexample
`probe_criterion_premises_insufficient`, found independently of prover_b's ℝ-side witness): without
`0 < decayQ rad ic 1` the row is FALSE at `rad = twoRad 1 1`, `ic = twoIc 0 (-1)`, `tol = 1/2`. -/
theorem kashaWithinQ_iff_funnelRatioQ {rad ic : ℕ → ℚ} {tol : ℚ} (h0 : 0 < decayQ rad ic 0)
    (h1 : 0 < decayQ rad ic 1) (htol : 0 < tol) (hr : 0 < rad 1) :
    KashaWithinQ rad ic tol 1 ↔ (1 - tol) / tol ≤ funnelRatioQ rad ic := by
  sorry

/-- Plan §8.1 classifier row. -/
theorem kashaQVerdict_eq_pure_iff {rad ic : ℕ → ℚ} {tol : ℚ} {N : ℕ}
    (h : QRateData rad ic N) :
    kashaQVerdict rad ic tol N = KashaQVerdict.pure ↔ upperYieldQ rad ic N = 0 := by
  sorry

/-- Plan §8.1 classifier row. -/
theorem kashaQVerdict_eq_withinTol_iff {rad ic : ℕ → ℚ} {tol : ℚ} {N : ℕ}
    (h : QRateData rad ic N) :
    kashaQVerdict rad ic tol N = KashaQVerdict.withinTol ↔
      upperYieldQ rad ic N ≠ 0 ∧ KashaWithinQ rad ic tol N := by
  sorry

/-- Plan §8.1 classifier row. **Corrected 2026-09-20** together with its ℝ-side twin
`kashaZone_eq_violating_iff`: without `0 < tol` the row is FALSE at `rad ≡ 1`, `ic ≡ 1`, `N = 0`,
`tol = -1` (the vanishing-leak branch parks the verdict in `pure` while `¬ KashaWithinQ` holds). -/
theorem kashaQVerdict_eq_violating_iff {rad ic : ℕ → ℚ} {tol : ℚ} {N : ℕ}
    (h : QRateData rad ic N) (htol : 0 < tol) :
    kashaQVerdict rad ic tol N = KashaQVerdict.violating ↔ ¬ KashaWithinQ rad ic tol N := by
  sorry

/-! ## K5b — instance rows (`PhotoLean/Kasha/Instances.lean`; plan §8.2) -/

/-- Plan §8.2 row I1 — conforming control: `ic 1 / rad 1 = 100 ≥ 99` at `tol = 1/100`. -/
theorem I1_conforming_control :
    KashaWithinQ (twoRad 1 1) (twoIc 0 100) (1 / 100) 1 := by
  sorry

/-- Plan §8.2 row I2 — anti-Kasha control at the same tolerance: `ic 1 / rad 1 = 10 < 99`. -/
theorem I2_antiKasha_control : ¬ KashaWithinQ (twoRad 1 1) (twoIc 0 10) (1 / 100) 1 := by
  sorry

/-- Plan §8.2 row I3 — the threshold is attained with equality (`ic 1 / rad 1 = 99`). -/
theorem I3_threshold_boundary : KashaWithinQ (twoRad 1 1) (twoIc 0 99) (1 / 100) 1 := by
  sorry

/-- Plan §8.2 row I3b — one unit below the threshold fails. -/
theorem I3b_threshold_below : ¬ KashaWithinQ (twoRad 1 1) (twoIc 0 (9899 / 100)) (1 / 100) 1 := by
  sorry

/-- Plan §8.2 row I4 — the Markov recursion at concrete rationals (`N = 1`). -/
theorem I4_fluoYield_one : fluoYieldQ (twoRad 1 1) (twoIc 0 100) 1 = 1 := by
  sorry

/-- Plan §8.2 row I5 — the leak at concrete rationals (`N = 1`). -/
theorem I5_upperYield_one : upperYieldQ (twoRad 1 1) (twoIc 0 100) 1 = 1 / 101 := by
  sorry

/-- Plan §8.2 row I6 — the three-level recursion at concrete rationals (`N = 2`). -/
theorem I6_fluoYield_two : fluoYieldQ (threeRad 1 1 1) (threeIc 1 1 1) 2 = 7 / 8 := by
  sorry

/-- Plan §8.2 row I7 — **the equal-rates counterexample**: every level above the lowest satisfies
`ic ≥ rad` and yet `upperYield / fluoYield = 6/7 > 1/2`. -/
theorem I7_equalRates_leak_two : upperYieldQ (threeRad 1 1 1) (threeIc 1 1 1) 2 = 3 / 4 := by
  sorry

/-- Plan §8.2 row I7b — the same ladder violates the tolerance form at `tol = 1/2`. -/
theorem I7b_equalRates_violating : ¬ KashaWithinQ (threeRad 1 1 1) (threeIc 1 1 1) (1 / 2) 2 := by
  sorry

/-- Plan §8.2 row I8 — the no-loss ladder: Vavilov holds at every step and the rule fails. -/
theorem I8_noLoss_vavilov : VavilovAt (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) 1 := by
  sorry

/-- Plan §8.2 row I8b — the same no-loss ladder fails the exact rule. -/
theorem I8b_noLoss_not_kasha : ¬ KashaRule (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) 1 := by
  sorry

/-- Plan §8.2 row I9 — verdict classifier witness: a violating row is classified `violating`. -/
theorem I9_verdict_violating :
    kashaQVerdict (twoRad 1 1) (twoIc 0 10) (1 / 100) 1 = KashaQVerdict.violating := by
  sorry

/-- Plan §8.2 row I13 — row inventory: the two model-constructed verdicts of I1/I2 in one
statement, at the same tolerance. -/
theorem I13_row_inventory :
    KashaWithinQ (twoRad 1 1) (twoIc 0 100) (1 / 100) 1 ∧
      ¬ KashaWithinQ (twoRad 1 1) (twoIc 0 10) (1 / 100) 1 := by
  sorry

/-- Plan §8.2 row I14 — non-vacuity: both verdict kinds occur in the model-constructed rows. -/
theorem I14_not_one_sided :
    (∃ rad ic : ℕ → ℚ, KashaWithinQ rad ic (1 / 100) 1) ∧
      (∃ rad ic : ℕ → ℚ, ¬ KashaWithinQ rad ic (1 / 100) 1) := by
  sorry

/-! ### K5b literature rows (appended 2026-09-20, plan §8.2; numbers from
`theories/kasha/LITERATURE.md` §R1.6) -/

/-- Plan §8.2 row I10 — **literature row, conforming**: 4,6,8-trimethylazulene in cyclohexane.
Transcribed in units of `10⁶ s⁻¹` from `theories/kasha/LITERATURE.md` §R1.6 (source: the 1995
Saskatchewan thesis, Table 3.3 p. 126, printing `Σk_r = 3.3×10⁷ s⁻¹` and `Σk_nr = 6.7×10¹⁰ s⁻¹`;
the identification `rad 1 ≡ Σk_r(S₂)`, `ic 1 ≡ Σk_nr(S₂)` is the declared bridge of §R1.4.2, not a
theorem of this development). `rad 0 = 1`, `ic 0 = 0` is a **declared modelling reduction** — the
lowest level's nonradiative channel is neglected in this row — and it is what makes K3 #3's reduced
criterion apply exactly. Ratio `ic 1 / rad 1 = 67000/33 ≈ 2030 ≥ 99 = (1 - 1/100)/(1/100)`. -/
theorem I10_trimethylazulene_conforming :
    KashaWithinQ (twoRad 1 33) (twoIc 0 67000) (1 / 100) 1 := by
  sorry

/-- Plan §8.2 row I11 — **literature row, anti-Kasha**: parent azulene in cyclohexane. Same
transcription rule and same `rad 0 = 1, ic 0 = 0` reduction as I10 (source: the 1995 thesis Table 3.1
p. 115, printing `Σk_r = 3.5×10⁷`, `Σk_nr = 7.2×10⁸ s⁻¹`). Ratio `720/35 ≈ 20.6 < 99`. -/
theorem I11_azulene_violating :
    ¬ KashaWithinQ (twoRad 1 35) (twoIc 0 720) (1 / 100) 1 := by
  sorry

/-- Plan §8.2 row I11-alt — **literature row, anti-Kasha, independent route**: azulene as printed in
*Chem. Sci.* 2026 (Table 2/3, `Φ_Fl = 2.42 %`, `τ_IC = 1.35 ns`; `LITERATURE.md` §R1.4/§R1.6). Here
the numbers come from the **printed quantum yield** rather than from two rate columns: with
`ic 0 = 0`, `(1 - Φ)/Φ` *is* the ratio `ic 1 / rad 1`, so `rad 1 = 242`, `ic 1 = 9758` in units of
`10⁶ s⁻¹`. Ratio `≈ 40.3 < 99`. The docstring records the spread against I11 (20.6), which is solvent
and method spread, not a disagreement in sign. -/
theorem I11alt_azulene2026_violating :
    ¬ KashaWithinQ (twoRad 1 242) (twoIc 0 9758) (1 / 100) 1 := by
  sorry

/-- Plan §8.2 row I11-alt2 — **literature row, anti-Kasha, peer-reviewed rates**: azulene from
Veys & Escudero, *J. Phys. Chem. A* **124**, 7228 (2020), Table 2 (both rates printed as
experimental: `k_r(S₂) = 2.3 × 10⁷ s⁻¹`, `k_IC(S₂ → S₁) = 5.3 × 10⁸ s⁻¹`; `LITERATURE.md` §R1.6).
Ratio `530/23 ≈ 23.0 < 99`; the printed `Φ = (3.5 ± 0.4) %` independently gives `≈ 27.6`. -/
theorem I11alt2_azulene2020_violating :
    ¬ KashaWithinQ (twoRad 1 23) (twoIc 0 530) (1 / 100) 1 := by
  sorry

/-- Plan §8.2 row I11t — **the verdict is tolerance-relative** (the honest form of "azulene violates
Kasha's rule"): the *same* measured azulene data (I11) violates the 1 % purity criterion and conforms
to a 10 % one. `LITERATURE.md` §R1.3 records that the literature's `k_IC ≫ k_rad` is a qualitative
statement with no printed threshold, and §R1.6 records that `tol = 1/100` is a **model choice**: this
row is what makes that choice visible in the kernel instead of hiding it in prose. -/
theorem I11t_azulene_tolerance_dependence :
    ¬ KashaWithinQ (twoRad 1 35) (twoIc 0 720) (1 / 100) 1 ∧
      KashaWithinQ (twoRad 1 35) (twoIc 0 720) (1 / 10) 1 := by
  sorry

/-- Plan §8.2 row I15 — **family contrast at one tolerance**: within the azulene family the measured
S₂ rates separate the methylated derivative (conforming, I10) from the parent (violating, I11) at the
*same* `tol = 1/100`. Two kernel computations, one tolerance, opposite verdicts — this is the
instance-level content that the model adds over the qualitative rule. -/
theorem I15_familyContrast :
    KashaWithinQ (twoRad 1 33) (twoIc 0 67000) (1 / 100) 1 ∧
      ¬ KashaWithinQ (twoRad 1 35) (twoIc 0 720) (1 / 100) 1 := by
  sorry

end Kasha

end PhotoLean
