/-
PhotoLean.Kasha.Basic — K1, the description layer of Kasha's rule.

Kasha's rule ("luminescence is emitted only from the lowest excited state of a given
multiplicity, whatever the excitation") is formalized here in the finite excited-state cascade
model of `theories/kasha/plan.md` §1.2: a ladder of excited levels `0, 1, …, N`, truncated at the
excitation level `N`; level `0` is the lowest excited state of the multiplicity under
consideration (`S₁` for fluorescence), level `n ≥ 1` is the n-th state above it. Each level
carries a radiative rate `rad n` and a nonradiative rate `ic n` (internal conversion `n → n-1`
for `n ≥ 1`, loss to the ground state for `n = 0`). Under the standing premise bundle `RateData`
(positive total decay up to the excitation level, nonnegative rates — an explicit hypothesis of
every physical theorem here, never hidden in a definition) the branching probabilities are
`radBranch = rad / decay` and `icBranch = ic / decay`, the probability of arriving at level `i`
from level `N` without emitting is the product `cascade i N`, and the observables are the
level-resolved yield `emitYield i N`, the total fluorescence yield `fluoYield N`, the leak
`upperYield N` (emission from levels above the lowest one), the normalized spectrum `specFrac`,
the funnel margin `kashaMargin` and the two funnel ratios (`funnelRatio`, `ladderRatio`). On top
of those sit the predicates `KashaRule` (exact rule), `KashaWithin` (its tolerance form),
`VavilovAt` / `VavilovUpTo` (excitation-independence of the total yield) and `KashaDescriptor`
(non-vacuity), plus the decidable regime classifier `kashaZone` with its three branch
characterizations.

This module is the description layer only. The laws of the cascade — the Markov recursion, the
conservation identity, the exact criterion `KashaRule ↔ rad = 0` above the lowest level, the
Kasha–Vavilov equivalence, the sharp funnel-ratio threshold, the effective two-level reduction
and the Marcus bridge — are milestones K2–K4 in `PhotoLean/Kasha/{Criterion,Sharp,Compose}.lean`.

What is NOT derived here (plan §1.2, §12, §13): the ladder model itself, the identification of
the branching probabilities with the outcome of competing exponential clocks, the reading of the
time-integrated yields as the observables of Kasha/Vavilov spectroscopy, and the interpretation
of `ic 0` as the lowest state's loss channel. They are modelling assumptions, registered as such
in the plan's honesty table and scope limits; no theorem below depends on one of them silently.

Statement authority: every definition body and every theorem signature below is taken word for
word from `theories/kasha/probes/kasha-statement-skeleton.lean` (its §K1 block; sha256
`e3ddc2d01317ec6bc46957cae7763034a23df691bffc480a08c9a23d9fe6412b`), which in turn transcribes
`theories/kasha/plan.md` §4.1 and §4.2. The design rule of the engine applies throughout: a
physical approximation is an explicit hypothesis (that is what `RateData` is for), never a
definition. Note deliberately: the two keyword literals that `proofs/scripts/check.sh --strict`
scans for are not spelled out anywhere in this file — that scan covers `PhotoLean/**/*.lean`
including block comments, so writing them (even in prose) would be a false-positive FAIL.

Plan locus: `theories/kasha/plan.md` §4 (K1); board `theories/kasha/TASKS.md` §K1. This module
imports `Mathlib` only — no `PhotoLean.Marcus`, no other `PhotoLean` module: the description
layer is self-contained. Docstrings §4.2 #n refer to the plan's theorem table.

Acceptance commands (run on a clean tree):

    proofs/scripts/lake build PhotoLean.Kasha.Basic
    proofs/scripts/check.sh --strict PhotoLean.Kasha.Basic
    proofs/scripts/axioms.sh PhotoLean.Kasha.Basic PhotoLean.Kasha.<fully.qualified.theorem>

The delivered file contains no unfinished-proof placeholder and no custom axiomatic
declaration; the `#print axioms` gate of every theorem below lists at most `propext`,
`Classical.choice`, `Quot.sound`.
-/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Kasha
/-! ## Definitions (plan §4.1) -/

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
/-! ## Theorems (plan §4.2) -/

/-- Plan §4.2 #1. The total decay rate is the sum of the two channels (definitional). -/
theorem decay_eq_rad_add_ic (rad ic : ℕ → ℝ) (n : ℕ) : decay rad ic n = rad n + ic n := rfl
/-- Plan §4.2 #2. The two branch probabilities of a level with nonzero total decay sum to `1`. -/
theorem radBranch_add_icBranch {rad ic : ℕ → ℝ} {n : ℕ} (h : decay rad ic n ≠ 0) :
    radBranch rad ic n + icBranch rad ic n = 1 := by
  unfold radBranch icBranch
  rw [← add_div]
  exact div_self h
/-- Plan §4.2 #3. The radiative branch is nonnegative under `RateData`. -/
theorem radBranch_nonneg {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    0 ≤ radBranch rad ic n := by
  unfold radBranch
  exact div_nonneg (h.rad_nonneg n) (le_of_lt (h.decay_pos n hn))
/-- Plan §4.2 #4. The nonradiative branch is nonnegative under `RateData`. -/
theorem icBranch_nonneg {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    0 ≤ icBranch rad ic n := by
  unfold icBranch
  exact div_nonneg (h.ic_nonneg n) (le_of_lt (h.decay_pos n hn))
/-- Plan §4.2 #5. The radiative branch is at most `1`: it is a probability. -/
theorem radBranch_le_one {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    radBranch rad ic n ≤ 1 := by
  have hsum : radBranch rad ic n + icBranch rad ic n = 1 :=
    radBranch_add_icBranch (ne_of_gt (h.decay_pos n hn))
  have hic : 0 ≤ icBranch rad ic n := icBranch_nonneg h hn
  linarith
/-- Plan §4.2 #6. The nonradiative branch is at most `1`: it is a probability. -/
theorem icBranch_le_one {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    icBranch rad ic n ≤ 1 := by
  have hsum : radBranch rad ic n + icBranch rad ic n = 1 :=
    radBranch_add_icBranch (ne_of_gt (h.decay_pos n hn))
  have hrad : 0 ≤ radBranch rad ic n := radBranch_nonneg h hn
  linarith
/-- Plan §4.2 #7. The cascade probability from a level to itself is `1` (the empty product). -/
theorem cascade_self (rad ic : ℕ → ℝ) (i : ℕ) : cascade rad ic i i = 1 := by
  unfold cascade
  rw [Finset.Icc_eq_empty (by omega)]
  simp
set_option linter.unusedVariables false in
/-- Plan §4.2 #8. The cascade probability is nonnegative under `RateData` (the premise `i ≤ N` is
part of the signature; the product's own membership hypothesis supplies `j ≤ N`). -/
theorem cascade_nonneg {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N) (h1 : i ≤ N) :
    0 ≤ cascade rad ic i N := by
  unfold cascade
  exact Finset.prod_nonneg fun j hj => icBranch_nonneg h (Finset.mem_Icc.mp hj).2
set_option linter.unusedVariables false in
/-- Plan §4.2 #9. The cascade probability is at most `1`: it is a probability (the premise `i ≤ N`
is part of the signature; the product's own membership hypothesis supplies `j ≤ N`). -/
theorem cascade_le_one {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N) (h1 : i ≤ N) :
    cascade rad ic i N ≤ 1 := by
  unfold cascade
  exact Finset.prod_le_one (fun j hj => icBranch_nonneg h (Finset.mem_Icc.mp hj).2)
    (fun j hj => icBranch_le_one h (Finset.mem_Icc.mp hj).2)
/-- Plan §4.2 #10. The excitation-at-`i` yield of level `i` is its radiative branch (nothing has
been lost on the way). -/
theorem emitYield_self (rad ic : ℕ → ℝ) (i : ℕ) : emitYield rad ic i i = radBranch rad ic i := by
  unfold emitYield
  rw [cascade_self, mul_one]
/-- Plan §4.2 #11. The level-resolved yield is nonnegative under `RateData`. -/
theorem emitYield_nonneg {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N) (h1 : i ≤ N) :
    0 ≤ emitYield rad ic i N := by
  unfold emitYield
  exact mul_nonneg (radBranch_nonneg h h1) (cascade_nonneg h h1)
/-- Plan §4.2 #12. The level-resolved yield is at most the level's radiative branch (the cascade
factor is at most `1`). -/
theorem emitYield_le_radBranch {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N) (h1 : i ≤ N) :
    emitYield rad ic i N ≤ radBranch rad ic i := by
  unfold emitYield
  exact mul_le_of_le_one_right (radBranch_nonneg h h1) (cascade_le_one h h1)
set_option linter.unusedVariables false in
/-- Plan §4.2 #13. The total yield splits into the lowest state's emission and the leak (the plan's
`range (N+1) = {0} ∪ Icc 1 N` index identity; the `RateData` premise is part of the description
layer's signature and is not consumed by this index identity). -/
theorem fluoYield_eq_low_add_upper {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    fluoYield rad ic N = emitYield rad ic 0 N + upperYield rad ic N := by
  have hrange : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  unfold fluoYield upperYield
  rw [hrange, Finset.sum_insert (by simp)]
/-- Plan §4.2 #14. At excitation level `0` the total yield is the lowest state's branch. -/
theorem fluoYield_zero (rad ic : ℕ → ℝ) : fluoYield rad ic 0 = radBranch rad ic 0 := by
  unfold fluoYield
  rw [Finset.sum_range_one, emitYield_self]
/-- Plan §4.2 #15. There is no leak at excitation level `0`. -/
theorem upperYield_zero (rad ic : ℕ → ℝ) : upperYield rad ic 0 = 0 := by
  unfold upperYield
  simp
/-- Plan §4.2 #16. The total yield is nonnegative under `RateData`. -/
theorem fluoYield_nonneg {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    0 ≤ fluoYield rad ic N := by
  unfold fluoYield
  exact Finset.sum_nonneg fun i hi =>
    emitYield_nonneg h (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
/-- Plan §4.2 #17. The leak is nonnegative under `RateData`. -/
theorem upperYield_nonneg {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    0 ≤ upperYield rad ic N := by
  unfold upperYield
  exact Finset.sum_nonneg fun i hi => emitYield_nonneg h (Finset.mem_Icc.mp hi).2
/-- Plan §4.2 #18. The leak is at most the total yield (the lowest state's emission is
nonnegative). -/
theorem upperYield_le_fluoYield {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    upperYield rad ic N ≤ fluoYield rad ic N := by
  have hsplit := fluoYield_eq_low_add_upper h
  have hlow : 0 ≤ emitYield rad ic 0 N := emitYield_nonneg h (Nat.zero_le N)
  linarith
/-- Plan §4.2 #19. The exact rule is, by definition, the vanishing of the leak. -/
theorem kashaRule_iff_upperYield_zero (rad ic : ℕ → ℝ) (N : ℕ) :
    KashaRule rad ic N ↔ upperYield rad ic N = 0 := Iff.rfl
set_option linter.unusedVariables false in
/-- Plan §4.2 #20. The normalized spectrum sums to `1` whenever the total yield does not vanish
(the `RateData` premise is decorative here: the identity only needs the nonzero denominator). -/
theorem specFrac_sum {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N)
    (hF : fluoYield rad ic N ≠ 0) :
    ∑ i ∈ Finset.range (N + 1), specFrac rad ic i N = 1 := by
  unfold specFrac
  rw [← Finset.sum_div, ← fluoYield, div_self hF]
/-- Plan §4.2 #21. The tolerance form is the statement that the lowest state carries all but `tol`
of the spectrum; dividing by the (positive, under `RateData`) total yield turns it into the
normalized form. -/
theorem kashaWithin_iff_specFrac {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ} (h : RateData rad ic N)
    (hF : fluoYield rad ic N ≠ 0) :
    KashaWithin rad ic tol N ↔ 1 - specFrac rad ic 0 N ≤ tol := by
  have hFpos : 0 < fluoYield rad ic N := lt_of_le_of_ne (fluoYield_nonneg h) (Ne.symm hF)
  have hkey : 1 - specFrac rad ic 0 N = upperYield rad ic N / fluoYield rad ic N := by
    have hu : upperYield rad ic N = fluoYield rad ic N - emitYield rad ic 0 N := by
      linarith [fluoYield_eq_low_add_upper h]
    rw [hu]
    unfold specFrac
    rw [← div_self hF, ← sub_div]
  rw [hkey]
  exact (div_le_iff₀ hFpos).symm
set_option linter.unusedVariables false in
/-- Plan §4.2 #22. Classifier characterization, `pure` branch: the first guard of the cascade is
exactly the exact rule (the `RateData` premise is decorative here — the characterization needs no
positivity). -/
theorem kashaZone_eq_pure_iff {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ} (h : RateData rad ic N) :
    kashaZone rad ic tol N = KashaZone.pure ↔ KashaRule rad ic N := by
  constructor
  · intro hz
    unfold kashaZone at hz
    split_ifs at hz with h1 h2
    exact h1
  · intro hr
    unfold kashaZone
    exact if_pos hr
set_option linter.unusedVariables false in
/-- Plan §4.2 #23. Classifier characterization, `withinTol` branch: the leak is nonzero and inside
the tolerance (the `RateData` premise is decorative here — the characterization needs no
positivity). -/
theorem kashaZone_eq_withinTol_iff {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ} (h : RateData rad ic N) :
    kashaZone rad ic tol N = KashaZone.withinTol ↔
      ¬ KashaRule rad ic N ∧ KashaWithin rad ic tol N := by
  unfold kashaZone
  split_ifs with h1 h2 <;>
    first
      | exact iff_of_true rfl ⟨h1, h2⟩
      | exact iff_of_false (by intro hh; cases hh) (by rintro ⟨hK, -⟩; exact hK h1)
      | exact iff_of_false (by intro hh; cases hh) (by rintro ⟨-, hw⟩; exact h2 hw)
end Kasha

end PhotoLean
