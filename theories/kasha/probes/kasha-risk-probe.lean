/-
theories/kasha/probes/kasha-risk-probe.lean

Sprint-0 risk probe for the Kasha theory (`theories/kasha/plan.md`, task K-PROBE-1). The riskiest
statement forms of Sprint 0 - plan rows K1 #13, K1 #23, K2 #4, K2 #5, K2 #6, K2 #14, K3 #1, K3 #2,
K3 #3, K3 #13, K4 #8 and K4 #12 - are proved here, verbatim from the statement authority
`theories/kasha/probes/kasha-statement-skeleton.lean` (same binders, same hypotheses, same
conclusion), *before* milestones K1-K4 are dispatched, so that dispatch rests on kernel evidence
instead of hope.

**Kernel finding of this probe (for the lead, not silently repaired here).** Risk row 7
(`theorem kashaWithin_one_iff_ratio`, plan §6.1 #2, skeleton lines 384-387) is **false as stated**:
its hypotheses `0 < decay rad ic 0`, `0 < tol`, `0 < rad 1` do not bound the sign of
`decay rad ic 1 = rad 1 + ic 1`, and the cross-multiplication of the rate form by that (possibly
negative) total decay rate flips the inequality. Kernel evidence is
`risk_kashaWithin_one_iff_ratio_refuted` (explicit witness `rad = 1,1,0,...`,
`ic = 1,-3,0,...`, `tol = 1/2`) and `risk_kashaWithin_one_iff_ratio_false` (the negation of the
universally quantified row). The minimal correction is to add the premise
`(h1 : 0 < decay rad ic 1)` - the premise the skeleton's row K3 #1 already has; the corrected form
is kernel-checked here as `risk_kashaWithin_one_iff_ratio_with_decay_pos` and is *not* the row.
Every other row below is proved as stated.

This is a probe, not a deliverable:
* it lives outside the contract's scan/build range (`SOURCE_DIRS="PhotoLean"`,
  `PROBES_kasha="theories/kasha/probes"`), so it is not part of the library build;
* it re-defines the K1 model locally (namespace `PhotoLean.Kasha.RiskProbe`), so it does not depend
  on `PhotoLean/Kasha/Basic.lean`, which does not exist yet;
* it contains no unproved placeholder and no custom axiomatic declaration - the whole point is
  kernel evidence; the `#print axioms` block at the end makes the kernel print the axiom footprint
  of every theorem above;
* where a standing `RateData` hypothesis of the statement authority is not consumed by the proof, it
  is kept verbatim for statement fidelity and the local `set_option linter.unusedVariables false in`
  (the `theories/BEP/probes/bep-risk-probe.lean` precedent) documents that instead of dropping it.

Model (plan §1.2). Level index `n : ℕ`; level `0` is the lowest excited state of the multiplicity
under consideration, level `n ≥ 1` the n-th state above it. Each level has a radiative rate `rad n`
and a nonradiative rate `ic n`; `decay n = rad n + ic n`, the branches are `rad n / decay n` and
`ic n / decay n`, `cascade i N` is the probability of reaching `i` from `N` without emitting,
`emitYield i N` is the emission yield of level `i`, `fluoYield N` the total and `upperYield N` the
emission from above the lowest state. `KashaRule` is `upperYield = 0`, `KashaWithin tol N` is
`upperYield ≤ tol * fluoYield`, and `RateData` is the standing physical premise bundle (positive
total decay rates up to the excitation level, nonnegative rates).

API calibration for the risky names used here (`Real.log_le_iff_le_exp`, `Real.exp_log`,
`Finset.sum_Icc_succ_top`, `Finset.prod_Icc_succ_top`, `Finset.sum_eq_zero_iff_of_nonneg`, ...):
`theories/kasha/probes/kasha-api-risk.lean`, whose kernel-checked `example`s are the recipes reused
below. The local helpers of §2 replay the K1/K2 rows the risk rows consume, with kernel evidence,
so that a false K1/K2 statement is caught here too.

Running:  proofs/scripts/lake env lean theories/kasha/probes/kasha-risk-probe.lean
-/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace PhotoLean
namespace Kasha
namespace RiskProbe

/-! ## 1. Model definitions (local copies mirroring the statement authority, plan §4.1/§7.1) -/

/-- Total decay rate of level `n`: the sum of its radiative and its nonradiative channel. -/
noncomputable def decay (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := rad n + ic n

/-- Probability that level `n` decays radiatively (emits a photon). -/
noncomputable def radBranch (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := rad n / decay rad ic n

/-- Probability that level `n` decays nonradiatively: internal conversion `n → n-1` for `n ≥ 1`,
loss to the ground state for `n = 0`. -/
noncomputable def icBranch (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := ic n / decay rad ic n

/-- Probability that, starting at level `N`, the molecule reaches level `i` without having emitted. -/
noncomputable def cascade (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (i + 1) N, icBranch rad ic j

/-- Time-integrated emission yield of level `i` under excitation at level `N`. -/
noncomputable def emitYield (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ :=
  radBranch rad ic i * cascade rad ic i N

/-- Total fluorescence quantum yield under excitation at level `N`. -/
noncomputable def fluoYield (rad ic : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), emitYield rad ic i N

/-- Emission from levels **above** the lowest one - the leak past the funnel of Kasha's rule. -/
noncomputable def upperYield (rad ic : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 N, emitYield rad ic i N

/-- The two-level funnel ratio: the `k_IC / k_rad`-shaped quantity whose threshold is the sharp
criterion (plan §1.3, §6.1 #2). -/
noncomputable def funnelRatio (rad ic : ℕ → ℝ) : ℝ := rad 0 * ic 1 / (rad 1 * decay rad ic 0)

/-- The exact Kasha rule: no emission from above the lowest excited state. -/
def KashaRule (rad ic : ℕ → ℝ) (N : ℕ) : Prop := upperYield rad ic N = 0

/-- The tolerance form of the rule: the fraction of emitted photons that does not come from the
lowest state is at most `tol`. -/
def KashaWithin (rad ic : ℕ → ℝ) (tol : ℝ) (N : ℕ) : Prop :=
  upperYield rad ic N ≤ tol * fluoYield rad ic N

/-- The standing physical premise bundle: positive total decay rates up to the excitation level,
nonnegative radiative and nonradiative rates. -/
structure RateData (rad ic : ℕ → ℝ) (N : ℕ) : Prop where
  decay_pos : ∀ n, n ≤ N → 0 < decay rad ic n
  rad_nonneg : ∀ n, 0 ≤ rad n
  ic_nonneg : ∀ n, 0 ≤ ic n

/-- Decidable regime classifier of a ladder at tolerance `tol` and excitation level `N`. -/
inductive KashaZone where
  | pure
  | withinTol
  | violating

/-- The classifier: `pure` for the exact rule, `withinTol` inside the tolerance, `violating`
outside it. -/
noncomputable def kashaZone (rad ic : ℕ → ℝ) (tol : ℝ) (N : ℕ) : KashaZone :=
  if upperYield rad ic N = 0 then KashaZone.pure
  else if upperYield rad ic N ≤ tol * fluoYield rad ic N then KashaZone.withinTol
  else KashaZone.violating

/-- Effective two-level radiative data of the ladder at excitation level `N` (plan §7.1). -/
noncomputable def effRad (rad ic : ℕ → ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n => if n = 0 then rad 0 else if n = 1 then upperYield rad ic N else 0

/-- Effective two-level nonradiative data of the ladder at excitation level `N` (plan §7.1). -/
noncomputable def effIc (rad ic : ℕ → ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n => if n = 0 then ic 0 else if n = 1 then cascade rad ic 0 N else 0

/-- The Marcus activation barrier, locally identical to
`PhotoLean.Marcus.barrier lam x = (lam - x) ^ 2 / (4 * lam)` (`PhotoLean/Marcus/Basic.lean:50`);
the risk probe stays self-contained and does not import the Marcus library. -/
noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- The internal-conversion rate in the Marcus form: pre-exponential `A`, reorganization energy
`lam`, thermal energy `kB * T`, driving force equal to the energy gap `x` (plan §7.1). -/
noncomputable def marcusIC (A lam kB T x : ℝ) : ℝ :=
  A * Real.exp (-(barrier lam x) / (kB * T))

/-- The gap threshold of the Marcus bridge: the multiplicative constant `K` whose logarithm is the
half-width of the Kasha window (plan §7.1). This is the `K` of task K-PROBE-1 row 10. -/
noncomputable def kashaGapThreshold (A rad0 dec0 rad1 tol : ℝ) : ℝ :=
  A * rad0 * tol / (rad1 * dec0 * (1 - tol))

/-! ## 2. Local K1/K2 helpers replayed with kernel evidence

These are the K1/K2 rows the risk rows consume. Those that need no physical premise are stated
without one, so that the risk rows of §3 can use them through the verbatim `RateData` form. -/

/-- `cascade rad ic i i = 1` (empty product). -/
theorem cascade_self (rad ic : ℕ → ℝ) (i : ℕ) : cascade rad ic i i = 1 := by
  unfold cascade
  refine Finset.prod_eq_one (fun j hj => ?_)
  simp only [Finset.mem_Icc] at hj
  omega

/-- `upperYield rad ic 0 = 0`. -/
theorem upperYield_zero (rad ic : ℕ → ℝ) : upperYield rad ic 0 = 0 := by
  unfold upperYield
  rw [Finset.Icc_eq_empty_iff.mpr (by norm_num : ¬ (1 ≤ 0)), Finset.sum_empty]

/-- `emitYield rad ic i i = radBranch rad ic i`. -/
theorem emitYield_self (rad ic : ℕ → ℝ) (i : ℕ) :
    emitYield rad ic i i = radBranch rad ic i := by
  unfold emitYield
  rw [cascade_self, mul_one]

/-- The product step of the cascade probability. -/
theorem cascade_succ {rad ic : ℕ → ℝ} {i N : ℕ} (h : i ≤ N) :
    cascade rad ic i (N + 1) = icBranch rad ic (N + 1) * cascade rad ic i N := by
  unfold cascade
  rw [Finset.prod_Icc_succ_top (by omega : i + 1 ≤ N + 1), mul_comm]

/-- The per-level emission yield step. -/
theorem emitYield_succ {rad ic : ℕ → ℝ} {i N : ℕ} (h : i ≤ N) :
    emitYield rad ic i (N + 1) = icBranch rad ic (N + 1) * emitYield rad ic i N := by
  unfold emitYield
  rw [cascade_succ h]
  ring

/-- `emitYield rad ic (N+1) (N+1) = radBranch rad ic (N+1)`. -/
theorem emitYield_succ_self (rad ic : ℕ → ℝ) (N : ℕ) :
    emitYield rad ic (N + 1) (N + 1) = radBranch rad ic (N + 1) :=
  emitYield_self rad ic (N + 1)

/-- The sum split `range (N+1) = {0} ∪ Icc 1 N`: the total yield is emission from the lowest level
plus the leak. No physical premise is needed for the split itself (plan §4.2 #13). -/
theorem fluoYield_eq_low_add_upper_free (rad ic : ℕ → ℝ) (N : ℕ) :
    fluoYield rad ic N = emitYield rad ic 0 N + upperYield rad ic N := by
  unfold fluoYield upperYield
  have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp)]

/-- `fluoYield rad ic 0 = radBranch rad ic 0`. -/
theorem fluoYield_zero (rad ic : ℕ → ℝ) : fluoYield rad ic 0 = radBranch rad ic 0 := by
  rw [fluoYield_eq_low_add_upper_free, upperYield_zero, add_zero, emitYield_self]

/-- The Markov recursion of the leak (plan §5.1 #5), in the form that needs no physical premise:
`upperYield (N+1) = radBranch (N+1) + icBranch (N+1) * upperYield N`. -/
theorem upperYield_succ_free (rad ic : ℕ → ℝ) (N : ℕ) :
    upperYield rad ic (N + 1) =
      radBranch rad ic (N + 1) + icBranch rad ic (N + 1) * upperYield rad ic N := by
  unfold upperYield
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), Finset.mul_sum]
  have h1 : (∑ i ∈ Finset.Icc 1 N, emitYield rad ic i (N + 1))
      = ∑ i ∈ Finset.Icc 1 N, icBranch rad ic (N + 1) * emitYield rad ic i N := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    exact emitYield_succ (by omega : i ≤ N)
  rw [h1, emitYield_succ_self, add_comm]

/-- The Markov recursion of the total yield (plan §5.1 #4), in the form that needs no physical
premise: `fluoYield (N+1) = radBranch (N+1) + icBranch (N+1) * fluoYield N`. -/
theorem fluoYield_succ_free (rad ic : ℕ → ℝ) (N : ℕ) :
    fluoYield rad ic (N + 1) =
      radBranch rad ic (N + 1) + icBranch rad ic (N + 1) * fluoYield rad ic N := by
  rw [fluoYield_eq_low_add_upper_free rad ic N,
    fluoYield_eq_low_add_upper_free rad ic (N + 1), upperYield_succ_free,
    emitYield_succ (Nat.zero_le N)]
  ring

/-- `radBranch rad ic n + icBranch rad ic n = 1` for nonzero total decay rate. -/
theorem radBranch_add_icBranch {rad ic : ℕ → ℝ} {n : ℕ} (h : decay rad ic n ≠ 0) :
    radBranch rad ic n + icBranch rad ic n = 1 := by
  unfold radBranch icBranch decay at *
  field_simp
  try ring

/-- Plan §4.2 #3. -/
theorem radBranch_nonneg {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    0 ≤ radBranch rad ic n :=
  div_nonneg (h.rad_nonneg n) (le_of_lt (h.decay_pos n hn))

/-- Plan §4.2 #4. -/
theorem icBranch_nonneg {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    0 ≤ icBranch rad ic n :=
  div_nonneg (h.ic_nonneg n) (le_of_lt (h.decay_pos n hn))

set_option linter.unusedVariables false in
/-- Plan §4.2 #8. The binder `h1` is kept verbatim from the statement authority; the product bound
only needs `j ≤ N` for `j ∈ Icc (i+1) N`, so `h1` is not consumed. -/
theorem cascade_nonneg {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N) (h1 : i ≤ N) :
    0 ≤ cascade rad ic i N := by
  unfold cascade
  refine Finset.prod_nonneg (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  exact icBranch_nonneg h hj.2

/-- Plan §4.2 #11. -/
theorem emitYield_nonneg {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N) (h1 : i ≤ N) :
    0 ≤ emitYield rad ic i N := by
  unfold emitYield
  exact mul_nonneg (radBranch_nonneg h h1) (cascade_nonneg h h1)

/-- Plan §4.2 #17. -/
theorem upperYield_nonneg {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    0 ≤ upperYield rad ic N := by
  unfold upperYield
  refine Finset.sum_nonneg (fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  exact emitYield_nonneg h hi.2

/-- `cascade rad ic 0 1 = icBranch rad ic 1`. -/
theorem cascade_zero_one (rad ic : ℕ → ℝ) : cascade rad ic 0 1 = icBranch rad ic 1 := by
  unfold cascade
  have hset : Finset.Icc (0 + 1) 1 = ({1} : Finset ℕ) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_singleton]
    omega
  rw [hset, Finset.prod_singleton]

/-- `upperYield rad ic 1 = radBranch rad ic 1`. -/
theorem upperYield_one (rad ic : ℕ → ℝ) : upperYield rad ic 1 = radBranch rad ic 1 := by
  unfold upperYield
  rw [Finset.Icc_self, Finset.sum_singleton]
  exact emitYield_self rad ic 1

/-- The two-level total yield: `fluoYield rad ic 1 = radBranch 0 * icBranch 1 + radBranch 1`. -/
theorem fluoYield_one (rad ic : ℕ → ℝ) :
    fluoYield rad ic 1 = radBranch rad ic 0 * icBranch rad ic 1 + radBranch rad ic 1 := by
  rw [fluoYield_eq_low_add_upper_free rad ic 1, upperYield_one]
  congr 1
  unfold emitYield
  rw [cascade_zero_one]

/-- The rate form of the two-level threshold, as pure algebra (risk row 6 engine): the two sides
are related by multiplying with the two positive total decay rates. -/
private theorem two_level_algebra {r0 c0 r1 c1 tol : ℝ} (hd0 : 0 < r0 + c0)
    (hd1 : 0 < r1 + c1) :
    r1 / (r1 + c1) ≤ tol * (r0 / (r0 + c0) * (c1 / (r1 + c1)) + r1 / (r1 + c1)) ↔
      r1 * (r0 + c0) * (1 - tol) ≤ tol * (r0 * c1) := by
  have e1 : (tol * (r0 / (r0 + c0) * (c1 / (r1 + c1)) + r1 / (r1 + c1))) * (r1 + c1)
      = tol * (r0 / (r0 + c0) * c1 + r1) := by
    field_simp
    try ring
  have e2 : tol * (r0 / (r0 + c0) * c1 + r1) = tol * (r0 * c1 + r1 * (r0 + c0)) / (r0 + c0) := by
    field_simp
    try ring
  rw [div_le_iff₀ hd1, e1, e2, le_div_iff₀ hd0]
  constructor <;> intro hh <;> linarith

/-- The effective two-level algebra of risk row 9: dividing by the effective total decay
`U + C > 0` turns the effective criterion into the ladder criterion. -/
private theorem effective_algebra {U C e0 tol : ℝ} (h : 0 < U + C) :
    U / (U + C) ≤ tol * (e0 / (U + C) + U / (U + C)) ↔ (1 - tol) * U ≤ tol * e0 := by
  have e2 : tol * (e0 / (U + C) + U / (U + C)) = tol * (e0 + U) / (U + C) := by
    field_simp
    try ring
  have e3 : tol * (e0 + U) / (U + C) * (U + C) = tol * (e0 + U) := by
    field_simp
    try ring
  rw [e2, div_le_iff₀ h, e3]
  constructor <;> intro hh <;> linarith

/-- The logarithm step of the Marcus bridge (risk row 10 engine): `1 / K ≤ exp y` is equivalent to
`log (1/K) ≤ y`, and `log (1/K) = -log K`. -/
private theorem log_recip_le_iff {K y : ℝ} (hK : 0 < K) :
    (1 / K ≤ Real.exp y) ↔ -Real.log K ≤ y := by
  rw [← Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < 1 / K),
    Real.log_div one_ne_zero (ne_of_gt hK), Real.log_one]
  ring_nf

/-! ## 3. The risk rows (the statements of the statement authority, verbatim) -/

set_option linter.unusedVariables false in
/-- **Risk row 1** (plan §4.2 #13, milestone K1): the total yield splits into emission from the
lowest level plus the leak. The standing premise is kept verbatim from the statement authority;
the split itself needs no positivity. -/
theorem risk_fluoYield_eq_low_add_upper {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    fluoYield rad ic N = emitYield rad ic 0 N + upperYield rad ic N :=
  fluoYield_eq_low_add_upper_free rad ic N

set_option linter.unusedVariables false in
/-- **Risk row 2** (plan §5.1 #4, milestone K2): the Markov recursion of the total yield. The
standing premise is kept verbatim from the statement authority; the recursion is an algebraic
identity of the model and needs no positivity. -/
theorem risk_fluoYield_succ {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1)) :
    fluoYield rad ic (N + 1) =
      radBranch rad ic (N + 1) + icBranch rad ic (N + 1) * fluoYield rad ic N :=
  fluoYield_succ_free rad ic N

set_option linter.unusedVariables false in
/-- **Risk row 3** (plan §5.1 #5, milestone K2): the Markov recursion of the leak. The standing
premise is kept verbatim from the statement authority; the recursion needs no positivity. -/
theorem risk_upperYield_succ {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1)) :
    upperYield rad ic (N + 1) =
      radBranch rad ic (N + 1) + icBranch rad ic (N + 1) * upperYield rad ic N :=
  upperYield_succ_free rad ic N

/-- **Risk row 4** (plan §5.1 #6, milestone K2): probability conservation - the cascade
probability plus the leak is one. Induction on `N`; the step consumes
`radBranch + icBranch = 1` at level `N + 1`, which is where `RateData` is essential. -/
theorem risk_cascade_add_upperYield {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    cascade rad ic 0 N + upperYield rad ic N = 1 := by
  induction N with
  | zero => rw [cascade_self, upperYield_zero, add_zero]
  | succ N ih =>
    have hN : RateData rad ic N :=
      ⟨fun n hn => h.decay_pos n (Nat.le_succ_of_le hn), h.rad_nonneg, h.ic_nonneg⟩
    have hdec : radBranch rad ic (N + 1) + icBranch rad ic (N + 1) = 1 :=
      radBranch_add_icBranch (ne_of_gt (h.decay_pos (N + 1) (le_refl _)))
    have hsum : cascade rad ic 0 N + upperYield rad ic N = 1 := ih hN
    rw [cascade_succ (Nat.zero_le N), upperYield_succ_free]
    have hfac : icBranch rad ic (N + 1) * cascade rad ic 0 N
        + icBranch rad ic (N + 1) * upperYield rad ic N = icBranch rad ic (N + 1) := by
      rw [← mul_add, hsum, mul_one]
    linarith

/-- **Risk row 5** (plan §5.2 #14, milestone K2 - the exact rule): Kasha's rule holds iff no level
above the lowest one emits at all. Forward direction by induction on `N` through the leak recursion
(where `radBranch + icBranch = 1` rules out the degenerate case `icBranch (N+1) = 0`), backward
direction through `radBranch = 0`. -/
theorem risk_kashaRule_iff_rad_zero {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    KashaRule rad ic N ↔ ∀ i, 1 ≤ i → i ≤ N → rad i = 0 := by
  constructor
  · intro hK
    induction N with
    | zero => intro i h1 h2; omega
    | succ N ih =>
      intro i hi1 hi2
      have hN : RateData rad ic N :=
        ⟨fun n hn => h.decay_pos n (Nat.le_succ_of_le hn), h.rad_nonneg, h.ic_nonneg⟩
      have hdec : decay rad ic (N + 1) ≠ 0 := ne_of_gt (h.decay_pos (N + 1) (le_refl _))
      have hnon1 : 0 ≤ radBranch rad ic (N + 1) := radBranch_nonneg h (le_refl _)
      have hnon2 : 0 ≤ icBranch rad ic (N + 1) * upperYield rad ic N :=
        mul_nonneg (icBranch_nonneg h (le_refl _)) (upperYield_nonneg hN)
      unfold KashaRule at hK
      rw [upperYield_succ_free] at hK
      have hradB : radBranch rad ic (N + 1) = 0 := by linarith
      have hicB : icBranch rad ic (N + 1) = 1 := by
        have h1 := radBranch_add_icBranch hdec
        linarith
      have huN : upperYield rad ic N = 0 := by
        have h2 : icBranch rad ic (N + 1) * upperYield rad ic N = 0 := by linarith
        rwa [hicB, one_mul] at h2
      rcases Nat.lt_or_ge i (N + 1) with hlt | hge
      · exact ih hN huN i hi1 (by omega)
      · have hi : i = N + 1 := by omega
        rw [hi]
        have h3 : rad (N + 1) / decay rad ic (N + 1) = 0 := by simpa [radBranch] using hradB
        exact (div_eq_zero_iff.mp h3).resolve_right hdec
  · intro hz
    unfold KashaRule upperYield
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    unfold emitYield radBranch
    rw [hz i hi.1 hi.2, zero_div, zero_mul]

/-- **Risk row 6** (plan §6.1 #1, milestone K3): the exact two-level criterion in rate form, under
`0 < decay rad ic 0` and `0 < decay rad ic 1` (both cross-multiplications have positive factors). -/
theorem risk_kashaWithin_one_iff_rates {rad ic : ℕ → ℝ} {tol : ℝ}
    (h0 : 0 < decay rad ic 0) (h1 : 0 < decay rad ic 1) :
    KashaWithin rad ic tol 1 ↔ rad 1 * decay rad ic 0 * (1 - tol) ≤ tol * (rad 0 * ic 1) := by
  unfold KashaWithin
  rw [upperYield_one, fluoYield_one]
  unfold radBranch icBranch decay
  exact two_level_algebra h0 h1

/-- **Risk row 7 - REFUTED, kernel evidence** (plan §6.1 #2, skeleton lines 384-387): the row's
hypotheses `0 < decay rad ic 0`, `0 < tol`, `0 < rad 1` do **not** determine the sign of the level-1
total decay `decay rad ic 1 = rad 1 + ic 1`, and the cross-multiplication of the rate form by that
possibly negative factor flips the inequality. Witness: `rad = (1, 1, 0, 0, ...)`,
`ic = (1, -3, 0, 0, ...)`, `tol = 1/2`; then `decay 0 = 2 > 0`, `decay 1 = -2`,

* `KashaWithin rad ic (1/2) 1` holds: `upperYield 1 = 1/(-2) = -1/2` and
  `fluoYield 1 = (1/2)*(3/2) - 1/2 = 1/4`, so `-1/2 ≤ 1/8`;
* its right-hand side fails: `(1 - 1/2)/(1/2) = 1` but
  `funnelRatio rad ic = 1*(-3)/(1*2) = -3/2`, and `1 ≤ -3/2` is false.

The minimal correction is the premise the sibling row K3 #1 already carries,
`(h1 : 0 < decay rad ic 1)`; the corrected statement is
`risk_kashaWithin_one_iff_ratio_with_decay_pos`. Not silently repaired: the row itself is not
claimed, only refuted. -/
theorem risk_kashaWithin_one_iff_ratio_refuted :
    ∃ (rad ic : ℕ → ℝ) (tol : ℝ), 0 < decay rad ic 0 ∧ 0 < tol ∧ 0 < rad 1 ∧
      KashaWithin rad ic tol 1 ∧ ¬ ((1 - tol) / tol ≤ funnelRatio rad ic) := by
  refine ⟨fun n => if n = 0 then 1 else if n = 1 then 1 else 0,
    fun n => if n = 0 then 1 else if n = 1 then -3 else 0, 1 / 2, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [decay]
  · norm_num
  · norm_num
  · unfold KashaWithin
    rw [upperYield_one, fluoYield_one]
    norm_num [radBranch, icBranch, decay]
  · unfold funnelRatio
    norm_num [decay]

/-- **Risk row 7 - REFUTED, kernel evidence, universally quantified form**: the row's statement as a
closed proposition is false. Same witness as `risk_kashaWithin_one_iff_ratio_refuted`. -/
theorem risk_kashaWithin_one_iff_ratio_false :
    ¬ (∀ (rad ic : ℕ → ℝ) (tol : ℝ), 0 < decay rad ic 0 → 0 < tol → 0 < rad 1 →
        (KashaWithin rad ic tol 1 ↔ (1 - tol) / tol ≤ funnelRatio rad ic)) := by
  rintro h
  obtain ⟨rad, ic, tol, h0, htol, hr, hW, hnot⟩ := risk_kashaWithin_one_iff_ratio_refuted
  exact hnot ((h rad ic tol h0 htol hr).mp hW)

/-- **Risk row 7, minimal correction** (not the row): the same threshold with the level-1 positivity
premise `0 < decay rad ic 1` added - i.e. risk row 6 divided by `tol * rad 1 * decay 0 > 0`. This is
the only statement change the probe proposes for row 7; the lead decides whether to amend the
statement authority. -/
theorem risk_kashaWithin_one_iff_ratio_with_decay_pos {rad ic : ℕ → ℝ} {tol : ℝ}
    (h0 : 0 < decay rad ic 0) (h1 : 0 < decay rad ic 1) (htol : 0 < tol) (hr : 0 < rad 1) :
    KashaWithin rad ic tol 1 ↔ (1 - tol) / tol ≤ funnelRatio rad ic := by
  have hrd : 0 < rad 1 * decay rad ic 0 := mul_pos hr h0
  rw [risk_kashaWithin_one_iff_rates h0 h1, funnelRatio, div_le_div_iff₀ htol hrd]
  constructor <;> intro hh <;> linarith

/-- **Risk row 8** (plan §6.2 #13, milestone K3 - the negative claim): the levelwise criterion
"`ic` beats `rad` at every upper level" is insufficient. Kernel-checked witness
`rad = fun _ => 1`, `ic = fun _ => 1`: `RateData rad ic 2` holds, the levelwise inequality holds with
equality at both levels 1 and 2 (`1 * 2 ≤ 1 * 2`), and `upperYield 2 = 3/4 > (1/2) * (7/8) =
(1/2) * fluoYield 2`. -/
theorem risk_perLevel_criterion_insufficient :
    ∃ rad ic : ℕ → ℝ, RateData rad ic 2 ∧
      (∀ i, 1 ≤ i → i ≤ 2 → rad i * decay rad ic (i - 1) ≤ ic i * decay rad ic i) ∧
      ¬ KashaWithin rad ic (1 / 2) 2 := by
  refine ⟨fun _ => (1 : ℝ), fun _ => (1 : ℝ), ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro n hn
      norm_num [decay]
    · intro n
      norm_num
    · intro n
      norm_num
  · intro i hi1 hi2
    have h12 : i = 1 ∨ i = 2 := by omega
    rcases h12 with rfl | rfl <;> norm_num [decay]
  · intro hcon
    have hU1 : upperYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 1 = 1 / 2 := by
      have hh := upperYield_succ_free (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 0
      rw [upperYield_zero] at hh
      norm_num [radBranch, icBranch, decay] at hh
      exact hh
    have hU2 : upperYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 2 = 3 / 4 := by
      have hh := upperYield_succ_free (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 1
      rw [hU1] at hh
      norm_num [radBranch, icBranch, decay] at hh
      exact hh
    have hF0 : fluoYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 0 = 1 / 2 := by
      rw [fluoYield_zero]
      norm_num [radBranch, decay]
    have hF1 : fluoYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 1 = 3 / 4 := by
      have hh := fluoYield_succ_free (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 0
      rw [hF0] at hh
      norm_num [radBranch, icBranch, decay] at hh
      exact hh
    have hF2 : fluoYield (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 2 = 7 / 8 := by
      have hh := fluoYield_succ_free (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => (1 : ℝ)) 1
      rw [hF1] at hh
      norm_num [radBranch, icBranch, decay] at hh
      exact hh
    unfold KashaWithin at hcon
    rw [hU2, hF2] at hcon
    norm_num at hcon

set_option linter.unusedVariables false in
/-- **Risk row 9** (plan §7.2 #8, milestone K4 - every ladder is a two-level model in disguise):
the tolerance criterion of the `N`-level ladder is the criterion of its effective two-level data.
The step is the monotone multiplication by `upperYield N + cascade 0 N > 0`; `RateData` is kept
verbatim from the statement authority (the `N`-level split it is normally consumed by needs no
positivity, as risk row 1 shows). -/
theorem risk_kashaWithin_iff_effective {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ}
    (h : RateData rad ic N) (hpos : 0 < upperYield rad ic N + cascade rad ic 0 N) :
    KashaWithin rad ic tol N ↔ KashaWithin (effRad rad ic N) (effIc rad ic N) tol 1 := by
  have hupy : upperYield (effRad rad ic N) (effIc rad ic N) 1
      = upperYield rad ic N / (upperYield rad ic N + cascade rad ic 0 N) := by
    rw [upperYield_one]
    simp [radBranch, effRad, effIc, decay]
  have hfl : fluoYield (effRad rad ic N) (effIc rad ic N) 1
      = (rad 0 / decay rad ic 0 * cascade rad ic 0 N) / (upperYield rad ic N + cascade rad ic 0 N)
        + upperYield rad ic N / (upperYield rad ic N + cascade rad ic 0 N) := by
    rw [fluoYield_one]
    simp [radBranch, icBranch, effRad, effIc, decay]
    try rw [mul_div_assoc]
  have hL : KashaWithin rad ic tol N ↔
      (1 - tol) * upperYield rad ic N ≤ tol * (rad 0 / decay rad ic 0 * cascade rad ic 0 N) := by
    unfold KashaWithin
    rw [fluoYield_eq_low_add_upper_free]
    unfold emitYield radBranch
    constructor <;> intro hh <;> linarith
  have hR : KashaWithin (effRad rad ic N) (effIc rad ic N) tol 1 ↔
      (1 - tol) * upperYield rad ic N ≤ tol * (rad 0 / decay rad ic 0 * cascade rad ic 0 N) := by
    unfold KashaWithin
    rw [hupy, hfl]
    exact effective_algebra hpos
  exact hL.trans hR.symm

set_option linter.unusedVariables false in
/-- **Risk row 11** (plan §4.2 #23, milestone K1): the `if`-chain classifier row. The proof is the
`split_ifs` recipe of `kasha-api-risk.lean` §5; the classifier is built literally from `KashaRule`
and `KashaWithin`, so the equivalence needs no positivity and the standing premise is kept verbatim
from the statement authority. -/
theorem risk_kashaZone_eq_withinTol_iff {rad ic : ℕ → ℝ} {N : ℕ} {tol : ℝ}
    (h : RateData rad ic N) :
    kashaZone rad ic tol N = KashaZone.withinTol ↔
      ¬ KashaRule rad ic N ∧ KashaWithin rad ic tol N := by
  unfold kashaZone KashaRule KashaWithin
  split_ifs with h1 h2
  · exact ⟨fun hc => absurd hc (by intro hh; cases hh), fun hh => absurd h1 hh.1⟩
  · exact ⟨fun _ => ⟨h1, h2⟩, fun _ => rfl⟩
  · exact ⟨fun hc => absurd hc (by intro hh; cases hh), fun hh => absurd hh.2 h2⟩

/-- **Risk row 12** (plan §6.1 #3, milestone K3 - the literature form): with no loss channel at the
lowest level, `decay 0 = rad 0` and `radBranch 0 = rad 0 / rad 0 = 1`, so the two-level total yield
is exactly `1` and the criterion collapses to `k_IC / k_rad ≥ (1 - tol)/tol`. The premise is
`rad 0 ≠ 0` (not `0 < rad 0`), which is what the proof consumes. -/
theorem risk_kashaWithin_one_iff_ic_ratio {rad ic : ℕ → ℝ} {tol : ℝ} (hic0 : ic 0 = 0)
    (hr0 : rad 0 ≠ 0) (htol : 0 < tol) (h1 : 0 < decay rad ic 1) (hr : 0 < rad 1) :
    KashaWithin rad ic tol 1 ↔ (1 - tol) / tol ≤ ic 1 / rad 1 := by
  have hd0 : decay rad ic 0 ≠ 0 := by
    unfold decay
    rw [hic0, add_zero]
    exact hr0
  have hrb0 : radBranch rad ic 0 = 1 := by
    unfold radBranch
    rw [show decay rad ic 0 = rad 0 by unfold decay; rw [hic0, add_zero]]
    exact div_self hr0
  have hF : fluoYield rad ic 1 = 1 := by
    rw [fluoYield_one, hrb0, one_mul, add_comm]
    exact radBranch_add_icBranch (ne_of_gt h1)
  rw [KashaWithin, upperYield_one, hF, mul_one]
  unfold radBranch
  rw [div_le_iff₀ h1, div_le_div_iff₀ htol hr]
  unfold decay
  constructor <;> intro hh <;> linarith

/-- **Risk row 10** (plan §7.2 #12, milestone K4 - the Marcus bridge, squared form). If the `S₂ → S₁`
internal-conversion rate is the Marcus rate of `PhotoLean.Marcus.barrier`, the tolerance criterion is
exactly a bound on the squared energy gap. The bridge chain: risk row 6 (rate form) → divide by
`tol * rad 0 * A > 0` → `1/K ≤ exp (-barrier/(kB*T))` with `K = kashaGapThreshold A (rad 0)
(decay rad ic 0) (rad 1) tol` (the `K` of the task, `A * rad 0 * tol / (rad 1 * decay rad ic 0 *
(1 - tol))`) → take logarithms (`log (1/K) = -log K`, `Real.log_le_iff_le_exp`) → multiply by
`kB * T > 0` → multiply by `4 * lam > 0`. Literature caveat (plan §7.2, `LITERATURE.md`): the
classical strong-coupling Marcus form is a modelling premise, not the general energy-gap law. -/
theorem risk_kashaWithin_one_marcus {rad ic : ℕ → ℝ} {A lam kB T x tol : ℝ}
    (h : RateData rad ic 1) (htol0 : 0 < tol) (htol1 : tol < 1) (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) (hr0 : 0 < rad 0) (hr1 : 0 < rad 1)
    (hic : ic 1 = marcusIC A lam kB T x) :
    KashaWithin rad ic tol 1 ↔
      (lam - x) ^ 2 ≤ 4 * lam * (kB * T) *
        Real.log (kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol) := by
  have hd0 : 0 < decay rad ic 0 := h.decay_pos 0 (by norm_num)
  have hd1 : 0 < decay rad ic 1 := h.decay_pos 1 (le_refl 1)
  have hm : 0 < 1 - tol := by linarith
  have hKpos : 0 < kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol := by
    unfold kashaGapThreshold
    exact div_pos (mul_pos (mul_pos hA hr0) htol0) (mul_pos (mul_pos hr1 hd0) hm)
  have hPpos : 0 < tol * (rad 0 * A) := mul_pos htol0 (mul_pos hr0 hA)
  have hratio : rad 1 * decay rad ic 0 * (1 - tol) / (tol * (rad 0 * A))
      = 1 / kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol := by
    rw [kashaGapThreshold, one_div_div]
    ring
  have hstep1 :
      (rad 1 * decay rad ic 0 * (1 - tol)
          ≤ tol * (rad 0 * (A * Real.exp (-(barrier lam x) / (kB * T)))))
        ↔ (1 / kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol
            ≤ Real.exp (-(barrier lam x) / (kB * T))) := by
    rw [show tol * (rad 0 * (A * Real.exp (-(barrier lam x) / (kB * T))))
          = Real.exp (-(barrier lam x) / (kB * T)) * (tol * (rad 0 * A)) from by ring,
      ← div_le_iff₀ hPpos, hratio]
  have hkey : -Real.log (kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol)
        ≤ -(barrier lam x) / (kB * T)
      ↔ barrier lam x / (kB * T)
          ≤ Real.log (kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol) := by
    rw [show -(barrier lam x) / (kB * T) = -(barrier lam x / (kB * T)) from by ring]
    exact neg_le_neg_iff
  have hassoc : 4 * lam * (kB * T)
        * Real.log (kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol)
      = Real.log (kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol)
        * ((4 * lam) * (kB * T)) := by
    ring
  rw [risk_kashaWithin_one_iff_rates hd0 hd1, hic, marcusIC, hstep1, log_recip_le_iff hKpos, hkey,
    show barrier lam x = (lam - x) ^ 2 / (4 * lam) from rfl, hassoc, div_div,
    div_le_iff₀ (mul_pos (by linarith : (0 : ℝ) < 4 * lam) hkT)]

/-! ## 4. Kernel axiom footprint of every theorem above -/

#print axioms cascade_self
#print axioms upperYield_zero
#print axioms emitYield_self
#print axioms cascade_succ
#print axioms emitYield_succ
#print axioms emitYield_succ_self
#print axioms fluoYield_eq_low_add_upper_free
#print axioms fluoYield_zero
#print axioms upperYield_succ_free
#print axioms fluoYield_succ_free
#print axioms radBranch_add_icBranch
#print axioms radBranch_nonneg
#print axioms icBranch_nonneg
#print axioms cascade_nonneg
#print axioms emitYield_nonneg
#print axioms upperYield_nonneg
#print axioms cascade_zero_one
#print axioms upperYield_one
#print axioms fluoYield_one
#print axioms risk_fluoYield_eq_low_add_upper
#print axioms risk_fluoYield_succ
#print axioms risk_upperYield_succ
#print axioms risk_cascade_add_upperYield
#print axioms risk_kashaRule_iff_rad_zero
#print axioms risk_kashaWithin_one_iff_rates
#print axioms risk_kashaWithin_one_iff_ratio_refuted
#print axioms risk_kashaWithin_one_iff_ratio_false
#print axioms risk_kashaWithin_one_iff_ratio_with_decay_pos
#print axioms risk_perLevel_criterion_insufficient
#print axioms risk_kashaWithin_iff_effective
#print axioms risk_kashaZone_eq_withinTol_iff
#print axioms risk_kashaWithin_one_iff_ic_ratio
#print axioms risk_kashaWithin_one_marcus

end RiskProbe
end Kasha
end PhotoLean
