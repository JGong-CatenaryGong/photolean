/-
PhotoLean.Kasha.Criterion — K2, the law layer of Kasha's rule.

The description layer `PhotoLean.Kasha.Basic` (K1) fixes the finite excited-state ladder, its
branching probabilities and its observables. This module proves the **laws** of that cascade. The
ladder is a Markov chain on the levels `0, 1, …, N`: from level `n` the molecule steps down to
`n - 1` with probability `icBranch n` and emits from level `n` with probability `radBranch n`, and
`radBranch n + icBranch n = 1` (K1). Everything below is a consequence of that chain structure, at
the level of the time-integrated yields — no time-resolved kinetics is involved (plan §1.2, §13).

Content, in the order of the statement authority (plan §5.1, §5.2):

* §5.1 #1–#3 — the one-step recursions of the cascade probability and of the level-resolved yield
  (the `Icc a (b+1)` top split of the ladder);
* §5.1 #4–#5 — the two **Markov recursions**: appending level `N+1` to the ladder gives
  `fluoYield (N+1) = radBranch (N+1) + icBranch (N+1) · fluoYield N`, and the leak obeys the same
  recursion;
* §5.1 #6–#7 — **probability conservation** `cascade 0 N + upperYield N = 1` and its yield
  counterpart `fluoYield N = 1 - icBranch 0 · cascade 0 N`: the total yield is one minus the
  ground-state loss;
* §5.1 #8–#12 — the yield is at most one; it is monotone in the excitation level; the strict
  increase happens exactly when the new level can emit (`0 < rad (N+1)`); and
  `fluoYield N < 1` is exactly the presence of a loss current at the lowest level;
* §5.2 #13–#15 — the leak vanishes iff no level above the lowest emits, hence **the exact rule**:
  Kasha's rule holds iff every level above the lowest has `rad i = 0` (the idealization: real
  excited states have `rad > 0`, which is why the tolerance form of K1 exists);
* §5.2 #16–#18 — the **Kasha–Vavilov equivalence**: `VavilovAt` (excitation-independence of the
  total yield at one step) holds iff the newly excited level is nonradiative, and with a loss
  channel at the lowest level (`0 < ic 0`, an explicit premise) the spectral rule and Vavilov's
  rule are the same condition;
* §5.2 #19–#22 — the rule is **not** a theorem of the model (an admissible equal-rates ladder
  violates it), the description is non-vacuous, the exact rule implies the tolerance form, and the
  leak is bounded by the sum of the upper levels' radiative branches.

What the module does **not** do: it does not derive the branching probabilities from exponential
clocks (modelling premise, plan §13), does not assume that the ladder is truncated anywhere else,
and adds no premise that is not in the statement authority. Every positivity that a proof needs is
either in `RateData` or an explicit hypothesis of the row (engine rule 3).

Statement authority: every theorem signature below is taken word for word from
`theories/kasha/probes/kasha-statement-skeleton.lean` (its §K2 block; sha256
`801983702a9dc0129e7a2ab4ec6505c4d7c9967daed444c58b460910bc7e3cb0`), which transcribes
`theories/kasha/plan.md` §5. This module imports `PhotoLean.Kasha.Basic` and reuses its 25
theorems; nothing of K1 is re-proved or re-defined here. Note deliberately: the two keyword
literals that `proofs/scripts/check.sh --strict` scans for are not spelled out anywhere in this
file — the scan covers `PhotoLean/**/*.lean` including block comments, so writing them (even in
prose) would be a false-positive FAIL.

Plan locus: `theories/kasha/plan.md` §5 (K2); board `theories/kasha/TASKS.md` §K2. Acceptance:

    proofs/scripts/lake build PhotoLean.Kasha.Criterion
    proofs/scripts/check.sh --strict PhotoLean.Kasha.Criterion
    proofs/scripts/axioms.sh PhotoLean.Kasha.Criterion PhotoLean.Kasha.<fully.qualified.theorem>

The delivered file contains no unfinished-proof placeholder and no custom axiomatic declaration;
`#print axioms` lists at most `propext`, `Classical.choice`, `Quot.sound`.
-/
import PhotoLean.Kasha.Basic

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Kasha
/-! ## The cascade laws (plan §5.1) -/

/-- Plan §5.1 #1. Adding a level on top of the ladder multiplies the cascade probability by the
top level's nonradiative branch (the `Icc a (b+1)` top split). -/
theorem cascade_succ {rad ic : ℕ → ℝ} {i N : ℕ} (h : i ≤ N) :
    cascade rad ic i (N + 1) = icBranch rad ic (N + 1) * cascade rad ic i N := by
  unfold cascade
  rw [Finset.prod_Icc_succ_top (by omega : i + 1 ≤ N + 1), mul_comm]
/-- Plan §5.1 #2. The level-resolved yield obeys the same one-step recursion. -/
theorem emitYield_succ {rad ic : ℕ → ℝ} {i N : ℕ} (h : i ≤ N) :
    emitYield rad ic i (N + 1) = icBranch rad ic (N + 1) * emitYield rad ic i N := by
  unfold emitYield
  rw [cascade_succ h]
  ring
/-- Plan §5.1 #3. At its own excitation level a level emits with its radiative branch. -/
theorem emitYield_succ_self (rad ic : ℕ → ℝ) (N : ℕ) :
    emitYield rad ic (N + 1) (N + 1) = radBranch rad ic (N + 1) :=
  emitYield_self rad ic (N + 1)
set_option linter.unusedVariables false in
/-- Plan §5.1 #4 — the Markov recursion of the total yield. The `RateData` premise belongs to the
signature (authority fidelity); the recursion itself is index algebra and consumes no positivity. -/
theorem fluoYield_succ {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1)) :
    fluoYield rad ic (N + 1) =
      radBranch rad ic (N + 1) + icBranch rad ic (N + 1) * fluoYield rad ic N := by
  calc fluoYield rad ic (N + 1)
      = (∑ x ∈ Finset.range (N + 1), emitYield rad ic x (N + 1))
          + emitYield rad ic (N + 1) (N + 1) := by
        rw [fluoYield, Finset.sum_range_succ]
    _ = (∑ x ∈ Finset.range (N + 1), icBranch rad ic (N + 1) * emitYield rad ic x N)
          + emitYield rad ic (N + 1) (N + 1) := by
        rw [Finset.sum_congr rfl
          (fun x hx => emitYield_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hx)))]
    _ = icBranch rad ic (N + 1) * (∑ x ∈ Finset.range (N + 1), emitYield rad ic x N)
          + emitYield rad ic (N + 1) (N + 1) := by
        rw [Finset.mul_sum]
    _ = icBranch rad ic (N + 1) * fluoYield rad ic N + radBranch rad ic (N + 1) := by
        rw [fluoYield, emitYield_succ_self]
    _ = radBranch rad ic (N + 1) + icBranch rad ic (N + 1) * fluoYield rad ic N := by
        rw [add_comm]
set_option linter.unusedVariables false in
/-- Plan §5.1 #5 — the Markov recursion of the leak. As in #4, the `RateData` premise is part of
the signature and the recursion itself needs no positivity. -/
theorem upperYield_succ {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1)) :
    upperYield rad ic (N + 1) =
      radBranch rad ic (N + 1) + icBranch rad ic (N + 1) * upperYield rad ic N := by
  calc upperYield rad ic (N + 1)
      = (∑ x ∈ Finset.Icc 1 N, emitYield rad ic x (N + 1))
          + emitYield rad ic (N + 1) (N + 1) := by
        rw [upperYield, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    _ = (∑ x ∈ Finset.Icc 1 N, icBranch rad ic (N + 1) * emitYield rad ic x N)
          + emitYield rad ic (N + 1) (N + 1) := by
        rw [Finset.sum_congr rfl (fun x hx => emitYield_succ (Finset.mem_Icc.mp hx).2)]
    _ = icBranch rad ic (N + 1) * (∑ x ∈ Finset.Icc 1 N, emitYield rad ic x N)
          + emitYield rad ic (N + 1) (N + 1) := by
        rw [Finset.mul_sum]
    _ = icBranch rad ic (N + 1) * upperYield rad ic N + radBranch rad ic (N + 1) := by
        rw [upperYield, emitYield_succ_self]
    _ = radBranch rad ic (N + 1) + icBranch rad ic (N + 1) * upperYield rad ic N := by
        rw [add_comm]
/-- Plan §5.1 #6 — probability conservation: the probability of reaching the lowest level without
emitting, plus the probability of emitting somewhere above it, is one. Proved by induction on the
excitation level from the two Markov recursions. -/
theorem cascade_add_upperYield {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    cascade rad ic 0 N + upperYield rad ic N = 1 := by
  have key : ∀ N, RateData rad ic N → cascade rad ic 0 N + upperYield rad ic N = 1 := by
    intro N
    induction N with
    | zero =>
        intro h
        rw [cascade_self, upperYield_zero, add_zero]
    | succ N ih =>
        intro h
        have hN : RateData rad ic N :=
          ⟨fun n hn => h.decay_pos n (Nat.le_succ_of_le hn), h.rad_nonneg, h.ic_nonneg⟩
        have hc : cascade rad ic 0 (Nat.succ N)
            = icBranch rad ic (Nat.succ N) * cascade rad ic 0 N := by
          rw [cascade_succ (i := 0) (N := N) (Nat.zero_le N), mul_comm]
        have hu : upperYield rad ic (Nat.succ N)
            = radBranch rad ic (Nat.succ N) + icBranch rad ic (Nat.succ N) * upperYield rad ic N :=
          upperYield_succ h
        have hstep : cascade rad ic 0 N + upperYield rad ic N = 1 := ih hN
        have hsum : radBranch rad ic (Nat.succ N) + icBranch rad ic (Nat.succ N) = 1 :=
          radBranch_add_icBranch (ne_of_gt (h.decay_pos (Nat.succ N) (le_refl _)))
        rw [hc, hu]
        calc icBranch rad ic (Nat.succ N) * cascade rad ic 0 N
              + (radBranch rad ic (Nat.succ N)
                + icBranch rad ic (Nat.succ N) * upperYield rad ic N)
            = radBranch rad ic (Nat.succ N)
              + icBranch rad ic (Nat.succ N) * (cascade rad ic 0 N + upperYield rad ic N) := by
              ring
          _ = radBranch rad ic (Nat.succ N) + icBranch rad ic (Nat.succ N) * 1 := by rw [hstep]
          _ = 1 := by rw [mul_one, hsum]
  exact key N h
/-- Plan §5.1 #7 — the total yield is one minus the ground-state loss current. -/
theorem fluoYield_eq_one_sub_loss {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    fluoYield rad ic N = 1 - icBranch rad ic 0 * cascade rad ic 0 N := by
  have hsplit : fluoYield rad ic N = emitYield rad ic 0 N + upperYield rad ic N :=
    fluoYield_eq_low_add_upper h
  have hcons : cascade rad ic 0 N + upperYield rad ic N = 1 := cascade_add_upperYield h
  have hsum : radBranch rad ic 0 + icBranch rad ic 0 = 1 :=
    radBranch_add_icBranch (ne_of_gt (h.decay_pos 0 (Nat.zero_le N)))
  have hic : icBranch rad ic 0 = 1 - radBranch rad ic 0 := by linarith
  have hupper : upperYield rad ic N = 1 - cascade rad ic 0 N := by linarith
  rw [hsplit, hupper]
  unfold emitYield
  rw [hic]
  ring
/-- Plan §5.1 #8. The total yield is at most one. -/
theorem fluoYield_le_one {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    fluoYield rad ic N ≤ 1 := by
  have h7 := fluoYield_eq_one_sub_loss h
  have hnn : 0 ≤ icBranch rad ic 0 * cascade rad ic 0 N :=
    mul_nonneg (icBranch_nonneg h (Nat.zero_le N)) (cascade_nonneg h (Nat.zero_le N))
  linarith
/-- Plan §5.1 #9. The total yield is monotone in the excitation level. -/
theorem fluoYield_mono_succ {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1)) :
    fluoYield rad ic N ≤ fluoYield rad ic (N + 1) := by
  have hN : RateData rad ic N :=
    ⟨fun n hn => h.decay_pos n (Nat.le_succ_of_le hn), h.rad_nonneg, h.ic_nonneg⟩
  have hrec := fluoYield_succ h
  have hsum : radBranch rad ic (N + 1) + icBranch rad ic (N + 1) = 1 :=
    radBranch_add_icBranch (ne_of_gt (h.decay_pos (N + 1) (le_refl _)))
  have hR : 0 ≤ radBranch rad ic (N + 1) := radBranch_nonneg h (le_refl _)
  have hF : fluoYield rad ic N ≤ 1 := fluoYield_le_one hN
  nlinarith [hrec, hsum, hR, hF]
/-- Plan §5.1 #10. The increase is strict exactly when the newly excited level can emit
radiatively. -/
theorem fluoYield_lt_succ_of_rad_pos {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1))
    (hr : 0 < rad (N + 1)) (h1 : fluoYield rad ic N < 1) :
    fluoYield rad ic N < fluoYield rad ic (N + 1) := by
  have hrec := fluoYield_succ h
  have hsum : radBranch rad ic (N + 1) + icBranch rad ic (N + 1) = 1 :=
    radBranch_add_icBranch (ne_of_gt (h.decay_pos (N + 1) (le_refl _)))
  have hR : 0 < radBranch rad ic (N + 1) := by
    unfold radBranch
    exact div_pos hr (h.decay_pos (N + 1) (le_refl _))
  nlinarith [hrec, hsum, mul_pos hR (sub_pos.mpr h1)]
/-- Plan §5.1 #11. The total yield is unchanged by exciting the next level iff that level cannot
emit (given that the lower ladder already loses something). -/
theorem fluoYield_eq_iff_rad_zero {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1))
    (h1 : fluoYield rad ic N < 1) :
    fluoYield rad ic (N + 1) = fluoYield rad ic N ↔ rad (N + 1) = 0 := by
  have hrec := fluoYield_succ h
  have hsum : radBranch rad ic (N + 1) + icBranch rad ic (N + 1) = 1 :=
    radBranch_add_icBranch (ne_of_gt (h.decay_pos (N + 1) (le_refl _)))
  have hne : (1 : ℝ) - fluoYield rad ic N ≠ 0 := by linarith
  constructor
  · intro heq
    have hfac : radBranch rad ic (N + 1) * (1 - fluoYield rad ic N) = 0 := by
      nlinarith [hrec, hsum, heq]
    have hR0 : radBranch rad ic (N + 1) = 0 := (mul_eq_zero.mp hfac).resolve_right hne
    unfold radBranch at hR0
    exact (div_eq_zero_iff.mp hR0).resolve_right (ne_of_gt (h.decay_pos (N + 1) (le_refl _)))
  · intro hr0
    have hR0 : radBranch rad ic (N + 1) = 0 := by
      unfold radBranch
      rw [hr0]
      simp
    have hI : icBranch rad ic (N + 1) = 1 := by linarith
    rw [hrec, hR0, hI, zero_add, one_mul]
/-- Plan §5.1 #12. The total yield is strictly below one iff a loss current flows out of the
lowest level (`icBranch 0 > 0` together with the arrival probability `cascade 0 N`). -/
theorem fluoYield_lt_one_iff_loss {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    fluoYield rad ic N < 1 ↔ 0 < icBranch rad ic 0 * cascade rad ic 0 N := by
  rw [fluoYield_eq_one_sub_loss h]
  constructor <;> intro hh <;> linarith
/-! ## The exact rule and Vavilov's rule (plan §5.2) -/

/-- Plan §5.2 #13. The leak vanishes iff no level above the lowest emits at all. -/
theorem upperYield_eq_zero_iff {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    upperYield rad ic N = 0 ↔ ∀ i, 1 ≤ i → i ≤ N → emitYield rad ic i N = 0 := by
  rw [upperYield, Finset.sum_eq_zero_iff_of_nonneg
    (fun i hi => emitYield_nonneg h (Finset.mem_Icc.mp hi).2)]
  constructor
  · intro hh i hi1 hiN
    exact hh i (Finset.mem_Icc.mpr ⟨hi1, hiN⟩)
  · intro hh i hi
    exact hh i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
/-- Plan §5.2 #14 — **the exact rule**: Kasha's rule holds iff every level above the lowest one is
nonradiative. Proved by induction on the excitation level: the new top level must be nonradiative,
and it cannot be the level that stops the cascade (a level with `rad = 0` still has `decay > 0`,
so it steps down with certainty), so the lower ladder must satisfy the rule by the induction
hypothesis. -/
theorem kashaRule_iff_rad_zero {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    KashaRule rad ic N ↔ ∀ i, 1 ≤ i → i ≤ N → rad i = 0 := by
  have key : ∀ N, RateData rad ic N →
      (KashaRule rad ic N ↔ ∀ i, 1 ≤ i → i ≤ N → rad i = 0) := by
    intro N
    induction N with
    | zero =>
        intro h
        constructor
        · intro _ i hi1 hiN
          omega
        · intro _
          exact upperYield_zero rad ic
    | succ N ih =>
        intro h
        have hN : RateData rad ic N :=
          ⟨fun n hn => h.decay_pos n (Nat.le_succ_of_le hn), h.rad_nonneg, h.ic_nonneg⟩
        constructor
        · intro hK
          have hu : upperYield rad ic (Nat.succ N) = 0 := hK
          have hrec : upperYield rad ic (Nat.succ N) =
              radBranch rad ic (Nat.succ N)
                + icBranch rad ic (Nat.succ N) * upperYield rad ic N :=
            upperYield_succ h
          have hRnn : 0 ≤ radBranch rad ic (Nat.succ N) := radBranch_nonneg h (le_refl _)
          have hInn : 0 ≤ icBranch rad ic (Nat.succ N) := icBranch_nonneg h (le_refl _)
          have hUnn : 0 ≤ upperYield rad ic N := upperYield_nonneg hN
          have hR0 : radBranch rad ic (Nat.succ N) = 0 := by nlinarith
          have hI0 : icBranch rad ic (Nat.succ N) * upperYield rad ic N = 0 := by linarith
          have hrad : rad (Nat.succ N) = 0 := by
            unfold radBranch at hR0
            exact (div_eq_zero_iff.mp hR0).resolve_right
              (ne_of_gt (h.decay_pos (Nat.succ N) (le_refl _)))
          have hU0 : upperYield rad ic N = 0 := by
            by_contra hne
            have hicb : icBranch rad ic (Nat.succ N) = 0 :=
              (mul_eq_zero.mp hI0).resolve_right hne
            have hic : ic (Nat.succ N) = 0 := by
              unfold icBranch at hicb
              exact (div_eq_zero_iff.mp hicb).resolve_right
                (ne_of_gt (h.decay_pos (Nat.succ N) (le_refl _)))
            have hzero : decay rad ic (Nat.succ N) = 0 := by
              unfold decay
              rw [hrad, hic]
              ring
            exact absurd hzero (ne_of_gt (h.decay_pos (Nat.succ N) (le_refl _)))
          have ihN := (ih hN).mp hU0
          intro i hi1 hiS
          rcases Nat.lt_or_eq_of_le hiS with hlt | heq
          · exact ihN i hi1 (Nat.le_of_lt_succ hlt)
          · rw [heq]
            exact hrad
        · intro hrad0
          have hR0 : radBranch rad ic (Nat.succ N) = 0 := by
            unfold radBranch
            rw [hrad0 (Nat.succ N) (Nat.succ_pos N) (le_refl _)]
            simp
          have hU0 : upperYield rad ic N = 0 :=
            (ih hN).mpr (fun j hj1 hjN => hrad0 j hj1 (le_trans hjN (Nat.le_succ N)))
          show upperYield rad ic (Nat.succ N) = 0
          rw [upperYield_succ h, hR0, zero_add, hU0, mul_zero]
  exact key N h
/-- Plan §5.2 #15. A single radiatively emitting level above the lowest already violates the exact
rule. -/
theorem not_kashaRule_of_rad_pos {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N)
    (h1 : 1 ≤ i) (h2 : i ≤ N) (hr : 0 < rad i) : ¬ KashaRule rad ic N := by
  intro hK
  exact absurd ((kashaRule_iff_rad_zero h).mp hK i h1 h2) (ne_of_gt hr)
/-- Plan §5.2 #16. Vavilov's rule at one step is the nonradiativity of the newly excited level
(same content as §5.1 #11, read as the `VavilovAt` predicate). -/
theorem vavilovAt_iff_rad_zero {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic (N + 1))
    (h1 : fluoYield rad ic N < 1) : VavilovAt rad ic N ↔ rad (N + 1) = 0 :=
  fluoYield_eq_iff_rad_zero h h1
/-- Plan §5.2 #17. Vavilov's rule up to level `N` holds iff every level up to `N` other than the
lowest is nonradiative, given that the lower ladders each lose something. -/
theorem vavilovUpTo_iff_rad_zero {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N)
    (h1 : ∀ i, i < N → fluoYield rad ic i < 1) :
    VavilovUpTo rad ic N ↔ ∀ i, i < N → rad (i + 1) = 0 := by
  constructor
  · intro hV i hi
    have hR : RateData rad ic (i + 1) :=
      ⟨fun n hn => h.decay_pos n (le_trans hn (Nat.succ_le_of_lt hi)), h.rad_nonneg, h.ic_nonneg⟩
    exact (vavilovAt_iff_rad_zero hR (h1 i hi)).mp (hV i hi)
  · intro hr i hi
    have hR : RateData rad ic (i + 1) :=
      ⟨fun n hn => h.decay_pos n (le_trans hn (Nat.succ_le_of_lt hi)), h.rad_nonneg, h.ic_nonneg⟩
    exact (vavilovAt_iff_rad_zero hR (h1 i hi)).mpr (hr i hi)
/-- Plan §5.2 #18 — **the Kasha–Vavilov equivalence**: with a loss channel at the lowest level
(`0 < ic 0`), the spectral rule and the excitation-independence of the total yield are the same
condition. The loss premise is what makes every lower ladder lose something
(`fluoYield i < 1`), i.e. it is exactly what rules out the degenerate lossless model in which
Vavilov's rule holds vacuously. -/
theorem kashaRule_iff_vavilovUpTo {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N)
    (hloss : 0 < ic 0) : KashaRule rad ic N ↔ VavilovUpTo rad ic N := by
  have h0lt : fluoYield rad ic 0 < 1 := by
    rw [fluoYield_zero]
    unfold radBranch
    rw [div_lt_one (h.decay_pos 0 (Nat.zero_le N))]
    unfold decay
    linarith
  constructor
  · intro hK
    have hrad : ∀ j, 1 ≤ j → j ≤ N → rad j = 0 := (kashaRule_iff_rad_zero h).mp hK
    intro i hi
    have hR : RateData rad ic (i + 1) :=
      ⟨fun n hn => h.decay_pos n (le_trans hn (Nat.succ_le_of_lt hi)), h.rad_nonneg, h.ic_nonneg⟩
    have hR0 : radBranch rad ic (i + 1) = 0 := by
      unfold radBranch
      rw [hrad (i + 1) (Nat.succ_pos i) (Nat.succ_le_of_lt hi), zero_div]
    have hI : icBranch rad ic (i + 1) = 1 := by
      have hsum := radBranch_add_icBranch (rad := rad) (ic := ic) (n := i + 1)
        (ne_of_gt (hR.decay_pos (i + 1) (le_refl _)))
      linarith
    show fluoYield rad ic (i + 1) = fluoYield rad ic i
    rw [fluoYield_succ hR, hR0, zero_add, hI, one_mul]
  · intro hV
    have hchain : ∀ i, i ≤ N → fluoYield rad ic i = fluoYield rad ic 0 := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ k ih =>
          intro hk
          exact (hV k (Nat.lt_of_succ_le hk)).trans (ih (Nat.le_of_succ_le hk))
    have hrad : ∀ j, 1 ≤ j → j ≤ N → rad j = 0 := by
      intro j hj1 hjN
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hk : k < N := by omega
      have hR : RateData rad ic (k + 1) :=
        ⟨fun n hn => h.decay_pos n (le_trans hn (Nat.succ_le_of_lt hk)), h.rad_nonneg, h.ic_nonneg⟩
      have hlt : fluoYield rad ic k < 1 := by
        rw [hchain k (le_of_lt hk)]
        exact h0lt
      exact (vavilovAt_iff_rad_zero hR hlt).mp (hV k hk)
    exact (kashaRule_iff_rad_zero h).mpr hrad
/-- Plan §5.2 #19 — **the rule is not a theorem of the model**: the equal-rates ladder
`rad ≡ ic ≡ 1` at excitation level `1` is admissible and violates the exact rule (level `1` emits
with probability `1/2`). -/
theorem not_kasha_universal :
    ∃ (rad ic : ℕ → ℝ) (N : ℕ), RateData rad ic N ∧ ¬ KashaRule rad ic N := by
  have hR : RateData (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => 1) 1 := by
    refine ⟨fun n hn => ?_, fun n => by norm_num, fun n => by norm_num⟩
    unfold decay
    norm_num
  refine ⟨fun _ => 1, fun _ => 1, 1, hR, ?_⟩
  intro hK
  have hrad := (kashaRule_iff_rad_zero hR).mp hK 1 (by norm_num) (by norm_num)
  norm_num at hrad
/-- Plan §5.2 #20 — non-vacuity of the description: the ladder with `rad 0 = 1`, `rad n = 0` for
`n ≥ 1`, `ic ≡ 1` satisfies the exact rule at excitation level `1` (K1's
`kashaRule_of_rad_zero`). -/
theorem kashaDescriptor_nonvacuous : ∃ rad ic : ℕ → ℝ, KashaDescriptor rad ic := by
  have hR : RateData (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) (fun _ : ℕ => 1) 1 := by
    refine ⟨fun n hn => ?_, fun n => ?_, fun n => by norm_num⟩
    · interval_cases n <;> norm_num [decay]
    · split_ifs <;> norm_num
  refine ⟨fun n : ℕ => if n = 0 then (1 : ℝ) else 0, fun _ : ℕ => 1, 1, ?_⟩
  refine kashaRule_of_rad_zero hR ?_
  intro i hi1 hiN
  have hi : i = 1 := by omega
  subst hi
  simp
end Kasha

end PhotoLean
