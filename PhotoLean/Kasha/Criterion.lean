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
end Kasha

end PhotoLean
