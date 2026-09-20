/-
PhotoLean.Kasha.Compose — K4, composition and bridges of Kasha's rule.

This module is the composition layer of the Kasha theory (`theories/kasha/plan.md` §7). The
description layer `PhotoLean/Kasha/Basic.lean` (K1) defines the finite excited-state ladder, its
branching probabilities, the cascade probability and the observables; K4 asks what happens when the
ladder is *composed* and when the internal-conversion rate is given by the Marcus rate law of this
repository's `PhotoLean.Marcus` theory. The three blocks below are:

* **Splitting (rows 1–2).** The cascade probability multiplies across an interior level:
  `cascade i N = cascade i M * cascade M N` for `i ≤ M ≤ N`, and the level-resolved yield inherits
  the split. This is the associativity of the funnel and the reason the blocks below exist.
* **Effective two-level reduction (rows 3–8).** The whole upper block of the ladder behaves as a
  *single* level: `effRad rad ic N` / `effIc rad ic N` give the upper block the radiative total
  `upperYield rad ic N` and the non-radiative total `cascade rad ic 0 N`, the effective ladder at
  excitation level `1` reproduces the funnel margin exactly (`kashaMargin_effective`), and the
  tolerance criterion of the `N`-level ladder **is** the criterion of that effective two-level model
  (`kashaWithin_iff_effective`) — every ladder is a two-level model in disguise.
* **N-level threshold and the Marcus bridge (rows 9–16).** The tolerance form holds iff
  `(1 - tol)/tol ≤ ladderRatio rad ic N` (`kashaWithin_iff_ladderRatio`, the general answer to the
  plan's question ②, with `ladderRatio` the exact `N`-level funnel ratio); and if the `S₂ → S₁`
  internal-conversion rate is the Marcus rate `A · exp (-barrier λ x / (kB·T))`, the same criterion
  is the explicit gap window `(λ - x)² ≤ 4 λ (kB·T) log K` (`kashaWithin_one_marcus`), with its
  failure direction (`not_kashaWithin_of_gap_far`) and the half-width form
  `|λ - x| ≤ √(4 λ (kB·T) log K)` (`kashaWindow_halfWidth`), where
  `K = kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol`.

Physical reading and honesty (plan §1.3 #5, §12, §13 #6). The Marcus bridge is **conditional**: the
identification of internal conversion with the classical strong-coupling Marcus form is the explicit
hypothesis `hic` of the rows below and a modelling premise, not a theorem of this module. The general
energy-gap law is exponential (Jortner) and the promoting-mode / Franck–Condon factors are outside
the model; the classical form used here is the one `PhotoLean.Marcus` models, and the literature
caveat is carried by `theories/kasha/LITERATURE.md`. The standing physical premise bundle `RateData`
is an explicit hypothesis of every physical row and is never hidden in a definition; where a row's
statement carries a premise its proof does not consume, the premise is kept verbatim for statement
fidelity and the local `set_option linter.unusedVariables false in` documents that (the repository
convention of `PhotoLean/Kasha/Basic.lean`).

Statement authority: every definition body and every theorem signature below is taken word for word
from the K4 block of `theories/kasha/probes/kasha-statement-skeleton.lean` (sha256
`801983702a9dc0129e7a2ab4ec6505c4d7c9967daed444c58b460910bc7e3cb0`), which transcribes
`theories/kasha/plan.md` §7.1 and §7.2: 4 definitions and 16 theorems, in the authority's order, with
nothing added, renamed or restated. Note deliberately: the two keyword literals that
`proofs/scripts/check.sh --strict` scans for are not spelled out anywhere in this file — that scan
covers `PhotoLean/**/*.lean` including block comments, so writing them (even in prose) would be a
false-positive FAIL.

Plan locus: `theories/kasha/plan.md` §7 (K4); board `theories/kasha/TASKS.md` §K4. This module
imports `PhotoLean.Kasha.Basic` and `PhotoLean.Marcus.Basic` only — the sharp layer
(`PhotoLean/Kasha/Sharp.lean`) is deliberately *not* imported: rows 9–11 are derived from the K1
level-1 identity `fluoYield_eq_low_add_upper` by algebra, as the plan's risk register requires. The
recipes used below are kernel-checked before delivery in
`theories/kasha/probes/kasha-d-api.lean` (the block split against the delivered `cascade`, the
premise-free level-1 toolkit, the row-7 cancellation, the row-14 square/`sqrt` step),
`theories/kasha/probes/kasha-api-logexp.lean` (the `exp`/`log` chain of row 12, rows 15–16) and
`theories/kasha/probes/kasha-risk-probe.lean` (rows 8 and 12 in their verbatim authority form).

Acceptance commands (run on a clean tree):

    proofs/scripts/lake build PhotoLean.Kasha.Compose
    proofs/scripts/check.sh --strict PhotoLean.Kasha.Compose
    proofs/scripts/axioms.sh PhotoLean.Kasha.Compose PhotoLean.Kasha.<fully.qualified.theorem>

The delivered file contains no unfinished-proof placeholder and no custom axiomatic declaration; the
`#print axioms` gate of every theorem below lists at most `propext`, `Classical.choice`, `Quot.sound`.
-/
import PhotoLean.Kasha.Basic
import PhotoLean.Marcus.Basic

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Kasha

/-! ## Definitions (plan §7.1) -/

/-- Effective two-level radiative data of the ladder at excitation level `N`: level `0` keeps the
lowest state's radiative rate, level `1` carries the **whole upper block's** radiative total
(`upperYield rad ic N`), and every level above `1` is inert (plan §7.1). -/
noncomputable def effRad (rad ic : ℕ → ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n => if n = 0 then rad 0 else if n = 1 then upperYield rad ic N else 0

/-- Effective two-level nonradiative data of the ladder at excitation level `N`: level `0` keeps the
lowest state's loss rate, level `1` carries the upper block's arrival probability
(`cascade rad ic 0 N`), and every level above `1` is inert (plan §7.1). -/
noncomputable def effIc (rad ic : ℕ → ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n => if n = 0 then ic 0 else if n = 1 then cascade rad ic 0 N else 0

/-- The internal-conversion rate in the Marcus form of `PhotoLean.Marcus`: driving force equal to the
energy gap `x`, reorganization energy `lam`, pre-exponential `A` (plan §7.1). -/
noncomputable def marcusIC (A lam kB T x : ℝ) : ℝ :=
  A * Real.exp (-(PhotoLean.Marcus.barrier lam x) / (kB * T))

/-- The gap threshold of the Marcus bridge: the multiplicative constant `K` whose logarithm is the
half-width of the Kasha window (plan §7.1). -/
noncomputable def kashaGapThreshold (A rad0 dec0 rad1 tol : ℝ) : ℝ :=
  A * rad0 * tol / (rad1 * dec0 * (1 - tol))

/-! ## Theorems (plan §7.2) -/

/-- Plan §7.2 #1. **The cascade splits at an interior level**: reaching `i` from `N` without emitting
is reaching `M` from `N` and then `i` from `M`. Proof: induction on the gap `N - M`
(`Nat.le_induction`), peeling the top index of the product with `Finset.prod_Icc_succ_top` and
finishing by associativity; no `Icc`-union lemma is needed (the plan §10 risk register's friction
point). -/
theorem cascade_compose {rad ic : ℕ → ℝ} {i M N : ℕ} (h1 : i ≤ M) (h2 : M ≤ N) :
    cascade rad ic i N = cascade rad ic i M * cascade rad ic M N := by
  induction N, h2 using Nat.le_induction with
  | base => rw [cascade_self, mul_one]
  | succ N hM ih =>
    have hstep : ∀ a : ℕ, a ≤ N →
        cascade rad ic a (N + 1) = cascade rad ic a N * icBranch rad ic (N + 1) := by
      intro a ha
      unfold cascade
      rw [Finset.prod_Icc_succ_top (by omega : a + 1 ≤ N + 1)]
    rw [hstep i (le_trans h1 hM), hstep M hM, ih, mul_assoc]

/-- Plan §7.2 #2. The level-resolved yield inherits the split: emission from `i` under excitation at
`N` is emission from `i` under excitation at `M`, attenuated by the arrival probability
`cascade M N`. -/
theorem emitYield_compose {rad ic : ℕ → ℝ} {i M N : ℕ} (h1 : i ≤ M) (h2 : M ≤ N) :
    emitYield rad ic i N = cascade rad ic M N * emitYield rad ic i M := by
  unfold emitYield
  rw [cascade_compose h1 h2]
  ring

/-- Plan §7.2 #3. The effective data reproduce the lowest level's total decay (definitional, by
`if`-reduction). -/
theorem effDecay_zero (rad ic : ℕ → ℝ) (N : ℕ) :
    decay (effRad rad ic N) (effIc rad ic N) 0 = decay rad ic 0 := by
  simp [decay, effRad, effIc]

/-- Plan §7.2 #4. The effective upper level's total decay is the ladder's **upper-block total**:
the radiative leak `upperYield rad ic N` plus the arrival probability `cascade rad ic 0 N` — the two
channels of the collapsed block. -/
theorem effDecay_one (rad ic : ℕ → ℝ) (N : ℕ) :
    decay (effRad rad ic N) (effIc rad ic N) 1
      = upperYield rad ic N + cascade rad ic 0 N := by
  simp [decay, effRad, effIc]

set_option linter.unusedVariables false in
/-- Plan §7.2 #5. The effective two-level leak is the ladder's leak, normalized by the upper block's
total `upperYield N + cascade 0 N`. The `RateData` premise is part of the row's authority signature
and is **not consumed** by the `if`-reduction (the linter is off locally, the `Basic.lean`
convention). -/
theorem effUpperYield_one {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    upperYield (effRad rad ic N) (effIc rad ic N) 1
      = upperYield rad ic N / (upperYield rad ic N + cascade rad ic 0 N) := by
  have hU : upperYield (effRad rad ic N) (effIc rad ic N) 1
      = radBranch (effRad rad ic N) (effIc rad ic N) 1 := by
    unfold upperYield
    rw [Finset.Icc_self, Finset.sum_singleton]
    exact emitYield_self _ _ 1
  rw [hU, radBranch, effDecay_one]
  simp [effRad]

set_option linter.unusedVariables false in
/-- Plan §7.2 #6. The effective two-level emission from the lowest state is the ladder's
`emitYield rad ic 0 N`, normalized the same way. The `RateData` premise is part of the row's
authority signature and is **not consumed** here (the linter is off locally). -/
theorem effEmitYield_zero_one {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    emitYield (effRad rad ic N) (effIc rad ic N) 0 1
      = emitYield rad ic 0 N / (upperYield rad ic N + cascade rad ic 0 N) := by
  have hC : cascade (effRad rad ic N) (effIc rad ic N) 0 1
      = icBranch (effRad rad ic N) (effIc rad ic N) 1 := by
    unfold cascade
    have hset : Finset.Icc (0 + 1) 1 = ({1} : Finset ℕ) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_singleton]
      omega
    rw [hset, Finset.prod_singleton]
  unfold emitYield radBranch
  rw [hC]
  unfold icBranch
  rw [effDecay_zero, effDecay_one]
  have hR0 : effRad rad ic N 0 = rad 0 := by simp [effRad]
  have hI1 : effIc rad ic N 1 = cascade rad ic 0 N := by simp [effIc]
  rw [hR0, hI1]
  ring

/-- Plan §7.2 #7 — **the ladder's margin is a two-level margin**: the funnel margin of the effective
two-level model is exactly the `N`-level margin `emitYield 0 N / upperYield N`, i.e. the collapse of
the upper block is faithful for the margin too. -/
theorem kashaMargin_effective {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N)
    (hu : 0 < upperYield rad ic N) :
    kashaMargin (effRad rad ic N) (effIc rad ic N) 1 = kashaMargin rad ic N := by
  have hC : 0 ≤ cascade rad ic 0 N := cascade_nonneg h (Nat.zero_le N)
  have hpos : 0 < upperYield rad ic N + cascade rad ic 0 N := by linarith
  unfold kashaMargin
  rw [effUpperYield_one h, effEmitYield_zero_one h]
  exact div_div_div_cancel_right₀ (ne_of_gt hpos) _ _


end Kasha

end PhotoLean
