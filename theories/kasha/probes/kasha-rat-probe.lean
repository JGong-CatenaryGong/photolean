/-
K-PROBE-2 — the ℚ verdict recipe probe for the Kasha theory (plan §8.1 / §8.2), owner `prover_c`.

**Purpose.** K5a (`PhotoLean/Kasha/RatModel.lean`) and K5b (`PhotoLean/Kasha/Instances.lean`) rest
on the claim that the concrete instance rows are *kernel computations*: the rational verdict
cascade of plan §8.1 evaluated at the plan §8.2 ladder data must close by `norm_num` (the measured
BEP recipe), because `by decide` does not reduce `ℚ` goals carrying `/`-literals and
`native_decide` is banned by the axiom discipline (`Lean.ofReduceBool` is outside
`ALLOWED_AXIOMS`). This file establishes that recipe end-to-end, on the exact definitions and the
exact row shapes of the plan, **before** K5a/K5b are dispatched.

**Statement authority.** `theories/kasha/probes/kasha-statement-skeleton.lean` (K5a/K5b blocks,
plan §8.1/§8.2). The definitions below are the skeleton's, verbatim (`decayQ` … `threeIc`), and the
rows are the skeleton's rows I1–I7b/I9 transported to the probe's `probe_*` names. The probe is a
scratch artifact: it lives under `theories/kasha/probes/`, outside `SOURCE_DIRS`, and is run with
`proofs/scripts/lake env lean theories/kasha/probes/kasha-rat-probe.lean` (exit 0 is the gate).

**The recipe (measured, one uniform tactic line per row).** Unfold the definitions and the
`Finset` recursions by handing `norm_num` the seven evaluation lemmas

  `Finset.sum_range_succ`, `Finset.sum_range_one`, `Finset.sum_Icc_succ_top`,
  `Finset.sum_singleton`, `Finset.prod_Icc_succ_top`, `Finset.Icc_self`, `Finset.prod_singleton`

together with the ladder definitions; `norm_num` then does the `ℚ` arithmetic. `norm_num`'s own
simp set already reduces the empty finsets (`Finset.Icc (i+1) i`, `Finset.range 0`), so
`Finset.Icc_eq_empty` / `Finset.prod_empty` / `Finset.sum_range_zero` are **not** needed for these
rows. Measured negatives and the alternative data formulations are recorded in the block below the
rows; the exact failure of `by decide` is in the comment there.

**Statement-defect evidence + repair.** `probe_criterion_premises_insufficient` below is a
kernel-checked refutation: the skeleton's K5a row `kashaWithinQ_iff_funnelRatioQ` (premises
`0 < decayQ rad ic 0`, `0 < tol`, `0 < rad 1`) is **false as stated** — the totalised `ℚ` division
makes `decayQ rad ic 1 = 0` reachable without any hypothesis excluding it. The repaired row
(`+ 0 < decayQ rad ic 1`, or `QRateData rad ic 1` in its place) is proved below as
`probe_criterion_general`, together with the four ℚ-side index lemmas that the general row needs
(they are the ℚ mirrors of K1's `cascade_self` / `fluoYield` recursion and are the recipe K5a
should use). See the two docstrings.

No unproved placeholder and no custom axiomatic declaration anywhere in this file (engine rules 2);
the `#print axioms` block at the end is the audit.
-/
import Mathlib

open scoped BigOperators

set_option autoImplicit false

namespace PhotoLean

namespace Kasha

/-! ## Definitions (plan §8.1 / §8.2 — the skeleton's bodies, verbatim) -/

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

/-- Rational tolerance predicate (plan §8.1). -/
def KashaWithinQ (rad ic : ℕ → ℚ) (tol : ℚ) (N : ℕ) : Prop :=
  upperYieldQ rad ic N ≤ tol * fluoYieldQ rad ic N

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

/-! ## The rows (probe names; plan §8.2 rows in brackets)

One uniform recipe: `norm_num [<definitions>, <the seven Finset lemmas>]`. Every row below was
closed by exactly that tactic line; the lemma list is repeated verbatim in each proof so that each
row can be copied into `RatModel.lean` / `Instances.lean` as-is. -/

/-- [I4] The `N = 1` total yield of the conforming ladder is exactly `1`. -/
theorem probe_fluoYield_one : fluoYieldQ (twoRad 1 1) (twoIc 0 100) 1 = 1 := by
  norm_num [fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ, decayQ, twoRad, twoIc,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- [I5] The `N = 1` leak of the conforming ladder is `1/101 = radBranch 1`. -/
theorem probe_upperYield_one : upperYieldQ (twoRad 1 1) (twoIc 0 100) 1 = 1 / 101 := by
  norm_num [upperYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ, decayQ, twoRad, twoIc,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- [I1] Conforming control: `ic 1 / rad 1 = 100 ≥ 99` at `tol = 1/100`. -/
theorem probe_conforming : KashaWithinQ (twoRad 1 1) (twoIc 0 100) (1 / 100) 1 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- [I2] Anti-Kasha control at the same tolerance: `ic 1 / rad 1 = 10 < 99`. -/
theorem probe_antiKasha : ¬ KashaWithinQ (twoRad 1 1) (twoIc 0 10) (1 / 100) 1 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- [I3] The threshold `ic 1 = 99` is attained with equality. -/
theorem probe_threshold_boundary : KashaWithinQ (twoRad 1 1) (twoIc 0 99) (1 / 100) 1 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- [I3b] One unit below the threshold fails: the boundary is sharp. -/
theorem probe_threshold_below : ¬ KashaWithinQ (twoRad 1 1) (twoIc 0 (9899 / 100)) (1 / 100) 1 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- [I6] The three-level recursion at concrete rationals: `fluoYieldQ 2 = 7/8`. -/
theorem probe_three_fluo : fluoYieldQ (threeRad 1 1 1) (threeIc 1 1 1) 2 = 7 / 8 := by
  norm_num [fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ, decayQ, threeRad, threeIc,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- [I7] The equal-rates ladder leaks `3/4` — **this is the `N = 2` row that needs the
`Finset.prod_Icc_succ_top` index surgery**: its cascade carries the non-singleton bound
`Finset.Icc 1 2`. -/
theorem probe_three_leak : upperYieldQ (threeRad 1 1 1) (threeIc 1 1 1) 2 = 3 / 4 := by
  norm_num [upperYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ, decayQ, threeRad, threeIc,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- [I7b] The same ladder violates the tolerance form at `tol = 1/2`: `upperYield/fluoYield = 6/7`. -/
theorem probe_equalRates_violating : ¬ KashaWithinQ (threeRad 1 1 1) (threeIc 1 1 1) (1 / 2) 2 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, threeRad, threeIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- [I9] The classifier on the I2 data lands in `violating`. -/
theorem probe_verdict_violating :
    kashaQVerdict (twoRad 1 1) (twoIc 0 10) (1 / 100) 1 = KashaQVerdict.violating := by
  norm_num [kashaQVerdict, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- [I8/I14] The no-loss ladder `rad ≡ 1`, `ic ≡ 0` lands in the vanishing-leak branch `pure`:
the totalised division `0 / 0 = 0` is what makes the branch take, and `norm_num` closes it. -/
theorem probe_verdict_pure :
    kashaQVerdict (twoRad 1 0) (twoIc 0 0) (1 / 100) 1 = KashaQVerdict.pure := by
  norm_num [kashaQVerdict, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- The ℚ threshold row at the conforming instance: both sides are true at `ic 1 = 100`
(`1/101 ≤ 1/100`, and `99 ≤ funnelRatioQ = 100`). This is the concrete instance of the K5a row
`kashaWithinQ_iff_funnelRatioQ` — see the defect row below for why the *general* row needs one
more premise. -/
theorem probe_criterion : KashaWithinQ (twoRad 1 1) (twoIc 0 100) (1 / 100) 1 ↔
    (1 - (1 / 100)) / (1 / 100) ≤ funnelRatioQ (twoRad 1 1) (twoIc 0 100) := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    funnelRatioQ, decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one,
    Finset.sum_Icc_succ_top, Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]

/-! ## Measured facts (probe findings; negatives included)

* **`by decide` cannot close these rows.** `decide` reduces the `ℚ` comparison only for
  division-free literals: it gets stuck in `Rat.instDecidableLt` → `Int.decNonneg`, which does not
  reduce on `/`-literals. Measured on row 1 (`theories/kasha/probes/kasha-rat-scratch.lean`):
  `tactic 'decide' failed for proposition fluoYieldQ (twoRad 1 1) (twoIc 0 100) 1 = 1`.
  `native_decide` *does* evaluate them but is banned (`Lean.ofReduceBool ∉ ALLOWED_AXIOMS`).

* **`Finset.sum` / `Finset.prod` do not reduce under `norm_num` alone.** Measured: `norm_num` with
  only the definitions leaves the sum/product intact (it never matches `Finset.Icc (i+1) N`). The
  seven lemmas listed in the header are exactly what is needed:
  `Finset.sum_range_succ` + `Finset.sum_range_one` expand `∑_{i ∈ range (N+1)}` (for `N = 1`;
  `Finset.sum_range_zero` is not needed because `range 1` is already the base case),
  `Finset.sum_Icc_succ_top` + `Finset.sum_singleton` expand `∑_{i ∈ Icc 1 N}`,
  `Finset.prod_Icc_succ_top` + `Finset.Icc_self` + `Finset.prod_singleton` expand
  `∏_{j ∈ Icc (i+1) N}` (the `N = 2` cascades carry the genuinely non-singleton bound `Icc 1 2`,
  and the `Icc (i+1) i` cascades need `Finset.Icc_eq_empty_iff`-style reasoning that `norm_num`'s
  own simp set already supplies — adding `Finset.Icc_eq_empty`, `Finset.prod_empty` or
  `Finset.sum_range_zero` to the list changes nothing, so the minimal list above is used).

* **The `Icc (i+1) i` side condition is what breaks `simp only`.** With `simp only [...]` (no
  `norm_num`), the empty-finset step needs the numerals normalized first: `Finset.Icc_eq_empty`
  asks for `¬ (i+1 ≤ i)`, and plain `simp only` cannot discharge it, while
  `simp (config := { decide := true }) only [...]` and plain `simp` can. This matters only for the
  *general* K5a rows (symbolic `rad ic`), not for the concrete instance rows above.

* **Alternative instance data are not faster.** Measured per-declaration elaboration time
  (`set_option trace.profiler true`, same machine, same recipe, `N = 2` rows): the skeleton's
  `if`-ladder `twoRad`/`threeRad` 0.51 s (fluo) / 0.32 s (leak); a `List`-access ladder
  `fun n => l.getD n 0` 0.59 s / 0.35 s; an `![…]`-literal ladder `fun n => if h : n < 3 then
  v ⟨n, h⟩ else 0` with `v : Fin 3 → ℚ` 0.46 s / 0.28 s. All three formulations close, all cost the
  same order (`norm_num`'s rational arithmetic dominates, not the data lookup), and the `![…]` form
  is only ~10 % cheaper. **Recommendation: keep the skeleton's `if`-ladders** — an alternative data
  type would change the statement authority for no measurable gain.

* **A `deriving DecidableEq` on `KashaQVerdict` is not needed for the rows above** (`norm_num`
  closes the `if`-cascade by proof terms, and the constructor inequality `pure ≠ violating` is
  discharged by the branch structure), but BEP's `EPQVerdict` does carry `deriving DecidableEq,
  Repr`; the classifier rows of K5a (`kashaQVerdict_eq_*_iff`) are easier with it, and the skeleton
  currently has no `deriving` clause — flagged to the lead. -/

/-! ## Statement-defect evidence: the K5a criterion row is false as stated

The skeleton's K5a row is

```
theorem kashaWithinQ_iff_funnelRatioQ {rad ic : ℕ → ℚ} {tol : ℚ} (h0 : 0 < decayQ rad ic 0)
    (htol : 0 < tol) (hr : 0 < rad 1) :
    KashaWithinQ rad ic tol 1 ↔ (1 - tol) / tol ≤ funnelRatioQ rad ic
```

**Counterexample (kernel-checked below).** Take `rad = twoRad 1 1` (so `rad 1 = 1 > 0`),
`ic = twoIc 0 (-1)`, `tol = 1/2`. Then `decayQ rad ic 0 = 1 > 0` and `0 < tol`, so every premise
of the row holds, yet `decayQ rad ic 1 = 1 + (-1) = 0`: the totalised `ℚ` division gives
`radBranchQ rad ic 1 = 1/0 = 0` and `icBranchQ rad ic 1 = (-1)/0 = 0`, hence
`upperYieldQ rad ic 1 = 0` and `fluoYieldQ rad ic 1 = 0`, so the left side is `0 ≤ 0` — **true** —
while `funnelRatioQ rad ic = 1 * (-1) / (1 * 1) = -1` and `(1 - 1/2)/(1/2) = 1`, so the right side
is `1 ≤ -1` — **false**. The `↔` therefore fails: the premise list does not exclude the degenerate
`decayQ rad ic 1 = 0` configuration, which the totalised division turns into a `pure`-looking row.

**Repair.** Add `(h1 : 0 < decayQ rad ic 1)` — equivalently, consume `QRateData rad ic 1`, whose
first conjunct is exactly `∀ n ≤ 1, 0 < decayQ rad ic n`; with `0 ≤ ic 1` from the bundle the
degenerate configuration is unreachable. The ℝ-side twin `kashaWithin_one_iff_ratio` (K3 #2, same
premise list) has the same defect and needs the same premise; its sibling
`kashaWithin_one_iff_rates` (K3 #1) already carries `h1 : 0 < decay rad ic 1`, so the fix is
consistent with the layer above. Statement changes go through the skeleton and the API log (engine
rule 1) — this probe only records the evidence. -/

/-- Kernel evidence for the defect above: with `rad = twoRad 1 1`, `ic = twoIc 0 (-1)`,
`tol = 1/2`, **all** premises of the skeleton's K5a criterion row hold, while the left side of the
`↔` is true and the right side is false. -/
theorem probe_criterion_premises_insufficient :
    (0 < decayQ (twoRad 1 1) (twoIc 0 (-1)) 0) ∧ (0 < (1 / 2 : ℚ)) ∧ (0 < twoRad 1 1 1) ∧
      KashaWithinQ (twoRad 1 1) (twoIc 0 (-1)) (1 / 2) 1 ∧
      ¬ ((1 - (1 / 2)) / (1 / 2) ≤ funnelRatioQ (twoRad 1 1) (twoIc 0 (-1))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [decayQ, twoRad, twoIc]
  · norm_num
  · norm_num [twoRad]
  · norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
      decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
      Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  · norm_num [funnelRatioQ, decayQ, twoRad, twoIc]

/-! ## Bonus: the repaired general criterion row and the ℚ-side index lemmas

The four lemmas below are the ℚ mirror of K1's `cascade_self` / `fluoYield` recursions at the
two-level instance, in the exact closed forms the general row consumes. They are **not** part of
the K5a inventory of plan §3 (16 definitions + 1 inductive + 12 theorems); the fidelity checker
tolerates extra declarations (BEP's `RatModel.lean` carries its AUX twins), but if the lead prefers
the inventory to stay exact, inline them as `have`s in the criterion proof.

The finset step is where `simp`'s discharger is *not* reliable: for the empty bound
`Finset.Icc (i+1) i` the conditional lemma `Finset.Icc_eq_empty` needs `¬ (i+1 ≤ i)` discharged, and
a `simp only` call whose body is a division does **not** do it (measured; the bare-product case
happens to close, the general row does not). The api_researcher-calibrated route
`rw [Finset.Icc_eq_empty_iff.mpr (by omega : …), Finset.prod_empty]` is what works and is used
below (the same recipe as `theories/kasha/probes/kasha-api-cascade.lean`). -/

/-- ℚ index lemma: the `i = 0` two-level cascade is `icBranchQ rad ic 1`. -/
lemma probe_cascadeQ_zero_one (rad ic : ℕ → ℚ) : cascadeQ rad ic 0 1 = ic 1 / decayQ rad ic 1 := by
  unfold cascadeQ icBranchQ
  rw [Finset.Icc_self, Finset.prod_singleton]

/-- ℚ index lemma: the `i = 1` two-level cascade is `1` (empty `Icc 2 1`). -/
lemma probe_cascadeQ_one_one (rad ic : ℕ → ℚ) : cascadeQ rad ic 1 1 = 1 := by
  unfold cascadeQ
  rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ ((1 : ℕ) + 1 ≤ 1)), Finset.prod_empty]

/-- ℚ index lemma: the `N = 1` total yield in closed form. -/
lemma probe_fluoYieldQ_one (rad ic : ℕ → ℚ) :
    fluoYieldQ rad ic 1 = rad 0 / decayQ rad ic 0 * (ic 1 / decayQ rad ic 1) +
      rad 1 / decayQ rad ic 1 := by
  unfold fluoYieldQ emitYieldQ radBranchQ
  rw [Finset.sum_range_succ, Finset.sum_range_one, probe_cascadeQ_zero_one, probe_cascadeQ_one_one,
    mul_one]

/-- ℚ index lemma: the `N = 1` leak in closed form. -/
lemma probe_upperYieldQ_one (rad ic : ℕ → ℚ) : upperYieldQ rad ic 1 = rad 1 / decayQ rad ic 1 := by
  unfold upperYieldQ emitYieldQ radBranchQ
  rw [Finset.Icc_self, Finset.sum_singleton, probe_cascadeQ_one_one, mul_one]

/-- **The repaired K5a criterion row**: the skeleton's `kashaWithinQ_iff_funnelRatioQ` with the
missing premise `0 < decayQ rad ic 1` added. Route: the two closed forms above, then the outer
divisions are cleared with `div_le_iff₀` / `le_div_iff₀` and the remaining fraction is normalized by
`field_simp` + `ring`; `nlinarith` finishes both directions. -/
theorem probe_criterion_general {rad ic : ℕ → ℚ} {tol : ℚ} (h0 : 0 < decayQ rad ic 0)
    (h1 : 0 < decayQ rad ic 1) (htol : 0 < tol) (hr : 0 < rad 1) :
    KashaWithinQ rad ic tol 1 ↔ (1 - tol) / tol ≤ funnelRatioQ rad ic := by
  have hp : 0 < rad 1 * decayQ rad ic 0 := mul_pos hr h0
  have h2 : tol * (rad 0 / decayQ rad ic 0 * (ic 1 / decayQ rad ic 1) + rad 1 / decayQ rad ic 1)
        * decayQ rad ic 1 = tol * (rad 0 * ic 1 / decayQ rad ic 0) + tol * rad 1 := by
    field_simp
    ring
  have h5 : rad 0 * ic 1 / (rad 1 * decayQ rad ic 0) * tol * (rad 1 * decayQ rad ic 0)
      = tol * (rad 0 * ic 1) := by
    field_simp
    ring
  simp only [KashaWithinQ, probe_fluoYieldQ_one, probe_upperYieldQ_one, funnelRatioQ]
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

end Kasha

end PhotoLean

/-! ## Axiom audit (engine rule 2) — every delivered row must sit inside
`{propext, Classical.choice, Quot.sound}`. -/

#print axioms PhotoLean.Kasha.probe_fluoYield_one
#print axioms PhotoLean.Kasha.probe_upperYield_one
#print axioms PhotoLean.Kasha.probe_conforming
#print axioms PhotoLean.Kasha.probe_antiKasha
#print axioms PhotoLean.Kasha.probe_threshold_boundary
#print axioms PhotoLean.Kasha.probe_threshold_below
#print axioms PhotoLean.Kasha.probe_three_fluo
#print axioms PhotoLean.Kasha.probe_three_leak
#print axioms PhotoLean.Kasha.probe_equalRates_violating
#print axioms PhotoLean.Kasha.probe_verdict_violating
#print axioms PhotoLean.Kasha.probe_verdict_pure
#print axioms PhotoLean.Kasha.probe_criterion
#print axioms PhotoLean.Kasha.probe_criterion_premises_insufficient
#print axioms PhotoLean.Kasha.probe_criterion_general
