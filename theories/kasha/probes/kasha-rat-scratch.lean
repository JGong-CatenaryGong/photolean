/-
Calibration log for the Kasha ℚ verdict layer (owner `prover_c`) — companion to the deliverable
`theories/kasha/probes/kasha-rat-probe.lean` (task K-PROBE-2, plan §8.1/§8.2).

This file is a scratch artifact: it lives under `theories/kasha/probes/` (outside `SOURCE_DIRS`)
and must compile at 0 error (`proofs/scripts/lake env lean <this file>`). It holds the *negative*
measurements in comment form and the positive micro-recipes as live theorems, so that the claims in
the probe's findings block are reproducible.

**Measured negatives (raw kernel output, reduced to the decisive lines).**

1. `by decide` on an equality row — fails:

     tactic 'decide' failed for proposition
       fluoYieldQ (twoRad 1 1) (twoIc 0 100) 1 = 1
     since its 'Decidable' instance
       instDecidableEqRat (fluoYieldQ (twoRad 1 1) (twoIc 0 100) 1) 1
     did not reduce to 'isTrue' or 'isFalse'.

2. `by decide` on a row stated through `KashaWithinQ` — fails at elaboration, before any reduction:
   the `Prop`-valued definition gets no `Decidable` instance,

     failed to synthesize Decidable (KashaWithinQ (twoRad 1 1) (twoIc 0 100) (1 / 100) 1)

3. `decide` after unfolding every definition — fails in the reduction of the comparison:

     ... its 'Decidable' instance ... .instDecidableLe ... did not reduce to 'isTrue' or 'isFalse'.
     After unfolding the instances 'instDecidableEqBool', 'Bool.decEq', 'Int.decLt',
     'Rat.instDecidableLe' and 'Int.decNonneg✝', reduction got stuck at the 'Decidable' instance
       ... .blt ... , false

   (the `Rat.blt` → `Int.decNonneg` trap of `proofs/API-NOTES.md` §kasha). Control: the
   division-free comparison `(1 : ℚ) < 3` *is* closed by `decide` (kept live below).

4. `simp only` with `Finset.Icc_eq_empty` does **not** reduce an empty `Finset.Icc (i+1) i` when the
   product body is a division (`simp made no progress`); the same `simp only` on a polynomial body
   does. The `norm_num` route is unaffected, and for symbolic `rad ic` the explicit
   `rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ (i + 1 ≤ i)), Finset.prod_empty]` is the reliable
   one (kept live below as `empty_Icc_route`).

**Measured cost of the data formulations** (`set_option trace.profiler true`, `N = 2` rows, one
elaboration each, same machine and same recipe): skeleton `if`-ladder 0.51 s (fluo) / 0.32 s (leak);
`List.getD` ladder `fun n => l.getD n 0` 0.59 s / 0.35 s; `![…]`-literal ladder
`fun n => if h : n < 3 then v ⟨n, h⟩ else 0` with `v : Fin 3 → ℚ` 0.46 s / 0.28 s. All three close;
the spread is ±10 % and `norm_num`'s rational arithmetic dominates. No change to the statement
authority is warranted. The three formulations are kept live below under
`/-! ### data-formulation rows -/`; uncomment the `trace.profiler` option to re-measure.
-/
import Mathlib

open scoped BigOperators

set_option autoImplicit false

-- set_option trace.profiler true

namespace PhotoLean

namespace Kasha

namespace Scratch

/-! ### the plan §8.1 definitions (verbatim) and the plan §8.2 ladders -/

def decayQ (rad ic : ℕ → ℚ) (n : ℕ) : ℚ := rad n + ic n

def radBranchQ (rad ic : ℕ → ℚ) (n : ℕ) : ℚ := rad n / decayQ rad ic n

def icBranchQ (rad ic : ℕ → ℚ) (n : ℕ) : ℚ := ic n / decayQ rad ic n

def cascadeQ (rad ic : ℕ → ℚ) (i N : ℕ) : ℚ := ∏ j ∈ Finset.Icc (i + 1) N, icBranchQ rad ic j

def emitYieldQ (rad ic : ℕ → ℚ) (i N : ℕ) : ℚ := radBranchQ rad ic i * cascadeQ rad ic i N

def fluoYieldQ (rad ic : ℕ → ℚ) (N : ℕ) : ℚ := ∑ i ∈ Finset.range (N + 1), emitYieldQ rad ic i N

def upperYieldQ (rad ic : ℕ → ℚ) (N : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 N, emitYieldQ rad ic i N

def twoRad (r0 r1 : ℚ) : ℕ → ℚ := fun n => if n = 0 then r0 else if n = 1 then r1 else 0

def twoIc (i0 i1 : ℚ) : ℕ → ℚ := fun n => if n = 0 then i0 else if n = 1 then i1 else 0

def threeRad (r0 r1 r2 : ℚ) : ℕ → ℚ :=
  fun n => if n = 0 then r0 else if n = 1 then r1 else if n = 2 then r2 else 0

def threeIc (i0 i1 i2 : ℚ) : ℕ → ℚ :=
  fun n => if n = 0 then i0 else if n = 1 then i1 else if n = 2 then i2 else 0

/-! ### positive controls -/

/-- `decide` is reliable on division-free ℚ literals (control for negative 1). -/
theorem decide_control : (1 : ℚ) < 3 := by decide

/-- The `N = 1` row with the uniform recipe (definitions + seven finset lemmas). -/
theorem uniform_recipe_one : fluoYieldQ (twoRad 1 1) (twoIc 0 100) 1 = 1 := by
  norm_num [fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ, decayQ, twoRad, twoIc,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- The `N = 2` row, whose cascade carries the non-singleton bound `Finset.Icc 1 2`. -/
theorem uniform_recipe_two : fluoYieldQ (threeRad 1 1 1) (threeIc 1 1 1) 2 = 7 / 8 := by
  norm_num [fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ, decayQ, threeRad, threeIc,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- The reliable empty-`Icc` route for symbolic ladders (negative 4). -/
theorem empty_Icc_route (rad ic : ℕ → ℚ) : cascadeQ rad ic 1 1 = 1 := by
  unfold cascadeQ
  rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ ((1 : ℕ) + 1 ≤ 1)), Finset.prod_empty]

/-! ### data-formulation rows (timing comparison; see the header) -/

/-- `List`-access ladder: `fun n => l.getD n 0`. -/
def listRad (l : List ℚ) : ℕ → ℚ := fun n => l.getD n 0

/-- `List`-access ladder for the nonradiative rates. -/
def listIc (l : List ℚ) : ℕ → ℚ := fun n => l.getD n 0

/-- `![…]`-literal ladder: `Fin 3 → ℚ` access with a fallback. -/
def finRad (v : Fin 3 → ℚ) : ℕ → ℚ := fun n => if h : n < 3 then v ⟨n, h⟩ else 0

/-- `![…]`-literal ladder for the nonradiative rates. -/
def finIc (v : Fin 3 → ℚ) : ℕ → ℚ := fun n => if h : n < 3 then v ⟨n, h⟩ else 0

theorem data_if : fluoYieldQ (threeRad 1 1 1) (threeIc 1 1 1) 2 = 7 / 8 := by
  norm_num [fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ, decayQ, threeRad, threeIc,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

theorem data_list : fluoYieldQ (listRad [1, 1, 1]) (listIc [1, 1, 1]) 2 = 7 / 8 := by
  norm_num [fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ, decayQ, listRad, listIc,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

theorem data_fin : fluoYieldQ (finRad ![1, 1, 1]) (finIc ![1, 1, 1]) 2 = 7 / 8 := by
  norm_num [fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ, decayQ, finRad, finIc,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

end Scratch

end Kasha

end PhotoLean
