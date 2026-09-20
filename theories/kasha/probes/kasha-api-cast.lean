/-
Kasha milestone — API probe (topic E): the ℚ → ℝ cast bridges of K5a (`PhotoLean/Kasha/RatModel.lean`).

Scope. Every K5a definition has an ℝ twin in K1, and every cast bridge is one of the seven rows
`decayQ_cast`, `radBranchQ_cast`, `icBranchQ_cast`, `cascadeQ_cast`, `emitYieldQ_cast`,
`fluoYieldQ_cast`, `upperYieldQ_cast`, plus the predicate transfer `kashaWithinQ_iff_cast`.  This
probe kernel-checks all eight in the delivery shape, and calibrates the `Rat.cast_*` family
(including the `Rat.cast_inj` `α`-argument trap and the `Rat.cast_sum`/`Rat.cast_prod` big-operator
lemmas that make the `cascadeQ` cast a two-liner).

Instance arithmetic (`twoRad`/`twoIc`/`threeRad`/`threeIc`, the verdict rows I1–I14) is **not**
duplicated here: it belongs to the `#norm_num`/`#decide` boundary recorded in the Marcus round and a
separate scratch probe; only the generic boundary is re-measured here.

Plan loci served: §8.1 (K5a `RatModel.lean`), §4.1/§5.1 (the ℝ twins), §7.2 #3–#6 (K4's effective
data, same recipe).

Running:  proofs/scripts/lake env lean theories/kasha/probes/kasha-api-cast.lean
Status:   0 errors / 0 warnings.
-/
import Mathlib

open scoped BigOperators

set_option autoImplicit false

namespace PhotoLean.Kasha.ProbeCast

/-! ## Local copies of the K5a definitions and their ℝ twins (same bodies as the skeleton) -/

def decayQ (rad ic : ℕ → ℚ) (n : ℕ) : ℚ := rad n + ic n
def radBranchQ (rad ic : ℕ → ℚ) (n : ℕ) : ℚ := rad n / decayQ rad ic n
def icBranchQ (rad ic : ℕ → ℚ) (n : ℕ) : ℚ := ic n / decayQ rad ic n
def cascadeQ (rad ic : ℕ → ℚ) (i N : ℕ) : ℚ := ∏ j ∈ Finset.Icc (i + 1) N, icBranchQ rad ic j
def emitYieldQ (rad ic : ℕ → ℚ) (i N : ℕ) : ℚ := radBranchQ rad ic i * cascadeQ rad ic i N
def fluoYieldQ (rad ic : ℕ → ℚ) (N : ℕ) : ℚ := ∑ i ∈ Finset.range (N + 1), emitYieldQ rad ic i N
def upperYieldQ (rad ic : ℕ → ℚ) (N : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 N, emitYieldQ rad ic i N
def KashaWithinQ (rad ic : ℕ → ℚ) (tol : ℚ) (N : ℕ) : Prop :=
  upperYieldQ rad ic N ≤ tol * fluoYieldQ rad ic N

noncomputable def decay (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := rad n + ic n
noncomputable def radBranch (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := rad n / decay rad ic n
noncomputable def icBranch (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := ic n / decay rad ic n
noncomputable def cascade (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (i + 1) N, icBranch rad ic j
noncomputable def emitYield (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ :=
  radBranch rad ic i * cascade rad ic i N
noncomputable def fluoYield (rad ic : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), emitYield rad ic i N
noncomputable def upperYield (rad ic : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 N, emitYield rad ic i N
def KashaWithin (rad ic : ℕ → ℝ) (tol : ℝ) (N : ℕ) : Prop :=
  upperYield rad ic N ≤ tol * fluoYield rad ic N

/-! ## `#check` — the `Rat.cast_*` family (exact signatures are quoted in `proofs/API-NOTES.md`) -/

#check @Rat.cast_add
#check @Rat.cast_sub
#check @Rat.cast_mul
#check @Rat.cast_div
#check @Rat.cast_inv
#check @Rat.cast_neg
#check @Rat.cast_pow
#check @Rat.cast_zero
#check @Rat.cast_one
#check @Rat.cast_ofNat
#check @Rat.cast_natCast
#check @Rat.cast_le
#check @Rat.cast_lt
#check @Rat.cast_pos
#check @Rat.cast_nonneg
#check @Rat.cast_nonpos
#check @Rat.cast_ne_zero
#check @Rat.cast_eq_zero
#check @Rat.cast_inj
#check @Rat.cast_injective
#check @Rat.cast_sum
#check @Rat.cast_prod
#check @Rat.cast_list_sum
#check @Rat.cast_multiset_prod
#check @Rat.castHom

/-! ## K5a cast bridges — one worked recipe per definition (all eight rows) -/

theorem decayQ_cast (rad ic : ℕ → ℚ) (n : ℕ) :
    ((decayQ rad ic n : ℚ) : ℝ) = decay (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) n := by
  unfold decayQ decay
  push_cast
  ring

theorem radBranchQ_cast (rad ic : ℕ → ℚ) (n : ℕ) :
    ((radBranchQ rad ic n : ℚ) : ℝ)
      = radBranch (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) n := by
  unfold radBranchQ radBranch
  rw [Rat.cast_div, decayQ_cast]

theorem icBranchQ_cast (rad ic : ℕ → ℚ) (n : ℕ) :
    ((icBranchQ rad ic n : ℚ) : ℝ)
      = icBranch (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) n := by
  unfold icBranchQ icBranch
  rw [Rat.cast_div, decayQ_cast]

/-- The cascade cast: `Rat.cast_prod` (a `[simp, norm_cast]` big-operator lemma) plus the
pointwise `icBranchQ_cast` — no induction, no `Finset.prod_bij`. -/
theorem cascadeQ_cast (rad ic : ℕ → ℚ) (i N : ℕ) :
    ((cascadeQ rad ic i N : ℚ) : ℝ)
      = cascade (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) i N := by
  unfold cascadeQ cascade
  rw [Rat.cast_prod]
  exact Finset.prod_congr rfl fun j _ => icBranchQ_cast rad ic j

theorem emitYieldQ_cast (rad ic : ℕ → ℚ) (i N : ℕ) :
    ((emitYieldQ rad ic i N : ℚ) : ℝ)
      = emitYield (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) i N := by
  unfold emitYieldQ emitYield
  rw [Rat.cast_mul, radBranchQ_cast, cascadeQ_cast]

/-- The total-yield cast: `Rat.cast_sum` plus the pointwise `emitYieldQ_cast`. -/
theorem fluoYieldQ_cast (rad ic : ℕ → ℚ) (N : ℕ) :
    ((fluoYieldQ rad ic N : ℚ) : ℝ)
      = fluoYield (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) N := by
  unfold fluoYieldQ fluoYield
  rw [Rat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => emitYieldQ_cast rad ic i N

theorem upperYieldQ_cast (rad ic : ℕ → ℚ) (N : ℕ) :
    ((upperYieldQ rad ic N : ℚ) : ℝ)
      = upperYield (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) N := by
  unfold upperYieldQ upperYield
  rw [Rat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => emitYieldQ_cast rad ic i N

/-- `kashaWithinQ_iff_cast` (K5a): the predicate transfer is three rewrites plus one `↔` —
the two ℝ-side yields back to casts (`← upperYieldQ_cast`, `← fluoYieldQ_cast`), the product back to
a cast (`← Rat.cast_mul`), and then `Rat.cast_le` **with the field given explicitly**
(`K := ℝ`); the bare `rw [← Rat.cast_le]` is stuck on `LinearOrderedField ?m` because the ℚ-side
comparison it must produce has an undetermined field. -/
theorem kashaWithinQ_iff_cast {rad ic : ℕ → ℚ} {tol : ℚ} {N : ℕ} :
    KashaWithinQ rad ic tol N ↔
      KashaWithin (fun k => (rad k : ℝ)) (fun k => (ic k : ℝ)) (tol : ℝ) N := by
  unfold KashaWithinQ KashaWithin
  rw [← upperYieldQ_cast, ← fluoYieldQ_cast, ← Rat.cast_mul]
  exact (Rat.cast_le (K := ℝ)).symm

/-! ## The `Rat.cast_*` usage forms the bridge cannot avoid -/

/-- `Rat.cast_le` / `Rat.cast_lt` are **iff** lemmas: they move a comparison in either direction.
With an explicit field they are total: `Rat.cast_le (K := ℝ)`. -/
theorem cast_le_usage {p q : ℚ} : (p : ℝ) ≤ (q : ℝ) ↔ p ≤ q := Rat.cast_le (K := ℝ)

/-- `Rat.cast_inj` needs its target field **explicit**, otherwise the `CharZero α` instance search
is stuck (verbatim error of the Marcus round: `typeclass instance problem is stuck … CharZero ?m`).
The usable form is `(Rat.cast_inj (α := ℝ)).mp`. -/
theorem cast_inj_usage {p q : ℚ} (h : (p : ℝ) = (q : ℝ)) : p = q := (Rat.cast_inj (α := ℝ)).mp h

/-- The `push_cast` route for a `decay`-shaped equality: `unfold …; push_cast; ring` — `push_cast`
alone does not close it (the Marcus-round F-4 lesson). -/
example (rad ic : ℕ → ℚ) (n : ℕ) :
    ((decayQ rad ic n : ℚ) : ℝ) = (rad n : ℝ) + (ic n : ℝ) := by
  unfold decayQ
  push_cast
  ring

/-- The generic ℚ decision boundary, re-measured: integer literals are `decide`-able… -/
example : (1 : ℚ) < 3 := by decide

/-- …while `/`-bearing literals are closed by `norm_num`, not `decide` (`Rat.blt` gets stuck at
`Int.decNonneg`; the verbatim `decide` failure is quoted in `proofs/API-NOTES.md` §kasha). -/
example : (3 / 4 : ℚ) < 1 := by norm_num

example : ¬ ((1 : ℚ) < 3 / 4) := by norm_num

end PhotoLean.Kasha.ProbeCast
