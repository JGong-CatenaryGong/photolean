/-
Kasha milestone — API probe (topic A): `Finset` index surgery for the cascade.

Scope. The K1/K2/K4 cascade rows are `Finset.Icc` / `Finset.range` bookkeeping plus three
big-operator order lemmas.  This probe (i) `#check`s every candidate name, and (ii) kernel-checks
one *worked recipe per row shape* (delivery-shaped goals, not toys): the top split
`Icc (i+1) (N+1)`, the degenerate `Icc (i+1) i` and `Icc 1 0`, the interior split at `M`, the
`range (N+1) ↔ {0} ∪ Icc 1 N` split, the two Markov recursions (K2 #4/#5), the one-sided bounds of
K1 #8/#9/#16/#17, the sum-zero elimination of K2 #13, the relative-leak bound of K3 #17, and the
`specFrac` sum law of K1 #20.

Name note: topic-A's probe was dispatched as `kasha-api-finset.lean`, but that path is occupied by
a **prover_c scratch probe written after this dispatch** (its header says "not a delivered
artifact"); per engine rule 5 (one writer per file) this probe is delivered as
`kasha-api-cascade.lean`, and `proofs/API-NOTES.md` §kasha records the collision.

Plan loci served: §4.2 #7–#21 (K1), §5.1 #1–#6 (K2), §5.2 #13/#22 (K2), §6.2 #17–#18 (K3),
§7.2 #1–#2 (K4), §8.1 (K5a — the ℚ twin uses the same index shapes).

Running:  proofs/scripts/lake env lean theories/kasha/probes/kasha-api-cascade.lean
Status:   0 errors / 0 warnings.
-/
import Mathlib

open scoped BigOperators

set_option autoImplicit false

namespace PhotoLean.Kasha.ProbeCascade

/-! ## Local copies of the K1 definitions (plan §4.1 / statement authority, same bodies) -/

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

noncomputable def specFrac (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ :=
  emitYield rad ic i N / fluoYield rad ic N

structure RateData (rad ic : ℕ → ℝ) (N : ℕ) : Prop where
  decay_pos : ∀ n, n ≤ N → 0 < decay rad ic n
  rad_nonneg : ∀ n, 0 ≤ rad n
  ic_nonneg : ∀ n, 0 ≤ ic n

/-! ## `#check` — candidate names (verbatim output is quoted in `proofs/API-NOTES.md` §kasha) -/

-- NOT in mathlib v4.17.0 (measured; verbatim errors are quoted in `proofs/API-NOTES.md` §kasha,
-- banned list): @Finset.Icc_succ_right, @Finset.Icc_insert_left, @Finset.prod_Icc_succ_bot,
-- @Finset.sum_Icc_succ_bot, @Finset.prod_Icc_consecutive, @Finset.sum_Icc_consecutive,
-- @Finset.Icc_union_Icc_eq_Icc, @Finset.Ico_zero_eq_range.
-- Splitting `Icc a (b+1)` at the top / at the bottom (the names that DO exist):
#check @Finset.Icc_eq_cons_Ico
#check @Finset.Icc_eq_cons_Ioc
#check @Finset.prod_Icc_succ_top
#check @Finset.sum_Icc_succ_top
#check @Finset.prod_Ico_succ_top
#check @Finset.sum_Ico_succ_top
#check @Finset.prod_eq_prod_Ico_succ_bot
#check @Finset.sum_eq_sum_Ico_succ_bot
#check @Finset.prod_Ico_consecutive
#check @Finset.sum_Ico_consecutive
#check @Finset.prod_Ioc_consecutive
#check @Finset.sum_Ioc_consecutive
-- the degenerate intervals `Icc (i+1) i` and `Icc 1 0`, and `range 1`
#check @Finset.Icc_self
#check @Finset.Icc_eq_empty
#check @Finset.Icc_eq_empty_iff
#check @Finset.prod_empty
#check @Finset.sum_empty
#check @Finset.prod_singleton
#check @Finset.sum_singleton
#check @Finset.range_one
#check @Finset.range_succ
#check @Finset.range_add_one
-- `range (N+1)` ↔ `{0} ∪ Icc 1 N` and the `Ico`/`range` translation
#check @Finset.range_eq_Ico
#check @Nat.Ico_zero_eq_range
#check @Nat.range_succ_eq_Icc_zero
#check @Nat.Ico_succ_right
#check @Nat.Icc_eq_range'
#check @Nat.Ico_eq_range'
#check @Finset.sum_range_eq_add_Ico
#check @Finset.prod_range_eq_mul_Ico
#check @Finset.sum_range_succ
#check @Finset.sum_range_succ'
#check @Finset.prod_range_succ
#check @Finset.sum_range_zero
#check @Finset.sum_range_one
-- the interior split at `M`
#check @Finset.Ico_union_Ico_eq_Ico
#check @Finset.prod_union
#check @Finset.sum_union
#check @Finset.disjoint_left
#check @Finset.disjoint_iff_inter_eq_empty
#check @Finset.prod_disjUnion
#check @Finset.sum_disjUnion
#check @Finset.disjUnion
-- big-operator order lemmas
#check @Finset.prod_nonneg
#check @Finset.prod_pos
#check @Finset.prod_le_one'
#check @Finset.prod_le_prod
#check @Finset.sum_nonneg
#check @Finset.sum_le_sum
#check @Finset.sum_eq_zero_iff_of_nonneg
#check @Finset.sum_eq_zero_iff_of_nonpos
#check @Finset.sum_div
#check @Finset.sum_mul
#check @Finset.mul_sum
#check @Finset.sum_congr
#check @Finset.prod_congr
#check @Finset.mem_Icc
#check @Finset.mem_range
#check @Finset.sum_insert
#check @Finset.prod_insert

/-! ## K1 #7/#15/#14 — the degenerate shapes `Icc (i+1) i`, `Icc 1 0`, `range 1` -/

/-- K1 #7 — `Icc (i+1) i` is **empty** (not a singleton): the plan's sketch names `Finset.Icc_self`,
but `cascade i i` carries the lower bound `i+1`, so the usable pair is `Finset.Icc_eq_empty_iff` +
`Finset.prod_empty`. -/
theorem cascade_self (rad ic : ℕ → ℝ) (i : ℕ) : cascade rad ic i i = 1 := by
  unfold cascade
  rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ (i + 1 ≤ i)), Finset.prod_empty]

/-- K1 #7, shortest form: `Finset.Icc_eq_empty_iff` is `@[simp]`, so `simp` closes it. -/
example (rad ic : ℕ → ℝ) (i : ℕ) : cascade rad ic i i = 1 := by simp [cascade]

/-- K1 #15 — `Icc 1 0 = ∅`, so the leak at `N = 0` vanishes. -/
theorem upperYield_zero (rad ic : ℕ → ℝ) : upperYield rad ic 0 = 0 := by
  unfold upperYield
  rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ ((1 : ℕ) ≤ 0)), Finset.sum_empty]

/-- K1 #14 — `range (0+1) = range 1 = {0}` and `cascade 0 0 = 1`. -/
theorem fluoYield_zero (rad ic : ℕ → ℝ) : fluoYield rad ic 0 = radBranch rad ic 0 := by
  unfold fluoYield emitYield
  rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    cascade_self rad ic 0, mul_one]

/-! ## K1 #8/#9/#11/#17 — nonnegativity and the one-bound -/

theorem radBranch_nonneg {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    0 ≤ radBranch rad ic n :=
  div_nonneg (h.rad_nonneg n) (le_of_lt (h.decay_pos n hn))

theorem icBranch_nonneg {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    0 ≤ icBranch rad ic n :=
  div_nonneg (h.ic_nonneg n) (le_of_lt (h.decay_pos n hn))

theorem radBranch_le_one {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    radBranch rad ic n ≤ 1 := by
  rw [radBranch, div_le_one (h.decay_pos n hn), decay]
  linarith [h.ic_nonneg n]

theorem icBranch_le_one {rad ic : ℕ → ℝ} {N n : ℕ} (h : RateData rad ic N) (hn : n ≤ N) :
    icBranch rad ic n ≤ 1 := by
  rw [icBranch, div_le_one (h.decay_pos n hn), decay]
  linarith [h.rad_nonneg n]

-- `h1` is the *lower* bound of the interval and is not consumed by the product bound (`Icc` collapses
-- to `∅` when `i > N`, and the upper bound alone drives `icBranch_le_one`); the linter is off.
set_option linter.unusedVariables false in
theorem cascade_nonneg {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N) (h1 : i ≤ N) :
    0 ≤ cascade rad ic i N := by
  unfold cascade
  exact Finset.prod_nonneg fun j hj => icBranch_nonneg h (Finset.mem_Icc.mp hj).2

set_option linter.unusedVariables false in
theorem cascade_le_one {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N) (h1 : i ≤ N) :
    cascade rad ic i N ≤ 1 := by
  unfold cascade
  -- `Finset.prod_le_one'` is stated for `OrderedCommMonoid`, which ℝ no longer synthetizes in this
  -- toolchain; the two-hypothesis `Finset.prod_le_one` (CommMonoidWithZero + PosMulMono) is the
  -- name that applies.
  exact Finset.prod_le_one (fun j hj => icBranch_nonneg h (Finset.mem_Icc.mp hj).2)
    (fun j hj => icBranch_le_one h (Finset.mem_Icc.mp hj).2)

theorem emitYield_nonneg {rad ic : ℕ → ℝ} {N i : ℕ} (h : RateData rad ic N) (h1 : i ≤ N) :
    0 ≤ emitYield rad ic i N := by
  unfold emitYield
  exact mul_nonneg (radBranch_nonneg h h1) (cascade_nonneg h h1)

theorem upperYield_nonneg {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    0 ≤ upperYield rad ic N := by
  unfold upperYield
  exact Finset.sum_nonneg fun i hi => emitYield_nonneg h (Finset.mem_Icc.mp hi).2

/-! ## K2 #1/#2/#3 — the top split `Icc (i+1) (N+1)` -/

theorem cascade_succ {rad ic : ℕ → ℝ} {i N : ℕ} (h : i ≤ N) :
    cascade rad ic i (N + 1) = icBranch rad ic (N + 1) * cascade rad ic i N := by
  unfold cascade
  rw [Finset.prod_Icc_succ_top (f := fun j => icBranch rad ic j) (by omega : i + 1 ≤ N + 1)]
  ring

theorem emitYield_succ {rad ic : ℕ → ℝ} {i N : ℕ} (h : i ≤ N) :
    emitYield rad ic i (N + 1) = icBranch rad ic (N + 1) * emitYield rad ic i N := by
  unfold emitYield
  rw [cascade_succ h]
  ring

theorem emitYield_succ_self (rad ic : ℕ → ℝ) (N : ℕ) :
    emitYield rad ic (N + 1) (N + 1) = radBranch rad ic (N + 1) := by
  unfold emitYield
  rw [cascade_self rad ic (N + 1), mul_one]

/-! ## K1 #13 — the `range (N+1) ↔ {0} ∪ Icc 1 N` split -/

theorem fluoYield_eq_low_add_upper (rad ic : ℕ → ℝ) (N : ℕ) :
    fluoYield rad ic N = emitYield rad ic 0 N + upperYield rad ic N := by
  unfold fluoYield upperYield
  rw [Finset.sum_range_eq_add_Ico (f := fun i => emitYield rad ic i N) (Nat.succ_pos N),
    Nat.Ico_succ_right]

/-! ## K2 #4/#5 — the two Markov recursions -/

theorem fluoYield_succ (rad ic : ℕ → ℝ) (N : ℕ) :
    fluoYield rad ic (N + 1) =
      radBranch rad ic (N + 1) + icBranch rad ic (N + 1) * fluoYield rad ic N := by
  have hterm : ∀ i ∈ Finset.range (N + 1),
      emitYield rad ic i (N + 1) = icBranch rad ic (N + 1) * emitYield rad ic i N :=
    fun i hi => emitYield_succ (by rw [Finset.mem_range] at hi; omega)
  unfold fluoYield
  rw [Finset.sum_range_succ, Finset.sum_congr rfl hterm, Finset.mul_sum, emitYield_succ_self]
  ring

theorem upperYield_succ (rad ic : ℕ → ℝ) (N : ℕ) :
    upperYield rad ic (N + 1) =
      radBranch rad ic (N + 1) + icBranch rad ic (N + 1) * upperYield rad ic N := by
  have hterm : ∀ i ∈ Finset.Icc 1 N,
      emitYield rad ic i (N + 1) = icBranch rad ic (N + 1) * emitYield rad ic i N :=
    fun i hi => emitYield_succ (Finset.mem_Icc.mp hi).2
  unfold upperYield
  rw [Finset.sum_Icc_succ_top (f := fun i => emitYield rad ic i (N + 1)) (by omega : 1 ≤ N + 1),
    Finset.sum_congr rfl hterm, Finset.mul_sum, emitYield_succ_self]
  ring

/-! ## K2 #13 — sum-zero elimination (`upperYield_eq_zero_iff`) -/

theorem upperYield_eq_zero_iff {rad ic : ℕ → ℝ} {N : ℕ} (h : RateData rad ic N) :
    upperYield rad ic N = 0 ↔ ∀ i, 1 ≤ i → i ≤ N → emitYield rad ic i N = 0 := by
  unfold upperYield
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i hi => emitYield_nonneg h (Finset.mem_Icc.mp hi).2)]
  constructor
  · intro h' i h1 h2
    exact h' i (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  · intro h' i hi
    exact h' i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2

/-! ## K3 #17 — the uniform-branch relative leak bound -/

theorem leak_le_of_radBranch_le {rad ic : ℕ → ℝ} {N : ℕ} {θ : ℝ} (h : RateData rad ic N)
    (hθ : ∀ i, 1 ≤ i → i ≤ N → radBranch rad ic i ≤ θ) :
    upperYield rad ic N ≤ θ * ∑ i ∈ Finset.Icc 1 N, cascade rad ic i N := by
  have hstep : ∀ i ∈ Finset.Icc 1 N, emitYield rad ic i N ≤ θ * cascade rad ic i N := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    unfold emitYield
    exact mul_le_mul_of_nonneg_right (hθ i h1 h2) (cascade_nonneg h h2)
  unfold upperYield
  calc ∑ i ∈ Finset.Icc 1 N, emitYield rad ic i N
      ≤ ∑ i ∈ Finset.Icc 1 N, θ * cascade rad ic i N := Finset.sum_le_sum hstep
    _ = θ * ∑ i ∈ Finset.Icc 1 N, cascade rad ic i N := (Finset.mul_sum ..).symm

/-! ## K1 #20 — `specFrac_sum` (the `Finset.sum_div` usage form) -/

theorem specFrac_sum {rad ic : ℕ → ℝ} {N : ℕ} (hF : fluoYield rad ic N ≠ 0) :
    ∑ i ∈ Finset.range (N + 1), specFrac rad ic i N = 1 := by
  unfold specFrac
  rw [← Finset.sum_div]
  exact div_self hF

/-! ## K4 #1 — the interior split at `M` (the collapse identity of `cascade`) -/

theorem cascade_compose {rad ic : ℕ → ℝ} {i M N : ℕ} (h1 : i ≤ M) (h2 : M ≤ N) :
    cascade rad ic i N = cascade rad ic i M * cascade rad ic M N := by
  have hset : Finset.Icc (i + 1) N = Finset.Icc (i + 1) M ∪ Finset.Icc (M + 1) N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc (i + 1) M) (Finset.Icc (M + 1) N) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  unfold cascade
  rw [hset, Finset.prod_union hdisj]

end PhotoLean.Kasha.ProbeCascade
