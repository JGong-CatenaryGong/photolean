/-
  PhotoLean — theories/goldschmidt/probes/goldschmidt-api-finset-z.lean

  mathlib API calibration for the Goldschmidt theory, dispatch item (e): the `Finset`/`ℤ`
  charge-balance toolkit (plan §5 G2 rows `chargeBalanced_single_iff`, `chargeBalanced_pair_iff`,
  `exists_negative_of_pos`, `exists_compensating_partner`; the `ℚ` analogue of plan §8).

  Run from the repository root:

      proofs/scripts/lake env lean theories/goldschmidt/probes/goldschmidt-api-finset-z.lean

  Lean 4.17.0 + mathlib v4.17.0. The four charge-balance theorems are **complete** kernel-checked
  proofs (no placeholder). Status: 0 error / 0 warning.
-/
import Mathlib

/-! ## (e) the `Finset` toolkit — confirmed signatures (verbatim `#check @`, wraps joined) -/

#check @Finset.sum_eq_zero_iff_of_nonneg
#check @Finset.sum_eq_zero_iff_of_nonpos
#check @Finset.sum_erase_add
#check @Finset.sum_erase_eq_sub
#check @Finset.sum_pos'
#check @Finset.sum_pos
#check @Finset.sum_nonneg
#check @Finset.sum_le_sum
#check @Finset.sum_lt_sum
#check @Finset.sum_sub_distrib
#check @Finset.sum_neg_distrib
#check @Finset.sum_eq_zero_iff
#check @Finset.sum_eq_single
#check @Finset.sum_singleton
#check @Finset.univ_unique
#check @Fintype.sum_unique
#check @Fintype.sum_bool

/-
  **Measured drift (this is the entry's headline):** `Finset.sum_bool` and `Finset.sum_unit`
  do **not** exist in v4.17.0 (`error: unknown constant 'Finset.sum_bool'` /
  `'Finset.sum_unit'`). The working replacements are the *`Fintype`-level* lemmas
  `Fintype.sum_bool` (`∑ b : Bool, f b = f true + f false`) and `Fintype.sum_unique`
  (`∑ x : α, f x = f default`, which covers `Unit`). Note also the `true + false` order of
  `Fintype.sum_bool` — the plan's `chargeBalanced_pair_iff` writes `dz false + dz true`.
-/

/-! ## The single-site and two-site charge rows (plan §5 G2) -/

/-- The authority's charge-rule predicate (`goldschmidt-statement-skeleton.lean:170`,
`PhotoLean/Goldschmidt/Rules.lean`): `ChargeBalanced dz := ∑ i, dz i = 0`. -/
def ChargeBalanced {ι : Type*} [Fintype ι] (dz : ι → ℤ) : Prop := ∑ i, dz i = 0

/-- `chargeBalanced_single_iff` **in the authority's exact signature** (its body is the authority's
`∂`-wrapped sum). Recipe: `rw [ChargeBalanced, Fintype.sum_unique]` — note the replacement for the
nonexistent `Finset.sum_unit`. -/
theorem chargeBalanced_single_iff_authority (dz : ℤ) :
    ChargeBalanced (fun _ : Unit => dz) ↔ dz = 0 := by
  rw [ChargeBalanced, Fintype.sum_unique]

/-- `chargeBalanced_pair_iff` **in the authority's exact signature and printed order**
(`dz false + dz true = 0`). `Fintype.sum_bool` produces the *reversed* order, so the proof needs one
`add_comm`. -/
theorem chargeBalanced_pair_iff_authority (dz : Bool → ℤ) :
    ChargeBalanced dz ↔ dz false + dz true = 0 := by
  rw [ChargeBalanced, Fintype.sum_bool, add_comm]

/-- `chargeBalanced_single_iff` (plan §5) on the raw sum: a `Unit`-indexed charge vector is balanced
iff its single entry vanishes. -/
theorem chargeBalanced_single_iff (dz : ℤ) : (∑ _ : Unit, dz) = 0 ↔ dz = 0 := by
  rw [Fintype.sum_unique]

/-- `chargeBalanced_pair_iff` (plan §5) in the order `Fintype.sum_bool` actually produces. -/
theorem chargeBalanced_pair_iff (dz : Bool → ℤ) :
    (∑ b : Bool, dz b) = 0 ↔ dz true + dz false = 0 := by
  rw [Fintype.sum_bool]

/-- The plan's printed order `dz false + dz true = 0` on the raw sum — same proof plus one
`add_comm`. The authority uses this order via `ChargeBalanced`. -/
theorem chargeBalanced_pair_iff' (dz : Bool → ℤ) :
    (∑ b : Bool, dz b) = 0 ↔ dz false + dz true = 0 := by
  rw [Fintype.sum_bool, add_comm]

/-! ## `exists_negative_of_pos` (plan §5 G2) — **complete proof**

  Statement (settled): for `dz : ι → ℤ` with `[Fintype ι]`,
  `(∑ i, dz i) = 0 → (∃ i, 0 < dz i) → ∃ j, dz j < 0`.

  Recipe (the plan's route, kernel-checked): `by_contra`, then
  `Finset.sum_eq_zero_iff_of_nonneg` on `Finset.univ`, then the positive entry contradicts the
  vanishing sum. No `DecidableEq ι` is needed. -/
theorem exists_negative_of_pos {ι : Type*} [Fintype ι] (dz : ι → ℤ)
    (hsum : ∑ i, dz i = 0) (hpos : ∃ i, 0 < dz i) : ∃ j, dz j < 0 := by
  by_contra h
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ dz i :=
    fun i _ => le_of_not_gt (fun hlt => h ⟨i, hlt⟩)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  obtain ⟨i, hi⟩ := hpos
  have := hz i (Finset.mem_univ i)
  omega

/-- **The authority's exact signature** (`goldschmidt-statement-skeleton.lean:210`): implicit `dz`
and the `ChargeBalanced` wrapper. It follows from the raw-sum form with **no `unfold`** — `def`s are
unfolded during elaboration, so `ChargeBalanced dz` is accepted where `∑ i, dz i = 0` is expected. -/
theorem exists_negative_of_pos_authority {ι : Type*} [Fintype ι] {dz : ι → ℤ}
    (h : ChargeBalanced dz) (hpos : ∃ i, 0 < dz i) : ∃ j, dz j < 0 :=
  exists_negative_of_pos dz h hpos

/-- The same row through the alternative engine `Finset.sum_pos'` (shorter, and the one to prefer
when the sum index is not `Finset.univ`): a nonnegative sum with a positive entry is positive. -/
theorem exists_negative_of_pos_sumpos {ι : Type*} [Fintype ι] (dz : ι → ℤ)
    (hsum : ∑ i, dz i = 0) (hpos : ∃ i, 0 < dz i) : ∃ j, dz j < 0 := by
  by_contra h
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ dz i :=
    fun i _ => le_of_not_gt (fun hlt => h ⟨i, hlt⟩)
  have hpos' : 0 < ∑ i, dz i := by
    refine Finset.sum_pos' hnonneg ?_
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, Finset.mem_univ i, hi⟩
  omega

/-- `exists_negative_of_pos` in `ℚ` — the plan §8 `chargeBalancedQ` analogue. -/
theorem exists_negative_of_pos_rat {ι : Type*} [Fintype ι] (dq : ι → ℚ)
    (hsum : ∑ i, dq i = 0) (hpos : ∃ i, 0 < dq i) : ∃ j, dq j < 0 := by
  by_contra h
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ dq i :=
    fun i _ => le_of_not_gt (fun hlt => h ⟨i, hlt⟩)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  obtain ⟨i, hi⟩ := hpos
  have := hz i (Finset.mem_univ i)
  linarith

/-! ## `exists_compensating_partner` (plan §5 G2) — **complete proof**

  Statement (settled, **the delivered signature carries no `DecidableEq`**): for `dz : ι → ℤ` with
  `[Fintype ι]`, `(∑ i, dz i) = 0 → 0 < dz i → ∃ j, j ≠ i ∧ dz j < 0`.

  The proof internally needs decidable equality (it splits the sum as
  `∑_{j ∈ univ.erase i} dz j = ∑ j, dz j - dz i` via `Finset.sum_erase_eq_sub`, and `Finset.erase`
  needs `DecidableEq ι`), but that instance is obtained **locally** with the `classical` tactic, so it
  does not appear in the theorem's signature. This is the form the statement authority keeps; the
  earlier `[DecidableEq ι]`-carrying variant is recorded below only as an alternative.

  Recipe (kernel-checked): if no `j ≠ i` were negative, `∑_{univ.erase i}` would be `≥ 0`, but
  `Finset.sum_erase_eq_sub` + the vanishing total make it `-dz i < 0`. -/
theorem exists_compensating_partner {ι : Type*} [Fintype ι] (dz : ι → ℤ)
    (hsum : ∑ i, dz i = 0) (i : ι) (hi : 0 < dz i) : ∃ j, j ≠ i ∧ dz j < 0 := by
  classical
  by_contra h
  have hnn : ∀ j ∈ (Finset.univ : Finset ι).erase i, 0 ≤ dz j := by
    intro j hj
    rw [Finset.mem_erase] at hj
    exact le_of_not_gt (fun hlt => h ⟨j, hj.1, hlt⟩)
  have hsum_erase : ∑ j ∈ (Finset.univ : Finset ι).erase i, dz j = -dz i := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hsum]
    ring
  have hnn' := Finset.sum_nonneg hnn
  rw [hsum_erase] at hnn'
  omega

/-- **The authority's exact signature** (`goldschmidt-statement-skeleton.lean:212`): implicit `dz`,
implicit `i`, and the `ChargeBalanced` wrapper — and, as required by the delivered work, **no
`DecidableEq ι`**. Again no `unfold` is needed. -/
theorem exists_compensating_partner_authority {ι : Type*} [Fintype ι] {dz : ι → ℤ}
    (h : ChargeBalanced dz) {i : ι} (hi : 0 < dz i) : ∃ j, j ≠ i ∧ dz j < 0 :=
  exists_compensating_partner dz h i hi

/-- The remaining `Finset` names of the dispatch, in the usage forms the theory needs. -/
example {ι : Type*} [Fintype ι] (dz : ι → ℤ) (h : ∀ i, 0 ≤ dz i) : 0 ≤ ∑ i, dz i :=
  Finset.sum_nonneg (fun i _ => h i)

example {ι : Type*} [Fintype ι] (f g : ι → ℤ) (h : ∀ i, f i ≤ g i) : ∑ i, f i ≤ ∑ i, g i :=
  Finset.sum_le_sum (fun i _ => h i)

example {ι : Type*} [Fintype ι] (f g : ι → ℤ) (h : ∀ i, f i ≤ g i) (i : ι) (hi : f i < g i) :
    ∑ i, f i < ∑ i, g i :=
  Finset.sum_lt_sum (fun i _ => h i) ⟨i, Finset.mem_univ i, hi⟩

example {ι : Type*} [Fintype ι] (f g : ι → ℤ) :
    ∑ i, (f i - g i) = ∑ i, f i - ∑ i, g i := Finset.sum_sub_distrib

example {ι : Type*} [Fintype ι] (f : ι → ℤ) : ∑ i, -f i = -∑ i, f i := Finset.sum_neg_distrib

/-- `Finset.sum_erase_add` is the `+`-shaped twin of `Finset.sum_erase_eq_sub` (it needs the
membership proof explicitly, and `Finset.mem_univ i` supplies it for the full index type). -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℤ) (i : ι) :
    (∑ j ∈ (Finset.univ : Finset ι).erase i, f j) + f i = ∑ j, f j :=
  Finset.sum_erase_add _ _ (Finset.mem_univ i)
