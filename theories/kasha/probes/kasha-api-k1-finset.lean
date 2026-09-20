/-
API calibration probe for the K1 description layer (`PhotoLean/Kasha/Basic.lean`), owner prover_a.

Every name below is a candidate for the index/order/arithmetic toolkit of the K1 theorems. The
file records which names the kernel of this toolchain (Lean 4.17.0 + mathlib v4.17.0) accepts, so
that no proof guesses a name. Calibration log: `proofs/API-NOTES.md` §kasha (the log itself is
maintained by api_researcher; the names calibrated here are reported in the K1 round record of
`proofs/EXPERIENCE.md`).

Verified accepted (verbatim `#check` output of the probe run):

  Finset.Icc_eq_empty          ¬a ≤ b → Finset.Icc a b = ∅        (K1 cascade_self)
  Finset.Icc_eq_empty_iff      Finset.Icc a b = ∅ ↔ ¬a ≤ b
  Finset.Icc_self              Finset.Icc a a = {a}
  Finset.sum_range_one         ∑ k ∈ Finset.range 1, f k = f 0    (K1 fluoYield_zero)
  Finset.sum_insert            a ∉ s → ∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x
  Finset.prod_insert           a ∉ s → ∏ x ∈ insert a s, f x = f a * ∏ x ∈ s, f x
  Finset.mem_Icc / mem_range   membership characterizations
  Finset.sum_Icc_succ_top / prod_Icc_succ_top  (K2 index surgery: Icc a (b+1) splits at the top)
  Finset.sum_nonneg / prod_nonneg              (K1 fluoYield_nonneg, cascade_nonneg)
  Finset.prod_le_one           (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, f i ≤ 1) → ∏ i ∈ s, f i ≤ 1
  Finset.sum_div               (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a   (K1 specFrac_sum; use ←)
  div_nonneg / add_div / sub_div / div_self / div_le_iff₀
  mul_le_of_le_one_right / mul_nonneg / lt_of_le_of_ne / Nat.le_of_lt_succ

Drift / absence measured here:

  Finset.Icc_succ_right — **unknown constant** in this toolchain. The K2 recursion
  (`cascade_succ`) must split `Finset.Icc (i+1) (N+1)` at the top with
  `Finset.prod_Icc_succ_top` (and `Finset.sum_Icc_succ_top` for sums), or build the split by hand.

Recipe measured on the K1 classifier rows (see `PhotoLean/Kasha/Basic.lean`):

  * forward direction of an `if`-cascade characterization on a hypothesis: `unfold kashaZone at hz;
    split_ifs at hz with h1 h2` — the branches whose generated equality is `Ctor₁ = Ctor₂` for
    distinct constructors are discharged by the case split itself, so a single `exact h1` closes
    the survivor (writing three bullets reports `no goals to be solved`);
  * backward direction: `unfold kashaZone; exact if_pos hr` (the guard proof comes from the
    characterization itself); `rw [if_neg …, if_pos …]` is the two-guard variant used for
    `kashaZone_eq_withinTol_iff`.

The probe is a `#check` file: it lives outside `SOURCE_DIRS` (`PhotoLean`), like the statement
skeleton, so the strict scan of the delivered tree does not cover it.
-/
import Mathlib

open scoped BigOperators

-- index lemmas for the ladder sums/products
#check @Finset.Icc_eq_empty
#check @Finset.Icc_eq_empty_iff
#check @Finset.Icc_self
#check @Finset.sum_range_one
#check @Finset.sum_range_succ
#check @Finset.sum_insert
#check @Finset.prod_insert
#check @Finset.mem_Icc
#check @Finset.mem_range
#check @Finset.sum_Icc_succ_top
#check @Finset.prod_Icc_succ_top

-- order lemmas for sums and products of probabilities
#check @Finset.sum_nonneg
#check @Finset.prod_nonneg
#check @Finset.prod_le_one
#check @Finset.prod_le_one'
#check @Finset.sum_div
#check @Finset.sum_eq_zero_iff_of_nonneg

-- field / order lemmas
#check @div_nonneg
#check @add_div
#check @sub_div
#check @div_self
#check @div_le_iff₀
#check @div_lt_iff₀
#check @lt_div_iff₀
#check @mul_le_of_le_one_right
#check @mul_le_of_le_one_left
#check @mul_nonneg
#check @lt_of_le_of_ne
#check @Nat.le_of_lt_succ
#check @Nat.zero_le
