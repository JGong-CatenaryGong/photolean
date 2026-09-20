/-
 theories/kasha/probes/kasha-api-risk.lean

 API calibration probe for the Sprint-0 risk probe
 (`theories/kasha/probes/kasha-risk-probe.lean`, task K-PROBE-1, rows 1-12). It calibrates the
 mathlib names those rows need and carries one kernel-checked `example` per risky recipe, so that no
 name in the risk probe is guessed.

 Findings for `proofs/API-NOTES.md` (leaf owner: api_researcher; recorded here as probe evidence,
 not written into the log by this role):

 * `Finset.sum_Icc_succ_top` / `Finset.prod_Icc_succ_top` exist with the exact split signatures;
   `Finset.sum_Icc_succ_bot`, `Finset.prod_Icc_succ_bot` and `Finset.sum_Icc_eq_sum_range` do NOT.
 * `Finset.sum_eq_zero_iff_of_nonneg`, `Finset.sum_pos'`, `Finset.sum_nonneg`, `Finset.prod_pos`,
   `Finset.prod_nonneg`, `Finset.prod_eq_one` exist; `Finset.prod_pos_iff_of_pos` does NOT.
 * `Real.log_le_iff_le_exp`, `Real.le_log_iff_exp_le`, `Real.log_le_log_iff`, `Real.log_exp`,
   `Real.exp_log`, `Real.log_div`, `Real.log_mul`, `Real.exp_pos`, `Real.exp_le_exp` all exist with
   the signatures the Marcus bridge row (risk row 10) uses.
 * `neg_le_neg_iff : -a ≤ -b ↔ b ≤ a` and `one_div_div : 1 / (a / b) = b / a` exist and are the two
   rewrites that turn the Marcus step into a `rw`-only chain (`risk_kashaWithin_one_marcus`).
 * `inv_le_inv_of_le` is deprecated (use `inv_anti₀`); `div_le_iff` / `le_div_iff` are deprecated
   (use `div_le_iff₀` / `le_div_iff₀`). None of the three is used by the risk probe.
 * `linter.unusedVariables` DOES warn about a theorem hypothesis that is not consumed by the proof
   (§6): rows that must keep an unconsumed `RateData` hypothesis for statement fidelity need a local
   `set_option linter.unusedVariables false in`, the `bep-risk-probe.lean` precedent.

 Tactic facts measured while building the risk probe (all reproduced in §5):
 * `field_simp` may close the goal by itself, after which a following `ring` errors with
   "no goals to be solved"; `field_simp` + `try ring` is the safe tail.
 * The numeral rewrite `rw [show (2 : ℕ) = 1 + 1 from rfl]` can fail with "motive is not type
   correct" on a goal that also contains real literals (`3 / 4`); computing through a
   `have h := <recursion> … ; rw [prev] at h; norm_num […] at h; exact h` chain avoids it.
 * `linarith` does not close `-Real.log K ≤ -(barrier lam x) / (kB*T) ↔ barrier lam x / (kB*T) ≤
   Real.log K` when the two sides carry a nested division (risk row 10); the `rw` chain
   `show -(barrier lam x) / (kB*T) = -(barrier lam x / (kB*T)) from by ring` + `exact
   neg_le_neg_iff` does.
 * The `if`-chain classifier of risk row 11 needs the `if` reduction lemmas in a `simp only` set;
   plain `simp [<defs>]` reduces `1 = 0` and the `if` in one pass.

 This is a probe, not a deliverable: it lives outside `SOURCE_DIRS`, it contains no unproved
 placeholder and no custom axiomatic declaration.
 Running:  proofs/scripts/lake env lean theories/kasha/probes/kasha-api-risk.lean
-/
import Mathlib

open scoped BigOperators

namespace PhotoLean.Kasha.ApiRisk

/-! ## 1. Interval splits of `Finset.range` / `Finset.Icc` -/

#check @Finset.sum_range_succ
#check @Finset.sum_range_succ'
#check @Finset.sum_Icc_succ_top
#check @Finset.prod_Icc_succ_top
#check @Finset.sum_Ico_succ_top
#check @Finset.sum_Ico_eq_sum_range
#check @Finset.sum_insert
#check @Finset.prod_insert
#check @Finset.Icc_eq_empty_iff
#check @Finset.Icc_self
#check @Finset.sum_singleton
#check @Finset.prod_singleton
#check @Finset.sum_congr
#check @Finset.mul_sum
#check @Finset.sum_mul
#check @Finset.sum_eq_zero

/-! ## 2. Order lemmas on sums and products -/

#check @Finset.sum_nonneg
#check @Finset.sum_pos
#check @Finset.sum_pos'
#check @Finset.sum_eq_zero_iff_of_nonneg
#check @Finset.prod_pos
#check @Finset.prod_nonneg
#check @Finset.prod_eq_one
#check @Finset.prod_le_one
#check @Finset.sum_le_sum
#check @Finset.prod_le_prod

/-! ## 3. `Real.exp` / `Real.log` monotonicity (risk row 10) -/

#check @Real.log_le_iff_le_exp
#check @Real.le_log_iff_exp_le
#check @Real.log_le_log_iff
#check @Real.log_exp
#check @Real.exp_log
#check @Real.log_inv
#check @Real.log_div
#check @Real.log_mul
#check @Real.log_pos
#check @Real.exp_pos
#check @Real.exp_le_exp

/-! ## 4. Division, order and the two rewrites of the Marcus chain -/

#check @div_le_iff₀
#check @le_div_iff₀
#check @div_le_div_iff₀
#check @div_eq_zero_iff
#check @div_nonneg
#check @div_pos
#check @div_ne_zero
#check @mul_pos
#check @mul_le_mul_of_nonneg_right
#check @mul_le_mul_of_nonneg_left
#check @div_self
#check @one_div_div
#check @neg_le_neg_iff
#check @mul_div_assoc
#check @div_div
#check @if_true
#check @if_false

/-! ## 5. Kernel-checked recipes -/

/-- The risk-row-1 split: no hypothesis needed. `ext` + `omega` identifies `range (N+1)` with
`insert 0 (Icc 1 N)`, then `Finset.sum_insert` splits the sum. -/
example (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), f i) = f 0 + ∑ i ∈ Finset.Icc 1 N, f i := by
  have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp)]

/-- The risk-row-3 split: `Icc 1 (N+1) = insert (N+1) (Icc 1 N)`. -/
example (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.Icc 1 (N + 1), f i) = f (N + 1) + ∑ i ∈ Finset.Icc 1 N, f i := by
  have hset : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp [Finset.mem_Icc])]

/-- The risk-row-2/4 product step (`Finset.prod_Icc_succ_top`, multiplicative side). -/
example (g : ℕ → ℝ) (N : ℕ) :
    (∏ j ∈ Finset.Icc 1 (N + 1), g j) = (∏ j ∈ Finset.Icc 1 N, g j) * g (N + 1) :=
  Finset.prod_Icc_succ_top (by omega) g

/-- The risk-row-10 logarithm step: `1/K ≤ exp y` is equivalent to `log (1/K) ≤ y`, and
`log (1/K) = -log K`. -/
example {K y : ℝ} (hK : 0 < K) : 1 / K ≤ Real.exp y ↔ -Real.log K ≤ y := by
  rw [← Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < 1 / K),
    Real.log_div one_ne_zero (ne_of_gt hK), Real.log_one]
  ring_nf

/-- The risk-row-10 fix for the `linarith` failure: push the negation outside the division, then
`neg_le_neg_iff` is the whole step. -/
example {b kT L : ℝ} (h : -L ≤ -b / kT) : b / kT ≤ L := by
  rw [show -b / kT = -(b / kT) from by ring] at h
  exact neg_le_neg_iff.mp h

/-- `field_simp` may already close the goal; `try ring` is then the safe tail (a bare `ring` errors
with "no goals to be solved"). -/
example (x : ℝ) (hx : x ≠ 0) : x / x = 1 := by
  field_simp
  try ring

/-- `induction` on `N` with hypotheses that depend on `N` in context: Lean 4 reverts them, so the
induction hypothesis is a function of the corresponding hypothesis. Risk rows 4 and 5
(`cascade_add_upperYield`, `kashaRule_iff_rad_zero`) rely on this. -/
example (P : ℕ → Prop) (n : ℕ) (h : P n) : True := by
  induction n with
  | zero => trivial
  | succ n ih => trivial

/-- `split_ifs` on a three-way `if`-chain classifier (risk row 11 recipe): the constructor-inequality
branches close by `noConfusion` (`intro h; cases h`). -/
inductive Toy where
  | pure
  | withinTol
  | violating

example (U F tol : ℝ) :
    (if U = 0 then Toy.pure else if U ≤ tol * F then Toy.withinTol else Toy.violating)
        = Toy.withinTol ↔
      ¬ (U = 0) ∧ U ≤ tol * F := by
  split_ifs with h1 h2
  · exact ⟨fun hc => absurd hc (by intro h; cases h), fun hh => absurd h1 hh.1⟩
  · exact ⟨fun _ => ⟨h1, h2⟩, fun _ => rfl⟩
  · exact ⟨fun hc => absurd hc (by intro h; cases h), fun hh => absurd hh.2 h2⟩

set_option linter.unusedVariables false in
/-- An unconsumed hypothesis in a theorem statement DOES trigger `linter.unusedVariables`
(measured: `warning: unused variable 'h'`); the risk probe keeps such hypotheses verbatim and
turns the linter off locally, as `theories/BEP/probes/bep-risk-probe.lean` does. -/
theorem unused_hyp_kept_for_fidelity (h : (1 : ℝ) = 1) : (2 : ℝ) = 2 := rfl

end PhotoLean.Kasha.ApiRisk
