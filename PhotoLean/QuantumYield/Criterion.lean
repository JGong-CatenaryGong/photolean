/-
PhotoLean.QuantumYield.Criterion — milestone QY2, the law layer.

The algebraic spine of the theory (plan `theories/QuantumYield/plan.md`, §1.1 and §4): for parallel
first-order decay channels of one excited state the yields are additive in two senses.

* **Conservation (QY-C1).** The channel yields sum to `1` — `∑ i, yieldOf k i = 1` under the
  premise bundle `QYData`. The `total_pos` field is load-bearing, not decoration: at the zero rate
  vector every rate is still nonnegative while totalized `0 / 0 = 0` makes the sum `0 ≠ 1`, which
  is exactly the delivered counterexample `totalRate_zero_counterexample` (QY-C8).
* **Common lifetime (QY-C2).** `yieldOf k i = k i * tauOf k`: all channels share the single
  lifetime `τ = 1/Σk`. The row is definitional, and it is the reason `tauOf` carries physical
  information rather than being a notational convenience.
* **Positivity and bounds (QY-C3, QY-C4).** Yields are nonnegative, never exceed `1`, and channel
  `i` is live exactly when its rate is positive.
* **Ratio law (QY-C5).** Relative yields measure rate ratios and are independent of every other
  channel: `yieldOf k i / yieldOf k j = k i / k j`. This is the structural fact behind the
  Stern–Volmer reduction — the shared total cancels.
* **Dilation (QY-C6, QY-C7).** Adding a channel `c` at index `0` adds its rate to the total
  (`totalRate_cons`), gives the new channel its own share `c/(c + Σk)` (`yieldOf_cons_zero`), and
  rescales every existing yield by the same factor `Σk/(Σk + c)` (`yieldOf_cons_succ_factor`) —
  additivity in the second sense; the rescaling is strict at every live channel (QY-C7).
* **Non-vacuity (QY-C9).** `![1, 2, 3]` has every channel live (yields `1/6, 1/3, 1/2`) with the
  conservation sum exact — the triple conjunct blocks the trivial-witness failure mode.

Measured API boundaries (api probe, `proofs/API-NOTES.md` §photobatch): `Fin.sum_univ_cons` does
NOT exist in this mathlib; the cons-sum route is `Fin.sum_univ_succ` + `Fin.cons_zero` (the tail
`Fin.cons_succ` equality is definitional). Matrix-literal indices need
`Matrix.cons_val_zero/one/two` in the `norm_num` set.

Statement authority: `theories/QuantumYield/probes/QuantumYield-statement-skeleton.lean` § QY-C;
every signature below is identical to its authority row. There is no unproved placeholder and no
custom axiomatic declaration anywhere in this file. Acceptance:
`proofs/scripts/lake build PhotoLean.QuantumYield.Criterion` (exit 0);
`proofs/scripts/check.sh --strict`;
`proofs/scripts/axioms.sh PhotoLean.QuantumYield.Criterion PhotoLean.QuantumYield.sum_yieldOf_eq_one`.
-/
import PhotoLean.QuantumYield.Basic

open scoped BigOperators

set_option autoImplicit false

namespace PhotoLean

namespace QuantumYield

/-! ## QY-C — laws -/

/-- Conservation: the channel yields sum to `1` (yield additivity, first sense).
Plan section 4, row QY-C1. -/
theorem sum_yieldOf_eq_one {n : ℕ} {k : Fin n → ℝ} (h : QYData k) :
    ∑ i, yieldOf k i = 1 := by
  -- Proof route (plan §5): `Finset.sum_div` + `div_self h.total_pos.ne'`.
  unfold yieldOf totalRate
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt h.total_pos)

/-- The common-lifetime law: every yield is its rate times the shared lifetime.
Plan section 4, row QY-C2. Re-frozen 2026-09-23 (plan §3.1 entry 1): the `QYData` premise was
dropped — the identity is definition-level under totalized division and consumes no premise
(weakest-premise standard, iron rule 3). -/
theorem yieldOf_eq_mul_tauOf {n : ℕ} {k : Fin n → ℝ} (i : Fin n) :
    yieldOf k i = k i * tauOf k := by
  -- Proof route: unfold `yieldOf`/`tauOf`; `div_eq_mul_inv` + `one_div` (no premises).
  unfold yieldOf tauOf
  rw [div_eq_mul_inv, one_div]

/-- Yields are nonnegative.
Plan section 4, row QY-C3, first half. -/
theorem yieldOf_nonneg {n : ℕ} {k : Fin n → ℝ} (h : QYData k) (i : Fin n) :
    0 ≤ yieldOf k i := by
  -- Proof route (plan §5): `div_nonneg (h.nonneg i) h.total_pos.le`.
  unfold yieldOf
  exact div_nonneg (h.nonneg i) h.total_pos.le

/-- Yields never exceed `1`.
Plan section 4, row QY-C3, second half. -/
theorem yieldOf_le_one {n : ℕ} {k : Fin n → ℝ} (h : QYData k) (i : Fin n) :
    yieldOf k i ≤ 1 := by
  -- Proof route (plan §5): `div_le_one h.total_pos` + `Finset.single_le_sum`.
  unfold yieldOf
  rw [div_le_one h.total_pos]
  exact Finset.single_le_sum (fun j _ => h.nonneg j) (Finset.mem_univ i)

/-- A channel is live exactly when its rate is positive.
Plan section 4, row QY-C4. -/
theorem yieldOf_pos_iff {n : ℕ} {k : Fin n → ℝ} (h : QYData k) (i : Fin n) :
    0 < yieldOf k i ↔ 0 < k i := by
  -- Proof route (plan §5): `div_pos`; the converse consumes `h.nonneg i` with `h.total_pos`.
  unfold yieldOf
  exact div_pos_iff_of_pos_right h.total_pos

/-- Relative yields measure rate ratios, independent of all other channels.
Plan section 4, row QY-C5. -/
theorem yieldOf_div_yieldOf {n : ℕ} {k : Fin n → ℝ} (h : QYData k) {i j : Fin n} (hj : 0 < k j) :
    yieldOf k i / yieldOf k j = k i / k j := by
  -- Proof route (plan §5): unfold `yieldOf`; field algebra with `hj.ne'` and `h.total_pos.ne'`.
  unfold yieldOf
  field_simp [h.total_pos.ne', hj.ne']

/-- Adding a channel adds its rate to the total.
Plan section 4, row QY-C6, first form. -/
theorem totalRate_cons {n : ℕ} (c : ℝ) (k : Fin n → ℝ) :
    totalRate (Fin.cons c k) = c + totalRate k := by
  -- Proof route (plan §5, API-calibrated): `Fin.sum_cons` (no `Fin.sum_univ_cons` exists).
  unfold totalRate
  rw [Fin.sum_univ_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]

/-- The added channel's own yield.
Plan section 4, row QY-C6, second form. -/
theorem yieldOf_cons_zero {n : ℕ} (c : ℝ) (k : Fin n → ℝ) :
    yieldOf (Fin.cons c k) 0 = c / (c + totalRate k) := by
  -- Proof route (plan §5, API-calibrated): unfold; `Fin.cons_zero` + `Fin.sum_cons`.
  unfold yieldOf
  rw [Fin.cons_zero, totalRate_cons]

/-- An existing channel's yield after a channel is added at index `0`.
Plan section 4, row QY-C6, third form. Re-frozen 2026-09-23 (plan §3.1 entry 2): the `QYData`
premise was dropped — the identity is definitional under totalized division and holds at every
rate vector (independent verifier run 2; stripped form re-proved before this edit). -/
theorem yieldOf_cons_succ {n : ℕ} {k : Fin n → ℝ} (c : ℝ) (i : Fin n) :
    yieldOf (Fin.cons c k) i.succ = k i / (c + totalRate k) := by
  unfold yieldOf
  rw [Fin.cons_succ, totalRate_cons]

/-- The dilution-factor form: adding a channel rescales every existing yield by the same factor
`Σk / (Σk + c)` (yield additivity, second sense).
Plan section 4, row QY-C6, fourth form. -/
theorem yieldOf_cons_succ_factor {n : ℕ} {k : Fin n → ℝ} (h : QYData k) (c : ℝ) (i : Fin n) :
    yieldOf (Fin.cons c k) i.succ = yieldOf k i * (totalRate k / (c + totalRate k)) := by
  -- Proof route (plan §5): `yieldOf_cons_succ` + field algebra with `h.total_pos.ne'`.
  rw [yieldOf_cons_succ c i]
  unfold yieldOf
  by_cases hc : c + totalRate k = 0
  · simp [hc]
  · field_simp [hc, h.total_pos.ne']

/-- A new channel strictly dilutes every live channel.
Plan section 4, row QY-C7. -/
theorem yieldOf_cons_lt {n : ℕ} {k : Fin n → ℝ} (h : QYData k) (c : ℝ) (hc : 0 < c) {i : Fin n}
    (hi : 0 < k i) :
    yieldOf (Fin.cons c k) i.succ < yieldOf k i := by
  -- Proof route (plan §5): `mul_lt_mul_of_pos_left` with the factor `< 1` (`div_lt_one`).
  rw [yieldOf_cons_succ_factor h c i]
  have hpos : 0 < yieldOf k i := (yieldOf_pos_iff h i).2 hi
  have hb : 0 < c + totalRate k := by linarith [h.total_pos]
  have hf : totalRate k / (c + totalRate k) < 1 := by
    rw [div_lt_one hb]
    linarith
  calc yieldOf k i * (totalRate k / (c + totalRate k)) < yieldOf k i * 1 :=
        mul_lt_mul_of_pos_left hf hpos
    _ = yieldOf k i := mul_one _

/-- The `total_pos` premise of QY-C1 is load-bearing: at `k ≡ 0` every rate is nonnegative, the
total is not positive, and totalized `0 / 0 = 0` makes the yield sum `0 ≠ 1`.
Plan section 4, row QY-C8 (witness `k ≡ 0` pre-computed in the api-probe). -/
theorem totalRate_zero_counterexample :
    ∃ k : Fin 2 → ℝ, (∀ i, 0 ≤ k i) ∧ ¬ (0 < totalRate k) ∧ ∑ i, yieldOf k i ≠ 1 := by
  refine ⟨fun _ => 0, fun _ => le_refl 0, ?_, ?_⟩
  · simp [totalRate]
  · simp [yieldOf, totalRate]

/-- Non-vacuity: a witness with every channel live and the conservation sum exact (the triple
conjunct blocks the trivial-witness failure mode — the M1 lesson). Witness `![1, 2, 3]`
(yields `1/6, 1/3, 1/2`) is pre-computed in the api-probe.
Plan section 4, row QY-C9. -/
theorem nonvacuous_all_channels_live :
    ∃ k : Fin 3 → ℝ, QYData k ∧ (∀ i, 0 < yieldOf k i) ∧ ∑ i, yieldOf k i = 1 := by
  refine ⟨![1, 2, 3], ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · norm_num [totalRate, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]
  · intro i
    fin_cases i <;>
      norm_num [yieldOf, totalRate, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two]
  · norm_num [yieldOf, totalRate, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

end QuantumYield

end PhotoLean
