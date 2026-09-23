/-
QuantumYield-statement-skeleton.lean — the STATEMENT AUTHORITY of the QuantumYield theory.

Statement-first (iron rule 2): every declaration below is the agreed statement of plan §4
verbatim; the theorem bodies are placeholders on purpose (definitions carry their real bodies).
This file must compile at 0 error
(`proofs/scripts/lake env lean theories/QuantumYield/probes/QuantumYield-statement-skeleton.lean`)
BEFORE any proof work starts; delivery replaces the placeholder bodies verbatim and
`python3 theories/BEP/probes/bep-fidelity.py --theory QuantumYield` compares the delivered
signatures to this file word for word.

Plan: `theories/QuantumYield/plan.md`. Milestones: QY1 (Basic), QY2 (Criterion), QY3 (RatModel),
QY4 (Instances).

The theory: `n` parallel first-order decay channels of one excited state with rates
`k : Fin n → ℝ`; the observable yield of channel `i` is `k i / Σⱼ k j` (totalized division).
The yields are additive in two senses: they sum to `1` (conservation, QY-C1), and adding a
channel rescales every existing yield by the same dilution factor `Σk / (Σk + c)` (QY-C6, the
algebraic spine underneath Stern–Volmer quenching and fluorescence/phosphorescence competition;
QY-C7 is its strict form). All channels share one lifetime `τ = 1/Σk` (QY-C2). The premise
bundle `QYData` (nonnegative rates + positive total) is an explicit hypothesis of every physical
row, never hidden in a definition (iron rule 3); QY-C8 shows `total_pos` is load-bearing.

API calibration for this skeleton (iron rule 4):
`theories/QuantumYield/probes/QuantumYield-api-probe.lean`. Two findings affect proof routes
only, never the statements: the `Fin.cons` sum rule is `Fin.sum_cons` (there is no
`Fin.sum_univ_cons`), and ℚ arithmetic verdicts go through `norm_num`, not `decide` (kernel
reduction of `Rat` addition/normalization is stuck at well-founded `Nat.gcd`).
-/
import Mathlib

open scoped BigOperators

set_option autoImplicit false

namespace PhotoLean

namespace QuantumYield

/-! ## QY1 — description layer (`PhotoLean/QuantumYield/Basic.lean`) -/

/-- Total decay rate: the sum of all channel rates.
Plan section 4, row QY-B1. -/
noncomputable def totalRate {n : ℕ} (k : Fin n → ℝ) : ℝ := ∑ i, k i

/-- The observable yield of channel `i`: its share of the total rate (totalized division).
Plan section 4, row QY-B2. -/
noncomputable def yieldOf {n : ℕ} (k : Fin n → ℝ) (i : Fin n) : ℝ := k i / totalRate k

/-- The common lifetime shared by all channels: `τ = 1 / Σk`.
Plan section 4, row QY-B3. -/
noncomputable def tauOf {n : ℕ} (k : Fin n → ℝ) : ℝ := 1 / totalRate k

/-- The premise bundle of the physical rows: nonnegative rates and a positive total.
Plan section 4, row QY-B4. -/
structure QYData {n : ℕ} (k : Fin n → ℝ) : Prop where
  /-- every channel rate is nonnegative -/
  nonneg : ∀ i, 0 ≤ k i
  /-- the total rate is positive (load-bearing: row QY-C8) -/
  total_pos : 0 < totalRate k

/-! ## QY2 — law layer (`PhotoLean/QuantumYield/Criterion.lean`) -/

/-- Conservation: the channel yields sum to `1` (yield additivity, first sense).
Plan section 4, row QY-C1. -/
theorem sum_yieldOf_eq_one {n : ℕ} {k : Fin n → ℝ} (h : QYData k) :
    ∑ i, yieldOf k i = 1 := by
  -- Proof route (plan §5): `Finset.sum_div` + `div_self h.total_pos.ne'`.
  sorry

/-- The common-lifetime law: every yield is its rate times the shared lifetime.
Plan section 4, row QY-C2. -/
theorem yieldOf_eq_mul_tauOf {n : ℕ} {k : Fin n → ℝ} (h : QYData k) (i : Fin n) :
    yieldOf k i = k i * tauOf k := by
  -- Proof route (plan §5): unfold `tauOf`; field algebra with `h.total_pos.ne'`.
  sorry

/-- Yields are nonnegative.
Plan section 4, row QY-C3, first half. -/
theorem yieldOf_nonneg {n : ℕ} {k : Fin n → ℝ} (h : QYData k) (i : Fin n) :
    0 ≤ yieldOf k i := by
  -- Proof route (plan §5): `div_nonneg (h.nonneg i) h.total_pos.le`.
  sorry

/-- Yields never exceed `1`.
Plan section 4, row QY-C3, second half. -/
theorem yieldOf_le_one {n : ℕ} {k : Fin n → ℝ} (h : QYData k) (i : Fin n) :
    yieldOf k i ≤ 1 := by
  -- Proof route (plan §5): `div_le_one h.total_pos` + `Finset.single_le_sum`.
  sorry

/-- A channel is live exactly when its rate is positive.
Plan section 4, row QY-C4. -/
theorem yieldOf_pos_iff {n : ℕ} {k : Fin n → ℝ} (h : QYData k) (i : Fin n) :
    0 < yieldOf k i ↔ 0 < k i := by
  -- Proof route (plan §5): `div_pos`; the converse consumes `h.nonneg i` with `h.total_pos`.
  sorry

/-- Relative yields measure rate ratios, independent of all other channels.
Plan section 4, row QY-C5. -/
theorem yieldOf_div_yieldOf {n : ℕ} {k : Fin n → ℝ} (h : QYData k) {i j : Fin n} (hj : 0 < k j) :
    yieldOf k i / yieldOf k j = k i / k j := by
  -- Proof route (plan §5): unfold `yieldOf`; field algebra with `hj.ne'` and `h.total_pos.ne'`.
  sorry

/-- Adding a channel adds its rate to the total.
Plan section 4, row QY-C6, first form. -/
theorem totalRate_cons {n : ℕ} (c : ℝ) (k : Fin n → ℝ) :
    totalRate (Fin.cons c k) = c + totalRate k := by
  -- Proof route (plan §5, API-calibrated): `Fin.sum_cons` (no `Fin.sum_univ_cons` exists).
  sorry

/-- The added channel's own yield.
Plan section 4, row QY-C6, second form. -/
theorem yieldOf_cons_zero {n : ℕ} (c : ℝ) (k : Fin n → ℝ) :
    yieldOf (Fin.cons c k) 0 = c / (c + totalRate k) := by
  -- Proof route (plan §5, API-calibrated): unfold; `Fin.cons_zero` + `Fin.sum_cons`.
  sorry

/-- An existing channel's yield after a channel is added at index `0`.
Plan section 4, row QY-C6, third form. -/
theorem yieldOf_cons_succ {n : ℕ} {k : Fin n → ℝ} (h : QYData k) (c : ℝ) (i : Fin n) :
    yieldOf (Fin.cons c k) i.succ = k i / (c + totalRate k) := by
  -- Proof route (plan §5, API-calibrated): unfold; `Fin.cons_succ` + `Fin.sum_cons`.
  sorry

/-- The dilution-factor form: adding a channel rescales every existing yield by the same factor
`Σk / (Σk + c)` (yield additivity, second sense).
Plan section 4, row QY-C6, fourth form. -/
theorem yieldOf_cons_succ_factor {n : ℕ} {k : Fin n → ℝ} (h : QYData k) (c : ℝ) (i : Fin n) :
    yieldOf (Fin.cons c k) i.succ = yieldOf k i * (totalRate k / (c + totalRate k)) := by
  -- Proof route (plan §5): `yieldOf_cons_succ` + field algebra with `h.total_pos.ne'`.
  sorry

/-- A new channel strictly dilutes every live channel.
Plan section 4, row QY-C7. -/
theorem yieldOf_cons_lt {n : ℕ} {k : Fin n → ℝ} (h : QYData k) (c : ℝ) (hc : 0 < c) {i : Fin n}
    (hi : 0 < k i) :
    yieldOf (Fin.cons c k) i.succ < yieldOf k i := by
  -- Proof route (plan §5): `mul_lt_mul_of_pos_left` with the factor `< 1` (`div_lt_one`).
  sorry

/-- The `total_pos` premise of QY-C1 is load-bearing: at `k ≡ 0` every rate is nonnegative, the
total is not positive, and totalized `0 / 0 = 0` makes the yield sum `0 ≠ 1`.
Plan section 4, row QY-C8 (witness `k ≡ 0` pre-computed in the api-probe). -/
theorem totalRate_zero_counterexample :
    ∃ k : Fin 2 → ℝ, (∀ i, 0 ≤ k i) ∧ ¬ (0 < totalRate k) ∧ ∑ i, yieldOf k i ≠ 1 := by
  sorry

/-- Non-vacuity: a witness with every channel live and the conservation sum exact (the triple
conjunct blocks the trivial-witness failure mode — the M1 lesson). Witness `![1, 2, 3]`
(yields `1/6, 1/3, 1/2`) is pre-computed in the api-probe.
Plan section 4, row QY-C9. -/
theorem nonvacuous_all_channels_live :
    ∃ k : Fin 3 → ℝ, QYData k ∧ (∀ i, 0 < yieldOf k i) ∧ ∑ i, yieldOf k i = 1 := by
  sorry

/-! ## QY3 — the rational decision layer (`PhotoLean/QuantumYield/RatModel.lean`) -/

namespace Rat

/-- Rational total rate.
Plan section 4, row QY-R1. -/
def totalRate {n : ℕ} (k : Fin n → ℚ) : ℚ := ∑ i, k i

/-- Rational yield of channel `i`.
Plan section 4, row QY-R1. -/
def yieldOf {n : ℕ} (k : Fin n → ℚ) (i : Fin n) : ℚ := k i / totalRate k

/-- The premise bundle in the decision layer.
Plan section 4, row QY-R1. -/
structure QYData {n : ℕ} (k : Fin n → ℚ) : Prop where
  /-- every channel rate is nonnegative -/
  nonneg : ∀ i, 0 ≤ k i
  /-- the total rate is positive -/
  total_pos : 0 < totalRate k

/-- Decidability of the decision-layer premise bundle (plan section 4, row QY-R1). Calibration
note (api-probe): `decide` closes the fieldwise `nonneg` half but cannot evaluate the
`Finset.univ` sum inside `total_pos` (kernel-stuck at `Rat.blt` via well-founded `Nat.gcd`);
concrete `total_pos` goals go through `norm_num [totalRate, Fin.sum_univ_three, …]`. -/
instance instDecidableQYData {n : ℕ} (k : Fin n → ℚ) : Decidable (QYData k) :=
  decidable_of_iff ((∀ i, 0 ≤ k i) ∧ 0 < totalRate k)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.nonneg, h.total_pos⟩⟩

/-- Cast coherence of the total rate: the rational total casts to the real total of the cast
rates.
Plan section 4, row QY-R2, first form. -/
theorem totalRate_cast {n : ℕ} (kq : Fin n → ℚ) :
    (totalRate kq : ℝ) = PhotoLean.QuantumYield.totalRate (fun i => (kq i : ℝ)) := by
  -- Proof route (API-calibrated): `Rat.cast_sum Finset.univ kq`.
  sorry

/-- Cast coherence of the yield: the rational yield casts to the real yield of the cast rates.
Plan section 4, row QY-R2, second form. -/
theorem yieldOf_cast {n : ℕ} (kq : Fin n → ℚ) (i : Fin n) :
    (yieldOf kq i : ℝ) = PhotoLean.QuantumYield.yieldOf (fun i => (kq i : ℝ)) i := by
  -- Proof route (API-calibrated): unfold; `Rat.cast_div` + `Rat.cast_sum`.
  sorry

end Rat

/-! ## QY4 — named instances and verdicts (`PhotoLean/QuantumYield/Instances.lean`) -/

/-- Fluorescein S₁ channel rates `(kF, kIC, kISC)`; fluorescence yield `φF = 9/10`.
Representative of the literature yield ordering (LITERATURE).
Plan section 4, row QY-I1. -/
def fluoresceinS1 : Fin 3 → ℚ := ![18, 1, 1]

/-- Quinine-like channel rates; `φF = 11/20`.
Plan section 4, row QY-I2. -/
def quinineLike : Fin 3 → ℚ := ![11, 5, 4]

/-- Fluorescein S₁ with an added quenching channel of rate `9` at index `0` (the Stern–Volmer
dilution rehearsal at ℚ).
Plan section 4, row QY-I3. -/
def quenchDilution : Fin 4 → ℚ := Fin.cons 9 fluoresceinS1

/-- Verdict row: the fluorescence yield of fluorescein S₁ is `9/10`.
Plan section 4, row QY-I1 (verdict). -/
theorem inst_fluoresceinS1_phiF : Rat.yieldOf fluoresceinS1 0 = 9 / 10 := by
  -- Proof route (API-calibrated; the plan's `(decide)` cannot reduce the `Finset.univ` sum):
  -- `norm_num [Rat.yieldOf, Rat.totalRate, fluoresceinS1, Fin.sum_univ_three,
  --   Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]`.
  sorry

/-- Verdict row: the fluorescence yield of the quinine-like instance is `11/20`.
Plan section 4, row QY-I2 (verdict). -/
theorem inst_quinineLike_phiF : Rat.yieldOf quinineLike 0 = 11 / 20 := by
  -- Proof route: as `inst_fluoresceinS1_phiF`.
  sorry

/-- Verdict row: the added channel dilutes the fluorescence yield to `18/29` (the fluorescence
channel now sits at index `1`).
Plan section 4, row QY-I3 (verdict, first form). -/
theorem inst_quenchDilution_phiF : Rat.yieldOf quenchDilution 1 = 18 / 29 := by
  -- Proof route (API-calibrated): `decide` for the index application
  -- (`Fin.cons 9 ![18, 1, 1] 1 = 18`), `norm_num [Fin.sum_cons, …]` for the total.
  sorry

/-- Verdict row: the Stern–Volmer ratio of the quenched instance is `29/20`.
Plan section 4, row QY-I3 (verdict, second form). -/
theorem inst_quenchDilution_sternVolmer :
    Rat.yieldOf fluoresceinS1 0 / Rat.yieldOf quenchDilution 1 = 29 / 20 := by
  -- Proof route: the verdicts `inst_fluoresceinS1_phiF` and `inst_quenchDilution_phiF`;
  -- `norm_num`.
  sorry

end QuantumYield

end PhotoLean
