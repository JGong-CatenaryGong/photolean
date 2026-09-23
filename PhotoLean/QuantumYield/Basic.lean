/-
PhotoLean.QuantumYield.Basic — milestone QY1, the description layer.

The theory: `n` parallel first-order decay channels of one excited state with rates
`k : Fin n → ℝ`; the observable yield of channel `i` is its share of the total rate,
`yieldOf k i = k i / totalRate k` (totalized division), and all channels share the single
lifetime `tauOf k = 1 / totalRate k` (plan `theories/QuantumYield/plan.md`, §1.1 and §4).

Honest scope, stated up front:
* everything is algebraic over `ℝ` with totalized division; the positivity content of the law
  rows lives in the explicit premise bundle `QYData` (nonnegative rates + positive total),
  never as a hidden side condition of a definition (engine rule 3), and `QY-C8` shows its
  `total_pos` field is load-bearing;
* no rate law is integrated and no time dependence is modelled: the yields are the
  time-integrated branching content, taken as the model's definition (plan §1.3);
* the channel count `n` is fixed per statement; the added channel of the dilation law is
  `Fin.cons` at index `0` (plan §2).

Statement authority: `theories/QuantumYield/probes/QuantumYield-statement-skeleton.lean` § QY-B;
every signature below is identical to its authority row. There is no unproved placeholder and
no custom axiomatic declaration anywhere in this file. Acceptance:
`proofs/scripts/lake build PhotoLean.QuantumYield.Basic` (exit 0);
`proofs/scripts/check.sh --strict`; fidelity
`python3 theories/BEP/probes/bep-fidelity.py --theory QuantumYield`.
-/
import Mathlib

open scoped BigOperators

set_option autoImplicit false

namespace PhotoLean

namespace QuantumYield

/-! ## QY-B — description layer -/

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

end QuantumYield

end PhotoLean
