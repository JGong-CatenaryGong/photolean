import Mathlib

private lemma gate_core {kISC kISC' kF kIC : ℝ} (hs1 : 0 < kF + kISC + kIC)
    (hkISC : 0 ≤ kISC) (hlt : kISC < kISC') : 0 < kISC + kISC' - kF - kIC := by
  by_contra hle
  push_neg at hle
  have hs' : 0 < kISC := lt_of_le_of_lt hkISC hlt
  have h2 : 2 * kISC < kF + kIC := by linarith
  have h3 : 4 * (kISC * kISC) < (kF + kIC) * (kF + kIC) := by nlinarith
  have h4 : kISC * kISC < (kF + kIC) * kISC := by nlinarith
  nlinarith [mul_pos hs1 hs']
