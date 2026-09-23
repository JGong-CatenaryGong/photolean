import Mathlib
set_option maxHeartbeats 800000

example {kF kISC kIC : ℝ} (hkF : 0 ≤ kF) (hkIC : 0 ≤ kIC) (hkISC : 0 ≤ kISC)
    (hs1 : 0 < kF + kISC + kIC) : 0 < kF + kIC := by
  have h : kISC ≤ 0 + (kF + kISC + kIC) := by linarith
  linarith [hs1, hkISC, hkF, hkIC, h]
