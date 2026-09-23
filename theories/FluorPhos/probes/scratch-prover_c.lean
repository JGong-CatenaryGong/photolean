import Mathlib
example {kF kISC kIC : ℝ} (hkIC : 0 ≤ kIC) (hkISC : 0 ≤ kISC) (hs1 : 0 < kF + kISC + kIC) :
    0 < kF + kIC := by
  by_contra hle
  push_neg at hle
  nlinarith [hs1, hkIC, hkISC, hle]
