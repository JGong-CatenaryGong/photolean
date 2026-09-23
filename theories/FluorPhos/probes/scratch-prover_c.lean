import Mathlib

def s1Decay (kF kISC kIC : ℝ) : ℝ := kF + kISC + kIC

example (kF kISC kIC kP kNR : ℝ) (hs : s1Decay kF kISC kIC ≠ 0) (ht : kP + kNR ≠ 0) :
    kF / s1Decay kF kISC kIC + kISC * kP / (s1Decay kF kISC kIC * (kP + kNR))
      = (kISC * kP + kF * (kP + kNR)) / (s1Decay kF kISC kIC * (kP + kNR)) := by
  field_simp [s1Decay]
  ring

example (kF kISC kIC kP kNR : ℝ) (hs : s1Decay kF kISC kIC ≠ 0) (ht : kP + kNR ≠ 0) :
    kF / s1Decay kF kISC kIC + kISC * kP / (s1Decay kF kISC kIC * (kP + kNR))
      = (kISC * kP + kF * (kP + kNR)) / (s1Decay kF kISC kIC * (kP + kNR)) := by
  rw [show kF / s1Decay kF kISC kIC = kF * (kP + kNR) / (s1Decay kF kISC kIC * (kP + kNR)) from by
    field_simp
    ring]
  rw [div_add_div_same]
  congr 1
  ring
