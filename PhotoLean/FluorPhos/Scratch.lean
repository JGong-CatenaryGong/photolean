import Mathlib

def s1Decay (kF kISC kIC : ℝ) : ℝ := kF + kISC + kIC

structure FPData (kF kISC kIC kP kNR : ℝ) : Prop where
  kF_nonneg : 0 ≤ kF
  kISC_nonneg : 0 ≤ kISC
  kIC_nonneg : 0 ≤ kIC
  kP_nonneg : 0 ≤ kP
  kNR_nonneg : 0 ≤ kNR
  s1Decay_pos : 0 < s1Decay kF kISC kIC
  t1Decay_pos : 0 < kP + kNR

private theorem exhaust_residue {kF kISC kIC kP kNR : ℝ}
    (h : FPData kF kISC kIC kP kNR) :
    s1Decay kF kISC kIC * (kP + kNR) - (kISC * kP + kF * (kP + kNR))
      = kIC * (kP + kNR) + kISC * kNR := by
  rw [s1Decay]; ring

example {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR)
    (heq : kISC * kP + kF * (kP + kNR) = s1Decay kF kISC kIC * (kP + kNR)) :
    kIC = 0 ∧ (kISC = 0 ∨ kNR = 0) := by
  have hkN : 0 < kP + kNR := h.t1Decay_pos
  have hres := exhaust_residue h
  have h1 : 0 ≤ kISC * kNR := mul_nonneg h.kISC_nonneg h.kNR_nonneg
  have h2 : 0 ≤ kIC * (kP + kNR) := mul_nonneg h.kIC_nonneg (le_of_lt hkN)
  have hzero : kIC * (kP + kNR) + kISC * kNR = 0 := by linarith
  have hIK : kIC * (kP + kNR) = 0 := by linarith
  have hIS : kISC * kNR = 0 := by linarith
  exact ⟨(mul_eq_zero.mp hIK).resolve_right (ne_of_gt hkN), mul_eq_zero.mp hIS⟩

example {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR)
    (hkIC : kIC = 0) (h5 : kISC = 0) :
    kISC * kP + kF * (kP + kNR) = s1Decay kF kISC kIC * (kP + kNR) := by
  have hres := exhaust_residue h
  have h0 : (0:ℝ) = kIC * (kP + kNR) + kISC * kNR := by
    rw [hkIC, h5]; ring
  linarith

example {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR)
    (hkIC : kIC = 0) (h5 : kNR = 0) :
    kISC * kP + kF * (kP + kNR) = s1Decay kF kISC kIC * (kP + kNR) := by
  have hres := exhaust_residue h
  have h0 : (0:ℝ) = kIC * (kP + kNR) + kISC * kNR := by
    rw [hkIC, h5]; ring
  linarith
