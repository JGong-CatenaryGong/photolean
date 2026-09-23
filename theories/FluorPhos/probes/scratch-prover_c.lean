import PhotoLean.FluorPhos.Criterion
open PhotoLean.FluorPhos

-- the two positive pieces of A2 - B2
example (kF kISC kISC' kIC kP kNR : ℝ) :
    kISC' * kP * ((kF + kISC' + kIC) * (kP + kNR)) - kISC * kP * ((kF + kISC + kIC) * (kP + kNR))
      = (kISC' + kISC) * kP * (kP + kNR) * (kISC' - kISC) := by
  ring_nf

example {kF kISC kISC' kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR)
    (h' : FPData kF kISC' kIC kP kNR) (hkP : 0 < kP) (h0 : 0 < kF + kIC)
    (hlt : kISC < kISC') :
    phiP kF kISC kIC kP kNR < phiP kF kISC' kIC kP kNR := by
  have hs1 : s1Decay kF kISC kIC = kF + kISC + kIC := rfl
  have hs1' : s1Decay kF kISC' kIC = kF + kISC' + kIC := rfl
  have hden : 0 < s1Decay kF kISC kIC * (kP + kNR) := mul_pos h.s1Decay_pos h.t1Decay_pos
  have hden' : 0 < s1Decay kF kISC' kIC * (kP + kNR) := mul_pos h'.s1Decay_pos h.t1Decay_pos
  have h1 : 0 < kISC' - kISC := by linarith
  have hISC0 : 0 ≤ kISC := h.kISC_nonneg
  have hISC'0 : 0 ≤ kISC' := le_trans hISC0 (le_of_lt hlt)
  have hnum : kISC * kP * (s1Decay kF kISC' kIC * (kP + kNR))
      < kISC' * kP * (s1Decay kF kISC kIC * (kP + kNR)) := by
    have hs : s1Decay kF kISC kIC = kISC + (kF + kIC) := by rw [hs1]; ring
    have hs' : s1Decay kF kISC' kIC = kISC' + (kF + kIC) := by rw [hs1']; ring
    rw [hs, hs']
    have hid : kISC' * kP * ((kISC' + (kF + kIC)) * (kP + kNR))
        - kISC * kP * ((kISC + (kF + kIC)) * (kP + kNR))
        = (kISC' + kISC) * kP * (kP + kNR) * (kISC' - kISC) := by ring_nf
    have hpos : 0 < (kISC' + kISC) * kP * (kP + kNR) * (kISC' - kISC) :=
      mul_pos (mul_pos (mul_pos (by linarith) hkP) h.t1Decay_pos) h1
    linarith
  rw [phiP_eq h, phiP_eq h']
  rw [div_lt_div_iff₀ (a := kISC * kP) (b := s1Decay kF kISC kIC * (kP + kNR))
    (c := kISC' * kP) (d := s1Decay kF kISC' kIC * (kP + kNR)) hden hden']
  exact hnum
