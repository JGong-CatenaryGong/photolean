import Mathlib
def qTransfer (lam x : ℚ) : ℚ := 1 / 2 - x / (2 * lam)
def qConformsWindow (lam tol w : ℚ) : Prop := 0 < lam ∧ 0 < tol ∧ w ^ 2 ≤ 4 * lam * tol
def qSecondDividedDiff (x₁ e₁ x₂ e₂ x₃ e₃ : ℚ) : ℚ :=
  ((e₃ - e₂) / (x₃ - x₂) - (e₂ - e₁) / (x₂ - x₁)) / (x₃ - x₁)
inductive EPQVerdict where | degenerate | unphysical | conforming | boundary | superLinear | subLinear
  deriving DecidableEq, Repr
def epQVerdict (lam x : ℚ) : EPQVerdict :=
  if lam = 0 then EPQVerdict.degenerate
  else if lam < 0 then EPQVerdict.unphysical
  else if x = lam then EPQVerdict.boundary
  else if x = -lam then EPQVerdict.boundary
  else if 0 < qTransfer lam x ∧ qTransfer lam x < 1 then EPQVerdict.conforming
  else if 1 < qTransfer lam x then EPQVerdict.superLinear
  else EPQVerdict.subLinear

-- decimals
example : ((0.3 : ℚ) = 3 / 10) := by norm_num
example : ((15.6 : ℚ) = 78 / 5) := by norm_num
example : ((7.62 : ℚ) = 381 / 50) := by norm_num
-- norm_num on the divided difference with decimal literals
example : qSecondDividedDiff (0.9 : ℚ) 15.7 2.3 15.7 4.9 13.9 = -9 / 52 := by
  norm_num [qSecondDividedDiff]
-- norm_num on conformance predicates
example : qConformsWindow (2 : ℚ) (1 / 8) 1 := by unfold qConformsWindow; norm_num
example : ¬ qConformsWindow (2 : ℚ) (1 / 16) 1 := by unfold qConformsWindow; norm_num
-- does unfold+norm_num close the verdict cascade?
example : qTransfer (2 : ℚ) 0 = 1 / 2 := by unfold qTransfer; norm_num
example : epQVerdict (2 : ℚ) 0 = EPQVerdict.conforming := by unfold epQVerdict qTransfer; norm_num
example : epQVerdict (2 : ℚ) 3 = EPQVerdict.subLinear := by unfold epQVerdict qTransfer; norm_num
