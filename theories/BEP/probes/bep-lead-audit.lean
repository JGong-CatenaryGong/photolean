/-
Lead audit probe for the BEP theory (2026-09-20).

Purpose: keep the few numbers quoted in `theories/BEP/RESULTS.md` as *kernel-checked
in-repository artifacts* rather than as unrecorded side computations. The closeout audits
correctly refused to accept "kernel-checked" without an artifact; this file is that artifact
for the `13/16` note of the I9 row (the two-point observable slope is `13/16`, while the
delivered coefficient is `3/4`).

Compile (the file lives outside `SOURCE_DIRS`, so it is a probe, not a delivery):

    proofs/scripts/lake env lean theories/BEP/probes/bep-lead-audit.lean

Expectation: exit 0, no output (every `example` below closes).
-/
import Mathlib
import PhotoLean.BEP.Basic
import PhotoLean.BEP.RatModel
import PhotoLean.BEP.Instances

namespace PhotoLean.BEP.LeadAudit

/-- The delivered I9 coefficient is `3/4`, not `13/16`. -/
example : Rat.qTransfer (-2 : ℚ) 1 = 3 / 4 :=
  inst_I9_unphysical_transfer

/-- `13/16` is the *two-point observable slope* of the same model point, taken over the pair
`x₁ = 1`, `x₂ = 3/2` (a different quantity — exactly the conflation the plan's premise registry
forbids). -/
example : Rat.qAlphaObs 1 (Rat.qEact (-2 : ℚ) 1) (3 / 2) (Rat.qEact (-2 : ℚ) (3 / 2)) = 13 / 16 := by
  unfold Rat.qAlphaObs Rat.qEact
  norm_num

/-- Non-vacuity of the blindness claim: the bounds hold at the unphysical point while the
descriptor's positivity fails, so `EPBounds` alone cannot detect `λ < 0`. -/
example : EPBounds (-2) 1 := by
  unfold EPBounds transfer
  norm_num

example : ¬ (0 < (-2 : ℝ)) := by norm_num

/-- A second, independent spot check of the sharp witnesses quoted in `RESULTS.md` §3. -/
example : bepDefect 2 1 = 1 / 8 := by
  unfold bepDefect bepLine eact
  norm_num

example : secSlope 2 0 1 = 3 / 8 := by
  unfold secSlope eact
  norm_num

example : epZone 2 3 = EPZone.beyondForward := by
  unfold epZone
  norm_num

end PhotoLean.BEP.LeadAudit
