import Mathlib

namespace PhotoLean


/-!
# RACI M3 — Barrier: monotonicity of the barrier-type nonradiative rate

Upstream provenance: the ChemLean RACI plan §6.3 (integration record: theories/RACI/plan.md §3.1).
Status note (upstream header, preserved): the statements were transcribed from the upstream plan.
Upstream owner: prover_m3 (exclusive file).
-/

namespace RACI

/-- The barrier-type nonradiative rate: `k_nr = A·exp(−β·B)` (upstream plan §6.3). -/
noncomputable def barrierRate (A β B : ℝ) : ℝ :=
  A * Real.exp (-(β * B))

/-- M3.3: the barrier-type nonradiative rate is antitone (upstream plan §6.3; the M3.1 exponential step, then multiplication by the positive `A`). -/
theorem barrierRate_antitone
    (hA : 0 < A) (hβ : 0 < β) {B1 B2 : ℝ}
    (hB : B1 < B2) :
    barrierRate A β B2 < barrierRate A β B1 := by
  have h1 : β * B1 < β * B2 := mul_lt_mul_of_pos_left hB hβ
  have h2 : -(β * B2) < -(β * B1) := neg_lt_neg h1
  have h3 := Real.exp_strictMono h2
  have h4 := mul_lt_mul_of_pos_left h3 hA
  simpa [barrierRate] using h4

end RACI


end PhotoLean