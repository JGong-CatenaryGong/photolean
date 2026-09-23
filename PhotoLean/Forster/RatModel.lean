/-
PhotoLean.Forster.RatModel — milestone FO3, the rational decision layer.

The theory: Förster resonance energy transfer and the κ² convention (plan
`theories/Forster/plan.md`, §4 FO-R). This module carries the kernel-decidable shadow of the law
layer: the `ℚ` twins of `fretEff6`, `r0six` and `fretRate`, their cast coherence with the `ℝ`
definitions, and the two headline verdicts of the convention analysis.

The `2/3` convention is formalized here — **not** as a continuous spherical average (that needs
integration over the rotation group and is a registered non-goal, plan §1.3) but as the **exact
average over the orthonormal frame**: dipoles along the axes `i, j`, separation along the axis `k`.
Every axis-aligned pair gives `0`, `1` or `4`, so the frame factor is `ℤ`-valued (`frameKappa`)
and the kernel decides the nine-pair sum (`frame_sum_eq_six`); the average `(Σ frameKappa)/9 = 2/3`
then follows by `norm_num` (`iso_frame_avg`). This two-step shape is a probe-time correction
recorded in the statement authority §3.1 item 1: `decide` does not reduce `ℚ` division, and
`norm_num` with `Fin.ext_iff` overflows the recursion depth.

Statement authority: `theories/Forster/probes/Forster-statement-skeleton.lean` § FO-R; every
signature below is identical to its authority row. The cast-coherence row `fretEff6_cast` was
checked against the SV-R1 lesson (a namespace-shadowed right-hand side can silently elaborate to
the vacuous identity `↑x = ↑x`): the authority writes the right-hand side explicitly qualified as
`Forster.fretEff6`, and a `#print` probe confirms the delivered row is the real bridge between the
`ℚ` twin and the `ℝ` definition — not a reflexive identity. There is no unproved placeholder and
no custom axiomatic declaration anywhere in this file. Acceptance:
`proofs/scripts/lake build PhotoLean.Forster.RatModel` (exit 0);
`proofs/scripts/check.sh --strict`;
`python3 theories/BEP/probes/bep-fidelity.py --theory Forster`.
-/
import PhotoLean.Forster.Criterion

set_option autoImplicit false

namespace PhotoLean

namespace Forster

/-! ## FO-R — the rational decision layer -/

namespace Rat

/-- Plan §4, FO-R1 (ℚ twin). -/
def fretEff6 (r6 R : ℚ) : ℚ := r6 / (r6 + R ^ 6)

/-- Plan §4, FO-R1 (ℚ twin). -/
def r0six (C kappasq Φ J n : ℚ) : ℚ := C * kappasq * Φ * J / n ^ 4

/-- Plan §4, FO-R1 (ℚ twin). -/
def fretRate (tauD r6 R : ℚ) : ℚ := (1 / tauD) * (r6 / R ^ 6)

/-- Plan §4, FO-R1. Cast coherence for `fretEff6`. Route: `Rat.cast_div` / `Rat.cast_add` /
`Rat.cast_pow` (names confirmed in the api probe). -/
theorem fretEff6_cast (r6 R : ℚ) :
    ((fretEff6 r6 R : ℚ) : ℝ) = Forster.fretEff6 (r6 : ℝ) (R : ℝ) := by
  unfold fretEff6 Forster.fretEff6
  push_cast
  ring

/-- Plan §4, FO-R2 (probe-corrected shape). The orientation factor on the orthonormal frame —
**integer-valued** (every axis-aligned pair gives `0`, `1` or `4`), so the kernel decides the
sum over ℤ. -/
def frameKappa (i j k : Fin 3) : ℤ :=
  ((if i = j then 1 else 0) - 3 * (if i = k then 1 else 0) * (if j = k then 1 else 0)) ^ 2

/-- Plan §4, FO-R2 (first step). The nine-pair frame sum, kernel-decided over ℤ. Route:
`decide` (probed green). -/
theorem frame_sum_eq_six : (∑ i : Fin 3, ∑ j : Fin 3, frameKappa i j 2) = 6 := by
  decide

/-- Plan §4, FO-R2 (**the `2/3` convention**). The isotropic convention is exactly the frame
average: `(Σ frameKappa)/9 = 2/3`. Route: `frame_sum_eq_six` + cast + `norm_num` (probed). -/
theorem iso_frame_avg :
    ((∑ i : Fin 3, ∑ j : Fin 3, frameKappa i j 2 : ℤ) : ℚ) / 9 = 2 / 3 := by
  norm_num [show (∑ i : Fin 3, ∑ j : Fin 3, frameKappa i j 2) = 6 from by decide]

/-- Plan §4, FO-R3. The blind-spot comparison at the decision layer: convention-positive,
truth-zero. Route: `norm_num [r0six, fretEff6]` (probed). -/
theorem rat_blind_spot :
    fretEff6 (r0six 1 0 1 1 1) 1 = 0 ∧ 0 < fretEff6 (r0six 1 (2 / 3) 1 1 1) 1 := by
  constructor <;> norm_num [fretEff6, r0six]

/-- Plan §4, FO-R3. The maximal-bias ratio at the decision layer. Route: `norm_num [r0six]`
(probed). -/
theorem rat_max_bias : r0six 1 4 1 1 1 / r0six 1 (2 / 3) 1 1 1 = 6 := by
  norm_num [r0six]

end Rat

end Forster

end PhotoLean
