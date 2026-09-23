/-
PhotoLean.StokesShift.Instances — milestone SS-I, the named-instance / verdict layer.

Representative rational models of the Stokes-shift rule, decided by the kernel through the ℚ
decision layer (milestone SS-R) and, where a real-model statement is claimed, tied back to the
`ℝ` row by the cast-coherence theorems. As everywhere in this repository, an instance row is a
statement **about the printed numbers** under the declared model — nothing here measures a dye,
and a row is only as good as the reading of the model it instantiates (plan §9).

The three instances:
* `mirrorDye` (`lam = 1/2`, `e00 = 2`) — the mirror-symmetric case: absorption `5/2`, emission
  `3/2`, shift `1` (twice the curvature `1/2`), midpoint `2`; the classifier returns
  `normalEmission`. This is the row SS-C6/SS-C3 instantiated at printed numbers.
* `largeRelaxation` (`lam = 3/2`, `e00 = 2`) — large reorganization, still emitting: emission
  `1/2 > 0`, shift `3`; the window is open but narrow (`lam < e00`).
* `invertedCorner` (`lam = 2, e00 = 2` and `lam = 3, e00 = 2`) — the window edge
  (`zeroPhoton`, emission `0`) and the regime beyond it (`invertedEmission`, emission `< 0`).
  This pair is the **negative result** registered as an instance verdict: it refutes
  "the vertical emission is always positive" with the model's own boundary, and it is exactly
  the `lam = e00` / `lam > e00` side of `emEnergy_pos_iff` (SS-C5) and
  `emEnergy_pos_iff_inverted` (SS-C9).

Numerics are decided by `norm_num` (the repository's measured rule: `decide` does not reduce `ℚ`
division); the classifier rows are decided by unfolding the `if`-cascade, never by `decide` on a
division-bearing literal.

Statement authority: `theories/StokesShift/probes/StokesShift-statement-skeleton.lean` § SS-I;
every signature below is identical to its authority row. There is no unproved placeholder and no
custom axiomatic declaration anywhere in this file; no runtime evaluation command appears in it
— every row is a proof term. The `#print axioms` gate of every theorem below lists at most
`propext`, `Classical.choice`, `Quot.sound`.

Acceptance (contract `proofs/ENGINE.yml`):
  proofs/scripts/lake build PhotoLean.StokesShift.Instances
  proofs/scripts/check.sh --strict PhotoLean.StokesShift.Instances
  proofs/scripts/axioms.sh PhotoLean.StokesShift.Instances PhotoLean.StokesShift.mirrorDye
-/
import PhotoLean.StokesShift.RatModel

set_option autoImplicit false

namespace PhotoLean

namespace StokesShift

/-! ## SS-I — instances and verdicts -/

/-- The mirror-symmetric dye (`lam = 1/2`, `e00 = 2`): absorption `5/2`, emission `3/2`,
shift `1`, midpoint `2`; zone `normalEmission`. Plan section 4, row SS-I1. Facts about printed
rationals, decided by `norm_num`/`decide`. -/
theorem mirrorDye :
    Rat.absEnergy (1 / 2) 2 = 5 / 2 ∧ Rat.emEnergy (1 / 2) 2 = 3 / 2 ∧
    Rat.stokesShift (1 / 2) 2 = 1 ∧ (Rat.absEnergy (1 / 2) 2 + Rat.emEnergy (1 / 2) 2) / 2 = 2 ∧
    ssZoneQ (1 / 2) 2 = .normalEmission := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Rat.absEnergy, Rat.s1Surface, Rat.s0Surface]
  · norm_num [Rat.emEnergy, Rat.s1Surface, Rat.s0Surface]
  · norm_num [Rat.stokesShift, Rat.absEnergy, Rat.emEnergy, Rat.s1Surface, Rat.s0Surface]
  · norm_num [Rat.absEnergy, Rat.emEnergy, Rat.s1Surface, Rat.s0Surface]
  · unfold ssZoneQ
    rw [if_pos (by norm_num)]

/-- Large relaxation (`lam = 3/2`, `e00 = 2`): emission `1/2`, shift `3` — still emitting.
Plan section 4, row SS-I2. Facts about printed rationals, decided by `norm_num`. -/
theorem largeRelaxation :
    Rat.emEnergy (3 / 2) 2 = 1 / 2 ∧ Rat.stokesShift (3 / 2) 2 = 3 := by
  constructor
  · norm_num [Rat.emEnergy, Rat.s1Surface, Rat.s0Surface]
  · norm_num [Rat.stokesShift, Rat.absEnergy, Rat.emEnergy, Rat.s1Surface, Rat.s0Surface]

/-- The inverted corner: at `(lam, e00) = (2, 2)` the window edge (`zeroPhoton`), and at
`(3, 2)` beyond it (`invertedEmission`) — the refuting pair for "emission is always positive"
(a negative result registered as an instance verdict). Plan section 4, row SS-I3. Zone
verdicts decided by `decide`. -/
theorem invertedCorner :
    ssZoneQ 2 2 = .zeroPhoton ∧ ssZoneQ 3 2 = .invertedEmission := by
  constructor
  · unfold ssZoneQ
    rw [if_neg (by norm_num), if_neg (by norm_num)]
  · unfold ssZoneQ
    rw [if_neg (by norm_num), if_pos (by norm_num)]

end StokesShift

end PhotoLean
