/-
PhotoLean.ICvsISC.Instances — FC4, the named rational models and their verdicts.

The law layer of this theory is quantitative: the rate ratio factors into spin/prefactor × the
Franck–Condon factor (`Criterion.lean`, FC-C1), the log-form competition law is exact (FC-C2), the
crossover is `isc_dominates_iff` (FC-C3), a sub-unit coupling charges the ISC channel a spin
discount (FC-C4) and at zero coupling the channel is shut (FC-C5). This module pins those claims to
**named rational models** so that a reader can check the two barrier values and the resulting
verdict on printed numbers rather than on the general statements:

* FC-I1 `aromaticCarbonylLike` — `lamI = 1, xI = 3/2, lamS = 1/2, xS = 1` (with `HSO = 1/10` and
  `AI = AS` in the narrative of the row, plan §4): the barriers are `1/16` (IC) and `1/8` (ISC).
  The ISC barrier is **higher**, so the barrier race is lost and the sub-unit spin discount
  (`2·log HSO < 0`, FC-C4) makes the win strictly harder: the class-C reading is that this
  aromatic-carbonyl-like corner of the parameter plane is IC-favoured. The registered direction is
  the FC-C4 contrapositive: because the ISC barrier is not lower, FC-C4 forbids an ISC win for
  **every** `0 < HSO < 1` at equal prefactors (and the theorem's third conjunct states that the pair
  of barrier values, not only their order, is as printed).
* FC-I2 `elSayedFavoredLike` — `HSO = 1, AI = AS, lamI = 1, xI = 3/2, lamS = 2, xS = 3/2`: a pure
  barrier race. The barriers are `1/16` (IC) and **`1/32`** (ISC), so the ISC barrier is strictly
  lower and the FC-C7 verdict is `true`. Plan §8 required these numbers to be recomputed by the
  probe before the row was written, and §3.1 records the arithmetic correction: the plan draft
  carried `1/16` with a question mark, the api-probe recomputation fixed the ISC value at `1/32`
  (the correction is indexed in `proofs/API-NOTES.md` §photobatch, statement-change index row 4).
  The frozen authority and this file therefore both carry `1/32`.
* FC-I3 `hsoZeroWitness` — `HSO = 0` with an arbitrary base prefactor `AS`: the ISC prefactor
  vanishes at ℚ, the FC-C5 boundary decided on the prefactor side (no gap data enters).

Every verdict is decided by kernel computation on rational literals — the same ladders the api
probe pre-computed (`theories/ICvsISC/probes/ICvsISC-api-probe.lean`) — with the rate ordering read
on the **barrier side** (`Rat.fcBarrier`), never through `Real.exp` (plan §4, row FC-C7: "no `exp`
evaluation enters any instance"). The route for the ℚ-literal rows is
`norm_num [Rat.fcBarrier]` for the arithmetic conjuncts plus `decide_eq_true_eq` /
`decide_eq_false_iff_not` before `norm_num` for the `Bool` verdicts: the bare decision procedure
does not reduce ℚ-literal Bools in the kernel (the api-probe note).

What is NOT derived here: the three models are **representative rational models, not fitted
spectroscopic data** (plan §9 honesty table row 4); they are named because their verdicts are
machine-checkable, not because they describe a particular molecule. El-Sayed's rule enters this
theory only as the parameter `HSO` — registered, never derived (plan §1.2, §9 row 2) — so
`elSayedFavoredLike` is a barrier-race model, not a derivation of the rule.

Plan locus: `theories/ICvsISC/plan.md` §4 (FC-I rows), §8 (the probe-recompute discipline), §9
(honesty table); sprint FC4; board `theories/ICvsISC/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.ICvsISC.Instances
    proofs/scripts/check.sh --strict PhotoLean.ICvsISC.Instances
    proofs/scripts/axioms.sh PhotoLean.ICvsISC.Instances PhotoLean.ICvsISC.<theorem>

Statement authority: every declaration below matches
`theories/ICvsISC/probes/ICvsISC-statement-skeleton.lean` word for word. The delivered file
contains no unfinished-proof placeholder and no custom axiomatic declaration; `#print axioms` of
every theorem below lists at most `propext`, `Classical.choice`, `Quot.sound`. Note deliberately:
the keyword literals that `proofs/scripts/check.sh --strict` scans for are not spelled out
anywhere in this file — the scan covers `PhotoLean/**/*.lean` including block comments.
-/
import PhotoLean.ICvsISC.RatModel

set_option autoImplicit false

namespace PhotoLean

namespace ICvsISC

/-! ## FC-I — named instances: representative rational models -/

/-- The aromatic-carbonyl-like instance (`lamI = 1, xI = 3/2, lamS = 1/2, xS = 1`, `HSO = 1/10`,
`AI = AS`): the barriers are `1/16` (IC) vs `1/8` (ISC) — the ISC barrier is *higher*, so with
equal prefactors and `HSO < 1` the spin discount makes the win harder. The verdict is computed at
the barrier level (`decide`), and the FC-C4 direction is registered contrapositively: the ISC
barrier is not lower, so FC-C4 gives no ISC win. Plan section 4, row FC-I1.
Proof route: `norm_num` at ℚ for the barrier values; the verdict via `decide_eq_false_iff_not`
+ `norm_num` (bare `by decide` does not reduce ℚ-literal Bools in the kernel — probe-calibrated;
values pre-computed in the API probe). -/
theorem aromaticCarbonylLike :
    Rat.fcBarrier 1 (3 / 2) = 1 / 16 ∧ Rat.fcBarrier (1 / 2) 1 = 1 / 8 ∧
      ¬ (Rat.fcBarrier (1 / 2) 1 < Rat.fcBarrier 1 (3 / 2)) ∧
        Rat.barrierOrderQ 1 (3 / 2) (1 / 2) 1 = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [Rat.fcBarrier]
  · norm_num [Rat.fcBarrier]
  · norm_num [Rat.fcBarrier]
  · rw [Rat.barrierOrderQ, decide_eq_false_iff_not]
    norm_num [Rat.fcBarrier]

/-- The El-Sayed-favored-like instance (`HSO = 1`, `AI = AS`, `lamI = 1, xI = 3/2, lamS = 2`,
`xS = 3/2`): a pure barrier race. The probe-recomputed barriers (plan §8: recomputed before the
row was written) are `1/16` (IC) vs `1/32` (ISC), so the ISC barrier is strictly lower and the
FC-C7 verdict is `true`. Plan section 4, row FC-I2.
Proof route: `norm_num` at ℚ for the barrier values; the verdict via `decide_eq_true_eq` +
`norm_num` (probe-calibrated). -/
theorem elSayedFavoredLike :
    Rat.fcBarrier 1 (3 / 2) = 1 / 16 ∧ Rat.fcBarrier 2 (3 / 2) = 1 / 32 ∧
      Rat.fcBarrier 2 (3 / 2) < Rat.fcBarrier 1 (3 / 2) ∧
        Rat.barrierOrderQ 1 (3 / 2) 2 (3 / 2) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [Rat.fcBarrier]
  · norm_num [Rat.fcBarrier]
  · norm_num [Rat.fcBarrier]
  · rw [Rat.barrierOrderQ, decide_eq_true_eq]
    norm_num [Rat.fcBarrier]

/-- **The spin discount trumps a Franck–Condon advantage** — FC-I3 made concrete at the
El-Sayed-favored barrier pair: the pure barrier race is won by ISC (`fcBarrier 2 (3/2) = 1/32 <
1/16 = fcBarrier 1 (3/2)`, decided at ℚ), yet with the spin-orbit coupling shut (`HSO = 0`) the
ISC rate is identically zero — no triplet channel, whatever the barriers.
Re-frozen 2026-09-23 (plan §3.1 entry 2; Phase-3 vacuity audit, verifier run 4 finding F3): the
first frozen form was the tautology `(0 : ℚ) ^ 2 * AS = 0` (`zero_mul`, no model object); this
form carries both halves of the intended witness.
Plan section 4, row FC-I3. -/
theorem hsoZeroWitness :
    Rat.barrierOrderQ 1 (3 / 2) 2 (3 / 2) = true ∧ iscRate (0 : ℝ) 1 2 1 1 (3 / 2) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [Rat.barrierOrderQ, decide_eq_true_eq]
    norm_num [Rat.fcBarrier]
  · unfold iscRate
    ring

end ICvsISC

end PhotoLean
