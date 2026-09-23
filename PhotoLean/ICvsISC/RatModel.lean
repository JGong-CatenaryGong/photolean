/-
PhotoLean.ICvsISC.RatModel — FC3, the rational decision layer of the IC-vs-ISC competition.

The real layer (`Basic`, `Criterion`) states the competition with `Real.exp`/`Real.log`. Every
*decision* the theory asks for, however, is a comparison of rational numbers: which of the two
Franck–Condon barriers is lower. This module delivers the computable ℚ shadow that those decisions
are made in — with **no transcendental function anywhere in the layer** (hard constraint 3 /
plan §4, row FC-C7: "no `exp` evaluation enters any instance"):

* FC-R1 `Rat.fcBarrier` — the computable ℚ copy of the Franck–Condon barrier; pure polynomial
  division. `Rat.fcBarrier_cast` is the cast-coherence row: the ℚ shadow computes the real barrier
  at cast parameters, with `push_cast` + `ring` under the cast-division/cast-power chain.
* FC-R2 `Rat.barrierOrderQ` — the barrier-order decision: `true` exactly when the ISC barrier is
  strictly lower than the IC barrier, i.e. `decide (fcBarrier lamS xS < fcBarrier lamI xI)` at ℚ.
  The correctness row `Rat.barrierOrderQ_correct` is the bridge to the real layer: the Bool
  computes the order of the **real** barriers. The cast is pulled off with `Rat.cast_lt` after the
  two `fcBarrier_cast` rewrites, so the equivalence closes definitionally.
* The proof route for ℚ-literal Bools is the api-probe-calibrated one (`decide_eq_true_eq` followed
  by `norm_num`, never a bare decision procedure — it does not reduce ℚ-literal Bools in the
  kernel); it is exercised by `Instances.lean`.

On the cast-coherence row and the namespace-shadowing pitfall (SV-R1, cross-cutting, found in the
SternVolmer batch of this sweep). A declaration whose name carries a namespace prefix
(`theorem Rat.fcBarrier_cast`) elaborates its own type inside that namespace, so an unqualified
right-hand side can silently resolve to the ℚ shadow and the row degenerates into the vacuous
identity `↑x = ↑x`. Here the statement is the authority's: the real barrier is written **fully
qualified** as `_root_.PhotoLean.ICvsISC.fcBarrier` on the left and the ℚ shadow unqualified on the
right, exactly as the skeleton writes it. The delivered row was therefore probed with `#print`
before delivery (scratch file under `.lake/tmp/`, unique name) and shows the
cast-division/cast-power/cast-sub chain — the non-vacuous bridge, **not** a definitional
`↑x = ↑x`; the `rfl`-level identity would have been a statement incident, not a proof.

Plan locus: `theories/ICvsISC/plan.md` §4 (FC-R rows), §5 (routes); sprint FC3; board
`theories/ICvsISC/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.ICvsISC.RatModel
    proofs/scripts/check.sh --strict PhotoLean.ICvsISC.RatModel
    proofs/scripts/axioms.sh PhotoLean.ICvsISC.RatModel PhotoLean.ICvsISC.<theorem>

Statement authority: every declaration below matches
`theories/ICvsISC/probes/ICvsISC-statement-skeleton.lean` word for word. The delivered file
contains no unfinished-proof placeholder and no custom axiomatic declaration; `#print axioms` of
every theorem below lists at most `propext`, `Classical.choice`, `Quot.sound`. Note deliberately:
the keyword literals that `proofs/scripts/check.sh --strict` scans for are not spelled out
anywhere in this file — the scan covers `PhotoLean/**/*.lean` including block comments.
-/
import PhotoLean.ICvsISC.Basic

set_option autoImplicit false

namespace PhotoLean

namespace ICvsISC

namespace Rat

/-- The ℚ shadow of the Franck–Condon barrier. Plan section 4, row FC-R1. -/
def fcBarrier (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- Cast coherence: the ℚ shadow computes the real barrier.
Plan section 4, row FC-R1. Proof route: `push_cast` + `ring` (dry-run in the API probe). -/
theorem fcBarrier_cast {lam x : ℚ} :
    _root_.PhotoLean.ICvsISC.fcBarrier (lam : ℝ) (x : ℝ) = (fcBarrier lam x : ℝ) := by
  unfold fcBarrier _root_.PhotoLean.ICvsISC.fcBarrier
  push_cast
  ring

/-- The barrier-order decision at ℚ: `true` iff the ISC barrier is strictly lower than the IC
barrier — the FC-C7 comparison, computed. Plan section 4, row FC-R2. -/
def barrierOrderQ (lamI xI lamS xS : ℚ) : Bool :=
  decide (fcBarrier lamS xS < fcBarrier lamI xI)

/-- Correctness of the decision: the Bool computes the real barrier order.
Plan section 4, row FC-R2.
Proof route: unfold `barrierOrderQ`, `of_decide_eq_true` / `decide_eq_true_eq`, then
`fcBarrier_cast` + `Rat.cast_lt`. -/
theorem barrierOrderQ_correct {lamI xI lamS xS : ℚ} :
    barrierOrderQ lamI xI lamS xS = true ↔
      _root_.PhotoLean.ICvsISC.fcBarrier (lamS : ℝ) (xS : ℝ) <
        _root_.PhotoLean.ICvsISC.fcBarrier (lamI : ℝ) (xI : ℝ) := by
  have hcastS : _root_.PhotoLean.ICvsISC.fcBarrier (lamS : ℝ) (xS : ℝ)
      = (fcBarrier lamS xS : ℝ) := fcBarrier_cast
  have hcastI : _root_.PhotoLean.ICvsISC.fcBarrier (lamI : ℝ) (xI : ℝ)
      = (fcBarrier lamI xI : ℝ) := fcBarrier_cast
  unfold barrierOrderQ
  rw [decide_eq_true_eq, hcastS, hcastI, Rat.cast_lt]

end Rat

end ICvsISC

end PhotoLean
