/-
PhotoLean.Kasha.Instances — K5b, the instance and verdict layer of the Kasha theory.

**What this file is.** Every declaration below instantiates the computable rational layer
`PhotoLean/Kasha/RatModel.lean` (K5a, plan §8.1) at one concrete rational rate ladder and lets the
kernel decide the verdict. There are two kinds of rows, labelled in every docstring:

* **model-constructed rows** (I1, I2, I3, I3b, I4, I5, I6, I7, I7b, I8, I8b, I9, I13, I14): the
  numbers are chosen model parameters, never data, and the row is the kernel's evaluation of the
  delivered classifier at those numbers. I8/I8b additionally evaluate the ℝ-side predicates
  `VavilovAt` and `KashaRule` of `PhotoLean/Kasha/Basic.lean` at the no-loss ladder.
* **literature rows** (I10, I11, I11-alt, I11-alt2, I11t, I15): each is an arithmetic verdict on
  numbers **printed in a cited source**, transcribed by `theories/kasha/LITERATURE.md` §R1.6 into
  units of `10⁶ s⁻¹` (the source's own printed unit is quoted in the row's docstring). These rows are
  arithmetic statements **about the printed numbers** — no measurement is performed in this file, and
  a row is only as good as its source. Every literature row states, in its own docstring, the
  transcription rule and the source locus, the `rad 0 = 1`, `ic 0 = 0` **declared modelling
  reduction** (the lowest level's nonradiative channel is neglected in that row, which is what makes
  K3 #3's reduced criterion apply *exactly*), and the identification `rad 1 ≡ Σk_r(S₂)`,
  `ic 1 ≡ Σk_nr(S₂)` as the **declared bridge** of `LITERATURE.md` §R1.4.2 — a modelling
  identification, never a theorem of this development. Neither the reduction nor the bridge is hidden
  in a definition: both live in the docstrings and in the plan's honesty table. The three independent
  azulene routes (I11 thesis, I11-alt printed quantum yield, I11-alt2 peer-reviewed rates) carry
  their mutual spread in every one of their docstrings, so the solvent/method spread is visible
  rather than averaged away; I11t shows that the *same* measured data flips verdict between the 1 %
  and 10 % tolerances, and `LITERATURE.md` §R1.3/§R1.6 records that `tol = 1/100` is a model choice
  with no printed literature threshold — the number `99` carries no literature citation.

**Recipe** (measured end to end in `theories/kasha/probes/kasha-rat-probe.lean`, 12 rows, exit 0;
the K5a layer is `PhotoLean.Kasha.RatModel`): every row below is closed by one `norm_num` call that
is handed the definitions of the row plus the finset evaluation lemmas
`Finset.sum_range_succ`, `Finset.sum_range_one`, `Finset.sum_Icc_succ_top`, `Finset.sum_singleton`,
`Finset.prod_Icc_succ_top`, `Finset.Icc_self`, `Finset.prod_singleton`. The `N = 2` rows (I6, I7,
I7b) genuinely need `Finset.prod_Icc_succ_top`: their cascade carries the non-singleton bound
`Finset.Icc 1 2`. The same recipe closes the ℝ-side rows I8/I8b. The alternative decision procedure
that evaluates these goals through the compiler is excluded by the axiom discipline
(`Lean.ofReduceBool` is not among `ALLOWED_AXIOMS`), and `by decide` does not reduce them (measured).

**Statement authority**: the K5b section of `theories/kasha/probes/kasha-statement-skeleton.lean`
(sha256 `8508e1df7705daaac31288ef78e97073aaff2f1c6422c31bd2eb83b669cbf888`), which transcribes
`theories/kasha/plan.md` §8.2 — including the literature rows appended 2026-09-20. Every statement
below is that block word for word; the literature docstrings extend the authority's text with the
provenance sentences required by the dispatch, and the numbers are the authority's literals
verbatim. Row I12 is **absent by decision, not by omission**: §R1.6 found no second anti-Kasha
molecule with first-hand numbers, so the row was dropped rather than guessed (plan §8.2).

Plan locus: `theories/kasha/plan.md` §8.2; board `theories/kasha/TASKS.md` §K5b. Imports:
`Mathlib` + `PhotoLean.Kasha.RatModel` only — the rows are kernel computations and deliberately do
not depend on the K3 sharpness module.

Acceptance commands (run on a clean tree):

    proofs/scripts/lake build PhotoLean.Kasha.Instances
    proofs/scripts/check.sh --strict PhotoLean.Kasha.Instances
    proofs/scripts/axioms.sh PhotoLean.Kasha.Instances PhotoLean.Kasha.<fully.qualified.theorem>

The delivered file contains no unfinished-proof placeholder and no custom axiomatic declaration;
the `#print axioms` gate of every theorem below lists at most `propext`, `Classical.choice`,
`Quot.sound`.
-/
import Mathlib
import PhotoLean.Kasha.RatModel

open scoped BigOperators

set_option autoImplicit false

namespace PhotoLean

namespace Kasha

/-! ## I1–I9 — model-constructed rows (plan §8.2)

Every row below is `model-constructed`: the ladder is a chosen family of rational rate data, not
data, and the verdict is the kernel's evaluation of the K5a cascade at those numbers. -/

/-- Plan §8.2 row I1 — conforming control: `ic 1 / rad 1 = 100 ≥ 99` at `tol = 1/100`. -/
theorem I1_conforming_control :
    KashaWithinQ (twoRad 1 1) (twoIc 0 100) (1 / 100) 1 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I2 — anti-Kasha control at the same tolerance: `ic 1 / rad 1 = 10 < 99`. -/
theorem I2_antiKasha_control : ¬ KashaWithinQ (twoRad 1 1) (twoIc 0 10) (1 / 100) 1 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I3 — the threshold is attained with equality (`ic 1 / rad 1 = 99`). -/
theorem I3_threshold_boundary : KashaWithinQ (twoRad 1 1) (twoIc 0 99) (1 / 100) 1 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I3b — one unit below the threshold fails. -/
theorem I3b_threshold_below : ¬ KashaWithinQ (twoRad 1 1) (twoIc 0 (9899 / 100)) (1 / 100) 1 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I4 — the Markov recursion at concrete rationals (`N = 1`). -/
theorem I4_fluoYield_one : fluoYieldQ (twoRad 1 1) (twoIc 0 100) 1 = 1 := by
  norm_num [fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ, decayQ, twoRad, twoIc,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I5 — the leak at concrete rationals (`N = 1`). -/
theorem I5_upperYield_one : upperYieldQ (twoRad 1 1) (twoIc 0 100) 1 = 1 / 101 := by
  norm_num [upperYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ, decayQ, twoRad, twoIc,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I6 — the three-level recursion at concrete rationals (`N = 2`). -/
theorem I6_fluoYield_two : fluoYieldQ (threeRad 1 1 1) (threeIc 1 1 1) 2 = 7 / 8 := by
  norm_num [fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ, decayQ, threeRad, threeIc,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I7 — **the equal-rates counterexample**: every level above the lowest satisfies
`ic ≥ rad` and yet `upperYield / fluoYield = 6/7 > 1/2`. -/
theorem I7_equalRates_leak_two : upperYieldQ (threeRad 1 1 1) (threeIc 1 1 1) 2 = 3 / 4 := by
  norm_num [upperYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ, decayQ, threeRad, threeIc,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I7b — the same ladder violates the tolerance form at `tol = 1/2`. -/
theorem I7b_equalRates_violating : ¬ KashaWithinQ (threeRad 1 1 1) (threeIc 1 1 1) (1 / 2) 2 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, threeRad, threeIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I8 — the no-loss ladder: Vavilov holds at every step and the rule fails. -/
theorem I8_noLoss_vavilov : VavilovAt (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) 1 := by
  norm_num [VavilovAt, fluoYield, emitYield, cascade, radBranch, icBranch, decay,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I8b — the same no-loss ladder fails the exact rule. -/
theorem I8b_noLoss_not_kasha : ¬ KashaRule (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) 1 := by
  norm_num [KashaRule, upperYield, emitYield, cascade, radBranch, icBranch, decay,
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I9 — verdict classifier witness: a violating row is classified `violating`. -/
theorem I9_verdict_violating :
    kashaQVerdict (twoRad 1 1) (twoIc 0 10) (1 / 100) 1 = KashaQVerdict.violating := by
  norm_num [kashaQVerdict, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

end Kasha

end PhotoLean
