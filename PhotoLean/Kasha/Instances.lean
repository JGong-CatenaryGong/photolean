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

/-- Plan §8.2 row I13 — row inventory: the two model-constructed verdicts of I1/I2 in one
statement, at the same tolerance. -/
theorem I13_row_inventory :
    KashaWithinQ (twoRad 1 1) (twoIc 0 100) (1 / 100) 1 ∧
      ¬ KashaWithinQ (twoRad 1 1) (twoIc 0 10) (1 / 100) 1 := by
  constructor
  · norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
      decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
      Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  · norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
      decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
      Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I14 — non-vacuity: both verdict kinds occur in the model-constructed rows. -/
theorem I14_not_one_sided :
    (∃ rad ic : ℕ → ℚ, KashaWithinQ rad ic (1 / 100) 1) ∧
      (∃ rad ic : ℕ → ℚ, ¬ KashaWithinQ rad ic (1 / 100) 1) := by
  refine ⟨⟨twoRad 1 1, twoIc 0 100, ?_⟩, ⟨twoRad 1 1, twoIc 0 10, ?_⟩⟩
  · norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
      decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
      Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  · norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
      decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
      Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-! ### K5b literature rows (appended 2026-09-20, plan §8.2; numbers from
`theories/kasha/LITERATURE.md` §R1.6)

Each row below is an **arithmetic verdict about numbers printed in a cited source**, transcribed by
`LITERATURE.md` §R1.6 into units of `10⁶ s⁻¹`; no measurement is performed in this file, and a row is
only as good as its source. The three independent azulene routes carry their mutual spread in every
docstring (20.6 thesis / 40.3 printed 2026 quantum yield / 23.0 peer-reviewed 2020 rates), and I11t
shows the same data flipping verdict between the 1 % and 10 % tolerances. -/

/-- Plan §8.2 row I10 — **literature row, conforming**: 4,6,8-trimethylazulene in cyclohexane.
Source and locus: `theories/kasha/LITERATURE.md` §R1.5.1 — the 1995 Saskatchewan thesis
(K. Tittelbach-Helmrich, *The Photophysics of Azulene and Related Compounds in Solution*,
handle `10388/16065`), Table 3.3, printed p. 126, row TMA/chx, printing `Σk_r = 3.3 × 10⁷ s⁻¹` and
`Σk_nr = 670 × 10⁸ s⁻¹ = 6.7 × 10¹⁰ s⁻¹`. Transcribed by §R1.6 into units of `10⁶ s⁻¹`: `rad 1 = 33`,
`ic 1 = 67000`. `rad 0 = 1`, `ic 0 = 0` is a **declared modelling reduction** — the lowest level's
nonradiative channel is neglected in this row — not data; it is what makes K3 #3's reduced criterion
apply exactly, so the verdict is the pure ratio arithmetic
`ic 1 / rad 1 = 67000/33 ≈ 2030 ≥ 99 = (1 - 1/100)/(1/100)`. The identification
`rad 1 ≡ Σk_r(S₂)`, `ic 1 ≡ Σk_nr(S₂)` is the **declared bridge** of `LITERATURE.md` §R1.4.2 — a
modelling identification, never a result of this development. This row is an arithmetic verdict
**about the printed numbers**; no measurement is performed here, and the row is only as good as its
source. -/
theorem I10_trimethylazulene_conforming :
    KashaWithinQ (twoRad 1 33) (twoIc 0 67000) (1 / 100) 1 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I11 — **literature row, anti-Kasha**: parent azulene in cyclohexane. Source and
locus: `theories/kasha/LITERATURE.md` §R1.4.1(A) — the same 1995 Saskatchewan thesis, Table 3.1,
printed p. 115, row AZU/chx, printing `Σk_r = 3.5 × 10⁷ s⁻¹` and `Σk_nr = 7.2 × 10⁸ s⁻¹`; transcribed
by §R1.6 into units of `10⁶ s⁻¹`: `rad 1 = 35`, `ic 1 = 720`. `rad 0 = 1`, `ic 0 = 0` is a **declared
modelling reduction** — the lowest level's nonradiative channel is neglected in this row — not data;
with it K3 #3's reduced criterion applies exactly. The identification `rad 1 ≡ Σk_r(S₂)`,
`ic 1 ≡ Σk_nr(S₂)` is the **declared bridge** of §R1.4.2, never a theorem of this development. Ratio
`720/35 ≈ 20.6 < 99`, so the printed data violate the 1 % criterion. **Spread between the independent
routes** (recorded here so it is visible rather than averaged away): 20.6 (this thesis row, 1995,
cyclohexane), 40.3 (I11-alt, from the printed 2026 quantum yield), 23.0 (I11-alt2, the peer-reviewed
2020 experimental rates) — a factor below 2, i.e. solvent and method spread, not a disagreement in
sign or order of magnitude. This row is an arithmetic verdict **about the printed numbers**; no
measurement is performed here, and it is only as good as its source. -/
theorem I11_azulene_violating :
    ¬ KashaWithinQ (twoRad 1 35) (twoIc 0 720) (1 / 100) 1 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I11-alt — **literature row, anti-Kasha, independent route**: azulene as printed in
*Chem. Sci.* 2026 (K. Vinod et al., DOI `10.1039/d6sc00694a`, `PMC13576160`; `LITERATURE.md` §R1.4.1(B)
and §R1.6), Table 3 (`τ_IC = 1.35 ns`, `k_IC = 7.4 × 10⁸ s⁻¹`) with the printed quantum yield
`Φ_Fl = 2.42 %` of Table 2/running text. Here the numbers come from the **printed quantum yield**
rather than from two rate columns: with `ic 0 = 0`, `(1 - Φ)/Φ` *is* the ratio `ic 1 / rad 1`, so §R1.6
transcribes `rad 1 = 242`, `ic 1 = 9758` in units of `10⁶ s⁻¹` (the pair is fixed only up to a common
scale, which cancels in the ratio). `rad 0 = 1`, `ic 0 = 0` is a **declared modelling reduction** — the
lowest level's nonradiative channel is neglected in this row — not data. The identification
`rad 1 ≡ Σk_r(S₂)`, `ic 1 ≡ Σk_nr(S₂)` is the **declared bridge** of §R1.4.2, never a theorem; this
route is robust to the `Σk_r`/`Σk_nr` column identification but needs the same `ic 1 ≈ k_IC` premise.
Ratio `9758/242 ≈ 40.3 < 99`. **Spread between the independent routes**: 20.6 (I11, 1995 thesis,
cyclohexane), 40.3 (this row, 2026 printed quantum yield), 23.0 (I11-alt2, 2020 peer-reviewed
experimental rates) — solvent and method spread, not a disagreement in sign. This row is an arithmetic
verdict **about the printed numbers**; no measurement is performed here, and it is only as good as its
source. -/
theorem I11alt_azulene2026_violating :
    ¬ KashaWithinQ (twoRad 1 242) (twoIc 0 9758) (1 / 100) 1 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I11-alt2 — **literature row, anti-Kasha, peer-reviewed rates**: azulene from
K. Veys and D. Escudero, *J. Phys. Chem. A* **124**(36), 7228–7237 (2020), DOI
`10.1021/acs.jpca.0c05205`, Table 2, whose experimental values are printed in parentheses:
`k_r(S₂→S₀) = (2.3 ± 0.1) × 10⁷ s⁻¹` and `k_IC(S₂→S₁) = (5.3 ± 1.2) × 10⁸ s⁻¹`; locus
`LITERATURE.md` §R1.4.1(C-bis) and §R1.6. Transcribed by §R1.6 into units of `10⁶ s⁻¹`:
`rad 1 = 23`, `ic 1 = 530`. `rad 0 = 1`, `ic 0 = 0` is a **declared modelling reduction** — the lowest
level's nonradiative channel is neglected in this row — not data. The identification
`rad 1 ≡ Σk_r(S₂)`, `ic 1 ≡ Σk_nr(S₂)` is the **declared bridge** of §R1.4.2, never a theorem. Ratio
`530/23 ≈ 23.0 < 99`; the same source's printed `Φ = (3.5 ± 0.4) %` independently gives
`(1 - Φ)/Φ ≈ 27.6`, i.e. the same verdict by a second route. **Spread between the independent
routes**: 20.6 (I11, 1995 thesis) / 40.3 (I11-alt, 2026 printed quantum yield) / 23.0 (this row) — all
three on the violating side, the spread being solvent and method spread. This row is an arithmetic
verdict **about the printed numbers**; no measurement is performed here, and it is only as good as its
source. -/
theorem I11alt2_azulene2020_violating :
    ¬ KashaWithinQ (twoRad 1 23) (twoIc 0 530) (1 / 100) 1 := by
  norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
    decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I11t — **the verdict is tolerance-relative** (the honest form of "azulene violates
Kasha's rule"): the *same* measured azulene data (I11: `rad 1 = 35`, `ic 1 = 720`, from the 1995
Saskatchewan thesis Table 3.1, printed p. 115, `Σk_r = 3.5 × 10⁷ s⁻¹`, `Σk_nr = 7.2 × 10⁸ s⁻¹`,
transcribed by `LITERATURE.md` §R1.6 into units of `10⁶ s⁻¹`) violate the 1 % purity criterion and
conform to a 10 % one: `720/35 ≈ 20.6 < 99` while `720/35 ≈ 20.6 ≥ 9 = (1 - 1/10)/(1/10)`. `rad 0 = 1`,
`ic 0 = 0` is a **declared modelling reduction** — the lowest level's nonradiative channel is
neglected in both conjuncts — not data; and the identification `rad 1 ≡ Σk_r(S₂)`,
`ic 1 ≡ Σk_nr(S₂)` is the **declared bridge** of §R1.4.2, never a theorem. `LITERATURE.md` §R1.3
records that the literature's `k_IC ≫ k_rad` is a **qualitative** statement with a "typically"
attached and that **no printed threshold** accompanies it — the number `99` carries no literature
citation, it is the model's sharpening of a slogan — and §R1.6 records that `tol = 1/100` is a **model
choice**: this row is what makes that choice visible in the kernel instead of hiding it in prose, the
same printed numbers flipping verdict when the tolerance moves by one decade. The row is an arithmetic
verdict **about the printed numbers**; no measurement is performed here. -/
theorem I11t_azulene_tolerance_dependence :
    ¬ KashaWithinQ (twoRad 1 35) (twoIc 0 720) (1 / 100) 1 ∧
      KashaWithinQ (twoRad 1 35) (twoIc 0 720) (1 / 10) 1 := by
  constructor
  · norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
      decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
      Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  · norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
      decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
      Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- Plan §8.2 row I15 — **family contrast at one tolerance**: within the azulene family the measured
S₂ rates separate the methylated derivative (conforming, I10) from the parent (violating, I11) at the
*same* `tol = 1/100`. Both components carry the same declared reduction and the same declared bridge:
`rad 0 = 1`, `ic 0 = 0` is a **declared modelling reduction** (the lowest level's nonradiative channel
is neglected in both rows — not data), and `rad 1 ≡ Σk_r(S₂)`, `ic 1 ≡ Σk_nr(S₂)` is the **declared
bridge** of `LITERATURE.md` §R1.4.2, never a theorem of this development. The literals are, in units of
`10⁶ s⁻¹`: `rad 1 = 33`, `ic 1 = 67000` for 4,6,8-trimethylazulene (1995 Saskatchewan thesis,
Table 3.3, printed p. 126, `Σk_r = 3.3 × 10⁷ s⁻¹`, `Σk_nr = 6.7 × 10¹⁰ s⁻¹`) and `rad 1 = 35`,
`ic 1 = 720` for azulene (same thesis, Table 3.1, printed p. 115, `Σk_r = 3.5 × 10⁷ s⁻¹`,
`Σk_nr = 7.2 × 10⁸ s⁻¹`). Two kernel computations, one tolerance, opposite verdicts — the
instance-level content the model adds over the qualitative rule; the spread between the independent
azulene routes is recorded in I11, I11-alt and I11-alt2 (20.6 / 40.3 / 23.0). This row is an
arithmetic verdict **about the printed numbers**; no measurement is performed here, and it is only as
good as its sources. -/
theorem I15_familyContrast :
    KashaWithinQ (twoRad 1 33) (twoIc 0 67000) (1 / 100) 1 ∧
      ¬ KashaWithinQ (twoRad 1 35) (twoIc 0 720) (1 / 100) 1 := by
  constructor
  · norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
      decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
      Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  · norm_num [KashaWithinQ, upperYieldQ, fluoYieldQ, emitYieldQ, radBranchQ, icBranchQ, cascadeQ,
      decayQ, twoRad, twoIc, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
      Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

end Kasha

end PhotoLean
