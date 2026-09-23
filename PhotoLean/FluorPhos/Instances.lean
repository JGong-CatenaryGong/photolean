/-
PhotoLean.FluorPhos.Instances — milestone FP4, the named rational instances.

The law layer of `PhotoLean.FluorPhos.Criterion` is quantitative but abstract; this module pins the
two named representative models of the plan's §4 rows FP-I1–FP-I3 and proves their verdicts on the
named rates themselves, so a reader can compare the models without re-reading the abstract rows.

* FP-I1 `naphthaleneLike` (`kF = 1`, `kISC = 1`, `kIC = 1/2`, `kP = 1/10`, `kNR = 1`):
  fluorescence-dominant — `phiF = 2/5`, `phiP = 2/55`, zone `fluorDominant`;
* FP-I2 `eosinLike` (the heavy-atom model, `kISC = 10`): the FP-C6 crossover premise holds
  (`kF·(kP+kNR) = 2 < 10 = kISC·kP`) and the zone is `phosphorDominant`;
* FP-I3 `crossoverWitness`: the two-parameter pair straddling the FP-C6 threshold — `kISC = 2`
  sits exactly at `kF·(kP+kNR)/kP = 2` (zone `balanced`), `kISC = 3` is past it (zone
  `phosphorDominant`).

What is NOT derived here: the two named models are **representative rational rate sets, not fitted
spectroscopic data** (plan §9 honesty table row 3; `theories/FluorPhos/LITERATURE.md` pins the
heavy-atom ordering `kISC` ↑ across the series). They are named because their verdicts are
machine-checkable, not because they describe a particular molecule.

Measured route (api probe calibration): the ℚ zone rows are decided by `unfold fpZoneQ` followed
by `norm_num` — bare `decide` does not reduce ℚ literals that involve division in this toolchain
(the repository's thrice-measured `Rat.instDecidableLt` boundary), so no `decide` appears below.
The ℝ-side yields are decided by unfolding the delivered definitions and closing with `norm_num`.

Statement authority: every definition body and theorem signature below is taken word for word from
`theories/FluorPhos/probes/FluorPhos-statement-skeleton.lean` (the frozen Phase-1 authority,
sha256 `2aa08f1c153b6494c09fd9848c76644ab0b7a59c2a3f46d32a25db7a8d3223bb`, 29 declarations),
which transcribes `theories/FluorPhos/plan.md` §4; fidelity is checked by
`python3 theories/BEP/probes/bep-fidelity.py --theory FluorPhos`.

There is no unproved placeholder and no custom axiomatic declaration in this file. Note: the two
keyword literals that `proofs/scripts/check.sh --strict` scans for are deliberately not spelled
out anywhere in this file — the scan covers `PhotoLean/**/*.lean` including block comments, so
writing them (even in prose) would be a false-positive FAIL.

Plan locus: `theories/FluorPhos/plan.md` §4 (FP-I rows), sprint FP4; board
`theories/FluorPhos/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.FluorPhos.Instances
    proofs/scripts/check.sh --strict PhotoLean.FluorPhos.Instances
    proofs/scripts/axioms.sh PhotoLean.FluorPhos.Instances PhotoLean.FluorPhos.naphthaleneLike_verdict
-/
import PhotoLean.FluorPhos.Basic
import PhotoLean.FluorPhos.Criterion
import PhotoLean.FluorPhos.RatModel

set_option autoImplicit false

namespace PhotoLean

namespace FluorPhos

/-- Plan §4, FP-I1. The naphthalene-like representative model (rates `kF = 1`, `kISC = 1`,
`kIC = 1/2`, `kP = 1/10`, `kNR = 1` over ℚ; representative of the literature ordering
`kISC/kF ≈ 3–4`, NOT a fitted value — LITERATURE.md). -/
def naphthaleneLike : ℚ × ℚ × ℚ × ℚ × ℚ := (1, 1, 1 / 2, 1 / 10, 1)

/-- Plan §4, FP-I1 (verdict). Fluorescence-dominant: `phiF = 2/5`, `phiP = 2/55`, zone
`fluorDominant`. Route: `norm_num [phiF, phiP, ...]` over ℝ at the cast instance; the zone by
`norm_num [fpZoneQ]` (the `decide` boundary: ℚ division equalities go to `norm_num`, never
`decide` — measured, cf. `PhotoLean.Marcus.RatModel`). -/
theorem naphthaleneLike_verdict :
    phiF (1 : ℝ) 1 (1 / 2) = 2 / 5 ∧
      phiP (1 : ℝ) 1 (1 / 2) (1 / 10) 1 = 2 / 55 ∧
        fpZoneQ 1 1 (1 / 2) (1 / 10) 1 = .fluorDominant := by
  refine ⟨?_, ?_, ?_⟩
  · unfold phiF s1Decay
    norm_num
  · unfold phiP iscBranch t1BranchP s1Decay
    norm_num
  · unfold fpZoneQ
    norm_num

/-- Plan §4, FP-I2. The eosin-like heavy-atom representative model (`kISC = 10`). -/
def eosinLike : ℚ × ℚ × ℚ × ℚ × ℚ := (1, 10, 1 / 2, 1, 1)

/-- Plan §4, FP-I2 (verdict). Phosphorescence-competitive: the crossover premise
`kF·(kP+kNR) < kISC·kP` holds (`2 < 10`) and the zone is `phosphorDominant`. -/
theorem eosinLike_verdict :
    (1 : ℝ) * (1 + 1) < 10 * 1 ∧
      fpZoneQ 1 10 (1 / 2) 1 1 = .phosphorDominant := by
  refine ⟨?_, ?_⟩
  · norm_num
  · unfold fpZoneQ
    norm_num

/-- Plan §4, FP-I3. The crossover witness pair: two models straddling the FP-C6 threshold
(`kISC = 2` sits exactly at `kF·(kP+kNR)/kP = 2` — balanced; `kISC = 3` is past it). -/
theorem crossoverWitness_verdict :
    fpZoneQ 1 2 (1 / 2) 1 1 = .balanced ∧ fpZoneQ 1 3 (1 / 2) 1 1 = .phosphorDominant := by
  refine ⟨?_, ?_⟩
  · unfold fpZoneQ
    norm_num
  · unfold fpZoneQ
    norm_num

end FluorPhos

end PhotoLean
