/-
PhotoLean.FluorPhos.RatModel — milestone FP3, the rational decision layer.

The order of `ℝ` is not computable, so a crossover verdict about measured rates cannot be decided by
the kernel over `ℝ` (the repository's standing structural solution: an `ℝ` theory plus a `ℚ` shadow
plus cast bridges). This module carries the ℚ twins of the two yields (FP-R1), the cast-coherence
rows that make the ℚ copy *the real thing* rather than an analogy, the three-zone classifier
`fpZoneQ` (FP-R2) and the correctness row tying its phosphorescence-dominant verdict to the ℝ-side
crossover of FP-C6 at cast parameters.

**Statement incident check (SV-R1 class, cross-cutting pitfall).** A `Rat.`-prefixed declaration
elaborates its own type inside namespace `Rat`, so an unqualified right-hand side would resolve to
the ℚ shadow and the row would silently become the vacuous identity `↑x = ↑x` (the SternVolmer
SV-R1 incident). Here the authority's right-hand sides are fully qualified
(`FluorPhos.phiF` / `FluorPhos.phiP`), so the rows are the intended bridges; this was confirmed by
`#print Rat.phiF_cast` / `#print Rat.phiP_cast` in the api probe scratch file, which show the
right-hand sides at the `PhotoLean.FluorPhos`-level definitions, not the `Rat` shadows. No
statement change was needed.

Statement authority: every definition body, theorem signature and inductive clause below is taken
word for word from `theories/FluorPhos/probes/FluorPhos-statement-skeleton.lean` (the frozen
Phase-1 authority, sha256 `b116adddea484896f7068c00141989d70871db4f51fe36749a2dbc44e24f4480` (re-frozen 2026-09-23; Phase-1 hash `2aa08f1c153b6494…`)`,
29 declarations), which transcribes `theories/FluorPhos/plan.md` §4; fidelity is checked by
`python3 theories/BEP/probes/bep-fidelity.py --theory FluorPhos`.

There is no unproved placeholder and no custom axiomatic declaration in this file. Note: the two
keyword literals that `proofs/scripts/check.sh --strict` scans for are deliberately not spelled
out anywhere in this file — the scan covers `PhotoLean/**/*.lean` including block comments, so
writing them (even in prose) would be a false-positive FAIL.

Plan locus: `theories/FluorPhos/plan.md` §4 (FP-R rows), sprint FP3; board
`theories/FluorPhos/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.FluorPhos.RatModel
    proofs/scripts/check.sh --strict PhotoLean.FluorPhos.RatModel
    proofs/scripts/axioms.sh PhotoLean.FluorPhos.RatModel PhotoLean.FluorPhos.Rat.phiF_cast
-/
import PhotoLean.FluorPhos.Basic
import PhotoLean.FluorPhos.Criterion

set_option autoImplicit false

namespace PhotoLean

namespace FluorPhos

namespace Rat

/-- Plan §4, FP-R1 (ℚ twin). The S₁ total decay over ℚ. -/
def s1Decay (kF kISC kIC : ℚ) : ℚ := kF + kISC + kIC

/-- Plan §4, FP-R1 (ℚ twin). The fluorescence yield over ℚ. -/
def phiF (kF kISC kIC : ℚ) : ℚ := kF / s1Decay kF kISC kIC

/-- Plan §4, FP-R1 (ℚ twin). The phosphorescence yield over ℚ. -/
def phiP (kF kISC kIC kP kNR : ℚ) : ℚ :=
  (kISC / s1Decay kF kISC kIC) * (kP / (kP + kNR))

/-- Plan §4, FP-R1. Cast coherence for `phiF`: the ℝ-side yield at cast parameters is the cast
of the ℚ-side yield. Route: `Rat.cast_div` / `Rat.cast_add` (names confirmed in the api probe).
-/
theorem phiF_cast (kF kISC kIC : ℚ) :
    ((phiF kF kISC kIC : ℚ) : ℝ) = FluorPhos.phiF (kF : ℝ) (kISC : ℝ) (kIC : ℝ) := by
  unfold phiF s1Decay PhotoLean.FluorPhos.phiF PhotoLean.FluorPhos.s1Decay
  push_cast
  ring

/-- Plan §4, FP-R1. Cast coherence for `phiP`. -/
theorem phiP_cast (kF kISC kIC kP kNR : ℚ) :
    ((phiP kF kISC kIC kP kNR : ℚ) : ℝ) =
      FluorPhos.phiP (kF : ℝ) (kISC : ℝ) (kIC : ℝ) (kP : ℝ) (kNR : ℝ) := by
  unfold phiP s1Decay PhotoLean.FluorPhos.phiP PhotoLean.FluorPhos.iscBranch
    PhotoLean.FluorPhos.t1BranchP PhotoLean.FluorPhos.s1Decay
  push_cast
  ring

end Rat

/-- Plan §4, FP-R2. The competition zone classifier: the crossover comparison of FP-C6 decided
over ℚ. -/
inductive FPZone where
  | fluorDominant
  | balanced
  | phosphorDominant
  deriving DecidableEq, Repr

/-- Plan §4, FP-R2. The classifier: compare `kISC·kP` with `kF·(kP+kNR)` (both ℚ — decidable
order). -/
def fpZoneQ (kF kISC kIC kP kNR : ℚ) : FPZone :=
  if kISC * kP = kF * (kP + kNR) then .balanced
  else if kF * (kP + kNR) < kISC * kP then .phosphorDominant
  else .fluorDominant

/-- Plan §4, FP-R2 (correctness). The ℚ classifier's phosphorescence-dominant verdict is the
ℝ-side crossover inequality at cast parameters. Route: unfold `fpZoneQ`, split the ifs, and
close by FP-C6 with `Rat.cast_lt` (the cast preserves the strict order). -/
theorem fpZoneQ_phosphorDominant_iff {kF kISC kIC kP kNR : ℚ}
    (h : FPData (kF : ℝ) (kISC : ℝ) (kIC : ℝ) (kP : ℝ) (kNR : ℝ)) :
    fpZoneQ kF kISC kIC kP kNR = .phosphorDominant ↔
      phiF (kF : ℝ) (kISC : ℝ) (kIC : ℝ) < phiP (kF : ℝ) (kISC : ℝ) (kIC : ℝ) (kP : ℝ) (kNR : ℝ) := by
  rw [crossover_isc h]
  unfold fpZoneQ
  by_cases h1 : kISC * kP = kF * (kP + kNR)
  · rw [if_pos h1]
    constructor
    · intro hbad
      exact absurd hbad (by simp)
    · intro hlt
      have h1' : (kISC : ℝ) * kP = (kF : ℝ) * (kP + kNR) := by exact_mod_cast h1
      exact absurd hlt (not_lt.mpr (le_of_eq h1'))
  · rw [if_neg h1]
    by_cases h2 : kF * (kP + kNR) < kISC * kP
    · rw [if_pos h2]
      constructor
      · intro _; exact_mod_cast h2
      · intro _; rfl
    · rw [if_neg h2]
      constructor
      · intro hbad
        exact absurd hbad (by simp)
      · intro hlt
        have h2' : (kISC : ℝ) * kP ≤ (kF : ℝ) * (kP + kNR) := by exact_mod_cast le_of_not_gt h2
        exact absurd hlt (not_lt.mpr h2')

end FluorPhos

end PhotoLean
