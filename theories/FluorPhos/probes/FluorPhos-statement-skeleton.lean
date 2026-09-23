/-
FluorPhos-statement-skeleton.lean — the STATEMENT AUTHORITY of the FluorPhos theory
(fluorescence–phosphorescence competition).

Statement-first (iron rule 2): every declaration below is the agreed statement verbatim from
`theories/FluorPhos/plan.md` §4; theorem bodies are placeholders on purpose (Phase 1). This file
must compile at 0 error
(`proofs/scripts/lake env lean theories/FluorPhos/probes/FluorPhos-statement-skeleton.lean`)
BEFORE any proof work starts; delivery replaces the bodies verbatim and
`python3 theories/BEP/probes/bep-fidelity.py --theory FluorPhos` compares the delivered
signatures to this file word for word.

Plan: `theories/FluorPhos/plan.md`. Milestones: FP1 (Basic), FP2 (Criterion), FP3 (RatModel),
FP4 (Instances). The design-time correction of FP-C4 (the losslessness boundary is
`kIC = 0 ∧ (kISC = 0 ∨ kNR = 0)`, not the naive `kIC = 0 ∧ kNR = 0`) is recorded in the plan
as §3.1 entry 0 and is carried by the corrected row below.

This probe lives outside the strict scan range (`SOURCE_DIRS` is `PhotoLean`); placeholder
bodies are Phase-1 registration, each recorded on the board `theories/FluorPhos/TASKS.md`.
-/
import Mathlib

set_option autoImplicit false

namespace PhotoLean

namespace FluorPhos

/-! ## FP1 — description layer (`PhotoLean/FluorPhos/Basic.lean`) -/

/-- Plan §4, FP-B1. Total decay rate of the S₁ state: fluorescence + intersystem crossing +
internal conversion. -/
def s1Decay (kF kISC kIC : ℝ) : ℝ := kF + kISC + kIC

/-- Plan §4, FP-B2. Fluorescence quantum yield: the S₁ radiative branch. -/
noncomputable def phiF (kF kISC kIC : ℝ) : ℝ := kF / s1Decay kF kISC kIC

/-- Plan §4, FP-B3. The S₁→T₁ intersystem-crossing branch. -/
noncomputable def iscBranch (kF kISC kIC : ℝ) : ℝ := kISC / s1Decay kF kISC kIC

/-- Plan §4, FP-B4. The T₁ radiative (phosphorescence) branch. -/
noncomputable def t1BranchP (kP kNR : ℝ) : ℝ := kP / (kP + kNR)

/-- Plan §4, FP-B5. Phosphorescence quantum yield: the cascade product of the S₁→T₁ branch and
the T₁ radiative branch. -/
noncomputable def phiP (kF kISC kIC kP kNR : ℝ) : ℝ :=
  iscBranch kF kISC kIC * t1BranchP kP kNR

/-- Plan §4, FP-B6. The premise bundle: nonnegative rates, positive total decay of S₁, positive
total decay of T₁ (engine rule 3 — every positivity is an explicit hypothesis). -/
structure FPData (kF kISC kIC kP kNR : ℝ) : Prop where
  kF_nonneg : 0 ≤ kF
  kISC_nonneg : 0 ≤ kISC
  kIC_nonneg : 0 ≤ kIC
  kP_nonneg : 0 ≤ kP
  kNR_nonneg : 0 ≤ kNR
  s1Decay_pos : 0 < s1Decay kF kISC kIC
  t1Decay_pos : 0 < kP + kNR

/-! ## FP2 — law layer (`PhotoLean/FluorPhos/Criterion.lean`) -/

/-- Plan §4, FP-C1. The phosphorescence yield as a single fraction. Route: `field_simp` + `ring`.
-/
theorem phiP_eq {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR) :
    phiP kF kISC kIC kP kNR = kISC * kP / (s1Decay kF kISC kIC * (kP + kNR)) := by
  sorry

/-- Plan §4, FP-C2. **The competition law**: the phosphorescence-to-fluorescence ratio is the
intersystem-crossing odds times the triplet radiative branch. Route: `field_simp` + `ring`. -/
theorem phiP_div_phiF {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR)
    (hkF : 0 < kF) :
    phiP kF kISC kIC kP kNR / phiF kF kISC kIC = (kISC / kF) * t1BranchP kP kNR := by
  sorry

/-- Plan §4, FP-C3. The two luminescence yields never exceed unity in total. Route:
`div_add_div` normal form, `div_le_one`, the nonnegativity fields of `FPData`. -/
theorem phiF_add_phiP_le_one {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR) :
    phiF kF kISC kIC + phiP kF kISC kIC kP kNR ≤ 1 := by
  sorry

/-- Plan §4, FP-C4 (corrected at design time — plan §3.1 entry 0). **The losslessness
boundary**: the two yields exhaust unity exactly when there is no S₁ internal-conversion loss
and the triplet is either never populated or perfectly radiative. Route: the numerator identity
`phiF + phiP = 1 ↔ kISC·kNR + kIC·(kP+kNR) = 0` under the bundle, then the nonnegativity split
and `h.t1Decay_pos`. -/
theorem phiF_add_phiP_eq_one_iff {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR) :
    phiF kF kISC kIC + phiP kF kISC kIC kP kNR = 1 ↔ kIC = 0 ∧ (kISC = 0 ∨ kNR = 0) := by
  sorry

/-- Plan §4, FP-C5 (first half). The heavy-atom direction on fluorescence: more intersystem
crossing, less fluorescence. Route: `div_lt_div_of_lt_...` on the denominator / `div_lt_iff`
chain with `h.s1Decay_pos` and the primed bundle. -/
theorem phiF_strictAnti_isc {kF kISC kISC' kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR)
    (h' : FPData kF kISC' kIC kP kNR) (hkF : 0 < kF) (hlt : kISC < kISC') :
    phiF kF kISC' kIC < phiF kF kISC kIC := by
  sorry

/-- Plan §4, FP-C5 (second half). The heavy-atom direction on phosphorescence: more intersystem
crossing, more phosphorescence. Route: `phiP_eq` both sides, clear the positive denominators, and
reduce to `kP·(kISC' − kISC)·(kF + kIC) > 0`.

**Re-frozen 2026-09-23 (plan §3.1 entry 2; counterexample found by the lead while the row resisted
proof).** The first frozen form carried only `FPData`, `0 < kP` and `kISC < kISC'`, and it is
**FALSE**: at `kF = 0, kIC = 0` (an admissible bundle: the S₁ state is populated only into the
triplet) the yield collapses to `kP/(kP+kNR)`, independent of `kISC` — kernel-checked counterexample
at `kISC = 1 → 2` (both sides `1/2`). The load-bearing premise is exactly `0 < kF + kIC` (the
non-triplet S₁ decay channel): with it the map `kISC ↦ phiP` is strictly increasing, without it it
is constant. The premise is added; nothing else changes. -/
theorem phiP_strictMono_isc {kF kISC kISC' kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR)
    (hkP : 0 < kP) (h0 : 0 < kF + kIC) (hlt : kISC < kISC') :
    phiP kF kISC kIC kP kNR < phiP kF kISC' kIC kP kNR := by
  sorry

/-- Plan §4, FP-C6. **The crossover in closed form**: phosphorescence overtakes fluorescence
exactly when `kISC·kP` exceeds `kF·(kP+kNR)`. Route: `div_lt_div_iff` chains with
`h.s1Decay_pos`, `h.t1Decay_pos`, `hkF`, `hkP`. -/
theorem crossover_isc {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR) :
    phiF kF kISC kIC < phiP kF kISC kIC kP kNR ↔ kF * (kP + kNR) < kISC * kP := by
  sorry

/-- Plan §4, FP-C6 (threshold form). The same crossover solved for `kISC`. Route: FP-C6's
statement divided through by `kP` (`lt_div_iff` with `hkP`). -/
theorem crossover_isc_threshold {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR)
    (hkP : 0 < kP) :
    phiF kF kISC kIC < phiP kF kISC kIC kP kNR ↔ kF * (kP + kNR) / kP < kISC := by
  sorry

/-- Plan §4, FP-C7. **The El-Sayed boundary as a model row**: with the intersystem channel shut
there is no phosphorescence, whatever the triplet rates. Route: `iscBranch` vanishes at
`kISC = 0` (`zero_div`). -/
theorem hso_zero_no_phosphorescence {kF kIC kP kNR : ℝ} :
    phiP kF 0 kIC kP kNR = 0 := by
  sorry

/-- Plan §4, FP-C8. **Non-vacuity of the competition**: both channels live at a concrete
witness (`kF = kISC = kP = 1`, `kIC = kNR = 1`: `phiF = 1/3`, `phiP = 1/6`). The triple
conjunct blocks the trivial-witness failure mode (the M1 lesson). Route: `refine ⟨1, 1, 1, 1,
1, ?_, ?_, ?_⟩` with `norm_num [FPData, phiF, phiP, ...]` verdicts. -/
theorem nonvacuous_competition :
    ∃ kF kISC kIC kP kNR : ℝ, FPData kF kISC kIC kP kNR ∧
      0 < phiF kF kISC kIC ∧ 0 < phiP kF kISC kIC kP kNR := by
  sorry

/-! ## FP3 — rational decision layer (`PhotoLean/FluorPhos/RatModel.lean`) -/

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
  sorry

/-- Plan §4, FP-R1. Cast coherence for `phiP`. -/
theorem phiP_cast (kF kISC kIC kP kNR : ℚ) :
    ((phiP kF kISC kIC kP kNR : ℚ) : ℝ) =
      FluorPhos.phiP (kF : ℝ) (kISC : ℝ) (kIC : ℝ) (kP : ℝ) (kNR : ℝ) := by
  sorry

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
  sorry

/-! ## FP4 — named instances (`PhotoLean/FluorPhos/Instances.lean`) -/

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
  sorry

/-- Plan §4, FP-I2. The eosin-like heavy-atom representative model (`kISC = 10`). -/
def eosinLike : ℚ × ℚ × ℚ × ℚ × ℚ := (1, 10, 1 / 2, 1, 1)

/-- Plan §4, FP-I2 (verdict). Phosphorescence-competitive: the crossover premise
`kF·(kP+kNR) < kISC·kP` holds (`2 < 10`) and the zone is `phosphorDominant`. -/
theorem eosinLike_verdict :
    (1 : ℝ) * (1 + 1) < 10 * 1 ∧
      fpZoneQ 1 10 (1 / 2) 1 1 = .phosphorDominant := by
  sorry

/-- Plan §4, FP-I3. The crossover witness pair: two models straddling the FP-C6 threshold
(`kISC = 2` sits exactly at `kF·(kP+kNR)/kP = 2` — balanced; `kISC = 3` is past it). -/
theorem crossoverWitness_verdict :
    fpZoneQ 1 2 (1 / 2) 1 1 = .balanced ∧ fpZoneQ 1 3 (1 / 2) 1 1 = .phosphorDominant := by
  sorry

end FluorPhos

end PhotoLean
