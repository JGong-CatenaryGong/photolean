/-
stokesShift-statement-skeleton.lean — the STATEMENT AUTHORITY of the StokesShift theory.

Statement-first (iron rule 2): every declaration below is the agreed statement verbatim; the theorem
bodies are placeholders on purpose (definitions carry their real bodies). This file must compile at
0 error
(`proofs/scripts/lake env lean theories/StokesShift/probes/StokesShift-statement-skeleton.lean`)
BEFORE any proof work starts; delivery replaces the bodies verbatim and
`python3 theories/BEP/probes/bep-fidelity.py --theory StokesShift` compares the delivered
signatures to this file word for word.

Plan: `theories/StokesShift/plan.md` (the frozen design; photophysics batch 2026-09-22, group B —
two-parabola basis, second theory of the group).
Milestones: SS-B (Basic: surface copies + kernel certificates + energy definitions),
SS-C (Criterion: the laws), SS-R (RatModel: the rational decision layer), SS-I (Instances: named
rational models and their zone verdicts).

The theory reads the kernel's equal-curvature two-parabola model optically: `q = 0` the
ground-state minimum geometry, `q = 1` the excited-state minimum geometry, vertical
(Franck–Condon) transitions at the minima. Vertical absorption is `lam + e00`, vertical emission
`e00 - lam`, and the Stokes shift is exactly `2 * lam`, independent of the 0-0 energy; the
emission window `lam < e00` closes at `e00 = lam`, the model's own boundary, tied back to
`PhotoLean.Marcus.InvertedRegion`. Literature anchors: `theories/StokesShift/LITERATURE.md`.
-/
import Mathlib
import PhotoLean.Kernel
import PhotoLean.Marcus.Basic

set_option autoImplicit false

namespace PhotoLean

namespace StokesShift

/-! ## SS-B — description layer (`PhotoLean/StokesShift/Basic.lean`) -/

/-- Ground-state potential-energy surface with reorganization energy `lam`: minimum at `q = 0`.
Plan section 4, row SS-B1. This theory's own copy, pinned to `PhotoLean.Kernel` by
`cert_s0Surface` (hard constraint 1). -/
noncomputable def s0Surface (lam q : ℝ) : ℝ := lam * q ^ 2

/-- Kernel certificate: the ground surface IS `PhotoLean.Kernel.reactantSurface`.
Plan section 4, row SS-B1. Proof route (plan §4): `rfl` (definitional copy). -/
theorem cert_s0Surface (lam q : ℝ) :
    s0Surface lam q = PhotoLean.Kernel.reactantSurface lam q := by
  sorry

/-- Excited-state potential-energy surface with reorganization energy `lam` and 0-0 energy
`e00`: minimum at `q = 1`, offset by `e00`. Plan section 4, row SS-B2. This theory's own copy,
pinned to `PhotoLean.Kernel` by `cert_s1Surface` (hard constraint 1). -/
noncomputable def s1Surface (lam e00 q : ℝ) : ℝ := lam * (q - 1) ^ 2 + e00

/-- Kernel certificate: the excited surface IS `PhotoLean.Kernel.productSurface`.
Plan section 4, row SS-B2. Proof route (plan §4): `rfl` (definitional copy). -/
theorem cert_s1Surface (lam e00 q : ℝ) :
    s1Surface lam e00 q = PhotoLean.Kernel.productSurface lam e00 q := by
  sorry

/-- Vertical (Franck–Condon) absorption energy from the ground minimum `q = 0`.
Plan section 4, row SS-B3. -/
noncomputable def absEnergy (lam e00 : ℝ) : ℝ := s1Surface lam e00 0 - s0Surface lam 0

/-- Vertical (Franck–Condon) emission energy from the excited minimum `q = 1`.
Plan section 4, row SS-B4. -/
noncomputable def emEnergy (lam e00 : ℝ) : ℝ := s1Surface lam e00 1 - s0Surface lam 1

/-- The Stokes shift: absorption energy minus emission energy. Plan section 4, row SS-B5. -/
noncomputable def stokesShift (lam e00 : ℝ) : ℝ := absEnergy lam e00 - emEnergy lam e00

/-! ## SS-C — law layer (`PhotoLean/StokesShift/Criterion.lean`) -/

/-- Absorption at the ground minimum costs exactly `lam + e00`.
Plan section 4, row SS-C1. Proof route (plan §5): `unfold` + `ring`. -/
theorem absEnergy_eq (lam e00 : ℝ) : absEnergy lam e00 = lam + e00 := by
  sorry

/-- Emission at the excited minimum releases exactly `e00 - lam`.
Plan section 4, row SS-C2. Proof route (plan §5): `unfold` + `ring`. -/
theorem emEnergy_eq (lam e00 : ℝ) : emEnergy lam e00 = e00 - lam := by
  sorry

/-- **The headline.** The Stokes shift is exactly twice the reorganization energy, independent
of the 0-0 energy. Plan section 4, row SS-C3. Proof route (plan §5): `unfold` + `ring`. -/
theorem stokesShift_eq_two_lam (lam e00 : ℝ) : stokesShift lam e00 = 2 * lam := by
  sorry

/-- Positivity of the shift is exactly physical curvature.
Plan section 4, row SS-C4. Proof route (plan §5): rewrite by SS-C3, then `linarith`. -/
theorem stokesShift_pos_iff (lam e00 : ℝ) : 0 < stokesShift lam e00 ↔ 0 < lam := by
  sorry

/-- The emission window: the vertical emission photon energy is positive exactly when
`lam < e00`. Plan section 4, row SS-C5. Proof route (plan §5): rewrite by SS-C2, then
`linarith` (`sub_pos`). -/
theorem emEnergy_pos_iff (lam e00 : ℝ) : 0 < emEnergy lam e00 ↔ lam < e00 := by
  sorry

/-- Mirror symmetry about the 0-0 energy: the mean of absorption and emission is `e00`.
Plan section 4, row SS-C6. Proof route (plan §5): `unfold` + `ring`. -/
theorem mirror_midpoint (lam e00 : ℝ) : (absEnergy lam e00 + emEnergy lam e00) / 2 = e00 := by
  sorry

/-- The two Franck–Condon offsets from `e00` are equal.
Plan section 4, row SS-C7. Proof route (plan §5): `unfold` + `ring`. -/
theorem abs_sub_e00_eq_e00_sub_em (lam e00 : ℝ) :
    absEnergy lam e00 - e00 = e00 - emEnergy lam e00 := by
  sorry

/-- The emission window's edge: at `e00 = lam` the vertical emission energy vanishes.
Plan section 4, row SS-C8 (edge). Proof route (plan §5): `unfold` + `ring`. -/
theorem emission_window_closes (lam : ℝ) : emEnergy lam lam = 0 := by
  sorry

/-- Beyond the window's edge the vertical emission is negative (no photon): the model's own
boundary. Plan section 4, row SS-C8 (corner). Proof route (plan §5): `unfold` + `linarith`. -/
theorem inverted_corner {lam e00 : ℝ} (h : e00 < lam) : emEnergy lam e00 < 0 := by
  sorry

/-- **The boundary identification (corrected form).** The emission window — a positive
vertical photon exists — IS the Marcus inverted region read at the gap; imports
`PhotoLean.Marcus.Basic`. Plan section 4, row SS-C9, **amended at Sprint 0** (plan §3.1 entry
1): the plan's first form `e00 < lam ↔ InvertedRegion lam e00` unfolds to `e00 < lam ↔
lam < e00`, which is FALSE (kernel-checked counterexample `lam = 1, e00 = 2` in
`StokesShift-api-probe.lean`); the physically correct reading is that the open emission window
(`0 < emEnergy`, i.e. `lam < e00`) coincides with the inverted region — in this model the
regime where a vertical photon exists is exactly the Marcus-inverted regime of the
nonradiative twin. Proof route: unfold `emEnergy` (SS-B4), `s1Surface`, `s0Surface`; both sides
reduce to `lam < e00` by `ring_nf`-level algebra. -/
theorem emEnergy_pos_iff_inverted (lam e00 : ℝ) :
    0 < emEnergy lam e00 ↔ PhotoLean.Marcus.InvertedRegion lam e00 := by
  sorry

/-! ## SS-R — the rational decision layer (`PhotoLean/StokesShift/RatModel.lean`) -/

namespace Rat

/-- The computable ℚ shadow of the ground surface. Plan section 4, row SS-R1.
Pure polynomial — no transcendentals anywhere in the layer. -/
def s0Surface (lam q : ℚ) : ℚ := lam * q ^ 2

/-- The computable ℚ shadow of the excited surface. Plan section 4, row SS-R1. -/
def s1Surface (lam e00 q : ℚ) : ℚ := lam * (q - 1) ^ 2 + e00

/-- The computable ℚ shadow of the absorption energy. Plan section 4, row SS-R1. -/
def absEnergy (lam e00 : ℚ) : ℚ := s1Surface lam e00 0 - s0Surface lam 0

/-- The computable ℚ shadow of the emission energy. Plan section 4, row SS-R1. -/
def emEnergy (lam e00 : ℚ) : ℚ := s1Surface lam e00 1 - s0Surface lam 1

/-- The computable ℚ shadow of the Stokes shift. Plan section 4, row SS-R1. -/
def stokesShift (lam e00 : ℚ) : ℚ := absEnergy lam e00 - emEnergy lam e00

/-- Cast coherence: the ℚ shadow computes the real ground surface at cast parameters.
Plan section 4, row SS-R1 (cast-coherence row; name assigned in Sprint 0).
Proof route: `unfold` + cast simp (`norm_cast`, dry-run in the api-probe). -/
theorem s0Surface_cast (lam q : ℚ) :
    (s0Surface lam q : ℝ) = PhotoLean.StokesShift.s0Surface (lam : ℝ) (q : ℝ) := by
  sorry

/-- Cast coherence: the ℚ shadow computes the real excited surface at cast parameters.
Plan section 4, row SS-R1 (cast-coherence row; name assigned in Sprint 0). -/
theorem s1Surface_cast (lam e00 q : ℚ) :
    (s1Surface lam e00 q : ℝ) = PhotoLean.StokesShift.s1Surface (lam : ℝ) (e00 : ℝ) (q : ℝ) := by
  sorry

/-- Cast coherence: the ℚ shadow computes the real absorption energy at cast parameters.
Plan section 4, row SS-R1 (cast-coherence row; name assigned in Sprint 0). -/
theorem absEnergy_cast (lam e00 : ℚ) :
    (absEnergy lam e00 : ℝ) = PhotoLean.StokesShift.absEnergy (lam : ℝ) (e00 : ℝ) := by
  sorry

/-- Cast coherence: the ℚ shadow computes the real emission energy at cast parameters.
Plan section 4, row SS-R1 (cast-coherence row; name assigned in Sprint 0). -/
theorem emEnergy_cast (lam e00 : ℚ) :
    (emEnergy lam e00 : ℝ) = PhotoLean.StokesShift.emEnergy (lam : ℝ) (e00 : ℝ) := by
  sorry

/-- Cast coherence: the ℚ shadow computes the real Stokes shift at cast parameters.
Plan section 4, row SS-R1 (cast-coherence row; name assigned in Sprint 0). -/
theorem stokesShift_cast (lam e00 : ℚ) :
    (stokesShift lam e00 : ℝ) = PhotoLean.StokesShift.stokesShift (lam : ℝ) (e00 : ℝ) := by
  sorry

end Rat

/-- The three-zone verdict of the Stokes-shift model. Plan section 4, row SS-R2. -/
inductive SSZone | normalEmission | zeroPhoton | invertedEmission
  deriving DecidableEq

/-- The zone classifier at rational parameters: positive emission (`lam < e00`) is
`normalEmission`, vanishing emission (`lam = e00`) is `zeroPhoton`, negative emission
(`e00 < lam`) is `invertedEmission`. Plan section 4, row SS-R2 (comparisons decidable on ℚ;
instance verdicts by `decide`). -/
def ssZoneQ (lam e00 : ℚ) : SSZone :=
  if lam < e00 then SSZone.normalEmission
  else if e00 < lam then SSZone.invertedEmission
  else SSZone.zeroPhoton

/-- Zone correctness at cast parameters, `normalEmission` row. Plan section 4, row SS-R2
(the plan's "correctness rows" pattern instantiated per constructor; name assigned in
Sprint 0). Proof route: unfold the classifier, then `Rat.cast_lt`. -/
theorem ssZoneQ_eq_normalEmission_iff (lam e00 : ℚ) :
    ssZoneQ lam e00 = .normalEmission ↔ (lam : ℝ) < (e00 : ℝ) := by
  sorry

/-- Zone correctness at cast parameters, `zeroPhoton` row. Plan section 4, row SS-R2
(the plan's "correctness rows" pattern instantiated per constructor; name assigned in
Sprint 0). Proof route: unfold the classifier, then `Rat.cast_inj`. -/
theorem ssZoneQ_eq_zeroPhoton_iff (lam e00 : ℚ) :
    ssZoneQ lam e00 = .zeroPhoton ↔ (lam : ℝ) = (e00 : ℝ) := by
  sorry

/-- Zone correctness at cast parameters, `invertedEmission` row — the row shape the plan
writes explicitly. Plan section 4, row SS-R2. Proof route: unfold the classifier, then
`Rat.cast_lt`. -/
theorem ssZoneQ_eq_invertedEmission_iff (lam e00 : ℚ) :
    ssZoneQ lam e00 = .invertedEmission ↔ (e00 : ℝ) < (lam : ℝ) := by
  sorry

/-! ## SS-I — instances and verdicts (`PhotoLean/StokesShift/Instances.lean`) -/

/-- The mirror-symmetric dye (`lam = 1/2`, `e00 = 2`): absorption `5/2`, emission `3/2`,
shift `1`, midpoint `2`; zone `normalEmission`. Plan section 4, row SS-I1. Facts about printed
rationals, decided by `norm_num`/`decide`. -/
theorem mirrorDye :
    Rat.absEnergy (1 / 2) 2 = 5 / 2 ∧ Rat.emEnergy (1 / 2) 2 = 3 / 2 ∧
    Rat.stokesShift (1 / 2) 2 = 1 ∧ (Rat.absEnergy (1 / 2) 2 + Rat.emEnergy (1 / 2) 2) / 2 = 2 ∧
    ssZoneQ (1 / 2) 2 = .normalEmission := by
  sorry

/-- Large relaxation (`lam = 3/2`, `e00 = 2`): emission `1/2`, shift `3` — still emitting.
Plan section 4, row SS-I2. Facts about printed rationals, decided by `norm_num`. -/
theorem largeRelaxation :
    Rat.emEnergy (3 / 2) 2 = 1 / 2 ∧ Rat.stokesShift (3 / 2) 2 = 3 := by
  sorry

/-- The inverted corner: at `(lam, e00) = (2, 2)` the window edge (`zeroPhoton`), and at
`(3, 2)` beyond it (`invertedEmission`) — the refuting pair for "emission is always positive"
(a negative result registered as an instance verdict). Plan section 4, row SS-I3. Zone
verdicts decided by `decide`. -/
theorem invertedCorner :
    ssZoneQ 2 2 = .zeroPhoton ∧ ssZoneQ 3 2 = .invertedEmission := by
  sorry

/-- **The negative result, finalized (Phase 3)**: the FIRST frozen form of SS-C9 is refuted by
the kernel — the plan's §3.1 entry 1 records that `e00 < lam ↔ Marcus.InvertedRegion lam e00`
unfolds to `e00 < lam ↔ lam < e00`, which is false; this row delivers that refutation as a
theorem with its parameter witness (`lam = 1, e00 = 2`: `2 < 1` false, `InvertedRegion 1 2`
true). Plan section 4, row SS-I4 (added in the Phase-3 negative-result finalization). -/
theorem invertedCorner_firstForm_refuted :
    ¬ (∀ lam e00 : ℝ, (e00 < lam ↔ PhotoLean.Marcus.InvertedRegion lam e00)) := by
  sorry

end StokesShift

end PhotoLean
