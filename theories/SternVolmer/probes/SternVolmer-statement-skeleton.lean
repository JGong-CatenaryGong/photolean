/-
SternVolmer-statement-skeleton.lean — the STATEMENT AUTHORITY of the SternVolmer theory.

Statement-first (iron rule 2): every declaration below is the agreed statement verbatim; the
theorem bodies are placeholders on purpose (definitions carry their real bodies). This file must
compile at 0 error
(`proofs/scripts/lake env lean theories/SternVolmer/probes/SternVolmer-statement-skeleton.lean`)
BEFORE any proof work starts; delivery replaces the bodies verbatim and
`python3 theories/BEP/probes/bep-fidelity.py --theory SternVolmer` compares the delivered
signatures to this file word for word.

Plan: `theories/SternVolmer/plan.md`. Milestones: SV1 (Basic), SV2 (Criterion — the D1 core),
SV3 (RatModel), SV4 (Instances). Batch: the photophysics subgraph (human request 2026-09-22),
group A (rate-cascade basis).

The theory adjudicates D1 — the static-vs-dynamic Stern–Volmer identifiability boundary:
both mechanisms give exactly linear intensity plots (`svRatioDyn_linear`, `svRatioStat_linear`);
the intensity-only observation map is not injective on the two-mechanism model space
(`intensity_curve_coincidence`, with the kernel-checked witness pair `conflation_witness`); the
exact identifiability boundary is the lifetime channel (`lifetimeTracks_iff_dyn`: the lifetime
ratio tracks the intensity ratio **iff** the mechanism is dynamic, with `0 < Ka` load-bearing);
and coexistence is positively witnessed by upward curvature
(`curvature_witnesses_coexistence`). Self-contained: `Mathlib` only, no `Real.exp`, no `Finset`
— the lightest module of the batch (plan §5, §11).
-/
import Mathlib

set_option autoImplicit false

namespace PhotoLean

namespace SternVolmer

/-! ## SV-B — description layer (`PhotoLean/SternVolmer/Basic.lean`) -/

/-- Decay rate under dynamic (collisional) quenching: the intrinsic decay `k0` plus the
concentration-dependent channel `kq·q`. Plan section 4, row SV-B1. -/
noncomputable def dynDecay (k0 kq q : ℝ) : ℝ := k0 + kq * q

/-- The dynamic intensity ratio `I₀/I`: the yield ratio `kr/decay(q)` over `kr/decay(0)`.
Plan section 4, row SV-B2. -/
noncomputable def svRatioDyn (k0 kq q : ℝ) : ℝ := dynDecay k0 kq q / k0

/-- The dynamic lifetime ratio `τ₀/τ`. The body is identical to `svRatioDyn` — that identity
**is** the physical claim of the dynamic mechanism (both observables are the decay ratio);
registered here and in the SV-C1 docstring. Plan section 4, row SV-B3. -/
noncomputable def tauRatioDyn (k0 kq q : ℝ) : ℝ := dynDecay k0 kq q / k0

/-- The static intensity ratio (inverse free fraction `1 + Ka·q`): ground-state complexation
removes emitters by the linearized-binding isotherm `free fraction = 1/(1 + Ka·q)`.
Plan section 4, row SV-B4. -/
noncomputable def svRatioStat (Ka q : ℝ) : ℝ := 1 + Ka * q

/-- The static lifetime ratio: the observed (free) fluorophores decay unchanged.
Plan section 4, row SV-B5. -/
noncomputable def tauRatioStat (Ka q : ℝ) : ℝ := 1

/-- The Stern–Volmer constant `KSV k0 kq = kq / k0` (= `kq·τ₀`). Plan section 4, row SV-B6. -/
noncomputable def KSV (k0 kq : ℝ) : ℝ := kq / k0

/-- The combined mechanism (dynamic quenching of the free fraction): the intensity ratio
factors as the dynamic ratio times the static ratio. Plan section 4, row SV-B7. -/
noncomputable def svRatioBoth (k0 kq Ka q : ℝ) : ℝ := svRatioDyn k0 kq q * svRatioStat Ka q

/-- The mechanism tag of the two-mechanism model space. Plan section 4, row SV-B8. -/
inductive Mech | dyn | stat

/-- The mechanism-tagged intensity ratio — the observation map of the two-mechanism model
space. Plan section 4, row SV-B8. -/
noncomputable def svRatioOf (m : Mech) (k0 kq Ka q : ℝ) : ℝ :=
  match m with
  | Mech.dyn => svRatioDyn k0 kq q
  | Mech.stat => svRatioStat Ka q

/-- The mechanism-tagged lifetime ratio — the discriminating channel of the two-mechanism
model space. Plan section 4, row SV-B8. -/
noncomputable def tauRatioOf (m : Mech) (k0 kq Ka q : ℝ) : ℝ :=
  match m with
  | Mech.dyn => tauRatioDyn k0 kq q
  | Mech.stat => tauRatioStat Ka q

/-- The discriminating observable: the lifetime ratio tracks the intensity ratio at every
positive concentration. Plan section 4, row SV-B9. -/
def LifetimeTracks (m : Mech) (k0 kq Ka : ℝ) : Prop :=
  ∀ q, 0 < q → tauRatioOf m k0 kq Ka q = svRatioOf m k0 kq Ka q

/-! ## SV-C — laws and the D1 core (`PhotoLean/SternVolmer/Criterion.lean`) -/

/-- The dynamic mechanism's identity: the lifetime ratio IS the intensity ratio at every
concentration — definitional (the two bodies are identical); the content is the contrast SV-C2.
Plan section 4, row SV-C1. Proof route: `rfl` (definitional unfolding row). -/
theorem dyn_lifetime_tracks_intensity (k0 kq : ℝ) :
    ∀ q, tauRatioDyn k0 kq q = svRatioDyn k0 kq q := by
  sorry

/-- The static lifetime channel is flat at every concentration. Plan section 4, row SV-C2.
Proof route: `rfl` (definitional unfolding row). -/
theorem stat_lifetime_flat (Ka : ℝ) : ∀ q, tauRatioStat Ka q = 1 := by
  sorry

/-- The static lifetime channel separates from the intensity channel at every positive
concentration — the discriminator's static side. Plan section 4, row SV-C2.
Proof route: `tauRatioStat` unfolds to `1`; `1 ≠ 1 + Ka·q` from `0 < Ka·q` (`mul_pos`). -/
theorem stat_lifetime_separates (Ka q : ℝ) (hKa : 0 < Ka) (hq : 0 < q) :
    tauRatioStat Ka q ≠ svRatioStat Ka q := by
  sorry

/-- The dynamic plot is exactly linear with slope `KSV` and intercept `1`.
Plan section 4, row SV-C3. Proof route: unfold, `field_simp` at `hk0`, `ring` (plan §5). -/
theorem svRatioDyn_linear (k0 kq q : ℝ) (hk0 : k0 ≠ 0) :
    svRatioDyn k0 kq q = 1 + KSV k0 kq * q := by
  sorry

/-- The static plot is exactly linear with slope `Ka` and intercept `1` — definitional;
registered so that "both linear" is a theorem pair, not a slogan. Plan section 4, row SV-C4.
Proof route: `rfl` (definitional unfolding row). -/
theorem svRatioStat_linear (Ka q : ℝ) : svRatioStat Ka q = 1 + Ka * q := by
  sorry

/-- The dynamic ratio at zero quencher is `1` (intercept calibration).
Plan section 4, row SV-C5. Proof route: unfold, `field_simp` at `hk0`. -/
theorem svRatioDyn_at_zero (k0 kq : ℝ) (hk0 : k0 ≠ 0) : svRatioDyn k0 kq 0 = 1 := by
  sorry

/-- The static ratio at zero quencher is `1` (intercept calibration).
Plan section 4, row SV-C5. Proof route: `ring` after unfolding. -/
theorem svRatioStat_at_zero (Ka : ℝ) : svRatioStat Ka 0 = 1 := by
  sorry

/-- The dynamic plot is strictly increasing in the quencher concentration.
Plan section 4, row SV-C6. Proof route: `mul_lt_mul_of_pos_left` + `add_lt_add_left` on the
linear form, the division by the positive `k0` via `div_lt_div_iff₀`-free `lt` algebra
(plan §5 monotonicity rows). -/
theorem svRatioDyn_strictMono_q (k0 kq q₁ q₂ : ℝ) (hk0 : 0 < k0) (hkq : 0 < kq)
    (h : q₁ < q₂) : svRatioDyn k0 kq q₁ < svRatioDyn k0 kq q₂ := by
  sorry

/-- The static plot is strictly increasing in the quencher concentration.
Plan section 4, row SV-C6. Proof route: `mul_lt_mul_of_pos_left h hKa` then
`add_lt_add_left` (plan §5). -/
theorem svRatioStat_strictMono_q (Ka q₁ q₂ : ℝ) (hKa : 0 < Ka) (h : q₁ < q₂) :
    svRatioStat Ka q₁ < svRatioStat Ka q₂ := by
  sorry

/-- **D1a, the conflation.** Matched parameters (`KSV k0 kq = Ka`) give pointwise-identical
intensity plots at **every** concentration: the intensity-only observation map is not injective
on the mechanism space. Plan section 4, row SV-C7.
Proof route: `svRatioDyn_linear` then rewrite along `hK` (plan §5: field algebra). -/
theorem intensity_curve_coincidence {k0 kq Ka : ℝ} (hk0 : k0 ≠ 0) (hK : KSV k0 kq = Ka) :
    ∀ q, svRatioDyn k0 kq q = svRatioStat Ka q := by
  sorry

/-- **D1b, the boundary.** Within the two-mechanism model space, lifetime-tracking decides the
mechanism exactly. Weakest-premise note (plan §4): no hypothesis on `kq` — at `kq = 0` the
dynamic plot is flat and tracking still holds; `0 < Ka` is load-bearing — at `Ka = 0` the
static plot is flat and tracking holds there too. Plan section 4, row SV-C8.
**Re-frozen 2026-09-23 (plan §3.1 entry 2; Phase-3 premise audit, verifier run 1).** The premise
`0 < k0` is dropped: the delivered proof never consumed it (the dynamic side tracks
definitionally by SV-C1; the static refutation uses only `0 < Ka`), and the iff survives at
`k0 = 0` — under totalized division the dynamic side's two ratios agree there. Scratch probe:
`.lake/tmp/prover_c_phase3_svc8_probe.lean` (exit 0).
Proof route: cases on `m`; `LifetimeTracks Mech.dyn` holds by SV-C1; `¬ LifetimeTracks Mech.stat`
instantiates the universal at `q = 1` and refutes by `stat_lifetime_separates` (plan §5). -/
theorem lifetimeTracks_iff_dyn {k0 kq Ka : ℝ} (hKa : 0 < Ka) :
    ∀ m : Mech, (LifetimeTracks m k0 kq Ka ↔ m = Mech.dyn) := by
  sorry

/-- The combined-mechanism plot in closed form: linear terms plus the `KSV·Ka·q²` cross term —
the algebraic source of upward curvature. Plan section 4, row SV-C9.
Proof route: unfold, `field_simp` at `hk0`, `ring` (plan §5). -/
theorem svRatioBoth_eq (k0 kq Ka q : ℝ) (hk0 : k0 ≠ 0) :
    svRatioBoth k0 kq Ka q = 1 + (KSV k0 kq + Ka) * q + KSV k0 kq * Ka * q ^ 2 := by
  sorry

/-- The second difference of the combined plot is the constant `2·KSV·Ka·h²`.
Plan section 4, row SV-C9. Proof route: `svRatioBoth_eq` three times, then `ring`. -/
theorem svRatioBoth_secondDifference (k0 kq Ka : ℝ) (hk0 : k0 ≠ 0) (x h : ℝ) :
    svRatioBoth k0 kq Ka (x + h) - 2 * svRatioBoth k0 kq Ka x + svRatioBoth k0 kq Ka (x - h)
      = 2 * KSV k0 kq * Ka * h ^ 2 := by
  sorry

/-- The second difference of the dynamic plot vanishes — no single mechanism curves.
Plan section 4, row SV-C9. Proof route: `svRatioDyn_linear` three times, then `ring`. -/
theorem svRatioDyn_secondDifference (k0 kq : ℝ) (hk0 : k0 ≠ 0) (x h : ℝ) :
    svRatioDyn k0 kq (x + h) - 2 * svRatioDyn k0 kq x + svRatioDyn k0 kq (x - h) = 0 := by
  sorry

/-- The second difference of the static plot vanishes — no single mechanism curves.
Plan section 4, row SV-C9. Proof route: `svRatioStat_linear` three times, then `ring`. -/
theorem svRatioStat_secondDifference (Ka x h : ℝ) :
    svRatioStat Ka (x + h) - 2 * svRatioStat Ka x + svRatioStat Ka (x - h) = 0 := by
  sorry

/-- **D1c, coexistence is positively witnessed.** Upward curvature (a strictly positive second
difference) occurs under the combined mechanism whenever all three constants are positive and
the step is nonzero — and by the two vanishing rows above, no single mechanism produces it.
Plan section 4, row SV-C9. Proof route: `svRatioBoth_secondDifference` + positivity of
`2·KSV·Ka·h²` (`div_pos`, `mul_pos`, `sq_pos_of_ne_zero`). -/
theorem curvature_witnesses_coexistence (k0 kq Ka x h : ℝ) (hk0 : 0 < k0) (hkq : 0 < kq)
    (hKa : 0 < Ka) (hh : h ≠ 0) :
    0 < svRatioBoth k0 kq Ka (x + h) - 2 * svRatioBoth k0 kq Ka x +
      svRatioBoth k0 kq Ka (x - h) := by
  sorry

/-- **D1 verdict** — one row with the three conjuncts: both plots linear (SV-C3/C4 at the
parameters, paired pointwise under one universal), the coincidence (SV-C7 at `Ka = KSV k0 kq`,
instantiated by `refl`/the hypothesis chain), and the boundary (SV-C8).
Plan section 4, row SV-C10. The persistence explanation is prose in RESULTS (Phase 3): routine
practice measures intensity only; lifetime resolution is a separate experiment. -/
theorem d1_verdict {k0 kq Ka : ℝ} (hk0 : 0 < k0) (hkq : 0 < kq) (hKa : 0 < Ka) :
    (∀ q, svRatioDyn k0 kq q = 1 + KSV k0 kq * q ∧ svRatioStat Ka q = 1 + Ka * q) ∧
      (∀ q, svRatioDyn k0 kq q = svRatioStat (KSV k0 kq) q) ∧
        ∀ m : Mech, (LifetimeTracks m k0 kq Ka ↔ m = Mech.dyn) := by
  sorry

/-! ## SV-R — the rational decision layer (`PhotoLean/SternVolmer/RatModel.lean`) -/

/-- The ℚ shadow of the dynamic intensity ratio: the same added-channel law, computed in the
decision layer. Plan section 4, row SV-R1. -/
def Rat.svRatioDyn (k0 kq q : ℚ) : ℚ := (k0 + kq * q) / k0

/-- The ℚ shadow of the dynamic lifetime ratio: the body is identical to `Rat.svRatioDyn` —
the dynamic mechanism's claim in the decision layer. Plan section 4, row SV-R1. -/
def Rat.tauRatioDyn (k0 kq q : ℚ) : ℚ := (k0 + kq * q) / k0

/-- The ℚ shadow of the static intensity ratio. Plan section 4, row SV-R1. -/
def Rat.svRatioStat (Ka q : ℚ) : ℚ := 1 + Ka * q

/-- The ℚ shadow of the static lifetime ratio. Plan section 4, row SV-R1. -/
def Rat.tauRatioStat (Ka q : ℚ) : ℚ := 1

/-- Cast coherence (SV-R1): the ℚ shadow computes the real dynamic intensity ratio.
Plan section 4, row SV-R1. Proof route: unfold both bodies; `push_cast`/`norm_cast` with
`Rat.cast_div`, `Rat.cast_add`, `Rat.cast_mul`. -/
theorem Rat.svRatioDyn_cast (a b q : ℚ) :
    (Rat.svRatioDyn a b q : ℝ) = PhotoLean.SternVolmer.svRatioDyn (a : ℝ) (b : ℝ) (q : ℝ) := by
  sorry

/-- Cast coherence (SV-R1): the ℚ shadow computes the real dynamic lifetime ratio.
Plan section 4, row SV-R1. Proof route: as `Rat.svRatioDyn_cast`. -/
theorem Rat.tauRatioDyn_cast (a b q : ℚ) :
    (Rat.tauRatioDyn a b q : ℝ) = PhotoLean.SternVolmer.tauRatioDyn (a : ℝ) (b : ℝ) (q : ℝ) := by
  sorry

/-- Cast coherence (SV-R1): the ℚ shadow computes the real static intensity ratio.
Plan section 4, row SV-R1. Proof route: as `Rat.svRatioDyn_cast`. -/
theorem Rat.svRatioStat_cast (a q : ℚ) :
    (Rat.svRatioStat a q : ℝ) = PhotoLean.SternVolmer.svRatioStat (a : ℝ) (q : ℝ) := by
  sorry

/-- Cast coherence (SV-R1): the ℚ shadow computes the real static lifetime ratio.
Plan section 4, row SV-R1. Proof route: as `Rat.svRatioDyn_cast`. -/
theorem Rat.tauRatioStat_cast (a q : ℚ) :
    (Rat.tauRatioStat a q : ℝ) = PhotoLean.SternVolmer.tauRatioStat (a : ℝ) (q : ℝ) := by
  sorry

/-- The four verdict zones of a measured slope pair. Plan section 4, row SV-R2.
(`DecidableEq` is derived so that the SV-R3 witness rows can be closed by `decide`/`rfl`,
as the plan prescribes.) -/
inductive SVZone | dynLike | statLike | mixedLike | inconsistent
  deriving DecidableEq

/-- Classify a measured slope pair `(slopeI, slopeTau)`: equal positive slopes ↦ `dynLike`;
zero lifetime slope with positive intensity slope ↦ `statLike`; `0 < slopeTau < slopeI` ↦
`mixedLike`; otherwise `inconsistent`. The `inconsistent` branch absorbs the non-physical slope
pairs — classification is a *data* classifier, not a mechanism theorem (plan §8).
Plan section 4, row SV-R2. -/
def svZoneQ (slopeI slopeTau : ℚ) : SVZone :=
  if 0 < slopeI ∧ slopeTau = slopeI then SVZone.dynLike
  else if 0 < slopeI ∧ slopeTau = 0 then SVZone.statLike
  else if 0 < slopeTau ∧ slopeTau < slopeI then SVZone.mixedLike
  else SVZone.inconsistent

/-- Zone-correctness witness, dynamic-like: the equal positive slope pair `(2, 2)` classifies
`dynLike`. Plan section 4, row SV-R3. Proof route: `decide`/`rfl` (kernel computation on
integer ℚ literals). -/
theorem svZoneQ_dynLike : svZoneQ 2 2 = SVZone.dynLike := by
  sorry

/-- Zone-correctness witness, static-like: the slope pair `(1, 0)` classifies `statLike`.
Plan section 4, row SV-R3. Proof route: `decide`/`rfl`. -/
theorem svZoneQ_statLike : svZoneQ 1 0 = SVZone.statLike := by
  sorry

/-- Zone-correctness witness, mixed-like: the slope pair `(2, 1)` classifies `mixedLike`.
Plan section 4, row SV-R3. Proof route: `decide`/`rfl`. -/
theorem svZoneQ_mixedLike : svZoneQ 2 1 = SVZone.mixedLike := by
  sorry

/-- Zone-correctness witness, inconsistent: the slope pair `(0, 1)` classifies `inconsistent`
(a non-physical pair: the lifetime slope is positive while the intensity slope vanishes).
Plan section 4, row SV-R3. Proof route: `decide`/`rfl`. -/
theorem svZoneQ_inconsistent : svZoneQ 0 1 = SVZone.inconsistent := by
  sorry

/-! ## SV-I — named instances (`PhotoLean/SternVolmer/Instances.lean`) -/

/-- Representative dynamic model `(k0, kq) = (2, 2)` (oxygen collisional quenching,
representative parameters — LITERATURE); verdict: zone `dynLike` at the measured slopes.
Plan section 4, row SV-I1. -/
noncomputable def oxygenDynamic : ℝ × ℝ := (2, 2)

/-- Representative static model `Ka = 1` (ground-state complexation, representative parameter —
LITERATURE); verdict: zone `statLike` at the measured slopes. Plan section 4, row SV-I2. -/
noncomputable def complexStatic : ℝ := 1

/-- **The D1 conflation witness pair**: the two named mechanisms are
intensity-indistinguishable — kernel-checked pointwise coincidence at every concentration.
Plan section 4, row SV-I3. Proof route: unfold, `field_simp`, `ring`. -/
theorem conflation_witness : ∀ q : ℝ, svRatioDyn 2 2 q = svRatioStat 1 q := by
  sorry

/-- The mixed witness: at `k0 = 2, kq = 1, Ka = 1` the exact slopes are
`(slopeI, slopeTau) = (KSV + Ka, KSV) = (1/2 + 1, 1/2)`, which `svZoneQ` classifies
`mixedLike`, and the second difference at `(x, h) = (0, 1)` is `2·KSV·Ka·h² = 1 > 0`
(decide at ℚ) — upward curvature positively witnesses coexistence (SV-C9).
Plan section 4, row SV-I4. -/
theorem mixed_witness :
    svZoneQ (1 / 2 + 1) (1 / 2) = SVZone.mixedLike ∧
      2 * ((1 : ℚ) / 2) * 1 * (1 : ℚ) ^ 2 = 1 ∧ (0 : ℚ) < 1 := by
  sorry

end SternVolmer

end PhotoLean
