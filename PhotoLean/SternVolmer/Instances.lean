/-
PhotoLean.SternVolmer.Instances — milestone SV4, the named-instance / verdict layer.

Named models at concrete parameters, tied to the law layer by the delivered theorems of SV2 (the
D1 core) and decided through the ℚ layer of SV3 where a kernel computation is possible. As
everywhere in this repository an instance row is a statement **about the printed numbers** under
the declared model: `oxygenDynamic` and `complexStatic` are *representative* parameter sets
(LITERATURE), not measurements, and no row here claims anything about a laboratory system.

The two honest headlines:
* `conflation_witness` (SV-I3) — **D1a made concrete**: the dynamic model `(k0, kq) = (2, 2)` and
  the static model `Ka = 1` have `KSV 2 2 = 2/2 = 1 = Ka`, so by SV-C7 their intensity plots
  coincide pointwise at every concentration. The two named mechanisms are
  intensity-indistinguishable — this is the witness the D1 verdict cites for non-injectivity.
* `mixed_witness` (SV-I4) — **D1c made concrete**: at `(k0, kq, Ka) = (2, 1, 1)` the exact slopes
  are `(KSV + Ka, KSV) = (1/2 + 1, 1/2)`, which the data classifier `svZoneQ` returns as
  `mixedLike` (a slope pair no single mechanism produces: dynamic has equal slopes, static has a
  vanishing lifetime slope), and the second difference at `(x, h) = (0, 1)` is
  `2·KSV·Ka·h² = 1 > 0` — upward curvature, positively witnessing coexistence (SV-C9).

Measured boundary (API round): `decide` does not reduce ℚ division, so the slope pair
`(1/2 + 1, 1/2)` goes through `norm_num` + the `if_neg`/`if_pos` route instead of `decide` (the
probe's `example` measures exactly this); the integer-literal zone rows of SV-R3 do use `decide`.

Statement authority: `theories/SternVolmer/probes/SternVolmer-statement-skeleton.lean` § SV-I;
every signature below is identical to its authority row. There is no unproved placeholder and no
custom axiomatic declaration anywhere in this file. Acceptance:
`proofs/scripts/lake build PhotoLean.SternVolmer.Instances` (exit 0);
`proofs/scripts/check.sh --strict`; fidelity
`python3 theories/BEP/probes/bep-fidelity.py --theory SternVolmer`.
-/
import PhotoLean.SternVolmer.RatModel
import PhotoLean.SternVolmer.Criterion

set_option autoImplicit false

namespace PhotoLean

namespace SternVolmer

/-! ## SV-I — named instances -/

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
  intro q
  unfold svRatioDyn svRatioStat dynDecay
  field_simp
  ring

/-- The mixed witness: at `k0 = 2, kq = 1, Ka = 1` the exact slopes are
`(slopeI, slopeTau) = (KSV + Ka, KSV) = (1/2 + 1, 1/2)`, which `svZoneQ` classifies
`mixedLike`, and the second difference at `(x, h) = (0, 1)` is `2·KSV·Ka·h² = 1 > 0`
(decide at ℚ) — upward curvature positively witnesses coexistence (SV-C9).
Plan section 4, row SV-I4. -/
theorem mixed_witness :
    svZoneQ (1 / 2 + 1) (1 / 2) = SVZone.mixedLike ∧
      2 * ((1 : ℚ) / 2) * 1 * (1 : ℚ) ^ 2 = 1 ∧ (0 : ℚ) < 1 := by
  refine ⟨?_, ?_, ?_⟩
  · have c1 : ¬ (0 < (1 / 2 + 1 : ℚ) ∧ (1 / 2 : ℚ) = 1 / 2 + 1) := by norm_num
    have c2 : ¬ (0 < (1 / 2 + 1 : ℚ) ∧ (1 / 2 : ℚ) = 0) := by norm_num
    have c3 : 0 < (1 / 2 : ℚ) ∧ (1 / 2 : ℚ) < 1 / 2 + 1 := by norm_num
    unfold svZoneQ
    rw [if_neg c1, if_neg c2, if_pos c3]
  · norm_num
  · norm_num

end SternVolmer

end PhotoLean
