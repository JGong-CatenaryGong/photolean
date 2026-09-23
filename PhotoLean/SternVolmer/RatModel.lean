/-
PhotoLean.SternVolmer.RatModel — milestone SV3, the computable rational decision layer.

The order of `ℝ` is not computable, so a verdict about a *measured* slope pair cannot be decided by
the kernel over `ℝ` (the repository's standing structural solution: an `ℝ` theory plus a `ℚ` shadow
plus cast bridges — `METHOD.md` five-piece item 2). This module carries the shadow of the two ratio
laws (SV-R1), the four-zone data classifier `svZoneQ` of a measured slope pair (SV-R2), and the
zone-correctness witnesses (SV-R3).

What the classifier is, and is not (plan §8): `svZoneQ` is a **data classifier**, not a mechanism
theorem — the `inconsistent` branch absorbs every non-physical slope pair (for instance a positive
lifetime slope with vanishing intensity slope), and the physical content lives in the law layer
(`Criterion`): the dynamic mechanism's slope pair has equal slopes (SV-C1), the static mechanism's
has a vanishing lifetime slope and intensity slope `Ka` (SV-C2/C4), and the mixed mechanism has
`0 < slopeTau < slopeI` (SV-C9). The cast bridges make the ℚ copy the real thing rather than an
analogy: each shadow computes the corresponding `ℝ` ratio of `Basic`.

Measured boundaries (API round, `theories/SternVolmer/probes/SternVolmer-api-probe.lean`,
`proofs/API-NOTES.md` §photobatch): `decide` handles integer `ℚ` literals but does NOT reduce `ℚ`
division (the repository's thrice-measured rule), so `svZoneQ_dynLike`/`statLike`/`mixedLike`/
`inconsistent` end in `decide` while a division-bearing slope pair needs the `if_neg`/`if_pos`
route (exercised in `Instances.mixed_witness`); `norm_cast` moves the cast through `+`, `*` and `/`
on ℚ → ℝ.

**Statement incident found while proving SV-R1, re-frozen 2026-09-22 (plan §3.1 entry 1).** The
authority's four cast-coherence rows were degenerate as first frozen: the `Rat.`-prefixed
declaration name elaborates its type inside the `Rat` namespace, so the unqualified right-hand
side resolved to the ℚ shadow and each row was the vacuous identity `↑x = ↑x`. The authority is
re-frozen with fully-qualified right-hand sides and the rows now deliver the intended cast
bridges.

Statement authority: `theories/SternVolmer/probes/SternVolmer-statement-skeleton.lean` § SV-R;
every signature below is identical to its authority row. There is no unproved placeholder and no
custom axiomatic declaration anywhere in this file. Acceptance:
`proofs/scripts/lake build PhotoLean.SternVolmer.RatModel` (exit 0);
`proofs/scripts/check.sh --strict`; fidelity
`python3 theories/BEP/probes/bep-fidelity.py --theory SternVolmer`.
-/
import PhotoLean.SternVolmer.Basic

set_option autoImplicit false

namespace PhotoLean

namespace SternVolmer

/-! ## SV-R — the rational decision layer -/

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
Plan section 4, row SV-R1. Proof route: `unfold` the two bodies with fully-qualified names (an
unqualified identifier inside a `Rat.`-prefixed declaration resolves to the ℚ shadow) and close by
`norm_cast`.

**Statement incident, re-frozen 2026-09-22 (plan §3.1 entry 1).** The first frozen form left the
right-hand side unqualified; the `Rat.`-prefixed name elaborates the type inside the `Rat`
namespace, so it resolved to the ℚ shadow and the row was the vacuous identity `↑x = ↑x`
(closable by `rfl`; detected while proving, reported by prover_c). The authority is re-frozen with
fully-qualified right-hand sides; the four rows now carry their intended bridges. -/
theorem Rat.svRatioDyn_cast (a b q : ℚ) :
    (Rat.svRatioDyn a b q : ℝ) = PhotoLean.SternVolmer.svRatioDyn (a : ℝ) (b : ℝ) (q : ℝ) := by
  unfold PhotoLean.SternVolmer.Rat.svRatioDyn
  unfold PhotoLean.SternVolmer.svRatioDyn
  unfold PhotoLean.SternVolmer.dynDecay
  norm_cast

/-- Cast coherence (SV-R1): the ℚ shadow computes the real dynamic lifetime ratio.
Plan section 4, row SV-R1. Proof route: as `Rat.svRatioDyn_cast`.
Re-frozen 2026-09-22 (plan §3.1 entry 1): fully-qualified right-hand side. -/
theorem Rat.tauRatioDyn_cast (a b q : ℚ) :
    (Rat.tauRatioDyn a b q : ℝ) = PhotoLean.SternVolmer.tauRatioDyn (a : ℝ) (b : ℝ) (q : ℝ) := by
  unfold PhotoLean.SternVolmer.Rat.tauRatioDyn
  unfold PhotoLean.SternVolmer.tauRatioDyn
  unfold PhotoLean.SternVolmer.dynDecay
  norm_cast

/-- Cast coherence (SV-R1): the ℚ shadow computes the real static intensity ratio.
Plan section 4, row SV-R1. Proof route: as `Rat.svRatioDyn_cast`.
Re-frozen 2026-09-22 (plan §3.1 entry 1): fully-qualified right-hand side. -/
theorem Rat.svRatioStat_cast (a q : ℚ) :
    (Rat.svRatioStat a q : ℝ) = PhotoLean.SternVolmer.svRatioStat (a : ℝ) (q : ℝ) := by
  unfold PhotoLean.SternVolmer.Rat.svRatioStat
  unfold PhotoLean.SternVolmer.svRatioStat
  norm_cast

/-- Cast coherence (SV-R1): the ℚ shadow computes the real static lifetime ratio.
Plan section 4, row SV-R1. Proof route: as `Rat.svRatioDyn_cast`.
Re-frozen 2026-09-22 (plan §3.1 entry 1): fully-qualified right-hand side. -/
theorem Rat.tauRatioStat_cast (a q : ℚ) :
    (Rat.tauRatioStat a q : ℝ) = PhotoLean.SternVolmer.tauRatioStat (a : ℝ) (q : ℝ) := by
  unfold PhotoLean.SternVolmer.Rat.tauRatioStat
  unfold PhotoLean.SternVolmer.tauRatioStat
  norm_cast

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
  decide

/-- Zone-correctness witness, static-like: the slope pair `(1, 0)` classifies `statLike`.
Plan section 4, row SV-R3. Proof route: `decide`/`rfl`. -/
theorem svZoneQ_statLike : svZoneQ 1 0 = SVZone.statLike := by
  decide

/-- Zone-correctness witness, mixed-like: the slope pair `(2, 1)` classifies `mixedLike`.
Plan section 4, row SV-R3. Proof route: `decide`/`rfl`. -/
theorem svZoneQ_mixedLike : svZoneQ 2 1 = SVZone.mixedLike := by
  decide

/-- Zone-correctness witness, inconsistent: the slope pair `(0, 1)` classifies `inconsistent`
(a non-physical pair: the lifetime slope is positive while the intensity slope vanishes).
Plan section 4, row SV-R3. Proof route: `decide`/`rfl`. -/
theorem svZoneQ_inconsistent : svZoneQ 0 1 = SVZone.inconsistent := by
  decide

end SternVolmer

end PhotoLean
