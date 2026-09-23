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

**Statement incident found while proving SV-R1 (see the docstring of `Rat.svRatioDyn_cast`).** The
authority's four cast-coherence rows are degenerate as written: the `Rat.`-prefixed declaration
name opens the `Rat` namespace for the elaboration of the type, so the unqualified right-hand
`svRatioDyn`/`tauRatioDyn`/`svRatioStat`/`tauRatioStat` resolves to the ℚ shadow and the delivered
type is `↑x = ↑x`. Kept verbatim (frozen authority, textual fidelity), with the intended bridges
delivered as `rat_*_cast_real` right below them and reported to the lead for a §3.1 re-freeze.

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
Plan section 4, row SV-R1. Proof route: unfold both bodies; `push_cast`/`norm_cast` with
`Rat.cast_div`, `Rat.cast_add`, `Rat.cast_mul`.

**STATEMENT-INCIDENT (SV-R1, found in SV3, 2026-09-22).** This signature is transcribed verbatim
from the statement authority, and in that authority the right-hand `svRatioDyn` does **not**
denote the real ratio: because the declaration's own `Rat.`-prefixed name opens the `Rat`
namespace for the elaboration of its type, the unqualified identifier resolves to
`PhotoLean.SternVolmer.Rat.svRatioDyn` (the ℚ shadow), so the delivered type is the degenerate
identity `↑(Rat.svRatioDyn a b q) = ↑(Rat.svRatioDyn a b q)` — vacuous, not the cast bridge
described by the authority's own docstring ("the ℚ shadow computes the real dynamic intensity
ratio"), by plan §4/§5, and by the API probe's measured shape (which used an unnamed `example`,
hence the outer namespace, hence the intended reading). Evidence: this row closes by `rfl`, and
`#print PhotoLean.SternVolmer.Rat.svRatioDyn_cast` shows `@Rat.cast
(PhotoLean.SternVolmer.Rat.svRatioDyn a b q)` on both sides.

The row is kept verbatim here (the statement authority is frozen and the fidelity checker compares
signatures textually); the **intended** bridge is delivered as `rat_svRatioDyn_cast_real`
immediately after the four rows. Recommended re-freeze of the authority: qualify the right-hand
side as `PhotoLean.SternVolmer.svRatioDyn a b q`, or drop the `Rat.` prefix from the four theorem
names. -/
theorem Rat.svRatioDyn_cast (a b q : ℚ) :
    (Rat.svRatioDyn a b q : ℝ) = svRatioDyn a b q := by
  rfl

/-- Cast coherence (SV-R1): the ℚ shadow computes the real dynamic lifetime ratio.
Plan section 4, row SV-R1. Proof route: as `Rat.svRatioDyn_cast`.
Statement-incident as documented on `Rat.svRatioDyn_cast`: the authority's right-hand
`tauRatioDyn` resolves to the ℚ shadow, so the delivered type is degenerate. -/
theorem Rat.tauRatioDyn_cast (a b q : ℚ) :
    (Rat.tauRatioDyn a b q : ℝ) = tauRatioDyn a b q := by
  rfl

/-- Cast coherence (SV-R1): the ℚ shadow computes the real static intensity ratio.
Plan section 4, row SV-R1. Proof route: as `Rat.svRatioDyn_cast`.
Statement-incident as documented on `Rat.svRatioDyn_cast`: the authority's right-hand
`svRatioStat` resolves to the ℚ shadow, so the delivered type is degenerate. -/
theorem Rat.svRatioStat_cast (a q : ℚ) :
    (Rat.svRatioStat a q : ℝ) = svRatioStat a q := by
  rfl

/-- Cast coherence (SV-R1): the ℚ shadow computes the real static lifetime ratio.
Plan section 4, row SV-R1. Proof route: as `Rat.svRatioDyn_cast`.
Statement-incident as documented on `Rat.svRatioDyn_cast`: the authority's right-hand
`tauRatioStat` resolves to the ℚ shadow, so the delivered type is degenerate. -/
theorem Rat.tauRatioStat_cast (a q : ℚ) :
    (Rat.tauRatioStat a q : ℝ) = tauRatioStat a q := by
  rfl

/-! ### SV-R1 incident workaround — the intended cast bridges

The four rows below carry the content the authority's SV-R1 docstrings and plan §4 actually
describe (the ℚ shadow computes the real `ℝ` ratio), with the right-hand side disambiguated by
explicit arguments so that `svRatioDyn`/`tauRatioDyn`/`svRatioStat`/`tauRatioStat` resolve to
`PhotoLean.SternVolmer` and not to their ℚ shadows. They are deliberately **not** named `Rat.*`,
so that the file's `Rat`-keyed signature (the fidelity checker collapses every `Rat.`-prefixed
declaration to one key) stays identical to the authority. -/

/-- The intended SV-R1 bridge, dynamic intensity ratio: disambiguated right-hand side. -/
theorem rat_svRatioDyn_cast_real (a b q : ℚ) :
    (Rat.svRatioDyn a b q : ℝ) = svRatioDyn (a : ℝ) (b : ℝ) (q : ℝ) := by
  unfold Rat.svRatioDyn
  unfold svRatioDyn
  unfold dynDecay
  norm_cast

/-- The intended SV-R1 bridge, dynamic lifetime ratio: disambiguated right-hand side. -/
theorem rat_tauRatioDyn_cast_real (a b q : ℚ) :
    (Rat.tauRatioDyn a b q : ℝ) = tauRatioDyn (a : ℝ) (b : ℝ) (q : ℝ) := by
  unfold Rat.tauRatioDyn
  unfold tauRatioDyn
  unfold dynDecay
  norm_cast

/-- The intended SV-R1 bridge, static intensity ratio: disambiguated right-hand side. -/
theorem rat_svRatioStat_cast_real (a q : ℚ) :
    (Rat.svRatioStat a q : ℝ) = svRatioStat (a : ℝ) (q : ℝ) := by
  unfold Rat.svRatioStat
  unfold svRatioStat
  norm_cast

/-- The intended SV-R1 bridge, static lifetime ratio: disambiguated right-hand side. -/
theorem rat_tauRatioStat_cast_real (a q : ℚ) :
    (Rat.tauRatioStat a q : ℝ) = tauRatioStat (a : ℝ) (q : ℝ) := by
  unfold Rat.tauRatioStat
  unfold tauRatioStat
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
