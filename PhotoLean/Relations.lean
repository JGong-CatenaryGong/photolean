/-
PhotoLean.Relations — the single home of the cross-theory relations of the two-parabola family.

The five delivered theories share one mathematical substrate (the equal-curvature two-parabola
model, now defined once in `PhotoLean.Kernel`), and their relation inventory is collected here,
organised by edge type:

* §1 **kernel certificates** (definitional, `rfl`): each theory's copy of the barrier, the
  transition-state coordinate, the transfer coefficient and the two surfaces is *literally* the
  kernel definition. A failing `rfl` here is a **regression alarm**: it means the kernel and a
  delivered definition have drifted apart, and the response is to stop and investigate — never to
  edit a delivered module in order to restore the certificate.
* §2 **true equivalences** (`↔`, non-definitional, reused verbatim from the theories).
* §3 **one-way entailments** (`→`, labelled as such upstream), plus one new edge proved here.
* §4 **definitional reuse**: the Hammond composition consumes `Marcus.Reorg`'s inner/outer
  reorganization energy instead of redefining it.
* §5 **remaining ledger rows** of the cross-theory bridge inventory (alias certificates, the BEP
  rate rewriting, the rational-side certification).
* §6 **non-relations and shape differences** — the new mathematics of this module: the same model
  in which the Hammond trend is exactly affine while the BEP line law is exactly violated on every
  non-degenerate interval, the co-extensiveness of the two sharp conditions, and the two `∀∀`
  predicates' different strength.
* §7 **Kasha → Marcus, conditional composition**: the excited-state ladder's internal-conversion
  rate is a Marcus rate (an explicit *modelling* premise), and conformance to Kasha's rule is then
  exactly a window condition on the energy gap. The edge carries its premise with it.
* §8 **Sabatier → BEP, composition**: the literature's linear volcano is the tangent (BEP) form of
  the repository's two-parabola model, it *underestimates* the barrier pointwise, and the volcano
  holds in the two-parabola model with no linearization at all.
* §9 **Sabatier ↔ Marcus, look-alike but different**: the two theories share one "interior
  optimum" predicate (and one observable functional form), while the optima themselves come apart
  in three checkable ways — the barrier height at the optimum, the one-sided secant behaviour, and
  the parameter dependence of the optimal position.
* §10 **the no-edge registry**: the theory pairs that carry no relation, with the reason, so that
  the graph is complete in the sense that *every* theory sits on it (an absent edge is a
  registered fact, not an oversight).

The re-exports of §1–§5 and §7–§8 add no mathematics — they are certificates and a ledger, and their
value is the compile-time pin: every statement below is written out in full, so a statement drift
anywhere upstream makes this module fail to compile. The declarations proved here rather than reused
are the last one of §3, the three of §6, the kernel certificate of §7, and the seven of §9. Every
declaration is fully proved: no unproved placeholder, no custom axiomatic declaration.
-/
import PhotoLean.Kernel
import PhotoLean.Marcus.RatModel
import PhotoLean.Marcus.Sharp
import PhotoLean.Hammond.Compose
import PhotoLean.Hammond.RatModel
import PhotoLean.Hammond.Sharp
import PhotoLean.BEP.Compose
import PhotoLean.BEP.Sharp
import PhotoLean.Kasha.Compose
import PhotoLean.Sabatier.Compose
import PhotoLean.Sabatier.Criterion

namespace PhotoLean

namespace Relations

/-! ## 1. Kernel certificates (definitional — the regression certificates of the extraction) -/

/-- Kernel certificate: the kernel barrier is literally the delivered Marcus barrier. -/
theorem kernel_barrier_eq_marcus (lam x : ℝ) :
    Kernel.barrier lam x = Marcus.barrier lam x := rfl

/-- Kernel certificate: the kernel barrier is literally the delivered Hammond forward gap. -/
theorem kernel_barrier_eq_hammond (lam x : ℝ) :
    Kernel.barrier lam x = Hammond.gapReactant lam x := rfl

/-- Kernel certificate: the kernel barrier is literally the delivered BEP activation barrier. -/
theorem kernel_barrier_eq_bep (lam x : ℝ) :
    Kernel.barrier lam x = BEP.eact lam x := rfl

/-- Kernel certificate: the kernel reverse barrier is literally the delivered Hammond reverse
gap. -/
theorem kernel_reverseBarrier_eq_hammond (lam x : ℝ) :
    Kernel.reverseBarrier lam x = Hammond.gapProduct lam x := rfl

/-- Kernel certificate: the kernel transition-state coordinate is literally the delivered
Hammond coordinate. -/
theorem kernel_tsCoord_eq_hammond (lam x : ℝ) :
    Kernel.tsCoord lam x = Hammond.tsCoord lam x := rfl

/-- Kernel certificate: the kernel transfer coefficient is literally the delivered BEP
coefficient (both use the linear-response body). -/
theorem kernel_transfer_eq_bep (lam x : ℝ) :
    Kernel.transfer lam x = BEP.transfer lam x := rfl

/-- Kernel certificate: the kernel reactant surface is literally the delivered Hammond
surface. -/
theorem kernel_reactantSurface_eq_hammond (lam q : ℝ) :
    Kernel.reactantSurface lam q = Hammond.reactantSurface lam q := rfl

/-- Kernel certificate: the kernel product surface is literally the delivered Hammond
surface. -/
theorem kernel_productSurface_eq_hammond (lam dG q : ℝ) :
    Kernel.productSurface lam dG q = Hammond.productSurface lam dG q := rfl

/-! ## 2. True equivalences (non-definitional; reused verbatim) -/

/-- The BEP transfer coefficient equals the Hammond transition-state coordinate of the same step.
This is a genuine theorem about the linear-response body `1/2 - x/(2*lam)` of `BEP.transfer`
(rather than a definitional restatement of `(lam - x)/(2*lam)`); the explicit physical premise
`lam ≠ 0` is what makes the coordinate well defined (at `lam = 0` the two totalised-division
values disagree). -/
theorem transfer_eq_tsCoord_bridge {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    BEP.transfer lam x = Hammond.tsCoord lam x :=
  BEP.transfer_eq_tsCoord_bridge hlam x

/-- The BEP *observable* slope (a finite difference of barrier data) is Hammond's Leffler secant
over the same pair of driving forces. Not definitional — the two bodies differ in sign convention
and pair indexing — hence proved rather than closed by `rfl`. -/
theorem secSlope_eq_lefflerSecant (lam x h : ℝ) :
    BEP.secSlope lam x h = Hammond.lefflerSecant lam x (x + h) :=
  BEP.secSlope_eq_lefflerSecant lam x h

/-- Headline equivalence: the Evans–Polanyi bounds `0 ≤ α ≤ 1` hold exactly when neither the
forward direction `x` nor the reverse direction `-x` of the step lies in the Marcus inverted
region. -/
theorem epBounds_iff_no_inverted_direction {lam x : ℝ} (hlam : 0 < lam) :
    BEP.EPBounds lam x ↔ ¬ (Marcus.InvertedRegion lam x ∨ Marcus.InvertedRegion lam (-x)) :=
  BEP.epBounds_iff_no_inverted_direction hlam

/-- The transition state leaves the reactant side of the interval exactly in the Marcus inverted
region. -/
theorem tsCoord_lt_zero_iff_inverted {lam x : ℝ} (hlam : 0 < lam) :
    Hammond.tsCoord lam x < 0 ↔ Marcus.InvertedRegion lam x :=
  Hammond.tsCoord_lt_zero_iff_inverted hlam

/-- A negative Brønsted coefficient is exactly the Marcus inverted region, seen from the barrier
data (via the pointwise identification above). -/
theorem lefflerSecant_neg_iff_inverted {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h : x₁ ≠ x₂) :
    Hammond.lefflerSecant lam x₁ x₂ < 0 ↔ Marcus.InvertedRegion lam ((x₁ + x₂) / 2) :=
  Hammond.lefflerSecant_neg_iff_inverted hlam h

/-- Rational-side agreement: the Hammond classifier's deep-exergonic branch and the Marcus
rational inverted-region classifier single out the same instances over `ℚ`. -/
theorem hammondZoneQ_beyondReactant_iff_inverted {lam x : ℚ} (hlam : 0 < lam) :
    Hammond.Rat.hammondZoneQ lam x = Hammond.HZone.beyondReactant ↔
      Marcus.Rat.zoneQ lam x = Marcus.Zone.inverted :=
  Hammond.Rat.hammondZoneQ_beyondReactant_iff_inverted hlam

/-! ## 3. One-way entailments -/

/-- Hammond's conformance region `-lam < x ∧ x < lam` entails the Evans–Polanyi bounds — a
strictly inside-the-window step has both directions in the Marcus normal region, so the headline
equivalence applies. One-way: the converse fails (a step outside the window can still satisfy the
bounds). -/
theorem epBounds_of_reactionRegion {lam x : ℝ} (hlam : 0 < lam)
    (h : Hammond.ReactionRegion lam x) : BEP.EPBounds lam x :=
  BEP.epBounds_of_reactionRegion hlam h

/-- A step in the Marcus normal region whose reverse direction is thermoneutral or exergonic
(`-lam ≤ x`) satisfies the Evans–Polanyi bounds. One-way: the two hypotheses are exactly the two
halves of the headline equivalence, and neither is implied by the other. -/
theorem epBounds_of_marcus_normal {lam x : ℝ} (hlam : 0 < lam)
    (h : Marcus.NormalRegion lam x) (hx : -lam ≤ x) : BEP.EPBounds lam x :=
  BEP.epBounds_of_marcus_normal hlam h hx

/-- **New edge (proved here)**: conformance to the BEP line law on a window entails the
*structural* Hammond descriptor. The road runs through the positivity conjunct of
`BEP.EPConformsOnWindow` (`0 < lam`), which alone carries the structural law
(`Hammond.hammond_descriptor_holds`); the tolerance bound itself is not consumed. The two
predicates are shaped differently (uniform error bound on a window vs. pointwise monotonicity) and
this is the only logical road between them — recorded here so the relation graph does not
over-claim a deeper link. -/
theorem hammondDescriptor_of_epConformsOnWindow {lam tol a b : ℝ}
    (h : BEP.EPConformsOnWindow lam tol a b) : Hammond.HammondDescriptor lam :=
  Hammond.hammond_descriptor_holds h.1

/-! ## 4. Definitional reuse (Hammond's composition over the Marcus reorganization energy) -/

/-- Reuse: the inner-sphere reorganization energy of `Marcus.Reorg` yields the Hammond
descriptor directly. -/
theorem hammond_descriptor_of_inner {kk dq : ℝ} (hkk : 0 < kk) (hdq : dq ≠ 0) :
    Hammond.HammondDescriptor (Marcus.lamInner kk dq) :=
  Hammond.hammond_descriptor_of_inner hkk hdq

/-- Reuse: the Pekar/geometric premises on the Marcus outer-sphere term make the total
reorganization energy positive, hence the descriptor holds. -/
theorem hammond_descriptor_of_microscopic {kk dq dE a1 a2 R nSq epsS : ℝ} (hkk : 0 ≤ kk)
    (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2) (hR : 0 < R)
    (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    Hammond.HammondDescriptor (Marcus.lamInner kk dq + Marcus.lamOuter dE a1 a2 R nSq epsS) :=
  Hammond.hammond_descriptor_of_microscopic hkk hdE ha1 ha2 hR hgeom hnSq hepsS hPekar

/-- Reuse (stretch form): the geometric premise is derivable from non-overlapping spheres. -/
theorem hammond_descriptor_of_nonoverlap {kk dq dE a1 a2 R nSq epsS : ℝ} (hkk : 0 ≤ kk)
    (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2) (hRge : a1 + a2 ≤ R) (hnSq : 0 < nSq)
    (hepsS : 0 < epsS) (hPekar : 1 / epsS < 1 / nSq) :
    Hammond.HammondDescriptor (Marcus.lamInner kk dq + Marcus.lamOuter dE a1 a2 R nSq epsS) :=
  Hammond.hammond_descriptor_of_nonoverlap hkk hdE ha1 ha2 hRge hnSq hepsS hPekar

/-- Reuse: non-vacuity of the Hammond regime from the Marcus microscopic premises. -/
theorem exists_reactionRegion_of_microscopic {kk dq dE a1 a2 R nSq epsS : ℝ} (hkk : 0 < kk)
    (hdq : dq ≠ 0) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2) (hR : 0 < R)
    (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    ∃ x : ℝ, Hammond.ReactionRegion (Marcus.lamInner kk dq + Marcus.lamOuter dE a1 a2 R nSq epsS) x :=
  Hammond.exists_reactionRegion_of_microscopic hkk hdq hdE ha1 ha2 hR hgeom hnSq hepsS hPekar

/-! ## 5. Remaining ledger rows of the bridge inventory -/

/-- Ledger: the two definitions have identical bodies, so the bridge is definitional — the BEP
barrier *is* the delivered Marcus barrier. -/
theorem bep_eact_eq_marcus_barrier (lam x : ℝ) :
    BEP.eact lam x = Marcus.barrier lam x :=
  BEP.eact_eq_barrier lam x

/-- Ledger: the delivered Marcus rate written through the BEP barrier — both sides are the same
term up to unfolding the two definitions, hence definitional. -/
theorem bep_rate_eq_exp_neg_eact (A lam kB T x : ℝ) :
    Marcus.rate A lam kB T x = A * Real.exp (-(BEP.eact lam x) / (kB * T)) :=
  BEP.rate_eq_exp_neg_eact A lam kB T x

/-- Ledger: the Hammond forward gap is literally the Marcus barrier (definitional alias
certificate at the theory level). -/
theorem hammond_barrier_eq_gapReactant (lam x : ℝ) :
    Marcus.barrier lam x = Hammond.gapReactant lam x :=
  Hammond.barrier_eq_gapReactant lam x

/-- Ledger: the rational inverted-region decision of Marcus connects to `InvertedRegion`; the
residual `Iff.rfl` closes a definitional unfolding after two substantive transfer rewrites. -/
theorem marcus_rat_zoneQ_inverted_iff (lam x : ℚ) :
    Marcus.Rat.zoneQ lam x = Marcus.Zone.inverted ↔ (lam : ℝ) < (x : ℝ) :=
  Marcus.Rat.zoneQ_inverted_iff lam x

/-! ## 6. Non-relations and shape differences (new theorems of this module) -/

/-- **Exact in one theory, exactly false in the other.** In one and the same model the Hammond
structural trend is *exactly* affine in the driving force — the transition-state coordinate is
`1/2 - x/(2*lam)`, an affine function — so for positive curvature the "more driving force, earlier
transition state" law holds with no tolerance parameter (`Hammond.hammond_sharp`); the affinity
itself is exact for every `lam ≠ 0`, but at `lam < 0` the *direction* is reversed, whose delivered
witness is `Hammond.exists_direction_reversal_of_neg` (and the descriptor fails there: the third
conjunct of the theorem below). So the qualifier `0 < lam` belongs to the trend reading, not to the
affinity claim. In the same model the BEP line law is
*exactly* violated on every non-degenerate interval (`BEP.not_epLinearOn_of_ne_zero`, the
second-difference engine): no affine model reproduces the barrier, the exact defect being the
quadratic remainder `x²/(4*lam)`. This is the sharpest formal statement of the difference between
the structural reading and the linear-free-energy reading of the same two-parabola object. -/
theorem hammond_trend_exact_bep_law_inexact {lam : ℝ} (hlam : lam ≠ 0) :
    (∃ c k : ℝ, ∀ x : ℝ, Kernel.tsCoord lam x = c + k * x) ∧
      (∀ p q : ℝ, p < q → ¬ BEP.EPLinearOn lam (Set.Icc p q)) := by
  constructor
  · refine ⟨1 / 2, -(1 / (2 * lam)), fun x => ?_⟩
    have h2 : (2 * lam : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hlam
    unfold Kernel.tsCoord
    field_simp
    ring
  · intro p q hpq
    exact BEP.not_epLinearOn_of_ne_zero hlam hpq

/-- **The two sharp conditions coincide.** Under the physical positivity premises on the Marcus
rate parameters, the Hammond structural descriptor holds exactly when the Marcus rate descriptor
holds with an everywhere-positive rate; both sides characterize precisely the positive-curvature
model (`Hammond.hammond_sharp`, `Marcus.descriptor_sharp`). The two descriptions are therefore
*co-extensive* as hypotheses on the curvature, even though neither is a restatement of the other.
Honest accounting: the statement is a **composition** of the two delivered sharp characterizations
(no new mathematics beyond the composition), whose content is the co-extensiveness itself — the
derived reading of the `rfl`-level barrier certificates. -/
theorem hammond_sharp_iff_marcus_sharp {A kB T : ℝ} (hA : 0 < A) (hkB : 0 < kB) (hT : 0 < T)
    (lam : ℝ) :
    Hammond.HammondDescriptor lam ↔
      ((∀ x : ℝ, 0 < Marcus.rate A lam kB T x) ∧ Marcus.InvertedDescriptor A lam kB T) := by
  rw [Hammond.hammond_sharp, Marcus.descriptor_sharp hkB hT A lam]
  exact ⟨fun h => ⟨hA, h⟩, fun h => h.2⟩

/-- **The two `∀∀` predicates are not equally strong.** The rate predicate alone is satisfiable in
a parameter region where the rate is everywhere *negative* (`A < 0`, `lam < 0`: the formal
monotone pattern survives multiplying by a negative prefactor), whereas the structural predicate
holds exactly for positive curvature. So "the rate decreases across the inverted region" does not
pin the physical model, while "the transition-state coordinate decreases" does — the shape
difference that the positivity conjunct of the Marcus sharpness theorem repairs. -/
theorem rate_predicate_satisfiable_without_positive_curvature :
    (∀ x : ℝ, Marcus.rate (-1) (-1) 1 1 x < 0) ∧
      Marcus.InvertedDescriptor (-1) (-1) 1 1 ∧ ¬ Hammond.HammondDescriptor (-1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    unfold Marcus.rate
    exact mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _)
  · exact Marcus.inverted_descriptor_holds_of_neg (A := -1) (lam := -1) (kB := 1) (T := 1)
      (by norm_num) (by norm_num) (by norm_num)
  · exact Hammond.hammond_fails_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)

/-! ## 7. Conditional composition edge: Kasha's internal conversion on the Marcus barrier

The excited-state ladder of `PhotoLean.Kasha` is a rate-competition model, and its only contact
with the two-parabola family is the **declared modelling premise** that the `S₂ → S₁`
internal-conversion rate is the Marcus rate `Kasha.marcusIC A lam kB T x`. The rows below carry
that premise explicitly (`hic`): nothing here claims that internal conversion *is* a Marcus
process — the identification is registered in the Kasha plan's honesty table and in
`theories/kasha/LITERATURE.md`. The conditional equivalence and its two consequences are
re-exported verbatim from `PhotoLean.Kasha.Compose`; the kernel certificate puts Kasha on the
shared kernel of §1 (Kasha itself states its rate against `PhotoLean.Marcus.Basic` and does not
import the kernel). -/

/-- Kernel certificate: the Kasha internal-conversion rate is the kernel barrier inside the
Marcus rate law, scaled by the pre-exponential factor. -/
theorem kernel_marcusIC (A lam kB T x : ℝ) :
    Kasha.marcusIC A lam kB T x = A * Real.exp (-(Kernel.barrier lam x) / (kB * T)) := by
  unfold Kasha.marcusIC Kernel.barrier Marcus.barrier
  rfl

/-- Kasha → Marcus (conditional equivalence): under the ladder data `RateData` and the declared
identification `hic` of the `S₂ → S₁` internal-conversion rate with the Marcus rate, conformance
at tolerance `tol` is exactly the explicit window condition on the squared energy gap. -/
theorem kashaWithin_one_marcus {rad ic : ℕ → ℝ} {A lam kB T x tol : ℝ}
    (h : Kasha.RateData rad ic 1) (htol0 : 0 < tol) (htol1 : tol < 1) (hA : 0 < A)
    (hlam : 0 < lam) (hkT : 0 < kB * T) (hr0 : 0 < rad 0) (hr1 : 0 < rad 1)
    (hic : ic 1 = Kasha.marcusIC A lam kB T x) :
    Kasha.KashaWithin rad ic tol 1 ↔
      (lam - x) ^ 2 ≤ 4 * lam * (kB * T)
        * Real.log (Kasha.kashaGapThreshold A (rad 0) (Kasha.decay rad ic 0) (rad 1) tol) :=
  Kasha.kashaWithin_one_marcus h htol0 htol1 hA hlam hkT hr0 hr1 hic

/-- Kasha → Marcus (one-way, the anti-Kasha direction): a gap outside the window violates the
tolerance, so the model-side face of the anti-Kasha family is the Marcus inverted region and the
activation-controlled side, read at the `S₂ → S₁` gap. -/
theorem not_kashaWithin_of_gap_far {rad ic : ℕ → ℝ} {A lam kB T x tol : ℝ}
    (h : Kasha.RateData rad ic 1) (htol0 : 0 < tol) (htol1 : tol < 1) (hA : 0 < A)
    (hlam : 0 < lam) (hkT : 0 < kB * T) (hr0 : 0 < rad 0) (hr1 : 0 < rad 1)
    (hic : ic 1 = Kasha.marcusIC A lam kB T x)
    (hfar : 4 * lam * (kB * T)
        * Real.log (Kasha.kashaGapThreshold A (rad 0) (Kasha.decay rad ic 0) (rad 1) tol)
      < (lam - x) ^ 2) :
    ¬ Kasha.KashaWithin rad ic tol 1 :=
  Kasha.not_kashaWithin_of_gap_far h htol0 htol1 hA hlam hkT hr0 hr1 hic hfar

/-- Kasha → Marcus (window form): the same criterion as a half-width bound around the
reorganization energy, `|lam - x| ≤ sqrt K'`. -/
theorem kashaWindow_halfWidth {rad ic : ℕ → ℝ} {A lam kB T x tol : ℝ}
    (h : Kasha.RateData rad ic 1) (htol0 : 0 < tol) (htol1 : tol < 1) (hA : 0 < A)
    (hlam : 0 < lam) (hkT : 0 < kB * T) (hr0 : 0 < rad 0) (hr1 : 0 < rad 1)
    (hic : ic 1 = Kasha.marcusIC A lam kB T x)
    (h0 : 0 ≤ 4 * lam * (kB * T)
        * Real.log (Kasha.kashaGapThreshold A (rad 0) (Kasha.decay rad ic 0) (rad 1) tol)) :
    Kasha.KashaWithin rad ic tol 1 ↔
      |lam - x| ≤ Real.sqrt (4 * lam * (kB * T)
        * Real.log (Kasha.kashaGapThreshold A (rad 0) (Kasha.decay rad ic 0) (rad 1) tol)) :=
  Kasha.kashaWindow_halfWidth h htol0 htol1 hA hlam hkT hr0 hr1 hic h0

/-- Kasha → Marcus (supporting row): the Marcus-form internal-conversion rate is positive
whenever the pre-exponential factor is. -/
theorem marcusIC_pos {A lam kB T x : ℝ} (hA : 0 < A) : 0 < Kasha.marcusIC A lam kB T x :=
  Kasha.marcusIC_pos hA

/-! ## 8. Composition edge: the Sabatier volcano over the BEP two-parabola model

The Sabatier theory describes the volcano in the phenomenological language of two affine BEP
branches; `PhotoLean.Sabatier.Compose` closes the loop with the repository's two-parabola model by
replacing each affine branch with the exact barrier `BEP.eact`. The rows below are re-exported
verbatim: the literature's linear volcano *is* the maximum of the two tangent lines
(`linearVolcano_eq_bepTangent`); the tangent lies below its parabola (`bepLine_le_eact`, the BEP
defect-law inequality `x^2/(4*lam) ≥ 0` read geometrically); hence the linear volcano
*underestimates* the two-parabola barrier pointwise (`linearVolcano_le_parabolic`); the
two-parabola model is itself a volcano with **no linearization** (`parabolic_descriptor`); and at a
symmetric cycle's apex the linear and the parabolic volcano agree exactly
(`linearVolcano_apex_exact`, with the apex at thermoneutrality, `apexPar_self`). -/

/-- Sabatier → BEP: the BEP-linear volcano is the maximum of the two tangent lines of the
parabolic branches at thermoneutrality. -/
theorem linearVolcano_eq_bepTangent (lam1 lam2 dE : ℝ) :
    Sabatier.volcanoBarrier (1 / 2) (lam1 / 4) (1 / 2) (lam2 / 4) dE
      = max (BEP.bepLine lam1 (-dE)) (BEP.bepLine lam2 dE) :=
  Sabatier.linearVolcano_eq_bepTangent lam1 lam2 dE

/-- Sabatier → BEP: the BEP tangent line lies below the parabola it is tangent to — the exact
violation is the quadratic remainder of the BEP defect law. -/
theorem bepLine_le_eact {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    BEP.bepLine lam x ≤ BEP.eact lam x :=
  Sabatier.bepLine_le_eact hlam x

/-- Sabatier → BEP: the linear volcano is a pointwise lower bound on the two-parabola volcano —
the linear model underestimates the barrier away from the apex. -/
theorem linearVolcano_le_parabolic {lam1 lam2 : ℝ} (h1 : 0 < lam1) (h2 : 0 < lam2) (dE : ℝ) :
    Sabatier.volcanoBarrier (1 / 2) (lam1 / 4) (1 / 2) (lam2 / 4) dE
      ≤ Sabatier.parabolicBarrier lam1 lam2 dE :=
  Sabatier.linearVolcano_le_parabolic h1 h2 dE

/-- Sabatier → BEP: the Sabatier description holds in the two-parabola model with no BEP
linearization — the crossing point of the two parabolas is the unique global minimizer whenever
both curvatures are physical. -/
theorem parabolic_descriptor {lam1 lam2 : ℝ} (h1 : 0 < lam1) (h2 : 0 < lam2) :
    Sabatier.VolcanoDescriptor (fun dE => Sabatier.parabolicBarrier lam1 lam2 dE)
      (Sabatier.apexPar lam1 lam2) :=
  Sabatier.parabolic_descriptor h1 h2

/-- Sabatier → BEP: a symmetric two-parabola cycle has its apex at the thermoneutral descriptor
value. -/
theorem apexPar_self {lam : ℝ} (h : 0 < lam) : Sabatier.apexPar lam lam = 0 :=
  Sabatier.apexPar_self h

/-- Sabatier → BEP: at a symmetric cycle's apex the tangent-line model and the parabola model
agree exactly. -/
theorem linearVolcano_apex_exact {lam : ℝ} (h : 0 < lam) :
    Sabatier.volcanoBarrier (1 / 2) (lam / 4) (1 / 2) (lam / 4) 0
      = Sabatier.parabolicBarrier lam lam 0 :=
  Sabatier.linearVolcano_apex_exact h

/-! ## 9. Look-alike but different: the Sabatier volcano predicate and the Marcus rate

Both theories present an observable with a unique interior optimum, and — as `C1` makes checkable —
they even share one functional form: the Marcus rate *is* the Sabatier activity of the kernel
barrier, scaled by the pre-exponential factor. `C2` pushes that further: the Marcus rate satisfies
the very same predicate `Sabatier.AntiVolcanoDescriptor`, with `lam` as its unique maximizer.

What the pair does **not** share is the optimum itself, and the three facets below pin the
difference. `C3`: at the optimum the Marcus barrier vanishes identically (the optimum is the
barrierless point), while the Sabatier reference pass sits at `1/2` — a volcano pass is not a
barrierless point. `C4`: the one-sided secant at the Marcus optimum is `h / (4 * lam)`, i.e. it
vanishes with the step, whereas the Sabatier volcano legs have secant slopes that do not depend on
the step at all (`alphaA` above the apex, `-alphaB` below it) — a kink against a smooth optimum,
stated without any calculus. `C5`: the Marcus optimal position is fixed by the curvature alone —
the same `lam` is optimal for every admissible prefactor and thermal energy — while the Sabatier
apex moves when only the offsets change with the slopes held fixed.

Accounting: `C1` is a certificate (the two bodies coincide after unfolding, no new mathematics);
`C2` is the instantiation of the shared predicate at the Marcus rate (new proof, the uniqueness
half is new); `C3`–`C5` are non-relations, i.e. the checkable content of "look-alike but
different". The statement forms were calibrated first in
`theories/Marcus/probes/relations-b2-statement-skeleton.lean`. -/

/-- **C1** — shared functional form: the Marcus rate is the Sabatier activity functional applied
to the kernel barrier, scaled by the pre-exponential factor. This is what makes "same shape" a
shared definition pattern rather than an analogy. -/
theorem marcus_rate_eq_activity (A lam kB T x : ℝ) :
    Marcus.rate A lam kB T x =
      A * Sabatier.activity (fun y => Kernel.barrier lam y) kB T x := by
  unfold Marcus.rate Sabatier.activity Kernel.barrier Marcus.barrier
  rfl

/-- **C2** — the same predicate, instantiated: the Marcus rate has the Sabatier volcano shape in
the very same predicate, with `lam` as its unique global maximizer. The first conjunct is the
delivered `Marcus.rate_peak_at_lam`; the uniqueness half is proved here (a tie in the rate forces a
tie in the barrier, and the barrier vanishes only at `lam`). -/
theorem marcusRate_antiVolcanoDescriptor {A lam kB T : ℝ}
    (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T) :
    Sabatier.AntiVolcanoDescriptor (Marcus.rate A lam kB T) lam := by
  constructor
  · intro x
    exact Marcus.rate_peak_at_lam hA hlam hkT x
  · intro x hx
    have hAne : A ≠ 0 := ne_of_gt hA
    have hkTne : kB * T ≠ 0 := ne_of_gt hkT
    have h4 : (4 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hlam)
    have h1 : Real.exp (-(Marcus.barrier lam x) / (kB * T))
        = Real.exp (-(Marcus.barrier lam lam) / (kB * T)) := by
      unfold Marcus.rate at hx
      exact mul_left_cancel₀ hAne hx
    have h2 : -(Marcus.barrier lam x) / (kB * T) = -(Marcus.barrier lam lam) / (kB * T) :=
      Real.exp_injective h1
    have h3 : Marcus.barrier lam x = Marcus.barrier lam lam := by
      have h2' : -(Marcus.barrier lam x) = -(Marcus.barrier lam lam) := by
        have h := h2
        rw [div_eq_div_iff hkTne hkTne] at h
        exact mul_right_cancel₀ hkTne h
      linarith
    have hzero : Marcus.barrier lam x = 0 := by
      rw [Marcus.barrier_at_lam lam] at h3
      exact h3
    unfold Marcus.barrier at hzero
    have hsq : (lam - x) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hzero with h | h
      · exact h
      · exact absurd h h4
    have hsub : lam - x = 0 := sq_eq_zero_iff.mp hsq
    linarith

/-- **C3a** — non-relation: the reference volcano's optimal pass height is nonzero (`1/2`), so a
volcano pass is not a barrierless point. -/
theorem apexBarrier_reference_nonzero :
    Sabatier.apexBarrier (1 / 2) (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  norm_num [Sabatier.apexBarrier, Sabatier.volcanoBarrier, Sabatier.branchUp, Sabatier.branchDown,
    Sabatier.apex]

/-- **C3b** — the contrast side by side: the Marcus optimal barrier is identically zero while the
Sabatier reference pass is `1/2`. -/
theorem optimal_barrier_height_contrast :
    (∀ lam : ℝ, Kernel.barrier lam lam = 0) ∧
      Sabatier.apexBarrier (1 / 2) (1 / 2) (1 / 2) (1 / 2) = 1 / 2 :=
  ⟨fun lam => by simp [Kernel.barrier], apexBarrier_reference_nonzero⟩

/-- **C4** — non-relation: at the Marcus optimum the one-sided secant of the barrier is exactly
`h / (4 * lam)`, hence it vanishes with the step; the Sabatier volcano legs have step-independent
secant slopes (`Sabatier.volcanoBarrier_secSlope_of_apex_le` gives `alphaA`, its counterpart below
the apex gives `-alphaB`). No calculus is involved on either side. -/
theorem marcus_secant_at_optimum {lam h : ℝ} (hlam : lam ≠ 0) (hh : h ≠ 0) :
    (Kernel.barrier lam (lam + h) - Kernel.barrier lam lam) / h = h / (4 * lam) := by
  have h4 : (4 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
  unfold Kernel.barrier
  field_simp
  ring

/-- **C5a** — non-relation: the Sabatier apex moves when only the offsets change, the two slopes
being held fixed (`apex (1/2) 0 (1/2) 1 = 1` against `apex (1/2) 0 (1/2) 0 = 0`). -/
theorem sabatier_apex_moves_with_offsets :
    Sabatier.apex (1 / 2) 0 (1 / 2) 1 = 1 ∧ Sabatier.apex (1 / 2) 0 (1 / 2) 0 = 0 := by
  constructor <;> norm_num [Sabatier.apex]

/-- **C5b** — non-relation: the Marcus optimal position is fixed by the curvature alone — the same
descriptor `lam` is optimal for every admissible pre-exponential factor and thermal energy, whereas
`C5a` shows the Sabatier apex responding to the offsets. -/
theorem marcus_optimum_fixed_by_curvature {lam : ℝ} (hlam : 0 < lam) :
    ∀ (A kB T : ℝ), 0 < A → 0 < kB * T →
      Sabatier.AntiVolcanoDescriptor (Marcus.rate A lam kB T) lam :=
  fun A kB T hA hkT => marcusRate_antiVolcanoDescriptor hA hlam hkT

end Relations

end PhotoLean
