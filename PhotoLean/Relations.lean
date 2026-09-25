/-
PhotoLean.Relations — the single home of the cross-theory relations of the delivered theories.

Seven theories are delivered, and they sit on the shared kernel in four different ways: the three
two-parabola theories (Marcus, Hammond, BEP) are readings of one equal-curvature quadratic object,
defined once in `PhotoLean.Kernel`; the two second-batch theories (Kasha, Sabatier) join through
**composition** edges (§7–§8) rather than by sharing that object; the sixth (Goldschmidt) shares no
module and no scalar with the others and is registered through the **no-edge** registry (§10); the
seventh (SymmetryFactor) generalizes the kernel's two-parabola object to **unequal curvatures** and
enters as the graph's first **adjudicated conflation** (§11, class A1). The relation inventory of
all seven is collected here, organised by edge type:

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
* §11 **adjudicated conflation** (class A1, the seventh theory): a reading the literature takes as
  a universal working value — the β = 1/2 symmetry factor — decided by the kernel against the
  structural transfer coefficient, with its **exact validity boundary** (`↔ kr = kp`) and its
  tie-back certificates to `Kernel.tsCoord` and `BEP.transfer`. An N-row says "similar shape, no
  edge"; an A-row says "treated as the same, here is the kernel's boundary of that sameness".

The re-exports of §1–§5, §7–§8 and §11 add no mathematics — they are certificates and a ledger, and
their value is the compile-time pin: every statement below is written out in full, so a statement
drift anywhere upstream makes this module fail to compile. The declarations proved here rather than
reused are the last one of §3, the three of §6, the kernel certificate of §7, and the seven of §9;
§11 re-exports the A1 verdict rows (their mathematics lives in `PhotoLean.SymmetryFactor`). Every
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
import PhotoLean.SymmetryFactor.Sharp
import PhotoLean.KashaVavilov.Basic
import PhotoLean.KashaVavilov.Criterion
import PhotoLean.KashaVavilov.Instances
import PhotoLean.SternVolmer.Basic
import PhotoLean.SternVolmer.Criterion
import PhotoLean.QuantumYield.Basic
import PhotoLean.QuantumYield.Criterion
import PhotoLean.FluorPhos.Basic
import PhotoLean.FluorPhos.Criterion
import PhotoLean.EnergyGapLaw.Basic
import PhotoLean.EnergyGapLaw.Criterion
import PhotoLean.EnergyGapLaw.Sharp
import PhotoLean.StokesShift.Basic
import PhotoLean.StokesShift.Criterion
import PhotoLean.ICvsISC.Basic
import PhotoLean.ICvsISC.Criterion
import PhotoLean.ICvsISC.RatModel
import PhotoLean.Forster.Basic
import PhotoLean.Forster.Criterion
import PhotoLean.Einstein.Basic
import PhotoLean.Einstein.Criterion
import PhotoLean.RACI.Main
import PhotoLean.RACI.Barrier
import PhotoLean.RACI.Jablonski
import PhotoLean.RACI.TwoState
import PhotoLean.RACI.Torsion
import PhotoLean.Marcus.Basic

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
  fun A kB T hA hkT =>
    marcusRate_antiVolcanoDescriptor (A := A) (lam := lam) (kB := kB) (T := T) hA hlam hkT

/-! ## 10. The no-edge registry (documentation, not theorems)

An absent edge is a registered fact, not an oversight: the relation graph is complete in the sense
that *every* theory sits on it. The pairs without an edge, and why:

* **Kasha ↔ BEP — no edge.** Kasha consumes exactly one object of the family, the Marcus barrier
  inside `Kasha.marcusIC` (§7). The BEP content — the affine line, its exact quadratic defect law
  and the tolerance/radius criterion — is stated for the *barrier profile of a family of steps*,
  and no row of the ladder theory mentions a line law, a defect or a window. Dependency fact:
  `PhotoLean/Kasha/*` imports `PhotoLean.Marcus.Basic` only, never `PhotoLean.BEP.*`.
* **Kasha ↔ Hammond — no edge.** The Hammond content is the *structural* coordinate `q‡` and its
  monotonicity; the ladder theory tracks branching probabilities, not geometries. No row connects a
  crossing coordinate to a cascade probability. Dependency fact: `PhotoLean.Hammond.*` and
  `PhotoLean.Kasha.*` share no module.
* **Sabatier ↔ Hammond — no edge.** Sabatier consumes `PhotoLean.BEP.Basic` (the two branches and
  their tangent lines) and never the structural reading. Dependency fact: `PhotoLean/Sabatier/*`
  imports `PhotoLean.BEP.Basic` only.
* **Sabatier ↔ Kasha — no edge.** The two second-batch theories share no module and no object: one
  is a descriptor-axis optimisation, the other an excited-state cascade.
* **Goldschmidt ↔ all six — no edge.** The Goldschmidt theory (`theories/goldschmidt/`,
  `PhotoLean/Goldschmidt/*`) formalizes a *geometric* criterion: the tolerance factor
  `t = (rA + rO) / (√2 * (rB + rO))` of an `ABO₃` perovskite, its band verdict, and Goldschmidt's
  three rules of ionic substitution. It has no energy model at all — no potential-energy surface, no
  barrier, no rate, no descriptor axis, no cascade, no curvature pair — so there is no object for an
  edge to be about.
  Dependency fact (measured with `grep -rn '^import' PhotoLean/Goldschmidt`): `Basic` and `Rules`
  import `Mathlib` only; `Criterion` imports `Basic`; `Sharp` imports `Basic + Rules + Criterion`;
  `RatModel` imports `Basic + Criterion + Rules`; `Instances` imports **four** of them (`Basic` +
  `Rules` + `Criterion` + `RatModel` — it does not import `Sharp`). No module of the
  family is imported, and no module of the family mentions `tolFac`, `GoldschmidtConforms` or any
  radius (measured: `grep -rln 'tolFac\|Goldschmidt' PhotoLean/ --include='*.lean'` returns only
  `PhotoLean/Goldschmidt/*` plus this registry comment itself, whose prose contains both words). Modelling reason: the six delivered theories state facts about
  *energies* along one reaction coordinate; Goldschmidt's states facts about *lengths* in a crystal,
  and the two vocabularies share no scalar.
* **Goldschmidt ↔ Sabatier — a look-alike of shape, with no edge.** Two shapes coincide: (i) a
  symmetric band about an ideal value *is* an absolute-deviation bound —
  `GoldschmidtConforms (1 - delta) (1 + delta) rA rB rO ↔ |rA - idealA rB rO| ≤ delta * idealAO rB rO`
  versus `Sabatier.NearOptimal tol apexD dE := |dE - apexD| ≤ tol` and its band reading; (ii) a
  three-way classifier of a scalar against a band — `GoldschmidtZone`/`goldschmidtZone` versus
  `Sabatier.SZone`/`sabatierZone`. No theorem transfers across it: the scalars are unrelated (a
  radius ratio versus a binding energy, with no delivered map between them), Goldschmidt's window
  equivalence is exact for *every* band (no nonemptiness premise) while Sabatier's sharp condition is
  the product condition `0 < alphaA * alphaB`, and the two classifiers decide different propositions
  (squares of rationals versus reals compared through `√2`). Registering the coincidence is the
  honest move: it is a shape, not an edge.
* **Marcus ↔ BEP and Marcus ↔ Hammond — first batch.** Registered in §2–§5 (true equivalences, the
  headline `epBounds_iff_no_inverted_direction`, the definitional aliases).
* **Marcus ↔ Sabatier — §9.** The look-alike pair: one shared functional form and predicate, three
  non-relations.
* **SymmetryFactor ↔ Marcus, Hammond, BEP — §11 (yes, A1 + specialization).** The seventh theory
  generalizes the kernel's two-parabola object to unequal curvatures; at the equal-curvature
  diagonal its coordinate IS `Kernel.tsCoord · 0` and IS `BEP.transfer · 0` (certificates below),
  and its A1 verdict decides the β = 1/2 reading that the E1 chain identifies with the structural
  coefficient. Dependency fact: `Sharp` imports `PhotoLean.Kernel` and `PhotoLean.BEP.Criterion`.
* **SymmetryFactor ↔ Kasha, Sabatier, Goldschmidt — no edge.** The curvature-pair scalar `(kr, kp)`
  of the seventh theory shares no object with the ladder's branching rates, the volcano's
  descriptor axis, or the ionic radii. Dependency fact (measured with `grep -rn '^import'
  PhotoLean/SymmetryFactor`): `Basic` imports `Mathlib` only; `Criterion` imports `Basic`; `Sharp`
  imports `Criterion + Kernel + BEP.Criterion` (`Basic` transitively); `RatModel` imports `Basic`;
  `Instances` imports `RatModel + Sharp`. No Kasha/Sabatier/Goldschmidt module is imported by any
  of them.

Re-derive the dependency facts with
`grep -rn '^import' PhotoLean/Kasha PhotoLean/Sabatier PhotoLean/Hammond PhotoLean/Goldschmidt PhotoLean/SymmetryFactor`. -/

/-! ## 11. Adjudicated conflation (class A1): the β = 1/2 symmetry factor vs the structural transfer coefficient

The first row of a new registration class. An N-row (§6, §9) says "similar shape, no edge"; an
A-row says something stronger: **the literature treats two readings as interchangeable, and the
kernel decides the identification with its exact validity boundary**. The practice locus is
first-hand on record (`theories/SymmetryFactor/LITERATURE.md` S1: the charge-transfer coefficient
"usually both taken to be equal to 0.5", with no force-constant condition); the warning record is
IUPAC TR 2014, printed pp. 255–257 (S2: the value "can by no means be assumed"; β deviates from
0.5 exactly when the two force constants differ). The seventh theory
(`PhotoLean/SymmetryFactor`) turns the warning into the verdict `BetaHalfReading kr kp ↔ kr = kp`
over the unequal-curvature two-parabola model, with kernel-checked witnesses `(1,4) ↦ 2/3 ≠ 1/2`
and `(4,1) ↦ 1/3`, and — the persistence half — `BetaHalfReading lam lam` throughout the
equal-curvature family, the regime of the delivered kernel and of every textbook picture. The four
rows below are two tie-back certificates and two re-exports; the mathematics lives in
`PhotoLean.SymmetryFactor.*`, none of it here. -/

/-- A1 certificate: at equal curvature the seventh theory's thermoneutral coordinate is the
kernel's transition-state coordinate. -/
theorem symmetryFactor_tsCoordZero_eq_kernel {lam : ℝ} (hlam : 0 < lam) :
    SymmetryFactor.tsCoordZero lam lam = Kernel.tsCoord lam 0 :=
  SymmetryFactor.tsCoordZero_eq_kernel_thermoneutral hlam

/-- A1 certificate: at equal curvature it is the delivered BEP transfer coefficient at
thermoneutrality — extending the E1 chain (`transfer = tsCoord`) to the seventh node. -/
theorem symmetryFactor_tsCoordZero_eq_bepTransfer {lam : ℝ} (hlam : 0 < lam) :
    SymmetryFactor.tsCoordZero lam lam = BEP.transfer lam 0 :=
  SymmetryFactor.betaHalf_eq_transfer_thermoneutral hlam

/-- A1 verdict (re-export): the β = 1/2 reading holds exactly when the two force constants agree. -/
theorem symmetryFactor_betaHalf_iff {kr kp : ℝ} (hkr : 0 < kr) (hkp : 0 < kp) :
    SymmetryFactor.BetaHalfReading kr kp ↔ kr = kp :=
  SymmetryFactor.betaHalf_iff_equalForceConstants hkr hkp

/-- A1 falsification-and-persistence (re-export): the conflated reading is refuted at a
kernel-checked unequal pair, and holds throughout the equal-curvature family — the two halves of
the adjudication in one row. -/
theorem symmetryFactor_conflation_falsified_and_holds_in_kernel :
    ¬ SymmetryFactor.BetaHalfReading 1 4 ∧
      ∀ lam : ℝ, 0 < lam → SymmetryFactor.BetaHalfReading lam lam :=
  ⟨SymmetryFactor.betaHalf_falsified_by_unequal,
   fun _ hlam => SymmetryFactor.betaHalf_holds_in_kernel hlam⟩


/-! ## 12. Kernel certificates of the photophysics batch (definitional pins)

The photophysics subgraph (nine theories, 2026-09-22/23) joins the graph through the same
`rfl`-certificate discipline as §1: the two-parabola theories of group B carry their own copies of
the kernel objects, and the rows below pin each copy to `PhotoLean.Kernel` / `PhotoLean.Marcus`
definitionally. A failing `rfl` here is a regression alarm, exactly as in §1.

Accounting: every row in §12–§15 is either a certificate re-export (no new mathematics) or a new
composition/adjudication row proved here; the four adjudication re-exports of §13/§14 add no
mathematics either (the theorems live in the theories). -/

/-- Batch certificate: the energy-gap-law barrier is the kernel barrier. -/
theorem eg_barrier_eq_kernel (lam x : ℝ) : EnergyGapLaw.nrBarrier lam x = Kernel.barrier lam x :=
  EnergyGapLaw.cert_nrBarrier lam x

/-- Batch certificate: the energy-gap-law rate is the Marcus rate. -/
theorem eg_rate_eq_marcus (A lam kB T x : ℝ) :
    EnergyGapLaw.nrRate A lam kB T x = Marcus.rate A lam kB T x :=
  EnergyGapLaw.cert_nrRate A lam kB T x

/-- Batch certificate: the energy-gap-law inverted-gap predicate is the Marcus inverted region. -/
theorem eg_invertedGap_iff_marcus (lam x : ℝ) :
    EnergyGapLaw.InvertedGap lam x ↔ Marcus.InvertedRegion lam x :=
  EnergyGapLaw.cert_invertedGap lam x

/-- Batch certificate: the Stokes-shift ground surface is the kernel reactant surface. -/
theorem ss_s0Surface_eq_kernel (lam q : ℝ) :
    StokesShift.s0Surface lam q = Kernel.reactantSurface lam q :=
  StokesShift.cert_s0Surface lam q

/-- Batch certificate: the Stokes-shift excited surface is the kernel product surface. -/
theorem ss_s1Surface_eq_kernel (lam e00 q : ℝ) :
    StokesShift.s1Surface lam e00 q = Kernel.productSurface lam e00 q :=
  StokesShift.cert_s1Surface lam e00 q

/-- Batch certificate: the IC-vs-ISC Franck–Condon barrier is the kernel barrier. -/
theorem icvscic_barrier_eq_kernel (lam x : ℝ) :
    ICvsISC.fcBarrier lam x = Kernel.barrier lam x :=
  ICvsISC.cert_fcBarrier

/-- Batch certificate: the IC-vs-ISC internal-conversion rate is the Marcus rate. -/
theorem icvscic_icRate_eq_marcus (AI lamI kB T xI : ℝ) :
    ICvsISC.icRate AI lamI kB T xI = Marcus.rate AI lamI kB T xI :=
  ICvsISC.cert_icRate

/-! ## 13. The D2 adjudication (class A2: adjudicated independence) — Kasha vs Kasha–Vavilov

The eighth theory (`PhotoLean/KashaVavilov`) adjudicates the pair of rules the literature runs
together. An A1 row (§11) decides a *conflation* (two readings used interchangeably, with an exact
validity boundary); an **A2 row decides an independence claim**: the two rules are *not* the same
statement — each has admissible witnesses where it holds and the other fails, at positive
excitation levels inside the lossy regime — and they coincide exactly under the closed
quantification with a loss channel at the lowest level (the boundary re-uses the delivered
`Kasha.kashaRule_iff_vavilovUpTo`), while the lossless corner separates the closed forms. The
persistence half (why the identification survives in practice): every ordinary lossy fluorophore
sits in the regime where the closed forms coincide, so the two rules are never seen to differ
except in the degenerate lossless model and in single-step readings. -/

/-- **D2 verdict (re-export)**: the four-part adjudication — pointwise independence both
directions (witnesses at `N = 1`, `ic 0 = 1 > 0`), the closed-form coincidence boundary, and the
lossless separation that makes the loss premise load-bearing. -/
theorem kv_d2_verdict :
    (∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 2 ∧ Kasha.KashaRule rad ic 1 ∧
        ¬ Kasha.VavilovAt rad ic 1 ∧ 0 < ic 0) ∧
      (∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 2 ∧ Kasha.VavilovAt rad ic 1 ∧
        ¬ Kasha.KashaRule rad ic 1 ∧ 0 < ic 0) ∧
      (∀ (rad ic : ℕ → ℝ) (N : ℕ), Kasha.RateData rad ic N → 0 < ic 0 →
        (Kasha.KashaRule rad ic N ↔ Kasha.VavilovUpTo rad ic N)) ∧
      (∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 1 ∧ ic 0 = 0 ∧
        Kasha.VavilovUpTo rad ic 1 ∧ ¬ Kasha.KashaRule rad ic 1) :=
  KashaVavilov.d2_verdict

/-- **D2 boundary (re-export)**: a violation of Kasha's rule is always an observable anti-Kasha
emission under `RateData` — the maximal-emitter argument. -/
theorem kv_antiKasha_boundary {rad ic : ℕ → ℝ} {N : ℕ} (h : Kasha.RateData rad ic N) :
    (0 < Kasha.upperYield rad ic N ↔ ¬ Kasha.KashaRule rad ic N) :=
  KashaVavilov.antiKasha_observable_iff h

/-! ## 14. The D1 adjudication (class A3: identifiability) — static vs dynamic quenching

The second theory of group A (`PhotoLean/SternVolmer`) adjudicates the Stern–Volmer
identifiability question. An **A3 row decides an identifiability claim**: two mechanisms that a
single observable cannot distinguish (the intensity-only Stern–Volmer plot is linear for both, and
matched parameters give pointwise-identical curves at every concentration), with the discriminating
observable (the lifetime channel) as the exact boundary: within the two-mechanism model space,
lifetime-tracking holds **iff** the mechanism is dynamic. The persistence half: routine practice
measures intensity only — lifetime resolution is a separate experiment — so the conflation survives
in the literature; upward curvature (the second difference `2·KSV·Ka·h²`) is the positive witness
that *both* mechanisms are present. -/

/-- **D1 verdict (re-export)**: the three-part adjudication — both plots linear, the intensity
coincidence (non-injectivity of the intensity-only observation map), and the lifetime-tracking
boundary. Weakest premises after the Phase-3 audit: `k0 ≠ 0`, `0 < Ka`. -/
theorem sv_d1_verdict {k0 kq Ka : ℝ} (hk0 : k0 ≠ 0) (hKa : 0 < Ka) :
    (∀ q, SternVolmer.svRatioDyn k0 kq q = 1 + SternVolmer.KSV k0 kq * q ∧
        SternVolmer.svRatioStat Ka q = 1 + Ka * q) ∧
      (∀ q, SternVolmer.svRatioDyn k0 kq q = SternVolmer.svRatioStat (SternVolmer.KSV k0 kq) q) ∧
        ∀ m : SternVolmer.Mech,
          (SternVolmer.LifetimeTracks m k0 kq Ka ↔ m = SternVolmer.Mech.dyn) :=
  SternVolmer.d1_verdict hk0 hKa

/-- **D1 boundary (re-export)**: the identifiability boundary alone — `0 < Ka` load-bearing, no
hypothesis on `k0` or `kq`. -/
theorem sv_identifiability_boundary {k0 kq Ka : ℝ} (hKa : 0 < Ka) :
    ∀ m : SternVolmer.Mech, (SternVolmer.LifetimeTracks m k0 kq Ka ↔ m = SternVolmer.Mech.dyn) :=
  SternVolmer.lifetimeTracks_iff_dyn hKa

/-! ## 15. Composition edges of the batch (proved here)

The photophysics subgraph's own composition edges: the algebraic spine is `QuantumYield` (the
parallel-channel calculus), and the four rate-level theories reduce to it — the Stern–Volmer
dilution, the fluorescence/phosphorescence cascade, the FRET added-donor channel, and the Einstein
radiative-rate anchor. The two-parabola theories compose through the kernel (§12) and through two
new rows: the energy-gap ordering of the Kasha internal-conversion rates (extending §7), and the
Stokes/emission-window boundary of the EGL barrier. The IC→EG certificate is definitional. Two
shape rows register the look-alikes with machine content: the SV/FO shared `1 + control` form and
the EG/Hammond boundary identification. -/

/-- QY ↔ Kasha: the ladder's radiative branch is the two-channel quantum yield. -/
theorem kasha_radBranch_eq_yieldOf (rad ic : ℕ → ℝ) (n : ℕ) :
    Kasha.radBranch rad ic n = QuantumYield.yieldOf ![rad n, ic n] 0 := by
  unfold Kasha.radBranch Kasha.decay QuantumYield.yieldOf QuantumYield.totalRate
  norm_num [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- SV → QY: dynamic quenching is exactly quantum-yield dilution — the unquenched yield is the
quenched yield times the Stern–Volmer ratio (true for every rate vector with positive total and a
nonnegative quench channel; the `kr = 0` corner is consistent under totalized division, both sides
vanishing). -/
theorem sv_quench_dilutes_yield (kr knr kq q : ℝ) (hpos : 0 < kr + knr) (hq : 0 ≤ kq * q) :
    QuantumYield.yieldOf ![kr, knr] 0 =
      QuantumYield.yieldOf ![kr, knr + kq * q] 0 * SternVolmer.svRatioDyn (kr + knr) kq q := by
  have hpq : 0 < kr + knr + kq * q := by linarith
  have hy0 : QuantumYield.yieldOf ![kr, knr] 0 = kr / (kr + knr) := by
    unfold QuantumYield.yieldOf QuantumYield.totalRate
    rw [Fin.sum_univ_succ]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hyq : QuantumYield.yieldOf ![kr, knr + kq * q] 0 = kr / (kr + (knr + kq * q)) := by
    unfold QuantumYield.yieldOf QuantumYield.totalRate
    rw [Fin.sum_univ_succ]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [hy0, hyq, SternVolmer.svRatioDyn, SternVolmer.dynDecay]
  rw [show kr + (knr + kq * q) = kr + knr + kq * q from by ring]
  field_simp [ne_of_gt hpos, ne_of_gt hpq]

/-- FP → QY (1): the fluorescence yield is the three-channel quantum yield. -/
theorem phiF_eq_yieldOf (kF kISC kIC : ℝ) :
    FluorPhos.phiF kF kISC kIC = QuantumYield.yieldOf ![kF, kISC, kIC] 0 := by
  unfold FluorPhos.phiF FluorPhos.s1Decay QuantumYield.yieldOf QuantumYield.totalRate
  norm_num [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- FP → QY (2): the phosphorescence yield is the cascade product of two quantum yields. -/
theorem phiP_eq_yieldOf_cascade (kF kISC kIC kP kNR : ℝ) :
    FluorPhos.phiP kF kISC kIC kP kNR =
      QuantumYield.yieldOf ![kF, kISC, kIC] 1 * QuantumYield.yieldOf ![kP, kNR] 0 := by
  have hs3 : QuantumYield.totalRate ![kF, kISC, kIC] = kF + kISC + kIC := by
    unfold QuantumYield.totalRate
    rw [Fin.sum_univ_three]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  have hs2 : QuantumYield.totalRate ![kP, kNR] = kP + kNR := by
    unfold QuantumYield.totalRate
    rw [Fin.sum_univ_succ]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  unfold FluorPhos.phiP FluorPhos.iscBranch FluorPhos.t1BranchP FluorPhos.s1Decay
    QuantumYield.yieldOf
  rw [hs3, hs2]
  field_simp

/-- EB → QY: the fluorescence yield of the two-channel decay with radiative rate `A` is the
QuantumYield of the pair — the Einstein-side anchor of the radiative channel. -/
theorem einstein_yield_via_qy (A kNR : ℝ) :
    A * Einstein.tauR (A + kNR) = QuantumYield.yieldOf ![A, kNR] 0 := by
  have hy : QuantumYield.yieldOf ![A, kNR] 0 = A / (A + kNR) := by
    unfold QuantumYield.yieldOf QuantumYield.totalRate
    rw [Fin.sum_univ_succ]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [hy, Einstein.tauR, mul_one_div]

/-- FO → QY: the FRET efficiency is one minus the donor yield of the channel-added model —
the "FRET is an added donor channel" composition. -/
theorem fretEff6_eq_one_sub_yieldOf (kD r6 R : ℝ) (hkD : 0 < kD) (hr6 : 0 ≤ r6) (hR : R ≠ 0) :
    Forster.fretEff6 r6 R = 1 - QuantumYield.yieldOf ![kD, kD * (r6 / R ^ 6)] 0 := by
  have hR2 : (0 : ℝ) < R ^ 2 := sq_pos_of_ne_zero hR
  have hR6 : (0 : ℝ) < R ^ 6 := by
    rw [show R ^ 6 = (R ^ 2) ^ 3 from by ring]
    exact pow_pos hR2 3
  have hsum : (0 : ℝ) < kD + kD * (r6 / R ^ 6) := by
    have : (0 : ℝ) ≤ kD * (r6 / R ^ 6) :=
      mul_nonneg (le_of_lt hkD) (div_nonneg hr6 (le_of_lt hR6))
    linarith
  unfold Forster.fretEff6 QuantumYield.yieldOf QuantumYield.totalRate
  rw [Fin.sum_univ_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  field_simp
  ring

/-- EG → Kasha (extends §7): in the inverted region a bigger gap slows the Marcus-form
internal-conversion rate — the energy-gap-law rationale of the Kasha funnel. -/
theorem marcusIC_strictAnti_on_inverted_gaps {A lam kB T x₁ x₂ : ℝ} (hA : 0 < A)
    (hlam : 0 < lam) (hkT : 0 < kB * T) (hx1 : lam < x₁) (hx : x₁ < x₂) :
    Kasha.marcusIC A lam kB T x₂ < Kasha.marcusIC A lam kB T x₁ := by
  unfold Kasha.marcusIC PhotoLean.Marcus.barrier
  have hsq : (lam - x₁) ^ 2 < (lam - x₂) ^ 2 := by nlinarith [hx1, hx, hlam]
  have hdiv : (lam - x₁) ^ 2 / (4 * lam) < (lam - x₂) ^ 2 / (4 * lam) := by
    apply div_lt_div_of_pos_right hsq
    linarith
  have hexp : Real.exp (-((lam - x₂) ^ 2 / (4 * lam)) / (kB * T))
      < Real.exp (-((lam - x₁) ^ 2 / (4 * lam)) / (kB * T)) := by
    apply Real.exp_strictMono
    have hkT' : 0 < kB * T := hkT
    rw [neg_div, neg_div, neg_lt_neg_iff]
    exact div_lt_div_of_pos_right hdiv hkT'
  exact mul_lt_mul_of_pos_left hexp hA

/-- SS → EG: the EGL barrier vanishes at the gap exactly when the Stokes emission window closes. -/
theorem egBarrier_zero_iff_emEnergy_zero {lam e00 : ℝ} (hlam : lam ≠ 0) :
    EnergyGapLaw.nrBarrier lam e00 = 0 ↔ StokesShift.emEnergy lam e00 = 0 := by
  unfold EnergyGapLaw.nrBarrier StokesShift.emEnergy StokesShift.s1Surface StokesShift.s0Surface
  constructor
  · intro h
    have h4 : (4 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
    have hsq : (lam - e00) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp h with h' | h'
      · exact h'
      · exact absurd h' h4
    have := sq_eq_zero_iff.mp hsq
    linarith
  · intro h
    have : lam - e00 = 0 := by linarith
    rw [this]
    norm_num

/-- IC → EG certificate: the IC rate IS the energy-gap-law rate. -/
theorem icvscic_icRate_eq_eg_nrRate (A lam kB T x : ℝ) :
    ICvsISC.icRate A lam kB T x = EnergyGapLaw.nrRate A lam kB T x := by
  unfold ICvsISC.icRate EnergyGapLaw.nrRate ICvsISC.fcBarrier EnergyGapLaw.nrBarrier
  rfl

/-- SV ↔ FP (composition): dynamic quenching of S₁ does not move the
fluorescence/phosphorescence balance — the ratio is invariant. -/
theorem fpRatio_invariant_under_quench {kF kISC kIC kP kNR kq q : ℝ}
    (hkF : 0 < kF) (hs1 : 0 < FluorPhos.s1Decay kF kISC kIC)
    (hs1q : 0 < FluorPhos.s1Decay kF kISC (kIC + kq * q)) (ht1 : 0 < kP + kNR) :
    FluorPhos.phiP kF kISC (kIC + kq * q) kP kNR / FluorPhos.phiF kF kISC (kIC + kq * q) =
      FluorPhos.phiP kF kISC kIC kP kNR / FluorPhos.phiF kF kISC kIC := by
  unfold FluorPhos.phiP FluorPhos.phiF FluorPhos.iscBranch FluorPhos.t1BranchP
  field_simp [ne_of_gt hkF, ne_of_gt hs1, ne_of_gt hs1q, ne_of_gt ht1]
  ring

/-- SV ↔ FO look-alike, machine face: the FRET inverse-efficiency is a `1 + control` law with
the sixth-power distance control, the same shape as the Stern–Volmer ratio's
`1 + slope·[Q]` concentration control. -/
theorem fretEff6_inv_eq_one_plus {r6 R : ℝ} (hr6 : 0 < r6) (hR : R ≠ 0) :
    (Forster.fretEff6 r6 R)⁻¹ = 1 + R ^ 6 / r6 := by
  have hR2 : (0 : ℝ) < R ^ 2 := sq_pos_of_ne_zero hR
  have h6 : (0 : ℝ) < R ^ 6 := by
    rw [show R ^ 6 = (R ^ 2) ^ 3 from by ring]
    exact pow_pos hR2 3
  unfold Forster.fretEff6
  rw [inv_div]
  field_simp

/-- EG ↔ Hammond boundary row: the EGL regime boundary `x = lam` is exactly the Hammond
coordinate leaving the reactant interval. -/
theorem eg_boundary_eq_tsCoord_zero {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    Kernel.tsCoord lam x = 0 ↔ lam = x := by
  unfold Kernel.tsCoord
  constructor
  · intro h
    have h2 : (2 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
    have := div_eq_zero_iff.mp h
    rcases this with h' | h'
    · linarith
    · exact absurd h' h2
  · intro h
    rw [h, sub_self, zero_div]

/-! ## 16. The extended no-edge registry (documentation, not theorems)

The nine new nodes and the seven earlier ones make sixteen; the pairs WITHOUT an edge, and why
(an absent edge is a registered fact, not an oversight). Machine content lives in §12–§15; every
pair below states what would be needed and why it is not there.

* **KashaVavilov ↔ Marcus / Hammond / BEP — no edge.** The D2 layer is about branching laws of
  the ladder, not barriers or coordinates; its only contact with the two-parabola family runs
  through Kasha's §7 composition (`Kasha.marcusIC`), which the EG row of §15 now sharpens.
* **KashaVavilov ↔ Sabatier / Goldschmidt / SymmetryFactor — no edge.** No shared scalar: the
  D2 predicates speak about yields and ladders; the volcano, the ionic radii and the curvature
  pairs share none of them.
* **SternVolmer ↔ Marcus / Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor — no edge.**
  The SV model has no energy surface, no descriptor axis, no geometry: it is a rate-parameter
  model over a concentration variable. Its contacts all run through QuantumYield (§15).
* **QuantumYield ↔ Marcus / Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor — no edge.**
  The parallel-channel calculus is purely algebraic; the energy-side theories enter only through
  the specific rates that fill its channels (the Einstein `A`, the IC/ISC rates), which §15
  registers as the composition edges instead.
* **FluorPhos ↔ Marcus / Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor / StokesShift /
  EnergyGapLaw / Forster / Einstein — no edge except through QuantumYield.** The competition
  layer's objects are branch probabilities; its two composition edges (§15: `phiF_eq_yieldOf`,
  `phiP_eq_yieldOf_cascade`) and its quench-invariance edge to SV exhaust its contacts.
* **StokesShift ↔ Kasha / KashaVavilov / SternVolmer / QuantumYield / FluorPhos / ICvsISC /
  Forster / Einstein — no edge** (positions of band maxima vs rates/ladders/geometries; the
  Einstein mirror-symmetry look-alike is a shape note in the StokesShift plan §10, no theorem
  transfers: detailed balance is about intensities, the mirror rule about positions).
* **ICvsISC ↔ Kasha / KashaVavilov / SternVolmer / QuantumYield / Forster / Einstein — no edge.**
  The spin-discount competition's contacts are the kernel/EG certificates (§12/§15) and the
  premise-level link to FluorPhos's `kISC` (registered in both plans as a modelling premise, not
  a Lean row).
* **Forster ↔ Marcus / Hammond / BEP / Kasha / KashaVavilov / Sabatier / SymmetryFactor /
  StokesShift / EnergyGapLaw / ICvsISC — no edge.** The transfer geometry shares no scalar with
  the energy-surface family. Two shape registrations carry machine content: the SV look-alike
  (`fretEff6_inv_eq_one_plus`, §15) and the Goldschmidt look-alike (two geometric threshold
  criteria, no shared scalar — registered in the Forster plan §10, no row).
* **Einstein ↔ Marcus / Hammond / BEP / Kasha / KashaVavilov / Sabatier / Goldschmidt /
  SymmetryFactor / StokesShift / Forster — no edge.** The radiative conversions' only machine
  contact is the QuantumYield anchor (§15); the `J`-integral link to Förster is a modelling
  premise (registered in both plans).

* **Completion rows (added 2026-09-24; provenance: the adversarial audit's finding F8).** The
  bullets above left 26 of the 136 node pairs without a row here, although this section's opening
  reserves a row for *every* pair; the audit enumerated the C(17,2) pairs and reported the gap.
  Every pair below already carries an absence draft (or an undelivered candidate) in the
  corresponding theory's `plan.md` §10 — these rows transcribe those drafts into the register of
  record and add no mathematics. With the one in-module edge noted first, §16 now accounts for
  every pair of the sixteen-node graph.
* **StokesShift ↔ Marcus — edge, delivered inside the theory module (not re-exported here).**
  `PhotoLean.StokesShift.emEnergy_pos_iff_inverted (lam e00) : 0 < emEnergy lam e00 ↔
  PhotoLean.Marcus.InvertedRegion lam e00` (`PhotoLean/StokesShift/Criterion.lean`, row SS-C9,
  amended form); the two §12 StokesShift rows pin only the surfaces. Registered here because the
  machine edge inventory of this file does not re-export it.
* **EnergyGapLaw ↔ BEP — no edge (a registered shape edge).** The barrier profile the two share
  **is** the kernel object, already pinned (§12); BEP's own content (the affine line and its defect
  law on the transfer coefficient, the Evans–Polanyi window) occurs in no EnergyGapLaw row, and the
  plan registers the relation as a *shape* — the same second-difference engine transplanted from the
  barrier to its logarithm (`theories/EnergyGapLaw/plan.md` §10). No theorem transfers.
* **EnergyGapLaw ↔ Sabatier / Goldschmidt / SymmetryFactor / KashaVavilov / SternVolmer /
  QuantumYield / Einstein — no edge.** The delivered EnergyGapLaw links are exactly the kernel and
  Marcus pins (§12), the Kasha ordering row, the Hammond boundary row, and the StokesShift and
  ICvsISC rows (§15); none of the partner scalars (a descriptor axis, ionic radii, a curvature pair,
  a ladder, a concentration axis, a yield algebra, radiative conversions) occurs in
  `nrBarrier`/`nrRate`/`lnRate`/`egZoneQ`. Plan §10 carries the absence drafts (KashaVavilov
  appears there as an undelivered composition candidate alongside Kasha).
* **StokesShift ↔ Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor — no edge.** The
  surfaces are §12 kernel copies and the content is band positions (`absEnergy`, `emEnergy`, the
  emission window); no rate, line law, descriptor, curvature pair or radius occurs in a StokesShift
  row. Plan §10 carries the absence drafts.
* **ICvsISC ↔ Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor — no edge.** The delivered
  ICvsISC links are the §12 kernel/Marcus pins, the EnergyGapLaw rate identity (§15) and the RACI
  row (§17); its FC-barrier/spin-discount content names none of the partner scalars. Plan §10
  carries the absence drafts.
* **FluorPhos ↔ Kasha / KashaVavilov — no edge (undelivered candidate compositions).** The
  competition layer's machine contacts are the QuantumYield compositions and the SternVolmer quench
  invariance (§15); the plan's `{S₁, T₁}`-projection candidates were not carried into rows.
* **FluorPhos ↔ ICvsISC — the premise-level `kISC` identification** (registered in both plans as a
  modelling premise, not a Lean row) — the complement of the FluorPhos clause of the ICvsISC
  bullet above.
* **KashaVavilov ↔ SternVolmer / QuantumYield — undelivered candidate compositions.** The
  KashaVavilov plan registers the SternVolmer quench as an added level-0 loss and `radBranch` as a
  two-channel yield; the delivered contacts of both sides run through Kasha's §7 edge and the
  QuantumYield spine (§15).
* **Kasha ↔ SternVolmer — no edge (registered candidate, not delivered).** The SternVolmer plan
  registers dynamic quenching as an addition to the ladder's level-0 loss; no delivered row relates
  the two, and each side's delivered contacts run through the QuantumYield spine (§15).
* **Einstein ↔ SternVolmer — no edge.** Both reach the batch only through QuantumYield (§15); the
  Einstein plan registers the pair as "via QuantumYield only".
* **Forster ↔ Goldschmidt — no edge (look-alike, no machine row).** Two purely geometric threshold
  criteria — transfer geometry versus ionic radii — sharing no scalar; the Forster plan §10
  registers the shape and `GRAPH-REPORT` §6.3 states the same as a look-alike without an edge.

Dependency facts (measured): every photophysics module imports only `Mathlib` plus its own
theory's earlier modules plus (for the group-B theories) `PhotoLean.Kernel` / `PhotoLean.Marcus.Basic`;
`PhotoLean/Relations.lean` is the only module importing across the batch. The one cross-theory
content row carried by a batch module itself is StokesShift's SS-C9 above (it imports
`PhotoLean.Marcus.Basic`, an earlier theory). -/

/-! ## 17. The seventeenth node: RACI (Restricted Access to a Conical Intersection)

The RACI theory — ported from the independent ChemLean repository (`[local path removed]
ChemLean`, same Lean 4.17.0 / mathlib v4.17.0 toolchain) — formalizes the accepted mechanism of
aggregation-induced emission: a geometric constraint on the torsion angle raises the minimal
accessible energy gap to the conical intersection, the nonradiative rate drops, and with the
radiative rate (approximately) unchanged the fluorescence quantum yield rises. Its contact with
the graph is one certificate, one algebraic composition, one rate-form composition, one
composition note, and one look-alike, plus the no-edge registrations below. The integration's own
instances layer (`PhotoLean/RACI/Instances.lean`, `RatModel.lean`) carries the named admissible
model (the delivered `torsionH` with its enhancement verdict) and the named non-model
(`nonModelNoCI`, an everywhere-empty conical set — the premise chain is uninstantiable there,
kernel-checked). -/

/-- RACI ↔ QuantumYield (composition certificate): the RACI quantum yield is the two-channel
QuantumYield. -/
theorem raci_qy_eq_yieldOf_two_channel (kr knr : ℝ) :
    RACI.quantumYield kr knr = QuantumYield.yieldOf ![kr, knr] 0 := by
  unfold RACI.quantumYield QuantumYield.yieldOf QuantumYield.totalRate
  rw [Fin.sum_univ_succ]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The RACI enhancement is the two-channel strict-antitone-in-`knr` reading of the QY layer —
the dilution theorem run backwards (removing a nonradiative channel strictly enhances the
remaining yield). -/
theorem qy_two_channel_strictAnti_of_nr_lt {kr knr₁ knr₂ : ℝ} (hkr : 0 < kr)
    (h1 : 0 ≤ knr₁) (h2 : 0 ≤ knr₂) (h : knr₂ < knr₁) :
    QuantumYield.yieldOf ![kr, knr₂] 0 > QuantumYield.yieldOf ![kr, knr₁] 0 := by
  rw [← raci_qy_eq_yieldOf_two_channel, ← raci_qy_eq_yieldOf_two_channel]
  exact RACI.quantumYield_strictMono_of_knr_lt hkr h1 h2 rfl h

/-- RACI → EnergyGapLaw (composition): the M3 barrier rate's log is exactly the affine
energy-gap law with slope `-β` (the EGL tangent shape; the Marcus-lnRate is quadratic and its
tangent is the affine form — the shape note of the plan). -/
theorem log_barrierRate_eq {A β B : ℝ} (hA : 0 < A) :
    Real.log (RACI.barrierRate A β B) = Real.log A - β * B := by
  unfold RACI.barrierRate
  rw [Real.log_mul (ne_of_gt hA) (Real.exp_ne_zero _), Real.log_exp]
  ring

/-- RACI ↔ ICvsISC (composition note with machine row): at a conical intersection the
two-parabola FC barrier vanishes — the maximal-rate point of the IC/ISC competition. -/
theorem icvsisc_barrier_zero_at_crossing {lam : ℝ} :
    ICvsISC.fcBarrier lam lam = 0 := by
  unfold ICvsISC.fcBarrier
  rw [sub_self]
  norm_num

/-- RACI ↔ Marcus (look-alike, machine note): the classical two-parabola model has a real
surface crossing at the transition-state coordinate — a single-condition degeneracy (the
classical model has no coupling coordinate); the RACI CI is the two-condition degeneracy of the
two-state Hamiltonian. Different objects; the row pins the Marcus side. -/
theorem kernel_surfaces_cross_at_tsCoord {lam x : ℝ} (hlam : lam ≠ 0) :
    Kernel.reactantSurface lam (Kernel.tsCoord lam x) =
      Kernel.productSurface lam (-x) (Kernel.tsCoord lam x) := by
  unfold Kernel.reactantSurface Kernel.productSurface Kernel.tsCoord
  field_simp
  ring

/- The no-edge registrations of the seventeenth node (the pairs without an edge, with reasons):

* **RACI ↔ Hammond / BEP / Sabatier — no edge.** RACI is a nonadiabatic kinetics theory about a
  topological degeneracy; the three two-parabola "principle" theories are structural readings of
  one equal-curvature object. No shared scalar.
* **RACI ↔ Goldschmidt — no edge.** Ionic radii vs conical intersections: no object in common.
* **RACI ↔ SymmetryFactor — no edge.** The curvature-pair scalar (kr, kp) of the seventh theory
  shares nothing with the two-state Hamiltonian family.
* **RACI ↔ Kasha / KashaVavilov — shape note (no machine row).** Both stories make the IC rate
  decide emission dominance, at opposite ends: RACI blocks the lowest state's nonradiative
  escape, the ladder funnels population through fast upper-state conversion. Registered as a
  shape, not an edge.
* **RACI ↔ SternVolmer — look-alike note (opposite trend).** Aggregation quenching (SV) and
  aggregation-induced emission (RACI) are opposite environment-dependencies of the fluorescence
  yield; no theorem transfers between the two mechanisms (one is a concentration model of an
  added decay channel, the other an accessibility model of a removed one).
* **RACI ↔ FluorPhos — no edge.** The CI-mediated IC competes for the same S₁ population as the
  ISC channel of FluorPhos, but the two models share no rate object (registered premise-level).
* **RACI ↔ StokesShift — no edge.** The Stokes surfaces are single-mode displaced parabolas;
  the RACI surfaces are a two-state Hamiltonian family. The "emission window closes" row of
  StokesShift is a vertical-transition fact, not a nonadiabatic-crossing fact.
* **RACI ↔ Forster — no edge.** Transfer geometry vs nonadiabatic kinetics: no shared scalar.
* **RACI ↔ Einstein — no edge.** The radiative conversions enter RACI only as the parameter `kr`
  (the A coefficient of the S₁ → S₀ transition); no Lean row beyond the plan's registered
  premise-level note.
* **RACI ↔ QuantumYield / EnergyGapLaw / ICvsISC / Marcus — see the five machine rows above.**
-/

end Relations

end PhotoLean
