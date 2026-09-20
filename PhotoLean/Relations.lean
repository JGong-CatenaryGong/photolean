/-
PhotoLean.Relations — the single home of the cross-theory relations of the two-parabola family.

The three delivered theories share one mathematical substrate (the equal-curvature two-parabola
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

The re-exports of §1–§5 add no mathematics — they are certificates and a ledger, and their value is
the compile-time pin: every statement below is written out in full, so a statement drift anywhere
upstream makes this module fail to compile. The only declarations proved here rather than reused
are the last one of §3 and the three of §6. Every declaration is fully proved: no unproved
placeholder, no custom axiomatic declaration.

See `theories/RELATIONS.md` for the discussion draft that this module makes checkable.
-/
import PhotoLean.Kernel
import PhotoLean.Marcus.RatModel
import PhotoLean.Marcus.Sharp
import PhotoLean.Hammond.Compose
import PhotoLean.Hammond.RatModel
import PhotoLean.Hammond.Sharp
import PhotoLean.BEP.Compose
import PhotoLean.BEP.Sharp

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
`1/2 - x/(2*lam)`, an affine function, so the "more driving force, earlier transition state" law
holds with no tolerance parameter — while the BEP line law is *exactly* violated on every
non-degenerate interval (`BEP.not_epLinearOn_of_ne_zero`, the second-difference engine): no affine
model reproduces the barrier, the exact defect being the quadratic remainder `x²/(4*lam)`. This is
the sharpest formal statement of the difference between the structural reading and the
linear-free-energy reading of the same two-parabola object. -/
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
*co-extensive* as hypotheses on the curvature, even though neither is a restatement of the other —
this is the derived content behind the `rfl`-level barrier certificates. -/
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

end Relations

end PhotoLean
