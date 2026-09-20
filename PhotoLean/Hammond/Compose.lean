/-
PhotoLean.Hammond.Compose — H4, microscopic conditions for the Hammond descriptor.

Replaces the abstract premise `0 < lam` by microscopic conditions, reusing the delivered
`PhotoLean.Marcus.Reorg` (no new physics is invented here): the inner-sphere reorganization
energy is positive for a positive force constant and a non-zero geometry change, the outer-sphere
(Pekar) term is positive under the geometric and Pekar premises, and the total reorganization
energy of the composition inherits positivity, hence the Hammond descriptor
(`hammond_descriptor_holds`, H2) and non-vacuity of the regime.

**Scope note (the difference from the Marcus rate-level counterpart)**: this composition carries
**no** temperature, Boltzmann-constant or prefactor premises (`kB`, `T`, `A` do not occur). The
structural description is independent of them — the Hammond descriptor has strictly fewer physical
premises than the Marcus rate descriptor, and none is hidden in a definition: `hnSq`, `hepsS`,
`hPekar`, `hgeom` / `hRge` are all visible in the signatures below.

Statement authority: every declaration below matches
`theories/hammond/probes/hammond-statement-skeleton.lean` (H4 section) word for word (plan §7).
There is no unproved placeholder and no custom axiom anywhere in this file.
-/
import PhotoLean.Hammond.Criterion
import PhotoLean.Marcus.Reorg

namespace PhotoLean

namespace Hammond

/-- A positive molecular force constant with a non-zero geometry change yields the Hammond
descriptor for the inner-sphere reorganization energy. -/
theorem hammond_descriptor_of_inner {kk dq : ℝ} (hkk : 0 < kk) (hdq : dq ≠ 0) :
    HammondDescriptor (Marcus.lamInner kk dq) :=
  hammond_descriptor_holds (Marcus.lamInner_pos hkk hdq)

/-- Microscopic sufficiency: the Pekar factor and the geometric factor (explicit physical
premises) make the total reorganization energy positive, hence the descriptor holds. -/
theorem hammond_descriptor_of_microscopic {kk dq dE a1 a2 R nSq epsS : ℝ} (hkk : 0 ≤ kk)
    (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2) (hR : 0 < R)
    (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    HammondDescriptor (Marcus.lamInner kk dq + Marcus.lamOuter dE a1 a2 R nSq epsS) :=
  hammond_descriptor_holds
    (Marcus.lam_total_pos (Marcus.lamInner_nonneg hkk dq)
      (Marcus.lamOuter_pos hdE ha1 ha2 hR hgeom hnSq hepsS hPekar))

/-- Stretch: the geometric premise is derivable from non-overlapping spheres. -/
theorem hammond_descriptor_of_nonoverlap {kk dq dE a1 a2 R nSq epsS : ℝ} (hkk : 0 ≤ kk)
    (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2) (hRge : a1 + a2 ≤ R) (hnSq : 0 < nSq)
    (hepsS : 0 < epsS) (hPekar : 1 / epsS < 1 / nSq) :
    HammondDescriptor (Marcus.lamInner kk dq + Marcus.lamOuter dE a1 a2 R nSq epsS) :=
  hammond_descriptor_holds
    (Marcus.lam_total_pos (Marcus.lamInner_nonneg hkk dq)
      (Marcus.lamOuter_pos hdE ha1 ha2 (by linarith)
        (Marcus.hgeom_of_nonoverlap ha1 ha2 hRge) hnSq hepsS hPekar))

