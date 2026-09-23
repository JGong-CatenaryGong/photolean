/-
PhotoLean.EnergyGapLaw.Basic — EG1, the description layer of the energy-gap law (Englman–Jortner
form).

`PhotoLean.Kernel` carries the single definitions of the two-parabola family (barrier, reverse
barrier, transition-state coordinate, transfer coefficient) and `PhotoLean.Marcus.Basic` the
inverted-region rate. This theory reads that classical model as the **energy-gap law**: the
nonradiative rate of an electronic relaxation is the Marcus rate at the gap
(driving-force convention `x = -ΔG° = ΔE`), and its logarithm falls off with the gap. Following
the kernel-copy pattern of the family (plan §1.2, hard constraint 1), this module delivers the
theory's **own copies** of the kernel objects and pins them to the kernel/Marcus definitions by
`rfl`-level certificates:

* EG-B1 `nrBarrier` + `cert_nrBarrier` — the nonradiative crossing barrier IS
  `PhotoLean.Kernel.barrier`;
* EG-B2 `nrRate` + `cert_nrRate` — the nonradiative rate IS `PhotoLean.Marcus.rate`;
* EG-B3 `InvertedGap` + `cert_invertedGap` — the inverted-gap predicate IS
  `PhotoLean.Marcus.InvertedRegion`;
* EG-B4 `lnRate` — `Real.log` of the nonradiative rate (the layer the law is stated on).

The certificates are the regression alarm of the copy pattern: they are pure definitional rows, so
a drifting kernel definition makes them fail to compile — a compile-time alarm, never an edit
permit (plan §1.2).

Every physical premise is explicit: the positivity premises (`0 < A`, `0 < lam`, `0 < kB * T`)
are carried by the rows of `Criterion.lean` and `Sharp.lean` that consume them; the definitions
here take their parameters unconstrained, as definitions do (iron rule 3 concerns statements about
them). The rate is positive under `0 < A`, so `Real.log` is applied where it is meant to be
(plan §2) — the premise is carried on the rows that use it.

Plan locus: `theories/EnergyGapLaw/plan.md` §4 (EG-B rows), sprint EG1; board
`theories/EnergyGapLaw/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.EnergyGapLaw.Basic
    proofs/scripts/check.sh --strict PhotoLean.EnergyGapLaw.Basic
    proofs/scripts/axioms.sh PhotoLean.EnergyGapLaw.Basic PhotoLean.EnergyGapLaw.<theorem>

Statement authority: every declaration below matches
`theories/EnergyGapLaw/probes/EnergyGapLaw-statement-skeleton.lean` (the frozen Phase-1 authority,
26 declarations) word for word in signature and body; the proof routes are the ones the api-probe
`theories/EnergyGapLaw/probes/EnergyGapLaw-api-probe.lean` calibrated. The delivered file contains
no unfinished-proof placeholder and no custom axiomatic declaration; `#print axioms` of every
theorem below lists at most `propext`, `Classical.choice`, `Quot.sound`. Note deliberately: the two
keyword literals that `proofs/scripts/check.sh --strict` scans for are not spelled out anywhere in
this file — the scan covers `PhotoLean/**/*.lean` including block comments.
-/
import Mathlib
import PhotoLean.Kernel
import PhotoLean.Marcus.Basic

set_option autoImplicit false

namespace PhotoLean

namespace EnergyGapLaw

/-! ## EG-B — the kernel copies and their certificates -/

/-- Nonradiative crossing barrier at reorganization energy `lam` and gap `x` (driving-force
convention `x = −ΔG°`). Plan section 4, row EG-B1. This theory's own copy, pinned to
`PhotoLean.Kernel.barrier` by `cert_nrBarrier` (hard constraint 1). -/
noncomputable def nrBarrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- Kernel certificate: the nonradiative barrier IS `PhotoLean.Kernel.barrier`.
Plan section 4, row EG-B1. Proof route (plan §4): `rfl` (definitional copy — the pointwise row;
dry-run in the api-probe). -/
theorem cert_nrBarrier (lam x : ℝ) : nrBarrier lam x = PhotoLean.Kernel.barrier lam x := by
  unfold nrBarrier PhotoLean.Kernel.barrier
  rfl

/-- Nonradiative rate with prefactor `A` at thermal energy `kB * T`: the Arrhenius/Marcus rate
over the crossing barrier. Plan section 4, row EG-B2. This theory's own copy, pinned to
`PhotoLean.Marcus.rate` by `cert_nrRate` (hard constraint 1). -/
noncomputable def nrRate (A lam kB T x : ℝ) : ℝ :=
  A * Real.exp (-(nrBarrier lam x) / (kB * T))

/-- Marcus certificate: the nonradiative rate IS `PhotoLean.Marcus.rate` (the Marcus body is
`A * Real.exp (-(Marcus.barrier lam x) / (kB * T))`). Plan section 4, row EG-B2.
Proof route (plan §4): `unfold` + `rfl` (plain `rfl` already closes it in the api-probe). -/
theorem cert_nrRate (A lam kB T x : ℝ) :
    nrRate A lam kB T x = PhotoLean.Marcus.rate A lam kB T x := by
  unfold nrRate PhotoLean.Marcus.rate PhotoLean.Marcus.barrier
  rfl

/-- The inverted-gap predicate: the gap exceeds the reorganization energy. Plan section 4,
row EG-B3. This theory's own copy, pinned to `PhotoLean.Marcus.InvertedRegion` by
`cert_invertedGap` (hard constraint 1). -/
def InvertedGap (lam x : ℝ) : Prop := lam < x

/-- Marcus certificate: the inverted-gap predicate IS `PhotoLean.Marcus.InvertedRegion`.
Plan section 4, row EG-B3. Proof route (plan §4): `Iff.rfl`. -/
theorem cert_invertedGap (lam x : ℝ) :
    InvertedGap lam x ↔ PhotoLean.Marcus.InvertedRegion lam x := by
  unfold InvertedGap PhotoLean.Marcus.InvertedRegion
  exact Iff.rfl

/-- The log-rate: `Real.log` of the nonradiative rate. Plan section 4, row EG-B4. (The rate is
positive under `0 < A`, so no totalization issue arises — the premise is carried on the rows
that consume it, plan §2.) -/
noncomputable def lnRate (A lam kB T x : ℝ) : ℝ := Real.log (nrRate A lam kB T x)

end EnergyGapLaw

end PhotoLean
