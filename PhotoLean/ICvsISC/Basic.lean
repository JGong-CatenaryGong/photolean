/-
PhotoLean.ICvsISC.Basic — FC1, the description layer of the IC-vs-ISC competition.

`PhotoLean.Kernel` carries the single definitions of the two-parabola family (barrier, reverse
barrier, transition-state coordinate, transfer coefficient) and `PhotoLean.Marcus.Basic` the
inverted-region rate. This theory reads that classical model as the **Franck–Condon competition
between internal conversion (IC) and intersystem crossing (ISC)**: both channels are nonradiative
transitions whose rates are Marcus rates over their **own** gap and reorganization energy, except
that ISC carries the explicit spin-orbit prefactor `HSO²` (plan §1.1). Following the kernel-copy
pattern of the family (plan §1.2, hard constraint 1), this module delivers the theory's **own
copies** of the kernel objects and pins them to the kernel/Marcus definitions by definitional
certificates:

* FC-B1 `fcBarrier` + `cert_fcBarrier` — the channel Franck–Condon barrier IS
  `PhotoLean.Kernel.barrier`;
* FC-B2 `icRate` + `cert_icRate` — the IC rate IS `PhotoLean.Marcus.rate`;
* FC-B3 `iscRate` — the ISC rate, whose spin-orbit factor `HSO ^ 2` is written **explicitly in the
  definition** (physical-premise visibility, iron rule 3: the coupling enters squared, so the
  statement layer needs no sign premise on `HSO`);
* FC-B4 `FCData` — the premise bundle: positivity of both prefactors, both reorganization
  energies and the thermal energy `kB * T`. There is deliberately no `HSO` sign premise — the
  amplitude enters squared (plan §4, row FC-B4).

The certificates are the regression alarm of the copy pattern: they are pure definitional rows, so
a drifting kernel definition makes them fail to compile — a compile-time alarm, never an edit
permit (plan §1.2).

Every physical premise is explicit: the positivity bundle `FCData` is the hypothesis of every
`Criterion.lean` row that consumes it. The definitions here take their parameters unconstrained,
as definitions do (iron rule 3 concerns statements *about* them).

Plan locus: `theories/ICvsISC/plan.md` §4 (FC-B rows), sprint FC1; board
`theories/ICvsISC/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.ICvsISC.Basic
    proofs/scripts/check.sh --strict PhotoLean.ICvsISC.Basic
    proofs/scripts/axioms.sh PhotoLean.ICvsISC.Basic PhotoLean.ICvsISC.<theorem>

Statement authority: every declaration below matches
`theories/ICvsISC/probes/ICvsISC-statement-skeleton.lean` (the frozen Phase-1 authority,
20 declarations) word for word in signature and body; the proof routes are the ones the api-probe
`theories/ICvsISC/probes/ICvsISC-api-probe.lean` calibrated. The delivered file contains no
unfinished-proof placeholder and no custom axiomatic declaration; `#print axioms` of every theorem
below lists at most `propext`, `Classical.choice`, `Quot.sound`. Note deliberately: the keyword
literals that `proofs/scripts/check.sh --strict` scans for are not spelled out anywhere in this
file — the scan covers `PhotoLean/**/*.lean` including block comments.
-/
import Mathlib
import PhotoLean.Kernel
import PhotoLean.Marcus.Basic

set_option autoImplicit false

namespace PhotoLean

namespace ICvsISC

/-! ## FC-B — the kernel copies, their certificates and the premise bundle -/

/-- The Franck–Condon barrier of one channel: reorganization energy `lam`, gap `x`. The theory's
own copy of the kernel barrier (plan §1.2, hard constraint 1), pinned by `cert_fcBarrier`.
Plan section 4, row FC-B1. -/
noncomputable def fcBarrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- Certificate: the theory's barrier copy IS the delivered kernel barrier.
Plan section 4, row FC-B1. Proof route: `rfl`. -/
theorem cert_fcBarrier {lam x : ℝ} : fcBarrier lam x = PhotoLean.Kernel.barrier lam x := by
  rfl

/-- The IC rate: Arrhenius over the channel's own barrier with prefactor `AI`.
Plan section 4, row FC-B2. -/
noncomputable def icRate (AI lamI kB T xI : ℝ) : ℝ :=
  AI * Real.exp (-(fcBarrier lamI xI) / (kB * T))

/-- Certificate: the IC rate IS the delivered Marcus rate.
Plan section 4, row FC-B2. Proof route: `unfold` + `rfl`. -/
theorem cert_icRate {AI lamI kB T xI : ℝ} :
    icRate AI lamI kB T xI = PhotoLean.Marcus.rate AI lamI kB T xI := by
  unfold icRate PhotoLean.Marcus.rate PhotoLean.Marcus.barrier
  rfl

/-- The ISC rate: Arrhenius over the channel's own barrier with the explicit spin-orbit
prefactor `HSO² · AS` (physical premise visibility: the coupling enters squared, so no sign
premise on `HSO`). Plan section 4, row FC-B3. -/
noncomputable def iscRate (HSO AS lamS kB T xS : ℝ) : ℝ :=
  HSO ^ 2 * AS * Real.exp (-(fcBarrier lamS xS) / (kB * T))

/-- The premise bundle: positivity of both prefactors, both reorganization energies, and the
thermal energy `kB · T`. No `HSO` sign premise — the amplitude enters squared.
Plan section 4, row FC-B4. -/
structure FCData (AI AS lamI lamS kB T : ℝ) : Prop where
  /-- Positive IC prefactor. -/
  posAI : 0 < AI
  /-- Positive ISC base prefactor. -/
  posAS : 0 < AS
  /-- Positive IC reorganization energy. -/
  posLamI : 0 < lamI
  /-- Positive ISC reorganization energy. -/
  posLamS : 0 < lamS
  /-- Positive thermal energy. -/
  poskBT : 0 < kB * T

end ICvsISC

end PhotoLean
