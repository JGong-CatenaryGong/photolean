/-
PhotoLean.RelationAudit.BoundedAudit.XD1 - candidate evidence for the R5 cross-domain-01
package (`bounded_audit/r5/cross-domain-01/`).

This module is additive. It imports delivered theory modules and changes no delivered
statement. It carries three *candidate* identities that the package search found when it
looked for a bridge between the Sabatier volcano and the excited-state rate theories:

* the descending Sabatier branch is the energy-gap-law barrier function;
* the symmetric Sabatier apex barrier is one eighth of the optical Stokes shift;
* the Sabatier activity functional at the Franck-Condon barrier is the ICvsISC
  internal-conversion rate with the same prefactor.

They are recorded here because they are genuine kernel identities with a checked axiom
footprint, and because the screening package must show *why* they do not discharge the
chemical queries. None of them is used as a certified outcome in the package: each is a
formula-level identity of one branch, one symmetric specialization, or one rate-law
substitution, and none supplies the statement-level identification of the catalytic process
with the optical/IC process that the chemical question requires. The package outcomes for
the three pairs are `unresolved`, with these declarations cited as candidate evidence.

There is no unfinished-proof placeholder and no custom axiomatic declaration in this file.
-/
import Mathlib
import PhotoLean.Sabatier.Compose
import PhotoLean.EnergyGapLaw.Basic
import PhotoLean.StokesShift.Basic
import PhotoLean.ICvsISC.Basic

set_option autoImplicit false

namespace PhotoLean.RelationAudit.BoundedAudit.XD1

open PhotoLean

/-- Candidate evidence for P-Sabatier-EnergyGapLaw: the descending Sabatier branch
`parabolaDown lam dE = BEP.eact lam dE` is the energy-gap-law nonradiative barrier
`nrBarrier lam dE`. This is the shared kernel barrier formula, not a statement that the
catalytic step is the optical nonradiative transition. -/
theorem sabatierStrongBranch_eq_eglBarrier (lam dE : ℝ) :
    Sabatier.parabolaDown lam dE = EnergyGapLaw.nrBarrier lam dE := by
  unfold Sabatier.parabolaDown BEP.eact EnergyGapLaw.nrBarrier
  rfl

/-- Candidate evidence for P-Sabatier-StokesShift: at a symmetric two-parabola cycle the
Sabatier apex barrier is `lam / 4`, while the displaced-harmonic Stokes shift is `2 * lam`;
hence the apex barrier is one eighth of the Stokes shift. The identity needs `lam ≠ 0` only
to keep the totalized division at the apex well defined; it does not identify the optical
reorganization energy with the catalytic one. -/
theorem sabatierSymmetricApex_eq_stokesEighth {lam e00 : ℝ} (hlam : lam ≠ 0) :
    Sabatier.parabolicBarrier lam lam 0 = StokesShift.stokesShift lam e00 / 8 := by
  unfold Sabatier.parabolicBarrier Sabatier.parabolaUp Sabatier.parabolaDown BEP.eact
    StokesShift.stokesShift StokesShift.absEnergy StokesShift.emEnergy
    StokesShift.s1Surface StokesShift.s0Surface
  field_simp
  ring

/-- Candidate evidence for P-Sabatier-ICvsISC: the ICvsISC internal-conversion rate at the
Franck-Condon barrier is the Sabatier activity functional at that barrier, with the same
prefactor `A`. This is a rate-law substitution; it does not identify the IC channel with the
catalytic step. -/
theorem sabatierActivity_eq_icRate (A lam kB T x : ℝ) :
    ICvsISC.icRate A lam kB T x =
      A * Sabatier.activity (fun y => ICvsISC.fcBarrier lam y) kB T x := by
  unfold ICvsISC.icRate ICvsISC.fcBarrier Sabatier.activity
  rfl

#print axioms PhotoLean.RelationAudit.BoundedAudit.XD1.sabatierStrongBranch_eq_eglBarrier
#print axioms PhotoLean.RelationAudit.BoundedAudit.XD1.sabatierSymmetricApex_eq_stokesEighth
#print axioms PhotoLean.RelationAudit.BoundedAudit.XD1.sabatierActivity_eq_icRate

end PhotoLean.RelationAudit.BoundedAudit.XD1
