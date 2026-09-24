import Mathlib
import PhotoLean.RACI.TwoState

namespace PhotoLean


/-!
# RACI M2 — Accessibility: admissible paths and energy blocking

Upstream provenance: the ChemLean RACI plan §2.3, §5.1 (integration record: theories/RACI/plan.md §3.1).
Status note (upstream header, preserved): the statements were transcribed from the upstream plan; deliberate deviations from the draft:
upstream §5.6 allowed the first M2 version to drop the energy field; this file keeps `below_energy` (as in §2.3),
and whether `BlockedBelow` holds for every ε is handled in the upstream §5.3 note.
Upstream owner: prover_m2 (exclusive file).
-/

open TwoState

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace RACI

/-- An admissible continuous path from the Franck–Condon region (`fc`) to the CI (upstream plan §2.3). -/
structure AdmissiblePath (M : TwoState X) (allowed : Set X) (fc : Set X) (ε : ℝ) where
  path : ℝ → X
  cont : Continuous path
  starts_fc : path 0 ∈ fc
  ends_ci : path 1 ∈ TwoState.conicalSet M
  stays_allowed : ∀ t, path t ∈ allowed
  below_energy : ∀ t, M.H (path t) 0 0 ≤ ε

/-- No admissible CI channel exists below the energy ε (upstream plan §2.3; `∃ A, True` is written `Nonempty` to silence the linter). -/
def BlockedBelow (M : TwoState X) (allowed : Set X) (fc : Set X) (ε : ℝ) : Prop :=
  ¬ Nonempty (AdmissiblePath M allowed fc ε)

end RACI


end PhotoLean