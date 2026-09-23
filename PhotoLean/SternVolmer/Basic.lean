/-
PhotoLean.SternVolmer.Basic — milestone SV1, the description layer.

The theory: Stern–Volmer quenching analysis and the **D1 adjudication** — the static-vs-dynamic
identifiability boundary (plan `theories/SternVolmer/plan.md`, §1.1 and §4).

Stern–Volmer practice plots `I₀/I` against the quencher concentration `[Q]` and reads a linear
plot as evidence of *dynamic* (collisional) quenching. Both textbook mechanisms do produce an
exactly linear plot, so the intensity channel alone cannot separate them (SV-C7, witness pair
`conflation_witness`); the separating channel is the lifetime ratio (SV-C8). This module fixes the
model: one excited state with intrinsic total decay `k0 = kr + knr`, quencher concentration
`q : ℝ`, dynamic quenching adding the channel `kq·q` (`dynDecay`), static quenching removing
emitters by the linearized-binding isotherm `free fraction = 1/(1 + Ka·q)` (`svRatioStat`), and the
mechanism tag `Mech` of the two-mechanism model space. The `tauRatioDyn` body is deliberately
identical to `svRatioDyn` — that identity **is** the physical content of the dynamic mechanism
(both observables are the same decay ratio), and it is what makes SV-C6/SV-C8 theorems rather than
definitions.

Honest scope, stated up front:
* everything is algebraic over `ℝ` with totalized division; every positivity premise is an
  explicit hypothesis of the law rows (`Criterion`), never a hidden side condition of a definition
  (engine rule 3);
* `kq` and `Ka` are free parameters — no diffusion theory (Smoluchowski) and no binding theory is
  derived, and no time-resolved decay profile is modelled (plan §1.3);
* the intensity is taken proportional to the fluorescence yield and the lifetime to the inverse
  total decay; both are declared premises of the reading, not theorems (plan §9).

Statement authority: `theories/SternVolmer/probes/SternVolmer-statement-skeleton.lean` § SV-B;
every signature below is identical to its authority row. There is no unproved placeholder and no
custom axiomatic declaration anywhere in this file. Acceptance:
`proofs/scripts/lake build PhotoLean.SternVolmer.Basic` (exit 0);
`proofs/scripts/check.sh --strict`; fidelity
`python3 theories/BEP/probes/bep-fidelity.py --theory SternVolmer`.
-/
import Mathlib

set_option autoImplicit false

namespace PhotoLean

namespace SternVolmer

/-! ## SV-B — description layer -/

/-- Decay rate under dynamic (collisional) quenching: the intrinsic decay `k0` plus the
concentration-dependent channel `kq·q`. Plan section 4, row SV-B1. -/
noncomputable def dynDecay (k0 kq q : ℝ) : ℝ := k0 + kq * q

/-- The dynamic intensity ratio `I₀/I`: the yield ratio `kr/decay(q)` over `kr/decay(0)`.
Plan section 4, row SV-B2. -/
noncomputable def svRatioDyn (k0 kq q : ℝ) : ℝ := dynDecay k0 kq q / k0

/-- The dynamic lifetime ratio `τ₀/τ`. The body is identical to `svRatioDyn` — that identity
**is** the physical claim of the dynamic mechanism (both observables are the decay ratio);
registered here and in the SV-C1 docstring. Plan section 4, row SV-B3. -/
noncomputable def tauRatioDyn (k0 kq q : ℝ) : ℝ := dynDecay k0 kq q / k0

/-- The static intensity ratio (inverse free fraction `1 + Ka·q`): ground-state complexation
removes emitters by the linearized-binding isotherm `free fraction = 1/(1 + Ka·q)`.
Plan section 4, row SV-B4. -/
noncomputable def svRatioStat (Ka q : ℝ) : ℝ := 1 + Ka * q

/-- The static lifetime ratio: the observed (free) fluorophores decay unchanged.
Plan section 4, row SV-B5. -/
noncomputable def tauRatioStat (Ka q : ℝ) : ℝ := 1

/-- The Stern–Volmer constant `KSV k0 kq = kq / k0` (= `kq·τ₀`). Plan section 4, row SV-B6. -/
noncomputable def KSV (k0 kq : ℝ) : ℝ := kq / k0

/-- The combined mechanism (dynamic quenching of the free fraction): the intensity ratio
factors as the dynamic ratio times the static ratio. Plan section 4, row SV-B7. -/
noncomputable def svRatioBoth (k0 kq Ka q : ℝ) : ℝ := svRatioDyn k0 kq q * svRatioStat Ka q

/-- The mechanism tag of the two-mechanism model space. Plan section 4, row SV-B8. -/
inductive Mech | dyn | stat

/-- The mechanism-tagged intensity ratio — the observation map of the two-mechanism model
space. Plan section 4, row SV-B8. -/
noncomputable def svRatioOf (m : Mech) (k0 kq Ka q : ℝ) : ℝ :=
  match m with
  | Mech.dyn => svRatioDyn k0 kq q
  | Mech.stat => svRatioStat Ka q

/-- The mechanism-tagged lifetime ratio — the discriminating channel of the two-mechanism
model space. Plan section 4, row SV-B8. -/
noncomputable def tauRatioOf (m : Mech) (k0 kq Ka q : ℝ) : ℝ :=
  match m with
  | Mech.dyn => tauRatioDyn k0 kq q
  | Mech.stat => tauRatioStat Ka q

/-- The discriminating observable: the lifetime ratio tracks the intensity ratio at every
positive concentration. Plan section 4, row SV-B9. -/
def LifetimeTracks (m : Mech) (k0 kq Ka : ℝ) : Prop :=
  ∀ q, 0 < q → tauRatioOf m k0 kq Ka q = svRatioOf m k0 kq Ka q

end SternVolmer

end PhotoLean
