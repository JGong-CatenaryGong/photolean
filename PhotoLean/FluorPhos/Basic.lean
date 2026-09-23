/-
PhotoLean.FluorPhos.Basic — milestone FP1, the description layer of the
fluorescence–phosphorescence competition.

From `S₁` the molecule fluoresces (rate `kF`), converts to the ground state (`kIC`), or crosses to
the triplet manifold (`kISC`); from `T₁` it phosphoresces (`kP`) or decays nonradiatively (`kNR`).
This module names the five rate-level quantities of that two-state branching model (plan §4,
FP-B1–FP-B5) and the premise bundle `FPData` (FP-B6) that carries every positivity assumption the
law layer consumes: nonnegativity of each rate, positivity of the total S₁ decay
`s1Decay = kF + kISC + kIC` and of the total T₁ decay `kP + kNR`. Positivity is an explicit
hypothesis of the bundle rather than a hidden property of a definition (engine iron rule 3).

`phiP` is the cascade product of the S₁→T₁ intersystem-crossing branch and the T₁ radiative
branch. Reverse intersystem crossing (T₁→S₁ back-crossing), delayed fluorescence and any cascade
above S₁ are out of scope (plan §1.2); El-Sayed's rule enters only as the parameter `kISC`, never
as a derivable row (plan §1.3, honesty table row 2).

Statement authority: every definition body and every structure signature below is taken word for
word from `theories/FluorPhos/probes/FluorPhos-statement-skeleton.lean` (the frozen Phase-1
authority, sha256 `b116adddea484896f7068c00141989d70871db4f51fe36749a2dbc44e24f4480` (re-frozen 2026-09-23; Phase-1 hash `2aa08f1c153b6494…`)`,
29 declarations), which transcribes `theories/FluorPhos/plan.md` §4; fidelity is checked by
`python3 theories/BEP/probes/bep-fidelity.py --theory FluorPhos`. The only departure from the
authority text is the proof bodies, which the authority leaves unfinished on purpose (Phase 1).

There is no unproved placeholder and no custom axiomatic declaration in this file. Note: the
two keyword literals that `proofs/scripts/check.sh --strict` scans for are deliberately not
spelled out anywhere in this file — the scan covers `PhotoLean/**/*.lean` including block
comments, so writing them (even in prose) would be a false-positive FAIL.

Plan locus: `theories/FluorPhos/plan.md` §4 (FP-B rows), sprint FP1; board
`theories/FluorPhos/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.FluorPhos.Basic
    proofs/scripts/check.sh --strict PhotoLean.FluorPhos.Basic
-/
import Mathlib

set_option autoImplicit false

namespace PhotoLean

namespace FluorPhos

/-! ## FP1 — description layer -/

/-- Plan §4, FP-B1. Total decay rate of the S₁ state: fluorescence + intersystem crossing +
internal conversion. -/
def s1Decay (kF kISC kIC : ℝ) : ℝ := kF + kISC + kIC

/-- Plan §4, FP-B2. Fluorescence quantum yield: the S₁ radiative branch. -/
noncomputable def phiF (kF kISC kIC : ℝ) : ℝ := kF / s1Decay kF kISC kIC

/-- Plan §4, FP-B3. The S₁→T₁ intersystem-crossing branch. -/
noncomputable def iscBranch (kF kISC kIC : ℝ) : ℝ := kISC / s1Decay kF kISC kIC

/-- Plan §4, FP-B4. The T₁ radiative (phosphorescence) branch. -/
noncomputable def t1BranchP (kP kNR : ℝ) : ℝ := kP / (kP + kNR)

/-- Plan §4, FP-B5. Phosphorescence quantum yield: the cascade product of the S₁→T₁ branch and
the T₁ radiative branch. -/
noncomputable def phiP (kF kISC kIC kP kNR : ℝ) : ℝ :=
  iscBranch kF kISC kIC * t1BranchP kP kNR

/-- Plan §4, FP-B6. The premise bundle: nonnegative rates, positive total decay of S₁, positive
total decay of T₁ (engine rule 3 — every positivity is an explicit hypothesis). -/
structure FPData (kF kISC kIC kP kNR : ℝ) : Prop where
  kF_nonneg : 0 ≤ kF
  kISC_nonneg : 0 ≤ kISC
  kIC_nonneg : 0 ≤ kIC
  kP_nonneg : 0 ≤ kP
  kNR_nonneg : 0 ≤ kNR
  s1Decay_pos : 0 < s1Decay kF kISC kIC
  t1Decay_pos : 0 < kP + kNR

end FluorPhos

end PhotoLean
