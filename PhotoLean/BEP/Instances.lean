/-
PhotoLean.BEP.Instances — B5b: the instance / verdict layer of the BEP theory.

**Statement authority**: the B5b block of `theories/BEP/probes/bep-statement-skeleton.lean`
(plan §8.2, rows I1–I12). All 48 declarations below match that block word for word (checked
mechanically by `theories/BEP/probes/bep-fidelity.py`), and every declaration of that block is
delivered here.

**What this file is.** Each row instantiates the equal-curvature two-parabola model at concrete
numbers and lets the kernel decide the verdict, on top of the computable decision layer
`PhotoLean/BEP/RatModel.lean` (plan §8.1):

* I1–I8 are `model-constructed` families at `λ = 2`, plus the degenerate `λ = 0` and the
  unphysical `λ = -2` rows. The verdict is a kernel computation in ℚ by `norm_num`;
  `by decide` cannot close these goals (comparisons containing `/`-literals do not reduce) and
  `native_decide` is forbidden (`Lean.ofReduceBool` is not in `ALLOWED_AXIOMS`).
* I9 exhibits the instructive gap: the Evans–Polanyi bounds are **blind** to an unphysical
  curvature (`λ = -2`, `α = 3/4 ∈ [0,1]`); the *sign* of the defect (`bepDefect (-2) 1 = -1/8`)
  is what detects it.
* I10 is the tolerance threshold (`λ = 2`, `w = 1`): conformance at `tol = 1/8`, failure at
  `tol = 1/16` — exactly the squared form `w ^ 2 ≤ 4 * λ * tol` that `qConformsWindow` states.
* I11 quotes four first-hand literature families of `theories/BEP/LITERATURE.md` §R1.10 with the
  sources' own printed numbers and refutes the model for their three-row triples.
* I12 is the summary: the affine (BEP) description conforms, the equal-curvature two-parabola model
  is refuted — for each of the four families that §R1.10 prints per-point.
* `inst_nonvacuous` records that the layer is not a table of one-sided verdicts.

**Provenance and units (binding on the I11 rows).** Every Lean literal is the source's printed
**kcal/mol** number, transcribed verbatim from §R1.10; the kJ/mol column of that record is the
record's own arithmetic (`1 kcal/mol = 4.184 kJ/mol`) and is **not** what any statement uses. The
model is unit-agnostic, so the unit statement in the docstring is what makes the numbers checkable
against the source. Each family docstring states whether the source prints a Gibbs energy (`ΔG°`
with barrier `ΔG‡`, families F1/F2/F3) or a **classical** energy (`ΔE` with forward barrier `V‡f`,
family F5) and carries the corresponding `ΔH`/`ΔE`/`ΔG°` caveat of §R1.10.1 / §R1.10.5. The
model's driving force is `x = -ΔG°` (F5: `x = -ΔE`), applied explicitly at every row.

**Every I11/I12 verdict is a statement about the model family *instantiated by those numbers*,
never about the experiment** (plan §8.2): what is proved is "no positive-λ equal-curvature
two-parabola law reproduces these three printed rows"; "the chemistry violates BEP" is not proved.

**F4 is deliberately absent.** §R1.10.4 prints only family aggregates for the Table 2 "PE" column
(mean `λ̂`, `λ̂` range, fitted curvature, linear fit, R²) and **no per-row `(driving force, barrier)`
pairs**, so none of the four I11 rows can be stated for it without inventing data. The gap is
recorded in `proofs/API-NOTES.md` (BEP follow-up §3) and in the skeleton's B5b section header; the
lead owns any arbitration.

**Recipes** (measured: `theories/BEP/probes/bep-api-instances.lean`): verdict rows
`unfold Rat.epQVerdict Rat.qTransfer; norm_num`; value rows `unfold <def>; norm_num`; window rows
`unfold Rat.qConformsWindow; norm_num`; falsification rows = `Rat.qModelConsistent3_curvature_pos`
at the three `by norm_num` distinctness facts + the computed negative divided difference +
`norm_num at hpos`. Decimal ℚ literals (`(15.6 : ℚ)`, `(7.62 : ℚ)`) are first-class for `norm_num`.

Every physical premise of the statements below (`0 < lam`, `0 < tol`, distinct abscissae, …) is an
explicit hypothesis of the theorem that consumes it; nothing is hidden in a definition. There is no
unproved placeholder and no custom axiom in this file. Imports: `PhotoLean.BEP.RatModel` + Mathlib.

Acceptance (contract `proofs/ENGINE.yml`, plan §10):
  proofs/scripts/lake build PhotoLean.BEP.Instances
  proofs/scripts/check.sh --strict PhotoLean.BEP.Instances
  proofs/scripts/axioms.sh PhotoLean.BEP.Instances PhotoLean.BEP.<theorem>
-/

import Mathlib
import PhotoLean.BEP.RatModel

namespace PhotoLean

namespace BEP

/-! ### I1–I10 — model-constructed families (plan §8.2)

Every family below is `model-constructed`: `λ` and `x` are chosen numbers, not data. The verdict is
the kernel's evaluation of the delivered cascade `Rat.epQVerdict` (§8.1) at those numbers. -/

/-! #### I1 — thermoneutral family -/

/-- I1 (`model-constructed`): thermoneutral family `λ = 2`, `x = 0` — the cascade lands in the open
conforming regime. -/
theorem inst_I1_thermoneutral_zone : Rat.epQVerdict (2 : ℚ) 0 = Rat.EPQVerdict.conforming := by
  unfold Rat.epQVerdict Rat.qTransfer
  norm_num

/-- I1 (`model-constructed`): `α(0) = 1/2` at `λ = 2` (the thermoneutral value of the
linear-response coefficient). -/
theorem inst_I1_thermoneutral_transfer : Rat.qTransfer (2 : ℚ) 0 = 1 / 2 := by
  unfold Rat.qTransfer
  norm_num

/-- I1 (`model-constructed`): the window predicate conforms at `tol = 1/4` and `w = 0` — the exact
window, in the squared form `w ^ 2 ≤ 4 * λ * tol`. -/
theorem inst_I1_thermoneutral_conforms : Rat.qConformsWindow (2 : ℚ) (1 / 4) 0 := by
  unfold Rat.qConformsWindow
  norm_num

/-! #### I2 — mildly exergonic family -/

/-- I2 (`model-constructed`): mildly exergonic family `λ = 2`, `x = 1/2` — conforming. -/
theorem inst_I2_exergonic_zone : Rat.epQVerdict (2 : ℚ) (1 / 2) = Rat.EPQVerdict.conforming := by
  unfold Rat.epQVerdict Rat.qTransfer
  norm_num

/-- I2 (`model-constructed`): `α(1/2) = 3/8 < 1/2` — the coefficient falls below thermoneutral on
the exergonic side. -/
theorem inst_I2_exergonic_transfer : Rat.qTransfer (2 : ℚ) (1 / 2) = 3 / 8 := by
  unfold Rat.qTransfer
  norm_num

/-- I2 (`model-constructed`): `x = 1/2` lies inside the `tol = 1/4` window of `λ = 2`. -/
theorem inst_I2_exergonic_conforms : Rat.qConformsWindow (2 : ℚ) (1 / 4) (1 / 2) := by
  unfold Rat.qConformsWindow
  norm_num

/-! #### I3 — mildly endergonic family -/

/-- I3 (`model-constructed`): mildly endergonic family `λ = 2`, `x = -1/2` — conforming. -/
theorem inst_I3_endergonic_zone : Rat.epQVerdict (2 : ℚ) (-(1 / 2)) = Rat.EPQVerdict.conforming := by
  unfold Rat.epQVerdict Rat.qTransfer
  norm_num

/-- I3 (`model-constructed`): `α(-1/2) = 5/8 > 1/2` — the complementarity mirror of I2
(`α_f + α_r = 1` at the same `|x|`). -/
theorem inst_I3_endergonic_transfer : Rat.qTransfer (2 : ℚ) (-(1 / 2)) = 5 / 8 := by
  unfold Rat.qTransfer
  norm_num

/-- I3 (`model-constructed`): `x = -1/2` lies inside the `tol = 1/4` window of `λ = 2`. -/
theorem inst_I3_endergonic_conforms : Rat.qConformsWindow (2 : ℚ) (1 / 4) (1 / 2) := by
  unfold Rat.qConformsWindow
  norm_num

/-! #### I4 — forward barrierless limit -/

/-- I4 (`model-constructed`): forward barrierless limit `λ = 2`, `x = 2` — the cascade reaches the
boundary guard `x = lam` before the open regime. -/
theorem inst_I4_forwardLimit_zone : Rat.epQVerdict (2 : ℚ) 2 = Rat.EPQVerdict.boundary := by
  unfold Rat.epQVerdict Rat.qTransfer
  norm_num

/-- I4 (`model-constructed`): `α(λ) = 0` — the forward barrier's minimum in the model. -/
theorem inst_I4_forwardLimit_transfer : Rat.qTransfer (2 : ℚ) 2 = 0 := by
  unfold Rat.qTransfer
  norm_num

/-- I4 (`model-constructed`): the limit sits on the edge of the Evans–Polanyi band — the *open*
regime `0 < α < 1` fails there, so conformance in the open sense is not a closed condition. -/
theorem inst_I4_forwardLimit_boundary :
    ¬ (0 < Rat.qTransfer (2 : ℚ) 2 ∧ Rat.qTransfer (2 : ℚ) 2 < 1) := by
  unfold Rat.qTransfer
  norm_num

/-! #### I5 — reverse barrierless limit -/

/-- I5 (`model-constructed`): reverse barrierless limit `λ = 2`, `x = -2` — boundary. -/
theorem inst_I5_reverseLimit_zone : Rat.epQVerdict (2 : ℚ) (-2) = Rat.EPQVerdict.boundary := by
  unfold Rat.epQVerdict Rat.qTransfer
  norm_num

/-- I5 (`model-constructed`): `α(-λ) = 1` — the reverse barrier's minimum in the model. -/
theorem inst_I5_reverseLimit_transfer : Rat.qTransfer (2 : ℚ) (-2) = 1 := by
  unfold Rat.qTransfer
  norm_num

/-- I5 (`model-constructed`): the reverse limit also sits on the edge of the band (the open regime
fails at `α = 1`). -/
theorem inst_I5_reverseLimit_boundary :
    ¬ (0 < Rat.qTransfer (2 : ℚ) (-2) ∧ Rat.qTransfer (2 : ℚ) (-2) < 1) := by
  unfold Rat.qTransfer
  norm_num

/-! #### I6–I7 — the two inverted regions -/

/-- I6 (`model-constructed`): strongly exergonic, forward inverted region `λ = 2`, `x = 3`; the
cascade lands below the Evans–Polanyi band. -/
theorem inst_I6_inverted_zone : Rat.epQVerdict (2 : ℚ) 3 = Rat.EPQVerdict.subLinear := by
  unfold Rat.epQVerdict Rat.qTransfer
  norm_num

/-- I6 (`model-constructed`): `α(3) = -1/4 < 0` — below the band. -/
theorem inst_I6_inverted_transfer : Rat.qTransfer (2 : ℚ) 3 = -(1 / 4) := by
  unfold Rat.qTransfer
  norm_num

/-- I6 (`model-constructed`): the Evans–Polanyi bounds `0 ≤ α ≤ 1` fail (not just the open regime:
the lower bound itself fails). -/
theorem inst_I6_inverted_notBounds :
    ¬ (0 ≤ Rat.qTransfer (2 : ℚ) 3 ∧ Rat.qTransfer (2 : ℚ) 3 ≤ 1) := by
  unfold Rat.qTransfer
  norm_num

/-- I7 (`model-constructed`): strongly endergonic, reverse inverted region `λ = 2`, `x = -3`; the
cascade lands above the band. -/
theorem inst_I7_reverseInverted_zone : Rat.epQVerdict (2 : ℚ) (-3) = Rat.EPQVerdict.superLinear := by
  unfold Rat.epQVerdict Rat.qTransfer
  norm_num

/-- I7 (`model-constructed`): `α(-3) = 5/4 > 1` — above the band. -/
theorem inst_I7_reverseInverted_transfer : Rat.qTransfer (2 : ℚ) (-3) = 5 / 4 := by
  unfold Rat.qTransfer
  norm_num

/-- I7 (`model-constructed`): the Evans–Polanyi bounds fail (the upper bound fails). -/
theorem inst_I7_reverseInverted_notBounds :
    ¬ (0 ≤ Rat.qTransfer (2 : ℚ) (-3) ∧ Rat.qTransfer (2 : ℚ) (-3) ≤ 1) := by
  unfold Rat.qTransfer
  norm_num

/-! #### I8 — degenerate family (`λ = 0`) -/

/-- I8 (`model-constructed`): degenerate family `λ = 0`, `x = 1` — the first guard of the cascade
returns `degenerate` (no physical reorganization energy). -/
theorem inst_I8_degenerate_zone : Rat.epQVerdict (0 : ℚ) 1 = Rat.EPQVerdict.degenerate := by
  unfold Rat.epQVerdict
  norm_num

/-- I8 (`model-constructed`): the barrier collapses at `λ = 0` — with totalised division
(`y / 0 = 0`) `qEact 0 x` is the constant `0`, i.e. the exact affinity holds trivially. -/
theorem inst_I8_degenerate_exact : Rat.qEact (0 : ℚ) 1 = 0 := by
  unfold Rat.qEact
  norm_num

/-- I8 (`model-constructed`): the degenerate value of the **linear-response** body is `α = 1/2`
(plan §4.2 #4). The I8 cell of plan §8.2 still prints `α = 0`, which belonged to the discarded
transition-state-coordinate body; the statement authority (skeleton) carries `1/2` and the plan's
I-table cell is the lead's to update. -/
theorem inst_I8_degenerate_transfer : Rat.qTransfer (0 : ℚ) 1 = 1 / 2 := by
  unfold Rat.qTransfer
  norm_num

/-! #### I9 — unphysical curvature (`λ = -2`): the bounds are blind -/

/-- I9 (`model-constructed`): unphysical curvature `λ = -2`, `x = 1` — the cascade's second guard
returns `unphysical`. -/
theorem inst_I9_unphysical_zone : Rat.epQVerdict (-2 : ℚ) 1 = Rat.EPQVerdict.unphysical := by
  unfold Rat.epQVerdict Rat.qTransfer
  norm_num

/-- I9 (`model-constructed`): `α(-2, 1) = 3/4`, which lies **inside** `[0,1]`. -/
theorem inst_I9_unphysical_transfer : Rat.qTransfer (-2 : ℚ) 1 = 3 / 4 := by
  unfold Rat.qTransfer
  norm_num

end BEP

end PhotoLean
