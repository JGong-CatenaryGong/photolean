/-
PhotoLean.BEP.Instances — B5b: the instance / verdict layer of the BEP theory.

**Statement authority**: the B5b block of `theories/BEP/probes/bep-statement-skeleton.lean`
(plan §8.2, rows I1–I12). All 48 declarations below match that block word for word (checked
mechanically by `theories/BEP/probes/bep-fidelity.py`), and every declaration of that block is
delivered here.

**What this file is.** Each row instantiates the equal-curvature two-parabola model at concrete
numbers and lets the kernel decide the verdict, on top of the computable decision layer
`PhotoLean/BEP/RatModel.lean` (plan §8.1):

* I1–I7 are `model-constructed` families at `λ = 2`; I8 is the degenerate `λ = 0` row, I9 the
  unphysical `λ = -2` row and I10 the tolerance threshold at `λ = 2`, `w = 1`. The verdict is a
  kernel computation in ℚ by `norm_num`; `by decide` cannot close these goals (comparisons
  containing `/`-literals do not reduce) and `native_decide` is forbidden (`Lean.ofReduceBool` is
  not in `ALLOWED_AXIOMS`).
* I9 exhibits the instructive gap: the Evans–Polanyi bounds are **blind** to an unphysical
  curvature (`λ = -2`, `α = 3/4 ∈ [0,1]`); the *sign* of the defect (`bepDefect (-2) 1 = -1/8`)
  is what detects it.
* I10 is the tolerance threshold (`λ = 2`, `w = 1`): conformance at `tol = 1/8`, failure at
  `tol = 1/16` — exactly the squared form `w ^ 2 ≤ 4 * λ * tol` that `qConformsWindow` states.
* I11 quotes four first-hand literature families of `theories/BEP/LITERATURE.md` §R1.10 with the
  sources' own printed numbers and refutes the model for their three-row triples.
* I12 is the summary, and its scope is exactly the **chosen** rows: for each of the four families
  that §R1.10 prints per-point, the two-point slope of the rows named in that family's heading lies
  strictly inside `(0,1)` — a claim about those printed rows, **not** about the family's fit quality
  (the family-level linear fits and their R² values are reported, by locus, in `LITERATURE.md`
  §R1.10.2–§R1.10.4; §R1.10.5 reports none for F5) — while the equal-curvature two-parabola model
  is refuted by the three-row curvature.
* `inst_nonvacuous` records that the layer is not a table of one-sided verdicts.

**Selection disclosure (independent verifier, MEDIUM-3).** The `_alphaObs` rows, the `_lamHat` rows
and the falsification rows of §I11 below do not use the same printed rows, and the choice matters:

* `_alphaObs` uses the two rows its family heading names (F1 `16(2)`/`8`, F2 `16(2)`/`10`,
  F3 `16(1)`/`7`, F5 `R2`/`R5`); `_lamHat` uses an **adjacent** printed pair in the record's table
  order (F1 `16(2)`/`16(1)`, F2 `16(2)`/`13`, F3 `16(1)`/`19(2)`, F5 `R2`/`R3`); every
  `_curvature_negative` / `_not_model_consistent` row uses **three** printed rows.
* the model's two-point solver `qLamOfPair` is **pair-dependent** on this real data, and not only in
  size: at the `_lamHat` pairs it takes the positive values `9/20`, `16/15`, `22/5`, `7958/675` (the
  four `_lamHat` theorems below), while at other documented pairs of the **same** families it is
  negative — F1 `-2079/25` at `16(2)`/`8`, F2 `-53/60` at `13`/`19(2)`, F3 `-749/108` at `19(2)`/`1`,
  F5 `-19667/1620` at `R3`/`R4` (all kernel-computed with `norm_num`; reproducible from §R1.10's
  printed rows). The pair-dependence — including the sign change between two pairs of one family — is
  itself evidence that the printed rows are not the data of any single equal-curvature two-parabola
  law.
* **No delivered verdict depends on `λ̂`.** The `_lamHat` rows are value rows; every falsification
  (I11 `_not_model_consistent`, I12) uses the λ-**in**dependent sign of the second divided difference,
  which the model forces to be `1/(4λ) > 0` for `λ > 0`. Changing the pair convention would move the
  `_lamHat` values and leave every verdict as it stands.

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

/-- I8 (`model-constructed`): the degenerate value of the **linear-response** body is `α = 1/2`.
Plan §4.2 #4 and the I8 cell of §8.2 both print `α = 1/2`, and the statement authority (skeleton)
carries the same value. The old `α = 0` belonged to the discarded transition-state-coordinate body:
its identification with `qTransfer`, `transfer_eq_tsCoord` in `PhotoLean/BEP/Criterion.lean`, needs
`lam ≠ 0` and therefore says nothing at the degenerate point. -/
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

/-- I9 (`model-constructed`): the sign of the exact defect detects what the bounds miss —
`qBepDefect (-2) 1 = -1/8 < 0`, against the exact law `x ^ 2 / (4 * λ) = -1/8` with `λ < 0`. -/
theorem inst_I9_unphysical_defect_negative : Rat.qBepDefect (-2 : ℚ) 1 = -(1 / 8) := by
  unfold Rat.qBepDefect Rat.qBepLine Rat.qEact
  norm_num

/-- I9 (`model-constructed`): the Evans–Polanyi bounds hold at the unphysical point. This is the
witness `λ = -2, x = 1` behind the plan's explanatory remark (plan §8.2) that the descriptor
`EPDescriptor` detects what the bounds pair misses; that remark is prose here, **not** a theorem of
this file — no statement below compares `EPDescriptor` with the bounds pair for all `lam`. What the
four I9 rows establish is the coincidence, at this point, of `0 ≤ α ≤ 1` with a negative defect. -/
theorem inst_I9_unphysical_bounds_blind :
    0 ≤ Rat.qTransfer (-2 : ℚ) 1 ∧ Rat.qTransfer (-2 : ℚ) 1 ≤ 1 := by
  unfold Rat.qTransfer
  norm_num

/-! #### I10 — the tolerance threshold (`λ = 2`, `w = 1`) -/

/-- I10 (`model-constructed`): at `λ = 2`, `w = 1` the threshold is `tol = 1/8` — exactly
`w ^ 2 = 4 * λ * tol`, so the window predicate holds (`w* = 2 * √(λ * tol)`). -/
theorem inst_I10_threshold_conforms : Rat.qConformsWindow (2 : ℚ) (1 / 8) 1 := by
  unfold Rat.qConformsWindow
  norm_num

/-- I10 (`model-constructed`): one step below the threshold (`tol = 1/16`) the window fails —
`1 = w ^ 2 > 4 * λ * tol = 1/2`. The pair exhibits that the conformance predicate is decided by
the *squared* threshold `w ^ 2 ≤ 4 * λ * tol`, not by a strict inequality. -/
theorem inst_I10_threshold_fails : ¬ Rat.qConformsWindow (2 : ℚ) (1 / 16) 1 := by
  unfold Rat.qConformsWindow
  norm_num

/-! ### I11 — the first-hand literature families (`LITERATURE.md` §R1.10, kcal/mol, verbatim)

The Lean literals are the sources' **printed kcal/mol** numbers; the model's driving force is
`x = -ΔG°` (F5 prints a classical `ΔE`, so `x = -ΔE`, with the `ΔE`-vs-`ΔG` caveat of §R1.10.5).
`_alphaObs` uses the two rows its family heading names (for F1/F2/F3 the first and the last
documented row with a printed barrier), `_lamHat` an **adjacent** printed pair in the record's table
order, and `_curvature_negative` **three** printed rows whose second divided difference is negative;
the falsification row is the λ-independent consequence (curvature `1/(4λ) > 0` cannot be negative).
Which pair is used matters — see the header's selection disclosure.

Per family the status flag of §R1.10 is `first-hand` for every number used. The record's kJ/mol
column is the record's own arithmetic and is never used in a statement. -/

/-! #### F1 — f-HAT from phenolic antioxidants to `•OOH`, water -/

/-- F1 — source: *Antioxidants* **15**(7), 840–860 (2026), DOI `10.3390/antiox15070868`
(OA, `PMC13405240`), "Computational Study of the Peroxyl Radical Scavenging Ability of Phenolic
Antioxidants"; locus: **Table 1**, "Water" columns, 298.15 K; status **`first-hand`**; reaction
family: f-HAT from a phenolic O–H to `•OOH`. Units: the rows below are the source's **printed
kcal/mol** values; the `ΔG°`/`ΔG‡` pair is a **Gibbs energy and its barrier** (the source prints
`ΔG°, ΔG‡`, not `ΔH`), so the model convention `x = -ΔG°` applies directly and no `ΔH ≈ ΔG°`
substitution is made here. The record's kJ/mol column is the record's own arithmetic (not used).

Rows used (kcal/mol, verbatim): `16(2)` `ΔG° = -0.3`, `ΔG‡ = 15.6`; `8` `ΔG° = -12.9`,
`ΔG‡ = 8.8`. Model abscissae `x = -ΔG°`: `0.3`, `12.9`. -/
theorem inst_I11_F1_alphaObs :
    Rat.qAlphaObs (0.3 : ℚ) 15.6 12.9 8.8 = 34 / 63 := by
  unfold Rat.qAlphaObs
  norm_num

/-- F1 (`first-hand`; **provenance: the F1 family heading above** — *Antioxidants* **15**(7) 840–860
(2026), DOI `10.3390/antiox15070868`, Table 1 "Water" columns, 298.15 K, printed kcal/mol
`ΔG°`/`ΔG‡`; the record's kJ/mol column is unused here). **Role of this row**: the model's two-point
solver at the **adjacent** printed pair `16(2)`/`16(1)` — `16(2)` `ΔG° = -0.3`, `ΔG‡ = 15.6`;
`16(1)` `ΔG° = -0.9`, `ΔG‡ = 15.7` (model abscissae `0.3`, `0.9`). The value `9/20` is the model's
own `λ̂`, **not** the record's per-pair `λ̂ = (x + 2Ea) ± 2√(Ea² + x·Ea)` (irrational, and a
different estimator). No verdict below depends on this value (header, selection disclosure). -/
theorem inst_I11_F1_lamHat : Rat.qLamOfPair (0.3 : ℚ) 15.6 0.9 15.7 = 9 / 20 := by
  unfold Rat.qLamOfPair
  norm_num

/-- F1 (`first-hand`; **provenance: the F1 family heading above** — *Antioxidants* **15**(7) 840–860
(2026), Table 1 "Water" columns, printed kcal/mol). **Role of this row**: the curvature witness at
**three** printed rows `16(1)` (`ΔG° = -0.9`, `ΔG‡ = 15.7`), `14(1)` (`-2.3`, `15.7`) and `12`
(`-4.9`, `13.9`), model abscissae `0.9`, `2.3`, `4.9`. The second divided difference is **negative**
— for every `λ > 0` the model forces `1/(4λ) > 0`. This is a statement about these three printed
rows, not about the record's family-level regression (a regression is not a ℚ identity). -/
theorem inst_I11_F1_curvature_negative :
    Rat.qSecondDividedDiff (0.9 : ℚ) 15.7 2.3 15.7 4.9 13.9 = -(9 / 52) := by
  unfold Rat.qSecondDividedDiff
  norm_num

/-- F1 (`first-hand`; **provenance: the F1 family heading above** — *Antioxidants* **15**(7) 840–860
(2026), Table 1 "Water" columns, printed kcal/mol). **Role of this row**: the λ-independent
falsification — **no** positive-λ equal-curvature two-parabola law reproduces the three printed rows
`16(1)`, `14(1)`, `12` of the water column; it is the quantified consequence of the negative
curvature of the row above, whose sign does not involve `λ̂`. Statement about the model family
instantiated by those numbers, not about the experiment. -/
theorem inst_I11_F1_not_model_consistent :
    ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (0.9 : ℚ) 2.3 4.9 15.7 15.7 13.9 := by
  rintro ⟨lam, hlam, h₁, h₂, h₃⟩
  have hpos := Rat.qModelConsistent3_curvature_pos ⟨hlam, h₁, h₂, h₃⟩
    (by norm_num : (0.9 : ℚ) ≠ 2.3) (by norm_num : (2.3 : ℚ) ≠ 4.9)
    (by norm_num : (0.9 : ℚ) ≠ 4.9)
  rw [show Rat.qSecondDividedDiff (0.9 : ℚ) 15.7 2.3 15.7 4.9 13.9 = -(9 / 52) by
    unfold Rat.qSecondDividedDiff
    norm_num] at hpos
  norm_num at hpos

/-! #### F2 — the same reaction in pentyl ethanoate (PE) -/

/-- F2 — same source / status as F1 (*Antioxidants* **15**(7) 840–860 (2026), DOI
`10.3390/antiox15070868`, OA `PMC13405240`); locus: **Table 1**, "PE" (pentyl ethanoate) columns;
status **`first-hand`**. Units: the source's **printed kcal/mol** `ΔG°` and `ΔG‡` (a Gibbs energy
and its barrier); model convention `x = -ΔG°`. The kJ/mol column of the record is the record's own
arithmetic (not used). Rows used (verbatim): `16(2)` `ΔG° = +1.0`, `ΔG‡ = 14.0`; `10`
`ΔG° = -14.3`, `ΔG‡ = 5.1` (model abscissae `-1.0`, `14.3`). -/
theorem inst_I11_F2_alphaObs :
    Rat.qAlphaObs (-(1.0) : ℚ) 14.0 14.3 5.1 = 89 / 153 := by
  unfold Rat.qAlphaObs
  norm_num

/-- F2 (`first-hand`; **provenance: the F2 family heading above** — same paper, *Antioxidants*
**15**(7) 840–860 (2026), Table 1 "PE" (pentyl ethanoate) columns, printed kcal/mol `ΔG°`/`ΔG‡`).
**Role of this row**: the model's two-point solver at the **adjacent** printed pair `16(2)`
(`ΔG° = +1.0`, `ΔG‡ = 14.0`) and `13` (`-2.2`, `13.3`) in the record's table order; model abscissae
`-1.0`, `2.2`. Pair-dependent (header, selection disclosure); no verdict depends on this value. -/
theorem inst_I11_F2_lamHat : Rat.qLamOfPair (-(1.0) : ℚ) 14.0 2.2 13.3 = 16 / 15 := by
  unfold Rat.qLamOfPair
  norm_num

/-- F2 (`first-hand`; **provenance: the F2 family heading above** — same paper, Table 1 "PE" columns,
printed kcal/mol). **Role of this row**: the curvature witness at **three** printed rows `16(2)`
(`ΔG° = +1.0`, `ΔG‡ = 14.0`), `13` (`-2.2`, `13.3`), `2` (`-4.6`, `10.0`), model abscissae `-1.0`,
`2.2`, `4.6`. Negative, as in F1 — but F2 is inconsistent for a *different* reason than the water
column: its free linear fit is **R² = 0.548** (`LITERATURE.md` §R1.10.3, quoted with its locus),
against R² = 0.934 for the F1 water column (§R1.10.2); hence §R1.10.3 requires the family to be
indexed by solvent as well as by the reacting pair. -/
theorem inst_I11_F2_curvature_negative :
    Rat.qSecondDividedDiff (-(1.0) : ℚ) 14.0 2.2 13.3 4.6 10.0 = -(185 / 896) := by
  unfold Rat.qSecondDividedDiff
  norm_num

/-- F2 (`first-hand`; **provenance: the F2 family heading above** — same paper, Table 1 "PE" columns,
printed kcal/mol). **Role of this row**: the λ-independent falsification of the two-parabola law for
the three printed PE rows `16(2)`, `13`, `2` (negative model curvature against `1/(4λ) > 0`). -/
theorem inst_I11_F2_not_model_consistent :
    ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (-(1.0) : ℚ) 2.2 4.6 14.0 13.3 10.0 := by
  rintro ⟨lam, hlam, h₁, h₂, h₃⟩
  have hpos := Rat.qModelConsistent3_curvature_pos ⟨hlam, h₁, h₂, h₃⟩
    (by norm_num : (-(1.0) : ℚ) ≠ 2.2) (by norm_num : (2.2 : ℚ) ≠ 4.6)
    (by norm_num : (-(1.0) : ℚ) ≠ 4.6)
  rw [show Rat.qSecondDividedDiff (-(1.0) : ℚ) 14.0 2.2 13.3 4.6 10.0 = -(185 / 896) by
    unfold Rat.qSecondDividedDiff
    norm_num] at hpos
  norm_num at hpos

/-! #### F3 — the same substrates with `•OOCH₃`, water column -/

/-- F3 — source: same paper as F1/F2 (*Antioxidants* **15**(7) 840–860 (2026), DOI
`10.3390/antiox15070868`, OA `PMC13405240`); locus: **Table 2**, "Water" columns (`•OOCH₃` as the
abstracting radical, i.e. a second radical and a separate family); status **`first-hand`**. Units:
printed **kcal/mol** `ΔG°`, `ΔG‡` (Gibbs energy and barrier); model convention `x = -ΔG°`.

**Locus honesty**: §R1.10.4 gives, for the Table 2 water column, the family aggregates plus a list
of *representative* rows rather than the full per-row table; the statement below uses exactly those
printed representative rows, taken verbatim: `16(1)` `ΔG° = +0.8`, `ΔG‡ = 15.6`; `7` `ΔG° = -9.9`,
`ΔG‡ = 7.3` (model abscissae `-0.8`, `9.9`). -/
theorem inst_I11_F3_alphaObs :
    Rat.qAlphaObs (-(0.8) : ℚ) 15.6 9.9 7.3 = 83 / 107 := by
  unfold Rat.qAlphaObs
  norm_num

/-- F3 (`first-hand`; **provenance: the F3 family heading above** — same paper, *Antioxidants*
**15**(7), Table 2 "Water" columns (`•OOCH₃`), printed kcal/mol `ΔG°`/`ΔG‡`, representative rows).
**Role of this row**: the model's two-point solver at the **adjacent** printed pair `16(1)`
(`ΔG° = +0.8`, `ΔG‡ = 15.6`) and `19(2)` (`+3.6`, `17.7`) in the record's listing; model abscissae
`-0.8`, `-3.6`. Pair-dependent (header, selection disclosure). -/
theorem inst_I11_F3_lamHat : Rat.qLamOfPair (-(0.8) : ℚ) 15.6 (-(3.6)) 17.7 = 22 / 5 := by
  unfold Rat.qLamOfPair
  norm_num

/-- F3 (`first-hand`; **provenance: the F3 family heading above** — same paper, Table 2 "Water"
columns, printed kcal/mol, representative rows). **Role of this row**: the curvature witness at
**three** printed rows `16(1)` (`ΔG° = +0.8`, `ΔG‡ = 15.6`), `1` (`-7.1`, `11.0`), `7` (`-9.9`,
`7.3`), model abscissae `-0.8`, `7.1`, `9.9`. Negative, against the model's `1/(4λ) > 0`. -/
theorem inst_I11_F3_curvature_negative :
    Rat.qSecondDividedDiff (-(0.8) : ℚ) 15.6 7.1 11.0 9.9 7.3 = -(8175 / 118342) := by
  unfold Rat.qSecondDividedDiff
  norm_num

/-- F3 (`first-hand`; **provenance: the F3 family heading above** — same paper, Table 2 "Water"
columns, printed kcal/mol). **Role of this row**: the λ-independent falsification of the
two-parabola law for the three printed Table 2 water rows `16(1)`, `1`, `7`. -/
theorem inst_I11_F3_not_model_consistent :
    ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (-(0.8) : ℚ) 7.1 9.9 15.6 11.0 7.3 := by
  rintro ⟨lam, hlam, h₁, h₂, h₃⟩
  have hpos := Rat.qModelConsistent3_curvature_pos ⟨hlam, h₁, h₂, h₃⟩
    (by norm_num : (-(0.8) : ℚ) ≠ 7.1) (by norm_num : (7.1 : ℚ) ≠ 9.9)
    (by norm_num : (-(0.8) : ℚ) ≠ 9.9)
  rw [show Rat.qSecondDividedDiff (-(0.8) : ℚ) 15.6 7.1 11.0 9.9 7.3 = -(8175 / 118342) by
    unfold Rat.qSecondDividedDiff
    norm_num] at hpos
  norm_num at hpos

/-! #### F5 — site-resolved C–H abstraction from 2-butanol (classical `ΔE`) -/

/-- F5 — source: *Chem. Sci.* **6**(10), 5866–5881 (2015), DOI `10.1039/c5sc01848j`
(OA, `PMC5950756`); locus: **Table 1**, row `CCSD(T)-F12a/jun-cc-pVTZ`; status **`first-hand`**;
reaction family: H abstraction from the five distinct C–H sites of 2-butanol by `•OOH`. Units: the
table prints a **classical** reaction energy `ΔE` and forward barrier `V‡f` in **kcal/mol** — an
energy, **not** a Gibbs energy, so the `ΔE`-vs-`ΔG` caveat of §R1.10.5 applies to every row and the
model's driving force is `x = -ΔE`. The kJ/mol column of the record is the record's own arithmetic
(not used). Rows used (kcal/mol, verbatim): `R2` `7.62 / 12.38`; `R5` `19.82 / 21.72` (model
abscissae `-7.62`, `-19.82`). -/
theorem inst_I11_F5_alphaObs :
    Rat.qAlphaObs (-(7.62) : ℚ) 12.38 (-(19.82)) 21.72 = 467 / 610 := by
  unfold Rat.qAlphaObs
  norm_num

/-- F5 (`first-hand`; **provenance: the F5 family heading above** — *Chem. Sci.* **6**(10) 5866–5881
(2015), DOI `10.1039/c5sc01848j`, Table 1 row `CCSD(T)-F12a/jun-cc-pVTZ`, printed kcal/mol classical
`ΔE`/`V‡f`). **Role of this row**: the model's two-point solver at the **adjacent** printed pair `R2`
(`ΔE = 7.62`, `V‡f = 12.38`) and `R3` (`13.14`, `17.57`); model abscissae `-7.62`, `-13.14`.
Classical energies, so this is `λ̂` in the `ΔE` convention; pair-dependent (header, selection
disclosure). -/
theorem inst_I11_F5_lamHat :
    Rat.qLamOfPair (-(7.62) : ℚ) 12.38 (-(13.14)) 17.57 = 7958 / 675 := by
  unfold Rat.qLamOfPair
  norm_num

/-- F5 (`first-hand`; **provenance: the F5 family heading above** — *Chem. Sci.* **6**(10),
Table 1 `CCSD(T)-F12a/jun-cc-pVTZ`, classical kcal/mol). **Role of this row**: the curvature witness
at **three** printed rows `R4` (`ΔE = 14.56`, `V‡f = 17.47`), `R1` (`15.80`, `20.32`), `R5`
(`19.82`, `21.72`), model abscissae `-14.56`, `-15.8`, `-19.82`. Negative (classical energies; the
`ΔE`-vs-`ΔG` caveat of §R1.10.5 stands). -/
theorem inst_I11_F5_curvature_negative :
    Rat.qSecondDividedDiff (-(14.56) : ℚ) 17.47 (-(15.8)) 20.32 (-(19.82)) 21.72 =
      -(1215125 / 3277506) := by
  unfold Rat.qSecondDividedDiff
  norm_num

/-- F5 (`first-hand`; **provenance: the F5 family heading above** — *Chem. Sci.* **6**(10) 5866–5881
(2015), Table 1 `CCSD(T)-F12a/jun-cc-pVTZ`, classical kcal/mol). **Role of this row**: the
λ-independent falsification of the two-parabola law for the three printed 2-butanol rows `R4`, `R1`,
`R5` (classical `ΔE`/`V‡f` data, `ΔE`-vs-`ΔG` caveat of §R1.10.5). -/
theorem inst_I11_F5_not_model_consistent :
    ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (-(14.56) : ℚ) (-(15.8)) (-(19.82)) 17.47 20.32 21.72 := by
  rintro ⟨lam, hlam, h₁, h₂, h₃⟩
  have hpos := Rat.qModelConsistent3_curvature_pos ⟨hlam, h₁, h₂, h₃⟩
    (by norm_num : (-(14.56) : ℚ) ≠ -(15.8)) (by norm_num : (-(15.8) : ℚ) ≠ -(19.82))
    (by norm_num : (-(14.56) : ℚ) ≠ -(19.82))
  rw [show Rat.qSecondDividedDiff (-(14.56) : ℚ) 17.47 (-(15.8)) 20.32 (-(19.82)) 21.72 =
      -(1215125 / 3277506) by
    unfold Rat.qSecondDividedDiff
    norm_num] at hpos
  norm_num at hpos

/-! ### I12 — the summary, and non-vacuity of the instance layer -/

/-- I12 (plan §8.2): for each of the four families with per-row data, the two-point slope of the
**chosen** rows lies strictly inside `(0,1)`, while the family's three-row second divided difference
is negative, so **no** positive-λ equal-curvature two-parabola law reproduces those printed rows.
The first conjunct is a claim about the pair named in the family heading — it is *not* a claim about
the family's fit quality (the family-level linear fits and R² values are reported, by locus, in
`LITERATURE.md` §R1.10.2–§R1.10.4; §R1.10.5 reports none for F5). The second is the falsification
shape the plan asks for (`¬ ∃ lam : ℚ, qModelConsistent3 lam …`) applied per family.

Provenance of the four conjuncts (all `first-hand`, kcal/mol, verbatim; the sources print `ΔG°`
for F1/F2/F3 and a classical `ΔE` for F5): F1 = *Antioxidants* **15**(7) 840–860 (2026), Table 1
"Water"; F2 = same paper, Table 1 "PE"; F3 = same paper, Table 2 "Water"; F5 = *Chem. Sci.*
**6**(10) 5866–5881 (2015), Table 1 `CCSD(T)-F12a/jun-cc-pVTZ`. Each family's source, locus, status
and unit are restated in its family heading above. -/
theorem inst_I12_affine_conforms_model_refuted :
    (0 < Rat.qAlphaObs (0.3 : ℚ) 15.6 12.9 8.8 ∧
        Rat.qAlphaObs (0.3 : ℚ) 15.6 12.9 8.8 < 1 ∧
        ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (0.9 : ℚ) 2.3 4.9 15.7 15.7 13.9) ∧
      (0 < Rat.qAlphaObs (-(1.0) : ℚ) 14.0 14.3 5.1 ∧
        Rat.qAlphaObs (-(1.0) : ℚ) 14.0 14.3 5.1 < 1 ∧
        ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (-(1.0) : ℚ) 2.2 4.6 14.0 13.3 10.0) ∧
      (0 < Rat.qAlphaObs (-(0.8) : ℚ) 15.6 9.9 7.3 ∧
        Rat.qAlphaObs (-(0.8) : ℚ) 15.6 9.9 7.3 < 1 ∧
        ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (-(0.8) : ℚ) 7.1 9.9 15.6 11.0 7.3) ∧
      (0 < Rat.qAlphaObs (-(7.62) : ℚ) 12.38 (-(19.82)) 21.72 ∧
        Rat.qAlphaObs (-(7.62) : ℚ) 12.38 (-(19.82)) 21.72 < 1 ∧
        ¬ ∃ lam : ℚ, Rat.qModelConsistent3 lam (-(14.56) : ℚ) (-(15.8)) (-(19.82)) 17.47 20.32 21.72) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · unfold Rat.qAlphaObs
    norm_num
  · unfold Rat.qAlphaObs
    norm_num
  · exact inst_I11_F1_not_model_consistent
  · unfold Rat.qAlphaObs
    norm_num
  · unfold Rat.qAlphaObs
    norm_num
  · exact inst_I11_F2_not_model_consistent
  · unfold Rat.qAlphaObs
    norm_num
  · unfold Rat.qAlphaObs
    norm_num
  · exact inst_I11_F3_not_model_consistent
  · unfold Rat.qAlphaObs
    norm_num
  · unfold Rat.qAlphaObs
    norm_num
  · exact inst_I11_F5_not_model_consistent

/-- Non-vacuity of the instance layer (plan §8.2, last requirement): a conforming verdict, a
non-conforming verdict, a conforming window and a failing window all exist — the layer is not a
table of one-sided verdicts, and the negative rows are not vacuous. -/
theorem inst_nonvacuous :
    (∃ lam x : ℚ, Rat.epQVerdict lam x = Rat.EPQVerdict.conforming) ∧
      (∃ lam x : ℚ, Rat.epQVerdict lam x = Rat.EPQVerdict.subLinear) ∧
      (∃ lam tol w : ℚ, Rat.qConformsWindow lam tol w) ∧
      (∃ lam tol w : ℚ, ¬ Rat.qConformsWindow lam tol w) :=
  ⟨⟨2, 0, inst_I1_thermoneutral_zone⟩, ⟨2, 3, inst_I6_inverted_zone⟩,
    ⟨2, 1 / 4, 0, inst_I1_thermoneutral_conforms⟩, ⟨2, 1 / 16, 1, inst_I10_threshold_fails⟩⟩

end BEP

end PhotoLean
