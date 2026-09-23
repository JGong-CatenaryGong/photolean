/-
kashaVavilov-statement-skeleton.lean — the STATEMENT AUTHORITY of the KashaVavilov theory.

Statement-first (iron rule 2): every declaration below is the agreed statement verbatim; the bodies
are placeholders on purpose. This file must compile at 0 error
(`proofs/scripts/lake env lean theories/KashaVavilov/probes/KashaVavilov-statement-skeleton.lean`)
BEFORE any proof work starts; delivery replaces the bodies verbatim and
`python3 theories/BEP/probes/bep-fidelity.py --theory KashaVavilov` compares the delivered
signatures to this file word for word.

Plan: `theories/KashaVavilov/plan.md` (the frozen design; its §4 is the statement inventory).
Milestones: KV1 (Basic — rows KV-B1–KV-B7), KV2 (Criterion — rows KV-C1–KV-C7, the D2 core),
KV3 (Instances — rows KV-I1–KV-I5).

The theory adjudicates the Kasha rule against Vavilov's rule (adjudication target D2): on the
delivered excited-state ladder of `PhotoLean.Kasha.Basic` (reused by import; nothing upstream is
modified), the two predicates are pointwise logically independent — each has admissible witnesses
where it holds and the other fails, inside the lossy regime `0 < ic 0` (KV-C1, KV-C2); the
coincidence holds exactly under the closed quantification plus the loss premise (the delivered
`Kasha.kashaRule_iff_vavilovUpTo`, re-stated as a conjunct of KV-C4); and the lossless corner
separates the closed forms (KV-C3), so the premise is load-bearing.
-/
import Mathlib
import PhotoLean.Kasha.Basic
import PhotoLean.Kasha.Criterion

set_option autoImplicit false

namespace PhotoLean

namespace KashaVavilov

/-! ## KV1 — description layer (`PhotoLean/KashaVavilov/Basic.lean`; plan §4, rows KV-B1–KV-B7) -/

/-- Plan section 4, row KV-B1 — the new predicate of this theory: the normalized spectra at two
excitation levels agree on the common levels (pairwise spectral agreement). -/
def SpecSame (rad ic : ℕ → ℝ) (M N : ℕ) : Prop :=
  ∀ i, i ≤ M → i ≤ N → Kasha.specFrac rad ic i M = Kasha.specFrac rad ic i N

/-- Plan section 4, row KV-B2 — the total yield splits into the lowest level's emission and the
leak; pure `Finset.range`/`Icc` split, no premises (totalized). Proof route (plan §5):
`Finset.sum_range_succ` at `0` + the `Icc 1 N` reindexing — check the delivered sibling
`Kasha.fluoYield_eq_low_add_upper` (same identity under a `RateData` signature premise) first;
do not re-prove a delivered row. -/
theorem fluoYield_eq_emitYield_zero_add_upperYield (rad ic : ℕ → ℝ) (N : ℕ) :
    Kasha.fluoYield rad ic N = Kasha.emitYield rad ic 0 N + Kasha.upperYield rad ic N := by
  sorry

/-- Plan section 4, row KV-B3 — premise-bundle restriction: the standing physical premises at
level `N` restrict to any lower level `M ≤ N`. -/
theorem rateData_mono {rad ic : ℕ → ℝ} {M N : ℕ} (h : Kasha.RateData rad ic N) (hMN : M ≤ N) :
    Kasha.RateData rad ic M := by
  sorry

/-- Plan section 4, row KV-B4 — under the exact Kasha rule the lowest level carries the whole
normalized spectrum. Proof route (plan §5): `Kasha.kashaRule_iff_rad_zero` + `radBranch = 0` +
`zero_div`/`div_self`. -/
theorem specFrac_zero_of_kashaRule {rad ic : ℕ → ℝ} {N : ℕ}
    (hK : Kasha.KashaRule rad ic N) (hpos : 0 < Kasha.fluoYield rad ic N) :
    Kasha.specFrac rad ic 0 N = 1 := by
  sorry

/-- Plan section 4, row KV-B5 — under the exact Kasha rule every upper level carries none of the
normalized spectrum. Proof route (plan §5): `Kasha.kashaRule_iff_rad_zero` + `radBranch = 0` +
`zero_div`/`div_self`. -/
theorem specFrac_succ_of_kashaRule {rad ic : ℕ → ℝ} {N i : ℕ} (h : Kasha.RateData rad ic N)
    (hK : Kasha.KashaRule rad ic N) (hi1 : 1 ≤ i) (hiN : i ≤ N) :
    Kasha.specFrac rad ic i N = 0 := by
  sorry

/-- Plan section 4, row KV-B6 — the exact Kasha rule at level `N` descends to every lower level
`M ≤ N`. -/
theorem kashaRule_mono {rad ic : ℕ → ℝ} {M N : ℕ} (h : Kasha.RateData rad ic N) (hMN : M ≤ N)
    (hK : Kasha.KashaRule rad ic N) : Kasha.KashaRule rad ic M := by
  sorry

/-- Plan section 4, row KV-B7 — the exact rule gives the spectral Vavilov rule: under Kasha the
spectrum is the delta at level `0`, hence excitation-independent. -/
theorem specSame_of_kashaRule {rad ic : ℕ → ℝ} {N : ℕ} (h : Kasha.RateData rad ic N)
    (hpos : ∀ M, M ≤ N → 0 < Kasha.fluoYield rad ic M) (hK : Kasha.KashaRule rad ic N) :
    ∀ M, M ≤ N → SpecSame rad ic M N := by
  sorry

/-! ## KV2 — the D2 core (`PhotoLean/KashaVavilov/Criterion.lean`; plan §4, rows KV-C1–KV-C7) -/

/-- Plan section 4, row KV-C1 — first independence direction: Kasha's rule does not imply
Vavilov's rule. Proof route (plan §5): witness `rad = fun n => if n = 1 then 0 else 1`,
`ic = fun _ => 1` with `fluoYield 1 = 1/2`, `fluoYield 2 = 3/4`; unfold `Kasha.fluoYield_succ` on
the literal witness and close the numeric goals by `norm_num`; admissibility by `intro n hn;
interval_cases n`. The witness sits at the positive excitation level `N = 1` inside the lossy
regime (`ic 0 = 1 > 0`): the independence is not the degenerate corner (the M1 lesson applied
prospectively). -/
theorem kashaRule_not_implies_vavilovAt :
    ∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 2 ∧ Kasha.KashaRule rad ic 1 ∧
      ¬ Kasha.VavilovAt rad ic 1 ∧ 0 < ic 0 := by
  sorry

/-- Plan section 4, row KV-C2 — second independence direction: Vavilov's rule does not imply
Kasha's rule. Proof route (plan §5): witness `rad = fun n => if n = 2 then 0 else 1`,
`ic = fun _ => 1` with `fluoYield 1 = fluoYield 2 = 3/4`, `rad 1 = 1 > 0`; `Kasha.fluoYield_succ`
+ `norm_num`, admissibility by `intro n hn; interval_cases n`. -/
theorem vavilovAt_not_implies_kashaRule :
    ∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 2 ∧ Kasha.VavilovAt rad ic 1 ∧
      ¬ Kasha.KashaRule rad ic 1 ∧ 0 < ic 0 := by
  sorry

/-- Plan section 4, row KV-C3 — the `0 < ic 0` premise of the delivered equivalence is
load-bearing: at `ic 0 = 0` the yield is identically `1` (`Kasha.fluoYield_eq_one_sub_loss`),
Vavilov's rule holds vacuously, and Kasha's rule fails. Proof route (plan §5): witness
`rad = fun _ => 1`, `ic = fun n => if n = 0 then 0 else 1`; `Kasha.fluoYield_succ` + `norm_num`,
admissibility by `intro n hn; interval_cases n`. -/
theorem lossless_separates_kasha_vavilov :
    ∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 1 ∧ ic 0 = 0 ∧ Kasha.VavilovUpTo rad ic 1 ∧
      ¬ Kasha.KashaRule rad ic 1 := by
  sorry

/-- Plan section 4, row KV-C4 — **the D2 adjudication headline**: the two rules are pointwise
independent in both directions (KV-C1, KV-C2), they coincide exactly under the closed
quantification plus the loss premise (the delivered `Kasha.kashaRule_iff_vavilovUpTo` re-stated),
and the lossless corner separates the closed forms (KV-C3). Proof route: one conjunct per
component row. -/
theorem d2_verdict :
    (∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 2 ∧ Kasha.KashaRule rad ic 1 ∧
      ¬ Kasha.VavilovAt rad ic 1 ∧ 0 < ic 0) ∧
    (∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 2 ∧ Kasha.VavilovAt rad ic 1 ∧
      ¬ Kasha.KashaRule rad ic 1 ∧ 0 < ic 0) ∧
    (∀ rad ic : ℕ → ℝ, ∀ N : ℕ, Kasha.RateData rad ic N → 0 < ic 0 →
      (Kasha.KashaRule rad ic N ↔ Kasha.VavilovUpTo rad ic N)) ∧
    (∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 1 ∧ ic 0 = 0 ∧ Kasha.VavilovUpTo rad ic 1 ∧
      ¬ Kasha.KashaRule rad ic 1) := by
  sorry

/-- Plan section 4, row KV-C5 — positivity of the cascade is exactly the positivity of every
nonradiative rate above level `i`. -/
theorem cascade_pos_iff {rad ic : ℕ → ℝ} {N i : ℕ} (h : Kasha.RateData rad ic N) :
    (0 < Kasha.cascade rad ic i N ↔ ∀ j, i + 1 ≤ j → j ≤ N → 0 < ic j) := by
  sorry

/-- Plan section 4, row KV-C6 — positivity of a level-resolved emission yield is exactly a
radiative level reached by a positive cascade. -/
theorem emitYield_pos_iff {rad ic : ℕ → ℝ} {N i : ℕ} (h : Kasha.RateData rad ic N) (hi : i ≤ N) :
    (0 < Kasha.emitYield rad ic i N ↔ 0 < rad i ∧ 0 < Kasha.cascade rad ic i N) := by
  sorry

/-- Plan section 4, row KV-C7 — **the anti-Kasha boundary**: a violation of the rule is always
observable in this model. Proof route (plan §4/§5): `→` is `Kasha.upperYield_eq_zero_iff`
contraposed with KV-C6; `←` uses the maximal emitter (KV-C7b): the largest `i ∈ [1,N]` with
`0 < rad i` has every level above it nonradiative, hence (by `RateData.decay_pos`) converting with
certainty, so its cascade is `1` and KV-C7a applies. -/
theorem antiKasha_observable_iff {rad ic : ℕ → ℝ} {N : ℕ} (h : Kasha.RateData rad ic N) :
    (0 < Kasha.upperYield rad ic N ↔ ¬ Kasha.KashaRule rad ic N) := by
  sorry

/-- Plan section 4, row KV-C7a (sub-row of KV-C7) — a radiative level above the lowest one whose
higher levels are all nonradiative makes the leak positive: its `icBranch` factors are all `1`
(by `RateData.decay_pos`), its cascade is `1`, and its `emitYield` lower-bounds the sum
`Kasha.upperYield`. -/
theorem upperYield_pos_of_rad_pos {rad ic : ℕ → ℝ} {N i : ℕ} (h : Kasha.RateData rad ic N)
    (hi1 : 1 ≤ i) (hiN : i ≤ N) (hrad : 0 < rad i) (habove : ∀ j, i < j → j ≤ N → rad j = 0) :
    0 < Kasha.upperYield rad ic N := by
  sorry

/-- Plan section 4, row KV-C7b (sub-row of KV-C7) — the maximal emitter exists: among the
radiative levels of `[1, N]` there is a largest one, and every level above it is nonradiative.
Proof route (plan §5): a maximal-element API over `{j ∈ Finset.Icc 1 N | 0 < rad j}`
(`Finset.max'`, classical); API-calibrate before proving (iron rule 4). Weakest-premise standard:
only `rad`-nonnegativity is consumed (to read maximality as `rad j = 0` above), so no `RateData`
bundle is taken. -/
theorem exists_maximal_emitter {rad : ℕ → ℝ} {N : ℕ} (hnn : ∀ n, 0 ≤ rad n)
    (h : ∃ i, 1 ≤ i ∧ i ≤ N ∧ 0 < rad i) :
    ∃ i, 1 ≤ i ∧ i ≤ N ∧ 0 < rad i ∧ ∀ j, i < j → j ≤ N → rad j = 0 := by
  sorry

/-! ## KV3 — named witnesses, rational-valued ladders (`PhotoLean/KashaVavilov/Instances.lean`;
plan §4, rows KV-I1–KV-I5). Verdicts close by `norm_num` over ℝ (kernel computation on rational
literals — no runtime evaluation enters any theorem). -/

/-- Plan section 4, row KV-I1 (definition) — the radiative ladder of the pure Kasha model:
emission only at the lowest level. -/
def kashaPureLadderRad : ℕ → ℚ := fun n => if n = 0 then 1 else 0

/-- Plan section 4, row KV-I1 (definition) — the loss ladder of the pure Kasha model: a unit
nonradiative channel at every level. -/
def kashaPureLadderIc : ℕ → ℚ := fun _ => 1

/-- Plan section 4, row KV-I1 (verdict) — the cast ladders satisfy `Kasha.KashaRule · 1 ∧
Kasha.VavilovUpTo · 1` (admissible model). Proof route (plan §4): `norm_num` over ℝ via
`Kasha.fluoYield_succ`. -/
theorem kashaPureLadder_verdict :
    Kasha.KashaRule (fun n => (kashaPureLadderRad n : ℝ)) (fun n => (kashaPureLadderIc n : ℝ)) 1 ∧
      Kasha.VavilovUpTo (fun n => (kashaPureLadderRad n : ℝ))
        (fun n => (kashaPureLadderIc n : ℝ)) 1 := by
  sorry

/-- Plan section 4, row KV-I2 (definition) — the radiative ladder of the KV-C1 witness at ℚ:
dark at level `1`, radiative elsewhere. -/
def antiVavilovLadderRad : ℕ → ℚ := fun n => if n = 1 then 0 else 1

/-- Plan section 4, row KV-I2 (definition) — the loss ladder of the KV-C1 witness at ℚ. -/
def antiVavilovLadderIc : ℕ → ℚ := fun _ => 1

/-- Plan section 4, row KV-I2 (verdict) — the KV-C1 witness pinned at a named rational ladder:
Kasha's rule holds at level `1`, Vavilov's rule fails there (`fluoYield 1 = 1/2 ≠ 3/4 =
fluoYield 2`), and the ladder sits inside the lossy regime. Proof route (plan §4/§5):
`Kasha.fluoYield_succ` + `norm_num` over ℝ. -/
theorem antiVavilovLadder_verdict :
    Kasha.KashaRule (fun n => (antiVavilovLadderRad n : ℝ))
        (fun n => (antiVavilovLadderIc n : ℝ)) 1 ∧
      ¬ Kasha.VavilovAt (fun n => (antiVavilovLadderRad n : ℝ))
        (fun n => (antiVavilovLadderIc n : ℝ)) 1 ∧
      0 < (antiVavilovLadderIc 0 : ℝ) := by
  sorry

/-- Plan section 4, row KV-I3 (definition) — the radiative ladder of the KV-C2 witness at ℚ:
dark at level `2`, radiative elsewhere. -/
def vavilovOnlyLadderRad : ℕ → ℚ := fun n => if n = 2 then 0 else 1

/-- Plan section 4, row KV-I3 (definition) — the loss ladder of the KV-C2 witness at ℚ. -/
def vavilovOnlyLadderIc : ℕ → ℚ := fun _ => 1

/-- Plan section 4, row KV-I3 (verdict) — the KV-C2 witness pinned at a named rational ladder:
Vavilov's rule holds at level `1` (`fluoYield 1 = fluoYield 2 = 3/4`), Kasha's rule fails there
(`rad 1 = 1 > 0`), inside the lossy regime. Proof route (plan §4/§5): `Kasha.fluoYield_succ` +
`norm_num` over ℝ. -/
theorem vavilovOnlyLadder_verdict :
    Kasha.VavilovAt (fun n => (vavilovOnlyLadderRad n : ℝ))
        (fun n => (vavilovOnlyLadderIc n : ℝ)) 1 ∧
      ¬ Kasha.KashaRule (fun n => (vavilovOnlyLadderRad n : ℝ))
        (fun n => (vavilovOnlyLadderIc n : ℝ)) 1 ∧
      0 < (vavilovOnlyLadderIc 0 : ℝ) := by
  sorry

/-- Plan section 4, row KV-I4 (definition) — the radiative ladder of the KV-C3 witness at ℚ:
radiative at every level. -/
def losslessLadderRad : ℕ → ℚ := fun _ => 1

/-- Plan section 4, row KV-I4 (definition) — the loss ladder of the KV-C3 witness at ℚ: no loss
channel at the lowest level, a unit channel above. -/
def losslessLadderIc : ℕ → ℚ := fun n => if n = 0 then 0 else 1

/-- Plan section 4, row KV-I4 (verdict) — the KV-C3 witness pinned at a named rational ladder:
lossless at the lowest level (`ic 0 = 0`, the yield is identically `1` by
`Kasha.fluoYield_eq_one_sub_loss`), Vavilov's rule holds vacuously up to level `1`, and Kasha's
rule fails. Proof route (plan §4/§5): `Kasha.fluoYield_succ` + `norm_num` over ℝ. -/
theorem losslessLadder_verdict :
    (losslessLadderIc 0 : ℝ) = 0 ∧
      Kasha.VavilovUpTo (fun n => (losslessLadderRad n : ℝ))
        (fun n => (losslessLadderIc n : ℝ)) 1 ∧
      ¬ Kasha.KashaRule (fun n => (losslessLadderRad n : ℝ))
        (fun n => (losslessLadderIc n : ℝ)) 1 := by
  sorry

/-- Plan section 4, row KV-I5 — the four named rad-ladders are pairwise different as functions.
Proof route (plan §4): each pair differs at a point of `{0, 1, 2}`; `congrFun` + `decide`. -/
theorem instances_distinct :
    kashaPureLadderRad ≠ antiVavilovLadderRad ∧ kashaPureLadderRad ≠ vavilovOnlyLadderRad ∧
      kashaPureLadderRad ≠ losslessLadderRad ∧ antiVavilovLadderRad ≠ vavilovOnlyLadderRad ∧
        antiVavilovLadderRad ≠ losslessLadderRad ∧ vavilovOnlyLadderRad ≠ losslessLadderRad := by
  sorry

end KashaVavilov

end PhotoLean
