/-
PhotoLean.KashaVavilov.Instances — KV3, the named rational witnesses of the D2 adjudication.

The D2 verdict of `PhotoLean.KashaVavilov.Criterion` is existential: independence needs witnesses,
and an adjudication result is only checkable if the witnesses are pinned down. This module names
the four rational ladders of the plan's §4 rows KV-I1–KV-I4 — the pure Kasha model, the
anti-Vavilov witness of KV-C1, the Vavilov-only witness of KV-C2 and the lossless separator of
KV-C3 — and proves each verdict row on the named ladders themselves, so that a reader can compare
the four models without re-reading the existential proofs.

Every verdict is decided by kernel computation on rational literals: the casts are the same
ladders the API probe pre-computed (`theories/KashaVavilov/probes/KashaVavilov-api-probe.lean`),
and the rows close by unfolding the delivered recursions `Kasha.fluoYield_succ` /
`Kasha.fluoYield_zero` on the literal ladders and finishing with `norm_num` over ℝ. No runtime
evaluation enters any theorem (plan §1.3); `instances_distinct` is decided on the value triples
`(0, 1, 2)`, which already separate the four ladders.

The four rows and what they say:

* KV-I1 `kashaPureLadder_verdict` — `rad 0 = 1`, `rad n = 0` above, `ic ≡ 1`: Kasha's exact rule
  holds at `N = 1` and Vavilov's rule up to `1` holds (the admissible closed model);
* KV-I2 `antiVavilovLadder_verdict` — the KV-C1 ladder (`rad = 0` only at level `1`): the rule
  holds, Vavilov's fails at `N = 1` (`fluoYield 1 = 1/2 ≠ 3/4 = fluoYield 2`), lossy (`ic 0 = 1`);
* KV-I3 `vavilovOnlyLadder_verdict` — the KV-C2 ladder (`rad = 0` only at level `2`):
  `fluoYield 1 = fluoYield 2 = 3/4`, so Vavilov holds while Kasha's rule fails (`rad 1 = 1 > 0`);
* KV-I4 `losslessLadder_verdict` — the KV-C3 ladder (`rad ≡ 1`, `ic 0 = 0`): lossless at the
  lowest level, Vavilov up to `1` vacuously, Kasha's rule fails.

What is NOT derived here: the four ladders are **representative rational models, not fitted
spectroscopic data** (plan §9 honesty table row 3); they are named because their verdicts are
machine-checkable, not because they describe a particular molecule.

Statement authority: every definition body and every theorem signature below is taken word for
word from `theories/KashaVavilov/probes/KashaVavilov-statement-skeleton.lean` (the frozen Phase-1
authority, sha256 `5a51614d80d8340d76b605657802152f6574ad40c31aa6eb9e8d373d65dfdb15`, 29
declarations), which transcribes `theories/KashaVavilov/plan.md` §4. The helper rows
`kashaPureLadder_upperYield`, `kashaPureLadder_fluoYield`, `antiVavilovLadder_fluoYield_one`,
`antiVavilovLadder_fluoYield_two`, `vavilovOnlyLadder_fluoYield_one`,
`vavilovOnlyLadder_fluoYield_two`, `losslessLadder_fluoYield_one` and
`verify_ladders_are_admissible` are auxiliary declarations of this module (the literal arithmetic
the vocabulary needs; no statement of the authority). Note deliberately: the two keyword literals
that `proofs/scripts/check.sh --strict` scans for are not spelled out anywhere in this file — the
scan covers `PhotoLean/**/*.lean` including block comments, so writing them (even in prose) would
be a false-positive FAIL.

Plan locus: `theories/KashaVavilov/plan.md` §4 (KV-I rows), sprint KV3; board
`theories/KashaVavilov/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.KashaVavilov.Instances
    proofs/scripts/check.sh --strict PhotoLean.KashaVavilov.Instances
    proofs/scripts/axioms.sh PhotoLean.KashaVavilov.Instances PhotoLean.KashaVavilov.<theorem>

The delivered file contains no unfinished-proof placeholder and no custom axiomatic declaration;
`#print axioms` of every theorem below lists at most `propext`, `Classical.choice`, `Quot.sound`.
-/
import PhotoLean.KashaVavilov.Basic
import PhotoLean.KashaVavilov.Criterion
import Mathlib
import PhotoLean.Kasha.Basic
import PhotoLean.Kasha.Criterion

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace PhotoLean

namespace KashaVavilov

/-! ## The four named ladders (plan §4, rows KV-I1–KV-I4) -/

/-- Plan section 4, row KV-I1 (definition) — the radiative ladder of the pure Kasha model:
emission only at the lowest level. -/
def kashaPureLadderRad : ℕ → ℚ := fun n => if n = 0 then 1 else 0

/-- Plan section 4, row KV-I1 (definition) — the loss ladder of the pure Kasha model: a unit
nonradiative channel at every level. -/
def kashaPureLadderIc : ℕ → ℚ := fun _ => 1

/-- Plan section 4, row KV-I2 (definition) — the radiative ladder of the KV-C1 witness at ℚ:
dark at level `1`, radiative elsewhere. -/
def antiVavilovLadderRad : ℕ → ℚ := fun n => if n = 1 then 0 else 1

/-- Plan section 4, row KV-I2 (definition) — the loss ladder of the KV-C1 witness at ℚ. -/
def antiVavilovLadderIc : ℕ → ℚ := fun _ => 1

/-- Plan section 4, row KV-I3 (definition) — the radiative ladder of the KV-C2 witness at ℚ:
dark at level `2`, radiative elsewhere. -/
def vavilovOnlyLadderRad : ℕ → ℚ := fun n => if n = 2 then 0 else 1

/-- Plan section 4, row KV-I3 (definition) — the loss ladder of the KV-C2 witness at ℚ. -/
def vavilovOnlyLadderIc : ℕ → ℚ := fun _ => 1

/-- Plan section 4, row KV-I4 (definition) — the radiative ladder of the KV-C3 witness at ℚ:
radiative at every level. -/
def losslessLadderRad : ℕ → ℚ := fun _ => 1

/-- Plan section 4, row KV-I4 (definition) — the loss ladder of the KV-C3 witness at ℚ: no loss
channel at the lowest level, a unit channel above. -/
def losslessLadderIc : ℕ → ℚ := fun n => if n = 0 then 0 else 1

/-! ## Auxiliary literal arithmetic and admissibility of the four ladders -/

/-- Auxiliary row of this module (no statement of the authority): admissibility of all four named
ladders at the excitation levels their verdicts use — the `RateData` bundle carried by KV-I1's
cast ladder at `N = 1`, KV-I2's at `N = 2`, KV-I3's at `N = 2` and KV-I4's at `N = 1`. Proved by
`interval_cases` on the literals plus `norm_num`. -/
theorem verify_ladders_are_admissible :
    Kasha.RateData (fun n => (kashaPureLadderRad n : ℝ)) (fun n => (kashaPureLadderIc n : ℝ)) 1 ∧
    Kasha.RateData (fun n => (antiVavilovLadderRad n : ℝ)) (fun n => (antiVavilovLadderIc n : ℝ)) 2 ∧
    Kasha.RateData (fun n => (vavilovOnlyLadderRad n : ℝ)) (fun n => (vavilovOnlyLadderIc n : ℝ)) 2 ∧
    Kasha.RateData (fun n => (losslessLadderRad n : ℝ)) (fun n => (losslessLadderIc n : ℝ)) 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨fun n hn => ?_, fun n => ?_, fun n => ?_⟩
    · interval_cases n <;> norm_num [Kasha.decay, kashaPureLadderRad, kashaPureLadderIc]
    · dsimp only [kashaPureLadderRad]
      split_ifs <;> norm_num
    · dsimp only [kashaPureLadderIc]
      norm_num
  · refine ⟨fun n hn => ?_, fun n => ?_, fun n => ?_⟩
    · interval_cases n <;> norm_num [Kasha.decay, antiVavilovLadderRad, antiVavilovLadderIc]
    · dsimp only [antiVavilovLadderRad]
      split_ifs <;> norm_num
    · dsimp only [antiVavilovLadderIc]
      norm_num
  · refine ⟨fun n hn => ?_, fun n => ?_, fun n => ?_⟩
    · interval_cases n <;> norm_num [Kasha.decay, vavilovOnlyLadderRad, vavilovOnlyLadderIc]
    · dsimp only [vavilovOnlyLadderRad]
      split_ifs <;> norm_num
    · dsimp only [vavilovOnlyLadderIc]
      norm_num
  · refine ⟨fun n hn => ?_, fun n => ?_, fun n => ?_⟩
    · interval_cases n <;> norm_num [Kasha.decay, losslessLadderRad, losslessLadderIc]
    · dsimp only [losslessLadderRad]
      norm_num
    · dsimp only [losslessLadderIc]
      split_ifs <;> norm_num

/-- Auxiliary row of this module (no statement of the authority): the KV-I1 cast ladder violates
nothing — its leak at `N = 1` vanishes because level `1` is dark. -/
theorem kashaPureLadder_upperYield :
    Kasha.upperYield (fun n => (kashaPureLadderRad n : ℝ)) (fun n => (kashaPureLadderIc n : ℝ)) 1
      = 0 := by
  unfold Kasha.upperYield
  refine Finset.sum_eq_zero fun i hi => ?_
  obtain ⟨hi1, hiN⟩ := Finset.mem_Icc.mp hi
  have hi_eq : i = 1 := by omega
  subst hi_eq
  unfold Kasha.emitYield Kasha.radBranch
  dsimp only [kashaPureLadderRad]
  norm_num

/-- Auxiliary row of this module (no statement of the authority): the KV-I1 yield at `N = 0` is
`1/2` and the yield at `N = 1` is unchanged — Vavilov's rule holds at level `0`. -/
theorem kashaPureLadder_fluoYield :
    Kasha.fluoYield (fun n => (kashaPureLadderRad n : ℝ)) (fun n => (kashaPureLadderIc n : ℝ)) 0
      = 1 / 2 ∧
    Kasha.fluoYield (fun n => (kashaPureLadderRad n : ℝ)) (fun n => (kashaPureLadderIc n : ℝ)) 1
      = 1 / 2 := by
  constructor <;>
    norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
      Kasha.decay, kashaPureLadderRad, kashaPureLadderIc, Finset.sum_range_succ,
      Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton, Finset.prod_Icc_succ_top,
      Finset.Icc_self, Finset.prod_singleton]

/-- Auxiliary row of this module (no statement of the authority): the KV-I2 ladder (`rad = 0`
only at level `1`) has `fluoYield 1 = 1/2` and `fluoYield 2 = 3/4`. -/
theorem antiVavilovLadder_fluoYield_one :
    Kasha.fluoYield (fun n => (antiVavilovLadderRad n : ℝ)) (fun n => (antiVavilovLadderIc n : ℝ)) 1
      = 1 / 2 := by
  norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
    Kasha.decay, antiVavilovLadderRad, antiVavilovLadderIc, Finset.sum_range_succ,
    Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton, Finset.prod_Icc_succ_top,
    Finset.Icc_self, Finset.prod_singleton]

/-- Auxiliary row of this module (no statement of the authority): the KV-I2 ladder's yield at
`N = 2` is `3/4`, so `VavilovAt · 1` fails on it. -/
theorem antiVavilovLadder_fluoYield_two :
    Kasha.fluoYield (fun n => (antiVavilovLadderRad n : ℝ)) (fun n => (antiVavilovLadderIc n : ℝ)) 2
      = 3 / 4 := by
  norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
    Kasha.decay, antiVavilovLadderRad, antiVavilovLadderIc, Finset.sum_range_succ,
    Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton, Finset.prod_Icc_succ_top,
    Finset.Icc_self, Finset.prod_singleton]

/-- Auxiliary row of this module (no statement of the authority): the KV-I3 ladder (`rad = 0`
only at level `2`) also has `fluoYield 1 = 3/4`. -/
theorem vavilovOnlyLadder_fluoYield_one :
    Kasha.fluoYield (fun n => (vavilovOnlyLadderRad n : ℝ)) (fun n => (vavilovOnlyLadderIc n : ℝ)) 1
      = 3 / 4 := by
  norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
    Kasha.decay, vavilovOnlyLadderRad, vavilovOnlyLadderIc, Finset.sum_range_succ,
    Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton, Finset.prod_Icc_succ_top,
    Finset.Icc_self, Finset.prod_singleton]

/-- Auxiliary row of this module (no statement of the authority): the KV-I3 ladder's yield at
`N = 2` is again `3/4`, so `VavilovAt · 1` holds on it. -/
theorem vavilovOnlyLadder_fluoYield_two :
    Kasha.fluoYield (fun n => (vavilovOnlyLadderRad n : ℝ)) (fun n => (vavilovOnlyLadderIc n : ℝ)) 2
      = 3 / 4 := by
  norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
    Kasha.decay, vavilovOnlyLadderRad, vavilovOnlyLadderIc, Finset.sum_range_succ,
    Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton, Finset.prod_Icc_succ_top,
    Finset.Icc_self, Finset.prod_singleton]

/-- Auxiliary row of this module (no statement of the authority): on the KV-I4 lossless ladder
(`rad ≡ 1`, `ic 0 = 0`) the yield at `N = 0` and at `N = 1` are both `1` — Vavilov's rule holds
vacuously and Kasha's rule is the only one that fails. -/
theorem losslessLadder_fluoYield_one :
    Kasha.fluoYield (fun n => (losslessLadderRad n : ℝ)) (fun n => (losslessLadderIc n : ℝ)) 0
      = 1 ∧
    Kasha.fluoYield (fun n => (losslessLadderRad n : ℝ)) (fun n => (losslessLadderIc n : ℝ)) 1
      = 1 := by
  constructor <;>
    norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
      Kasha.decay, losslessLadderRad, losslessLadderIc, Finset.sum_range_succ,
      Finset.sum_range_one, Finset.sum_Icc_succ_top, Finset.sum_singleton, Finset.prod_Icc_succ_top,
      Finset.Icc_self, Finset.prod_singleton]

/-! ## The verdict rows (plan §4, rows KV-I1–KV-I5) -/

/-- Plan section 4, row KV-I1 (verdict) — the cast ladders satisfy `Kasha.KashaRule · 1 ∧
Kasha.VavilovUpTo · 1` (admissible model): the leak at `N = 1` is `0` and the yield does not move
from `N = 0` to `N = 1` (both `1/2`). -/
theorem kashaPureLadder_verdict :
    Kasha.KashaRule (fun n => (kashaPureLadderRad n : ℝ)) (fun n => (kashaPureLadderIc n : ℝ)) 1 ∧
      Kasha.VavilovUpTo (fun n => (kashaPureLadderRad n : ℝ))
        (fun n => (kashaPureLadderIc n : ℝ)) 1 := by
  refine ⟨kashaPureLadder_upperYield, ?_⟩
  intro i hi
  interval_cases i
  exact kashaPureLadder_fluoYield.2.trans kashaPureLadder_fluoYield.1.symm

/-- Plan section 4, row KV-I2 (verdict) — the KV-C1 witness pinned at a named rational ladder:
Kasha's rule holds at level `1`, Vavilov's rule fails there (`fluoYield 1 = 1/2 ≠ 3/4 =
fluoYield 2`), and the ladder sits inside the lossy regime. -/
theorem antiVavilovLadder_verdict :
    Kasha.KashaRule (fun n => (antiVavilovLadderRad n : ℝ))
        (fun n => (antiVavilovLadderIc n : ℝ)) 1 ∧
      ¬ Kasha.VavilovAt (fun n => (antiVavilovLadderRad n : ℝ))
        (fun n => (antiVavilovLadderIc n : ℝ)) 1 ∧
      0 < (antiVavilovLadderIc 0 : ℝ) := by
  have hR2 : Kasha.RateData (fun n => (antiVavilovLadderRad n : ℝ))
      (fun n => (antiVavilovLadderIc n : ℝ)) 1 :=
    rateData_mono verify_ladders_are_admissible.2.1 (by norm_num)
  refine ⟨?_, ?_, by norm_num [antiVavilovLadderIc]⟩
  · exact Kasha.kashaRule_of_rad_zero hR2 fun i hi1 hi2 => by
      have hi : i = 1 := by omega
      subst hi
      norm_num [antiVavilovLadderRad]
  · intro hV
    have hV' : Kasha.fluoYield (fun n => (antiVavilovLadderRad n : ℝ))
        (fun n => (antiVavilovLadderIc n : ℝ)) (1 + 1) =
        Kasha.fluoYield (fun n => (antiVavilovLadderRad n : ℝ))
          (fun n => (antiVavilovLadderIc n : ℝ)) 1 := hV
    rw [antiVavilovLadder_fluoYield_one, antiVavilovLadder_fluoYield_two] at hV'
    norm_num at hV'

/-- Plan section 4, row KV-I3 (verdict) — the KV-C2 witness pinned at a named rational ladder:
Vavilov's rule holds at level `1` (`fluoYield 1 = fluoYield 2 = 3/4`), Kasha's rule fails there
(`rad 1 = 1 > 0`), inside the lossy regime. -/
theorem vavilovOnlyLadder_verdict :
    Kasha.VavilovAt (fun n => (vavilovOnlyLadderRad n : ℝ))
        (fun n => (vavilovOnlyLadderIc n : ℝ)) 1 ∧
      ¬ Kasha.KashaRule (fun n => (vavilovOnlyLadderRad n : ℝ))
        (fun n => (vavilovOnlyLadderIc n : ℝ)) 1 ∧
      0 < (vavilovOnlyLadderIc 0 : ℝ) := by
  refine ⟨?_, ?_, by norm_num [vavilovOnlyLadderIc]⟩
  · show Kasha.fluoYield (fun n => (vavilovOnlyLadderRad n : ℝ))
        (fun n => (vavilovOnlyLadderIc n : ℝ)) (1 + 1) =
        Kasha.fluoYield (fun n => (vavilovOnlyLadderRad n : ℝ))
          (fun n => (vavilovOnlyLadderIc n : ℝ)) 1
    rw [vavilovOnlyLadder_fluoYield_one, vavilovOnlyLadder_fluoYield_two]
  · have hpos1 : 0 < (fun n => (vavilovOnlyLadderRad n : ℝ)) 1 := by
      norm_num [vavilovOnlyLadderRad]
    have hR1 : Kasha.RateData (fun n => (vavilovOnlyLadderRad n : ℝ))
        (fun n => (vavilovOnlyLadderIc n : ℝ)) 1 :=
      rateData_mono verify_ladders_are_admissible.2.2.1 (by norm_num)
    exact Kasha.not_kashaRule_of_rad_pos (i := 1) hR1 (by norm_num) (by norm_num) hpos1

/-- Plan section 4, row KV-I4 (verdict) — the KV-C3 witness pinned at a named rational ladder:
lossless at the lowest level (`ic 0 = 0`, the yield is identically `1` by
`Kasha.fluoYield_eq_one_sub_loss`), Vavilov's rule holds vacuously up to level `1`, and Kasha's
rule fails. -/
theorem losslessLadder_verdict :
    (losslessLadderIc 0 : ℝ) = 0 ∧
      Kasha.VavilovUpTo (fun n => (losslessLadderRad n : ℝ))
        (fun n => (losslessLadderIc n : ℝ)) 1 ∧
      ¬ Kasha.KashaRule (fun n => (losslessLadderRad n : ℝ))
        (fun n => (losslessLadderIc n : ℝ)) 1 := by
  refine ⟨by norm_num [losslessLadderIc], ?_, ?_⟩
  · intro i hi
    interval_cases i
    exact losslessLadder_fluoYield_one.2.trans losslessLadder_fluoYield_one.1.symm
  · have hpos1 : 0 < (fun n => (losslessLadderRad n : ℝ)) 1 := by
      norm_num [losslessLadderRad]
    exact Kasha.not_kashaRule_of_rad_pos (i := 1) verify_ladders_are_admissible.2.2.2
      (by norm_num) (by norm_num) hpos1

/-- Plan section 4, row KV-I5 — the four named rad-ladders are pairwise different as functions.
Proof route (plan §4): each pair differs at a point of `{0, 1, 2}` (their value triples are
`(1,0,0)`, `(1,0,1)`, `(1,1,0)`, `(1,1,1)`), decided by `congrFun` + `decide`. -/
theorem instances_distinct :
    kashaPureLadderRad ≠ antiVavilovLadderRad ∧ kashaPureLadderRad ≠ vavilovOnlyLadderRad ∧
      kashaPureLadderRad ≠ losslessLadderRad ∧ antiVavilovLadderRad ≠ vavilovOnlyLadderRad ∧
        antiVavilovLadderRad ≠ losslessLadderRad ∧ vavilovOnlyLadderRad ≠ losslessLadderRad := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h2 := congrFun h 2
    simp only [kashaPureLadderRad, antiVavilovLadderRad] at h2
    norm_num at h2
  · intro h
    have h1 := congrFun h 1
    simp only [kashaPureLadderRad, vavilovOnlyLadderRad] at h1
    norm_num at h1
  · intro h
    have h1 := congrFun h 1
    simp only [kashaPureLadderRad, losslessLadderRad] at h1
    norm_num at h1
  · intro h
    have h2 := congrFun h 2
    simp only [antiVavilovLadderRad, vavilovOnlyLadderRad] at h2
    norm_num at h2
  · intro h
    have h1 := congrFun h 1
    simp only [antiVavilovLadderRad, losslessLadderRad] at h1
    norm_num at h1
  · intro h
    have h2 := congrFun h 2
    simp only [vavilovOnlyLadderRad, losslessLadderRad] at h2
    norm_num at h2

end KashaVavilov

end PhotoLean
