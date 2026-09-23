/-
kashaVavilov API-calibration probe (Sprint KV0; iron rule 4: no guessed names).
Run: proofs/scripts/lake env lean theories/KashaVavilov/probes/KashaVavilov-api-probe.lean
Expected: exit 0. Every `#check` confirms a name that the statement skeleton
(`KashaVavilov-statement-skeleton.lean`) or its plan-§5 proof routes use; the proved `example`s
pre-compute the witness values that plan §4 pins down for rows KV-C1/KV-C2/KV-C3 (probes are
calibration tools — examples here MAY be proved; the skeleton itself stays placeholder-only).
-/
import Mathlib
import PhotoLean.Kasha.Basic
import PhotoLean.Kasha.Criterion

namespace PhotoLean

set_option autoImplicit false

-- ==== delivered `PhotoLean.Kasha` names the skeleton statements use ====
#check @PhotoLean.Kasha.RateData
#check @PhotoLean.Kasha.RateData.decay_pos
#check @PhotoLean.Kasha.RateData.rad_nonneg
#check @PhotoLean.Kasha.RateData.ic_nonneg
#check @PhotoLean.Kasha.decay
#check @PhotoLean.Kasha.radBranch
#check @PhotoLean.Kasha.icBranch
#check @PhotoLean.Kasha.cascade
#check @PhotoLean.Kasha.emitYield
#check @PhotoLean.Kasha.fluoYield
#check @PhotoLean.Kasha.upperYield
#check @PhotoLean.Kasha.specFrac
#check @PhotoLean.Kasha.KashaRule
#check @PhotoLean.Kasha.VavilovAt
#check @PhotoLean.Kasha.VavilovUpTo

-- ==== delivered theorems the docstrings and plan-§5 routes cite ====
#check @PhotoLean.Kasha.fluoYield_eq_low_add_upper
#check @PhotoLean.Kasha.fluoYield_zero
#check @PhotoLean.Kasha.upperYield_zero
#check @PhotoLean.Kasha.cascade_self
#check @PhotoLean.Kasha.emitYield_self
#check @PhotoLean.Kasha.radBranch_nonneg
#check @PhotoLean.Kasha.icBranch_nonneg
#check @PhotoLean.Kasha.emitYield_nonneg
#check @PhotoLean.Kasha.fluoYield_nonneg
#check @PhotoLean.Kasha.upperYield_nonneg
#check @PhotoLean.Kasha.cascade_succ
#check @PhotoLean.Kasha.emitYield_succ
#check @PhotoLean.Kasha.emitYield_succ_self
#check @PhotoLean.Kasha.fluoYield_succ
#check @PhotoLean.Kasha.fluoYield_eq_one_sub_loss
#check @PhotoLean.Kasha.upperYield_eq_zero_iff
#check @PhotoLean.Kasha.kashaRule_iff_rad_zero
#check @PhotoLean.Kasha.not_kashaRule_of_rad_pos
#check @PhotoLean.Kasha.vavilovAt_iff_rad_zero
#check @PhotoLean.Kasha.vavilovUpTo_iff_rad_zero
#check @PhotoLean.Kasha.kashaRule_iff_vavilovUpTo

-- ==== mathlib names the plan-§5 routes and the literal-witness computation pattern use ====
#check @Finset.sum_range_succ
#check @Finset.sum_range_one
#check @Finset.sum_Icc_succ_top
#check @Finset.sum_singleton
#check @Finset.prod_Icc_succ_top
#check @Finset.Icc_self
#check @Finset.prod_singleton
#check @Finset.mem_Icc
#check @zero_div
#check @div_self
-- KV-C7a candidates: lower-bound a nonnegative sum by one positive term
#check @Finset.single_le_sum
#check @Finset.sum_pos'
-- KV-C7b candidates: maximal-element API over `{j ∈ Finset.Icc 1 N | 0 < rad j}` (classical)
#check @Finset.max'
#check @Finset.exists_max_image

-- ==== KV-C1 witness pre-computation (plan §4 row KV-C1):
-- rad = fun n => if n = 1 then 0 else 1, ic = fun _ => 1 ====

/-- Admissibility of the KV-C1 witness (plan §5 route: `intro n hn; interval_cases n`). -/
example : Kasha.RateData (fun n => if n = 1 then (0 : ℝ) else 1) (fun _ => 1) 2 := by
  refine ⟨fun n hn => ?_, fun n => ?_, fun n => ?_⟩
  · interval_cases n <;> norm_num [Kasha.decay]
  · by_cases h : n = 1
    · subst h
      norm_num
    · rw [if_neg h]
      norm_num
  · exact zero_le_one

/-- The KV-C1 witness yield at level 1 is 1/2 (computation pattern of `PhotoLean.Kasha.Instances`
rows I8/I8b, reused verbatim). -/
example : Kasha.fluoYield (fun n => if n = 1 then (0 : ℝ) else 1) (fun _ => 1) 1 = 1 / 2 := by
  norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
    Kasha.decay, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- The KV-C1 witness yield at level 2 is 3/4: `VavilovAt · 1` fails. -/
example : Kasha.fluoYield (fun n => if n = 1 then (0 : ℝ) else 1) (fun _ => 1) 2 = 3 / 4 := by
  norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
    Kasha.decay, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

-- ==== KV-C2 witness pre-computation (plan §4 row KV-C2):
-- rad = fun n => if n = 2 then 0 else 1, ic = fun _ => 1 ====

/-- Admissibility of the KV-C2 witness. -/
example : Kasha.RateData (fun n => if n = 2 then (0 : ℝ) else 1) (fun _ => 1) 2 := by
  refine ⟨fun n hn => ?_, fun n => ?_, fun n => ?_⟩
  · interval_cases n <;> norm_num [Kasha.decay]
  · by_cases h : n = 2
    · subst h
      norm_num
    · rw [if_neg h]
      norm_num
  · exact zero_le_one

/-- The KV-C2 witness yield at level 1 is 3/4. -/
example : Kasha.fluoYield (fun n => if n = 2 then (0 : ℝ) else 1) (fun _ => 1) 1 = 3 / 4 := by
  norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
    Kasha.decay, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- The KV-C2 witness yield at level 2 is again 3/4: `VavilovAt · 1` holds while `rad 1 = 1 > 0`
refutes Kasha's rule. -/
example : Kasha.fluoYield (fun n => if n = 2 then (0 : ℝ) else 1) (fun _ => 1) 2 = 3 / 4 := by
  norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
    Kasha.decay, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- The KV-C2 witness is radiative at level 1 (`rad 1 = 1 > 0`). -/
example : 0 < (fun n => if n = 2 then (0 : ℝ) else 1) 1 := by
  norm_num

-- ==== KV-C3 witness pre-computation (plan §4 row KV-C3):
-- rad = fun _ => 1, ic = fun n => if n = 0 then 0 else 1 ====

/-- Admissibility of the KV-C3 witness (only level `N = 1` is needed). -/
example : Kasha.RateData (fun _ => (1 : ℝ)) (fun n => if n = 0 then (0 : ℝ) else 1) 1 := by
  refine ⟨fun n hn => ?_, fun n => ?_, fun n => ?_⟩
  · interval_cases n <;> norm_num [Kasha.decay]
  · exact zero_le_one
  · by_cases h : n = 0
    · subst h
      norm_num
    · rw [if_neg h]
      norm_num

/-- The KV-C3 witness is lossless at the lowest level. -/
example : (fun n => if n = 0 then (0 : ℝ) else 1) 0 = 0 := by
  norm_num

/-- The KV-C3 witness yield at level 0 is 1 (the yield is identically `1`, cf.
`Kasha.fluoYield_eq_one_sub_loss`). -/
example : Kasha.fluoYield (fun _ => (1 : ℝ)) (fun n => if n = 0 then (0 : ℝ) else 1) 0 = 1 := by
  norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
    Kasha.decay, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/-- The KV-C3 witness yield at level 1 is still 1: `VavilovAt · 0` holds vacuously while
`rad 1 = 1 > 0` refutes Kasha's rule. -/
example : Kasha.fluoYield (fun _ => (1 : ℝ)) (fun n => if n = 0 then (0 : ℝ) else 1) 1 = 1 := by
  norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
    Kasha.decay, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
    Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

end PhotoLean
