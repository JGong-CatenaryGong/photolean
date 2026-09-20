/- 自动生成（lead）。运行 proofs/scripts/lake env lean proofs/probes/marcus-all-axioms.lean

   English: Auto-generated (lead). Run proofs/scripts/lake env lean proofs/probes/marcus-all-axioms.lean
-/

import PhotoLean.Marcus.Barrier
import PhotoLean.Marcus.Basic
import PhotoLean.Marcus.Compose
import PhotoLean.Marcus.Instances
import PhotoLean.Marcus.RatModel
import PhotoLean.Marcus.Rate
import PhotoLean.Marcus.Reorg
import PhotoLean.Marcus.Sharp

-- ---- Barrier.lean ----
#print axioms PhotoLean.Marcus.barrier_antitone_of_neg
#print axioms PhotoLean.Marcus.barrier_antitone_of_pos
#print axioms PhotoLean.Marcus.barrier_at_lam
#print axioms PhotoLean.Marcus.barrier_min_at_lam
#print axioms PhotoLean.Marcus.barrier_mono_cases
#print axioms PhotoLean.Marcus.barrier_mono_of_pos
#print axioms PhotoLean.Marcus.barrier_nonneg
#print axioms PhotoLean.Marcus.barrier_symm
#print axioms PhotoLean.Marcus.barrier_zero_lam

-- ---- Basic.lean ----
#print axioms PhotoLean.Marcus.zone_eq_barrierless_iff
#print axioms PhotoLean.Marcus.zone_eq_inverted_iff
#print axioms PhotoLean.Marcus.zone_eq_normal_iff
#print axioms PhotoLean.Marcus.zone_trichotomy

-- ---- Compose.lean ----
#print axioms PhotoLean.Marcus.descriptor_holds_of_microscopic
#print axioms PhotoLean.Marcus.descriptor_holds_of_nonoverlap

-- ---- Instances.lean ----
#print axioms PhotoLean.Marcus.inst_I1_inverted
#print axioms PhotoLean.Marcus.inst_I1_zoneQ
#print axioms PhotoLean.Marcus.inst_I2_not_inverted
#print axioms PhotoLean.Marcus.inst_I2_zoneQ
#print axioms PhotoLean.Marcus.inst_I3_barrier_value
#print axioms PhotoLean.Marcus.inst_I3_inverted
#print axioms PhotoLean.Marcus.inst_I3_rate_peak
#print axioms PhotoLean.Marcus.inst_I3_zoneQ
#print axioms PhotoLean.Marcus.inst_I4_mcc_admissible
#print axioms PhotoLean.Marcus.inst_I4_mcc_descriptor
#print axioms PhotoLean.Marcus.inst_I4_mcc_descriptor_any_kT
#print axioms PhotoLean.Marcus.inst_I4_mcc_rate_drop
#print axioms PhotoLean.Marcus.inst_I4_mcc_rate_drop_unit_kT
#print axioms PhotoLean.Marcus.inst_I4_mcc_rate_drop_x200
#print axioms PhotoLean.Marcus.inst_I4_mcc_x200
#print axioms PhotoLean.Marcus.inst_I4_mcc_x200_zoneQ
#print axioms PhotoLean.Marcus.inst_I4_mcc_x240
#print axioms PhotoLean.Marcus.inst_I4_mcc_x240_zoneQ
#print axioms PhotoLean.Marcus.inst_I5_mcc_not_inverted
#print axioms PhotoLean.Marcus.inst_I5_mcc_rate_rise
#print axioms PhotoLean.Marcus.inst_I5_mcc_x060
#print axioms PhotoLean.Marcus.inst_I5_mcc_x060_zoneQ
#print axioms PhotoLean.Marcus.inst_I6_rc_descriptor_any_kT
#print axioms PhotoLean.Marcus.inst_I6_rc_x110
#print axioms PhotoLean.Marcus.inst_I6_rc_x110_zoneQ
#print axioms PhotoLean.Marcus.inst_I7_nonpos_lam_not_descriptor
#print axioms PhotoLean.Marcus.inst_I7_unphysical_descriptor
#print axioms PhotoLean.Marcus.inst_I7_unphysical_not_admissible
#print axioms PhotoLean.Marcus.inst_I7_unphysical_rate_not_pos
#print axioms PhotoLean.Marcus.normalRegion_of_zoneQ_normal
#print axioms PhotoLean.Marcus.not_invertedRegion_of_zoneQ_normal

-- ---- RatModel.lean ----
#print axioms PhotoLean.Marcus.Rat.barrierQ_cast
#print axioms PhotoLean.Marcus.Rat.barrierQ_zero_lam
#print axioms PhotoLean.Marcus.Rat.zoneQ_eq_zone
#print axioms PhotoLean.Marcus.Rat.zoneQ_inverted_iff

-- ---- Rate.lean ----
#print axioms PhotoLean.Marcus.inverted_rate_decreases
#print axioms PhotoLean.Marcus.normal_rate_increases
#print axioms PhotoLean.Marcus.rate_gt_of_barrier_lt
#print axioms PhotoLean.Marcus.rate_peak_at_lam
#print axioms PhotoLean.Marcus.rate_pos
#print axioms PhotoLean.Marcus.rate_ratio

-- ---- Reorg.lean ----
#print axioms PhotoLean.Marcus.hgeom_of_nonoverlap
#print axioms PhotoLean.Marcus.lamInner_nonneg
#print axioms PhotoLean.Marcus.lamInner_pos
#print axioms PhotoLean.Marcus.lamOuter_pos
#print axioms PhotoLean.Marcus.lam_total_pos

-- ---- Sharp.lean ----
#print axioms PhotoLean.Marcus.descriptor_fails_of_nonpos_lam
#print axioms PhotoLean.Marcus.descriptor_sharp
#print axioms PhotoLean.Marcus.inverted_descriptor_holds
#print axioms PhotoLean.Marcus.inverted_descriptor_holds_of_neg
#print axioms PhotoLean.Marcus.normal_descriptor_holds
#print axioms PhotoLean.Marcus.sharp_A_pos
#print axioms PhotoLean.Marcus.sharp_lam_pos
#print axioms PhotoLean.Marcus.sharp_lam_pos_of_eq
#print axioms PhotoLean.Marcus.sharp_lam_pos_of_lt
