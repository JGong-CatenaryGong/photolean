/-
PhotoLean.FluorPhos.Criterion — milestone FP2, the law layer of the fluorescence–phosphorescence
competition.

The claim proved here (plan §1.1): from `S₁` the molecule fluoresces (rate `kF`), converts to the
ground state (`kIC`), or crosses to the triplet manifold (`kISC`); from `T₁` it phosphoresces
(`kP`) or decays nonradiatively (`kNR`). The phosphorescence-to-fluorescence ratio is then the
intersystem-crossing odds times the triplet radiative branch (FP-C2), the two yields never exceed
unity in total (FP-C3) and they exhaust unity exactly when there is no S₁ internal-conversion loss
and the triplet is either never populated or perfectly radiative (FP-C4). This module carries the
closed-form cascade (FP-C1), the competition law (FP-C2), the exhaustion bound (FP-C3), the
losslessness boundary (FP-C4), both halves of the heavy-atom direction (FP-C5), the crossover in
closed form and its threshold form (FP-C6), the spin-forbiddenness boundary (FP-C7) and the
non-vacuity witness that keeps the competition from being empty (FP-C8).

**FP-C4 was corrected at design time** (plan §3.1 entry 0): the losslessness boundary is
`kIC = 0 ∧ (kISC = 0 ∨ kNR = 0)`, not the naive `kIC = 0 ∧ kNR = 0`. With `kISC = 0` the triplet
is never populated, so no triplet loss can pass through it and `kNR` is unconstrained. The
delivered row is the corrected row of the authority. The delivered proof reduces the row to the
nonnegative defect `kIC·(kP+kNR) + kISC·kNR` (see `exhaust_residue`), which is exactly the
nonnegativity split the row's docstring prescribes.

**FP-C5 premise note.** Both halves consume the primed bundle `h' : FPData kF kISC' kIC kP kNR`.
The prime-side bookkeeping is load-bearing: without it the monotonicity rows would speak about a
non-physical parameter region, and `h.s1Decay_pos` together with `h.kISC_nonneg` is exactly what
supplies `0 < kF + kIC` for the `phiP` half (the S₁→T₁ branch `kISC / (kISC + (kF + kIC))` is
strictly increasing only when `kF + kIC > 0`; at `kF = kIC = 0` the branch is pinned at `1`).
No premise was added, dropped or weakened relative to the frozen authority.

Measured tactic boundary (this module, mathlib v4.17.0): the `ring` tactic does **not** unfold the
opaque definition `s1Decay`, so each auxiliary row below spells the unfolding as `rw [s1Decay]`
(or `unfold s1Decay`) before `ring`. Measured here: `ring` on a goal containing
`s1Decay kF kISC kIC * kNR` leaves the goal open, while the same goal after `rw [s1Decay]` closes.

Statement authority: every theorem signature below is taken word for word from
`theories/FluorPhos/probes/FluorPhos-statement-skeleton.lean` (the frozen Phase-1 authority,
sha256 `2aa08f1c153b6494c09fd9848c76644ab0b7a59c2a3f46d32a25db7a8d3223bb`, 29 declarations),
which transcribes `theories/FluorPhos/plan.md` §4; fidelity is checked by
`python3 theories/BEP/probes/bep-fidelity.py --theory FluorPhos`. The only departure from the
authority text is the proof bodies, which the authority leaves unfinished on purpose (Phase 1).

There is no unproved placeholder and no custom axiomatic declaration in this file. Note: the two
keyword literals that `proofs/scripts/check.sh --strict` scans for are deliberately not spelled
out anywhere in this file — the scan covers `PhotoLean/**/*.lean` including block comments, so
writing them (even in prose) would be a false-positive FAIL.

Plan locus: `theories/FluorPhos/plan.md` §4 (FP-C rows), §5 (proof routes), sprint FP2; board
`theories/FluorPhos/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.FluorPhos.Criterion
    proofs/scripts/check.sh --strict PhotoLean.FluorPhos.Criterion
    proofs/scripts/axioms.sh PhotoLean.FluorPhos.Criterion PhotoLean.FluorPhos.crossover_isc
-/
import PhotoLean.FluorPhos.Basic

set_option autoImplicit false

namespace PhotoLean

namespace FluorPhos

/-! ## FP2 — law layer -/

/-- Auxiliary normal form: `phiF` written over the common denominator `s1Decay · (kP + kNR)`.
Arithmetic the vocabulary of this module needs, not a statement of the authority. -/
private theorem phiF_common {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR) :
    phiF kF kISC kIC = kF * (kP + kNR) / (s1Decay kF kISC kIC * (kP + kNR)) := by
  have hs : s1Decay kF kISC kIC ≠ 0 := ne_of_gt h.s1Decay_pos
  have ht : kP + kNR ≠ 0 := ne_of_gt h.t1Decay_pos
  unfold phiF
  field_simp
  ring

/-- Auxiliary normal form of the exhaustion sum: both yields over the common denominator
`s1Decay · (kP + kNR)`, with numerator `kISC·kP + kF·(kP + kNR)`. Not a statement of the
authority; the FP-C3/FP-C4 rows consume it. -/
private theorem add_common {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR) :
    phiF kF kISC kIC + phiP kF kISC kIC kP kNR =
      (kISC * kP + kF * (kP + kNR)) /
        (s1Decay kF kISC kIC * (kP + kNR)) := by
  have hs : s1Decay kF kISC kIC ≠ 0 := ne_of_gt h.s1Decay_pos
  have ht : kP + kNR ≠ 0 := ne_of_gt h.t1Decay_pos
  have hP : phiP kF kISC kIC kP kNR = kISC * kP / (s1Decay kF kISC kIC * (kP + kNR)) := by
    unfold phiP iscBranch t1BranchP
    field_simp
    ring
  have hF : kF / s1Decay kF kISC kIC
      = kF * (kP + kNR) / (s1Decay kF kISC kIC * (kP + kNR)) := by
    field_simp
    ring
  unfold phiF
  rw [hF, hP, div_add_div_same]
  congr 1
  ring

/-- Auxiliary arithmetic for the corrected FP-C4 boundary: the defect of the exhaustion numerator
from the common denominator is the nonnegative quantity `kIC·(kP+kNR) + kISC·kNR`. This is the
identity behind the design-time correction (plan §3.1 entry 0) — with `kISC = 0` the triplet is
never populated, so only `kIC` can leak. Not a statement of the authority. -/
private theorem exhaust_residue {kF kISC kIC kP kNR : ℝ}
    (_h : FPData kF kISC kIC kP kNR) :
    s1Decay kF kISC kIC * (kP + kNR) - (kISC * kP + kF * (kP + kNR))
      = kIC * (kP + kNR) + kISC * kNR := by
  rw [s1Decay]
  ring

/-- Auxiliary arithmetic for the corrected FP-C4 boundary: the exhaustion numerator reaches the
common denominator exactly at the nonnegativity split. Not a statement of the authority. -/
private theorem exhaust_zero_iff {kF kISC kIC kP kNR : ℝ}
    (h : FPData kF kISC kIC kP kNR) :
    (kISC * kP + kF * (kP + kNR) = s1Decay kF kISC kIC * (kP + kNR))
      ↔ kIC = 0 ∧ (kISC = 0 ∨ kNR = 0) := by
  have hkN : 0 < kP + kNR := h.t1Decay_pos
  have hres := exhaust_residue h
  have h1 : 0 ≤ kISC * kNR := mul_nonneg h.kISC_nonneg h.kNR_nonneg
  have h2 : 0 ≤ kIC * (kP + kNR) := mul_nonneg h.kIC_nonneg (le_of_lt hkN)
  constructor
  · intro heq
    have hzero : kIC * (kP + kNR) + kISC * kNR = 0 := by
      rw [← hres]
      linarith
    have hIK : kIC * (kP + kNR) = 0 := by linarith
    have hIS : kISC * kNR = 0 := by linarith
    exact ⟨(mul_eq_zero.mp hIK).resolve_right (ne_of_gt hkN), mul_eq_zero.mp hIS⟩
  · rintro ⟨hkIC, h5 | h5⟩
    · have h0 : (0 : ℝ) = kIC * (kP + kNR) + kISC * kNR := by
        rw [hkIC, h5]
        ring
      linarith
    · have h0 : (0 : ℝ) = kIC * (kP + kNR) + kISC * kNR := by
        rw [hkIC, h5]
        ring
      linarith

/-- Plan §4, FP-C1. The phosphorescence yield as a single fraction. Route: `field_simp` + `ring`.
-/
theorem phiP_eq {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR) :
    phiP kF kISC kIC kP kNR = kISC * kP / (s1Decay kF kISC kIC * (kP + kNR)) := by
  have hs : s1Decay kF kISC kIC ≠ 0 := ne_of_gt h.s1Decay_pos
  have ht : kP + kNR ≠ 0 := ne_of_gt h.t1Decay_pos
  unfold phiP iscBranch t1BranchP
  field_simp

/-- Plan §4, FP-C2. **The competition law**: the phosphorescence-to-fluorescence ratio is the
intersystem-crossing odds times the triplet radiative branch. Route: `field_simp` + `ring`. -/
theorem phiP_div_phiF {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR)
    (hkF : 0 < kF) :
    phiP kF kISC kIC kP kNR / phiF kF kISC kIC = (kISC / kF) * t1BranchP kP kNR := by
  have hs : s1Decay kF kISC kIC ≠ 0 := ne_of_gt h.s1Decay_pos
  have ht : kP + kNR ≠ 0 := ne_of_gt h.t1Decay_pos
  have hkF' : kF ≠ 0 := ne_of_gt hkF
  unfold phiP phiF iscBranch t1BranchP
  field_simp
  ring

/-- Plan §4, FP-C3. The two luminescence yields never exceed unity in total. Route:
`div_add_div` normal form, `div_le_one`, the nonnegativity fields of `FPData`. -/
theorem phiF_add_phiP_le_one {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR) :
    phiF kF kISC kIC + phiP kF kISC kIC kP kNR ≤ 1 := by
  have hd0 : 0 < s1Decay kF kISC kIC * (kP + kNR) := mul_pos h.s1Decay_pos h.t1Decay_pos
  have hres := exhaust_residue h
  have hnn : 0 ≤ kIC * (kP + kNR) + kISC * kNR :=
    add_nonneg (mul_nonneg h.kIC_nonneg (le_of_lt h.t1Decay_pos))
      (mul_nonneg h.kISC_nonneg h.kNR_nonneg)
  have hlex : kISC * kP + kF * (kP + kNR) ≤ s1Decay kF kISC kIC * (kP + kNR) := by
    have h1 : 0 ≤ kISC * kNR := mul_nonneg h.kISC_nonneg h.kNR_nonneg
    have h2 : 0 ≤ kIC * (kP + kNR) := mul_nonneg h.kIC_nonneg (le_of_lt h.t1Decay_pos)
    linarith
  rw [add_common h]
  exact (div_le_one hd0).mpr hlex

/-- Plan §4, FP-C4 (corrected at design time — plan §3.1 entry 0). **The losslessness
boundary**: the two yields exhaust unity exactly when there is no S₁ internal-conversion loss
and the triplet is either never populated or perfectly radiative. Route: the numerator identity
`phiF + phiP = 1 ↔ kISC·kNR + kIC·(kP+kNR) = 0` under the bundle, then the nonnegativity split
and `h.t1Decay_pos`. -/
theorem phiF_add_phiP_eq_one_iff {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR) :
    phiF kF kISC kIC + phiP kF kISC kIC kP kNR = 1 ↔ kIC = 0 ∧ (kISC = 0 ∨ kNR = 0) := by
  have hd0 : 0 < s1Decay kF kISC kIC * (kP + kNR) := mul_pos h.s1Decay_pos h.t1Decay_pos
  have hd : s1Decay kF kISC kIC * (kP + kNR) ≠ 0 := ne_of_gt hd0
  rw [add_common h]
  rw [show (kISC * kP + kF * (kP + kNR)) / (s1Decay kF kISC kIC * (kP + kNR)) = 1
      ↔ kISC * kP + kF * (kP + kNR) = s1Decay kF kISC kIC * (kP + kNR) from
    div_eq_one_iff_eq hd]
  exact exhaust_zero_iff h

/-- Plan §4, FP-C5 (first half). The heavy-atom direction on fluorescence: more intersystem
crossing, less fluorescence. Route: `div_lt_div_of_lt_...` on the denominator / `div_lt_iff`
chain with `h.s1Decay_pos` and the primed bundle. -/
theorem phiF_strictAnti_isc {kF kISC kISC' kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR)
    (h' : FPData kF kISC' kIC kP kNR) (hkF : 0 < kF) (hlt : kISC < kISC') :
    phiF kF kISC' kIC < phiF kF kISC kIC := by
  have hs : 0 < s1Decay kF kISC kIC := h.s1Decay_pos
  have hs' : 0 < s1Decay kF kISC' kIC := h'.s1Decay_pos
  have hden : s1Decay kF kISC kIC < s1Decay kF kISC' kIC := by
    rw [s1Decay, s1Decay]
    linarith
  unfold phiF
  rw [div_lt_div_iff₀ hs' hs]
  nlinarith [mul_lt_mul_of_pos_left hden hkF]

/-- Plan §4, FP-C5 (second half). The heavy-atom direction on phosphorescence: more intersystem
crossing, more phosphorescence. Route: `phiP_eq` both sides, then `div_lt_div_iff` with the
positivity fields. -/
theorem phiP_strictMono_isc {kF kISC kISC' kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR)
    (h' : FPData kF kISC' kIC kP kNR) (hkP : 0 < kP) (hlt : kISC < kISC') :
    phiP kF kISC kIC kP kNR < phiP kF kISC' kIC kP kNR := by
  have hs : 0 < s1Decay kF kISC kIC := h.s1Decay_pos
  have hs' : 0 < s1Decay kF kISC' kIC := h'.s1Decay_pos
  have ht : 0 < kP + kNR := h.t1Decay_pos
  have hden : 0 < s1Decay kF kISC kIC * (kP + kNR) := mul_pos hs ht
  have hden' : 0 < s1Decay kF kISC' kIC * (kP + kNR) := mul_pos hs' ht
  have hs1 : 0 < kF + kISC + kIC := by
    have hsc : s1Decay kF kISC kIC = kF + kISC + kIC := rfl
    rwa [hsc] at hs
  have hposISC : 0 < kISC := lt_of_le_of_lt h.kISC_nonneg hlt
  have hgate : 0 < kISC + kISC' - kF - kIC := by
    by_contra hle
    push_neg at hle
    have h2 : 2 * kISC < kF + kIC := by linarith
    have h3 : 4 * (kISC * kISC) < (kF + kIC) * (kF + kIC) := by nlinarith
    have h4 : kISC * kISC < (kF + kIC) * kISC := by nlinarith
    nlinarith [mul_pos hs1 hposISC]
  have hkey : kISC' * kP * ((kF + kISC' + kIC) * (kP + kNR))
      = kISC * kP * ((kF + kISC + kIC) * (kP + kNR))
        + (kISC' - kISC) * (kISC + kISC' - kF - kIC) * kP * (kP + kNR) := by
    ring
  have h1 : 0 < kISC' - kISC := by linarith
  have hpos : 0 < (kISC' - kISC) * (kISC + kISC' - kF - kIC) * kP * (kP + kNR) :=
    mul_pos (mul_pos (mul_pos h1 hgate) hkP) ht
  rw [phiP_eq h, phiP_eq h']
  rw [show kISC * kP / (s1Decay kF kISC kIC * (kP + kNR))
        < kISC' * kP / (s1Decay kF kISC' kIC * (kP + kNR))
      ↔ (kISC * kP) * (s1Decay kF kISC' kIC * (kP + kNR))
        < (kISC' * kP) * (s1Decay kF kISC kIC * (kP + kNR)) from
    div_lt_div_iff₀ (a := kISC * kP) (b := s1Decay kF kISC kIC * (kP + kNR))
      (c := kISC' * kP) (d := s1Decay kF kISC' kIC * (kP + kNR)) hden hden']
  rw [show s1Decay kF kISC kIC = kF + kISC + kIC from rfl,
    show s1Decay kF kISC' kIC = kF + kISC' + kIC from rfl]
  linarith

/-- Plan §4, FP-C6. **The crossover in closed form**: phosphorescence overtakes fluorescence
exactly when `kISC·kP` exceeds `kF·(kP+kNR)`. Route: `div_lt_div_iff` chains with
`h.s1Decay_pos`, `h.t1Decay_pos`, `hkF`, `hkP`. -/
theorem crossover_isc {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR)
    (hkF : 0 < kF) (hkP : 0 < kP) :
    phiF kF kISC kIC < phiP kF kISC kIC kP kNR ↔ kF * (kP + kNR) < kISC * kP := by
  have hs : 0 < s1Decay kF kISC kIC := h.s1Decay_pos
  have ht : 0 < kP + kNR := h.t1Decay_pos
  have hd0 : 0 < s1Decay kF kISC kIC * (kP + kNR) := mul_pos hs ht
  rw [phiF_common h, phiP_eq h]
  rw [show kF * (kP + kNR) / (s1Decay kF kISC kIC * (kP + kNR))
        < kISC * kP / (s1Decay kF kISC kIC * (kP + kNR))
      ↔ (kF * (kP + kNR)) * (s1Decay kF kISC kIC * (kP + kNR))
        < (kISC * kP) * (s1Decay kF kISC kIC * (kP + kNR)) from
    div_lt_div_iff₀ hd0 hd0]
  exact mul_lt_mul_iff_of_pos_right hd0

/-- Plan §4, FP-C6 (threshold form). The same crossover solved for `kISC`. Route: FP-C6's
statement divided through by `kP` (`lt_div_iff` with `hkP`). -/
theorem crossover_isc_threshold {kF kISC kIC kP kNR : ℝ} (h : FPData kF kISC kIC kP kNR)
    (hkF : 0 < kF) (hkP : 0 < kP) :
    phiF kF kISC kIC < phiP kF kISC kIC kP kNR ↔ kF * (kP + kNR) / kP < kISC := by
  rw [crossover_isc h hkF hkP]
  constructor
  · intro hlt
    rw [div_lt_iff₀ hkP]
    linarith
  · intro hlt
    rw [div_lt_iff₀ hkP] at hlt
    linarith

/-- Plan §4, FP-C7. **The El-Sayed boundary as a model row**: with the intersystem channel shut
there is no phosphorescence, whatever the triplet rates. Route: `iscBranch` vanishes at
`kISC = 0` (`zero_div`). -/
theorem hso_zero_no_phosphorescence {kF kIC kP kNR : ℝ} (h : FPData kF 0 kIC kP kNR) :
    phiP kF 0 kIC kP kNR = 0 := by
  unfold phiP iscBranch
  rw [zero_div, zero_mul]

/-- Plan §4, FP-C8. **Non-vacuity of the competition**: both channels live at a concrete
witness (`kF = kISC = kP = 1`, `kIC = kNR = 1`: `phiF = 1/3`, `phiP = 1/6`). The triple
conjunct blocks the trivial-witness failure mode (the M1 lesson). Route: `refine ⟨1, 1, 1, 1,
1, ?_, ?_, ?_⟩` with `norm_num [FPData, phiF, phiP, ...]` verdicts. -/
theorem nonvacuous_competition :
    ∃ kF kISC kIC kP kNR : ℝ, FPData kF kISC kIC kP kNR ∧
      0 < phiF kF kISC kIC ∧ 0 < phiP kF kISC kIC kP kNR := by
  refine ⟨1, 1, 1, 1, 1, ?_, ?_, ?_⟩
  · constructor <;> norm_num [s1Decay]
  · norm_num [phiF, s1Decay]
  · norm_num [phiP, iscBranch, t1BranchP, s1Decay]

end FluorPhos

end PhotoLean
