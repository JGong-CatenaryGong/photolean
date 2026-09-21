/-
  PhotoLean — PhotoLean/Goldschmidt/Basic.lean

  The Goldschmidt theory, milestone G1 (the description layer): the Goldschmidt tolerance factor of
  the ideal cubic `ABO₃` perovskite, the ideal-packing identification, the band verdict and the
  three-way zone classifier.

  Design of record: `theories/goldschmidt/plan.md` §1–§4 (symbol table §2, honesty table §12).
  Statement authority: `theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean` §G1, which
  every signature below matches word for word (checked by
  `python3 theories/BEP/probes/bep-fidelity.py --theory goldschmidt --milestone G1`).

  Every physical premise is an explicit hypothesis — positivity of `rB + rO`, positivity of
  `rA + rO`, non-emptiness of the band — and none of them is hidden inside a definition (engine
  iron rule 3).

  Authority defect found and corrected on 2026-09-21: the first draft of the row
  `goldschmidtZone_eq_tooLarge_iff` read `goldschmidtZone lo hi t = GoldschmidtZone.tooLarge ↔
  hi < t`, which is FALSE for an inverted band. The classifier tests `t < lo` first, so at
  `lo = 1`, `hi = 0`, `t = 1/2` the first branch fires and the factor is classified `tooSmall`,
  while `hi < t` holds — the biconditional is false there (kernel-checked counterexample, reported
  by prover_b and accepted by the lead). The authority now declares the exact unconditional row
  `↔ lo ≤ t ∧ hi < t` plus the `lo ≤ hi` corollary; the correction is recorded in plan §3.1 item 4.
-/
import Mathlib

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Goldschmidt

/-! ## G1 — description layer (`PhotoLean/Goldschmidt/Basic.lean`) -/

/-- Goldschmidt tolerance factor of the ideal cubic `ABO₃` perovskite: the A–O contact distance in
units of the ideal cuboctahedral A–O distance `√2 * (rB + rO)` (plan §1.2, §2). -/
noncomputable def tolFac (rA rB rO : ℝ) : ℝ := (rA + rO) / (Real.sqrt 2 * (rB + rO))

/-- Cubic lattice parameter fixed by the B–O contact: `a = 2 * (rB + rO)` (plan §2). -/
noncomputable def latticeOf (rB rO : ℝ) : ℝ := 2 * (rB + rO)

/-- Ideal A–O distance of the cubic perovskite: `a / √2 = √2 * (rB + rO)` (plan §2). -/
noncomputable def idealAO (rB rO : ℝ) : ℝ := Real.sqrt 2 * (rB + rO)

/-- A-site radius giving the ideal packing `t = 1`: `√2 * (rB + rO) - rO` (plan §2). -/
noncomputable def idealA (rB rO : ℝ) : ℝ := idealAO rB rO - rO

/-- Lower window edge of the band verdict: the A radius at which `t = lo` (plan §2, consumed by the
radius-window equivalence of §6). -/
noncomputable def rAMin (lo rB rO : ℝ) : ℝ := lo * Real.sqrt 2 * (rB + rO) - rO

/-- Upper window edge of the band verdict: the A radius at which `t = hi` (plan §2, consumed by the
radius-window equivalence of §6). -/
noncomputable def rAMax (hi rB rO : ℝ) : ℝ := hi * Real.sqrt 2 * (rB + rO) - rO

/-- Band predicate on the factor itself (plan §2). -/
def InBand (lo hi t : ℝ) : Prop := lo ≤ t ∧ t ≤ hi

/-- The band verdict for a perovskite triple: the tolerance factor lies in the band `[lo, hi]`.
The band edges are parameters, so the literature's several conventions are instances (plan §1.2,
§2). -/
def GoldschmidtConforms (lo hi rA rB rO : ℝ) : Prop := InBand lo hi (tolFac rA rB rO)

/-- Three-way Goldschmidt classification of a tolerance factor against a band (plan §2). -/
inductive GoldschmidtZone where
  | tooSmall
  | ideal
  | tooLarge
  deriving DecidableEq

/-- Computable three-way classifier: `t < lo` is too small, `t ≤ hi` is ideal, otherwise too large
(plan §2). -/
noncomputable def goldschmidtZone (lo hi t : ℝ) : GoldschmidtZone :=
  if t < lo then GoldschmidtZone.tooSmall
  else if t ≤ hi then GoldschmidtZone.ideal
  else GoldschmidtZone.tooLarge

/-- A–O rattling gap: the signed excess of the ideal A–O distance over the actual one (plan §4). -/
noncomputable def gapA (rA rB rO : ℝ) : ℝ := idealAO rB rO - (rA + rO)

/-- Lower edge of the literature's classic cubic band (`0.8 ≤ t`); the constant is an *instance* of
the band parameter, never hard-coded into a statement (plan §1.2, §2). -/
noncomputable def classicLo : ℝ := 4 / 5

/-- Upper edge of the literature's classic cubic band (`t ≤ 1`) (plan §2). -/
def classicHi : ℝ := 1

/-- Upper edge of the tetragonally distorted band (`t ≤ 1.1`) (plan §2, exercised by the G6 band-flip
row). -/
noncomputable def tetragonalHi : ℝ := 11 / 10

/-- The printed "15 %" radius figure of Goldschmidt's radius rule (plan §2, consumed by G2 and G4). -/
noncomputable def tauGoldschmidt : ℝ := 3 / 20

/-- Positivity of the tolerance factor, from the two explicit physical premises `0 < rB + rO` and
`0 < rA + rO` (plan §4). -/
theorem tolFac_pos {rA rB rO : ℝ} (hB : 0 < rB + rO) (hA : 0 < rA + rO) :
    0 < tolFac rA rB rO := by
  unfold tolFac
  exact div_pos hA (mul_pos (Real.sqrt_pos_of_pos (by norm_num)) hB)

/-- `2 / √2 = √2`: mathlib's `Real.div_sqrt` is unconditional and closes this in one step
(plan §4, risk item §11). -/
theorem two_div_sqrtTwo : 2 / Real.sqrt 2 = Real.sqrt 2 := Real.div_sqrt

/-- The B–O contact fixes the lattice parameter: `latticeOf rB rO / √2 = idealAO rB rO`, i.e. the
ideal A–O distance is `a / √2` (plan §2, §4). -/
theorem latticeOf_div_sqrtTwo (rB rO : ℝ) : latticeOf rB rO / Real.sqrt 2 = idealAO rB rO := by
  have h : latticeOf rB rO / Real.sqrt 2 = (2 / Real.sqrt 2) * (rB + rO) := by
    unfold latticeOf
    ring
  rw [h, two_div_sqrtTwo]
  unfold idealAO
  ring

/-- The geometric reading of the factor: `t` is the ratio of the actual A–O contact distance to the
ideal cuboctahedral one (plan §1.1, §12 row 2). -/
theorem tolFac_eq_distRatio (rA rB rO : ℝ) :
    tolFac rA rB rO = (rA + rO) / (latticeOf rB rO / Real.sqrt 2) := by
  rw [latticeOf_div_sqrtTwo]
  unfold tolFac idealAO
  ring

/-- Ideal packing `t = 1` is exactly the A–O contact equation `rA + rO = idealAO rB rO` (plan §1.2,
§4): divide by the positive denominator. -/
theorem contact_iff_tolFac_one {rA rB rO : ℝ} (h : 0 < rB + rO) :
    rA + rO = idealAO rB rO ↔ tolFac rA rB rO = 1 := by
  unfold tolFac idealAO
  rw [div_eq_one_iff_eq
    (mul_ne_zero ((Real.sqrt_ne_zero').mpr (by norm_num : (0 : ℝ) < 2)) h.ne')]

/-- The ideal A radius in linear form, the shape used by the radius-window rows of §6 (plan §4). -/
theorem idealA_eq (rB rO : ℝ) : idealA rB rO = Real.sqrt 2 * rB + (Real.sqrt 2 - 1) * rO := by
  unfold idealA idealAO
  ring

/-- The defining property of the ideal A radius: it makes the tolerance factor exactly one
(plan §4, §12 row 3). -/
theorem idealA_tolFac {rB rO : ℝ} (h : 0 < rB + rO) : tolFac (idealA rB rO) rB rO = 1 := by
  rw [← contact_iff_tolFac_one h]
  unfold idealA
  ring

/-- The rattling gap is positive exactly when the factor is below the ideal value (plan §4). -/
theorem gapA_pos_iff {rA rB rO : ℝ} (h : 0 < rB + rO) :
    0 < gapA rA rB rO ↔ tolFac rA rB rO < 1 := by
  unfold gapA tolFac idealAO
  rw [div_lt_one (mul_pos (Real.sqrt_pos_of_pos (by norm_num)) h)]
  constructor <;> intro hh <;> linarith

/-- Classifier row 1: `tooSmall` is exactly the first branch condition `t < lo`; the other two
branches yield the distinct constructors `ideal` / `tooLarge` (plan §4). -/
theorem goldschmidtZone_eq_tooSmall_iff (lo hi t : ℝ) :
    goldschmidtZone lo hi t = GoldschmidtZone.tooSmall ↔ t < lo := by
  unfold goldschmidtZone
  split_ifs with h1 h2
  · exact iff_of_true rfl h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1

/-- Classifier row 2: `ideal` is exactly `lo ≤ t ∧ t ≤ hi`, i.e. the band verdict on the factor
(plan §4). -/
theorem goldschmidtZone_eq_ideal_iff (lo hi t : ℝ) :
    goldschmidtZone lo hi t = GoldschmidtZone.ideal ↔ lo ≤ t ∧ t ≤ hi := by
  unfold goldschmidtZone
  split_ifs with h1 h2
  · exact iff_of_false (by decide) (fun hc => not_le.mpr h1 hc.1)
  · exact iff_of_true rfl ⟨le_of_not_gt h1, h2⟩
  · exact iff_of_false (by decide) (fun hc => h2 hc.2)

/-- Classifier row 3, exact form (the authority row as corrected in plan §3.1 item 4): the
`tooLarge` branch is taken exactly when the first test fails and the second fails too, i.e.
`lo ≤ t ∧ hi < t`. The conjunct `lo ≤ t` cannot be dropped: the classifier tests `t < lo` first, so
for an inverted band `hi < t < lo` the factor is classified `tooSmall`. Kernel counterexample to the
dropped-conjunct form: `lo = 1`, `hi = 0`, `t = 1/2` gives `goldschmidtZone 1 0 (1/2) =
GoldschmidtZone.tooSmall` while `hi < t` holds. -/
theorem goldschmidtZone_eq_tooLarge_iff (lo hi t : ℝ) :
    goldschmidtZone lo hi t = GoldschmidtZone.tooLarge ↔ lo ≤ t ∧ hi < t := by
  unfold goldschmidtZone
  split_ifs with h1 h2
  · exact iff_of_false (by decide) (fun hc => not_le.mpr h1 hc.1)
  · exact iff_of_false (by decide) (fun hc => not_lt.mpr h2 hc.2)
  · exact iff_of_true rfl ⟨le_of_not_gt h1, not_le.mp h2⟩

/-- Classifier row 3 for a non-empty band: under the explicit physical premise `lo ≤ hi` (plan §2
lists band non-emptiness among the standing hypotheses) the exact form collapses to `hi < t`. The
premise is load-bearing — without it the statement is the `lo = 1, hi = 0, t = 1/2` counterexample
(plan §3.1 item 4, and the docstring of `goldschmidtZone_eq_tooLarge_iff`). -/
theorem goldschmidtZone_eq_tooLarge_iff_of_band (lo hi t : ℝ) (h : lo ≤ hi) :
    goldschmidtZone lo hi t = GoldschmidtZone.tooLarge ↔ hi < t := by
  unfold goldschmidtZone
  split_ifs with h1 h2
  · exact iff_of_false (by decide) (not_lt.mpr (le_trans (le_of_lt h1) h))
  · exact iff_of_false (by decide) (not_lt.mpr h2)
  · exact iff_of_true rfl (not_le.mp h2)

/-- The bottom of the radius window at the classic upper edge `lo = 1` is the ideal A radius
(plan §4). -/
theorem rAMin_one (rB rO : ℝ) : rAMin 1 rB rO = idealA rB rO := by
  unfold rAMin idealA idealAO
  ring

/-- The top of the radius window at `hi = 1` is the same ideal A radius: unit band edge means ideal
packing (plan §4). -/
theorem rAMax_one (rB rO : ℝ) : rAMax 1 rB rO = idealA rB rO := by
  unfold rAMax idealA idealAO
  ring

end Goldschmidt

end PhotoLean
