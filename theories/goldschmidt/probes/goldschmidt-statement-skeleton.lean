/-
Statement skeleton for the Goldschmidt theory (the Goldschmidt tolerance factor and Goldschmidt's
rules of ionic substitution) — the **authority for all delivered signatures** of
`PhotoLean/Goldschmidt/*.lean`. Every delivered declaration must match the corresponding signature
here word for word (the mechanical check is
`theories/BEP/probes/bep-fidelity.py --theory goldschmidt`, which is theory-generic). It lives under
`theories/goldschmidt/probes/`, i.e. OUTSIDE `SOURCE_DIRS` (`PhotoLean`), because the source tree has
zero tolerance for the unfinished-proof placeholder keyword; statement-first requires the signatures
to elaborate before any proof work starts. 0 error is the Sprint-0 gate.

Model (plan §1.2). The ideal cubic `ABO₃` perovskite is described by three ionic radii. The B cation
touches its six face-centred oxygens (`r_B + r_O = a/2`, `a` the cubic lattice parameter) and the A
cation sits in the cuboctahedral cage with A–O distance `a/√2`; the ratio of the A–O contact distance
to that ideal distance is the tolerance factor

  tolFac rA rB rO = (rA + rO) / (√2 * (rB + rO))        -- with latticeOf rB rO = 2 * (rB + rO)
  idealAO rB rO   = √2 * (rB + rO)                     -- the ideal A–O distance `a/√2`
  idealA  rB rO   = idealAO rB rO - rO                 -- the A radius giving `t = 1`

`GoldschmidtConforms lo hi rA rB rO` is the band verdict (`lo ≤ t ≤ hi`); the band edges are
**parameters** so that the literature's several conventions (`4/5`–`1`, `1`–`11/10`, symmetric
`1 ± δ`) are instances of one definition rather than hard-coded constants. `GoldschmidtZone` /
`goldschmidtZone` classify the factor three-way (`tooSmall`/`ideal`/`tooLarge`).

Goldschmidt's rules of ionic substitution are the predicates `RadiusMatch τ r r'` (the radius rule,
`|r - r'| ≤ τ * r`, with `τ = 3/20` the printed "15 %" figure), `ChargeBalanced dz` (the charge rule:
the substitution set's integer charge increments sum to zero — single-site balance is exactly the
isovalent case) and `Substitutable tol₀ k χ χ' r r'` (the chemical rule: the tolerance is dressed by
the electronegativity difference, `chiTol`; only its monotonicity in `|Δχ|` is a theorem, the linear
shape is a declared modelling choice).

The `√2`-free decision layer lives in the `Rat` sub-namespace: `tolFacSq` is `t²` (rational at
rational radii) and `inBandQ` is the squared band criterion; `inBandQ_cast` is the theorem that the
rational decision reproduces the real verdict. Every physical premise is an explicit hypothesis —
nothing is hidden in a definition (engine rule 3).

Provenance of the rows below: `theories/goldschmidt/plan.md` §4 (G1), §5 (G2), §6 (G3), §7 (G4),
§8 (G5), §9 (G6); each delivered docstring carries its plan locus. The literature rows of §G6 are
appended when `theories/goldschmidt/LITERATURE.md` round 1 lands the printed radii (the append is
recorded in the plan's statement-correction log).
-/
import Mathlib

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Goldschmidt

/-! ## G1 — description layer (`PhotoLean/Goldschmidt/Basic.lean`) -/

/-- Goldschmidt tolerance factor of the ideal cubic `ABO₃` perovskite: the A–O contact distance in
units of the ideal cuboctahedral A–O distance `√2 * (rB + rO)`. -/
noncomputable def tolFac (rA rB rO : ℝ) : ℝ := (rA + rO) / (Real.sqrt 2 * (rB + rO))

/-- Cubic lattice parameter fixed by the B–O contact: `a = 2 * (rB + rO)`. -/
noncomputable def latticeOf (rB rO : ℝ) : ℝ := 2 * (rB + rO)

/-- Ideal A–O distance of the cubic perovskite: `a / √2 = √2 * (rB + rO)`. -/
noncomputable def idealAO (rB rO : ℝ) : ℝ := Real.sqrt 2 * (rB + rO)

/-- A-site radius giving the ideal packing `t = 1`: `√2 * (rB + rO) - rO`. -/
noncomputable def idealA (rB rO : ℝ) : ℝ := idealAO rB rO - rO

/-- Lower window edge of the band verdict: the A radius at which `t = lo`. -/
noncomputable def rAMin (lo rB rO : ℝ) : ℝ := lo * Real.sqrt 2 * (rB + rO) - rO

/-- Upper window edge of the band verdict: the A radius at which `t = hi`. -/
noncomputable def rAMax (hi rB rO : ℝ) : ℝ := hi * Real.sqrt 2 * (rB + rO) - rO

/-- Band predicate on the factor itself. -/
def InBand (lo hi t : ℝ) : Prop := lo ≤ t ∧ t ≤ hi

/-- The band verdict for a perovskite triple: the tolerance factor lies in the band `[lo, hi]`. -/
def GoldschmidtConforms (lo hi rA rB rO : ℝ) : Prop := InBand lo hi (tolFac rA rB rO)

/-- Three-way Goldschmidt classification of a tolerance factor against a band. -/
inductive GoldschmidtZone where
  | tooSmall
  | ideal
  | tooLarge
  deriving DecidableEq

/-- Computable three-way classifier: `t < lo` is too small, `t ≤ hi` is ideal, otherwise too large. -/
noncomputable def goldschmidtZone (lo hi t : ℝ) : GoldschmidtZone :=
  if t < lo then GoldschmidtZone.tooSmall
  else if t ≤ hi then GoldschmidtZone.ideal
  else GoldschmidtZone.tooLarge

/-- A–O rattling gap: the signed excess of the ideal A–O distance over the actual one. -/
noncomputable def gapA (rA rB rO : ℝ) : ℝ := idealAO rB rO - (rA + rO)

/-- Lower edge of the literature's classic cubic band (`0.8 ≤ t`). -/
noncomputable def classicLo : ℝ := 4 / 5

/-- Upper edge of the literature's classic cubic band (`t ≤ 1`). -/
def classicHi : ℝ := 1

/-- Upper edge of the tetragonally distorted band (`t ≤ 1.1`). -/
noncomputable def tetragonalHi : ℝ := 11 / 10

/-- The printed "15 %" radius figure of Goldschmidt's radius rule. -/
noncomputable def tauGoldschmidt : ℝ := 3 / 20

theorem tolFac_pos {rA rB rO : ℝ} (hB : 0 < rB + rO) (hA : 0 < rA + rO) :
    0 < tolFac rA rB rO := by
  sorry

theorem two_div_sqrtTwo : 2 / Real.sqrt 2 = Real.sqrt 2 := by
  sorry

theorem latticeOf_div_sqrtTwo (rB rO : ℝ) : latticeOf rB rO / Real.sqrt 2 = idealAO rB rO := by
  sorry

theorem tolFac_eq_distRatio (rA rB rO : ℝ) :
    tolFac rA rB rO = (rA + rO) / (latticeOf rB rO / Real.sqrt 2) := by
  sorry

theorem contact_iff_tolFac_one {rA rB rO : ℝ} (h : 0 < rB + rO) :
    rA + rO = idealAO rB rO ↔ tolFac rA rB rO = 1 := by
  sorry

theorem idealA_eq (rB rO : ℝ) : idealA rB rO = Real.sqrt 2 * rB + (Real.sqrt 2 - 1) * rO := by
  sorry

theorem idealA_tolFac {rB rO : ℝ} (h : 0 < rB + rO) : tolFac (idealA rB rO) rB rO = 1 := by
  sorry

theorem gapA_pos_iff {rA rB rO : ℝ} (h : 0 < rB + rO) :
    0 < gapA rA rB rO ↔ tolFac rA rB rO < 1 := by
  sorry

theorem goldschmidtZone_eq_tooSmall_iff (lo hi t : ℝ) :
    goldschmidtZone lo hi t = GoldschmidtZone.tooSmall ↔ t < lo := by
  sorry

theorem goldschmidtZone_eq_ideal_iff (lo hi t : ℝ) :
    goldschmidtZone lo hi t = GoldschmidtZone.ideal ↔ lo ≤ t ∧ t ≤ hi := by
  sorry

theorem goldschmidtZone_eq_tooLarge_iff (lo hi t : ℝ) :
    goldschmidtZone lo hi t = GoldschmidtZone.tooLarge ↔ lo ≤ t ∧ hi < t := by
  sorry

theorem goldschmidtZone_eq_tooLarge_iff_of_band (lo hi t : ℝ) (h : lo ≤ hi) :
    goldschmidtZone lo hi t = GoldschmidtZone.tooLarge ↔ hi < t := by
  sorry

theorem rAMin_one (rB rO : ℝ) : rAMin 1 rB rO = idealA rB rO := by
  sorry

theorem rAMax_one (rB rO : ℝ) : rAMax 1 rB rO = idealA rB rO := by
  sorry

/-! ## G2 — rules layer (`PhotoLean/Goldschmidt/Rules.lean`) -/

/-- Goldschmidt's radius rule: `r'` may replace `r` if the radii differ by at most the fraction `τ`
of the reference radius `r`. At `τ = 3/20` this is the printed "15 %" rule. -/
def RadiusMatch (tau r r' : ℝ) : Prop := |r - r'| ≤ tau * r

/-- Electronegativity-dressed radius tolerance: the closer the chemical character (`|χ - χ'|`), the
larger the tolerated radius fraction. The linear shape is a declared modelling choice. -/
noncomputable def chiTol (tol0 k chi chi' : ℝ) : ℝ := tol0 - k * |chi - chi'|

/-- Goldschmidt's chemical rule composed with the radius rule. -/
def Substitutable (tol0 k chi chi' r r' : ℝ) : Prop := RadiusMatch (chiTol tol0 k chi chi') r r'

/-- Goldschmidt's charge rule: the integer charge increments of a substitution set sum to zero. -/
def ChargeBalanced {ι : Type*} [Fintype ι] (dz : ι → ℤ) : Prop := ∑ i, dz i = 0

/-- A single-site substitution with charge increment `dz` is isovalent when that increment vanishes. -/
def isovalent (dz : ℤ) : Prop := dz = 0

theorem radiusMatch_iff_window {tau r r' : ℝ} :
    RadiusMatch tau r r' ↔ (1 - tau) * r ≤ r' ∧ r' ≤ (1 + tau) * r := by
  sorry

theorem radiusMatch_min_iff {tau r r' : ℝ} (htau : 0 ≤ tau) :
    RadiusMatch tau r r' ∧ RadiusMatch tau r' r ↔ |r - r'| ≤ tau * min r r' := by
  sorry

theorem radiusMatch_refl {tau r : ℝ} (htau : 0 ≤ tau) (hr : 0 ≤ r) : RadiusMatch tau r r := by
  sorry

theorem radiusMatch_mono_tau {tau tau' r r' : ℝ} (h : tau ≤ tau') (hr : 0 ≤ r) :
    RadiusMatch tau r r' → RadiusMatch tau' r r' := by
  sorry

theorem radiusMatch_fifteen_window {r r' : ℝ} :
    RadiusMatch (3 / 20) r r' ↔ 17 * r ≤ 20 * r' ∧ 20 * r' ≤ 23 * r := by
  sorry

theorem radiusMatch_comp_ratchet {tau r1 r2 r3 : ℝ} (hr1 : 0 < r1) (htau : 0 ≤ tau)
    (htau1 : tau ≤ 1) : RadiusMatch tau r1 r2 → RadiusMatch tau r2 r3 →
      RadiusMatch ((1 + tau) ^ 2 - 1) r1 r3 := by
  sorry

theorem chargeBalanced_single_iff (dz : ℤ) :
    ChargeBalanced (fun _ : Unit => dz) ↔ dz = 0 := by
  sorry

theorem chargeBalanced_pair_iff (dz : Bool → ℤ) :
    ChargeBalanced dz ↔ dz false + dz true = 0 := by
  sorry

theorem exists_negative_of_pos {ι : Type*} [Fintype ι] {dz : ι → ℤ} (h : ChargeBalanced dz)
    (hpos : ∃ i, 0 < dz i) : ∃ j, dz j < 0 := by
  sorry

theorem exists_compensating_partner {ι : Type*} [Fintype ι] {dz : ι → ℤ} (h : ChargeBalanced dz)
    {i : ι} (hi : 0 < dz i) : ∃ j, j ≠ i ∧ dz j < 0 := by
  sorry

theorem chiTol_anti {tol0 k chi chi' chi'' : ℝ} (hk : 0 ≤ k) (h : |chi' - chi| ≤ |chi'' - chi|) :
    chiTol tol0 k chi chi'' ≤ chiTol tol0 k chi chi' := by
  sorry

theorem substitutable_mono_chi {tol0 k chi chi' chi'' r r' : ℝ} (hk : 0 ≤ k) (hr : 0 ≤ r)
    (h : |chi'' - chi| ≤ |chi' - chi|) :
    Substitutable tol0 k chi chi' r r' → Substitutable tol0 k chi chi'' r r' := by
  sorry

theorem substitutable_iff_window {tol0 k chi chi' r r' : ℝ} :
    Substitutable tol0 k chi chi' r r' ↔
      (1 - chiTol tol0 k chi chi') * r ≤ r' ∧ r' ≤ (1 + chiTol tol0 k chi chi') * r := by
  sorry

/-! ## G3 — law layer (`PhotoLean/Goldschmidt/Criterion.lean`) -/

theorem tolFac_strictMono_rA {rA rA' rB rO : ℝ} (h : 0 < rB + rO) (hlt : rA < rA') :
    tolFac rA rB rO < tolFac rA' rB rO := by
  sorry

theorem tolFac_strictAnti_rB {rA rB rB' rO : ℝ} (h : 0 < rB + rO) (hA : 0 < rA + rO)
    (hlt : rB < rB') : tolFac rA rB' rO < tolFac rA rB rO := by
  sorry

theorem tolFac_mono_rO_of_lt {rA rB rO rO' : ℝ} (hB : 0 < rB + rO) (h : rA < rB)
    (hlt : rO < rO') : tolFac rA rB rO < tolFac rA rB rO' := by
  sorry

theorem tolFac_anti_rO_of_lt {rA rB rO rO' : ℝ} (hB : 0 < rB + rO) (h : rB < rA)
    (hlt : rO < rO') : tolFac rA rB rO' < tolFac rA rB rO := by
  sorry

theorem tolFac_rO_const_iff {rA rB rO : ℝ} (hrB : 0 ≤ rB) (hrO : 0 < rO) :
    (∀ rO' : ℝ, 0 < rO' → tolFac rA rB rO' = tolFac rA rB rO) ↔ rA = rB := by
  sorry

theorem tolFac_eq_invSqrtTwo_iff {rA rB rO : ℝ} (h : 0 < rB + rO) :
    tolFac rA rB rO = 1 / Real.sqrt 2 ↔ rA = rB := by
  sorry

theorem tolFac_scale_invariance {c rA rB rO : ℝ} (hc : c ≠ 0) :
    tolFac (c * rA) (c * rB) (c * rO) = tolFac rA rB rO := by
  sorry

theorem tolFac_ratio_form {rA rB rO : ℝ} (hrO : rO ≠ 0) :
    tolFac rA rB rO = (rA / rO + 1) / (Real.sqrt 2 * (rB / rO + 1)) := by
  sorry

theorem tolFac_shift (rA rB rO d : ℝ) :
    tolFac (rA + d) rB rO - tolFac rA rB rO = d / (Real.sqrt 2 * (rB + rO)) := by
  sorry

theorem tolFac_abs_shift_eq {rA rB rO d : ℝ} (h : 0 < rB + rO) :
    |tolFac (rA + d) rB rO - tolFac rA rB rO| = |d| / (Real.sqrt 2 * (rB + rO)) := by
  sorry

theorem conforms_at_idealA_iff {lo hi rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms lo hi (idealA rB rO) rB rO ↔ lo ≤ 1 ∧ 1 ≤ hi := by
  sorry

theorem conforms_iff_ideal_packing {rA rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms 1 1 rA rB rO ↔ rA + rO = idealAO rB rO := by
  sorry

theorem conforms_iff_radius_window {lo hi rA rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms lo hi rA rB rO ↔ rAMin lo rB rO ≤ rA ∧ rA ≤ rAMax hi rB rO := by
  sorry

theorem rAMin_le_iff_sq {lo rA rB rO : ℝ} (hlo : 0 ≤ lo) (h : 0 < rB + rO) (hA : 0 ≤ rA + rO) :
    rAMin lo rB rO ≤ rA ↔ 2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 := by
  sorry

theorem le_rAMax_iff_sq {hi rA rB rO : ℝ} (hhi : 0 ≤ hi) (h : 0 < rB + rO) (hA : 0 ≤ rA + rO) :
    rA ≤ rAMax hi rB rO ↔ (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2 := by
  sorry

theorem conforms_iff_sq {lo hi rA rB rO : ℝ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (h : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) : GoldschmidtConforms lo hi rA rB rO ↔
      2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 ∧
        (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2 := by
  sorry

theorem conforms_symmetric_band_iff {delta rA rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms (1 - delta) (1 + delta) rA rB rO ↔
      |rA - idealA rB rO| ≤ delta * idealAO rB rO := by
  sorry

theorem conforms_classic_band_iff {rA rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms classicLo classicHi rA rB rO ↔
      classicLo * idealAO rB rO - rO ≤ rA ∧ rA ≤ idealA rB rO := by
  sorry

theorem conforms_of_conforms_window_le {lo lo' hi hi' rA rB rO : ℝ} (h1 : lo' ≤ lo)
    (h2 : hi ≤ hi') : GoldschmidtConforms lo hi rA rB rO →
      GoldschmidtConforms lo' hi' rA rB rO := by
  sorry

theorem goldschmidtZone_ideal_iff_conforms {lo hi rA rB rO : ℝ} :
    goldschmidtZone lo hi (tolFac rA rB rO) = GoldschmidtZone.ideal ↔
      GoldschmidtConforms lo hi rA rB rO := by
  sorry

theorem exists_conforming {lo hi : ℝ} (h : lo ≤ hi) :
    ∃ rA : ℝ, GoldschmidtConforms lo hi rA 1 1 := by
  sorry

theorem exists_tooSmall (lo hi : ℝ) : ∃ rA : ℝ, ¬ GoldschmidtConforms lo hi rA 1 1 := by
  sorry

theorem exists_tooLarge (lo hi : ℝ) : ∃ rA : ℝ, ¬ GoldschmidtConforms lo hi rA 1 1 := by
  sorry

theorem conforms_at_idealA_classic {rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms classicLo classicHi (idealA rB rO) rB rO := by
  sorry

/-! ## G4 — sharp conditions (`PhotoLean/Goldschmidt/Sharp.lean`) -/

theorem not_conforms_of_band_empty {lo hi rA rB rO : ℝ} (h : hi < lo) :
    ¬ GoldschmidtConforms lo hi rA rB rO := by
  sorry

theorem conforms_point_band_iff {lo rA rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms lo lo rA rB rO ↔ tolFac rA rB rO = lo := by
  sorry

theorem not_conforms_of_lt_rAMin {lo hi rA rB rO : ℝ} (h : 0 < rB + rO)
    (h' : rA < rAMin lo rB rO) : ¬ GoldschmidtConforms lo hi rA rB rO := by
  sorry

theorem not_conforms_of_rAMax_lt {lo hi rA rB rO : ℝ} (h : 0 < rB + rO)
    (h' : rAMax hi rB rO < rA) : ¬ GoldschmidtConforms lo hi rA rB rO := by
  sorry

theorem tolFac_irrational {rA rB rO : ℚ} (hB : rB + rO ≠ 0) (hA : rA + rO ≠ 0) :
    Irrational (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)) := by
  sorry

theorem tolFacFifteen_le {rA rA' rB rO : ℝ} (h : 0 < rB + rO)
    (hm : RadiusMatch tauGoldschmidt rA rA') : |tolFac rA' rB rO - tolFac rA rB rO| ≤
      tauGoldschmidt * rA / (Real.sqrt 2 * (rB + rO)) := by
  sorry

theorem conforms_of_radiusMatch_window {lo hi tau rA rA' rB rO : ℝ} (h : 0 < rB + rO)
    (hm : RadiusMatch tau rA rA') (hlo : rAMin lo rB rO ≤ (1 - tau) * rA)
    (hhi : (1 + tau) * rA ≤ rAMax hi rB rO) : GoldschmidtConforms lo hi rA' rB rO := by
  sorry

theorem witness_tooSmall : ¬ GoldschmidtConforms classicLo classicHi (-1) 1 1 := by
  sorry

theorem witness_tooLarge : ¬ GoldschmidtConforms classicLo classicHi 3 1 1 := by
  sorry

theorem witness_inverted_band : ¬ GoldschmidtConforms 1 classicLo 0 1 1 := by
  sorry

theorem witness_ideal_packing : GoldschmidtConforms classicLo classicHi (idealA 1 1) 1 1 := by
  sorry

theorem witness_band_flip : GoldschmidtConforms classicHi tetragonalHi (161 / 100) (121 / 200)
    (7 / 5) ∧ ¬ GoldschmidtConforms classicLo classicHi (161 / 100) (121 / 200) (7 / 5) := by
  sorry

/-! ## G5 — rational decision layer (`PhotoLean/Goldschmidt/RatModel.lean`) -/

namespace Rat

/-- The square of the tolerance factor: rational whenever the radii are rational, unlike `t` itself
(`√2` is irrational). -/
noncomputable def tolFacSq (rA rB rO : ℚ) : ℚ := (rA + rO) ^ 2 / (2 * (rB + rO) ^ 2)

/-- The `√2`-free band criterion on `ℚ`: the squared window on `(rA + rO)`. -/
def inBandQ (lo hi rA rB rO : ℚ) : Prop :=
  2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 ∧ (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2

/-- The radius rule on `ℚ`. -/
def radiusMatchQ (tau r r' : ℚ) : Prop := |r - r'| ≤ tau * r

/-- The electronegativity-dressed tolerance on `ℚ`. -/
noncomputable def chiTolQ (tol0 k chi chi' : ℚ) : ℚ := tol0 - k * |chi - chi'|

/-- The chemical rule composed with the radius rule on `ℚ`. -/
def substitutableQ (tol0 k chi chi' r r' : ℚ) : Prop := radiusMatchQ (chiTolQ tol0 k chi chi') r r'

/-- Computable three-way classifier on `ℚ`, comparing the squared quantities. -/
def zoneQ (lo hi rA rB rO : ℚ) : GoldschmidtZone :=
  if (rA + rO) ^ 2 < 2 * lo ^ 2 * (rB + rO) ^ 2 then GoldschmidtZone.tooSmall
  else if (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2 then GoldschmidtZone.ideal
  else GoldschmidtZone.tooLarge

/-- `ℚ` mirror of the classic band's lower edge. -/
def classicLoQ : ℚ := 4 / 5

/-- `ℚ` mirror of the classic band's upper edge. -/
def classicHiQ : ℚ := 1

/-- `ℚ` mirror of the tetragonal band's upper edge. -/
def tetragonalHiQ : ℚ := 11 / 10

/-- `ℚ` mirror of the printed "15 %" figure. -/
def tauGoldschmidtQ : ℚ := 3 / 20

theorem tolFacSq_cast (rA rB rO : ℚ) :
    ((tolFacSq rA rB rO : ℚ) : ℝ) = (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)) ^ 2 := by
  sorry

theorem inBandQ_cast {lo hi rA rB rO : ℚ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hB : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) : inBandQ lo hi rA rB rO ↔
      GoldschmidtConforms (lo : ℝ) (hi : ℝ) (rA : ℝ) (rB : ℝ) (rO : ℝ) := by
  sorry

theorem inBandQ_ideal_iff {rA rB rO : ℚ} (hB : 0 < rB + rO) (hA : 0 ≤ rA + rO) :
    inBandQ 1 1 rA rB rO ↔ (rA + rO) ^ 2 = 2 * (rB + rO) ^ 2 := by
  sorry

theorem radiusMatchQ_cast {tau r r' : ℚ} :
    radiusMatchQ tau r r' ↔ RadiusMatch (tau : ℝ) (r : ℝ) (r' : ℝ) := by
  sorry

theorem radiusMatchQ_iff_window {tau r r' : ℚ} :
    radiusMatchQ tau r r' ↔ (1 - tau) * r ≤ r' ∧ r' ≤ (1 + tau) * r := by
  sorry

theorem radiusMatchQ_fifteen {r r' : ℚ} :
    radiusMatchQ (3 / 20) r r' ↔ 17 * r ≤ 20 * r' ∧ 20 * r' ≤ 23 * r := by
  sorry

theorem zoneQ_eq_zone {lo hi rA rB rO : ℚ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hB : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) : zoneQ lo hi rA rB rO =
      goldschmidtZone (lo : ℝ) (hi : ℝ) (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)) := by
  sorry

theorem zoneQ_ideal_iff (lo hi rA rB rO : ℚ) :
    zoneQ lo hi rA rB rO = GoldschmidtZone.ideal ↔ inBandQ lo hi rA rB rO := by
  sorry

theorem classicLoQ_cast : (classicLoQ : ℝ) = classicLo := by
  sorry

theorem classicHiQ_cast : (classicHiQ : ℝ) = classicHi := by
  sorry

theorem tetragonalHiQ_cast : (tetragonalHiQ : ℝ) = tetragonalHi := by
  sorry

theorem tauGoldschmidtQ_cast : (tauGoldschmidtQ : ℝ) = tauGoldschmidt := by
  sorry

end Rat

/-! ## G6 — instance verdicts (`PhotoLean/Goldschmidt/Instances.lean`) -/

/-- Shannon 1976, 12-coordinate `Sr²⁺`: `1.44 Å`. -/
def rA_Sr : ℚ := 36 / 25

/-- Shannon 1976, 12-coordinate `Ca²⁺`: `1.34 Å`. -/
def rA_Ca : ℚ := 67 / 50

/-- Shannon 1976, 12-coordinate `Ba²⁺`: `1.61 Å`. -/
def rA_Ba : ℚ := 161 / 100

/-- Shannon 1976, 12-coordinate `Cs⁺`: `1.88 Å`. -/
def rA_Cs : ℚ := 47 / 25

/-- Shannon 1976, 12-coordinate `La³⁺`: `1.36 Å`. -/
def rA_La : ℚ := 34 / 25

/-- Shannon 1976, 12-coordinate `Na⁺`: `1.39 Å`. -/
def rA_Na : ℚ := 139 / 100

/-- Shannon 1976, 6-coordinate `Ti⁴⁺`: `0.605 Å`. -/
def rB_Ti : ℚ := 121 / 200

/-- Shannon 1976, 6-coordinate high-spin `Mn³⁺`: `0.645 Å`. -/
def rB_Mn : ℚ := 129 / 200

/-- Shannon 1976, 6-coordinate `Nb⁵⁺`: `0.64 Å`. -/
def rB_Nb : ℚ := 16 / 25

/-- Shannon 1976, 6-coordinate `Ni⁴⁺`: `0.48 Å`. -/
def rB_Ni : ℚ := 12 / 25

/-- Shannon 1976 oxygen radius: `1.40 Å`. -/
def rO_shannon : ℚ := 7 / 5

theorem inst_SrTiO3_tooLarge_classic :
    ¬ Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Sr rB_Ti rO_shannon := by
  sorry

theorem inst_SrTiO3_conforms_symmetric :
    Rat.inBandQ (49 / 50) (51 / 50) rA_Sr rB_Ti rO_shannon := by
  sorry

theorem inst_SrTiO3_zone_tooLarge :
    Rat.zoneQ Rat.classicLoQ Rat.classicHiQ rA_Sr rB_Ti rO_shannon = GoldschmidtZone.tooLarge := by
  sorry

theorem inst_CaTiO3_classic : Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Ca rB_Ti rO_shannon := by
  sorry

theorem inst_CaTiO3_zone_ideal :
    Rat.zoneQ Rat.classicLoQ Rat.classicHiQ rA_Ca rB_Ti rO_shannon = GoldschmidtZone.ideal := by
  sorry

theorem inst_BaTiO3_not_classic :
    ¬ Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Ba rB_Ti rO_shannon := by
  sorry

theorem inst_BaTiO3_conforms_tetragonal :
    Rat.inBandQ Rat.classicHiQ Rat.tetragonalHiQ rA_Ba rB_Ti rO_shannon := by
  sorry

theorem inst_BaTiO3_band_flip : Rat.inBandQ Rat.classicHiQ Rat.tetragonalHiQ rA_Ba rB_Ti rO_shannon
    ∧ ¬ Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Ba rB_Ti rO_shannon := by
  sorry

theorem inst_LaMnO3_classic : Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_La rB_Mn rO_shannon := by
  sorry

theorem inst_NaNbO3_classic : Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Na rB_Nb rO_shannon := by
  sorry

theorem inst_BaNiO3_not_tetragonal :
    ¬ Rat.inBandQ Rat.classicHiQ Rat.tetragonalHiQ rA_Ba rB_Ni rO_shannon := by
  sorry

theorem inst_BaNiO3_zone_tooLarge :
    Rat.zoneQ Rat.classicHiQ Rat.tetragonalHiQ rA_Ba rB_Ni rO_shannon = GoldschmidtZone.tooLarge := by
  sorry

theorem inst_ideal_row_classic : GoldschmidtConforms classicLo classicHi (idealA 1 1) 1 1 := by
  sorry

theorem inst_rA_eq_rB_tolFac : tolFac 1 1 1 = 1 / Real.sqrt 2 := by
  sorry

theorem inst_radius_Sr_Ca : Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Sr rA_Ca := by
  sorry

theorem inst_radius_Sr_Ba : Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Sr rA_Ba := by
  sorry

theorem inst_radius_Ca_Ba_fails : ¬ Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Ca rA_Ba := by
  sorry

theorem inst_radius_convention_Ba_Cs :
    Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Cs rA_Ba ∧
      ¬ Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Ba rA_Cs := by
  sorry

theorem inst_radius_ok_but_band_lost : Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Ca rA_Sr ∧
    ¬ Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Sr rB_Ti rO_shannon := by
  sorry

theorem inst_charge_coupled : ChargeBalanced (fun b : Bool => if b then (1 : ℤ) else -1) := by
  sorry

theorem inst_charge_single_fails : ¬ ChargeBalanced (fun _ : Unit => (1 : ℤ)) := by
  sorry

theorem inst_charge_compensating_partner :
    ∃ j : Bool, j ≠ true ∧ (fun b : Bool => if b then (1 : ℤ) else -1) j < 0 := by
  sorry

theorem inst_chi_load_bearing :
    Rat.substitutableQ (3 / 20) (1 / 10) 0 0 rA_Ca (153 / 100) ∧
      ¬ Rat.substitutableQ (3 / 20) (1 / 10) 0 (3 / 2) rA_Ca (153 / 100) := by
  sorry

end Goldschmidt

end PhotoLean
