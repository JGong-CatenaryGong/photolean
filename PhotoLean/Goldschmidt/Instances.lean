/-
  PhotoLean — PhotoLean/Goldschmidt/Instances.lean

  The Goldschmidt theory, milestone G6 (the **instance / verdict layer**): the theory applied to
  named perovskite triples, each row decided by the kernel rather than by prose.

  Design of record: `theories/goldschmidt/plan.md` §9 (the row families I1–I8) and §12 (honesty
  table).  Statement authority:
  `theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean` § `## G6`, which every signature
  below matches word for word (checked by
  `python3 theories/BEP/probes/bep-fidelity.py --theory goldschmidt --milestone G6`).

  What this layer is, and what it is not.  The eleven radius constants are **printed numbers with
  provenance** (Shannon 1976, `theories/goldschmidt/LITERATURE.md` and the printed tables in
  `theories/goldschmidt/literature/INSTANCE-DATA.md`): A-site values are 12-coordinate, B-site values
  6-coordinate (`Mn³⁺` high-spin), and `rO_shannon = 1.40 Å`.  A row is a statement *about those
  numbers*, never about the material: nothing here claims that a measured crystal adopts a structure.
  The band edges are **parameters** of the theory (§1.2, §2), so every verdict below names the band it
  applies — the classic `[4/5, 1]`, the tetragonal `[1, 11/10]`, the symmetric `1 ± 1/50` — and every
  band edge enters as an explicit argument, never as a value hidden inside a definition.

  Every numeric verdict is decided in the rational layer G5 (`Rat.inBandQ`, `Rat.zoneQ`,
  `Rat.radiusMatchQ`, `Rat.substitutableQ`), i.e. by exact arithmetic on the squared criterion, whose
  correctness theorem is `Rat.inBandQ_cast` (built on `Criterion.conforms_iff_sq`): the kernel decides
  the `ℚ` statement and the transfer theorem carries it to the real band verdict, so no `√2` and no
  numerical approximation enters a proof.  The two rows that are stated in `ℝ` are the model's own
  (`inst_ideal_row_classic`, `inst_rA_eq_rB_tolFac`), where the algebra is closed form.

  The numbers were certified three times over before dispatch — independently of this file and of the
  kernel — by the off-kernel exact-rational cross-check
  `theories/goldschmidt/probes/goldschmidt-instance-check.py` (exit 0, 0 mismatches), by the verifier's
  separate recomputation (identical to plan §9), and by the authority itself.  That is why a failure
  of `norm_num` anywhere in this file would be a HIGH finding about a *value*, not a proof bug: every
  row below is closed by `norm_num` (with `abs_of_nonneg` for the `ℚ` absolute values) or by an
  explicit closed form.

  Two rows are this theory's honest headlines.  `inst_SrTiO3_tooLarge_classic`: with Shannon's own
  printed radii the archetypal cubic perovskite `SrTiO₃` lands *just above* `t = 1`
  (`t² = 161312/160801 > 1`), so it **fails** the classic `0.8 ≤ t ≤ 1` band — while
  `inst_SrTiO3_conforms_symmetric` shows it *conforms* to the symmetric `1 ± 1/50` band.  The verdict
  is convention-dependent, and the dependency is delivered as two kernel facts (plus the band
  monotonicity theorem of G3, `conforms_of_conforms_window_le`), not as commentary.
  `inst_BaTiO3_band_flip`: `BaTiO₃` fails the classic band and conforms to the tetragonal one — the
  same two-sided fact at the band's upper edge, which is why the band convention is a parameter of the
  theory rather than a constant of it.
-/
import PhotoLean.Goldschmidt.Basic

import PhotoLean.Goldschmidt.Rules

import PhotoLean.Goldschmidt.Criterion

import PhotoLean.Goldschmidt.RatModel

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Goldschmidt

/-! ## G6 radius constants — Shannon 1976, printed values as exact rationals (plan §9, §12)

  A-site radii are for 12-coordinate cations, B-site radii for 6-coordinate cations; oxygen is the
  1.40 Å value.  Each constant is an *instance* of the formalized parameter, with its provenance in
  the docstring; no radius is derived inside the theory. -/

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

/-! ## G6 instance verdicts (plan §9, families I1–I8) -/

/-- **`SrTiO₃` fails the classic cubic band** (family I2, and this theory's negative headline).  With
Shannon's printed radii `rA_Sr + rO_shannon = 71/25` and `rB_Ti + rO_shannon = 401/200`, the squared
factor is `t² = 161312/160801 > 1`, so the upper half of `Rat.inBandQ classicLoQ classicHiQ` fails;
the row is decided by `norm_num` on the squared criterion (G5), which `Rat.inBandQ_cast` carries to the
classic band `4/5 ≤ t ≤ 1`.  The verdict is a fact about the printed numbers, and it is
convention-dependent — see `inst_SrTiO3_conforms_symmetric` for the same triple against `1 ± 1/50`. -/
theorem inst_SrTiO3_tooLarge_classic :
    ¬ Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Sr rB_Ti rO_shannon := by
  rintro ⟨_, h2⟩
  unfold Rat.classicHiQ rA_Sr rB_Ti rO_shannon at h2
  norm_num at h2

/-- **The same `SrTiO₃` triple conforms to the narrow symmetric band `1 ± 1/50`** (family I2).  With
`t² = 161312/160801` in `[(49/50)², (51/50)²] = [2401/2500, 2601/2500]`, both halves of
`Rat.inBandQ (49/50) (51/50)` hold.  Delivered beside the negative classic-band row so that the
convention dependence of the archetypal cubic perovskite is a pair of kernel facts, not a caveat in
prose. -/
theorem inst_SrTiO3_conforms_symmetric :
    Rat.inBandQ (49 / 50) (51 / 50) rA_Sr rB_Ti rO_shannon := by
  unfold Rat.inBandQ rA_Sr rB_Ti rO_shannon
  norm_num

/-- The G5 classifier on the same triple takes the `tooLarge` branch of the classic band (family I2),
computed on the squared criterion by the `zoneQ` cascade (`Rat.zoneQ_eq_zone` transfers it to
`goldschmidtZone` on the real factor). -/
theorem inst_SrTiO3_zone_tooLarge :
    Rat.zoneQ Rat.classicLoQ Rat.classicHiQ rA_Sr rB_Ti rO_shannon = GoldschmidtZone.tooLarge := by
  unfold Rat.zoneQ Rat.classicLoQ Rat.classicHiQ rA_Sr rB_Ti rO_shannon
  norm_num

/-- **`CaTiO₃` conforms to the classic cubic band** (family I2).  `rA_Ca + rO_shannon = 137/50` with
`rB_Ti + rO_shannon = 401/200` gives `t² = 150152/160801`, inside `[16/25, 1]`, i.e.
`(4/5)² ≤ t² ≤ 1²` — the band is applied as the parameter it is. -/
theorem inst_CaTiO3_classic : Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Ca rB_Ti rO_shannon := by
  unfold Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Ca rB_Ti rO_shannon
  norm_num

/-- The classifier places `CaTiO₃` in the `ideal` branch of the classic band (family I2) — the
positive counterpart of `inst_SrTiO3_zone_tooLarge`, decided by the same `zoneQ` cascade. -/
theorem inst_CaTiO3_zone_ideal :
    Rat.zoneQ Rat.classicLoQ Rat.classicHiQ rA_Ca rB_Ti rO_shannon = GoldschmidtZone.ideal := by
  unfold Rat.zoneQ Rat.classicLoQ Rat.classicHiQ rA_Ca rB_Ti rO_shannon
  norm_num

/-- **`BaTiO₃` fails the classic cubic band** (family I3).  `rA_Ba + rO_shannon = 301/100` with
`rB_Ti + rO_shannon = 401/200` gives `t² = 181202/160801 > 1`: the ferroelectric distortion of
`BaTiO₃` shows up in the printed radii as a factor just above the classic upper edge `t = 1`. -/
theorem inst_BaTiO3_not_classic :
    ¬ Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Ba rB_Ti rO_shannon := by
  rintro ⟨_, h2⟩
  unfold Rat.classicHiQ rA_Ba rB_Ti rO_shannon at h2
  norm_num at h2

/-- **`BaTiO₃` conforms to the tetragonal band `[1, 11/10]`** (family I3): `t² = 181202/160801` lies in
`[1, 121/100]`.  The band here is `[classicHiQ, tetragonalHiQ]`, i.e. the reference edge `t = 1` is
read as the *lower* edge — the same numbers, a different convention, a different verdict. -/
theorem inst_BaTiO3_conforms_tetragonal :
    Rat.inBandQ Rat.classicHiQ Rat.tetragonalHiQ rA_Ba rB_Ti rO_shannon := by
  unfold Rat.inBandQ Rat.classicHiQ Rat.tetragonalHiQ rA_Ba rB_Ti rO_shannon
  norm_num

/-- **The band flip of `BaTiO₃`** (family I3): conforming to `[1, 11/10]` and failing `[4/5, 1]` are two
kernel facts about the same triple.  This conjunction *is* the statement that the band convention is a
parameter of the theory rather than a constant of it; the two halves are the two rows above (and G3's
`conforms_of_conforms_window_le` is the general monotonicity law behind the "widening never loses a
candidate" reading). -/
theorem inst_BaTiO3_band_flip : Rat.inBandQ Rat.classicHiQ Rat.tetragonalHiQ rA_Ba rB_Ti rO_shannon
    ∧ ¬ Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Ba rB_Ti rO_shannon :=
  ⟨inst_BaTiO3_conforms_tetragonal, inst_BaTiO3_not_classic⟩

/-- **`LaMnO₃` conforms to the classic cubic band** (family I2), with the high-spin 6-coordinate
`Mn³⁺` radius: `rA_La + rO_shannon = 69/25`, `rB_Mn + rO_shannon = 409/200`, `t² = 152352/167281`. -/
theorem inst_LaMnO3_classic : Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_La rB_Mn rO_shannon := by
  unfold Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_La rB_Mn rO_shannon
  norm_num

/-- **`NaNbO₃` conforms to the classic cubic band** (family I2): `rA_Na + rO_shannon = 279/100`,
`rB_Nb + rO_shannon = 51/25`, `t² = 8649/9248`. -/
theorem inst_NaNbO3_classic : Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Na rB_Nb rO_shannon := by
  unfold Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Na rB_Nb rO_shannon
  norm_num

/-- **`BaNiO₃` is outside even the tetragonal band** (family I4): `rA_Ba + rO_shannon = 301/100` with
the small `Ni⁴⁺` radius gives `rB_Ni + rO_shannon = 47/25` and `t² = 90601/70688 > 121/100`, so the
upper edge of `[1, 11/10]` is violated — the theory's own way of recording the literature's hexagonal
assignment of `BaNiO₃`: no delivered band contains these printed numbers. -/
theorem inst_BaNiO3_not_tetragonal :
    ¬ Rat.inBandQ Rat.classicHiQ Rat.tetragonalHiQ rA_Ba rB_Ni rO_shannon := by
  rintro ⟨_, h2⟩
  unfold Rat.tetragonalHiQ rA_Ba rB_Ni rO_shannon at h2
  norm_num at h2

/-- The classifier's `tooLarge` branch for `BaNiO₃` against the tetragonal band (family I4), the
classifier companion of `inst_BaNiO3_not_tetragonal`. -/
theorem inst_BaNiO3_zone_tooLarge :
    Rat.zoneQ Rat.classicHiQ Rat.tetragonalHiQ rA_Ba rB_Ni rO_shannon = GoldschmidtZone.tooLarge := by
  unfold Rat.zoneQ Rat.classicHiQ Rat.tetragonalHiQ rA_Ba rB_Ni rO_shannon
  norm_num

/-- **The model's ideal row** (family I1) in `ℝ`: the ideal A radius of the normalized triple
`rB = rO = 1` conforms to the classic band.  Closed form rather than arithmetic — the A radius that
realizes `t = 1` is inside every band whose upper edge is at least `1` (`conforms_at_idealA_iff`, G3),
and this row instantiates that at the classic band `[4/5, 1]`. -/
theorem inst_ideal_row_classic : GoldschmidtConforms classicLo classicHi (idealA 1 1) 1 1 :=
  conforms_at_idealA_classic (by norm_num : (0 : ℝ) < 1 + 1)

/-- **The `rA = rB` degenerate row** (family I1) in `ℝ`: at `rA = rB = 1`, `rO = 1` the factor is
exactly `1/√2` — the constant branch of the G3 `rO` trichotomy in closed form, computed as
`2/(√2·2) = 1/√2` by `div_eq_div_iff`. -/
theorem inst_rA_eq_rB_tolFac : tolFac 1 1 1 = 1 / Real.sqrt 2 := by
  unfold tolFac
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-! ## G6 substitution-rule verdicts (families I5–I7, plan §5/§9) -/

/-- **`Sr²⁺`/`Ca²⁺` pass Goldschmidt's 15 % radius rule** (family I5): the radii differ by
`|36/25 - 67/50| = 1/10`, well inside `τ r = (3/20)(36/25) = 27/125`.  The rule is the *declared*
one of G2, applied with `r` as the reference radius — the convention that matters in the two rows
below. -/
theorem inst_radius_Sr_Ca : Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Sr rA_Ca := by
  unfold Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Sr rA_Ca
  norm_num [abs_of_nonneg]

/-- **`Sr²⁺`/`Ba²⁺` pass the 15 % rule** (family I5): `|36/25 - 161/100| = 17/100 ≤ 27/125`. -/
theorem inst_radius_Sr_Ba : Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Sr rA_Ba := by
  unfold Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Sr rA_Ba
  norm_num [abs_of_nonneg]

/-- **`Ca²⁺`/`Ba²⁺` fail the 15 % rule with `Ca²⁺` as the reference** (family I5):
`|67/50 - 161/100| = 27/100 > 201/1000 = (3/20)(67/50)`. -/
theorem inst_radius_Ca_Ba_fails : ¬ Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Ca rA_Ba := by
  unfold Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Ca rA_Ba
  norm_num [abs_of_nonneg]

/-- **The reference-radius convention made visible** (family I5): the pair `Cs⁺`/`Ba²⁺` passes the
15 % rule with `Cs⁺` as the reference radius (`27/100 ≤ 141/500`) and fails it with `Ba²⁺` as the
reference (`27/100 > 483/2000`).  The declared rule of G2 is normalized by its *first* argument
(`RadiusMatch τ r r' := |r - r'| ≤ τ * r`), so both verdicts hold simultaneously — the ambiguity the
literature record flags rather than resolves, delivered here as a kernel-checked pair. -/
theorem inst_radius_convention_Ba_Cs :
    Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Cs rA_Ba ∧
      ¬ Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Ba rA_Cs :=
  ⟨by
    unfold Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Cs rA_Ba
    norm_num [abs_of_nonneg],
   by
    unfold Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Ba rA_Cs
    norm_num [abs_of_nonneg]⟩

/-- **A substitution that satisfies the radius rule can still lose the band** (family I5): `Ca²⁺` lies
inside 15 % of `Sr²⁺` (`inst_radius_Sr_Ca`'s mirror), yet the resulting `SrTiO₃` triple fails the
classic band (`inst_SrTiO3_tooLarge_classic`).  This is the composition row of the two layers: rule 1
governs the *radii*, the band verdict governs the *geometry*, and passing the former does not imply
the latter — the transfer theorem for the other direction is G4's
`conforms_of_radiusMatch_window`, whose window hypotheses are exactly what this pair violates. -/
theorem inst_radius_ok_but_band_lost : Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Ca rA_Sr ∧
    ¬ Rat.inBandQ Rat.classicLoQ Rat.classicHiQ rA_Sr rB_Ti rO_shannon :=
  ⟨by
    unfold Rat.radiusMatchQ Rat.tauGoldschmidtQ rA_Ca rA_Sr
    norm_num [abs_of_nonneg],
   inst_SrTiO3_tooLarge_classic⟩

/-- **A coupled (charge-balanced) substitution** (family I6): the `Na⁺`/`Nb⁵⁺ ↔ Ca²⁺`-style pair has
charge increments `+1` and `−1`, whose sum over the two-site set is zero.  Charge balance is exact
integer arithmetic (G2's `ChargeBalanced`), decided here by `Fintype.sum_bool`. -/
theorem inst_charge_coupled : ChargeBalanced (fun b : Bool => if b then (1 : ℤ) else -1) := by
  unfold ChargeBalanced
  rw [Fintype.sum_bool]
  norm_num

/-- **An uncompensated single-site substitution is not charge-balanced** (family I6): one site with
increment `+1` sums to `1 ≠ 0`.  The negative companion of `inst_charge_coupled`, showing that the
charge rule is load-bearing rather than vacuous. -/
theorem inst_charge_single_fails : ¬ ChargeBalanced (fun _ : Unit => (1 : ℤ)) := by
  unfold ChargeBalanced
  rw [Fintype.sum_unique]
  norm_num

/-- **The compensating partner exists** (family I6): in the coupled pair of `inst_charge_coupled` the
positively charged `true` site has the distinct negatively charged partner `false` — the instance of
G2's existence theorem `exists_compensating_partner`, checked concretely. -/
theorem inst_charge_compensating_partner :
    ∃ j : Bool, j ≠ true ∧ (fun b : Bool => if b then (1 : ℤ) else -1) j < 0 :=
  ⟨false, by decide, by norm_num⟩

/-- **The electronegativity term is load-bearing** (family I7): with the declared linear shape
`chiTolQ tol₀ k χ χ' = tol₀ - k |χ - χ'|`, the substitution `Ca²⁺ ← 1.53 Å` passes the dressed radius
rule at `|χ - χ'| = 0` (tolerance `3/20`, `19/100 ≤ 201/1000`) and fails it at `|χ - χ'| = 3/2` (the
tolerance drops to `3/20 - 3/20 = 0`, and `19/100 ≤ 0` is false).  That pair is exactly the theorem
content of rule 3: the closer the chemical character, the larger the tolerated radius difference —
with the *shape* of the trade-off a declared modelling choice (plan §12), not a derived law. -/
theorem inst_chi_load_bearing :
    Rat.substitutableQ (3 / 20) (1 / 10) 0 0 rA_Ca (153 / 100) ∧
      ¬ Rat.substitutableQ (3 / 20) (1 / 10) 0 (3 / 2) rA_Ca (153 / 100) :=
  ⟨by
    unfold Rat.substitutableQ Rat.radiusMatchQ Rat.chiTolQ rA_Ca
    norm_num [abs_of_nonneg],
   by
    unfold Rat.substitutableQ Rat.radiusMatchQ Rat.chiTolQ rA_Ca
    norm_num [abs_of_nonneg]⟩

end Goldschmidt

end PhotoLean
