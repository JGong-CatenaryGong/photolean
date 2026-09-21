/-
  PhotoLean — theories/goldschmidt/probes/goldschmidt-api-instance-arith.lean

  mathlib API calibration for the Goldschmidt theory, dispatch item (h): the instance arithmetic of
  the six Shannon-radius rows of plan §9 (I2/I3/I4). Every verdict is a `norm_num` fact **in `ℚ`,
  with no `Real.sqrt` anywhere** — the criterion is `(rA+rO)^2` versus `2 (rB+rO)^2`.

  Run from the repository root:

      proofs/scripts/lake env lean theories/goldschmidt/probes/goldschmidt-api-instance-arith.lean

  Lean 4.17.0 + mathlib v4.17.0. Status: 0 error / 0 warning.

  Normalization used below: with `rO := 0` the three-radius factor collapses to
  `tolFac nA nB 0 = nA / (√2 * nB)`, i.e. exactly the two contact sums `nA = rA + rO`,
  `nB = rB + rO`. So a verdict on the pair `(nA, nB)` is a verdict on the tolerance factor.

  **Six verdicts (independent cross-check of the numbers, `norm_num`-kernel-checked):**

  | row | `rA + rO` | `rB + rO` | `(rA+rO)^2` vs `2 (rB+rO)^2` | verdict |
  |---|---|---|---|---|
  | `SrTiO₃` | `71/25` | `401/200` | `>` | **`t > 1`** (`t ≈ 1.00159`) |
  | `CaTiO₃` | `137/50` | `401/200` | `<` | **`t < 1`** (`t ≈ 0.96632`) |
  | `BaTiO₃` | `301/100` | `401/200` | `>` | **`t > 1`** (`t ≈ 1.06154`) |
  | `LaMnO₃` | `69/25` | `409/200` | `<` | **`t < 1`** (`t ≈ 0.95434`) |
  | `NaNbO₃` | `279/100` | `51/25` | `<` | **`t < 1`** (`t ≈ 0.96707`) |
  | `BaNiO₃` | `301/100` | `47/25` | `>` | **`t > 1`** (`t ≈ 1.13212`; `t^2 = 90601/70688`) |

  No row gives `t = 1` (no row has `(rA+rO)^2 = 2 (rB+rO)^2`). The verdicts agree with the plan's
  own claims (`SrTiO₃` above the classic `1.0` edge, `BaTiO₃` flipped into the tetragonal band,
  `BaNiO₃` outside every delivered band).

  **One number in the dispatch's brief is wrong and is corrected here (reported loudly):** the
  `BaNiO₃` row was given as `rB + rO = 47/50`; the authority's Shannon radii
  (`rB_Ni = 12/25`, `rO_shannon = 7/5`, `goldschmidt-statement-skeleton.lean` G6) give
  `rB + rO = 47/25 = 1.88`, and `47/50 = 0.94 < rO = 1.40` would force `rB < 0`. The verdict
  *direction* is unaffected (`t > 1` and outside the tetragonal band in both readings), but the
  delivered numbers must be `47/25`, `t ≈ 1.13212`, `t^2 = 90601/70688` — matching plan §9. The
  other five rows' sums are exactly `rA_X + rO_shannon` (kernel-checked at the end of this file).
-/
import Mathlib

noncomputable section

/-- Plan §2 mirror (`ℝ`); the instance criterion below is about the three radii, `rO := 0` is the
canonical normalization onto the two contact sums. -/
def tolFac (rA rB rO : ℝ) : ℝ := (rA + rO) / (Real.sqrt 2 * (rB + rO))

/-! ## The two criteria as ℝ verdicts (mirrors of plan §6 `conforms_iff_sq` halves) -/

/-- `t ≤ 1 ↔ (rA+rO)^2 ≤ 2 (rB+rO)^2`. -/
theorem tolFac_le_one_iff_sq {rA rB rO : ℝ} (hB : 0 < rB + rO) (hA : 0 ≤ rA + rO) :
    tolFac rA rB rO ≤ 1 ↔ (rA + rO) ^ 2 ≤ 2 * (rB + rO) ^ 2 := by
  have hd : 0 < Real.sqrt 2 * (rB + rO) :=
    mul_pos (Real.sqrt_pos_of_pos (by norm_num)) hB
  have hsq : (1 * (Real.sqrt 2 * (rB + rO))) ^ 2 = 2 * (rB + rO) ^ 2 := by
    rw [one_mul, mul_pow, Real.sq_sqrt (by norm_num)]
  rw [tolFac, div_le_iff₀ hd, ← hsq]
  exact (sq_le_sq₀ hA (by positivity)).symm

/-- `1 ≤ t ↔ 2 (rB+rO)^2 ≤ (rA+rO)^2`. -/
theorem one_le_tolFac_iff_sq {rA rB rO : ℝ} (hB : 0 < rB + rO) (hA : 0 ≤ rA + rO) :
    1 ≤ tolFac rA rB rO ↔ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 := by
  have hd : 0 < Real.sqrt 2 * (rB + rO) :=
    mul_pos (Real.sqrt_pos_of_pos (by norm_num)) hB
  have hsq : (1 * (Real.sqrt 2 * (rB + rO))) ^ 2 = 2 * (rB + rO) ^ 2 := by
    rw [one_mul, mul_pow, Real.sq_sqrt (by norm_num)]
  rw [tolFac, le_div_iff₀ hd, ← hsq]
  exact (sq_le_sq₀ (by positivity) hA).symm

/-- The `lo`-general window half used by the classic-band rows. -/
theorem le_tolFac_iff_sq {rA rB rO lo : ℝ} (hlo : 0 ≤ lo) (hB : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) :
    lo ≤ tolFac rA rB rO ↔ 2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 := by
  have hd : 0 < Real.sqrt 2 * (rB + rO) :=
    mul_pos (Real.sqrt_pos_of_pos (by norm_num)) hB
  have hsq : (lo * (Real.sqrt 2 * (rB + rO))) ^ 2 = 2 * lo ^ 2 * (rB + rO) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [tolFac, le_div_iff₀ hd, ← hsq]
  exact (sq_le_sq₀ (mul_nonneg hlo (le_of_lt hd)) hA).symm

/-- The `hi`-general window half. -/
theorem tolFac_le_iff_sq {rA rB rO hi : ℝ} (hhi : 0 ≤ hi) (hB : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) :
    tolFac rA rB rO ≤ hi ↔ (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2 := by
  have hd : 0 < Real.sqrt 2 * (rB + rO) :=
    mul_pos (Real.sqrt_pos_of_pos (by norm_num)) hB
  have hsq : (hi * (Real.sqrt 2 * (rB + rO))) ^ 2 = 2 * hi ^ 2 * (rB + rO) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [tolFac, div_le_iff₀ hd, ← hsq]
  exact (sq_le_sq₀ hA (mul_nonneg hhi (le_of_lt hd))).symm

/-- Generic `t > 1` from the squared criterion. -/
theorem tolFac_gt_one_of_sq_gt {rA rB rO : ℝ} (hB : 0 < rB + rO) (hA : 0 ≤ rA + rO)
    (h : 2 * (rB + rO) ^ 2 < (rA + rO) ^ 2) : 1 < tolFac rA rB rO :=
  not_le.mp (by
    rw [tolFac_le_one_iff_sq hB hA]
    exact not_le.mpr h)

/-- Generic `t < 1` from the squared criterion. -/
theorem tolFac_lt_one_of_sq_lt {rA rB rO : ℝ} (hB : 0 < rB + rO) (hA : 0 ≤ rA + rO)
    (h : (rA + rO) ^ 2 < 2 * (rB + rO) ^ 2) : tolFac rA rB rO < 1 :=
  not_le.mp (by
    rw [one_le_tolFac_iff_sq hB hA]
    exact not_le.mpr h)

/-! ## I2/I3: the six rows

  Each row comes with the `ℚ`-only squared comparison (`*_sq_*`) and the corresponding ℝ verdict on
  the factor. The comparisons' common denominators are the ones in the header table: the `1`-edge
  test for `SrTiO₃` is `568² = 322624 > 321602 = 2·401²`, i.e. `(71/25)^2 = 322624/40000`. -/

/-- `SrTiO₃`: `(71/25)^2 > 2 (401/200)^2` in `ℚ` — the `norm_num` evidence for `t > 1`. -/
theorem srTiO3_sq_gt_one : 2 * (401 / 200 : ℚ) ^ 2 < (71 / 25 : ℚ) ^ 2 := by norm_num

theorem srTiO3_gt_one : 1 < tolFac (71 / 25) (401 / 200) 0 :=
  tolFac_gt_one_of_sq_gt (by norm_num) (by norm_num) (by norm_num)

/-- `SrTiO₃` is **above** the classic `[4/5, 1]` band (plan §1.1's headline negative row). -/
theorem srTiO3_not_classic :
    ¬ (4 / 5 ≤ tolFac (71 / 25) (401 / 200) 0 ∧ tolFac (71 / 25) (401 / 200) 0 ≤ 1) :=
  fun h => absurd h.2 (not_le.mpr srTiO3_gt_one)

/-- It **does** conform to the tetragonal `[1, 11/10]` band. -/
theorem srTiO3_tetragonal_conforms :
    1 ≤ tolFac (71 / 25) (401 / 200) 0 ∧ tolFac (71 / 25) (401 / 200) 0 ≤ 11 / 10 :=
  ⟨le_of_lt srTiO3_gt_one,
    (tolFac_le_iff_sq (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)⟩

/-- `CaTiO₃`: `(137/50)^2 < 2 (401/200)^2` — `t < 1`. -/
theorem caTiO3_sq_lt_one : (137 / 50 : ℚ) ^ 2 < 2 * (401 / 200 : ℚ) ^ 2 := by norm_num

theorem caTiO3_lt_one : tolFac (137 / 50) (401 / 200) 0 < 1 :=
  tolFac_lt_one_of_sq_lt (by norm_num) (by norm_num) (by norm_num)

/-- `CaTiO₃` conforms to the classic `[4/5, 1]` band. -/
theorem caTiO3_classic_conforms :
    4 / 5 ≤ tolFac (137 / 50) (401 / 200) 0 ∧ tolFac (137 / 50) (401 / 200) 0 ≤ 1 :=
  ⟨(le_tolFac_iff_sq (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num),
    le_of_lt caTiO3_lt_one⟩

/-- `BaTiO₃`: `(301/100)^2 > 2 (401/200)^2` — `t > 1` (the plan §9 I3 band-flip row). -/
theorem baTiO3_sq_gt_one : 2 * (401 / 200 : ℚ) ^ 2 < (301 / 100 : ℚ) ^ 2 := by norm_num

theorem baTiO3_gt_one : 1 < tolFac (301 / 100) (401 / 200) 0 :=
  tolFac_gt_one_of_sq_gt (by norm_num) (by norm_num) (by norm_num)

/-- `BaTiO₃` fails the classic band. -/
theorem baTiO3_not_classic :
    ¬ (4 / 5 ≤ tolFac (301 / 100) (401 / 200) 0 ∧ tolFac (301 / 100) (401 / 200) 0 ≤ 1) :=
  fun h => absurd h.2 (not_le.mpr baTiO3_gt_one)

/-- `BaTiO₃` conforms to the tetragonal `[1, 11/10]` band — the second half of the flip. -/
theorem baTiO3_tetragonal_conforms :
    1 ≤ tolFac (301 / 100) (401 / 200) 0 ∧ tolFac (301 / 100) (401 / 200) 0 ≤ 11 / 10 :=
  ⟨le_of_lt baTiO3_gt_one,
    (tolFac_le_iff_sq (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)⟩

/-- `LaMnO₃`: `(69/25)^2 < 2 (409/200)^2` — `t < 1`. -/
theorem laMnO3_sq_lt_one : (69 / 25 : ℚ) ^ 2 < 2 * (409 / 200 : ℚ) ^ 2 := by norm_num

theorem laMnO3_lt_one : tolFac (69 / 25) (409 / 200) 0 < 1 :=
  tolFac_lt_one_of_sq_lt (by norm_num) (by norm_num) (by norm_num)

/-- `LaMnO₃` conforms to the classic band. -/
theorem laMnO3_classic_conforms :
    4 / 5 ≤ tolFac (69 / 25) (409 / 200) 0 ∧ tolFac (69 / 25) (409 / 200) 0 ≤ 1 :=
  ⟨(le_tolFac_iff_sq (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num),
    le_of_lt laMnO3_lt_one⟩

/-- `NaNbO₃`: `(279/100)^2 < 2 (51/25)^2` — `t < 1`. -/
theorem NaNbO3_sq_lt_one : (279 / 100 : ℚ) ^ 2 < 2 * (51 / 25 : ℚ) ^ 2 := by norm_num

theorem NaNbO3_lt_one : tolFac (279 / 100) (51 / 25) 0 < 1 :=
  tolFac_lt_one_of_sq_lt (by norm_num) (by norm_num) (by norm_num)

/-- `NaNbO₃` conforms to the classic band. -/
theorem NaNbO3_classic_conforms :
    4 / 5 ≤ tolFac (279 / 100) (51 / 25) 0 ∧ tolFac (279 / 100) (51 / 25) 0 ≤ 1 :=
  ⟨(le_tolFac_iff_sq (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num),
    le_of_lt NaNbO3_lt_one⟩

/-- `BaNiO₃`: `2 * (47/25)^2 < (301/100)^2` — `t > 1`.

**Number correction (the dispatch's brief had `rB + rO = 47/50` for this row; see the header and
API-NOTES).** With the Shannon radii used by the authority (`rB_Ni = 12/25 = 0.48 Å`,
`rO = 7/5 = 1.40 Å`) the B–O contact distance is `47/25 = 1.88 Å`; `47/50` would make `rB` negative.
The verdict direction is unchanged (`t > 1`), only the magnitude (`t ≈ 1.13212`, not `2.26425`). -/
theorem BaNiO3_sq_gt_one : 2 * (47 / 25 : ℚ) ^ 2 < (301 / 100 : ℚ) ^ 2 := by norm_num

theorem BaNiO3_gt_one : 1 < tolFac (301 / 100) (47 / 25) 0 :=
  tolFac_gt_one_of_sq_gt (by norm_num) (by norm_num) (by norm_num)

/-- `BaNiO₃` is outside **even** the tetragonal band (plan §9 I4 / §1.1): `t > 11/10`. -/
theorem BaNiO3_not_tetragonal : ¬ tolFac (301 / 100) (47 / 25) 0 ≤ 11 / 10 := by
  rw [tolFac_le_iff_sq (by norm_num) (by norm_num) (by norm_num)]
  norm_num


/-! ## Cross-check of the six rows against the authority's Shannon radii (G6 declarations)

  The authority declares the individual radii (`goldschmidt-statement-skeleton.lean` G6) and the row
  verdicts use them directly. The nine kernel-checked equalities below verify that the two contact
  sums of the table are exactly `rA_X + rO_shannon` and `rB_Y + rO_shannon` — i.e. the table's
  numbers are the authority's data, not an independent paraphrase. -/

/-- Shannon 1976, 12-coordinate `Sr²⁺` (authority G6). -/
def rA_Sr : ℚ := 36 / 25
/-- Shannon 1976, 12-coordinate `Ca²⁺`. -/
def rA_Ca : ℚ := 67 / 50
/-- Shannon 1976, 12-coordinate `Ba²⁺`. -/
def rA_Ba : ℚ := 161 / 100
/-- Shannon 1976, 12-coordinate `La³⁺`. -/
def rA_La : ℚ := 34 / 25
/-- Shannon 1976, 12-coordinate `Na⁺`. -/
def rA_Na : ℚ := 139 / 100
/-- Shannon 1976, 6-coordinate `Ti⁴⁺`. -/
def rB_Ti : ℚ := 121 / 200
/-- Shannon 1976, 6-coordinate high-spin `Mn³⁺`. -/
def rB_Mn : ℚ := 129 / 200
/-- Shannon 1976, 6-coordinate `Nb⁵⁺`. -/
def rB_Nb : ℚ := 16 / 25
/-- Shannon 1976, 6-coordinate `Ni⁴⁺`. -/
def rB_Ni : ℚ := 12 / 25
/-- Shannon 1976 oxygen radius. -/
def rO_shannon : ℚ := 7 / 5

example : rA_Sr + rO_shannon = 71 / 25 := by norm_num [rA_Sr, rO_shannon]
example : rA_Ca + rO_shannon = 137 / 50 := by norm_num [rA_Ca, rO_shannon]
example : rA_Ba + rO_shannon = 301 / 100 := by norm_num [rA_Ba, rO_shannon]
example : rA_La + rO_shannon = 69 / 25 := by norm_num [rA_La, rO_shannon]
example : rA_Na + rO_shannon = 279 / 100 := by norm_num [rA_Na, rO_shannon]
example : rB_Ti + rO_shannon = 401 / 200 := by norm_num [rB_Ti, rO_shannon]
example : rB_Mn + rO_shannon = 409 / 200 := by norm_num [rB_Mn, rO_shannon]
example : rB_Nb + rO_shannon = 51 / 25 := by norm_num [rB_Nb, rO_shannon]
example : rB_Ni + rO_shannon = 47 / 25 := by norm_num [rB_Ni, rO_shannon]

end
