/-
  PhotoLean — theories/goldschmidt/probes/goldschmidt-api-rat-cast.lean

  mathlib API calibration for the Goldschmidt theory, dispatch item (f): the `ℚ` layer and the
  `ℚ → ℝ` cast push-through (plan §8 G5 rows `tolFacSq_cast`, `inBandQ_cast`).

  Run from the repository root:

      proofs/scripts/lake env lean theories/goldschmidt/probes/goldschmidt-api-rat-cast.lean

  Lean 4.17.0 + mathlib v4.17.0. All `Rat.cast_*` names below exist; `tolFacSq_cast` and
  `inBandQ_cast` are kernel-checked end to end. Status: 0 error / 0 warning.
-/
import Mathlib

noncomputable section

/-! ## (f) the `ℚ` cast layer — confirmed signatures (verbatim `#check @`, wraps joined) -/

#check @Rat.cast_pow
#check @Rat.cast_div
#check @Rat.cast_mul
#check @Rat.cast_add
#check @Rat.cast_sub
#check @Rat.cast_inv
#check @Rat.cast_le
#check @Rat.cast_lt
#check @Rat.cast_nonneg
#check @Rat.cast_eq_zero
#check @Rat.cast_ne_zero
#check @Rat.cast_pos
#check @Rat.cast_neg
#check @Rat.cast_one
#check @Rat.cast_zero
#check @Rat.cast_ofNat
#check @Rat.cast_natCast
#check @Rat.cast_intCast
#check @Rat.cast_inj
#check @Rat.cast_abs
#check @Rat.cast_max
#check @Rat.cast_min
#check @Rat.cast_sum

/-
  Notes for the prover (all measured):
  * `Rat.cast_le` / `Rat.cast_lt` / `Rat.cast_nonneg` / `Rat.cast_eq_zero` / `Rat.cast_ne_zero` /
    `Rat.cast_pos` are **iff**s, so `.mp`, `.mpr` and `.symm` are all usable; the field must be
    given explicitly (`(Rat.cast_le (K := ℝ))`) whenever the goal does not determine it.
  * `Rat.cast_pow` does **not** need `CharZero`; `Rat.cast_div` / `cast_mul` / `cast_add` /
    `cast_sub` / `cast_inv` do (`[DivisionRing α] [CharZero α]`).
  * There is no `Rat.cast_pow`-free route: `push_cast` uses these lemmas, so `push_cast` followed
    by the right `norm_num`/`ring` tail is the house recipe below.
-/

/-! ## The cast-push recipe for `(rA + rO)^2 / (2 * (rB + rO)^2)`

  Plan §2: `tolFacSq rA rB rO = (rA + rO)^2 / (2 * (rB + rO)^2)` on `ℚ`, and
  `tolFac rA rB rO = (rA + rO) / (√2 * (rB + rO))` on `ℝ`.
  The transfer is `tolFacSq_cast : ↑(tolFacSq rA rB rO) = (tolFac ↑rA ↑rB ↑rO)^2`. -/

/-- Plan §2 mirror (`ℚ`). -/
def tolFacSq (rA rB rO : ℚ) : ℚ := (rA + rO) ^ 2 / (2 * (rB + rO) ^ 2)

/-- Plan §2 mirror (`ℝ`). -/
def tolFac (rA rB rO : ℝ) : ℝ := (rA + rO) / (Real.sqrt 2 * (rB + rO))

/-- **`tolFacSq_cast`** (plan §8 G5), route A: `unfold` both definitions, `push_cast`, then
`field_simp` and the single rewrite `mul_pow, Real.sq_sqrt (by norm_num)` — no trailing `ring`. -/
theorem tolFacSq_cast (rA rB rO : ℚ) :
    ((tolFacSq rA rB rO : ℚ) : ℝ) = (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)) ^ 2 := by
  unfold tolFacSq tolFac
  push_cast
  field_simp
  rw [mul_pow, Real.sq_sqrt (by norm_num)]

/-- **`tolFacSq_cast`**, route B — no `field_simp`; the three rewrites `div_pow`, `mul_pow`,
`Real.sq_sqrt (by norm_num)` close it by themselves (append no `ring`: `no goals to be solved`). -/
theorem tolFacSq_cast' (rA rB rO : ℚ) :
    ((tolFacSq rA rB rO : ℚ) : ℝ) = (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)) ^ 2 := by
  unfold tolFacSq tolFac
  push_cast
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]

/-! ## The `≤`-transfer pattern of the G5 layer (used by `inBandQ_cast`)

  Statement shape: `(Pq : Prop on ℚ) ↔ (Pr : Prop on ℝ)` where `Pr` is `Pq` with every leaf cast.
  The kernel-checked two-step recipe is `rw [(Rat.cast_le (K := ℝ)).symm]; push_cast; rfl`. -/

example (lo rA rB rO : ℚ) :
    (2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2) ↔
      (2 * (lo : ℝ) ^ 2 * ((rB : ℝ) + (rO : ℝ)) ^ 2 ≤ ((rA : ℝ) + (rO : ℝ)) ^ 2) := by
  rw [(Rat.cast_le (K := ℝ)).symm]
  push_cast
  rfl

example (p q : ℚ) : p < q ↔ ((p : ℝ) < (q : ℝ)) := (Rat.cast_lt (K := ℝ)).symm

example (p : ℚ) : 0 < ((p : ℝ)) ↔ 0 < p := Rat.cast_pos

example (p : ℚ) : ((p : ℝ)) ≠ 0 ↔ p ≠ 0 := Rat.cast_ne_zero

/-! ## `GoldschmidtConforms` / `inBandQ` and the G5 correctness theorem `inBandQ_cast`

  The `ℚ` decision predicate is defined as the **squared** criterion of plan §6 `conforms_iff_sq`,
  so that `inBandQ_cast` is exactly `conforms_iff_sq` plus the cast alignment. -/

/-- Plan §2/§6 mirror: the band verdict on `ℝ`. -/
def GoldschmidtConforms (lo hi rA rB rO : ℝ) : Prop :=
  lo ≤ tolFac rA rB rO ∧ tolFac rA rB rO ≤ hi

/-- Plan §8 mirror: the `√2`-free squared band criterion on `ℚ`. -/
def inBandQ (lo hi rA rB rO : ℚ) : Prop :=
  2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 ∧
    (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2

/-- Half of `conforms_iff_sq` (plan §6): `lo ≤ t ↔ 2 lo² (rB+rO)² ≤ (rA+rO)²`. -/
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

/-- The other half of `conforms_iff_sq`: `t ≤ hi ↔ (rA+rO)² ≤ 2 hi² (rB+rO)²`. -/
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

/-- **`inBandQ_cast`** (plan §8 G5) — the correctness theorem of the rational decision layer,
kernel-checked end to end. The four side conditions are exactly the physical premises:
`0 ≤ lo`, `0 ≤ hi` (band edges), `0 < rB + rO`, `0 ≤ rA + rO` (radii). -/
theorem inBandQ_cast (lo hi rA rB rO : ℚ) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hB : 0 < rB + rO) (hA : 0 ≤ rA + rO) :
    inBandQ lo hi rA rB rO ↔
      GoldschmidtConforms (lo : ℝ) (hi : ℝ) (rA : ℝ) (rB : ℝ) (rO : ℝ) := by
  have hlo' : (0 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hlo
  have hhi' : (0 : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hhi
  have hB' : (0 : ℝ) < (rB : ℝ) + (rO : ℝ) := by exact_mod_cast hB
  have hA' : (0 : ℝ) ≤ (rA : ℝ) + (rO : ℝ) := by exact_mod_cast hA
  have hcast1 : (2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2) ↔
      (2 * (lo : ℝ) ^ 2 * ((rB : ℝ) + (rO : ℝ)) ^ 2 ≤ ((rA : ℝ) + (rO : ℝ)) ^ 2) := by
    rw [(Rat.cast_le (K := ℝ)).symm]
    push_cast
    rfl
  have hcast2 : ((rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2) ↔
      (((rA : ℝ) + (rO : ℝ)) ^ 2 ≤ 2 * (hi : ℝ) ^ 2 * ((rB : ℝ) + (rO : ℝ)) ^ 2) := by
    rw [(Rat.cast_le (K := ℝ)).symm]
    push_cast
    rfl
  unfold inBandQ GoldschmidtConforms
  rw [le_tolFac_iff_sq hlo' hB' hA', tolFac_le_iff_sq hhi' hB' hA']
  exact and_congr hcast1 hcast2

/-! ## `norm_num` and `decide` on concrete `ℚ` goals (dispatch (f), last sub-question)

  Measured domain of the two tactics on `ℚ`:

  | goal | `norm_num` | `decide` |
  |---|---|---|
  | `2 * (3/20 : ℚ)^2 * (401/200)^2 ≤ (71/25)^2` | **closes** | fails |
  | `(322624 : ℚ) > 321602` | closes | **closes** |
  | `(322624 : ℚ)/40000 > (321602 : ℚ)/40000` | closes | fails |
  | `(2 : ℚ) * 3 = 6` | closes | fails |
  | `(71/25 : ℚ)^2 > 2 * (401/200)^2` | **closes** | fails |

  `decide` is only reliable on a comparison of **integer literals**; any `/`, `*` or `^` in `ℚ`
  leaves `Rat.instDecidableLt` stuck at `Rat.blt` (verbatim failure text in `proofs/API-NOTES.md`).
  The `decide`-after-rewriting route that *does* work clears the division first with
  `show` + `div_lt_div_iff_of_pos_right` (see the second `example` below).
-/

example : 2 * (3 / 20 : ℚ) ^ 2 * (401 / 200) ^ 2 ≤ (71 / 25) ^ 2 := by norm_num

example : (322624 : ℚ) > 321602 := by norm_num

example : (322624 : ℚ) > 321602 := by decide

example : (2 : ℚ) * 3 = 6 := by norm_num

/-- The working `decide` route: turn the `>` into `<`, clear the common denominator, then `decide`
on the integer-literal comparison `321602 < 322624`. -/
example : (322624 : ℚ) / 40000 > (321602 : ℚ) / 40000 := by
  show (321602 : ℚ) / 40000 < (322624 : ℚ) / 40000
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 40000)]
  decide

/-! ## Measured traps on `ℚ` (the verbatim failure texts are quoted in `proofs/API-NOTES.md`)

  * **Always pin the statement to `ℚ`.** The bare goal `2 / 3 ≤ 1 / 2` silently elaborates in `ℕ`
    (where it is `0 ≤ 0`) and `norm_num` *closes* it, although the intended `ℚ` reading is **false**;
    the annotated `(2 / 3 : ℚ) ≤ 1 / 2` fails with `unsolved goals ⊢ False`. Row statements that go
    through the ℚ-parameterized definitions (`inBandQ`, `zoneQ`, `tolFacSq`) cannot hit this trap,
    because the parameters pin the type — that is an additional reason to state the instance layer
    through those definitions rather than with bare literals.
  * `norm_num` **does** evaluate `|·|` of a closed *literal* `ℚ` expression, but for a *variable* `q`
    the goal `|q| = q` stalls at `⊢ 0 ≤ q`; the side condition must be supplied:
    `norm_num [abs_of_nonneg hq]`.
  * plain `norm_num` **does** decide the concrete `inBandQ` conjunction below; `decide` does **not**
    (see the `decide` table above).
-/

example : |(3 : ℚ) - 5| = 2 := by norm_num

example (q : ℚ) (hq : 0 ≤ q) : |q| = q := by norm_num [abs_of_nonneg hq]

example : inBandQ (4 / 5) 1 (137 / 50 - 51 / 50) (401 / 200 - 51 / 50) (51 / 50) := by
  norm_num [inBandQ]

end
