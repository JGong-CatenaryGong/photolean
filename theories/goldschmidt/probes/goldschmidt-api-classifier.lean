/-
  PhotoLean — theories/goldschmidt/probes/goldschmidt-api-classifier.lean

  mathlib API calibration for the Goldschmidt theory, dispatch item (g): the computable classifier
  layer — `if`/`ite` splitting, `deriving DecidableEq` on a 3-constructor inductive, and the
  transfer row `zoneQ_eq_zone` (plan §8 G5).

  Run from the repository root:

      proofs/scripts/lake env lean theories/goldschmidt/probes/goldschmidt-api-classifier.lean

  Lean 4.17.0 + mathlib v4.17.0. `zoneQ_eq_zone` and the three `goldschmidtZone` characterization
  rows are kernel-checked end to end. Status: 0 error / 0 warning.
-/
import Mathlib

noncomputable section

/-! ## The `if` / `ite` layer and the trichotomy lemmas (verbatim `#check @`, wraps joined) -/

#check @if_pos
#check @if_neg
#check @ite_eq_iff
#check @ite_eq_iff'
#check @lt_trichotomy
#check @lt_or_ge
#check @le_or_lt
#check @lt_or_gt_of_ne
#check @lt_iff_not_ge
#check @le_iff_lt_or_eq
#check @Bool.rec
#check @decide

/-
  `if_pos` / `if_neg` are the goal-side splitters; `split_ifs with h1 … hn` is the tool when the
  hypothesis must be *consumed* (the branch bookkeeping rule is recorded in the Sabatier section of
  `proofs/API-NOTES.md` §8: in branch `i` the earlier hypotheses are negated, the `i`-th is
  positive). `deriving DecidableEq` on an inductive gives `Decidable (a = b)` by constructor
  injectivity/disjointness, so a branch mismatch is closable by `by decide` (see below).
-/

/-! ## The 3-constructor classifier (plan §1.3/§2/§8)

  Shape, **cross-checked against the statement authority**
  `theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean`:
  * `GoldschmidtZone` = `tooSmall | ideal | tooLarge`, `deriving DecidableEq` (authority line 80);
  * `goldschmidtZone lo hi t` compares the **real** factor `t` against the band edges
    (authority line 87) — identical here;
  * `zoneQ lo hi rA rB rO` compares the **inlined `ℚ` squares** `(rA+rO)^2` against
    `2 lo^2 (rB+rO)^2` (authority line 402) — *not* `tolFacSq`; the authority's body is reproduced
    verbatim below. "ideal" is the *in-band* branch (`lo ≤ t ∧ t ≤ hi`).
  The definitional body matters for the G6 evaluator: with this inlined body plain
  `norm_num [zoneQ]` already closes the concrete verdicts (with a `tolFacSq`-delegating body it does
  not — see API-NOTES §9.1). -/

/-- The three-way classifier's value type. `deriving DecidableEq` is what lets a branch mismatch be
discharged by `by decide` in the characterization rows. -/
inductive GoldschmidtZone where
  | tooSmall
  | ideal
  | tooLarge
  deriving DecidableEq

/-- Plan §2 mirror (`ℚ`) — the `√2`-free decision object (authority `Rat.tolFacSq`, line 386). -/
def tolFacSq (rA rB rO : ℚ) : ℚ := (rA + rO) ^ 2 / (2 * (rB + rO) ^ 2)

/-- Plan §2 mirror (`ℝ`). -/
def tolFac (rA rB rO : ℝ) : ℝ := (rA + rO) / (Real.sqrt 2 * (rB + rO))

/-- Plan §8 mirror: the computable classifier on `ℚ`, comparing *squares* — **the authority's body
verbatim** (`goldschmidt-statement-skeleton.lean`, `Rat.zoneQ`). -/
def zoneQ (lo hi rA rB rO : ℚ) : GoldschmidtZone :=
  if (rA + rO) ^ 2 < 2 * lo ^ 2 * (rB + rO) ^ 2 then GoldschmidtZone.tooSmall
  else if (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2 then GoldschmidtZone.ideal
  else GoldschmidtZone.tooLarge

/-- Plan §1.3/§2 mirror: the classifier on the `ℝ` factor — the authority's body verbatim. -/
def goldschmidtZone (lo hi t : ℝ) : GoldschmidtZone :=
  if t < lo then GoldschmidtZone.tooSmall
  else if t ≤ hi then GoldschmidtZone.ideal
  else GoldschmidtZone.tooLarge

/-! ## The `…_iff` characterization rows (plan §4 G1) — kernel-checked, authority shapes

  All three `…_iff` rows hold **unconditionally** in their exact form (`tooLarge` is the
  conjunction `lo ≤ t ∧ hi < t`, not `hi < t`). The *reduced* `hi < t` shape is a corollary that
  needs the band hypothesis `lo ≤ hi`: without it the reduced row is *false*, because for an
  inverted band with `hi < t < lo` the first branch wins (`tooSmall`) while `hi < t` holds. The
  authority (`goldschmidt-statement-skeleton.lean:143/147`, delivered at
  `PhotoLean/Goldschmidt/Basic.lean:179/186`) carries both rows; plan §3.1 item 4 records the
  correction. -/

theorem goldschmidtZone_eq_tooSmall_iff {lo hi t : ℝ} :
    goldschmidtZone lo hi t = GoldschmidtZone.tooSmall ↔ t < lo := by
  unfold goldschmidtZone
  by_cases h : t < lo
  · rw [if_pos h]; exact iff_of_true rfl h
  · rw [if_neg h]
    by_cases h2 : t ≤ hi
    · rw [if_pos h2]; exact iff_of_false (by decide) h
    · rw [if_neg h2]; exact iff_of_false (by decide) h

theorem goldschmidtZone_eq_ideal_iff {lo hi t : ℝ} :
    goldschmidtZone lo hi t = GoldschmidtZone.ideal ↔ lo ≤ t ∧ t ≤ hi := by
  unfold goldschmidtZone
  by_cases h : t < lo
  · rw [if_pos h]
    refine iff_of_false (by decide) ?_
    intro hc
    exact absurd hc.1 (not_le.mpr h)
  · rw [if_neg h]
    have hlo : lo ≤ t := le_of_not_gt h
    by_cases h2 : t ≤ hi
    · rw [if_pos h2]; exact iff_of_true rfl ⟨hlo, h2⟩
    · rw [if_neg h2]
      refine iff_of_false (by decide) ?_
      intro hc
      exact h2 hc.2

/-- **The delivered `tooLarge` row (authority + `PhotoLean/Goldschmidt/Basic.lean:179`)**: the exact
form is the *conjunction*, unconditional. The conjunct `lo ≤ t` cannot be dropped — for an inverted
band (`hi < t < lo`) the first test wins (`tooSmall`), with the kernel witness
`lo = 1, hi = 0, t = 1/2` (plan §3.1 item 4). -/
theorem goldschmidtZone_eq_tooLarge_iff (lo hi t : ℝ) :
    goldschmidtZone lo hi t = GoldschmidtZone.tooLarge ↔ lo ≤ t ∧ hi < t := by
  unfold goldschmidtZone
  split_ifs with h1 h2
  · exact iff_of_false (by decide) (fun hc => not_le.mpr h1 hc.1)
  · exact iff_of_false (by decide) (fun hc => not_lt.mpr h2 hc.2)
  · exact iff_of_true rfl ⟨le_of_not_gt h1, not_le.mp h2⟩

/-- The non-empty-band corollary: with `lo ≤ hi` the conjunction collapses to `hi < t`
(`PhotoLean/Goldschmidt/Basic.lean:186`). -/
theorem goldschmidtZone_eq_tooLarge_iff_of_band (lo hi t : ℝ) (h : lo ≤ hi) :
    goldschmidtZone lo hi t = GoldschmidtZone.tooLarge ↔ hi < t := by
  unfold goldschmidtZone
  split_ifs with h1 h2
  · exact iff_of_false (by decide) (not_lt.mpr (le_trans (le_of_lt h1) h))
  · exact iff_of_false (by decide) (not_lt.mpr h2)
  · exact iff_of_true rfl (not_le.mp h2)

/-- The plan §3.1 item 4 kernel witness for why the conjunct is load-bearing: at `lo = 1`, `hi = 0`,
`t = 1/2` the classifier returns `tooSmall` while `hi < t` holds, so the *dropped-conjunct* form is
false. -/
theorem goldschmidtZone_tooLarge_dropped_conjunct_false :
    goldschmidtZone 1 0 (1 / 2) = GoldschmidtZone.tooSmall ∧ (0 : ℝ) < 1 / 2 := by
  constructor
  · norm_num [goldschmidtZone]
  · norm_num

/-! ## `zoneQ_eq_zone` (plan §8 G5) — **the transfer row, kernel-checked**

  Statement (settled): for `lo hi rA rB rO : ℚ` with `0 ≤ lo`, `0 ≤ hi`, `0 ≤ rA + rO`,
  `0 < rB + rO`,

  `zoneQ lo hi rA rB rO = goldschmidtZone ↑lo ↑hi (tolFac ↑rA ↑rB ↑rO)`.

  Recipe (4 steps):
  1. `hlo' : 0 ≤ ↑lo` (and the other physical premises) by `exact_mod_cast`;
  2. the two ℝ↔ℚ **squared halves** `le_tolFac_iff_sq` / `tolFac_le_iff_sq` (below), giving
     `t < ↑lo ↔ nA^2 < 2 lo^2 nB^2` (strict, via `lt_tolFac_iff_sq`) and
     `t ≤ ↑hi ↔ nA^2 ≤ 2 hi^2 nB^2`;
  3. the two **guard equivalences** for the ℚ guards: each is
     `rw [lt_tolFac_iff_sq … / tolFac_le_iff_sq …, (Rat.cast_lt/le (K := ℝ)).symm]; push_cast; rfl`;
  4. `unfold zoneQ goldschmidtZone`, then two nested `by_cases` / `rw [if_pos …]` /
     `rw [if_neg …]` pairs; each `else`-branch guard is converted with
     `fun hc => h1 (h1iff.mpr hc)`.

  No `norm_cast`-style automation is used and `tolFacSq` is **not** involved: the authority's `zoneQ`
  inlines `(rA+rO)^2` against `2 lo^2 (rB+rO)^2`, so the guard equivalence goes through the ℝ halves
  directly. Declared hypothesis order matches the authority: `hlo hhi hB hA`. -/

/-- The `≤` half of plan §6 `conforms_iff_sq` (the engine of the guard equivalence below). -/
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

/-- The other `≤` half: `t ≤ hi ↔ (rA+rO)^2 ≤ 2 hi^2 (rB+rO)^2`. -/
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

/-- The **strict** half, by contraposition of `le_tolFac_iff_sq`: it is what the strict `tooSmall`
guard of the authority's `zoneQ` needs. -/
theorem lt_tolFac_iff_sq {rA rB rO lo : ℝ} (hlo : 0 ≤ lo) (hB : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) :
    tolFac rA rB rO < lo ↔ (rA + rO) ^ 2 < 2 * lo ^ 2 * (rB + rO) ^ 2 := by
  rw [← not_le, le_tolFac_iff_sq hlo hB hA, not_le]

theorem zoneQ_eq_zone {lo hi rA rB rO : ℚ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hB : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) : zoneQ lo hi rA rB rO =
      goldschmidtZone (lo : ℝ) (hi : ℝ) (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)) := by
  have hlo' : (0 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hlo
  have hhi' : (0 : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hhi
  have hA' : (0 : ℝ) ≤ (rA : ℝ) + (rO : ℝ) := by exact_mod_cast hA
  have hB' : (0 : ℝ) < (rB : ℝ) + (rO : ℝ) := by exact_mod_cast hB
  have h1iff : ((rA + rO) ^ 2 < 2 * lo ^ 2 * (rB + rO) ^ 2) ↔
      (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ) < (lo : ℝ)) := by
    rw [lt_tolFac_iff_sq hlo' hB' hA', (Rat.cast_lt (K := ℝ)).symm]
    push_cast
    rfl
  have h2iff : ((rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2) ↔
      (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ) ≤ (hi : ℝ)) := by
    rw [tolFac_le_iff_sq hhi' hB' hA', (Rat.cast_le (K := ℝ)).symm]
    push_cast
    rfl
  unfold zoneQ goldschmidtZone
  by_cases h1 : (rA + rO) ^ 2 < 2 * lo ^ 2 * (rB + rO) ^ 2
  · rw [if_pos h1, if_pos (h1iff.mp h1)]
  · rw [if_neg h1, if_neg (fun hc => h1 (h1iff.mpr hc))]
    by_cases h2 : (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2
    · rw [if_pos h2, if_pos (h2iff.mp h2)]
    · rw [if_neg h2, if_neg (fun hc => h2 (h2iff.mpr hc))]

/-- Plan §8 mirror of the ℚ band criterion — **the authority's body verbatim**
(`Rat.inBandQ`, `goldschmidt-statement-skeleton.lean` line 389). -/
def inBandQ (lo hi rA rB rO : ℚ) : Prop :=
  2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 ∧ (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2

/-- **`zoneQ_ideal_iff`** (authority line 449) — the classifier's `ideal` branch is exactly the
band predicate. Complete proof; note that `by decide` is only used *after* the `if` has been
resolved by `rw [if_pos/if_neg …]` (a `decide` before that would hit the ℚ-comparison stall). -/
theorem zoneQ_ideal_iff (lo hi rA rB rO : ℚ) :
    zoneQ lo hi rA rB rO = GoldschmidtZone.ideal ↔ inBandQ lo hi rA rB rO := by
  unfold zoneQ inBandQ
  by_cases h1 : (rA + rO) ^ 2 < 2 * lo ^ 2 * (rB + rO) ^ 2
  · rw [if_pos h1]
    refine iff_of_false (by decide) ?_
    intro hc
    exact absurd hc.1 (not_le.mpr h1)
  · rw [if_neg h1]
    by_cases h2 : (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2
    · rw [if_pos h2]
      exact iff_of_true rfl ⟨not_lt.mp h1, h2⟩
    · rw [if_neg h2]
      refine iff_of_false (by decide) ?_
      intro hc
      exact h2 hc.2

/-- Concrete non-vacuity of the transfer: the `SrTiO₃` sums of plan §9 in the classic band
`[4/5, 1]` — the `ℚ` classifier and the `ℝ` classifier agree on this row (they must both yield
`tooLarge`, since `(71/25)^2 > 2·(401/200)^2`). -/
example : zoneQ (4 / 5) 1 (71 / 25 - 51 / 50) (401 / 200 - 51 / 50) (51 / 50) =
    goldschmidtZone ((4 / 5 : ℚ) : ℝ) ((1 : ℚ) : ℝ)
      (tolFac ((71 / 25 - 51 / 50 : ℚ) : ℝ) ((401 / 200 - 51 / 50 : ℚ) : ℝ)
        ((51 / 50 : ℚ) : ℝ)) :=
  zoneQ_eq_zone (lo := 4 / 5) (hi := 1) (rA := 71 / 25 - 51 / 50) (rB := 401 / 200 - 51 / 50)
    (rO := 51 / 50) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The G6 verdict recipe: with the authority's inlined `zoneQ` body, plain `norm_num [zoneQ]`
evaluates the concrete `if`-cascade (`SrTiO₃` at the classic band `[4/5, 1]` is `tooLarge`). -/
example : zoneQ (4 / 5) 1 (71 / 25 - 51 / 50) (401 / 200 - 51 / 50) (51 / 50) =
    GoldschmidtZone.tooLarge := by
  norm_num [zoneQ]

/-- The `ideal` branch of the same recipe (`CaTiO₃` at `[4/5, 1]`). -/
example : zoneQ (4 / 5) 1 (137 / 50 - 51 / 50) (401 / 200 - 51 / 50) (51 / 50) =
    GoldschmidtZone.ideal := by
  norm_num [zoneQ]

/-- The `zoneQ_ideal_iff` recipe on a concrete row: the ideal verdict is the band predicate. -/
example : inBandQ (4 / 5) 1 (137 / 50 - 51 / 50) (401 / 200 - 51 / 50) (51 / 50) :=
  (zoneQ_ideal_iff _ _ _ _ _).mp (by norm_num [zoneQ])

/-! ## Why the *quotient* form of `zoneQ` must not be used (measured divergence)

  A tempting reformulation of the first guard is `tolFacSq rA rB rO < lo^2` with
  `tolFacSq = (rA+rO)^2 / (2*(rB+rO)^2)`. It agrees with the authority's inlined form **only under
  `rB + rO ≠ 0`**: at `rB + rO = 0` the quotient is `x / 0 = 0` in `ℚ`, so the first guard becomes
  `0 < lo^2` (true whenever `lo ≠ 0`) and the classifier reports `tooSmall` where the authority
  reports `tooLarge`; the authority's unconditional `zoneQ_ideal_iff` then fails too. The definition
  below exists **only** to document that divergence — it is not the delivered definition and must
  not be used. -/

/-- DO NOT USE — the quotient-shaped guard, kept solely as the kernel witness of the divergence. -/
def zoneQQuotientForm (lo hi rA rB rO : ℚ) : GoldschmidtZone :=
  if tolFacSq rA rB rO < lo ^ 2 then GoldschmidtZone.tooSmall
  else if tolFacSq rA rB rO ≤ hi ^ 2 then GoldschmidtZone.ideal
  else GoldschmidtZone.tooLarge

/-- Divergence witness 1, at `rA = 0`, `rB = -1`, `rO = 1` (so `rB + rO = 0`): the authority's
classifier says `tooLarge`, the quotient form says `tooSmall`. -/
theorem zoneQ_quotient_form_diverges :
    zoneQ 1 1 0 (-1) 1 = GoldschmidtZone.tooLarge ∧
      zoneQQuotientForm 1 1 0 (-1) 1 = GoldschmidtZone.tooSmall := by
  constructor <;> norm_num [zoneQ, zoneQQuotientForm, tolFacSq]

/-- Divergence witness 2: with the quotient form the authority's unconditional `zoneQ_ideal_iff`
would be **false** — the quotient form returns `ideal` while `inBandQ` is false. -/
theorem zoneQ_quotient_form_breaks_ideal_iff :
    zoneQQuotientForm 0 1 0 (-1) 1 = GoldschmidtZone.ideal ∧ ¬ inBandQ 0 1 0 (-1) 1 := by
  constructor
  · norm_num [zoneQQuotientForm, tolFacSq]
  · norm_num [inBandQ]

end
