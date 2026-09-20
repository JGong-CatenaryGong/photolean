/-
theories/hammond/probes/hammond-audit-b.lean — adversarial audit of H1 (`PhotoLean.Hammond.Basic`)
and H5a (`PhotoLean.Hammond.RatModel`). Owner: prover_b.

This is an AUDIT, not a delivery: every check is chosen so that it *could* fail, and each one
carries a one-line statement of what it establishes. Unlike
`theories/hammond/probes/hammond-lead-audit.lean` (which copies the definitions inline), this
probe imports the delivered modules, so every check below is about the executed objects — the
definitions and the theorems actually shipped, not a transcription of them.

Sections:
  §0  shared independent boundary facts (used by the later sections, all from the definitions)
  A   hypothesis necessity — kernel counterexamples against the delivered statements, plus the
      tightness analysis of `0 < lam` for each of the seven zone characterizations
  B   boundary / degeneracy truth (`x = ±lam`, `x = 0`, tiny `lam`, both sign conventions, ℚ side)
  C   non-vacuity and refutability of every predicate, with kernel witnesses
  D   classifier integrity — a 13-point grid (`0 < lam`) where all seven characterization guards
      must decide exactly as the expected branch requires, plus ℚ-side points
  E   independence / anti-circularity — re-derivations straight from the definitions, without
      calling any delivered H1 theorem
  G   H5a — the same necessity/tightness checks on the ℚ layer and the content of the Marcus
      cross-link (`beyondReactant ↔ inverted`)
  F   axiom-dependency spot check of the audit itself and of the delivered H1/H5a theorems

This file contains no unproved placeholder and no custom axiom.
-/
import PhotoLean.Hammond.Basic
import PhotoLean.Hammond.RatModel

namespace PhotoLean

namespace Hammond

/-! ## Local decision procedures for the seven-branch classifiers -/

/-- Decide the ℝ classifier at concrete literals (the recipe verified by the lead's probe:
unfold, split the `if`-chain, close each leaf by `rfl` / `decide` / `norm_num`). -/
macro "zone_decide" : tactic =>
  `(tactic| (unfold hammondZone; split_ifs <;> first | rfl | decide | norm_num at *))

/-- Same decision procedure on the ℚ mirror; `decide` can get stuck on the `HZone` comparison
there, and the `norm_num at *` fallback carries those leaves. -/
macro "zoneQ_decide" : tactic =>
  `(tactic| (unfold Rat.hammondZoneQ; split_ifs <;> first | rfl | decide | norm_num at *))

/-- Close one ℝ grid record: the classifier value by `zone_decide`, then each of the seven literal
characterization guards by `norm_num` (they must all decide exactly as expected). -/
macro "zone_grid" : tactic =>
  `(tactic| refine ⟨by zone_decide, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num⟩)

/-- Close one ℚ grid record: the same eight checks with the ℚ classifier. -/
macro "zoneQ_grid" : tactic =>
  `(tactic| refine ⟨by zoneQ_decide, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num⟩)

/-! ## §0. Shared independent boundary facts (re-derived from the definitions only)

These are the load-bearing boundary values of the model, proved here without calling the delivered
H1 theorems, so that sections A–E and G can use them without circularity. -/

/-- Boundary value at the rate-maximizing driving force: `tsCoord lam lam = 0` for EVERY `lam`
(the delivered `tsCoord_at_lam` carries a `lam ≠ 0` premise that this proof does not need). -/
theorem audit_tsCoord_at_lam (lam : ℝ) : tsCoord lam lam = 0 := by
  unfold tsCoord
  rw [sub_self, zero_div]

/-- Opposite boundary: `tsCoord lam (-lam) = 1`, i.e. the reverse barrierless point has the
transition state at the product geometry. -/
theorem audit_tsCoord_neg_lam {lam : ℝ} (hlam : lam ≠ 0) : tsCoord lam (-lam) = 1 := by
  unfold tsCoord
  rw [sub_neg_eq_add, ← two_mul, div_self (mul_ne_zero two_ne_zero hlam)]

/-- Thermoneutrality: `tsCoord lam 0 = 1 / 2` (independent route through `div_eq_div_iff`). -/
theorem audit_tsCoord_zero {lam : ℝ} (hlam : lam ≠ 0) : tsCoord lam 0 = 1 / 2 := by
  unfold tsCoord
  rw [sub_zero, div_eq_div_iff (mul_ne_zero two_ne_zero hlam) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- The mid-regime value used for the non-vacuity witnesses: `tsCoord lam (lam/2) = 1/4`. -/
theorem audit_tsCoord_half_lam {lam : ℝ} (hlam : lam ≠ 0) : tsCoord lam (lam / 2) = 1 / 4 := by
  unfold tsCoord
  field_simp
  ring

/-- The mirror mid-regime value: `tsCoord lam (-(lam/2)) = 3/4`. -/
theorem audit_tsCoord_neg_half_lam {lam : ℝ} (hlam : lam ≠ 0) :
    tsCoord lam (-(lam / 2)) = 3 / 4 := by
  unfold tsCoord
  field_simp
  ring

/-! ## A. Hypothesis necessity — kernel counterexamples against the delivered statements -/

/- A1: `tsCoord_mem_iff` without its `0 < lam` premise fails at `lam = -3`, `x = 0`:
the left side is `0 < 1/2 ∧ 1/2 < 1` (true) while `ReactionRegion (-3) 0` is empty. -/
example : ¬ (0 < tsCoord (-3) 0 ∧ tsCoord (-3) 0 < 1 ↔ ReactionRegion (-3) 0) := by
  norm_num [tsCoord, ReactionRegion]

/- A2: the same failure is systematic, not a single point: for EVERY `lam < 0` there is an `x`
(namely `0`) where the two sides of `tsCoord_mem_iff` disagree — the `0 < lam` premise is
necessary, not decorative. -/
theorem audit_tsCoord_mem_iff_fails_of_neg {lam : ℝ} (hlam : lam < 0) :
    ¬ (∀ x : ℝ, (0 < tsCoord lam x ∧ tsCoord lam x < 1 ↔ ReactionRegion lam x)) := by
  intro hall
  have hz : tsCoord lam 0 = 1 / 2 :=
    audit_tsCoord_zero (ne_of_lt hlam)
  have hiff := hall 0
  rw [hz] at hiff
  have hnot : ¬ ReactionRegion lam 0 := by
    unfold ReactionRegion
    intro hc
    linarith [hc.1, hc.2]
  exact hnot (hiff.mp ⟨by norm_num, by norm_num⟩)

/- A3: at the degenerate curvature `lam = 0` the equivalence of A1 still HOLDS for every `x`
(both sides are false) — measured sharpness of the premise: it fails for `lam < 0` and not at
`lam = 0`, so the tight premise is `0 ≤ lam`. -/
example (x : ℝ) : (0 < tsCoord 0 x ∧ tsCoord 0 x < 1 ↔ ReactionRegion 0 x) := by
  unfold tsCoord ReactionRegion
  simp only [mul_zero, div_zero, zero_sub, neg_zero]
  constructor <;> intro h <;> linarith [h.1, h.2]

/- A4: `gapProduct_sub_gapReactant` without `lam ≠ 0` fails at `lam = 0`, `x = 1`: both barriers
collapse to `0` by the `x / 0 = 0` convention, so the difference is `0`, not `1`. -/
example : gapProduct 0 1 - gapReactant 0 1 ≠ 1 := by
  norm_num [gapProduct, gapReactant]

/- A5: `tsCoord_neg` without `lam ≠ 0` fails at `lam = 0`: the left side is `0` while
`1 - tsCoord 0 1` is `1`. -/
example : tsCoord 0 (-1) ≠ 1 - tsCoord 0 1 := by
  norm_num [tsCoord]

/- A6: `tsCoord_zero` without `lam ≠ 0` fails at `lam = 0`: the zero-curvature coordinate is `0`,
not `1/2` (the `x / 0 = 0` convention is what makes this branch true). -/
example : tsCoord 0 0 ≠ 1 / 2 := by
  norm_num [tsCoord]

/- A7: `crossing_iff` without `lam ≠ 0` fails at `lam = 0`, `dG = 1`, `q = 0`: the two surfaces
coincide there (`0 = 1` is false) while `q = tsCoord 0 (-1)` is true. -/
example : ¬ (reactantSurface 0 0 = productSurface 0 1 0 ↔ (0 : ℝ) = tsCoord 0 (-1)) := by
  norm_num [reactantSurface, productSurface, tsCoord]

/- A8: `hammondZone_eq_half_iff` without `0 < lam` fails at `lam = -1`, `x = 0`: the classifier
fires `beyondProduct` (since `0 < -lam`) although the algebraic condition `x = 0` is true. -/
example : ¬ (hammondZone (-1) 0 = HZone.half ↔ (0 : ℝ) = 0) := by
  zone_decide

/- A9: `hammondZone_eq_atProduct_iff` without `0 < lam` fails at `lam = 0`, `x = 0`: the first
branch (`x = lam`) fires, so the classifier returns `atReactant`, while `x = -lam` also holds —
the two boundary characterizations are not separated without a sign premise. -/
example : ¬ (hammondZone 0 0 = HZone.atProduct ↔ (0 : ℝ) = -(0 : ℝ)) := by
  zone_decide

/- A10: `hammondZone_eq_beyondReactant_iff` without `0 < lam` fails at `lam = -1`, `x = 1 = -lam`:
the classifier fires `atProduct` while `lam < x` is true. -/
example : ¬ (hammondZone (-1) 1 = HZone.beyondReactant ↔ (-1 : ℝ) < 1) := by
  zone_decide

/- A11: `hammondZone_eq_beyondProduct_iff` without `0 < lam` fails at `lam = -1`, `x = -1 = lam`:
the classifier fires `atReactant` while `x < -lam` is true. -/
example : ¬ (hammondZone (-1) (-1) = HZone.beyondProduct ↔ (-1 : ℝ) < -(-1 : ℝ)) := by
  zone_decide

/- A12: the `half` failure of A8 is systematic for every non-positive curvature: at `x = 0` the
classifier returns `atReactant` (when `lam = 0`) or `beyondProduct` (when `lam < 0`), never
`half`, while the algebraic condition `x = 0` holds. -/
theorem audit_half_iff_fails_of_nonpos {lam : ℝ} (hlam : lam ≤ 0) :
    ¬ (hammondZone lam 0 = HZone.half ↔ (0 : ℝ) = 0) := by
  have h : hammondZone lam 0 ≠ HZone.half := by
    rcases lt_or_eq_of_le hlam with hlt | heq
    · unfold hammondZone
      rw [if_neg (by intro hh; linarith), if_neg (by intro hh; linarith),
        if_pos (by linarith)]
      simp
    · subst heq
      simp [hammondZone]
  simpa using h

/- A13: `beyondReactant` also fails systematically on the negative side: at `x = -lam` the
classifier fires `atProduct` while `lam < -lam` is true for every `lam < 0`. -/
theorem audit_beyondReactant_iff_fails_of_neg {lam : ℝ} (hlam : lam < 0) :
    ¬ (hammondZone lam (-lam) = HZone.beyondReactant ↔ lam < -lam) := by
  have h : hammondZone lam (-lam) = HZone.atProduct := by
    unfold hammondZone
    rw [if_neg (by intro hh; linarith), if_pos rfl]
  rw [h]
  simp only [reduceCtorEq, false_iff, not_not]
  linarith

/- A14: `beyondProduct` fails systematically on the negative side as well: at `x = lam` the
classifier fires `atReactant` while `lam < -lam` (i.e. `x < -lam`) is true for every `lam < 0`. -/
theorem audit_beyondProduct_iff_fails_of_neg {lam : ℝ} (hlam : lam < 0) :
    ¬ (hammondZone lam lam = HZone.beyondProduct ↔ lam < -lam) := by
  have h : hammondZone lam lam = HZone.atReactant := by
    unfold hammondZone
    rw [if_pos rfl]
  rw [h]
  simp only [reduceCtorEq, false_iff, not_not]
  linarith

/- A15: tightness on the other side — the `early` characterization needs NO sign premise at all:
`0 < lam` is redundant there (the early branch is unreachable when `lam ≤ 0` and the algebraic
condition is then empty too). -/
theorem audit_early_iff_no_hyp (lam x : ℝ) :
    hammondZone lam x = HZone.early ↔ 0 < x ∧ x < lam := by
  constructor
  · intro h
    unfold hammondZone at h
    split_ifs at h with h1 h2 h3 h4 h5 h6
    exact ⟨h6, lt_of_le_of_ne (le_of_not_gt h4) h1⟩
  · rintro ⟨h1, h2⟩
    unfold hammondZone
    rw [if_neg (ne_of_lt h2), if_neg (by linarith), if_neg (by linarith),
      if_neg (not_lt.mpr (le_of_lt h2)), if_neg (ne_of_gt h1), if_pos h1]

/- A16: the same for `late`: the `0 < lam` premise is redundant (the late branch is unreachable
when `lam ≤ 0` and the algebraic condition is empty there as well). -/
theorem audit_late_iff_no_hyp (lam x : ℝ) :
    hammondZone lam x = HZone.late ↔ x < 0 ∧ -lam < x := by
  constructor
  · intro h
    unfold hammondZone at h
    split_ifs at h with h1 h2 h3 h4 h5 h6
    exact ⟨lt_of_le_of_ne (le_of_not_gt h6) h5, lt_of_le_of_ne (le_of_not_gt h3) (Ne.symm h2)⟩
  · rintro ⟨h1, h2⟩
    unfold hammondZone
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith),
      if_neg (by linarith), if_neg (by linarith)]

/- A17: and for `atReactant`: the premise is redundant because the first branch of the chain
already decides the value. -/
theorem audit_atReactant_iff_no_hyp (lam x : ℝ) :
    hammondZone lam x = HZone.atReactant ↔ x = lam := by
  constructor
  · intro h
    unfold hammondZone at h
    split_ifs at h with h1 h2 h3 h4 h5 h6
    exact h1
  · intro h
    rw [h]
    unfold hammondZone
    rw [if_pos rfl]

/- A18: `atProduct` is the one characterization sharpened by the *positive* form of the premise:
`lam ≠ 0` already suffices (the `0 < lam` of the delivered statement is stronger than necessary). -/
theorem audit_atProduct_iff_of_ne {lam x : ℝ} (hlam : lam ≠ 0) :
    hammondZone lam x = HZone.atProduct ↔ x = -lam := by
  constructor
  · intro h
    unfold hammondZone at h
    split_ifs at h with h1 h2 h3 h4 h5 h6
    exact h2
  · intro h
    rw [h]
    unfold hammondZone
    rw [if_neg (by intro hh; exact hlam (by linarith)), if_pos rfl]

/- A19: `reactionRegion_pos`'s conclusion is forced: the Hammond region is empty for every
non-positive curvature — re-derived here independently of the delivered
`not_reactionRegion_of_nonpos`. -/
theorem audit_not_reactionRegion_of_nonpos {lam x : ℝ} (hlam : lam ≤ 0) :
    ¬ ReactionRegion lam x := by
  intro h
  unfold ReactionRegion at h
  linarith [h.1, h.2]

/- A20: the sharp form of A19: a driving force in the Hammond regime EXISTS exactly when the
curvature is positive (witness `x = 0` for the reverse direction), so the existence claim of
`reactionRegion_pos` is not only forced but characterizes the physical sign. -/
theorem audit_exists_reactionRegion_iff (lam : ℝ) : (∃ x, ReactionRegion lam x) ↔ 0 < lam := by
  constructor
  · rintro ⟨x, hx⟩
    unfold ReactionRegion at hx
    linarith [hx.1, hx.2]
  · intro h
    exact ⟨0, by unfold ReactionRegion; constructor <;> linarith⟩

/- A21: tightness of `gapReactant_eq_crossing_energy`: at `lam = 0` its `lam ≠ 0` premise is
redundant — both sides collapse to `0` under the `x / 0 = 0` convention, so this premise is not
load-bearing at the degenerate point. -/
example (dG : ℝ) : gapReactant 0 (-dG) = reactantSurface 0 (tsCoord 0 (-dG)) := by
  simp [gapReactant, reactantSurface, tsCoord]

/- A22: same for the well-referenced reverse-barrier identity: at `lam = 0` both sides vanish, so
its `lam ≠ 0` premise is redundant there as well. -/
example (dG : ℝ) : gapProduct 0 (-dG) = productSurface 0 dG (tsCoord 0 (-dG)) - dG := by
  simp [gapProduct, productSurface, tsCoord]

/- A23: `gapProduct_eq_gapReactant_neg` carries no premise, which is correct: the identity is a
polynomial identity and survives the degenerate curvature (`0 = 0`). -/
example : gapProduct 0 5 = gapReactant 0 (-5) := by norm_num [gapProduct, gapReactant]

/- A24: hypothesis non-vacuity — every premise pattern used by the delivered H1 theorems is
satisfiable (`0 < lam` at `lam = 3`, `lam ≠ 0` at `lam = -3`, `lam ≤ 0` at `lam = -1`, and
`ReactionRegion lam x` at `(1, 0)`), so none of the delivered statements is vacuously true. -/
example : (0 : ℝ) < 3 ∧ (-3 : ℝ) ≠ 0 ∧ (-1 : ℝ) ≤ 0 ∧ ReactionRegion 1 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num [ReactionRegion]

/-! ## B. Boundary / degeneracy truth

The three boundary values (`x = lam`, `x = -lam`, `x = 0`) are proved symbolically in §0; here are
the regime boundary equivalences, the tiny-curvature limit, both sign conventions and the ℚ
mirror. -/

/- B1: the forward regime boundary is exact: `tsCoord lam x = 0 ↔ x = lam` for `0 < lam` (not
merely the one-sided `tsCoord lam lam = 0` of §0). -/
theorem audit_tsCoord_eq_zero_iff {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x = 0 ↔ x = lam := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold tsCoord at h
    rw [div_eq_zero_iff, sub_eq_zero] at h
    rcases h with h | h
    · exact h.symm
    · exact absurd h (by linarith)
  · rw [h]; exact audit_tsCoord_at_lam lam

/- B2: the reverse regime boundary is exact: `tsCoord lam x = 1 ↔ x = -lam` for `0 < lam`. -/
theorem audit_tsCoord_eq_one_iff {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x = 1 ↔ x = -lam := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold tsCoord at h
    rw [div_eq_one_iff_eq (by linarith : (2 * lam : ℝ) ≠ 0)] at h
    linarith
  · rw [h]; exact audit_tsCoord_neg_lam (ne_of_gt hlam)

/- B3: tiny but positive curvature behaves exactly like the physical branch: the boundary values
and the regime classification survive at `lam = 10⁻⁶`. -/
example : tsCoord (1 / 1000000) 0 = 1 / 2 ∧ tsCoord (1 / 1000000) (1 / 1000000) = 0
    ∧ tsCoord (1 / 1000000) (-(1 / 1000000)) = 1 := by
  norm_num [tsCoord]

/- B4: tiny curvature still admits a non-empty Hammond region, and the barrierless boundary is
still excluded from it (strictness is not lost in the small-`lam` limit). -/
example : ReactionRegion (1 / 1000000) 0 ∧ ¬ ReactionRegion (1 / 1000000) (1 / 1000000) := by
  norm_num [ReactionRegion]

/- B5: the two sign conventions meet at the crossing point: with `dG = 1` (i.e. `x = -dG = -1`)
the reactant and product surfaces coincide at `q = tsCoord 3 (-1) = 2/3`. -/
example : reactantSurface 3 (tsCoord 3 (-1)) = productSurface 3 1 (tsCoord 3 (-1)) := by
  norm_num [reactantSurface, productSurface, tsCoord]

/- B6: negative control for B5: away from the crossing point the surfaces differ, so B5 is not a
tautology of the surface definitions. -/
example : reactantSurface 3 0 ≠ productSurface 3 1 0 := by
  norm_num [reactantSurface, productSurface]

/- B7: the well-referenced reverse barrier of the delivered `gapProduct_eq_crossing_energy` holds
at `lam = 3`, `dG = -1`: `gapProduct lam (-dG) = productSurface lam dG (tsCoord lam (-dG)) - dG`. -/
example : gapProduct 3 1 = productSurface 3 (-1) (tsCoord 3 1) - (-1) := by
  norm_num [gapProduct, productSurface, tsCoord]

/- B8: the `- dG` in B7 is necessary: the un-referenced form is off by exactly `dG`, so the
delivered statement cannot be weakened to it. -/
example : gapProduct 3 1 ≠ productSurface 3 (-1) (tsCoord 3 1) := by
  norm_num [gapProduct, productSurface, tsCoord]

/- B9: the forward-barrier identity at the same data point (`lam = 3`, `dG = 1` → `x = -1`): the
barrier is the reactant-surface energy at the crossing point `tsCoord 3 (-1) = 2/3`. -/
example : gapReactant 3 (-1) = reactantSurface 3 (tsCoord 3 (-1)) := by
  norm_num [gapReactant, reactantSurface, tsCoord]

/- B10: negative control for B9 — pairing the barrier with the WRONG crossing point (`tsCoord 3 1`
instead of `tsCoord 3 (-1)`) breaks the identity, so the `-dG` argument of the delivered
`gapReactant_eq_crossing_energy` is load-bearing. -/
example : gapReactant 3 (-1) ≠ reactantSurface 3 (tsCoord 3 1) := by
  norm_num [gapReactant, reactantSurface, tsCoord]

/- B11: both sign conventions for the same data point: `tsCoord 3 (-1) = 1 - tsCoord 3 1`, i.e.
the reverse reaction's coordinate mirrors the forward one — checked at the model's numbers. -/
example : tsCoord 3 (-1) = 1 - tsCoord 3 1 := by norm_num [tsCoord]

/- B12: the zero-curvature degeneracy is the formal convention, not physics: `tsCoord 0 x = 0`
for every `x`, and in particular the "thermoneutral" value `1/2` is NOT attained there. -/
example : tsCoord 0 5 = 0 ∧ tsCoord 0 0 ≠ 1 / 2 := by norm_num [tsCoord]

/- B13: the ℚ mirror reproduces all three boundary values symbolically. -/
theorem audit_tsCoordQ_at_lam (lam : ℚ) : Rat.tsCoordQ lam lam = 0 := by
  unfold Rat.tsCoordQ
  rw [sub_self, zero_div]

theorem audit_tsCoordQ_neg_lam {lam : ℚ} (hlam : lam ≠ 0) : Rat.tsCoordQ lam (-lam) = 1 := by
  unfold Rat.tsCoordQ
  rw [sub_neg_eq_add, ← two_mul, div_self (mul_ne_zero two_ne_zero hlam)]

theorem audit_tsCoordQ_zero {lam : ℚ} (hlam : lam ≠ 0) : Rat.tsCoordQ lam 0 = 1 / 2 := by
  unfold Rat.tsCoordQ
  rw [sub_zero, div_eq_div_iff (mul_ne_zero two_ne_zero hlam) (by norm_num : (2 : ℚ) ≠ 0)]
  ring

/- B14: the ℚ regime boundaries are exact as well (`lam ≠ 0` is needed for the `0`-side; `0 < lam`
gives both directions of the `1`-side). -/
theorem audit_tsCoordQ_eq_zero_iff {lam x : ℚ} (hlam : 0 < lam) :
    Rat.tsCoordQ lam x = 0 ↔ x = lam := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold Rat.tsCoordQ at h
    rw [div_eq_zero_iff, sub_eq_zero] at h
    rcases h with h | h
    · exact h.symm
    · exact absurd h (by linarith)
  · rw [h]; exact audit_tsCoordQ_at_lam lam

theorem audit_tsCoordQ_eq_one_iff {lam x : ℚ} (hlam : 0 < lam) :
    Rat.tsCoordQ lam x = 1 ↔ x = -lam := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold Rat.tsCoordQ at h
    rw [div_eq_one_iff_eq (by linarith : (2 * lam : ℚ) ≠ 0)] at h
    linarith
  · rw [h]; exact audit_tsCoordQ_neg_lam (ne_of_gt hlam)

/- B15: ℚ barrier degeneracy: the rational forward barrier vanishes exactly at `x = lam`
(`lam ≠ 0`), the ℚ-side analogue of the ℝ statement. -/
theorem audit_gapReactantQ_eq_zero_iff {lam x : ℚ} (hlam : lam ≠ 0) :
    Rat.gapReactantQ lam x = 0 ↔ x = lam := by
  have h4 : (4 * lam : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hlam
  unfold Rat.gapReactantQ
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have hlx : lam - x = 0 := sq_eq_zero_iff.mp h
      exact (sub_eq_zero.mp hlx).symm
    · exact absurd h h4
  · intro h; exact Or.inl (by rw [h]; ring)

/- B16: ℚ numeric boundary values at the literature instance parameters (`lam = 6/5`), including
a kernel computation that is *computational* over `Rat` and a cast to ℝ — the decision layer's
evidence chain in miniature. -/
example : Rat.tsCoordQ (6 / 5) (6 / 5) = 0 ∧ Rat.tsCoordQ (6 / 5) (-(6 / 5)) = 1
    ∧ Rat.tsCoordQ (6 / 5) 0 = 1 / 2 := by
  norm_num [Rat.tsCoordQ]

/- B17: the ℚ → ℝ casts agree at the degenerate curvature `lam = 0`: the `x / 0 = 0` convention
is preserved by the cast, so the delivered cast lemmas are not silently excluding that branch. -/
example : ((Rat.tsCoordQ 0 5 : ℚ) : ℝ) = tsCoord (0 : ℝ) 5
    ∧ ((Rat.gapReactantQ 0 5 : ℚ) : ℝ) = gapReactant (0 : ℝ) 5 := by
  norm_num [Rat.tsCoordQ, Rat.gapReactantQ, tsCoord, gapReactant]

/-! ## C. Non-vacuity and refutability (kernel witnesses) -/

/- C1: `ReactantLike` is inhabited for every positive curvature (witness `x = lam/2`, coordinate
`1/4 < 1/2`). -/
theorem audit_exists_reactantLike {lam : ℝ} (hlam : 0 < lam) : ∃ x, ReactantLike lam x := by
  refine ⟨lam / 2, ?_⟩
  unfold ReactantLike
  rw [audit_tsCoord_half_lam (ne_of_gt hlam)]
  norm_num

/- C2: `ProductLike` is inhabited for every positive curvature (witness `x = -lam/2`, coordinate
`3/4 > 1/2`). -/
theorem audit_exists_productLike {lam : ℝ} (hlam : 0 < lam) : ∃ x, ProductLike lam x := by
  refine ⟨-(lam / 2), ?_⟩
  unfold ProductLike
  rw [audit_tsCoord_neg_half_lam (ne_of_gt hlam)]
  norm_num

/- C3: `ReactionRegion` is inhabited for every positive curvature (witness `x = 0`). -/
theorem audit_exists_reactionRegion {lam : ℝ} (hlam : 0 < lam) : ∃ x, ReactionRegion lam x := by
  refine ⟨0, ?_⟩
  unfold ReactionRegion
  constructor <;> linarith

/- C4: `ReactionRegion` is also refutable at the same curvature (witness `x = 2 * lam`), so the
regime predicate is a strict sub-interval, not everything. -/
theorem audit_exists_not_reactionRegion {lam : ℝ} (hlam : 0 < lam) :
    ∃ x, ¬ ReactionRegion lam x := by
  refine ⟨2 * lam, ?_⟩
  unfold ReactionRegion
  intro h
  linarith [h.2]

/- C5: `HammondDescriptor` is satisfied by the physical curvature `lam = 1` (the family-level
statement is not vacuous). -/
theorem audit_descriptor_one : HammondDescriptor 1 := by
  intro x₁ x₂ h
  unfold tsCoord
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2 * 1)]
  linarith

/- C6: `HammondDescriptor` is refuted at the degenerate curvature `lam = 0`. -/
example : ¬ HammondDescriptor 0 := by
  intro hd
  have h := hd 0 1 (by norm_num)
  norm_num [tsCoord] at h

/- C7: `HammondDescriptor` is refuted at the negative curvature `lam = -1/2` (the descriptor is
not just degenerate at `0`). -/
example : ¬ HammondDescriptor (-(1 / 2)) := by
  intro hd
  have h := hd 0 1 (by norm_num)
  norm_num [tsCoord] at h

/- C8: the two resemblance predicates are disjoint: they can never both classify one transition
state (a consistency check on the two strict inequalities defining them). -/
theorem audit_reactantLike_not_productLike (lam x : ℝ) :
    ¬ (ReactantLike lam x ∧ ProductLike lam x) := by
  rintro ⟨h1, h2⟩
  unfold ReactantLike at h1
  unfold ProductLike at h2
  linarith

/- C9: `ReactantLike` has the intended physical meaning (not a vacuous predicate): it forces an
exergonic driving force `x > 0`. -/
theorem audit_reactantLike_pos {lam x : ℝ} (hlam : 0 < lam) (h : ReactantLike lam x) : 0 < x := by
  unfold ReactantLike tsCoord at h
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  have h3 : lam - x < (1 / 2) * (2 * lam) := (div_lt_iff₀ h2).mp h
  linarith

/- C10: `ProductLike` likewise forces an endergonic driving force `x < 0`. -/
theorem audit_productLike_neg {lam x : ℝ} (hlam : 0 < lam) (h : ProductLike lam x) : x < 0 := by
  unfold ProductLike tsCoord at h
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  have h3 : (1 / 2) * (2 * lam) < lam - x := (lt_div_iff₀ h2).mp h
  linarith

/- C11: the verdict predicate `HammondConforms` is inhabited (`lam = 1`, `x = 0`) and refutable
(`lam = 1`, `x = 1`: the barrierless boundary is NOT a conforming instance). -/
example : HammondConforms 1 0 ∧ ¬ HammondConforms 1 1 := by
  constructor
  · norm_num [HammondConforms, ReactionRegion]
  · norm_num [HammondConforms, ReactionRegion]

/- C12: the non-physical branch is rejected by the verdict for both signs (`lam = -1/2` and
`lam = 0`), so the verdict's domain constraint is enforced by its definition. -/
example : ¬ HammondConforms (-(1 / 2)) 0 ∧ ¬ HammondConforms 0 0 := by
  constructor <;> norm_num [HammondConforms, ReactionRegion]

/- C13: the verdict's positivity constraint is extractable from the definition alone (no H3
theorem is called): `HammondConforms lam x → 0 < lam`. -/
theorem audit_conforms_pos {lam x : ℝ} (h : HammondConforms lam x) : 0 < lam := h.1

/-! ## D. Classifier integrity — 13-point grid over `0 < lam`

Each record is `hammondZone lam x = <expected branch> ∧ <expected guard> ∧ ¬ <other six guards>`.
The classifier value is decided by `zone_decide`; the seven literal guards are decided by
`norm_num`. This is a semantic check of the classifier itself, independent of the delivered
`hammondZone_eq_*_iff` lemmas. Grid points G1–G7 walk the whole chain at `lam = 3`; G8–G10 are the
textbook instances of the plan (`lam = 1`, including the barrierless boundary `x = lam`); G11–G13
are the literature parameter pairs of the plan's I5/I6/I7; G14-G16 are the ℚ-side mirror. -/

/- G1: `lam = 3`, `x = 1` — middle region on the exergonic side: only `0 < x ∧ x < lam` fires. -/
example : hammondZone 3 1 = HZone.early ∧ (0 < (1 : ℝ) ∧ (1 : ℝ) < 3)
    ∧ ¬ ((1 : ℝ) = 0) ∧ ¬ ((1 : ℝ) < 0 ∧ -(3 : ℝ) < (1 : ℝ)) ∧ ¬ ((1 : ℝ) = 3)
    ∧ ¬ ((1 : ℝ) = -(3 : ℝ)) ∧ ¬ ((3 : ℝ) < (1 : ℝ)) ∧ ¬ ((1 : ℝ) < -(3 : ℝ)) := by
  zone_grid

/- G2: `lam = 3`, `x = 0` — thermoneutral: only `x = 0` fires. -/
example : hammondZone 3 0 = HZone.half ∧ ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < 3) ∧ ((0 : ℝ) = 0)
    ∧ ¬ ((0 : ℝ) < 0 ∧ -(3 : ℝ) < (0 : ℝ)) ∧ ¬ ((0 : ℝ) = 3) ∧ ¬ ((0 : ℝ) = -(3 : ℝ))
    ∧ ¬ ((3 : ℝ) < (0 : ℝ)) ∧ ¬ ((0 : ℝ) < -(3 : ℝ)) := by
  zone_grid

/- G3: `lam = 3`, `x = -1` — middle region on the endergonic side: only `x < 0 ∧ -lam < x` fires. -/
example : hammondZone 3 (-1) = HZone.late ∧ ¬ (0 < (-1 : ℝ) ∧ (-1 : ℝ) < 3)
    ∧ ¬ ((-1 : ℝ) = 0) ∧ ((-1 : ℝ) < 0 ∧ -(3 : ℝ) < (-1 : ℝ)) ∧ ¬ ((-1 : ℝ) = 3)
    ∧ ¬ ((-1 : ℝ) = -(3 : ℝ)) ∧ ¬ ((3 : ℝ) < (-1 : ℝ)) ∧ ¬ ((-1 : ℝ) < -(3 : ℝ)) := by
  zone_grid

/- G4: `lam = 3`, `x = lam` — barrierless forward: only `x = lam` fires, and strictness of the
region is what keeps it out of `early`. -/
example : hammondZone 3 3 = HZone.atReactant ∧ ¬ (0 < (3 : ℝ) ∧ (3 : ℝ) < 3)
    ∧ ¬ ((3 : ℝ) = 0) ∧ ¬ ((3 : ℝ) < 0 ∧ -(3 : ℝ) < (3 : ℝ)) ∧ ((3 : ℝ) = 3)
    ∧ ¬ ((3 : ℝ) = -(3 : ℝ)) ∧ ¬ ((3 : ℝ) < (3 : ℝ)) ∧ ¬ ((3 : ℝ) < -(3 : ℝ)) := by
  zone_grid

/- G5: `lam = 3`, `x = -lam` — barrierless reverse: only `x = -lam` fires. -/
example : hammondZone 3 (-3) = HZone.atProduct ∧ ¬ (0 < (-3 : ℝ) ∧ (-3 : ℝ) < 3)
    ∧ ¬ ((-3 : ℝ) = 0) ∧ ¬ ((-3 : ℝ) < 0 ∧ -(3 : ℝ) < (-3 : ℝ)) ∧ ¬ ((-3 : ℝ) = 3)
    ∧ ((-3 : ℝ) = -(3 : ℝ)) ∧ ¬ ((3 : ℝ) < (-3 : ℝ)) ∧ ¬ ((-3 : ℝ) < -(3 : ℝ)) := by
  zone_grid

/- G6: `lam = 3`, `x = 5` — inverted region: only `lam < x` fires. -/
example : hammondZone 3 5 = HZone.beyondReactant ∧ ¬ (0 < (5 : ℝ) ∧ (5 : ℝ) < 3)
    ∧ ¬ ((5 : ℝ) = 0) ∧ ¬ ((5 : ℝ) < 0 ∧ -(3 : ℝ) < (5 : ℝ)) ∧ ¬ ((5 : ℝ) = 3)
    ∧ ¬ ((5 : ℝ) = -(3 : ℝ)) ∧ ((3 : ℝ) < (5 : ℝ)) ∧ ¬ ((5 : ℝ) < -(3 : ℝ)) := by
  zone_grid

/- G7: `lam = 3`, `x = -5` — deep endergonic: only `x < -lam` fires. -/
example : hammondZone 3 (-5) = HZone.beyondProduct ∧ ¬ (0 < (-5 : ℝ) ∧ (-5 : ℝ) < 3)
    ∧ ¬ ((-5 : ℝ) = 0) ∧ ¬ ((-5 : ℝ) < 0 ∧ -(3 : ℝ) < (-5 : ℝ)) ∧ ¬ ((-5 : ℝ) = 3)
    ∧ ¬ ((-5 : ℝ) = -(3 : ℝ)) ∧ ¬ ((3 : ℝ) < (-5 : ℝ)) ∧ ((-5 : ℝ) < -(3 : ℝ)) := by
  zone_grid

/- G8: `lam = 1`, `x = 3/4` — plan instance I2 (mildly exergonic textbook): `early`. -/
example : hammondZone 1 (3 / 4) = HZone.early ∧ (0 < (3 / 4 : ℝ) ∧ (3 / 4 : ℝ) < 1)
    ∧ ¬ ((3 / 4 : ℝ) = 0) ∧ ¬ ((3 / 4 : ℝ) < 0 ∧ -(1 : ℝ) < (3 / 4 : ℝ))
    ∧ ¬ ((3 / 4 : ℝ) = 1) ∧ ¬ ((3 / 4 : ℝ) = -(1 : ℝ)) ∧ ¬ ((1 : ℝ) < (3 / 4 : ℝ))
    ∧ ¬ ((3 / 4 : ℝ) < -(1 : ℝ)) := by
  zone_grid

/- G9: `lam = 1`, `x = -1/2` — plan instance I3 (endergonic textbook): `late`. -/
example : hammondZone 1 (-(1 / 2)) = HZone.late ∧ ¬ (0 < (-(1 / 2) : ℝ) ∧ (-(1 / 2) : ℝ) < 1)
    ∧ ¬ ((-(1 / 2) : ℝ) = 0) ∧ ((-(1 / 2) : ℝ) < 0 ∧ -(1 : ℝ) < (-(1 / 2) : ℝ))
    ∧ ¬ ((-(1 / 2) : ℝ) = 1) ∧ ¬ ((-(1 / 2) : ℝ) = -(1 : ℝ)) ∧ ¬ ((1 : ℝ) < (-(1 / 2) : ℝ))
    ∧ ¬ ((-(1 / 2) : ℝ) < -(1 : ℝ)) := by
  zone_grid

/- G10: `lam = 1`, `x = 1` — plan instance I4 (barrierless forward boundary): `atReactant`, i.e.
the boundary is a branch of the classifier but (by C11) not a conforming verdict. -/
example : hammondZone 1 1 = HZone.atReactant ∧ ¬ (0 < (1 : ℝ) ∧ (1 : ℝ) < 1)
    ∧ ¬ ((1 : ℝ) = 0) ∧ ¬ ((1 : ℝ) < 0 ∧ -(1 : ℝ) < (1 : ℝ)) ∧ ((1 : ℝ) = 1)
    ∧ ¬ ((1 : ℝ) = -(1 : ℝ)) ∧ ¬ ((1 : ℝ) < (1 : ℝ)) ∧ ¬ ((1 : ℝ) < -(1 : ℝ)) := by
  zone_grid

/- G11: `lam = 6/5`, `x = 1/20` — plan instance I5 (literature MCC, normal region): `early`. -/
example : hammondZone (6 / 5) (1 / 20) = HZone.early
    ∧ (0 < (1 / 20 : ℝ) ∧ (1 / 20 : ℝ) < 6 / 5) ∧ ¬ ((1 / 20 : ℝ) = 0)
    ∧ ¬ ((1 / 20 : ℝ) < 0 ∧ -(6 / 5 : ℝ) < (1 / 20 : ℝ)) ∧ ¬ ((1 / 20 : ℝ) = 6 / 5)
    ∧ ¬ ((1 / 20 : ℝ) = -(6 / 5 : ℝ)) ∧ ¬ ((6 / 5 : ℝ) < (1 / 20 : ℝ))
    ∧ ¬ ((1 / 20 : ℝ) < -(6 / 5 : ℝ)) := by
  zone_grid

/- G12: `lam = 6/5`, `x = 12/5` — plan instance I6 (literature MCC, inverted region):
`beyondReactant`, not `early`/`late`. -/
example : hammondZone (6 / 5) (12 / 5) = HZone.beyondReactant
    ∧ ¬ (0 < (12 / 5 : ℝ) ∧ (12 / 5 : ℝ) < 6 / 5) ∧ ¬ ((12 / 5 : ℝ) = 0)
    ∧ ¬ ((12 / 5 : ℝ) < 0 ∧ -(6 / 5 : ℝ) < (12 / 5 : ℝ)) ∧ ¬ ((12 / 5 : ℝ) = 6 / 5)
    ∧ ¬ ((12 / 5 : ℝ) = -(6 / 5 : ℝ)) ∧ ((6 / 5 : ℝ) < (12 / 5 : ℝ))
    ∧ ¬ ((12 / 5 : ℝ) < -(6 / 5 : ℝ)) := by
  zone_grid

/- G13: `lam = 1/4`, `x = 11/10` — plan instance I7 (reaction centre, deep inverted):
`beyondReactant`. -/
example : hammondZone (1 / 4) (11 / 10) = HZone.beyondReactant
    ∧ ¬ (0 < (11 / 10 : ℝ) ∧ (11 / 10 : ℝ) < 1 / 4) ∧ ¬ ((11 / 10 : ℝ) = 0)
    ∧ ¬ ((11 / 10 : ℝ) < 0 ∧ -(1 / 4 : ℝ) < (11 / 10 : ℝ)) ∧ ¬ ((11 / 10 : ℝ) = 1 / 4)
    ∧ ¬ ((11 / 10 : ℝ) = -(1 / 4 : ℝ)) ∧ ((1 / 4 : ℝ) < (11 / 10 : ℝ))
    ∧ ¬ ((11 / 10 : ℝ) < -(1 / 4 : ℝ)) := by
  zone_grid

/- G14: ℚ-side grid (kernel computation over `Rat`): normal-region and inverted-region
literature points, and the degenerate `lam = 0` point, must classify exactly as their ℝ images
do. -/
example : Rat.hammondZoneQ (6 / 5) (1 / 20) = HZone.early
    ∧ (0 < (1 / 20 : ℚ) ∧ (1 / 20 : ℚ) < 6 / 5) ∧ ¬ ((1 / 20 : ℚ) = 0)
    ∧ ¬ ((1 / 20 : ℚ) < 0 ∧ -(6 / 5 : ℚ) < (1 / 20 : ℚ)) ∧ ¬ ((1 / 20 : ℚ) = 6 / 5)
    ∧ ¬ ((1 / 20 : ℚ) = -(6 / 5 : ℚ)) ∧ ¬ ((6 / 5 : ℚ) < (1 / 20 : ℚ))
    ∧ ¬ ((1 / 20 : ℚ) < -(6 / 5 : ℚ)) := by
  zoneQ_grid

/- G15: ℚ-side inverted-region point (the plan's I6 parameter pair as a ℚ kernel computation):
`beyondReactant` and no other guard fires — the ℚ mirror of G12. -/
example : Rat.hammondZoneQ (6 / 5) (12 / 5) = HZone.beyondReactant
    ∧ ¬ (0 < (12 / 5 : ℚ) ∧ (12 / 5 : ℚ) < 6 / 5) ∧ ¬ ((12 / 5 : ℚ) = 0)
    ∧ ¬ ((12 / 5 : ℚ) < 0 ∧ -(6 / 5 : ℚ) < (12 / 5 : ℚ)) ∧ ¬ ((12 / 5 : ℚ) = 6 / 5)
    ∧ ¬ ((12 / 5 : ℚ) = -(6 / 5 : ℚ)) ∧ ((6 / 5 : ℚ) < (12 / 5 : ℚ))
    ∧ ¬ ((12 / 5 : ℚ) < -(6 / 5 : ℚ)) := by
  zoneQ_grid

/- G16: the ℚ classifier on the degenerate diagonal point agrees with the ℝ classifier
(`atReactant` on both sides), i.e. the transfer lemma is not silently excluding the `lam = 0`
branch. -/
example : Rat.hammondZoneQ (0 : ℚ) 0 = HZone.atReactant
    ∧ hammondZone (0 : ℝ) 0 = HZone.atReactant
    ∧ Rat.hammondZoneQ (-1) 0 = hammondZone (-1 : ℝ) 0 := by
  refine ⟨by zoneQ_decide, by zone_decide, ?_⟩
  simpa using Rat.hammondZoneQ_eq_hammondZone (-1) 0

/-! ## E. Independence / anti-circularity — re-derivations straight from the definitions

No delivered H1 theorem is called in this section: the identities below are recomputed from the
defining expressions (`tsCoord`, `gapReactant`, `gapProduct`, `lefflerSecant`) with different proof
routes, which is the evidence that the delivered theorems are not definitional restatements of one
another. -/

/- E1: Leffler secant identity at the symmetric rational pair `(3, -1) → (3, 1)`: the secant of
the barrier equals the coordinate at the midpoint `x = 0`. -/
example : lefflerSecant 3 (-1) 1 = tsCoord 3 0 := by
  norm_num [lefflerSecant, gapReactant, tsCoord]

/- E2: Leffler secant identity at the pair `(3, 1) → (3, 5)` (midpoint `x = 3`, the barrierless
forward point): the secant is `0`, agreeing with the coordinate there. -/
example : lefflerSecant 3 1 5 = tsCoord 3 3 := by
  norm_num [lefflerSecant, gapReactant, tsCoord]

/- E3: the secant is NOT a definitional copy of the coordinate: at the pair `(3, 1) → (3, 3)` the
secant is `1/6` while `tsCoord 3 1` is `1/3` — it equals the coordinate at the midpoint only. -/
example : lefflerSecant 3 1 3 ≠ tsCoord 3 1 := by
  norm_num [lefflerSecant, gapReactant, tsCoord]

/- E4: the Leffler identity holds for the literature MCC pair as well (plan I9), including in the
inverted region where the midpoint coordinate is negative — the identity is exact, not a
small-driving-force approximation. -/
example : lefflerSecant (6 / 5) (3 / 5) (12 / 5) = tsCoord (6 / 5) ((3 / 5 + 12 / 5) / 2) := by
  norm_num [lefflerSecant, gapReactant, tsCoord]

/- E5: the gap-difference identity at a concrete point, computed from the two barrier definitions
only. -/
example : gapProduct 3 1 - gapReactant 3 1 = 1 := by
  norm_num [gapProduct, gapReactant]

/- E6: the same identity symbolically by a route that does NOT reuse the delivered proof shape
(`div_sub_div_same` then `div_eq_iff`, instead of `field_simp`), so the delivered
`gapProduct_sub_gapReactant` is not the only way to reach it. -/
theorem audit_gap_sub_identity {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    gapProduct lam x - gapReactant lam x = x := by
  have h4 : (4 * lam : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hlam
  unfold gapProduct gapReactant
  rw [div_sub_div_same, div_eq_iff h4]
  ring

/- E7: monotonicity direction at one rational pair, re-derived through
`div_lt_div_iff_of_pos_right` (no delivered H2 theorem exists yet and none is called). -/
example : tsCoord 3 5 < tsCoord 3 1 := by
  unfold tsCoord
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2 * 3)]
  norm_num

/- E8: the same direction at the literature pair (`x = 3/5 → 12/5`), i.e. the descriptor's
inequality is witnessed by the instance data, not by the general descriptor theorem. -/
example : tsCoord (6 / 5) (12 / 5) < tsCoord (6 / 5) (3 / 5) := by
  norm_num [tsCoord]

/- E9: the reverse-reaction mirror identity at the model's numbers, computed from the definition
(no delivered `tsCoord_neg` is called). -/
example : tsCoord 3 (-1) = 1 - tsCoord 3 1 := by norm_num [tsCoord]

/-! ## G. H5a (ℚ side) — the same adversarial checks on the delivered rational layer

The ℚ layer is not decoration: it is the layer where classification is *computable*, so its
characterizations must pass and fail exactly where the ℝ ones do. Q1–Q4 mirror A8–A11, Q5–Q8
mirror the tightness results A15–A18, Q9 checks the transfer lemma where both sides are
kernel-computed, and Q10–Q12 check the content of the Marcus cross-link. -/

/- Q1: ℚ `hammondZoneQ_eq_half_iff` without `0 < lam` fails at `lam = -1`, `x = 0`: the classifier
returns `beyondProduct` while the algebraic condition `x = 0` holds. -/
example : ¬ (Rat.hammondZoneQ (-1) 0 = HZone.half ↔ (0 : ℚ) = 0) := by zoneQ_decide

/- Q2: ℚ `hammondZoneQ_eq_atProduct_iff` without `0 < lam` fails at `lam = 0`, `x = 0`: the first
branch absorbs the point as `atReactant`. -/
example : ¬ (Rat.hammondZoneQ (0 : ℚ) 0 = HZone.atProduct ↔ (0 : ℚ) = -(0 : ℚ)) := by
  zoneQ_decide

/- Q3: ℚ `hammondZoneQ_eq_beyondReactant_iff` without `0 < lam` fails at `lam = -1`,
`x = 1 = -lam`: the classifier fires `atProduct`. -/
example : ¬ (Rat.hammondZoneQ (-1) 1 = HZone.beyondReactant ↔ (-1 : ℚ) < 1) := by zoneQ_decide

/- Q4: ℚ `hammondZoneQ_eq_beyondProduct_iff` without `0 < lam` fails at `lam = -1`,
`x = -1 = lam`: the classifier fires `atReactant`. -/
example : ¬ (Rat.hammondZoneQ (-1) (-1) = HZone.beyondProduct ↔ (-1 : ℚ) < -(-1 : ℚ)) := by
  zoneQ_decide

/- Q5: ℚ `early` needs no sign premise either (general statement, mirroring A15). -/
theorem audit_earlyQ_iff_no_hyp (lam x : ℚ) :
    Rat.hammondZoneQ lam x = HZone.early ↔ 0 < x ∧ x < lam := by
  constructor
  · intro h
    unfold Rat.hammondZoneQ at h
    split_ifs at h with h1 h2 h3 h4 h5 h6
    exact ⟨h6, lt_of_le_of_ne (le_of_not_gt h4) h1⟩
  · rintro ⟨h1, h2⟩
    unfold Rat.hammondZoneQ
    rw [if_neg (ne_of_lt h2), if_neg (by linarith), if_neg (by linarith),
      if_neg (not_lt.mpr (le_of_lt h2)), if_neg (ne_of_gt h1), if_pos h1]

/- Q6: ℚ `late` needs no sign premise either (general statement, mirroring A16). -/
theorem audit_lateQ_iff_no_hyp (lam x : ℚ) :
    Rat.hammondZoneQ lam x = HZone.late ↔ x < 0 ∧ -lam < x := by
  constructor
  · intro h
    unfold Rat.hammondZoneQ at h
    split_ifs at h with h1 h2 h3 h4 h5 h6
    exact ⟨lt_of_le_of_ne (le_of_not_gt h6) h5, lt_of_le_of_ne (le_of_not_gt h3) (Ne.symm h2)⟩
  · rintro ⟨h1, h2⟩
    unfold Rat.hammondZoneQ
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith),
      if_neg (by linarith), if_neg (by linarith)]

/- Q7: ℚ `atReactant` needs no sign premise either (general statement, mirroring A17). -/
theorem audit_atReactantQ_iff_no_hyp (lam x : ℚ) :
    Rat.hammondZoneQ lam x = HZone.atReactant ↔ x = lam := by
  constructor
  · intro h
    unfold Rat.hammondZoneQ at h
    split_ifs at h with h1 h2 h3 h4 h5 h6
    exact h1
  · intro h
    rw [h]
    unfold Rat.hammondZoneQ
    rw [if_pos rfl]

/- Q8: ℚ `atProduct` is sharp at `lam ≠ 0` (general statement, mirroring A18); the `0 < lam` of
the delivered form is stronger than necessary on the ℚ side too. -/
theorem audit_atProductQ_iff_of_ne {lam x : ℚ} (hlam : lam ≠ 0) :
    Rat.hammondZoneQ lam x = HZone.atProduct ↔ x = -lam := by
  constructor
  · intro h
    unfold Rat.hammondZoneQ at h
    split_ifs at h with h1 h2 h3 h4 h5 h6
    exact h2
  · intro h
    rw [h]
    unfold Rat.hammondZoneQ
    rw [if_neg (by intro hh; exact hlam (by linarith)), if_pos rfl]

/- Q9: the transfer lemma instantiated where both sides are decided by the kernel (ℚ by
`zoneQ_decide`, ℝ by the same ℚ value cast) — the transfer is not a vacuous equality. -/
example : Rat.hammondZoneQ (6 / 5) (1 / 20) = hammondZone (6 / 5 : ℝ) (1 / 20 : ℝ) := by
  simpa using Rat.hammondZoneQ_eq_hammondZone (6 / 5) (1 / 20)

/- Q10: content of the Marcus cross-link at the inverted instance (plan I6): the Marcus classifier
selects `inverted` and the Hammond classifier `beyondReactant`, as the delivered iff requires. -/
example : Marcus.Rat.zoneQ (6 / 5) (12 / 5) = Marcus.Zone.inverted
    ∧ Rat.hammondZoneQ (6 / 5) (12 / 5) = HZone.beyondReactant := by
  refine ⟨by norm_num [Marcus.Rat.zoneQ], by zoneQ_decide⟩

/- Q11: negative control for Q10 at the normal-region instance (plan I5): the Marcus classifier
says `normal`, so `beyondReactant` must be false there — the cross-link is not an equivalence of
always-true statements. -/
example : ¬ (Marcus.Rat.zoneQ (6 / 5) (1 / 20) = Marcus.Zone.inverted)
    ∧ Rat.hammondZoneQ (6 / 5) (1 / 20) = HZone.early := by
  have hz : Marcus.Rat.zoneQ (6 / 5) (1 / 20) = Marcus.Zone.normal := by
    norm_num [Marcus.Rat.zoneQ]
  refine ⟨?_, by zoneQ_decide⟩
  rw [hz]
  decide

/- Q12: the cross-link at the barrierless boundary `x = lam`: Marcus says `barrierless` (not
inverted) and the Hammond classifier says `atReactant` (not `beyondReactant`), so both sides of
the delivered iff are false — the strictness of the two boundaries is inherited on both layers. -/
example : Marcus.Rat.zoneQ (1 : ℚ) 1 = Marcus.Zone.barrierless
    ∧ Rat.hammondZoneQ (1 : ℚ) 1 = HZone.atReactant := by
  refine ⟨by norm_num [Marcus.Rat.zoneQ], by zoneQ_decide⟩

/-! ## F. Axiom-dependency spot check

The audit itself and the delivered H1 theorems must depend on at most the contract's
infrastructure axioms (`propext`, `Classical.choice`, `Quot.sound`); a build succeeding would not
show this. -/

#print axioms audit_tsCoord_mem_iff_fails_of_neg
#print axioms audit_half_iff_fails_of_nonpos
#print axioms audit_beyondReactant_iff_fails_of_neg
#print axioms audit_exists_reactionRegion_iff
#print axioms audit_early_iff_no_hyp
#print axioms audit_not_reactionRegion_of_nonpos
#print axioms PhotoLean.Hammond.crossing_iff
#print axioms PhotoLean.Hammond.gapReactant_eq_crossing_energy
#print axioms PhotoLean.Hammond.gapProduct_eq_crossing_energy
#print axioms PhotoLean.Hammond.gapProduct_sub_gapReactant
#print axioms PhotoLean.Hammond.gapProduct_eq_gapReactant_neg
#print axioms PhotoLean.Hammond.tsCoord_neg
#print axioms PhotoLean.Hammond.tsCoord_zero
#print axioms PhotoLean.Hammond.tsCoord_zero_lam
#print axioms PhotoLean.Hammond.tsCoord_at_lam
#print axioms PhotoLean.Hammond.tsCoord_mem_iff
#print axioms PhotoLean.Hammond.reactionRegion_pos
#print axioms PhotoLean.Hammond.not_reactionRegion_of_nonpos
#print axioms PhotoLean.Hammond.hammondZone_eq_early_iff
#print axioms PhotoLean.Hammond.hammondZone_eq_half_iff
#print axioms PhotoLean.Hammond.hammondZone_eq_late_iff
#print axioms PhotoLean.Hammond.hammondZone_eq_atReactant_iff
#print axioms PhotoLean.Hammond.hammondZone_eq_atProduct_iff
#print axioms PhotoLean.Hammond.hammondZone_eq_beyondReactant_iff
#print axioms PhotoLean.Hammond.hammondZone_eq_beyondProduct_iff
#print axioms PhotoLean.Hammond.Rat.tsCoordQ_cast
#print axioms PhotoLean.Hammond.Rat.gapReactantQ_cast
#print axioms PhotoLean.Hammond.Rat.lefflerSecantQ_cast
#print axioms PhotoLean.Hammond.Rat.hammondZoneQ_eq_hammondZone
#print axioms PhotoLean.Hammond.Rat.hammondZoneQ_eq_early_iff
#print axioms PhotoLean.Hammond.Rat.hammondZoneQ_eq_half_iff
#print axioms PhotoLean.Hammond.Rat.hammondZoneQ_eq_late_iff
#print axioms PhotoLean.Hammond.Rat.hammondZoneQ_eq_atReactant_iff
#print axioms PhotoLean.Hammond.Rat.hammondZoneQ_eq_atProduct_iff
#print axioms PhotoLean.Hammond.Rat.hammondZoneQ_eq_beyondReactant_iff
#print axioms PhotoLean.Hammond.Rat.hammondZoneQ_eq_beyondProduct_iff
#print axioms PhotoLean.Hammond.Rat.hammondZoneQ_beyondReactant_iff_inverted
#print axioms audit_earlyQ_iff_no_hyp
#print axioms audit_lateQ_iff_no_hyp
#print axioms audit_atReactantQ_iff_no_hyp
#print axioms audit_atProductQ_iff_of_ne

end Hammond

end PhotoLean
