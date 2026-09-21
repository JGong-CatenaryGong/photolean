/-
PhotoLean — PhotoLean/Goldschmidt/Rules.lean

Milestone G2 (plan §5): the **rules layer** of the Goldschmidt theory — the radius rule, the charge
rule and the chemical rule of ionic substitution as predicates, together with their exact
kernel-checked content.

Nothing in this file derives Goldschmidt's rules: they are *declared* modelling content (plan §1.2,
plan §12). What is proved is the structure those declarations carry — the two-sided window form of
the radius rule, its reflexivity, its monotonicity in the tolerance, the "15 %" arithmetic window,
the two-step ratchet, the isovalent characterization and the compensating-partner theorem of the
charge rule, and the monotonicity of the electronegativity-dressed tolerance. In particular the
*linear shape* of `chiTol` is a declared modelling choice, not a theorem (plan §12).

Every physical premise is an explicit hypothesis (engine rule 3): `radiusMatch_refl` carries both
`0 ≤ tau` and `0 ≤ r` (with a negative reference radius the statement is false), and
`radiusMatch_comp_ratchet` carries `0 < r1`, `0 ≤ tau`, `tau ≤ 1`.

Statement authority: `theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean` § G2; every
signature below is identical to its authority row, and the mechanical check
`python3 theories/BEP/probes/bep-fidelity.py --theory goldschmidt --milestone G2` reports 17 of the
18 G2 declarations word-for-word, 0 signature differences and 1 row not delivered (see below).

**One G2 row is not delivered here, because the authority's version of it is false.** The authority's
`chiTol_anti` reads

  `(hk : 0 ≤ k) (h : |chi'' - chi| ≤ |chi' - chi|) : chiTol tol0 k chi chi'' ≤ chiTol tol0 k chi chi'`

with `chiTol tol0 k chi chi' = tol0 - k * |chi - chi'|`, which is *decreasing* in the distance for
`k > 0`. It is refuted at `tol0 = 0`, `k = 1`, `chi = 0`, `chi' = 10`, `chi'' = 0`: the hypothesis
holds (`0 ≤ 10`) and the conclusion is `0 ≤ -10` (kernel-checked counterexample, recorded in
`proofs/EXPERIENCE.md`, 2026-09-21, G2). The true direction is the flipped conclusion
`chiTol .. chi chi' ≤ chiTol .. chi chi''` — exactly the inequality `substitutable_mono_chi` below
consumes — but changing the authority is a statement-correction-log action (plan §3.1), not a
prover's, so the row is left undelivered rather than weakened or silently replaced in place.

This module deliberately does not import `PhotoLean.Goldschmidt.Basic`: nothing in G2 needs the
description layer, and the two layers are independent (plan §5). It declares no `DecidableEq`
hypothesis — Goldschmidt's charge rule quantifies over an arbitrary finite substitution set, so
`exists_compensating_partner` obtains the decidable equality it needs for `Finset.erase` locally,
with `classical`, rather than putting a non-physical typeclass into the statement.
-/
import Mathlib

open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Goldschmidt

/-! ## G2 definitions — the three rules as predicates (plan §5) -/

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

/-! ## G2 radius-rule rows (plan §5) -/

/-- The radius rule as a two-sided **window** on `r'`: `r'` lies between `(1 - τ) r` and
`(1 + τ) r`. Proof: `abs_le` turns the absolute value into a conjunction of two affine inequalities,
and `linarith` rearranges each half. -/
theorem radiusMatch_iff_window {tau r r' : ℝ} :
    RadiusMatch tau r r' ↔ (1 - tau) * r ≤ r' ∧ r' ≤ (1 + tau) * r := by
  rw [RadiusMatch, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- The symmetric form of the radius rule: requiring *both* directions is the same as requiring the
rule with the **smaller** of the two reference radii (`min r r'`). This is the row in which the
radius rule is genuinely symmetric; `RadiusMatch τ r r'` alone is not (it is normalized by `r`).
`0 ≤ τ` is needed only for the backward direction, where the `min` bound is pushed to each side with
`mul_le_mul_of_nonneg_left`; the case split uses `min_eq_left` / `min_eq_right` on `le_total r r'`
(no `mul_min` distributivity lemma is involved). -/
theorem radiusMatch_min_iff {tau r r' : ℝ} (htau : 0 ≤ tau) :
    RadiusMatch tau r r' ∧ RadiusMatch tau r' r ↔ |r - r'| ≤ tau * min r r' := by
  constructor
  · rintro ⟨h1, h2⟩
    unfold RadiusMatch at h1 h2
    rcases le_total r r' with hle | hle
    · rw [min_eq_left hle]
      exact h1
    · rw [min_eq_right hle]
      rwa [abs_sub_comm] at h2
  · intro h
    unfold RadiusMatch
    constructor
    · calc |r - r'| ≤ tau * min r r' := h
        _ ≤ tau * r := mul_le_mul_of_nonneg_left (min_le_left r r') htau
    · rw [abs_sub_comm r' r]
      calc |r - r'| ≤ tau * min r r' := h
        _ ≤ tau * r' := mul_le_mul_of_nonneg_left (min_le_right r r') htau

/-- Reflexivity of the radius rule — an ion may always replace itself. Both hypotheses are needed:
`0 ≤ τ` for the tolerance and `0 ≤ r` because the rule is normalized by the reference radius `r`
(with `r < 0` the right-hand side `τ * r` would be negative while `|r - r| = 0`). -/
theorem radiusMatch_refl {tau r : ℝ} (htau : 0 ≤ tau) (hr : 0 ≤ r) : RadiusMatch tau r r := by
  rw [RadiusMatch, sub_self, abs_zero]
  exact mul_nonneg htau hr

/-- Monotonicity of the radius rule in the tolerance `τ`: a larger tolerated fraction never rejects a
substitution that a smaller one accepted. This is the row the chemical rule consumes. -/
theorem radiusMatch_mono_tau {tau tau' r r' : ℝ} (h : tau ≤ tau') (hr : 0 ≤ r) :
    RadiusMatch tau r r' → RadiusMatch tau' r r' := by
  intro h12
  rw [RadiusMatch] at h12 ⊢
  exact le_trans h12 (mul_le_mul_of_nonneg_right h hr)

/-- The printed "15 %" radius rule (`τ = 3/20`) in a clearing-denominators arithmetic form: the
window `17 r ≤ 20 r' ∧ 20 r' ≤ 23 r`. This is `radiusMatch_iff_window` at `τ = 3/20`
(`1 - 3/20 = 17/20`, `1 + 3/20 = 23/20`) with the positive factors `20` cleared. -/
theorem radiusMatch_fifteen_window {r r' : ℝ} :
    RadiusMatch (3 / 20) r r' ↔ 17 * r ≤ 20 * r' ∧ 20 * r' ≤ 23 * r := by
  rw [radiusMatch_iff_window]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- The **ratchet** of the radius rule: two chained `τ`-steps drift by more than `τ`. With
`0 < r1`, `0 ≤ τ ≤ 1` and both steps inside `τ`, the composite substitution is inside the widened
tolerance `(1 + τ)² - 1` (at the printed `τ = 3/20` that is `129/400 = 32.25 %`, more than the
15 % of either single step — which is why the rule is one-step).

Proof (all three hypotheses are load-bearing): `abs_le` splits the goal into the two sides of the
composite window, and each side is read off the *two-sided* bounds of the individual steps. The
upper side uses `r3 ≤ (1 + τ) r2 ≤ (1 + τ)² r1` (needs `0 ≤ τ`); the lower side uses
`r3 ≥ (1 - τ) r2 ≥ (1 - τ)² r1`, which needs `τ ≤ 1` (so that `1 - τ ≥ 0` carries the second
multiplication) and `r1 ≥ 0` (to compare `(1 - τ)² r1` with `r1`). -/
theorem radiusMatch_comp_ratchet {tau r1 r2 r3 : ℝ} (hr1 : 0 < r1) (htau : 0 ≤ tau)
    (htau1 : tau ≤ 1) : RadiusMatch tau r1 r2 → RadiusMatch tau r2 r3 →
      RadiusMatch ((1 + tau) ^ 2 - 1) r1 r3 := by
  intro h12 h23
  unfold RadiusMatch at h12 h23 ⊢
  have htau1' : 0 ≤ 1 - tau := by linarith
  have hup2 : r2 ≤ (1 + tau) * r1 := by
    have h := neg_le_abs (r1 - r2)
    linarith
  have hlow2 : (1 - tau) * r1 ≤ r2 := by
    have h := le_abs_self (r1 - r2)
    linarith
  have hup3 : r3 ≤ (1 + tau) * r2 := by
    have h := neg_le_abs (r2 - r3)
    linarith
  have hlow3 : (1 - tau) * r2 ≤ r3 := by
    have h := le_abs_self (r2 - r3)
    linarith
  rw [abs_le]
  constructor
  · have hm : (1 + tau) * r2 ≤ (1 + tau) * ((1 + tau) * r1) :=
      mul_le_mul_of_nonneg_left hup2 (by linarith)
    linarith
  · have hm : (1 - tau) * ((1 - tau) * r1) ≤ (1 - tau) * r2 :=
      mul_le_mul_of_nonneg_left hlow2 htau1'
    have hm2 : (1 - tau) * ((1 - tau) * r1) ≤ r3 := le_trans hm hlow3
    have hsq : 0 ≤ tau ^ 2 * r1 := mul_nonneg (sq_nonneg tau) (le_of_lt hr1)
    nlinarith

/-! ## G2 charge-rule rows (plan §5) -/

/-- Single-site charge balance: a substitution set with one site is balanced exactly when its charge
increment vanishes, i.e. exactly when the substitution is isovalent. (The v4.17.0 name is the
`Fintype`-level `Fintype.sum_unique`; there is no `Finset.sum_unit`.) -/
theorem chargeBalanced_single_iff (dz : ℤ) :
    ChargeBalanced (fun _ : Unit => dz) ↔ dz = 0 := by
  rw [ChargeBalanced, Fintype.sum_unique]

/-- Two-site charge balance: a `Bool`-indexed charge vector is balanced exactly when its two
increments cancel. `Fintype.sum_bool` computes the sum in the order `dz true + dz false`, so one
`add_comm` produces the authority's printed order `dz false + dz true = 0`. -/
theorem chargeBalanced_pair_iff (dz : Bool → ℤ) :
    ChargeBalanced dz ↔ dz false + dz true = 0 := by
  rw [ChargeBalanced, Fintype.sum_bool, add_comm]

/-- A balanced substitution set with a positively charged site must also carry a negatively charged
site — charge balance cannot be achieved by positive increments alone. -/
theorem exists_negative_of_pos {ι : Type*} [Fintype ι] {dz : ι → ℤ} (h : ChargeBalanced dz)
    (hpos : ∃ i, 0 < dz i) : ∃ j, dz j < 0 := by
  by_contra hneg
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ dz i :=
    fun i _ => le_of_not_gt (fun hlt => hneg ⟨i, hlt⟩)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h
  obtain ⟨i, hi⟩ := hpos
  have := hz i (Finset.mem_univ i)
  omega

/-- **Compensating partner**: every positively charged site of a balanced substitution set has a
*distinct* negatively charged partner. Proof: split the sum at `i` with
`Finset.sum_erase_eq_sub`; if no other site were negative, the sum over `Finset.univ.erase i` would
be `≥ 0`, but it equals `-dz i < 0`. The statement carries no `DecidableEq ι` hypothesis — the
substitution set is an arbitrary finite type and the decidable equality that `Finset.erase` needs is
provided locally by `classical`. -/
theorem exists_compensating_partner {ι : Type*} [Fintype ι] {dz : ι → ℤ} (h : ChargeBalanced dz)
    {i : ι} (hi : 0 < dz i) : ∃ j, j ≠ i ∧ dz j < 0 := by
  classical
  by_contra hneg
  have hsum : ∑ j : ι, dz j = 0 := h
  have hnn : ∀ j ∈ (Finset.univ : Finset ι).erase i, 0 ≤ dz j := by
    intro j hj
    rw [Finset.mem_erase] at hj
    exact le_of_not_gt (fun hlt => hneg ⟨j, hj.1, hlt⟩)
  have hsum_erase : ∑ j ∈ (Finset.univ : Finset ι).erase i, dz j = -dz i := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hsum]
    ring
  have hnn' := Finset.sum_nonneg hnn
  rw [hsum_erase] at hnn'
  omega

/-! ## G2 chemical-rule rows (plan §5)

  The linear shape of `chiTol` is a declared modelling choice (plan §12); the theorem content is its
  monotonicity in the electronegativity difference, and that monotonicity transported to
  `Substitutable`. -/

/-- Goldschmidt's chemical rule (rule 3): the closer the electronegativities, the more substitutions
are tolerated — a substitution accepted at `χ'` is still accepted at a `χ''` that is at least as
close to the reference chemistry `χ`.

Proof: the tolerance inequality `chiTol .. χ' ≤ chiTol .. χ''` is `tol0 - k |χ - χ'| ≤
tol0 - k |χ - χ''|`, i.e. it is the *reversed* distance inequality multiplied by `0 ≤ k` (the two
`abs_sub_comm` rewrites align the argument order of `chiTol`, which writes `|χ - χ'|`, with the
statement's `|χ' - χ|`); `radiusMatch_mono_tau` then pushes the tolerance through the radius rule,
which is where `0 ≤ r` is needed. -/
theorem substitutable_mono_chi {tol0 k chi chi' chi'' r r' : ℝ} (hk : 0 ≤ k) (hr : 0 ≤ r)
    (h : |chi'' - chi| ≤ |chi' - chi|) :
    Substitutable tol0 k chi chi' r r' → Substitutable tol0 k chi chi'' r r' := by
  intro hsub
  rw [Substitutable] at hsub ⊢
  refine radiusMatch_mono_tau ?_ hr hsub
  have hmul : k * |chi - chi''| ≤ k * |chi - chi'| := by
    have h' : |chi'' - chi| ≤ |chi' - chi| := h
    rw [abs_sub_comm chi'' chi, abs_sub_comm chi' chi] at h'
    exact mul_le_mul_of_nonneg_left h' hk
  rw [chiTol, chiTol]
  linarith

/-- The composed chemical + radius rule in window form: `Substitutable` is the radius rule with the
electronegativity-dressed tolerance `chiTol` in place of `τ`. -/
theorem substitutable_iff_window {tol0 k chi chi' r r' : ℝ} :
    Substitutable tol0 k chi chi' r r' ↔
      (1 - chiTol tol0 k chi chi') * r ≤ r' ∧ r' ≤ (1 + chiTol tol0 k chi chi') * r := by
  rw [Substitutable]
  exact radiusMatch_iff_window

end Goldschmidt

end PhotoLean
