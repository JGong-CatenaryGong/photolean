/-
Sabatier API calibration — probe (f)+(g): the `ℚ → ℝ` cast layer and the `if`/`ite`
classifier layer.

Owner: api_researcher. Evidence behind the `## Sabatier theory (2026-09-21)` section of
`proofs/API-NOTES.md`. Run from the repository root with

  proofs/scripts/lake env lean theories/Sabatier/probes/sabatier-api-cast-ite.lean

The instance/verdict layer of the volcano theory repeats the delivered photoLean pattern: a
`ℚ`-side classifier and arithmetic body that the kernel can *compute* (`norm_num`), plus
`..._cast` transfer lemmas that carry the verdict to the `ℝ` theory. §2 and §4 below reproduce
that pattern on a small self-contained volcano model and are kernel-checked end to end.
-/
import Mathlib

namespace PhotoLean
namespace Sabatier
namespace ApiProbeCastIte

/-! ## 1. `ℚ → ℝ` cast — confirmed signatures -/

#check @Rat.cast_add
#check @Rat.cast_sub
#check @Rat.cast_mul
#check @Rat.cast_div
#check @Rat.cast_inv
#check @Rat.cast_neg
#check @Rat.cast_zero
#check @Rat.cast_one
#check @Rat.cast_ofNat
#check @Rat.cast_natCast
#check @Rat.cast_intCast
#check @Rat.cast_le
#check @Rat.cast_lt
#check @Rat.cast_inj
#check @Rat.cast_injective
#check @Rat.cast_def
#check @Rat.cast_max
#check @Rat.cast_min
#check @Rat.cast_abs
#check @Rat.cast_pos
#check @Rat.cast_nonneg
#check @Rat.cast_nonpos
#check @Rat.cast_lt_zero
#check @Rat.cast_ne_zero
#check @Rat.cast_eq_zero
#check @Rat.cast_sum
#check @Rat.cast_prod
#check @Rat.cast_mono
#check @Rat.cast_strictMono
#check Rat.castHom

/-! ### 1a. The two comparison transfers, and the explicit-field trap

`Rat.cast_lt` / `Rat.cast_le` are **iff**s, so the exact goal shape matters. The measured trap
(recorded in `proofs/API-NOTES.md` §kasha §4.4) is that a `rw [← Rat.cast_lt]` with the target
field still a metavariable fails with a stuck typeclass instance; the explicit-field form
`(Rat.cast_lt (K := ℝ))` is always safe. -/

/-- Recipe: `((p : ℚ) : ℝ) < ((q : ℚ) : ℝ) ↔ p < q`, in one step — the lemma *is* the `iff`. -/
example {p q : ℚ} : ((p : ℚ) : ℝ) < ((q : ℚ) : ℝ) ↔ p < q := Rat.cast_lt

/-- Recipe: the same for `≤`. -/
example {p q : ℚ} : ((p : ℚ) : ℝ) ≤ ((q : ℚ) : ℝ) ↔ p ≤ q := Rat.cast_le

/-- Recipe: the reverse orientation of the same goal — `.symm` with an **explicit field**. -/
example {p q : ℚ} : p < q ↔ ((p : ℚ) : ℝ) < ((q : ℚ) : ℝ) := (Rat.cast_lt (K := ℝ)).symm

/-- Recipe: from the ℚ comparison to the ℝ comparison (`exact_mod_cast` is the tactic form). -/
example {p q : ℚ} (h : p < q) : ((p : ℚ) : ℝ) < ((q : ℚ) : ℝ) := by exact_mod_cast h

/-- Recipe: the same in one step with the explicit-field `iff`. -/
example {p q : ℚ} (h : p < q) : ((p : ℚ) : ℝ) < ((q : ℚ) : ℝ) := (Rat.cast_lt (K := ℝ)).mpr h

/-- Recipe: from a *hypothesis* `↑p < ↑q` to `p < q` — the `.mp` form with the field explicit.
**Trap (measured, extends the one registered in `proofs/API-NOTES.md` §kasha §4.4):**
`rw [← Rat.cast_lt] at h` does **not** work here — rewriting is syntactic, the rewrite pattern is
a *ℚ* comparison, and `h` carries an *ℝ* comparison:
`error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  ?m.94 < ?m.95`.
`push_cast` does not cross this direction either (from `h : p < q` to the goal `↑p < ↑q` it leaves
the goal untouched). The working forms are `.mp` / `.mpr` / `exact_mod_cast` / `norm_cast`. -/
example {p q : ℚ} (h : ((p : ℚ) : ℝ) < ((q : ℚ) : ℝ)) : p < q := (Rat.cast_lt (K := ℝ)).mp h

/-- Recipe: the `≤` twin on a hypothesis. -/
example {p q : ℚ} (h : ((p : ℚ) : ℝ) ≤ ((q : ℚ) : ℝ)) : p ≤ q := (Rat.cast_le (K := ℝ)).mp h

/-- Recipe: `norm_cast` closes the goal-side comparison directly, when the whole goal is a
cast comparison (no `↔` orientation bookkeeping needed). -/
example {p q : ℚ} : ((p : ℚ) : ℝ) < ((q : ℚ) : ℝ) ↔ p < q := by norm_cast

/-- Recipe: and back (this is the step that makes a rational computation binding for the real
theory). -/
example {p q : ℚ} (h : ((p : ℚ) : ℝ) < ((q : ℚ) : ℝ)) : p < q := by exact_mod_cast h

/-- Recipe: equality on the ℝ side is an equality on the ℚ side — same shape, `Rat.cast_inj`. -/
example {p q : ℚ} : ((p : ℚ) : ℝ) = ((q : ℚ) : ℝ) ↔ p = q := Rat.cast_inj

/-- Recipe: positivity transfer (`Rat.cast_pos` is an `iff`). -/
example {p : ℚ} : (0 : ℝ) < (p : ℝ) ↔ 0 < p := Rat.cast_pos

/-! ### 1b. The cast commuting with `max` / `min` / `abs`

**Name drift (measured):** there is **no** `map_max` usable here (`error: unknown identifier
'map_max'`); the named lemmas are `Rat.cast_max` / `Rat.cast_min` / `Rat.cast_abs`, all
`@[simp, norm_cast]`. -/

/-- Recipe: the cast commutes with `max` — direct application. -/
example (p q : ℚ) : ((max p q : ℚ) : ℝ) = max (p : ℝ) (q : ℝ) := Rat.cast_max p q

/-- Recipe: the same through `push_cast` (`norm_cast` lemmas are what `push_cast` consumes). -/
example (p q : ℚ) : ((max p q : ℚ) : ℝ) = max (p : ℝ) (q : ℝ) := by push_cast; rfl

/-- Recipe: and through `norm_cast`. -/
example (p q : ℚ) : ((max p q : ℚ) : ℝ) = max (p : ℝ) (q : ℝ) := by norm_cast

/-- Recipe: the `min` twin. -/
example (p q : ℚ) : ((min p q : ℚ) : ℝ) = min (p : ℝ) (q : ℝ) := Rat.cast_min p q

/-- Recipe: a `max`-form comparison transfers by composing the two `iff`s — the transfer the
volcano optimization rows need. -/
example (p q c : ℚ) : ((max p q : ℚ) : ℝ) ≤ (c : ℝ) ↔ max p q ≤ c := Rat.cast_le

/-- Recipe: the same with `max` on the right-hand side. -/
example (p q c : ℚ) : (c : ℝ) ≤ ((max p q : ℚ) : ℝ) ↔ c ≤ max p q := Rat.cast_le

/-- Recipe: `Rat.cast_def` gives the `num/den` normal form, for a `norm_num`-style computation. -/
example (q : ℚ) : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q

/-! ## 2. The house `..._cast` transfer shape (self-contained reproduction)

`PhotoLean/Hammond/RatModel.lean` §"Transfer lemmas" and `PhotoLean/Kasha/RatModel.lean` §6 of
`proofs/API-NOTES.md` both use: **algebraic** bodies → `unfold Xq X; push_cast; ring`;
**classifier** bodies → `unfold zoneQ zone; norm_cast`. The model below is a miniature volcano
body (`Ea(λ, x) = (λ - x)^2 / (4λ)` is the same quadratic as `Marcus.barrier`), and both recipes
are kernel-checked on it. -/

/-- Rational volcano barrier (the computable side). -/
def volcanoQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- Real volcano barrier (the theory side). -/
noncomputable def volcano (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- Recipe: the algebraic transfer — `unfold`, `push_cast`, `ring`. `push_cast` alone does not
close the goal; `ring` must follow. -/
theorem volcanoQ_cast (lam x : ℚ) :
    ((volcanoQ lam x : ℚ) : ℝ) = volcano (lam : ℝ) (x : ℝ) := by
  unfold volcanoQ volcano
  push_cast
  ring

/-- Recipe: the same transfer written with explicit `Rat.cast_*` rewrites instead of
`push_cast`. **Trap (measured):** this route closes *by itself* (the goal becomes `rfl`), so
appending an explicit `rfl` gives `error: no goals to be solved`. The two routes therefore have
opposite tails: `push_cast` **needs** the following `ring`/`rfl`, the explicit `rw` route must
**not** have one. -/
theorem volcanoQ_cast' (lam x : ℚ) :
    ((volcanoQ lam x : ℚ) : ℝ) = volcano (lam : ℝ) (x : ℝ) := by
  unfold volcanoQ volcano
  rw [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]

/-- A rational prediction: is the barrier below the threshold `t`? -/
def volcanoWithinQ (lam x t : ℚ) : Prop := volcanoQ lam x ≤ t

/-- The real twin. -/
def VolcanoWithin (lam x t : ℝ) : Prop := volcano lam x ≤ t

/-- Recipe: the predicate transfer — push the cast through the body, then hand the comparison
to `Rat.cast_le` **with the field explicit**. `Rat.cast_le : ↑p ≤ ↑q ↔ p ≤ q` already has the
orientation of this goal; the `.symm` form is only needed when the goal is written the other way
round (see `proofs/API-NOTES.md` §kasha §6, where `kashaWithinQ_iff_cast` needs `.symm`). -/
theorem volcanoWithinQ_iff_cast (lam x t : ℚ) :
    VolcanoWithin (lam : ℝ) (x : ℝ) (t : ℝ) ↔ volcanoWithinQ lam x t := by
  unfold VolcanoWithin volcanoWithinQ
  rw [← volcanoQ_cast]
  exact Rat.cast_le (K := ℝ)

/-! ## 3. `if` / `ite` — confirmed signatures -/

#check @if_pos
#check @if_neg
#check @ite_eq_iff
#check @ite_eq_iff'
#check @dif_pos
#check @dif_neg
#check @apply_ite
#check @apply_dite
#check @ite_cond_eq_true
#check @ite_cond_eq_false

/-- Recipe: a single `if` with the guard discharged — `if_pos` / `if_neg` are the two one-liners
used by the delivered classifiers' *backward* direction. -/
example {P : Prop} [Decidable P] {a b : ℝ} (h : P) : (if P then a else b) = a := if_pos h

/-- Recipe: the negative branch. -/
example {P : Prop} [Decidable P] {a b : ℝ} (h : ¬P) : (if P then a else b) = b := if_neg h

/-- Recipe: consuming an `if`-valued *hypothesis* — `split_ifs at h` turns `h : (if P then a else b) = c`
into the two branch hypotheses. -/
example {P : Prop} [Decidable P] {a b c : ℝ} (h : (if P then a else b) = c) : a = c ∨ b = c := by
  split_ifs at h with hP
  · exact Or.inl h
  · exact Or.inr h

/-- Recipe: `ite_eq_iff` is the packaged form of the same case analysis. -/
example {P : Prop} [Decidable P] {a b c : ℝ} : (if P then a else b) = c ↔ P ∧ a = c ∨ ¬P ∧ b = c :=
  ite_eq_iff

/-- Recipe: pushing a function through an `if` (`apply_ite`) — the tool for a `cast`/`abs`/`max`
that sits outside a classifier. -/
example {P : Prop} [Decidable P] {a b : ℝ} : (2 : ℝ) * (if P then a else b) = if P then 2 * a else 2 * b :=
  apply_ite (fun x => (2 : ℝ) * x) P a b

/-- Recipe: `dif_pos` for a dependent `if` (the `dite` form). -/
example {P : Prop} [Decidable P] {t : P → ℝ} {e : ¬P → ℝ} (h : P) : dite P t e = t h := dif_pos h

/-! ## 4. The classifier layer (house shape, self-contained reproduction)

`PhotoLean/Hammond/Basic.lean` (`hammondZone`, 7 branches) and `PhotoLean/BEP/Basic.lean`
(`epZone`, 9 branches) are `if`-cascades over `ℝ` with a set of `..._iff` characterization
lemmas. The reproduction below is a 6-branch volcano classifier; the two measured recipes are:
(i) the *classifier* transfer `unfold` + `norm_cast` (no hypotheses, no case bash);
(ii) the *characterization* proof `unfold` + `split_ifs with h1 … h5`, with the naming
convention spelled out. -/

/-- Where a volcano instance sits relative to the apex. -/
inductive VZone where
  | atApex
  | strong
  | apex
  | optimal
  | weakEdge
  | weak
  deriving DecidableEq, Repr

/-- Rational volcano classifier (computable: `ℚ` comparisons are decidable). -/
def volcanoZoneQ (lam x : ℚ) : VZone :=
  if x = lam then VZone.atApex
  else if lam < x then VZone.strong
  else if x = 0 then VZone.apex
  else if 0 < x then VZone.optimal
  else if x = -lam then VZone.weakEdge
  else VZone.weak

/-- Real volcano classifier (the theory side; `ℝ` order is not computable). -/
noncomputable def volcanoZone (lam x : ℝ) : VZone :=
  if x = lam then VZone.atApex
  else if lam < x then VZone.strong
  else if x = 0 then VZone.apex
  else if 0 < x then VZone.optimal
  else if x = -lam then VZone.weakEdge
  else VZone.weak

/-- Recipe (i): the **classifier transfer** — the two definitions are the same `if`-cascade, so
`unfold` + `norm_cast` closes it, with no hypotheses and no case analysis. `norm_cast` moves the
five `ℚ`-side tests across, handling the literal `0` and `-lam` (`Rat.cast_neg`) itself. -/
theorem volcanoZoneQ_eq_volcanoZone (lam x : ℚ) :
    volcanoZoneQ lam x = volcanoZone (lam : ℝ) (x : ℝ) := by
  unfold volcanoZoneQ volcanoZone
  norm_cast

set_option linter.unusedVariables false in
/-- Recipe (ii): **the characterization lemma**, in the house shape. `split_ifs with h1 … h5`
produces exactly 6 goals, and the naming convention is: in branch `i`, `h1 … h_{i-1}` are the
**negated** earlier guards and `h_i` is the **positive** one; the final branch has `h1 … h5` all
negated. Each goal is closed by `iff_of_true rfl …` / `iff_of_false (by decide) …`.

**Measured linter fact:** an unused *hypothesis* is flagged (`warning: unused variable \`hlam\``),
exactly as in `PhotoLean/Hammond/RatModel.lean` (`hammondZoneQ_eq_atReactant_iff`); the house
response is a local `set_option linter.unusedVariables false in`, and it must be placed *before*
the doc comment (`set_option … in` → doc comment → declaration, the ordering rule recorded in
`proofs/API-NOTES.md` §kasha §4.4). -/
theorem volcanoZoneQ_eq_strong_iff {lam x : ℚ} (hlam : 0 < lam) :
    volcanoZoneQ lam x = VZone.strong ↔ lam < x := by
  unfold volcanoZoneQ
  split_ifs with h1 h2 h3 h4 h5
  · exact iff_of_false (by decide) (by rw [h1]; linarith)
  · exact iff_of_true rfl h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2

/-- Recipe (ii) on the *last* branch, where the **negated** hypotheses are the useful ones: in
the final branch `h1 … h5` are all negations, and those negations are exactly the arithmetic
content of the characterization. This is the shape `PhotoLean/Hammond/RatModel.lean`'s
`hammondZoneQ_eq_late_iff` uses (`le_of_not_gt h6`, `lt_of_le_of_ne … (Ne.symm h2)`). -/
theorem volcanoZoneQ_eq_weak_iff (lam x : ℚ) :
    volcanoZoneQ lam x = VZone.weak ↔
      ¬(x = lam) ∧ ¬(lam < x) ∧ ¬(x = 0) ∧ ¬(0 < x) ∧ ¬(x = -lam) := by
  unfold volcanoZoneQ
  split_ifs with h1 h2 h3 h4 h5
  · exact iff_of_false (by decide) (by rintro ⟨h, -⟩; exact h h1)
  · exact iff_of_false (by decide) (by rintro ⟨-, h, -⟩; exact h h2)
  · exact iff_of_false (by decide) (by rintro ⟨-, -, h, -⟩; exact h h3)
  · exact iff_of_false (by decide) (by rintro ⟨-, -, -, h, -⟩; exact h h4)
  · exact iff_of_false (by decide) (by rintro ⟨-, -, -, -, h⟩; exact h h5)
  · exact iff_of_true rfl ⟨h1, h2, h3, h4, h5⟩

/-- Recipe: the *backward* direction of a characterization, in the house style — `unfold` the
classifier and rewrite each guard with the explicit `if_neg` / `if_pos`, each side condition
discharged inline by `linarith`/`norm_num`. This is the `PhotoLean/BEP/Basic.lean` `epZone` route
(the forward direction there used `split_ifs at h`). -/
theorem volcanoZone_eq_strong {lam x : ℝ} (h : lam < x) :
    volcanoZone lam x = VZone.strong := by
  unfold volcanoZone
  rw [if_neg (by rintro rfl; exact absurd h (lt_irrefl _)), if_pos h]

/-- Recipe: a kernel-computed verdict on the rational side (`norm_num` reduces the whole
`if`-cascade of concrete rational comparisons), then the transfer makes it a statement about the
real theory. This is the `Rat.epQVerdict` recipe of `proofs/API-NOTES.md` §BEP §3.

**Trap (measured):** `rw [← volcanoZoneQ_eq_volcanoZone (2 : ℚ) (3 : ℚ)]` does **not** match a
goal stated with the ℝ literals `(2 : ℝ)`, `(3 : ℝ)`: the error is
`tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  volcanoZone ↑2 ↑3`, because `(2 : ℝ)` is `OfNat.ofNat 2` and not syntactically `↑(2 : ℚ)`.
Fix: prove the ℚ-literal form in a `have` and let `simpa` close the numeral gap. -/
theorem volcanoZone_verdict_at_two :
    volcanoZone (2 : ℝ) (3 : ℝ) = VZone.strong := by
  have h : volcanoZone ((2 : ℚ) : ℝ) ((3 : ℚ) : ℝ) = VZone.strong := by
    rw [← volcanoZoneQ_eq_volcanoZone (2 : ℚ) (3 : ℚ)]
    unfold volcanoZoneQ
    norm_num
  simpa using h

end ApiProbeCastIte
end Sabatier
end PhotoLean
