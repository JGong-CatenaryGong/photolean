/-
Sabatier API calibration — probe (a)+(c): `max` on `ℝ` and `abs`.

Owner: api_researcher. This file is the evidence behind the `## Sabatier theory (2026-09-21)`
section of `proofs/API-NOTES.md`. Run from the repository root with

  proofs/scripts/lake env lean theories/Sabatier/probes/sabatier-api-max-abs.lean

Never call `lake` directly (the toolchain is not on PATH) and never run `lake update`.
Every `#check` line below is verbatim compiler output (`#check` with `@` shows the implicit
arguments too); every `example` is a kernel-checked proof body, i.e. a recipe a prover can
transcribe. Nothing in this file names an unverified name: the names that survived `#check`
appear below, the ones that did not are recorded in `proofs/API-NOTES.md` §NOT FOUND.
-/
import Mathlib

namespace PhotoLean
namespace Sabatier
namespace ApiProbeMaxAbs

/-! ## (a) `max` on `ℝ` — the confirmed signature surface -/

#check @le_max_left
#check @le_max_right
#check @max_le
#check @max_le_iff
#check @le_max_iff
#check @lt_max_iff
#check @max_lt_iff
#check @max_eq_left
#check @max_eq_right
#check @max_eq_left_iff
#check @max_eq_right_iff
#check @max_comm
#check @max_assoc
#check @max_left_comm
#check @max_self
#check @max_idem
#check @max_eq_iff
#check @max_le_max
#check @max_le_max_left
#check @max_le_max_right
#check @min_le_max
#check @max_cases
#check @max_choice
#check @max_def
#check @le_max_of_le_left
#check @le_max_of_le_right

/-! ### (a1) Recipes for the goal shapes the volcano layer needs

The volcano statements are `max`-form minimizations: "the optimal descriptor maximizes the
activity", "the apex is `max (rate l₁) (rate l₂)`", etc. The useful goals are therefore
`max a b ≤ c`, `c ≤ max a b`, `max a b = a` and `max a b = c`. -/

/-- Recipe: goal `max a b ≤ c` — two projections, no tactic needed. -/
example {a b c : ℝ} (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c := max_le ha hb

/-- Recipe: goal `max a b ≤ c` — the `iff` form, for turning it into a conjunction. -/
example {a b c : ℝ} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c := max_le_iff

/-- Recipe: consume `max a b ≤ c` componentwise. -/
example {a b c : ℝ} (h : max a b ≤ c) : a ≤ c ∧ b ≤ c := max_le_iff.mp h

/-- Recipe: goal `a ≤ max a b` — left projection (this is the monotonicity of `max` in its
first argument, and it needs no hypotheses). -/
example {a b : ℝ} : a ≤ max a b := le_max_left a b

/-- Recipe: goal `b ≤ max a b` — right projection. -/
example {a b : ℝ} : b ≤ max a b := le_max_right a b

/-- Recipe: goal `c ≤ max a b` from one branch — `le_max_iff` is the usable `iff`. -/
example {a b c : ℝ} (h : c ≤ a) : c ≤ max a b := le_max_iff.mpr (Or.inl h)

/-- Recipe: goal `c ≤ max a b` from the other branch. -/
example {a b c : ℝ} (h : c ≤ b) : c ≤ max a b := le_max_of_le_right h

/-- Recipe: goal `a ≤ max b c` from `a ≤ b`. -/
example {a b c : ℝ} (h : a ≤ b) : a ≤ max b c := le_max_of_le_left h

/-- Recipe: goal `max a b = a` from `b ≤ a`. -/
example {a b : ℝ} (h : b ≤ a) : max a b = a := max_eq_left h

/-- Recipe: goal `max a b = b` from `a ≤ b`. -/
example {a b : ℝ} (h : a ≤ b) : max a b = b := max_eq_right h

/-- Recipe: the equality characterization `max a b = a ↔ b ≤ a`, in one step (this is the
house answer to "max a b = a iff b ≤ a"). -/
example {a b : ℝ} : max a b = a ↔ b ≤ a := max_eq_left_iff

/-- Recipe: the same, through `simp`. -/
example {a b : ℝ} : max a b = a ↔ b ≤ a := by simp only [max_eq_left_iff]

/-- Recipe: idempotence. **Name drift (measured):** `max_idem` exists, but it is *not* the
pointwise equation `max a a = a` — it is the **instance** `Std.IdempotentOp max`
(`Mathlib/Order/MinMax.lean:157`), so the usable form is the field projection
`max_idem.idempotent a`; writing `max_idem a` gives
`error: function expected at max_idem … term has type Std.IdempotentOp max`. The pointwise
lemma `max_self` is the simpler route. -/
example {a : ℝ} : max a a = a := max_idem.idempotent a

/-- Recipe: same statement through `max_self`. -/
example {a : ℝ} : max a a = a := max_self a

/-- Recipe: `max a b = b ↔ a ≤ b`. -/
example {a b : ℝ} : max a b = b ↔ a ≤ b := max_eq_right_iff

/-- Recipe: goal `max a b = c` — the full characterization, for a `rcases`. -/
example {a b c : ℝ} : max a b = c ↔ (a = c ∧ b ≤ a) ∨ (b = c ∧ a ≤ b) := max_eq_iff

/-- Recipe: **canonical tactic recipe for `max a b = …`** — split on which argument is larger
and rewrite. This is the shape that scales to a goal whose right-hand side mentions `a` or `b`
indirectly (the `linear_combination`-free route the house files use). -/
example (a b : ℝ) : max a b = a ∨ max a b = b := by
  rcases le_total a b with h | h
  · exact Or.inr (max_eq_right h)
  · exact Or.inl (max_eq_left h)

/-- Recipe: the same disjunction from the packaged `max_choice`. -/
example (a b : ℝ) : max a b = a ∨ max a b = b := max_choice a b

/-- Recipe: the packaged case analysis with the side conditions (`max_cases`). -/
example (a b : ℝ) : max a b = a ∧ b ≤ a ∨ max a b = b ∧ a < b := max_cases a b

/-- Recipe: rewrite `max` into an `if` when a `split_ifs` case analysis is wanted — this is the
bridge between the `max` layer and the classifier layer of §(g). -/
example (a b : ℝ) : max a b = if a ≤ b then b else a := max_def a b

/-- Recipe: goal `max a b = a` by contradiction-free case split inside a `have`. -/
example {a b : ℝ} (h : b ≤ a) : max a b = a := by
  rw [max_eq_left h]

/-- Recipe: monotonicity of `max` in both arguments at once (`max_le_max`). -/
example {a b c d : ℝ} (h₁ : a ≤ c) (h₂ : b ≤ d) : max a b ≤ max c d := max_le_max h₁ h₂

/-- Recipe: monotonicity in one argument (`max_le_max_left` / `max_le_max_right`). -/
example {a b c : ℝ} (h : a ≤ b) : max c a ≤ max c b := max_le_max_left c h

/-- Recipe: the `min`/`max` sandwich used by volcano-window arguments. -/
example {a b : ℝ} : min a b ≤ max a b := min_le_max

/-- Recipe: **the `max`-form minimization step** — "the optimum is one of the two candidate
values" written as a `≤`-bound that consumes `max`. -/
example {a b c : ℝ} (h : max a b ≤ c) : a ≤ c := (max_le_iff.mp h).1

/-- Recipe: the same bound consumed from the other side. **Trap (measured):** the rewrite must
go *backwards* — `rw [h]` with `h : max a b = c` fails on the goal `a ≤ c` with
`error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  a ⊔ b`, because the target does not contain `max a b` yet. Use `rw [← h]`. -/
example {a b c : ℝ} (h : max a b = c) : a ≤ c := by
  rw [← h]; exact le_max_left a b

/-- Recipe: `max a b = c` gives both branch bounds (again the rewrite is backwards). -/
example {a b c : ℝ} (h : max a b = c) : a ≤ c ∧ b ≤ c := by
  rw [← h]; exact ⟨le_max_left a b, le_max_right a b⟩

/-! ## (c) `abs` on `ℝ` — the confirmed signature surface -/

#check @abs_le
#check @abs_lt
#check @abs_le'
#check @abs_sub_comm
#check @abs_of_nonneg
#check @abs_of_nonpos
#check @abs_of_pos
#check @abs_of_neg
#check @neg_le_of_abs_le
#check @le_of_abs_le
#check @abs_sub_le_iff
#check @abs_sub_le
#check @abs_nonneg
#check @abs_nonpos_iff
#check @abs_pos
#check @abs_eq_max_neg

/-! ### (c1) The recipe that matters: `|x - y| ≤ t → x ≤ y + t` -/

/-- Recipe (shortest, kernel-checked): `abs_le` gives the conjunction, `linarith` closes. -/
example {x y t : ℝ} (h : |x - y| ≤ t) : x ≤ y + t := by
  have h' : x - y ≤ t := (abs_le.mp h).2
  linarith

/-- Recipe (one step): `le_of_abs_le` is exactly the second projection. -/
example {x y t : ℝ} (h : |x - y| ≤ t) : x ≤ y + t := by
  have h' : x - y ≤ t := le_of_abs_le h
  linarith

/-- Recipe (no `linarith` at all): the arithmetic step is `sub_le_iff_le_add'`. -/
example {x y t : ℝ} (h : |x - y| ≤ t) : x ≤ y + t :=
  sub_le_iff_le_add'.mp (le_of_abs_le h)

/-- Recipe (via the `abs_sub` specialisation): the first component of `abs_sub_le_iff`. -/
example {x y t : ℝ} (h : |x - y| ≤ t) : x ≤ y + t := by
  have h' : x - y ≤ t := (abs_sub_le_iff.mp h).1
  linarith

/-- Recipe: `linarith` with the projection supplied as a hint (the house style — a single line
that survives definition unfolding in the caller). -/
example {x y t : ℝ} (h : |x - y| ≤ t) : x ≤ y + t := by linarith [le_of_abs_le h]

/-- Recipe: the mirrored bound `y ≤ x + t`. -/
example {x y t : ℝ} (h : |x - y| ≤ t) : y ≤ x + t := by linarith [(abs_sub_le_iff.mp h).2]

/-- Recipe: symmetry of the argument order (`abs_sub_comm`), which is what lets the same
`abs_le` projection serve both mirrored statements. -/
example {x y t : ℝ} (h : |x - y| ≤ t) : |y - x| ≤ t := by rwa [abs_sub_comm]

/-- Recipe: the `≤ 0` collapse, used when a bound is squared/degenerate. -/
example {x : ℝ} (h : x ≤ 0) : |x| = -x := abs_of_nonpos h

/-- Recipe: the `0 ≤` collapse. -/
example {x : ℝ} (h : 0 ≤ x) : |x| = x := abs_of_nonneg h

/-- Recipe: `abs` of a positive quantity is the identity, in the branch where the sign is
already known (the volcano apex is a `√`-window; this is its sign bookkeeping). -/
example {x t : ℝ} (hx : 0 ≤ x) (h : |x| ≤ t) : x ≤ t := by
  rwa [abs_of_nonneg hx] at h

/-- Recipe: turn an `abs`-bound into a two-sided window (the form a `max`-free `linarith`
expects). -/
example {x y t : ℝ} (h : |x - y| ≤ t) : y - t ≤ x ∧ x ≤ y + t := by
  rw [abs_sub_le_iff] at h
  constructor <;> linarith [h.1, h.2]

/-- Recipe: `|x| ≤ t` with the explicit `neg_le_of_abs_le` projection (the left half). -/
example {x t : ℝ} (h : |x| ≤ t) : -t ≤ x := neg_le_of_abs_le h

end ApiProbeMaxAbs
end Sabatier
end PhotoLean
