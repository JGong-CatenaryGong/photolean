/-
Sabatier API calibration — probe (b): monotonicity on a half-line.

Owner: api_researcher. Evidence behind the `## Sabatier theory (2026-09-21)` section of
`proofs/API-NOTES.md`. Run from the repository root with

  proofs/scripts/lake env lean theories/Sabatier/probes/sabatier-api-monotone.lean

The volcano statements need "the rate is strictly increasing on one side of the apex" and
"strictly decreasing on the other side". The delivered PhotoLean sources never use
`StrictMonoOn`/`MonotoneOn`/`Set.Iic`/`Set.Ici` (measured: 0 occurrences under `PhotoLean/`);
they state monotonicity as **plain `∀`-statements with explicit hypotheses**. This probe
verifies (i) the mathlib `Set`-predicate API, and (ii) the two-way bridge between that API and
the house `∀`-form, using the delivered definitions `Marcus.NormalDescriptor`,
`Marcus.InvertedDescriptor` and `Hammond.HammondDescriptor`.
-/
import Mathlib
import PhotoLean.Marcus.Basic
import PhotoLean.Hammond.Basic

namespace PhotoLean
namespace Sabatier
namespace ApiProbeMonotone

/-! ## 1. The four `Set`-predicates — verbatim definitions -/

#print StrictMonoOn
#print StrictAntiOn
#print MonotoneOn
#print AntitoneOn

#check @StrictMonoOn
#check @StrictAntiOn
#check @MonotoneOn
#check @AntitoneOn

/-! ## 2. The lemmas that make an `intro`-style proof terminate -/

#check @monotoneOn_iff_forall_lt
#check @antitoneOn_iff_forall_lt
#check @StrictMonoOn.monotoneOn
#check @StrictAntiOn.antitoneOn
#check @StrictMonoOn.le_iff_le
#check @StrictMonoOn.lt_iff_lt
#check @StrictMonoOn.eq_iff_eq
#check @StrictMonoOn.compares
#check @StrictMonoOn.injOn
#check @Set.strictMonoOn_iff_strictMono
#check @strictMonoOn_univ
#check @strictMonoOn_id
#check @Set.strictMonoOn_singleton
#check @strictMonoOn_insert_iff
#check @Set.monotoneOn_iff_monotone
#check @monotoneOn_id
#check @monotoneOn_const
#check @antitoneOn_const
#check @Set.monotoneOn_singleton
#check @strictMono_restrict
#check @StrictMonoOn.restrict
#check @MonotoneOn.mono
#check @AntitoneOn.mono
#check @StrictMonoOn.mono
#check @StrictAntiOn.mono
#check @MonotoneOn.monotone
#check @StrictMonoOn.strictMono
#check @StrictMonoOn.comp
#check @StrictAntiOn.comp
#check @StrictMonoOn.comp_strictAntiOn
#check @StrictAntiOn.comp_strictMonoOn
#check @StrictMonoOn.Iic_union_Ici
#check @StrictMonoOn.union

/-! ## 3. Membership rewriting for `Set.Iic` / `Set.Ici` / `Set.Icc` -/

#check @Set.Iic
#check @Set.Ici
#check @Set.mem_Iic
#check @Set.mem_Ici
#check @Set.mem_Iio
#check @Set.mem_Ioi
#check @Set.mem_Icc
#check @Set.mem_univ
#check @Set.MapsTo

/-- Recipe: `x ∈ Set.Iic b` and `x ≤ b` are the *same* term up to definitional equality, so no
rewrite is needed at all. -/
example {x b : ℝ} (hx : x ∈ Set.Iic b) : x ≤ b := hx

/-- Recipe: the same in the reverse direction. -/
example {x b : ℝ} (hx : x ≤ b) : x ∈ Set.Iic b := hx

/-- Recipe: the explicit projections, when a `rw`/`simp` needs a named lemma. -/
example {x b : ℝ} (hx : x ∈ Set.Iic b) : x ≤ b := Set.mem_Iic.mp hx

/-- Recipe: `_root_.Set.mem_Ici` for a half-line to the right. -/
example {a x : ℝ} (hx : x ∈ Set.Ici a) : a ≤ x := Set.mem_Ici.mp hx

/-- Recipe: build an `Ici`-membership from an inequality. -/
example {a x : ℝ} (hx : a ≤ x) : x ∈ Set.Ici a := Set.mem_Ici.mpr hx

/-- Recipe: build an `Icc`-membership from a conjunction (this is how the two-sided volcano
window is fed to `StrictMonoOn`). -/
example {a b x : ℝ} (hx : a ≤ x ∧ x ≤ b) : x ∈ Set.Icc a b := Set.mem_Icc.mpr hx

/-! ## 4. `intro`-style proofs that terminate

`StrictMonoOn f s` unfolds to `∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a < b → f a < f b`, so a bare
`intro` introduces the two elements, the two membership proofs and the order hypothesis, in
that order. -/

/-- Recipe: the whole content of a half-line monotonicity proof, with `linarith` doing the
arithmetic (this is exactly the shape the volcano criterion needs). **Trap (measured):** after
`intro`, the goal still contains the beta-redex `(fun x => 2 * x) x`, and `linarith` treats it as
an opaque atom — it then fails with `linarith failed to find a contradiction`. Run `dsimp only`
(or `show`) first to beta-reduce. -/
example : StrictMonoOn (fun x : ℝ => 2 * x) (Set.Ici (0 : ℝ)) := by
  intro x _ y _ hxy
  dsimp only
  linarith

/-- Recipe: **consume** a `StrictMonoOn` half-line hypothesis in the house style — the
membership proofs are discharged by the two explicit `≤` hypotheses, with no `Set` syntax at
the use site. -/
example {f : ℝ → ℝ} (hf : StrictMonoOn f (Set.Ici (1 : ℝ))) {x y : ℝ}
    (hx : (1 : ℝ) ≤ x) (hy : (1 : ℝ) ≤ y) (hxy : x < y) : f x < f y :=
  hf hx hy hxy

/-- Recipe: the antitone twin (`f y < f x`). -/
example {f : ℝ → ℝ} (hf : StrictAntiOn f (Set.Iic (1 : ℝ))) {x y : ℝ}
    (hx : x ≤ (1 : ℝ)) (hy : y ≤ (1 : ℝ)) (hxy : x < y) : f y < f x :=
  hf hx hy hxy

/-- Recipe: a strictly monotone function on `Set.Ici a` is automatically monotone there
(`StrictMonoOn.monotoneOn`) — the usable bridge when a later step only needs `≤`. -/
example {f : ℝ → ℝ} (hf : StrictMonoOn f (Set.Ici (1 : ℝ))) {x y : ℝ}
    (hx : (1 : ℝ) ≤ x) (hy : (1 : ℝ) ≤ y) (hxy : x ≤ y) : f x ≤ f y :=
  hf.monotoneOn hx hy hxy

/-- Recipe: `StrictMonoOn.lt_iff_lt` — the `iff` form, which is what turns a monotone
bijection-style argument into a comparison of arguments. -/
example {f : ℝ → ℝ} (hf : StrictMonoOn f (Set.Ici (1 : ℝ))) {x y : ℝ}
    (hx : (1 : ℝ) ≤ x) (hy : (1 : ℝ) ≤ y) : f x < f y ↔ x < y :=
  hf.lt_iff_lt hx hy

/-- Recipe: restricting a half-line statement to a smaller half-line — `StrictMonoOn.mono`
(**this name does exist**, contrary to a first grep that missed the `_root_.` prefix). -/
example {f : ℝ → ℝ} (hf : StrictMonoOn f (Set.Ici (0 : ℝ))) :
    StrictMonoOn f (Set.Ici (1 : ℝ)) :=
  hf.mono fun _ hx => le_trans (show (0 : ℝ) ≤ 1 by norm_num) hx

/-- Recipe: the constant function is monotone on any set — `monotoneOn_const`. There is **no**
`strictMonoOn_const` (and there cannot be: a constant function is not strictly monotone on a
nontrivial set). -/
example (c : ℝ) (s : Set ℝ) : MonotoneOn (fun _ : ℝ => c) s := monotoneOn_const

/-- Recipe: `StrictMonoOn.comp` needs a `Set.MapsTo` side condition. -/
example {f g : ℝ → ℝ} (hg : StrictMonoOn g (Set.Ici (0 : ℝ)))
    (hf : StrictMonoOn f (Set.Ici (0 : ℝ))) (hmap : Set.MapsTo f (Set.Ici (0 : ℝ)) (Set.Ici (0 : ℝ))) :
    StrictMonoOn (g ∘ f) (Set.Ici (0 : ℝ)) :=
  hg.comp hf hmap

/-- Recipe: composing with a strictly positive scalar at the `intro` level (the house route: no
name needed for the rescaling, `intro` + `linarith` after the `StrictMonoOn` call). -/
example {f : ℝ → ℝ} (hf : StrictMonoOn f (Set.Ici (0 : ℝ))) :
    StrictMonoOn (fun x => 2 * f x) (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have h := hf hx hy hxy
  dsimp only
  linarith

/-- Recipe: the `Set`-predicate view of the subtype (`StrictMonoOn.strictMono`), for a
`StrictMono`-shaped consumer. -/
example {f : ℝ → ℝ} (hf : StrictMonoOn f (Set.Ici (0 : ℝ))) :
    StrictMono (f ∘ (Subtype.val : Set.Ici (0 : ℝ) → ℝ)) :=
  hf.strictMono

/-! ## 5. The house-pattern bridge (kernel-verified on the delivered definitions)

`proofs/API-NOTES.md` §(b) records the measured house pattern: the delivered Marcus/Hammond
descriptors are plain `∀`-statements with explicit side hypotheses, and `StrictMonoOn` occurs
nowhere under `PhotoLean/`. The four equivalences below show the two forms are interderivable,
so the Sabatier layer may stay in the house `∀`-form and still call the mathlib
`StrictMonoOn` toolkit (or move to `Set`-predicates without losing anything). -/

/-- `Marcus.NormalDescriptor` **is** `StrictMonoOn` on the two-sided window `Set.Icc 0 lam`. -/
example (A lam kB T : ℝ) :
    Marcus.NormalDescriptor A lam kB T ↔
      StrictMonoOn (fun x => Marcus.rate A lam kB T x) (Set.Icc 0 lam) := by
  unfold Marcus.NormalDescriptor
  constructor
  · intro h x hx y hy hxy
    exact h x y (Set.mem_Icc.mp hx).1 hxy (Set.mem_Icc.mp hy).2
  · intro h x₁ x₂ h₁ h₂ h₃
    exact h (Set.mem_Icc.mpr ⟨h₁, le_trans h₂.le h₃⟩)
      (Set.mem_Icc.mpr ⟨le_trans h₁ h₂.le, h₃⟩) h₂

/-- `Marcus.InvertedDescriptor` **is** `StrictAntiOn` on the *open* half-line `Set.Ioi lam`.
**Trap (measured, and it is a statement fact, not a name fact):** `Set.Ici lam` is the *wrong*
set here. `InvertedDescriptor` demands the *strict* side condition `lam < x₁`, while membership
in `Set.Ici lam` only gives `lam ≤ x₁`; the two do not match, and the proof fails at
`application type mismatch … has type lam ≤ x : Prop but is expected to have type lam < x : Prop`
(that is, the resulting `↔` is simply false at `x₁ = lam`). Use `Set.Ioi`. -/
example (A lam kB T : ℝ) :
    Marcus.InvertedDescriptor A lam kB T ↔
      StrictAntiOn (fun x => Marcus.rate A lam kB T x) (Set.Ioi lam) := by
  unfold Marcus.InvertedDescriptor
  constructor
  · intro h x hx y _ hxy
    exact h x y (Set.mem_Ioi.mp hx) hxy
  · intro h x₁ x₂ h₁ h₂
    exact h (Set.mem_Ioi.mpr h₁) (Set.mem_Ioi.mpr (lt_trans h₁ h₂)) h₂

/-- `Hammond.HammondDescriptor` **is** `StrictAntiOn` on `Set.univ`. -/
example (lam : ℝ) :
    Hammond.HammondDescriptor lam ↔
      StrictAntiOn (fun x => Hammond.tsCoord lam x) Set.univ := by
  unfold Hammond.HammondDescriptor
  constructor
  · intro h x _ y _ hxy
    exact h x y hxy
  · intro h x y hxy
    exact h (Set.mem_univ x) (Set.mem_univ y) hxy

/-- The house `∀`-descriptor is *literally* the unfolded `Set`-predicate: the `↔` of the
previous three rows is available definitionally on `Set.univ` (`strictMonoOn_univ`). -/
example {f : ℝ → ℝ} : StrictMonoOn f Set.univ ↔ StrictMono f := strictMonoOn_univ

end ApiProbeMonotone
end Sabatier
end PhotoLean
