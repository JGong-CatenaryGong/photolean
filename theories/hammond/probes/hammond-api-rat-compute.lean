/-
Hammond milestone — API probe (topic E): which ℚ-side evaluations reduce by computation.

Rule confirmed here (refinement of the Marcus-round rule recorded in `proofs/API-NOTES.md`):

* `decide` works **only when no division is evaluated**, neither in a literal nor inside the
  definition being evaluated.  `hammondZoneQ 1 0 = HZone.half` is fine (its `if`-chain only
  compares integer-valued rationals), but `hammondZoneQ 1 (3 / 4) = HZone.early` and even
  `tsCoordQ 1 0 = 1 / 2` fail (the rational division `3 / 4`, resp. `tsCoordQ`'s internal
  `a / b`, is not reduced by the kernel's `decide`).
* `norm_num [<defs>]` is the reliable tactic for every rational-literal evaluation, and it
  must be given **every** definition in the expression: `norm_num [lefflerSecantQ]` leaves
  `gapReactantQ` opaque and fails; `norm_num [lefflerSecantQ, gapReactantQ]` works.
* `native_decide` evaluates all of them, but it is **forbidden** by this project's axiom
  discipline: measured `#print axioms` gives `[propext, Lean.ofReduceBool]`, and
  `ALLOWED_AXIOMS` in `proofs/ENGINE.yml` does not contain `Lean.ofReduceBool`.

Running:  proofs/scripts/lake env lean theories/hammond/probes/hammond-api-rat-compute.lean
Status:   0 errors / 0 warnings.
-/
import Mathlib
import PhotoLean.Marcus.RatModel

namespace PhotoLean.Hammond.ProbeRatCompute

/-- Zone classification (same shape as the ℝ-side `HZone`). -/
inductive HZone where
  | early | half | late | atReactant | atProduct | beyondReactant | beyondProduct
  deriving DecidableEq, Repr

/-- ℚ-side classifier, verbatim copy of the planned `PhotoLean.Hammond.Rat.hammondZoneQ`. -/
def hammondZoneQ (lam x : ℚ) : HZone :=
  if x = lam then HZone.atReactant
  else if x = -lam then HZone.atProduct
  else if x < -lam then HZone.beyondProduct
  else if lam < x then HZone.beyondReactant
  else if x = 0 then HZone.half
  else if 0 < x then HZone.early
  else HZone.late

/-- ℚ-side transition-state coordinate (planned `PhotoLean.Hammond.Rat.tsCoordQ`). -/
def tsCoordQ (lam x : ℚ) : ℚ := (lam - x) / (2 * lam)

/-- ℚ-side reactant gap (planned `PhotoLean.Hammond.Rat.gapReactantQ`). -/
def gapReactantQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- ℚ-side Leffler secant (planned `PhotoLean.Hammond.Rat.lefflerSecantQ`). -/
def lefflerSecantQ (lam x₁ x₂ : ℚ) : ℚ :=
  -(gapReactantQ lam x₂ - gapReactantQ lam x₁) / (x₂ - x₁)

/-! ## `decide` domain: integer-valued rationals only -/

/-- Integer numerators, no division evaluated — `decide` works. -/
theorem zoneQ_half_decide : hammondZoneQ 1 0 = HZone.half := by decide

/-- Integer numerators — `decide` works. -/
theorem zoneQ_atReactant_decide : hammondZoneQ 1 1 = HZone.atReactant := by decide

/-- Integer numerators — `decide` works. -/
theorem zoneQ_beyondReactant_decide : hammondZoneQ 1 3 = HZone.beyondReactant := by decide

/-- Degenerate curvature `lam = 0` (the `x / 0 = 0` convention) — `decide` still works,
because only comparisons are evaluated. -/
theorem zoneQ_zero_lam_decide : hammondZoneQ 0 0 = HZone.atReactant := by decide

/-! ## `norm_num` domain: every rational literal / definition -/

/-- The Marcus-style baseline: the same goal with `norm_num`. -/
theorem zoneQ_half_norm_num : hammondZoneQ 1 0 = HZone.half := by norm_num [hammondZoneQ]

/-- Rational literal `3 / 4`: `decide` fails, `norm_num` works. -/
theorem zoneQ_early : hammondZoneQ 1 (3 / 4) = HZone.early := by norm_num [hammondZoneQ]

/-- Rational literal `-1 / 2`. -/
theorem zoneQ_late : hammondZoneQ 1 (-1 / 2) = HZone.late := by norm_num [hammondZoneQ]

/-- Rational literals on both arguments. -/
theorem zoneQ_beyondReactant : hammondZoneQ (6 / 5) (12 / 5) = HZone.beyondReactant := by
  norm_num [hammondZoneQ]

/-- Integer numerator, rational value: `tsCoordQ (6/5) (1/20) = 23/48`. -/
theorem tsCoordQ_value : tsCoordQ (6 / 5) (1 / 20) = 23 / 48 := by norm_num [tsCoordQ]

/-- The thermoneutral value of the coordinate. -/
theorem tsCoordQ_half : tsCoordQ 1 0 = 1 / 2 := by norm_num [tsCoordQ]

/-- Two definitions deep: `norm_num` must be given **both** `lefflerSecantQ` and the
`gapReactantQ` it unfolds to. -/
theorem lefflerSecantQ_value :
    lefflerSecantQ (6 / 5) (3 / 5) (12 / 5) = -1 / 8 := by
  norm_num [lefflerSecantQ, gapReactantQ]

/-! ## The ℚ-side zone characterization — same `split_ifs` recipe as the ℝ side

`decide` cannot help here: the statement has free variables (`lam`, `x`), so there is nothing
to compute; `decide` only closes *closed* goals (see the `decide` domain above).  The
ℝ-side recipe of `hammond-api-zone-char.lean` transfers verbatim to ℚ — `linarith`,
`le_of_not_gt` and `lt_of_le_of_ne` are all order-generic.
-/

/-- ℚ-side `early` characterization, shortest form (identical to the ℝ-side recipe). -/
theorem zoneQ_early_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.early ↔ 0 < x ∧ x < lam := by
  unfold hammondZoneQ
  split_ifs with h1 h2 h3 h4 h5 h6 <;>
    first
      | exact iff_of_true rfl ⟨h6, lt_of_le_of_ne (le_of_not_gt h4) h1⟩
      | exact iff_of_false (by decide) (by rintro ⟨hx, hy⟩; linarith)

/-- ℚ-side `half` characterization, explicit-branch form (note the last leaf uses `h5`
directly, exactly as on the ℝ side). -/
theorem zoneQ_half_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.half ↔ x = 0 := by
  unfold hammondZoneQ
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_true rfl h5
  · exact iff_of_false (by decide) (ne_of_gt h6)
  · exact iff_of_false (by decide) h5

/-- ℚ-side `late` characterization.  Careful: the statement skeleton writes the conjunction
as `x < 0 ∧ -lam < x`, i.e. the *opposite* order from the ℝ-side lemma — each leaf then hands
its falsified conjunct in the other position, so the `rintro ⟨hx, -⟩` / `rintro ⟨-, hx⟩`
patterns must be swapped accordingly. -/
theorem zoneQ_late_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.late ↔ x < 0 ∧ -lam < x := by
  unfold hammondZoneQ
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨-, hx⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨-, hx⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_true rfl
      ⟨lt_of_le_of_ne (le_of_not_gt h6) h5, lt_of_le_of_ne (le_of_not_gt h3) (Ne.symm h2)⟩

/-- ℚ-side inverted-region branch. -/
theorem zoneQ_beyondReactant_iff {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.beyondReactant ↔ lam < x := by
  unfold hammondZoneQ
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_false (by decide) (by rw [h1]; linarith)
  · exact iff_of_false (by decide) (by rw [h2]; linarith)
  · exact iff_of_false (by decide) (by linarith)
  · exact iff_of_true rfl h4
  · exact iff_of_false (by decide) h4
  · exact iff_of_false (by decide) h4
  · exact iff_of_false (by decide) h4

/-- ℚ-side barrierless forward branch.  As on the ℝ side this is **unconditional** — the
statement skeleton's `(hlam : 0 < lam)` is not needed and would be reported as an unused
variable by the linter. -/
theorem zoneQ_atReactant_iff (lam x : ℚ) :
    hammondZoneQ lam x = HZone.atReactant ↔ x = lam := by
  unfold hammondZoneQ
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact iff_of_true rfl h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1

/-! ## Cross-link to the Marcus rational decision layer

⚠️ Measured pitfall: `Rat.cast_lt` has an **implicit** `K` (the target field), so the plain
`rw [← Rat.cast_lt]` gets stuck with

    error: typeclass instance problem is stuck, it is often due to metavariables
      LinearOrderedField ?m.99703

Give the field explicitly: `← (Rat.cast_lt (K := ℝ))`.  (`Rat.cast_inj` has the same trap;
see the Marcus round's note on `apply (Rat.cast_inj (α := ℝ)).mp`.)
-/

/-- The Hammond inverted branch is exactly Marcus's rational inverted region — the bridge that
makes a rational instance verdict binding on the Marcus theory as well. -/
theorem zoneQ_beyondReactant_iff_marcusInverted {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.beyondReactant ↔
      PhotoLean.Marcus.Rat.zoneQ lam x = PhotoLean.Marcus.Zone.inverted := by
  rw [zoneQ_beyondReactant_iff hlam, ← (Rat.cast_lt (K := ℝ)),
    PhotoLean.Marcus.Rat.zoneQ_inverted_iff]

/-! ## Measured negative results (documented, not reproducible as live code)

`decide` fails (measured error, verbatim):

    error: tactic 'decide' failed for proposition
      hammondZoneQ 1 (3 / 4) = HZone.early
    since its 'Decidable' instance
      instDecidableEqHZone (hammondZoneQ 1 (3 / 4)) HZone.early
    did not reduce to 'isTrue' or 'isFalse'.

The same error shape appears for `hammondZoneQ 1 (-1 / 2) = HZone.late`,
`hammondZoneQ (6 / 5) (12 / 5) = HZone.beyondReactant`,
`tsCoordQ (6 / 5) (1 / 20) = 23 / 48`,
`lefflerSecantQ (6 / 5) (3 / 5) (12 / 5) = -1 / 8`, and — importantly —
`tsCoordQ 1 0 = 1 / 2` (integer inputs, but the *definition* divides, so the kernel's
`decide` still does not reduce it).

`norm_num [lefflerSecantQ]` alone fails with

    error: unsolved goals
    ⊢ (gapReactantQ (6 / 5) (3 / 5) - gapReactantQ (6 / 5) (12 / 5)) / (9 / 5) = -(1 / 8)

i.e. `norm_num` does not unfold definitions that the given definitions call.

`native_decide` (banned by the axiom discipline) does evaluate the division case; measured:

    #print axioms native_decide_probe
    'native_decide_probe' depends on axioms: [propext, Lean.ofReduceBool]

Since `ALLOWED_AXIOMS="propext Classical.choice Quot.sound"`, any delivered theorem proved
with `native_decide` would fail `proofs/scripts/axioms.sh`.

`omega` is not an option on ℚ either (it only handles `Nat` / `Int`); measured on
`example {lam : ℚ} (h : 0 < lam) : 0 < lam + lam := by omega`:

    error: omega could not prove the goal:
    No usable constraints found. You may need to unfold definitions so `omega` can see linear
    arithmetic facts about `Nat` and `Int`, ...
-/

end PhotoLean.Hammond.ProbeRatCompute
