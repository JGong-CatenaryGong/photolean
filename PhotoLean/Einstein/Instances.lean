/-
PhotoLean.Einstein.Instances — milestone EB-I, the named-instance layer.

Two named surrogate instances of the equivalence chain, computed exactly in the rational decision
layer of `PhotoLean/Einstein/RatModel.lean` (plan §4, EB-I):

* `twoLevelDyeLike` — the two-level dye-like surrogate (`K = 3`, `Cf = 5`, `g₁ = 1`, `g₂ = 3`, at
  the transition value `A = 2`): the three legs of `full_chain_roundtrip` (EB-C6) computed at `ℚ`,
  in the EB-C6 order (f-leg, A↔B leg, degeneracy leg);
* `degeneracySwap` — the degeneracy-swap instance (`g₁ = 1`, `g₂ = 3`, `B₂₁ = 2`): the measured
  asymmetry of detailed balance read both ways (`B₁₂ = 3·B₂₁ = 6` up, `B₂₁ = (1/3)·B₁₂ = 2` down)
  and the double swap closed.

Honest scope (plan §9 row 3): these are *rational surrogate constants*, not the physical constants
of any real transition — the physical radiation-density factor contains `π` and is irrational
(`PhotoLean.Einstein.radFactor_not_rational`). What the rows show is that the chain's algebra closes
exactly at the named surrogates.

Measured tactic boundary (as in EB-R): `decide` does not reduce `ℚ` division in mathlib v4.17.0, so
both rows are closed by `norm_num [Rat.…]`. The declaration docstrings below keep the authority's
"by `decide`" wording verbatim; the tactic that actually closes them is `norm_num`.

Statement authority: `theories/Einstein/probes/Einstein-statement-skeleton.lean` § EB-I; every
signature below is identical to its authority row. There is no unproved placeholder and no custom
axiomatic declaration anywhere in this file.

Acceptance:
    proofs/scripts/lake build PhotoLean.Einstein.Instances
    proofs/scripts/axioms.sh PhotoLean.Einstein.Instances PhotoLean.Einstein.twoLevelDyeLike
    proofs/scripts/check.sh --strict PhotoLean.Einstein.Instances
-/
import PhotoLean.Einstein.RatModel

set_option autoImplicit false

namespace PhotoLean

namespace Einstein

/-! ## EB-I — named instances -/

/-- The two-level dye-like surrogate instance (`K = 3`, `Cf = 5`, `g1 = 1`, `g2 = 3`, at the
transition value `A = 2`): the full round trip of the equivalence chain computed at ℚ — the three
legs in the EB-C6 order. Plan section 4, row EB-I1. Proof route (plan §4): `decide`. -/
theorem twoLevelDyeLike :
    Rat.fOfA 5 1 3 2 / (5 * (3 / 1)) = 2 ∧
    Rat.aOfB 3 (Rat.aOfB 3 2 / 3) / 3 = 2 ∧
    Rat.b12OfB21 3 1 (Rat.b12OfB21 1 3 2) = 2 := by
  norm_num [Rat.fOfA, Rat.aOfB, Rat.b12OfB21]

/-- The degeneracy-swap instance (`g1 = 1`, `g2 = 3`, at `B21 = 2`): the B12/B21 asymmetry computed
both ways (`B12 = 3·B21 = 6` up, `B21 = (1/3)·B12 = 2` down) and the round trip closed. Plan
section 4, row EB-I2. Proof route (plan §4): `decide`. -/
theorem degeneracySwap :
    Rat.b12OfB21 1 3 2 = 6 ∧
    Rat.b12OfB21 3 1 6 = 2 ∧
    Rat.b12OfB21 3 1 (Rat.b12OfB21 1 3 2) = 2 := by
  norm_num [Rat.b12OfB21]

end Einstein

end PhotoLean
