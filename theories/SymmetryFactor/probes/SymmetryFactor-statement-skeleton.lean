/-
symmetryFactor-statement-skeleton.lean — the STATEMENT AUTHORITY of the symmetryFactor theory.

Statement-first (iron rule 2): every declaration below is the agreed statement verbatim; the bodies
are placeholders on purpose. This file must compile at 0 error
(`proofs/scripts/lake env lean theories/SymmetryFactor/probes/SymmetryFactor-statement-skeleton.lean`)
BEFORE any proof work starts; delivery replaces the bodies verbatim and
`python3 theories/BEP/probes/bep-fidelity.py --theory symmetryFactor` compares the delivered
signatures to this file word for word.

Milestones: F1 (Basic + Criterion), F2 (Sharp), F3 (RatModel), F4 (Instances).

The theory adjudicates the β = 1/2 symmetry-factor reading against the structural transfer
coefficient (thermoneutral crossing coordinate) of the UNEQUAL-curvature two-parabola model:
`BetaHalfReading kr kp ↔ kr = kp`, with kernel-checked witnesses (1,4) ↦ 2/3 and (4,1) ↦ 1/3,
and tie-back certificates to `PhotoLean.Kernel.tsCoord` / `PhotoLean.BEP.transfer` at equal
curvature. Literature anchors: `theories/SymmetryFactor/LITERATURE.md` (practice locus S1,
warning loci S2–S3).
-/
import Mathlib
import PhotoLean.Kernel
import PhotoLean.BEP.Criterion

open Real Set

namespace PhotoLean

namespace SymmetryFactor

/-! ## F1 — description layer (`PhotoLean/SymmetryFactor/Basic.lean`) -/

/-- Reactant potential-energy surface with curvature parameter `kr`: minimum at `q = 0`.
The equal-curvature kernel (`PhotoLean.Kernel.reactantSurface`) is the `kr = lam` reading. -/
noncomputable def asymReactantSurface (kr q : ℝ) : ℝ := kr * q ^ 2

/-- Product potential-energy surface with curvature parameter `kp`: minimum at `q = 1`, offset by
the reaction energy `dG = ΔG°`. -/
noncomputable def asymProductSurface (kp dG q : ℝ) : ℝ := kp * (q - 1) ^ 2 + dG

/-- The thermoneutral crossing: at `x = -ΔG° = 0` the two surfaces meet. -/
def CrossesAtThermoneutral (kr kp q : ℝ) : Prop :=
  asymReactantSurface kr q = asymProductSurface kp 0 q

/-- The structural transfer coefficient at thermoneutrality: the crossing coordinate of the
unequal-curvature two-parabola model, in closed form. At `kr = kp = lam` this is
`Kernel.tsCoord lam 0 = 1/2` (the tie-back certificates of F2). -/
noncomputable def tsCoordZero (kr kp : ℝ) : ℝ := Real.sqrt kp / (Real.sqrt kr + Real.sqrt kp)

/-- The β = 1/2 symmetry-factor reading, applied to this step: the working value the
electrochemical literature "usually takes" (LITERATURE S1) — as a claim about the structural
transfer coefficient of the model. -/
def BetaHalfReading (kr kp : ℝ) : Prop := tsCoordZero kr kp = 1 / 2

/-- The crossing predicate unfolds to the plain algebraic form (definitional unfolding row;
`asymProductSurface kp 0 q` carries the totalized `+ 0`). -/
theorem crosses_eq_algebra {kr kp q : ℝ} :
    CrossesAtThermoneutral kr kp q ↔ kr * q ^ 2 = kp * (q - 1) ^ 2 := by
  sorry

/-! ## F1 — law layer (`PhotoLean/SymmetryFactor/Criterion.lean`) -/

/-- The closed form is a coordinate: nonnegative **unconditionally** (totalized `Real.sqrt` is
nonnegative on every input, totalized division gives `0/0 = 0`; the first draft's `0 ≤ kr`,
`0 ≤ kp` premises were dropped as non-load-bearing — plan §3.1, weakest-premise standard). -/
theorem tsCoordZero_nonneg {kr kp : ℝ} : 0 ≤ tsCoordZero kr kp := by
  sorry

/-- The closed form never exceeds `1`, unconditionally (same totalization note; the first draft's
premises were dropped — plan §3.1). -/
theorem tsCoordZero_le_one {kr kp : ℝ} : tsCoordZero kr kp ≤ 1 := by
  sorry

/-- Positivity needs exactly one premise: a positive product curvature makes the numerator
positive and the denominator at least the numerator (weakest-premise standard: no premise on
`kr` is consumed — at `kr < 0` the totalized `Real.sqrt kr = 0` and the row still holds). -/
theorem tsCoordZero_pos {kr kp : ℝ} (hkp : 0 < kp) : 0 < tsCoordZero kr kp := by
  sorry

/-- Staying below `1` needs exactly one premise: a positive reactant curvature. -/
theorem tsCoordZero_lt_one {kr kp : ℝ} (hkr : 0 < kr) : tsCoordZero kr kp < 1 := by
  sorry

/-- The closed form IS the thermoneutral crossing of the two surfaces. -/
theorem tsCoordZero_crosses {kr kp : ℝ} (hkr : 0 < kr) (hkp : 0 < kp) :
    CrossesAtThermoneutral kr kp (tsCoordZero kr kp) := by
  sorry

/-- Uniqueness on the reaction interval: inside `[0,1]` the crossing point is exactly the closed
form. Proof route (calculus-free): both `√kr·q` and `√kp·(1-q)` are nonnegative with equal
squares, hence equal; then a linear solve. -/
theorem crossing_unique_in_unit_interval {kr kp q : ℝ} (hkr : 0 < kr) (hkp : 0 < kp)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hc : CrossesAtThermoneutral kr kp q) :
    q = tsCoordZero kr kp := by
  sorry

/-- The interval restriction is load-bearing: outside `[0,1]` the crossing equation has a second
real root. Kernel-checked witness at `(kr, kp) = (1, 4)`: `q = 2` satisfies `1·q² = 4·(q-1)²`
and `2 ∉ [0,1]`, while the delivered crossing coordinate is `2/3` (F2). -/
theorem crossing_witness_outside_interval :
    CrossesAtThermoneutral 1 4 2 ∧ (2 : ℝ) ∉ Set.Icc (0 : ℝ) 1 := by
  sorry

/-- A stiffer product well pushes the thermoneutral crossing later (strictly monotone in `kp`). -/
theorem tsCoordZero_strictMono_kp {kr kp kp' : ℝ} (hkr : 0 < kr) (hkp : 0 ≤ kp) (h : kp < kp') :
    tsCoordZero kr kp < tsCoordZero kr kp' := by
  sorry

/-- A stiffer reactant well pushes the thermoneutral crossing earlier (strictly antitone in
`kr`). -/
theorem tsCoordZero_strictAnti_kr {kr kr' kp : ℝ} (hkp : 0 < kp) (hkr : 0 ≤ kr) (h : kr < kr') :
    tsCoordZero kr' kp < tsCoordZero kr kp := by
  sorry

/-! ## F2 — sharp conditions and the verdicts (`PhotoLean/SymmetryFactor/Sharp.lean`) -/

/-- **The verdict (headline).** The β = 1/2 symmetry-factor reading coincides with the structural
transfer coefficient at thermoneutrality **exactly when the two force constants are equal**. The
equal-curvature Marcus picture is precisely the regime where the conflated reading survives —
which is why it survives (IUPAC TR 2014 pp. 255–256 predicts the deviation; LITERATURE S2). -/
theorem betaHalf_iff_equalForceConstants {kr kp : ℝ} (hkr : 0 < kr) (hkp : 0 < kp) :
    BetaHalfReading kr kp ↔ kr = kp := by
  sorry

/-- Kernel-checked witness, product well stiffer: `(kr, kp) = (1, 4)` gives `q‡₀ = 2/3`. -/
theorem tsCoordZero_one_four : tsCoordZero 1 4 = 2 / 3 := by
  sorry

/-- Kernel-checked witness, reactant well stiffer: `(kr, kp) = (4, 1)` gives `q‡₀ = 1/3` — the
direction asymmetry: the crossing sits on the side of the *softer* well. -/
theorem tsCoordZero_four_one : tsCoordZero 4 1 = 1 / 3 := by
  sorry

/-- The conflated reading, refuted at a kernel-checked parameter pair. -/
theorem betaHalf_falsified_by_unequal : ¬ BetaHalfReading 1 4 := by
  sorry

/-- The conflated reading is not a theorem of the model class: it fails for some admissible
positive force constants. -/
theorem not_betaHalf_universal :
    ¬ ∀ kr kp : ℝ, 0 < kr → 0 < kp → BetaHalfReading kr kp := by
  sorry

/-- Late transition state at ZERO driving force, exactly when the product well is stiffer — a
Hammond-style structural verdict that needs no driving force at all. -/
theorem tsCoordZero_gt_half_iff_stiffProduct {kr kp : ℝ} (hkr : 0 < kr) (hkp : 0 < kp) :
    (1 : ℝ) / 2 < tsCoordZero kr kp ↔ kr < kp := by
  sorry

/-- Early transition state at zero driving force, exactly when the reactant well is stiffer. -/
theorem tsCoordZero_lt_half_iff_stiffReactant {kr kp : ℝ} (hkr : 0 < kr) (hkp : 0 < kp) :
    tsCoordZero kr kp < (1 : ℝ) / 2 ↔ kp < kr := by
  sorry

/-- Tie-back certificate: at equal curvature the closed form is the delivered kernel coordinate at
thermoneutrality. -/
theorem tsCoordZero_eq_kernel_thermoneutral {lam : ℝ} (hlam : 0 < lam) :
    tsCoordZero lam lam = PhotoLean.Kernel.tsCoord lam 0 := by
  sorry

/-- The conflated reading HOLDS in the equal-curvature kernel model — the regime every textbook
picture draws. -/
theorem betaHalf_holds_in_kernel {lam : ℝ} (hlam : 0 < lam) : BetaHalfReading lam lam := by
  sorry

/-- Tie-back certificate: at equal curvature the closed form is the delivered BEP transfer
coefficient at thermoneutrality (`BEP.transfer_thermoneutral`). -/
theorem betaHalf_eq_transfer_thermoneutral {lam : ℝ} (hlam : 0 < lam) :
    tsCoordZero lam lam = PhotoLean.BEP.transfer lam 0 := by
  sorry

/-! ## F3 — the rational decision layer (`PhotoLean/SymmetryFactor/RatModel.lean`) -/

/-- The computable ℚ shadow at perfect-square curvatures: for `kr = a²`, `kp = b²` (positive
rationals) the crossing coordinate is the rational `b/(a+b)` — no `Real.sqrt` in the decision
layer (the Goldschmidt √-free-squares pattern). -/
def tsCoordZeroQ (a b : ℚ) : ℚ := b / (a + b)

/-- The β = 1/2 reading in the decision layer. -/
def BetaHalfQ (a b : ℚ) : Prop := tsCoordZeroQ a b = 1 / 2

/-- Cast bridge: the ℚ shadow computes the real closed form at perfect-square curvatures. -/
theorem tsCoordZeroQ_cast {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    tsCoordZero ((a : ℝ) * (a : ℝ)) ((b : ℝ) * (b : ℝ)) = (tsCoordZeroQ a b : ℝ) := by
  sorry

/-- The decision-layer verdict: `BetaHalfQ a b ↔ a = b` — decidable by `norm_num` per instance. -/
theorem betaHalfQ_iff {a b : ℚ} (ha : 0 < a) (hb : 0 < b) : BetaHalfQ a b ↔ a = b := by
  sorry

/-- Cast bridge for the reading: the ℚ verdict is the real verdict at the corresponding
perfect-square curvatures. -/
theorem betaHalfQ_cast {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    BetaHalfQ a b ↔ BetaHalfReading ((a : ℝ) * (a : ℝ)) ((b : ℝ) * (b : ℝ)) := by
  sorry

/-! ## F4 — instances and verdicts (`PhotoLean/SymmetryFactor/Instances.lean`) -/

/-- Verdict row, product well stiffer (`kr, kp = 1², 2²`): `q‡₀ = 2/3`, late side. A fact about
the printed numbers, decided by `norm_num`. -/
theorem inst_stiffProduct_lateTS :
    tsCoordZeroQ 1 2 = 2 / 3 ∧ (1 : ℚ) / 2 < tsCoordZeroQ 1 2 := by
  sorry

/-- Verdict row, reactant well stiffer (`kr, kp = 2², 1²`): `q‡₀ = 1/3`, early side. -/
theorem inst_stiffReactant_earlyTS :
    tsCoordZeroQ 2 1 = 1 / 3 ∧ tsCoordZeroQ 2 1 < (1 : ℚ) / 2 := by
  sorry

/-- Verdict row, symmetric (`kr = kp = 1²`): `q‡₀ = 1/2` — the conflated reading holds here, and
this is the whole equal-curvature family by the F2 iff. -/
theorem inst_symmetric_half : tsCoordZeroQ 1 1 = 1 / 2 ∧ BetaHalfQ 1 1 := by
  sorry

/-- **The adjudication as one kernel fact**: the β = 1/2 reading fails at `(1², 2²)` in BOTH
layers (ℚ decision and ℝ closed form) while the force constants are positive and unequal. This is
the row the H1 verdict cites. -/
theorem inst_conflation_falsified :
    ¬ BetaHalfQ 1 2 ∧ ¬ BetaHalfReading (1 : ℝ) 4 := by
  sorry

/-- Non-vacuity of both readings, pinned at concrete positive curvatures (the M1 lesson: no
bare `∃`-row that a degenerate parameter satisfies for free): the conflated reading holds at
`(1,1)` and fails at `(1,4)`. -/
theorem inst_nonvacuous_both_readings :
    BetaHalfReading (1 : ℝ) 1 ∧ ¬ BetaHalfReading (1 : ℝ) 4 := by
  sorry

end SymmetryFactor

end PhotoLean
