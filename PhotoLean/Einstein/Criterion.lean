/-
PhotoLean.Einstein.Criterion — milestone EB-C, the equivalence chain.

The theory: the **Einstein A/B coefficients of one electronic transition and the
oscillator-strength equivalence chain** (plan `theories/Einstein/plan.md` §1.1, §4). The content of
the theory is invertibility: knowing any one of `{A, B₂₁, B₁₂, f, ∫ε}` determines all others, and
every round trip around the chain is the identity. This module carries the thirteen EB-C rows:

* EB-C1 `radFactor_pos` — the radiation-density factor is positive (explicit positivity premises);
* EB-C2 `bOfA_roundtrip`, `aOfb_roundtrip` — A↔B invertibility, both directions;
* EB-C3 `detailed_balance`, `degeneracy_roundtrip` — the symmetric detailed-balance form and the
  double degeneracy swap;
* EB-C4 `af_roundtrip`, `fa_roundtrip` — A↔f invertibility, both directions;
* EB-C5 `int_roundtrip`, `aOfInt_roundtrip` — the Strickler–Berg leg, both directions;
* EB-C6 `full_chain_roundtrip` — the whole cycle named by one row;
* EB-C7 `f_pos_iff_a_pos` — positivity transport across the collected factor;
* EB-C8 `yield_radiative`, `lifetime_pos` — the yield anchor and the radiative lifetime.

Every physical premise is an explicit hypothesis and none is hidden in a definition (engine rule 3):
positivity of `h`, `c`, `ν` (EB-C1), of the degeneracies `g₁`, `g₂` (EB-C3/C4/C7) and of `A` (EB-C8),
and non-vanishing of the collected conversion factors `K`, `Cf`, `Ci` (EB-C2/C4/C5/C6). The
degeneracy-positivity premises are load-bearing in their rows; EB-C3's symmetric form needs only
`0 < g₁`, which is the weakest-premise form frozen in the plan §4.

Two records of the statement layer, both about the authority rather than about this module:
* the EB-C6 middle conjunct is the **corrected** spelling: `aOfB K (aOfB K A / K) / K = A`. The plan
  §4 literal `… = A / K` is false (at `K = 2`, `A = 1` it claims `1 = 1/2`; the composed round trip
  returns `A`), and the authority `theories/Einstein/probes/Einstein-statement-skeleton.lean` already
  carries the corrected right-hand side; the plan's §4 row still shows the old one while the plan's
  §3.1 correction log is empty — a documentation-plane gap reported by prover_d, not a statement
  change here.
* EB-C8's `yield_radiative` supersedes the design-time `fluorescence_lifetime` triviality; it is
  stated so the QuantumYield composition edge has a home (plan §10).

Statement authority: `theories/Einstein/probes/Einstein-statement-skeleton.lean` § EB-C; every
signature below is identical to its authority row. There is no unproved placeholder and no custom
axiomatic declaration anywhere in this file. The `#print axioms` gate of every theorem below lists
at most `propext`, `Classical.choice`, `Quot.sound`.

Acceptance:
    proofs/scripts/lake build PhotoLean.Einstein.Criterion
    proofs/scripts/axioms.sh PhotoLean.Einstein.Criterion PhotoLean.Einstein.full_chain_roundtrip
    proofs/scripts/check.sh --strict PhotoLean.Einstein.Criterion
-/
import PhotoLean.Einstein.Basic

set_option autoImplicit false

namespace PhotoLean

namespace Einstein

/-! ## EB-C — the equivalence chain -/

/-- The radiation-density factor is positive at positive Planck constant, light speed and
frequency. Plan section 4, row EB-C1. Proof route (plan §5): `Real.pi_pos` + `mul_pos`/`div_pos`
chains (probe dry-run: `positivity` once `Real.pi_pos` is in context). -/
theorem radFactor_pos {h c ν : ℝ} (hh : 0 < h) (hc : 0 < c) (hν : 0 < ν) :
    0 < radFactor h c ν := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h3 : (0 : ℝ) < ν ^ 3 := pow_pos hν 3
  have hc3 : (0 : ℝ) < c ^ 3 := pow_pos hc 3
  unfold radFactor
  positivity

/-- A↔B invertibility, B-side: computing `A = K·B₂₁` and dividing back recovers `B₂₁`.
Plan section 4, row EB-C2. Proof route (plan §5): `field_simp` + `ring`. -/
theorem bOfA_roundtrip {K : ℝ} (hK : K ≠ 0) (B21 : ℝ) : aOfB K B21 / K = B21 := by
  unfold aOfB
  exact mul_div_cancel_left₀ B21 hK

/-- A↔B invertibility, A-side: `K · (A/K) = A`. Plan section 4, row EB-C2 (second form; the plan's
spelling `aOfb_roundtrip` is kept verbatim). Proof route (plan §5): `field_simp` + `ring`. -/
theorem aOfb_roundtrip {K : ℝ} (hK : K ≠ 0) (A : ℝ) : aOfB K (A / K) = A := by
  unfold aOfB
  exact mul_div_cancel₀ A hK

/-- Detailed balance, symmetric form: `B₁₂ = (g₂/g₁)·B₂₁` iff `g₁·B₁₂ = g₂·B₂₁`. Only `g₁` needs a
positivity premise (weakest-premise form as frozen in the plan). Plan section 4, row EB-C3.
Proof route (plan §5): `div_mul_eq_mul_div` + `mul_right_cancel₀`/`div_eq_iff` algebra. -/
theorem detailed_balance {g1 : ℝ} (hg1 : 0 < g1) (g2 B21 B12 : ℝ) :
    (b12OfB21 g1 g2 B21 = B12 ↔ g1 * B12 = g2 * B21) := by
  unfold b12OfB21
  rw [div_mul_eq_mul_div, div_eq_iff (ne_of_gt hg1), mul_comm B12 g1]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- The double degeneracy swap is the identity. Plan section 4, row EB-C3 (second form).
Proof route (plan §5): `field_simp` + `ring`. -/
theorem degeneracy_roundtrip {g1 g2 : ℝ} (hg1 : 0 < g1) (hg2 : 0 < g2) (B : ℝ) :
    b12OfB21 g2 g1 (b12OfB21 g1 g2 B) = B := by
  unfold b12OfB21
  field_simp
  ring

/-- A↔f invertibility, A-side: the oscillator strength divided back by its collected factor
recovers `A`. Plan section 4, row EB-C4. Proof route (plan §5): `field_simp` + `ring`. -/
theorem af_roundtrip {Cf g1 g2 : ℝ} (hCf : Cf ≠ 0) (hg1 : 0 < g1) (hg2 : 0 < g2) (A : ℝ) :
    fOfA Cf g1 g2 A / (Cf * (g2 / g1)) = A := by
  have h : Cf * (g2 / g1) ≠ 0 :=
    mul_ne_zero hCf (div_ne_zero (ne_of_gt hg2) (ne_of_gt hg1))
  unfold fOfA
  exact mul_div_cancel_left₀ A h

/-- A↔f invertibility, f-side — the plan's "forward form" (the plan gives the row but no name;
`fa_roundtrip` is assigned here, mirroring the EB-C2 pair). Plan section 4, row EB-C4 (forward
form). Proof route (plan §5): `field_simp` + `ring`. -/
theorem fa_roundtrip {Cf g1 g2 : ℝ} (hCf : Cf ≠ 0) (hg1 : 0 < g1) (hg2 : 0 < g2) (f : ℝ) :
    fOfA Cf g1 g2 (f / (Cf * (g2 / g1))) = f := by
  have h : Cf * (g2 / g1) ≠ 0 :=
    mul_ne_zero hCf (div_ne_zero (ne_of_gt hg2) (ne_of_gt hg1))
  unfold fOfA
  exact mul_div_cancel₀ f h

/-- The Strickler–Berg leg, I-side: the radiative rate divided back by `Ci` recovers the
integrated absorption. Plan section 4, row EB-C5. Proof route (plan §5): `field_simp` + `ring`. -/
theorem int_roundtrip {Ci : ℝ} (hCi : Ci ≠ 0) (I : ℝ) : aOfInt Ci I / Ci = I := by
  unfold aOfInt
  exact mul_div_cancel_left₀ I hCi

/-- The Strickler–Berg leg, A-side — the plan's "forward" form (unnamed in the plan;
`aOfInt_roundtrip` is assigned here, mirroring EB-C2's `aOfb_roundtrip`). Plan section 4, row
EB-C5 (forward). Proof route (plan §5): `field_simp` + `ring`. -/
theorem aOfInt_roundtrip {Ci : ℝ} (hCi : Ci ≠ 0) (A : ℝ) : aOfInt Ci (A / Ci) = A := by
  unfold aOfInt
  exact mul_div_cancel₀ A hCi

/-- The chain closes around every leg: the conjunction of the three legs at shared premises — one
row naming the whole cycle. Plan section 4, row EB-C6, **as corrected in plan §3.1 item 1**: the
plan's literal middle conjunct `… = A / K` is false (at `K = 2`, `A = 1` it claims `1 = 1/2`; the
composed round trip returns `A`), so the right-hand side is `A`. -/
theorem full_chain_roundtrip {K g1 g2 Cf : ℝ} (hK : K ≠ 0) (hg1 : 0 < g1) (hg2 : 0 < g2)
    (hCf : Cf ≠ 0) (A B21 : ℝ) :
    fOfA Cf g1 g2 A / (Cf * (g2 / g1)) = A ∧
    aOfB K (aOfB K A / K) / K = A ∧
    b12OfB21 g2 g1 (b12OfB21 g1 g2 B21) = B21 := by
  refine ⟨af_roundtrip hCf hg1 hg2 A, ?_, degeneracy_roundtrip hg1 hg2 B21⟩
  rw [bOfA_roundtrip hK (aOfB K A / K), bOfA_roundtrip hK A]

/-- Positivity transport across the A↔f leg: at positive `Cf`, `g₁`, `g₂` the oscillator strength
is positive exactly when `A` is. Plan section 4, row EB-C7. Proof route: `mul_pos` on the collected
positive factor, then `mul_pos_iff_of_pos_left`. -/
theorem f_pos_iff_a_pos {Cf g1 g2 : ℝ} (hCf : 0 < Cf) (hg1 : 0 < g1) (hg2 : 0 < g2) (A : ℝ) :
    (0 < fOfA Cf g1 g2 A ↔ 0 < A) := by
  have h : 0 < Cf * (g2 / g1) := mul_pos hCf (div_pos hg2 hg1)
  unfold fOfA
  exact mul_pos_iff_of_pos_left h

/-- The fluorescence yield of a two-channel decay is the radiative rate times the lifetime — the
QuantumYield edge anchor (corrected at design time, superseding the trivial `fluorescence_lifetime`;
trivial as algebra, stated so the edge has a home). Plan section 4, row EB-C8. Proof route:
`mul_one_div`. -/
theorem yield_radiative {A kNR : ℝ} (hA : 0 < A) (hkNR : 0 ≤ kNR) :
    A * (1 / (A + kNR)) = A / (A + kNR) := by
  rw [mul_one_div]

/-- The radiative lifetime of a positive A coefficient is positive. Plan section 4, row EB-C8
(second form). Proof route: `one_div_pos`. -/
theorem lifetime_pos {A : ℝ} (hA : 0 < A) : 0 < tauR A := by
  unfold tauR
  exact one_div_pos.mpr hA

end Einstein

end PhotoLean
