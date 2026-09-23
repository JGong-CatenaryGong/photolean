/-
PhotoLean.QuantumYield.Instances — milestone QY4, the named instances and their verdicts.

Three rate triples at the rational decision layer, each a representative of a literature yield
*ordering* rather than fitted data (plan `theories/QuantumYield/plan.md` §3.1 entry 0 and
`theories/QuantumYield/LITERATURE.md`; the docstrings below must not present them as the
recommended measured values — the literature's best current yields are fluorescein ≈ 0.95 and
quinine ≈ 0.546, so `9/10` and `11/20` are order-of-magnitude representatives only).

* **QY-I1, fluorescein S₁** — rates `(kF, kIC, kISC) = (18, 1, 1)`, fluorescence yield `φF = 9/10`
  and non-fluorescence share `1/10`.
* **QY-I2, quinine-like** — rates `(11, 5, 4)`, `φF = 11/20`.
* **QY-I3, quench dilution** — fluorescein S₁ with an added quenching channel of rate `9` at index
  `0` (`Fin.cons 9 fluoresceinS1`); the fluorescence channel moves to index `1`, its yield is
  diluted to `18/29`, and the Stern–Volmer ratio `φF(unquenched)/φF(quenched)` is `29/20` — the
  A2 edge rehearsal at ℚ (plan §10: the dilution factor of QY-C6 *is* the SV ratio's inverse).

Measured API boundary (api probe, `proofs/API-NOTES.md` §photobatch): `decide` does not reduce ℚ
division, and it does not even close the index application `quenchDilution 1 = 18` (measured while
proving this module); the whole verdict family closes by one `norm_num [Rat.yieldOf, Rat.totalRate,
…, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_three, Matrix.cons_val_zero/one/
two]` call per row, with the two instance verdicts of QY-I1/QY-I2 reusable as rewrite rules for the
ratio row.

Statement authority: `theories/QuantumYield/probes/QuantumYield-statement-skeleton.lean` § QY4;
every signature below is identical to its authority row. There is no unproved placeholder and no
custom axiomatic declaration anywhere in this file. Acceptance:
`proofs/scripts/lake build PhotoLean.QuantumYield.Instances` (exit 0);
`proofs/scripts/check.sh --strict`; fidelity
`python3 theories/BEP/probes/bep-fidelity.py --theory QuantumYield`.
-/
import PhotoLean.QuantumYield.RatModel

open scoped BigOperators

set_option autoImplicit false

namespace PhotoLean

namespace QuantumYield

/-! ## QY4 — named instances and verdicts -/

/-- Fluorescein S₁ channel rates `(kF, kIC, kISC)`; fluorescence yield `φF = 9/10`.
Representative of the literature yield ordering (LITERATURE).
Plan section 4, row QY-I1. -/
def fluoresceinS1 : Fin 3 → ℚ := ![18, 1, 1]

/-- Quinine-like channel rates; `φF = 11/20`.
Plan section 4, row QY-I2. -/
def quinineLike : Fin 3 → ℚ := ![11, 5, 4]

/-- Fluorescein S₁ with an added quenching channel of rate `9` at index `0` (the Stern–Volmer
dilution rehearsal at ℚ).
Plan section 4, row QY-I3. -/
def quenchDilution : Fin 4 → ℚ := Fin.cons 9 fluoresceinS1

/-- Verdict row: the fluorescence yield of fluorescein S₁ is `9/10`.
Plan section 4, row QY-I1 (verdict). -/
theorem inst_fluoresceinS1_phiF : Rat.yieldOf fluoresceinS1 0 = 9 / 10 := by
  -- Proof route (API-calibrated; the plan's `(decide)` cannot reduce the `Finset.univ` sum):
  -- `norm_num [Rat.yieldOf, Rat.totalRate, fluoresceinS1, Fin.sum_univ_three,
  --   Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]`.
  norm_num [Rat.yieldOf, Rat.totalRate, fluoresceinS1, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Verdict row: the fluorescence yield of the quinine-like instance is `11/20`.
Plan section 4, row QY-I2 (verdict). -/
theorem inst_quinineLike_phiF : Rat.yieldOf quinineLike 0 = 11 / 20 := by
  -- Proof route: as `inst_fluoresceinS1_phiF`.
  norm_num [Rat.yieldOf, Rat.totalRate, quinineLike, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Verdict row: the added channel dilutes the fluorescence yield to `18/29` (the fluorescence
channel now sits at index `1`).
Plan section 4, row QY-I3 (verdict, first form). -/
theorem inst_quenchDilution_phiF : Rat.yieldOf quenchDilution 1 = 18 / 29 := by
  -- Proof route (API-calibrated): `decide` for the index application
  -- (`Fin.cons 9 ![18, 1, 1] 1 = 18`), `norm_num [Fin.sum_cons, …]` for the total.
  norm_num [Rat.yieldOf, Rat.totalRate, quenchDilution, fluoresceinS1, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- Verdict row: the Stern–Volmer ratio of the quenched instance is `29/20`.
Plan section 4, row QY-I3 (verdict, second form). -/
theorem inst_quenchDilution_sternVolmer :
    Rat.yieldOf fluoresceinS1 0 / Rat.yieldOf quenchDilution 1 = 29 / 20 := by
  -- Proof route: the verdicts `inst_fluoresceinS1_phiF` and `inst_quenchDilution_phiF`;
  -- `norm_num`.
  rw [inst_fluoresceinS1_phiF, inst_quenchDilution_phiF]
  norm_num

end QuantumYield

end PhotoLean
