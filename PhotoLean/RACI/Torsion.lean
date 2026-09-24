import Mathlib
import PhotoLean.RACI.Accessibility

namespace PhotoLean


/-!
# RACI M2 — Torsion: the torsion-angle model and the path-blocking theorem

Upstream provenance: the ChemLean RACI plan §5.1–§5.4 (integration record: theories/RACI/plan.md §3.1).
Status note (upstream header, preserved): the statements were transcribed from the upstream plan; the deviation from the draft:
in `torsion_blocks_ci`, FC is a `Set ℝ` variable (upstream §5.1 leaves FC to its use site;
in the M2.3 instance FC does not participate).
Upstream owner: prover_m2 (exclusive file).
-/

open TwoState

namespace RACI

/-- The allowed configurations: `|θ| ≥ δ` (the aggregate phase; the CI sits at `θ = 0`, upstream plan §5.1). -/
def Allowed (δ : ℝ) : Set ℝ := {θ | δ ≤ |θ|}

/-- M2.1: the IVT crossing lemma — a continuous walk from `θ ≥ θ0` down to `0` must pass through `|θ| < δ` (upstream plan §5.2). -/
theorem exists_cross_forbidden
    {δ θ0 : ℝ} (hδ : 0 < δ) (hθ : δ < θ0)
    {γ : ℝ → ℝ} (hγ : Continuous γ)
    (h0 : θ0 ≤ γ 0) (h1 : γ 1 = 0) :
    ∃ t : ℝ, |γ t| < δ := by
  let c : ℝ := δ / 2
  have hc_pos : 0 < c := by
    unfold c
    exact div_pos hδ (by norm_num)
  have hc_lt : c < δ := by
    unfold c
    linarith
  have hγ0 : c ≤ γ 0 := le_trans hc_lt.le (le_trans hθ.le h0)
  have hc_mem : c ∈ Set.uIcc (γ 0) (γ 1) := by
    rw [Set.mem_uIcc]
    right
    constructor
    · rw [h1]
      exact le_of_lt hc_pos
    · exact hγ0
  rcases (intermediate_value_uIcc hγ.continuousOn) hc_mem with ⟨t, ht, ht_eq⟩
  refine ⟨t, ?_⟩
  rw [ht_eq, abs_of_pos hc_pos]
  exact hc_lt

/-- M2.2: the torsion constraint blocks every FC→CI path (for every ε; upstream plan §5.3). -/
theorem torsion_blocks_ci
    {M : TwoState ℝ} {FC : Set ℝ} {δ θ0 : ℝ}
    (hδ : 0 < δ) (hθ : δ < θ0)
    (hFC : FC ⊆ {θ | θ0 ≤ θ})
    (hCI : TwoState.conicalSet M ⊆ {θ | θ = 0}) :
    ∀ ε, BlockedBelow M (Allowed δ) FC ε := by
  intro ε
  rintro ⟨A⟩
  have hstart : θ0 ≤ A.path 0 := hFC A.starts_fc
  have hend : A.path 1 = 0 := hCI A.ends_ci
  rcases exists_cross_forbidden hδ hθ A.cont hstart hend with ⟨t, ht⟩
  have hstay : δ ≤ |A.path t| := A.stays_allowed t
  linarith

/-- M2.3: the diagonal torsion Hamiltonian `H(θ) = diag(θ, −θ)`: the CI at `θ = 0`, the gap `2|θ|` (upstream plan §5.4). -/
def torsionH (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![θ, 0; 0, -θ]

/-- M2.3: `torsionH` is symmetric (entrywise; upstream plan §5.4). -/
theorem torsionH_symm : ∀ θ, Matrix.IsSymm (torsionH θ) := by
  intro θ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torsionH, Matrix.transpose]

/-- M2.3: `torsionH` is continuous (the entries are the identity and its negative; upstream plan §5.4). -/
theorem torsionH_cont : Continuous torsionH := by
  refine continuous_matrix (fun i j => ?_)
  fin_cases i <;> fin_cases j
  · simpa [torsionH] using (continuous_id : Continuous fun a : ℝ => a)
  · simpa [torsionH] using (continuous_const : Continuous fun a : ℝ => (0 : ℝ))
  · simpa [torsionH] using (continuous_const : Continuous fun a : ℝ => (0 : ℝ))
  · simpa [torsionH] using (continuous_neg : Continuous fun a : ℝ => -a)

/-- M2.3: the CI set of `torsionH` is exactly `{0}` (upstream plan §5.4). -/
theorem torsionH_conicalSet :
    TwoState.conicalSet (⟨torsionH, torsionH_symm, torsionH_cont⟩ : TwoState ℝ) = {0} := by
  ext θ
  constructor
  · intro hθ
    have hθθ : θ = -θ := by
      simpa [TwoState.a, TwoState.d, torsionH] using hθ.1
    have hθ0 : θ = 0 := by linarith
    simpa using hθ0
  · intro hθ
    have hθ0 : θ = 0 := by
      simpa using hθ
    constructor
    · simp [TwoState.a, TwoState.d, torsionH, hθ0]
    · simp [TwoState.b, torsionH]

end RACI


end PhotoLean