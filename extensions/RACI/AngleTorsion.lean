import Mathlib

/-!
# Scoped angle-typed torsion variant (theory-level, zero active coverage)

This module is an ADDITIVE, out-of-manifest companion to the retained Real-coordinate
RACI torsion model (`PhotoLean/RACI/Torsion.lean`). It is deliberately placed OUTSIDE the
frozen `PhotoLean/**` manifest and OUTSIDE the pinned nine-probe validation set, so it
changes no census denominator, no certificate hash and no active pair/query coverage.

Purpose: answer the referee's torsion-typing concern by exhibiting a genuinely PERIODIC
(circular) angle type, rather than a Real local coordinate. The configuration space is the
unit circle in `ℂ`; it carries no global linear order and no global absolute value, so the
Real `exists_cross_forbidden` argument (which orders `|γ t|`) is NOT reused. Instead the
blocking theorem uses only a continuous real-valued chord distance to the conical intersection
and the intermediate value theorem on the real path parameter. This is the periodic refinement
listed as a well-defined extension in the response letter (Part C).

Discipline: no `sorry`, no custom `axiom`. Self-contained: `import Mathlib` only.
-/

namespace AngleTorsion

/-- The periodic angle type: the unit circle in `ℂ`. A torsion is a point on this circle,
not a real number; the circle has no global linear order. -/
abbrev Angle : Type := {z : ℂ // ‖z‖ = 1}

/-- The conical intersection sits at the angle `0`, i.e. the circle point `1 : ℂ`. -/
def ci : Angle := ⟨1, by simp⟩

/-- The accessibility coordinate: the chord distance from the CI point.
This is a continuous real-valued function on the circle, vanishing exactly at the CI,
and monotone in the angular separation locally; it requires no global angular order. -/
noncomputable def gap (z : Angle) : ℝ := dist z.val (1 : ℂ)

/-- The allowed (aggregate) phase: configurations at chord distance at least `δ` from the CI. -/
def allowed (δ : ℝ) : Set Angle := {z | δ ≤ gap z}

/-- The Franck–Condon region: configurations at chord distance at least `θ0` from the CI. -/
def fc (θ0 : ℝ) : Set Angle := {z | θ0 ≤ gap z}

@[simp] theorem gap_ci : gap ci = 0 := by
  simp [gap, ci]

theorem gap_continuous : Continuous gap := by
  have h : Continuous (fun z : Angle => z.val) := continuous_subtype_val
  exact h.dist continuous_const

/-- An admissible continuous path on the circle from the FC region to the CI that stays in the
allowed phase. The energy field is irrelevant to the geometric blocking, so it is omitted. -/
structure AdmissiblePath (δ θ0 : ℝ) where
  path : ℝ → Angle
  cont : Continuous path
  starts_fc : path 0 ∈ fc θ0
  ends_ci : path 1 = ci
  stays_allowed : ∀ t, path t ∈ allowed δ

/-- No admissible FC→CI path exists: the accessibility window blocks every continuous walk.
This is the periodic analogue of `RACI.torsion_blocks_ci`, proved without any global order on
the angle type — only the continuous chord coordinate and the real-parameter IVT are used. -/
theorem angle_blocks_ci {δ θ0 : ℝ} (hδ : 0 < δ) (hθ : δ < θ0) :
    ¬ Nonempty (AdmissiblePath δ θ0) := by
  rintro ⟨A⟩
  let f : ℝ → ℝ := fun t => gap (A.path t)
  have hf : Continuous f := gap_continuous.comp A.cont
  have h0 : θ0 ≤ f 0 := A.starts_fc
  have h1 : f 1 = 0 := by
    have : A.path 1 = ci := A.ends_ci
    simp [f, this]
  have hc_pos : 0 < δ / 2 := div_pos hδ (by norm_num)
  have hc_lt : δ / 2 < δ := by linarith
  have hmem : (δ / 2 : ℝ) ∈ Set.uIcc (f 0) (f 1) := by
    rw [Set.mem_uIcc]
    right
    constructor
    · rw [h1]; exact le_of_lt hc_pos
    · exact le_trans hc_lt.le (le_trans hθ.le h0)
  rcases intermediate_value_uIcc hf.continuousOn hmem with ⟨t, _, ht_eq⟩
  have hstay : δ ≤ f t := A.stays_allowed t
  linarith

end AngleTorsion