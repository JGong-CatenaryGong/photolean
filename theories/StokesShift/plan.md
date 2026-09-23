# theories/StokesShift/plan.md — PhotoLean formalization plan: the Stokes shift rule (SS1–SS4)

> Status: **Phase 1 (statement formalization)** — the statement inventory of §4 is the frozen
> design; the statement authority `probes/StokesShift-statement-skeleton.lean` transcribes it
> verbatim with placeholder proof bodies. No proof work in Phase 1.
> Authority: contract `proofs/ENGINE.yml`; board `theories/StokesShift/TASKS.md`.
> Batch: the photophysics subgraph (human request 2026-09-22), group B (two-parabola basis),
> second theory of the group.

---

## 1. Overall goal and boundaries

### 1.1 The claim

In the two-parabola model with ground surface `λq²` and excited surface `λ(q−1)² + E₀₀`, the
vertical absorption energy (from the ground minimum) is `λ + E₀₀`, the vertical emission energy
(from the excited minimum) is `E₀₀ − λ`, and the Stokes shift is **exactly `2λ`** — independent
of the 0-0 energy; the shift is positive exactly when the curvature is physical; absorption and
emission are mirror-symmetric about `E₀₀` (their mean is `E₀₀`); and the emission photon energy
is positive exactly in the window `λ < E₀₀` — whose complement at `x = E₀₀` is the Marcus
inverted region (the emission window closes where the inverted region begins).

### 1.2 The model (chosen, not derived)

The kernel's equal-curvature surfaces, read optically: `q = 0` the ground-state minimum
geometry, `q = 1` the excited-state minimum geometry, vertical (Franck–Condon) transitions at
the minima. This theory carries **its own copies** of the two surfaces pinned to
`PhotoLean.Kernel` by `rfl` certificates (hard constraint 1). No division appears anywhere in
the theory — every row is pure polynomial algebra (the lightest group-B theory).

### 1.3 Explicit non-goals

* No vibronic structure (single-mode classical surfaces only).
* No solvent-relaxation dynamics; `λ` collects all reorganization (registered).
* No lineshape widths — maxima only.

## 2. Conventions and symbols

`lam` reorganization energy (curvature `2·lam`); `e00` the 0-0 energy; `q` the dimensionless
coordinate. Namespace `PhotoLean.StokesShift`; rational layer `PhotoLean.StokesShift.Rat`.

## 3. Statement authority and inventory

The authority is `probes/StokesShift-statement-skeleton.lean` (Phase-1 placeholder bodies;
sha256 on the board once compiling).

### 3.1 Statement-correction log

* **Entry 2 (SS-I4, 2026-09-23, Phase-3 negative-result finalization)** — the
  refutation of the SS-C9 first form (entry 1) is now delivered as a theorem with its parameter
  witness: `invertedCorner_firstForm_refuted : ¬ (∀ lam e00, (e00 < lam ↔
  Marcus.InvertedRegion lam e00))`, refuted at `lam = 1, e00 = 2` (`2 < 1` false,
  `InvertedRegion 1 2` true). An authority ADDITION (row SS-I4); sha256 updated on the board.

* **Entry 1 (SS-C9, 2026-09-22, Sprint-0 calibration)** — the first form
  `e00 < lam ↔ PhotoLean.Marcus.InvertedRegion lam e00` unfolds to `e00 < lam ↔ lam < e00`,
  which is **false** (kernel-checked counterexample `lam = 1, e00 = 2` in
  `StokesShift-api-probe.lean`; flagged by the skeleton worker as a calibration finding). The
  corrected row is `emEnergy_pos_iff_inverted : 0 < emEnergy lam e00 ↔
  PhotoLean.Marcus.InvertedRegion lam e00` — the *open* emission window IS the inverted region
  read at the gap (both sides reduce to `lam < e00`); the physically interesting content (the
  vertical-photon regime coincides with the Marcus-inverted regime of the nonradiative twin) is
  preserved and sharpened. The skeleton carries the corrected row.

## 4. Statement inventory

Module plan (Phase 2): `Basic.lean` (SS-B), `Criterion.lean` (SS-C), `RatModel.lean` (SS-R),
`Instances.lean` (SS-I).

**SS-B (copies + certificates + definitions):**

* SS-B1 `s0Surface (lam q : ℝ) : ℝ := lam * q ^ 2`;
  `cert_s0Surface : s0Surface lam q = PhotoLean.Kernel.reactantSurface lam q` (`rfl`).
* SS-B2 `s1Surface (lam e00 q : ℝ) : ℝ := lam * (q - 1) ^ 2 + e00`;
  `cert_s1Surface : s1Surface lam e00 q = PhotoLean.Kernel.productSurface lam e00 q` (`rfl`).
* SS-B3 `absEnergy (lam e00 : ℝ) : ℝ := s1Surface lam e00 0 - s0Surface lam 0` — vertical
  absorption at the ground minimum.
* SS-B4 `emEnergy (lam e00 : ℝ) : ℝ := s1Surface lam e00 1 - s0Surface lam 1` — vertical
  emission at the excited minimum.
* SS-B5 `stokesShift (lam e00 : ℝ) : ℝ := absEnergy lam e00 - emEnergy lam e00`.

**SS-C (the laws — all pure algebra, no premises unless stated):**

* SS-C1 `absEnergy_eq (lam e00 : ℝ) : absEnergy lam e00 = lam + e00`.
* SS-C2 `emEnergy_eq (lam e00 : ℝ) : emEnergy lam e00 = e00 - lam`.
* SS-C3 `stokesShift_eq_two_lam (lam e00 : ℝ) : stokesShift lam e00 = 2 * lam` — **the
  headline**: the shift is twice the reorganization energy, independent of `e00`.
* SS-C4 `stokesShift_pos_iff (lam e00 : ℝ) : 0 < stokesShift lam e00 ↔ 0 < lam` — positivity of
  the shift is exactly physical curvature.
* SS-C5 `emEnergy_pos_iff (lam e00 : ℝ) : 0 < emEnergy lam e00 ↔ lam < e00` — the emission
  window.
* SS-C6 `mirror_midpoint (lam e00 : ℝ) : (absEnergy lam e00 + emEnergy lam e00) / 2 = e00` —
  mirror symmetry about the 0-0 energy.
* SS-C7 `abs_sub_e00_eq_e00_sub_em (lam e00 : ℝ) :
  absEnergy lam e00 - e00 = e00 - emEnergy lam e00` — the two Franck–Condon offsets are equal.
* SS-C8 `emission_window_closes (lam : ℝ) : emEnergy lam lam = 0` — the window's edge; and
  `inverted_corner (h : e00 < lam) : emEnergy lam e00 < 0` — beyond it the vertical emission is
  negative (no photon): the model's own boundary.
* SS-C9 `emEnergy_pos_iff_inverted (lam e00 : ℝ) :
  0 < emEnergy lam e00 ↔ PhotoLean.Marcus.InvertedRegion lam e00` — the **open** emission window
  (a positive vertical photon) *is* the Marcus inverted region read at the gap; both sides reduce
  to `lam < e00` (imports `PhotoLean.Marcus.Basic`). **Amended at Sprint 0** (§3.1 entry 1): the
  first form `e00 < lam ↔ InvertedRegion lam e00` is false (counterexample `lam = 1, e00 = 2` in
  the api probe).

**SS-R (rational decision layer):**

* SS-R1 `Rat.s0Surface`, `Rat.s1Surface`, `Rat.absEnergy`, `Rat.emEnergy`, `Rat.stokesShift`
  over `ℚ` + cast coherence (pure polynomial — no transcendentals anywhere).
* SS-R2 `inductive SSZone | normalEmission | zeroPhoton | invertedEmission`;
  `ssZoneQ (lam e00 : ℚ) : SSZone` by comparing `lam ? e00` (`decide`); correctness rows at cast
  parameters (`(ssZoneQ lam e00 = .invertedEmission) ↔ (e00 : ℝ) < lam`).

**SS-I (named instances, representative rational models):**

* SS-I1 `mirrorDye` (lam = 1/2, e00 = 2): absorption `5/2`, emission `3/2`, shift `1`,
  midpoint `2` — the mirror-symmetric case; zone `normalEmission`.
* SS-I2 `largeRelaxation` (lam = 3/2, e00 = 2): emission `1/2`, shift `3` — still emitting.
* SS-I3 `invertedCorner` (lam = 2, e00 = 2, and lam = 3, e00 = 2): the window edge
  (`zeroPhoton`) and beyond (`invertedEmission`) — the refuting pair for "emission is always
  positive" (a negative result registered as an instance verdict).

## 5. Proof routes

SS-C1..C8 are `unfold` + `ring`/`linarith` (SS-C4/C5 after rewriting by SS-C3/C2); SS-C9 (the amended
`emEnergy_pos_iff_inverted`) is
`Iff.rfl` (check `Marcus.InvertedRegion`'s body first — it is `lam < x`, so the iff is
`e00 < lam ↔ lam < e00` up to commutativity of the flipped order: state exactly
`PhotoLean.Marcus.InvertedRegion lam e00 ↔ e00 < lam` — one `Iff.rfl` or
`propext`-free `Iff.intro` pair). No API risk; the lightest skeleton of group B.

## 6. Sprint order, ownership, dispatch

Sprint SS0 (Phase 1) → SS1 `Basic` → SS2 `Criterion` → SS3 `RatModel` → SS4 `Instances`.
Owner: prover_a (group B block).

## 7. Acceptance criteria and gate commands

    proofs/scripts/lake build PhotoLean.StokesShift.Basic   (etc. per module)
    proofs/scripts/check.sh --strict PhotoLean.StokesShift.Criterion
    proofs/scripts/axioms.sh PhotoLean.StokesShift.Criterion PhotoLean.StokesShift.stokesShift_eq_two_lam
    python3 theories/BEP/probes/bep-fidelity.py --theory StokesShift

## 8. Risks and mitigations

* SS-C9's direction conventions (`InvertedRegion lam x := lam < x`) must be checked against the
  delivered body before freezing the skeleton — a sign slip here inverts the physics. **It happened**:
  the first frozen direction was inverted; see §3.1 entry 1 (the amendment was caught at Sprint 0 by
  the api probe, before any proof work).
* The `2 * lam` vs `lam * 2` normal form is fixed by `ring`; no risk.

## 9. Honesty table

| # | Assumed (declared premise) | Proved (theorem) |
|---|---|---|
| 1 | Single-mode equal-curvature surfaces; vertical transitions at the minima | SS-C rows |
| 2 | `λ` collects all reorganization (inner + outer) | — |
| 3 | Named instances are representative rational models | their zone verdicts |

## 10. Edge candidates (toward the 7 delivered nodes + the 8 batch siblings)

* **Marcus — certificate + zone edge (machine targets)**: SS-B1/B2 pins; SS-C9 identifies the
  inverted corner with `Marcus.InvertedRegion` at the gap.
* **EnergyGapLaw — certificate**: same surfaces; `lam` shared; the EGL barrier at `x = e00` is
  the emission-window boundary (one row: `nrBarrier lam e00 = 0 ↔ emEnergy lam e00 = 0` —
  both sides reduce to `lam = e00`; state exactly).
* **Einstein — look-alike candidate (N-class)**: mirror symmetry of band *positions* (SS-C6) vs
  detailed balance of band *intensities* — same slogan ("absorption↔emission symmetry"),
  different objects; register the shape, no theorem transfers.
* **Kasha / KashaVavilov / SternVolmer / QuantumYield / FluorPhos / ICvsISC / Forster /
  Sabatier / Goldschmidt / SymmetryFactor / Hammond / BEP**: no edge — absence drafts
  registered (the SS layer carries energies, not rates, ladders, curvatures-as-data, or
  geometries).

## 11. Position in the repository

Sixth theory of the batch, second of group B; imports `PhotoLean.Kernel` and
`PhotoLean.Marcus.Basic` for the certificates; nothing delivered is modified.
