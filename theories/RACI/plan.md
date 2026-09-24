# theories/RACI/plan.md — PhotoLean formalization plan: RACI — Restricted Access to a Conical Intersection (integration of the ChemLean work)

> Status: **delivered (ported) and gated** — the RACI modules are integrated from the independent
> ChemLean repository (`[local path removed]`) and registered as PhotoLean's 17th
> theory. All eleven modules build against the repository's mathlib v4.17.0, the strict scan is
> clean, 46/46 theorems pass `#print axioms` with the allowed infrastructure axioms, and the
> statement authority's fidelity report is 71/71 word-for-word with 0 differences.
> Authority: contract `proofs/ENGINE.yml`; board `theories/RACI/TASKS.md`; experience bank
> `proofs/EXPERIENCE.md`; literature `theories/RACI/LITERATURE.md`.

---

## 1. Overall goal and boundaries

### 1.1 The claim (the RACI mechanism of aggregation-induced emission)

Aggregation-induced emission (AIE): a chromophore that is dark in dilute solution becomes
emissive in the aggregate. The accepted mechanism — **Restricted Access to a Conical
Intersection (RACI)** — is: in the free phase, the excited state reaches an S1/S0 conical
intersection (CI) by a large-amplitude motion and decays nonradiatively; in the aggregate, the
motion is geometrically restricted, the CI is no longer accessible, the nonradiative channel
collapses, and the radiative channel wins.

The integrated work proves this as a machine-checked theorem in a declared model class:

1. **M1 — the CI algebra** (`TwoState.lean`, `Branching.lean`): a two-state adiabatic Hamiltonian
   `H : X → Matrix (Fin 2) (Fin 2) ℝ` (continuous, symmetric) has a conical intersection exactly
   where the degeneracy conditions `a = d` and `b = 0` hold simultaneously, equivalently where the
   discriminant `(a−d)² + 4b²` vanishes, equivalently where the two eigenvalues coincide; the
   branching space of a surjective degeneracy map has codimension **2** (the von Neumann–Wigner
   rule), with the explicit linearized instance `v ↦ (2·v 0, v 1)` and its gap.
2. **M2 — accessibility** (`Accessibility.lean`, `Torsion.lean`): the accessibility parameter
   `accessGap = 2·sInf(|θ|''allowed)`; the free phase allows every torsion angle
   (`accessGap Set.univ = 0`) while the aggregate allows only `|θ| ≥ δ`
   (`accessGap (Allowed δ) = 2δ`), hence a strictly positive accessibility jump.
3. **M3 — nonradiative rates** (`Barrier.lean`, `LandauZener.lean`): the barrier rate
   `A·exp(−β·B)` and the Landau–Zener probability are strictly decreasing in the gap.
4. **M4 — the RACI theorem** (`Jablonski.lean`, `JablonskiRatios.lean`, `Main.lean`): with the
   radiative rate (approximately) unchanged, the yield is strictly antitone in the nonradiative
   rate, hence `Φ_agg > Φ_sol` (`torsion_raci_emission_enhancement`), plus the channel-ratio
   generalization (Φ rises ⟺ `knr/kr` drops) and the kr-nonincreasing sufficient version.
5. **M1\* — the seam** (`Seam.lean`): near a non-degenerate CI, the conical set is locally a
   codimension-2 submanifold slice (`conicalSet_locally_slice`, via the implicit function
   theorem), with `conicalSet_local_codim_two`.
6. **M6 — the Longuet–Higgins sign theorem** (`GeometricPhase.lean`): on the canonical loop
   around the linearized CI, the lower eigenvector flips sign after one circuit
   (`loop_monodromy`), with the loop's constant gap making the adiabatic transport well-defined.

### 1.2 Explicit non-goals (registered)

* No ab-initio/electronic-structure numerics; the Hamiltonian is an abstract continuous family.
* No wavepacket dynamics, surface hopping, or tunnelling; rates enter as monotone forms.
* No global smooth-submanifold theorem for the whole seam (only the local slice near a
  non-degenerate point).
* No proof that AIE always happens: the theorem is conditional (the constraint must raise the
  accessibility gap and the radiative rate must be (approximately) preserved); instances whose
  constraints fail are registered as named non-models (§4.7).

## 2. Conventions and symbols

* `TwoState X`: the continuous symmetric `Fin 2 → ℝ` Hamiltonian family on the nuclear
  configuration space `X` (normed space over ℝ); `a, b, d` its matrix entries.
* `discr = (a−d)² + 4b²`; `conicalSet = {x | a = d ∧ b = 0}`; `eigenRoots` the two eigenvalues.
* `Allowed δ := {θ | |θ| ≥ δ}`; `accessGap = 2·sInf(|θ|''allowed)`;
  `barrierRate A β B = A·exp(−βB)`; `quantumYield kr knr = kr/(kr+knr)`;
  `competitionRatio = knr/kr`.
* Totalized division and totalized `Real.sqrt` (Lean conventions); every positivity is an
  explicit hypothesis (iron rule 3).

## 3. Statement authority and inventory

The statement authority is `probes/RACI-statement-skeleton.lean` (71 declarations: 46 theorems +
25 definitions/structures/inductives), **extracted verbatim from the delivered modules** (the
integration direction is reverse: the authority records the delivered signatures rather than the
delivered code following a frozen plan; the fidelity checker enforces that any later edit keeps
the two in sync). The skeleton compiles at 0 errors (`lake env lean`, placeholder-body warnings
only), sha256 recorded on the board.

### 3.1 Integration record (the deviations from a fresh theory, all registered)

1. **autoImplicit**: the ported code uses Lean's default `autoImplicit` (free variables in
   definitions are auto-bound); the PhotoLean convention `set_option autoImplicit false` is NOT
   applied to the ported files, so the upstream statements are preserved verbatim.
2. **Layout**: the upstream `RACI/Rates/` subdirectory is flattened to the per-theory layout
   (`PhotoLean/RACI/{Barrier,LandauZener}.lean`) — the fidelity checker's delivered-file glob is
   non-recursive; module names are unchanged (`PhotoLean.RACI.Barrier` etc.).
3. **Namespaces**: every ported file is wrapped in `namespace PhotoLean`, so the RACI-namespace
   rows are `PhotoLean.RACI.*` and the TwoState-algebra rows are `PhotoLean.TwoState.*`; the
   Branching rows sit at `PhotoLean.*` (their upstream top-level layout, kept verbatim).
4. **Upstream status headers**: several ported files carry a stale `SKELETON` header from the
   upstream repo although the content is fully proved; the headers were preserved through the
   port and reworded in the close-out translation (below), and the real status is this plan + the
   board.
5. **Language policy (close-out audit finding F4)**: the ported modules originally carried
   Chinese comments and cross-references to the ChemLean plan (≈149 lines across 11 files). The
   close-out commit translated every comment to English (Lean identifiers and mathematical
   notation verbatim; the upstream plan references now read "the ChemLean RACI plan §N" with the
   integration record pointer), and each module header keeps its ChemLean provenance. The
   comments-only change leaves every signature untouched (fidelity 71/71 unchanged, whole-tree
   gate PASS).

## 4. Milestones and module plan

Delivered (11 modules, ported verbatim): `TwoState` (M1: the CI algebra, 12 decls),
`Branching` (M1: branching space codim 2, linearized gap, 10 decls), `Accessibility` (M2, 2
decls), `Torsion` (M2: the torsion model, 7 decls), `Barrier` (M3, 2 decls), `LandauZener` (M3,
5 decls), `Jablonski` (M4: yield algebra, 3 decls), `JablonskiRatios` (M4+, 12 decls), `Main`
(M4: the RACI template + torsion instances, 8 decls), `Seam` (M1\*, 4 decls), `GeometricPhase`
(M6, 6 decls).

**PhotoLean-standard additions (new in the integration, §4.7–§4.8)**: `Instances.lean` (the
named admissible model and the named non-model with verdicts) and `RatModel.lean` (the ℚ
decision layer for the discriminant and the CI zone classifier) — see §4.7.

## 4.7 The instances layer (integration addition)

* **Admissible model (named)**: `torsionH` (the linearized torsion Hamiltonian, already delivered
  with `torsionH_symm`/`torsionH_cont`/`torsionH_conicalSet`) at a positive gap; the free/blocked
  phase pair at `δ > 0` realizes the enhancement theorem (`torsion_raci_emission_enhancement`).
* **Refuting model (named non-model)**: `nonModelNoCI`, a constant diagonal Hamiltonian
  `H ≡ [[1,0],[0,2]]` with `conicalSet = ∅` everywhere — no conical intersection exists, so the
  RACI mechanism has nothing to suppress; the accessibility-jump premise cannot be instantiated
  (registered, with the kernel-checked `conicalSet nonModelNoCI = ∅`).
* **The ℚ decision layer**: `Rat.discrQ (a b d : ℚ) : ℚ := (a − d)² + 4·b²` (pure rational);
  `Rat.ciZoneQ` classifies a `Fin 2 → Fin 2 → ℚ` matrix entry set as `conical | gapped` by
  `discrQ = 0` (decidable at ℚ); cast-coherence rows tying the ℚ decision to the ℝ discriminant;
  instance verdicts computed at ℚ by `norm_num`/`decide` (never evaluating `Real.exp` or
  `Real.sqrt` — the decision stays at the discriminant level, the EnergyGapLaw precedent).

## 5. Edge registration (Relations §17)

Machine edges (proved in `PhotoLean/Relations.lean` §17):

* **RACI ↔ QuantumYield** (composition certificate): `quantumYield kr knr = yieldOf ![kr, knr] 0`
  — the yield is the two-channel yield; the RACI monotonicity template is the two-channel
  strict-antitone-in-`knr` reading of QY-C7's dilution.
* **RACI → EnergyGapLaw** (composition): `log (barrierRate A β B) = log A − β·B` (`0 < A`) — the
  M3 barrier rate is the affine energy-gap law exactly (the EGL tangent shape; the Marcus-lnRate
  is quadratic, its tangent affine — the shape note is registered).
* **RACI ↔ ICvsISC** (composition note with machine row): at a conical intersection the
  two-parabola FC barrier vanishes (`fcBarrier lam lam = 0`, `lam ≠ 0`) — the maximal-rate point
  of the ICvsISC competition; the CI is the geometric site of the ultrafast IC the barrier model
  describes.
* **RACI ↔ Marcus** (look-alike, N-class with machine note): the Marcus crossing is a
  codimension-1 degeneracy of two classical surfaces (the coupling coordinate is absent — the
  `b ≡ 0` degenerate subfamily); the RACI CI is a codimension-2 degeneracy requiring `a = d ∧
  b = 0`. Different objects; the registry records why no theorem transfers (the classical model
  has no coupling coordinate).
* **RACI ↔ Kasha / KashaVavilov** (shape note): both are "IC-rate determines emission dominance"
  stories, at opposite ends of the ladder (blocking IC at the lowest state vs funneling through
  it from upper states); no machine row.
* **RACI ↔ SternVolmer** (look-alike note, opposite trend): aggregation quenching vs
  aggregation-induced emission — opposite environment-dependence of the yield.
* **RACI ↔ Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor / StokesShift / FluorPhos /
  Forster / Einstein — no edge** (registered with reasons in §16 of `PhotoLean/Relations.lean`).

## 6. Acceptance criteria and gates

    proofs/scripts/lake build PhotoLean.RACI.Main PhotoLean.RACI.Seam PhotoLean.RACI.GeometricPhase
    proofs/scripts/check.sh --strict
    proofs/scripts/axioms.sh PhotoLean.RACI.<Module> PhotoLean.<RACI|TwoState>.<theorem>   (all 46)
    python3 theories/BEP/probes/bep-fidelity.py --theory RACI
    an independent verifier run (the close-out of this plan)

## 7. Risks and mitigations

* The `Seam` (implicit-function-theorem) and `GeometricPhase` modules are the mathematically
  heaviest; both built on the first pass against the repository's mathlib (same version as the
  upstream toolchain — the single biggest integration risk, toolchain drift, was checked first).
* The upstream autoImplicit style (§3.1 #1) is preserved deliberately; any future PhotoLean-native
  edit of this theory may introduce the `set_option` only by converting every auto-bound
  definition explicitly — a registered non-goal for this integration.

## 8. Honesty table

| # | Assumed (declared premise) | Proved (theorem) |
|---|---|---|
| 1 | Two-state truncation with a continuous symmetric Hamiltonian family | M1 algebra |
| 2 | Surjectivity of the degeneracy map (for the codimension-2 count) | M1.3 |
| 3 | The aggregate phase is the `|θ| ≥ δ` accessibility window | M2 |
| 4 | The barrier/LZ rate forms (collected prefactors) | M3 |
| 5 | The radiative rate is (approximately) unchanged across phases | M4 enhancement |
| 6 | Non-degenerate point + C¹ Hamiltonian (for the seam slice) | M1\* |
| 7 | The linearized loop model (for the sign theorem) | M6 |
| 8 | Named instances are representative models, not fitted data | instance verdicts |

## 9. Position in the repository

Seventeenth theory; self-contained at the `Mathlib`-only base (the ported modules import only
`Mathlib`); the graph contact is registered in `PhotoLean/Relations.lean` §17 and
`theories/RELATIONS.md` §9. Nothing delivered elsewhere is modified except the engine leaves
(`ENGINE.yml`, `lakefile.toml`, `Relations.lean` extension, README).
