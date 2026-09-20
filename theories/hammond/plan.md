# theories/hammond/plan.md — PhotoLean formalization plan: the Hammond postulate (H1–H5)

> Project: turn **Hammond's postulate** into a *machine-checked* theorem set inside the
> two-parabola (Marcus-type) model of an elementary reaction step.
> Target system: Lean 4.17.0 + mathlib (`MODULE_PREFIX=PhotoLean`, see `proofs/ENGINE.yml`).
> Status: plan drafted, awaiting human confirmation; implementation not started.
> Authority: contract `proofs/ENGINE.yml`; board `theories/hammond/TASKS.md`;
> experience bank `proofs/EXPERIENCE.md`; literature `theories/hammond/LITERATURE.md`.
> **Statement authority**: `theories/hammond/probes/hammond-statement-skeleton.lean`
> (compiles: 0 error, 85 placeholder warnings) — delivered signatures must match it word for word.

---

## 1. Overall goal and boundaries

### 1.1 Project goal

In the classical two-parabola model — reaction coordinate `q`, reactant well at `q = 0`,
product well at `q = 1`, harmonic surfaces of **equal** curvature, classical crossing point
as transition state (TS) — formalize and prove:

> **Main theorem (family level)**: the TS coordinate `q‡` is *strictly decreasing* in the
> driving force `x = -ΔG°` — the more exergonic the step, the more **reactant-like** (earlier)
> the TS — **and this holds if and only if the reorganization energy satisfies `λ > 0`**.
> The conditions are *sharp*: `λ = 0` and `λ < 0` each break the descriptor.

and, at the point level:

> **Hammond criterion**: the TS is *structurally* closer to whichever well it is *closer in
> energy* to — proved as an exact equivalence; the **Leffler/Brønsted coefficient measured
> from barrier data** (a finite difference, i.e. an observable) equals `q‡` at the midpoint
> and satisfies `0 < α < 1` **iff** the crossing point lies strictly between the two wells;
> the Marcus **inverted region** `x > λ` is *exactly* the regime where `q‡ < 0`, `α < 0` and
> the structural-resemblance reading fails.

This is the executable version of Hammond's postulate: "the structure of the transition state
resembles that of the species to which it is closest in energy", quantified in the model where
that statement becomes an exact equation and its validity condition becomes a theorem.

**Attribution (settled by `theories/hammond/LITERATURE.md`, the authority for loci and wording)**:
the postulate is **Hammond 1955**, *J. Am. Chem. Soc.* **77**(2), 334–338, `10.1021/ja01607a027`,
whose printed p. 334 says *verbatim*: "If two states … have nearly the same energy content, their
interconversion will involve only a small reorganization of the molecular structures", with the
operational consequence "In highly exothermic steps it will be expected that the transition states
will resemble reactants closely and in endothermic steps the products will provide the best models
for the transition states."
**Correction (literature survey, §9 item 1)**: the familiar sentence "the structure of the
transition state resembles that of the species to which it is closest in energy" is a **later
paraphrase**, *not* Hammond's wording — "closest / close in / nearest / near in" occur **0 times**
in the 1955 paper. This plan's wording above should be read as the modern paraphrase; the normative
modern definition ("Hammond–Leffler principle", a *hypothesis*; `α` an approximate measure of the TS
displacement; "many exceptions") is the IUPAC glossary (Perrin et al., *Pure Appl. Chem.* **94**,
353–534, `10.1515/pac-2018-1010`).
**Correction (literature survey, §9 item 2)**: the two-parabola model and the barrier formula are
**Marcus 1956**, Eq. (38) p. 974 (`10.1063/1.1742723`) — but the **α formula** `α = 1/2 + ΔG°/(2λ)`
and the slope ↔ TS-position identification are **not** in 1956 (its full text has 0 hits for
"slope", "alpha", "Bronsted", "inverted"); they are **Cohen & Marcus 1968** (`10.1021/j100858a052`),
**Marcus 1968** (`10.1021/j100849a019`) and **Marcus 1969** (`10.1021/ja01054a003`). Leffler's
priority for the α-as-structure idea (1953, `10.1126/science.117.3039.340`) is bibliographically
correct but its own text was **not accessible** (`not-accessed` in the record — do not cite it for
content).
Literature fixes statements and premises; it never substitutes for a proof.

### 1.2 Human request → milestones

| Human request | Milestone | Deliverable |
|---|---|---|
| ① turn the Hammond postulate into a formal description | **H1** (description layer) | `Hammond/Basic.lean`: surfaces, `tsCoord`, barriers, `lefflerSecant`, regime/resemblance predicates, `HammondDescriptor`, decidable classifier `hammondZone`, crossing geometry |
| ②a prove the description | **H2** (criterion layer) | `Hammond/Criterion.lean`: monotonicity, energy–structure correspondence, Leffler identity, Marcus bridge, non-vacuity |
| ②b find the conditions under which it holds | **H3 + H4** (sharp + microscopic) | `Hammond/Sharp.lean` (`⟺ λ > 0`, explicit reversal witnesses) and `Hammond/Compose.lean` (`λ = λ_in + λ_out`, Pekar factor positivity ⇒ descriptor) |
| ③ plug in instances and decide whether they conform to the Hammond description | **H5** (instances & verdicts) | `Hammond/RatModel.lean` (computable ℚ verdict layer + transfer lemmas) and `Hammond/Instances.lean` (kernel-checked verdicts) |

### 1.3 Explicit non-goals (scope control)

- **Not deriving the model.** That real molecular structure is captured by one scalar `q`, that
  the two surfaces are harmonic with equal curvature, that the TS is the crossing point, and
  that `λ` takes the Marcus form are **modeling assumptions**, not theorems. The formalized
  content is conditional on them (see §13).
- **No claim that Hammond's postulate is a theorem of quantum mechanics.** The general postulate
  is a qualitative regularity; this project makes *one* quantitative realization of it exact.
- **No unequal-curvature generalization.** With `λ_R ≠ λ_P` the monotonicity survives but the
  affine `α = 1/2 + ΔG°/(2λ)` does not (the crossing equation becomes quadratic and the
  implicit-function step needs analysis). Recorded as a next station (§14).
- **No quantum nuclear dynamics** (tunneling, surface hopping, recrossing), **no electronic
  structure**, **no vibrational/FC factors**.
- **No temperature or prefactor dependence.** The structural statements are independent of
  `k_B`, `T`, `A` — this is a feature: the Hammond descriptor has strictly fewer physical
  premises than the Marcus rate descriptor. Rate-level statements are *not* reproved here;
  they are the already-delivered `PhotoLean/Marcus/Rate.lean` and are only cross-referenced.
- **No claim about measured experimental rates or structures** (the model is not the molecule).
- **No `sorry`, no custom `axiom`** in delivered files (enforced by `proofs/scripts/check.sh --strict`
  and `axioms.sh`).

---

## 2. Formal system design

### 2.1 Embedding strategy

Everything lives on `ℝ`; the decision layer on `ℚ`; **the only tools needed are the ordered
field operations and `if`-classification**. No `Real.exp`, no limits, no derivatives, no
`Set`-topology API: the structural theory is pure algebra, so the API risk is far smaller than
in the Marcus milestone (which needed the `Real.exp` layer). This is deliberate:
the mathematical content that remains is the *modeling* content, and the algebra is
mechanically checkable.

### 2.2 Global definitions (H1; `Hammond/Basic.lean`)

```lean
/-- Reactant potential-energy surface: minimum at `q = 0`, curvature `2*lam`. -/
noncomputable def reactantSurface (lam q : ℝ) : ℝ := lam * q ^ 2

/-- Product surface: minimum at `q = 1`, same curvature, offset `dG = ΔG°` (exergonic: `dG < 0`). -/
noncomputable def productSurface (lam dG q : ℝ) : ℝ := lam * (q - 1) ^ 2 + dG

/-- TS coordinate, driving-force convention `x = -ΔG°` (exergonic: `x > 0`). -/
noncomputable def tsCoord (lam x : ℝ) : ℝ := (lam - x) / (2 * lam)

/-- Forward barrier (reactant well → crossing point); reverse barrier is `gapProduct`. -/
noncomputable def gapReactant (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)
noncomputable def gapProduct (lam x : ℝ) : ℝ := (lam + x) ^ 2 / (4 * lam)

/-- Leffler/Brønsted coefficient as a finite difference of the barrier (an observable). -/
noncomputable def lefflerSecant (lam x₁ x₂ : ℝ) : ℝ :=
  -(gapReactant lam x₂ - gapReactant lam x₁) / (x₂ - x₁)

def ReactionRegion (lam x : ℝ) : Prop := -lam < x ∧ x < lam      -- crossing strictly between wells
def ReactantLike (lam x : ℝ) : Prop := tsCoord lam x < 1 / 2
def ProductLike (lam x : ℝ) : Prop := 1 / 2 < tsCoord lam x
def HammondConforms (lam x : ℝ) : Prop := 0 < lam ∧ ReactionRegion lam x   -- instance-level verdict
def HammondDescriptor (lam : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, x₁ < x₂ → tsCoord lam x₂ < tsCoord lam x₁        -- family-level statement

inductive HZone where
  | early | half | late | atReactant | atProduct | beyondReactant | beyondProduct
  deriving DecidableEq, Repr

noncomputable def hammondZone (lam x : ℝ) : HZone :=
  if x = lam then HZone.atReactant
  else if x = -lam then HZone.atProduct
  else if x < -lam then HZone.beyondProduct
  else if lam < x then HZone.beyondReactant
  else if x = 0 then HZone.half
  else if 0 < x then HZone.early
  else HZone.late
```

**✅ Sprint 0 measured (kernel evidence, not intent)**: these definition bodies and the theorem
forms of §4–§8 were compiled in `theories/hammond/probes/hammond-risk-probe.lean`
(0 error / 0 warning, all proofs complete), and all 85 signatures are in the compiled
statement skeleton. The following are already *proven* at probe level:
`crossing_iff`, `gapReactant_eq_crossing_energy`, `gapProduct_sub_gapReactant`,
`tsCoord_antitone`, `tsCoord_zero_lam`, `tsCoord_increasing_of_neg` (the `λ < 0` branch),
both direction-reversal witnesses, `tsCoord_mem_iff`, `bronsted_pos_iff`, `bronsted_neg_iff`
(the `div_neg_iff_of_pos_right` route does **not** exist; `div_lt_iff₀` works),
`leffler_finite_difference`, `gap_compare_iff`, `tsCoord_neg`, `tsCoord_zero`,
`tsCoordQ_cast` and the ℚ classifier computations.

**Sprint 1 correction (two statements of the first skeleton draft were false; caught before
delivery, recorded in `proofs/EXPERIENCE.md` and in the API log)**:
(i) `gapProduct_eq_crossing_energy` must be well-referenced — the reverse barrier is the crossing
energy *measured from the product well* (`… - dG`); the un-referenced form is off by `dG`
(found by `prover_a` with a kernel counterexample);
(ii) the intended "verdict characterization by the three resemblance predicates" is a *tautology*
of trichotomy (it holds for every `(lam, x)`, so it characterizes nothing) — the verdict is
characterized by the **classifier** (`conforms_iff_zone`), which is the form the instance layer uses.
**Lesson for the remaining milestones: every skeleton statement must be spot-checked, not only the
ones that look risky.**

### 2.3 Why these formulation choices (and what each one buys)

1. **Descriptor as a predicate, not a curve-invariant claim.** `HammondDescriptor` is a
   `Prop` that can be negated and used in sharpness statements (`⟺ 0 < lam`, H3) — the same
   design as the Marcus `InvertedDescriptor`, so the two theories compose.
2. **`HammondConforms` separates the two levels of the human question.** The *family-level*
   descriptor depends on `λ` alone; the *point-level* verdict `HammondConforms` depends on
   `(λ, x)` and asserts that a resemblance verdict is meaningful at all (crossing strictly
   between the wells). Instances in the inverted region are not "anti-Hammond reactions" —
   they are instances **outside the domain where the Hammond reading applies**; the plan uses
   exactly this wording (§8, §13).
3. **`α` is a *secant*, not a definitional copy of `q‡`.** Defining `α := q‡` would make the
   "α measures the structural extent" claim a tautology. Here `lefflerSecant` is computed from
   barrier data only, and `lefflerSecant_eq_midpoint` (H2) *proves* it equals the structural
   coordinate at the midpoint. That is the non-trivial content of Leffler's relation, and in
   this model it is **exact** (the barrier is a quadratic, so the midpoint is the exact
   secant point — no mean value theorem, no analysis).
3b. **The regime boundary is not our invention.** Marcus 1968's eq. (32) carries the explicit
applicability condition `|ΔF°'| ≲ λ`, which is exactly `ReactionRegion lam x` (`-λ < x < λ`); the same
paper describes the coordinate as the "product-like character" of the TS. The H2 statements are
therefore the *model's* theorems, with a documented primary locus for both the identity and its
range — still not a claim about a molecule (plan §13 rows 11/12).
4. **Both sign conventions are stated and bridged.** `x = -ΔG°` (Marcus convention, used for
   everything) and `dG = ΔG°` (used in the surface definitions); the crossing theorem
   `crossing_iff` is stated in `dG` and the coordinate in `x`, so sign errors cannot hide.
5. **The zero-curvature branch is handled, not assumed away.** `tsCoord 0 x = 0` by Lean's
   `x / 0 = 0` convention — a *formal* convention, not a physical fact — and it is exactly
   what makes the `λ = 0` failure branch true; it is therefore labelled as such (§13, item 5).
6. **No temperature anywhere.** `kB`, `T`, `A` do not occur in this theory; the descriptor's
   premises are `0 < λ` (later derived microscopically in H4). This is a strictly stronger
   composition than the Marcus one and is worth stating explicitly in the final report.

### 2.4 Proof discipline (non-negotiable)

1. Delivered theorems contain no `sorry` and no custom `axiom`; `#print axioms` shows only
   `propext`, `Classical.choice`, `Quot.sound` (contract `ALLOWED_AXIOMS`).
2. **Physical/modeling premises are explicit theorem hypotheses** (`0 < lam`, `lam ≠ 0`,
   `x₁ ≠ x₂`, the Pekar and geometric premises, …); none may be folded into a definition.
3. One lemma = one commit: `feat(H<n>): <lemma>` (`<n>` = milestone number). Deviations
   (semantic batches) must be recorded on the board as known deviations, as in the Marcus run.
4. API names are never guessed: consult `proofs/API-NOTES.md`; the `api_researcher` calibrates
   new names and records them. The Hammond milestone's calibration section is in that file.
5. Exclusive file ownership (§10). **`lake build` succeeding is not acceptance** — the
   three-layer gate (build + strict scan + `#print axioms`) is run by the `verifier`.
6. Statement-first: the skeleton (`theories/hammond/probes/hammond-statement-skeleton.lean`)
   is authoritative; a delivered file must match it word for word (fidelity check).
7. ASCII identifiers only (`lam`, `lamIn`, `nSq`, …, never `λ`, which is a Lean keyword).
8. Doc comments must not contain the scanned placeholder keyword literally (the strict scan
   does not skip block comments — see `proofs/EXPERIENCE.md`).

---

## 3. File layout and dependency graph

```text
PhotoLean/Hammond/
  Basic.lean       -- H1 : definitions + crossing geometry + classifier lemmas
  Criterion.lean   -- H2 : monotonicity, energy–structure, Leffler identity, Marcus bridge
  Sharp.lean       -- H3 : ⟺ 0 < lam + explicit reversal witnesses
  Compose.lean     -- H4 : microscopic λ > 0 (imports Marcus.Reorg) ⇒ descriptor
  RatModel.lean    -- H5a: ℚ classifier, ℚ observables, transfer lemmas
  Instances.lean   -- H5b: instance verdicts (kernel-checked)
theories/hammond/
  plan.md, TASKS.md, LITERATURE.md, RESULTS.md
  probes/          -- statement skeleton, risk probe, API probes, cross-check probe
```

Imports (`→` = import):

```text
Basic ──→ Criterion ──→ Sharp ──┬──→ Compose  (also imports PhotoLean.Marcus.Reorg)
  │                             │
  ├──→ RatModel ────────────────┴──→ Instances
  └──→ (nothing else: Basic imports Mathlib only)
```

Critical path: `Basic → Criterion → Sharp → Instances`. Parallel branches: `RatModel` (needs
`Basic` only) and `Compose` (needs `Criterion` + the delivered `Marcus.Reorg`).

**Engineering necessity (lead-owned)**: `lakefile.toml` `defaultTargets` must gain one line per
delivered module, otherwise a bare `check.sh --strict` scans the whole tree but builds nothing
new — an acceptance hole already documented in the Marcus run.

---

## 4. H1 — description layer (`Hammond/Basic.lean`; owner prover_a)

**Goal**: make "TS structure", "resembles", "Hammond regime" and "Hammond description" Lean
objects, and ground `tsCoord` in the surface geometry (why *this* expression is the TS).

### 4.1 Definitions

§2.2 in full.

### 4.2 Crossing geometry (the model's own consistency)

```lean
theorem crossing_iff {lam dG q : ℝ} (hlam : lam ≠ 0) :
    reactantSurface lam q = productSurface lam dG q ↔ q = tsCoord lam (-dG)
theorem gapReactant_eq_crossing_energy {lam dG : ℝ} (hlam : lam ≠ 0) :
    gapReactant lam (-dG) = reactantSurface lam (tsCoord lam (-dG))
theorem gapProduct_eq_crossing_energy {lam dG : ℝ} (hlam : lam ≠ 0) :
    gapProduct lam (-dG) = productSurface lam dG (tsCoord lam (-dG)) - dG   -- measured from the product well
theorem gapProduct_sub_gapReactant {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    gapProduct lam x - gapReactant lam x = x
theorem gapProduct_eq_gapReactant_neg (lam x : ℝ) : gapProduct lam x = gapReactant lam (-x)
theorem tsCoord_neg {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) : tsCoord lam (-x) = 1 - tsCoord lam x
theorem tsCoord_zero {lam : ℝ} (hlam : lam ≠ 0) : tsCoord lam 0 = 1 / 2
theorem tsCoord_zero_lam (x : ℝ) : tsCoord 0 x = 0
theorem tsCoord_at_lam {lam : ℝ} (hlam : lam ≠ 0) : tsCoord lam lam = 0
```

### 4.3 Regime predicates and the classifier

```lean
theorem tsCoord_mem_iff {lam x : ℝ} (hlam : 0 < lam) :
    0 < tsCoord lam x ∧ tsCoord lam x < 1 ↔ ReactionRegion lam x
theorem reactionRegion_pos {lam x : ℝ} (h : ReactionRegion lam x) : 0 < lam
theorem not_reactionRegion_of_nonpos {lam x : ℝ} (hlam : lam ≤ 0) : ¬ ReactionRegion lam x
theorem hammondZone_eq_early_iff          {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.early ↔ 0 < x ∧ x < lam
theorem hammondZone_eq_half_iff           {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.half ↔ x = 0
theorem hammondZone_eq_late_iff           {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.late ↔ x < 0 ∧ -lam < x
theorem hammondZone_eq_atReactant_iff     {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.atReactant ↔ x = lam
theorem hammondZone_eq_atProduct_iff      {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.atProduct ↔ x = -lam
theorem hammondZone_eq_beyondReactant_iff {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.beyondReactant ↔ lam < x
theorem hammondZone_eq_beyondProduct_iff  {lam x : ℝ} (hlam : 0 < lam) :
    hammondZone lam x = HZone.beyondProduct ↔ x < -lam
```

**Proof sketches**: `crossing_iff` — expand the surfaces, `eq_div_iff (mul_ne_zero two_ne_zero hlam)`
for `⇒`, `field_simp; ring` for `⇐`, then `nlinarith`. `gapReactant_eq_crossing_energy` —
clear denominators with explicit `(4*lam) ≠ 0`, `(2*lam) ≠ 0`, then `ring`. The zone lemmas —
`unfold hammondZone`, `by_cases`/`split_ifs` on the branch conditions, close each branch with
`linarith`/`norm_num` (the probe has the working shape for the `early` branch).
**Acceptance**: `check.sh --strict PhotoLean.Hammond.Basic` PASS; `axioms.sh` clean for every
theorem; verifier re-checks the seven zone lemmas against the classifier *definition*.

---

## 5. H2 — Hammond criterion (`Hammond/Criterion.lean`; owner prover_a)

**Goal**: prove the postulate's content in the model, including the two *exact* bridges
(energy ↔ structure; barrier data ↔ structure) and the Marcus cross-link.

```lean
/-- The postulate's direction. -/
theorem tsCoord_antitone {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ} (h : x₁ < x₂) :
    tsCoord lam x₂ < tsCoord lam x₁
theorem hammond_descriptor_holds {lam : ℝ} (hlam : 0 < lam) : HammondDescriptor lam

/-- Qualitative Hammond: exergonic ⇒ reactant-like, endergonic ⇒ product-like. -/
theorem reactantLike_iff {lam x : ℝ} (hlam : 0 < lam) : ReactantLike lam x ↔ 0 < x
theorem productLike_iff  {lam x : ℝ} (hlam : 0 < lam) : ProductLike lam x ↔ x < 0

/-- Hammond's own criterion: closest in structure ⟺ closest in energy. -/
theorem gap_compare_iff {lam x : ℝ} (hlam : 0 < lam) :
    gapReactant lam x < gapProduct lam x ↔ 0 < x

/-- Leffler's relation, exact in this model (α is a barrier-data observable). -/
theorem lefflerSecant_eq_midpoint {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h : x₁ ≠ x₂) :
    lefflerSecant lam x₁ x₂ = tsCoord lam ((x₁ + x₂) / 2)
theorem lefflerSecant_symm {lam x : ℝ} (hlam : 0 < lam) :
    lefflerSecant lam (x - 1) (x + 1) = tsCoord lam x
theorem lefflerSecant_mem_iff {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h : x₁ ≠ x₂) :
    0 < lefflerSecant lam x₁ x₂ ∧ lefflerSecant lam x₁ x₂ < 1 ↔
      ReactionRegion lam ((x₁ + x₂) / 2)

/-- Where the postulate's structural reading runs out: the Marcus inverted region. -/
theorem tsCoord_lt_zero_iff_inverted {lam x : ℝ} (hlam : 0 < lam) :
    tsCoord lam x < 0 ↔ Marcus.InvertedRegion lam x
theorem lefflerSecant_neg_iff_inverted {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h : x₁ ≠ x₂) :
    lefflerSecant lam x₁ x₂ < 0 ↔ Marcus.InvertedRegion lam ((x₁ + x₂) / 2)

/-- Verdict characterization + non-vacuity (the predicates are inhabited). -/
theorem conforms_iff_zone {lam x : ℝ} (hlam : 0 < lam) :
    HammondConforms lam x ↔
      hammondZone lam x = HZone.early ∨ hammondZone lam x = HZone.half ∨
        hammondZone lam x = HZone.late
theorem exists_reactantLike   {lam : ℝ} (hlam : 0 < lam) : ∃ x : ℝ, ReactantLike lam x
theorem exists_productLike    {lam : ℝ} (hlam : 0 < lam) : ∃ x : ℝ, ProductLike lam x
theorem exists_reactionRegion {lam : ℝ} (hlam : 0 < lam) : ∃ x : ℝ, ReactionRegion lam x

/-- Fidelity bridge to the delivered Marcus module (definitionally the same function). -/
theorem barrier_eq_gapReactant (lam x : ℝ) : Marcus.barrier lam x = gapReactant lam x
```

**Proof sketches** (all probe-validated except `conforms_iff_structure` and the `exists_*`
lines, which are one-liners with witnesses `x = lam/2`, `x = -lam/2`, `x = 0`):
- `tsCoord_antitone`: `unfold tsCoord`, `div_lt_div_iff_of_pos_right (by linarith : 0 < 2*lam)`, `linarith`.
- `gap_compare_iff`: from `gapProduct lam x - gapReactant lam x = x` (H1), `constructor <;> intro <;> linarith`.
- `lefflerSecant_eq_midpoint`: `unfold lefflerSecant tsCoord`, `field_simp`, `ring`.
- `lefflerSecant_mem_iff`: `lefflerSecant_eq_midpoint` + `tsCoord_mem_iff` (H1).
- `tsCoord_lt_zero_iff_inverted`: `unfold tsCoord Marcus.InvertedRegion`, `div_lt_iff₀ (by linarith)`, `linarith`
  (note: `div_neg_iff_of_pos_right` does **not** exist in v4.17 — see `proofs/API-NOTES.md`).
- `exists_*`: explicit witnesses + the corresponding `iff` lemma + `nlinarith`.
**Risk**: low (no analysis). **Acceptance**: strict gate + `#print axioms` per theorem;
verifier must independently re-derive `lefflerSecant_eq_midpoint` numerically at two rational
points and confirm the definition of `lefflerSecant` is genuinely barrier-based.

---

## 6. H3 — sharp conditions (`Hammond/Sharp.lean`; owner prover_d)

**Goal**: prove that `λ > 0` is *necessary and sufficient*, with explicit counter-witnesses
(not just a negated quantifier).

```lean
theorem hammond_lam_pos_of_descriptor {lam : ℝ} (h : HammondDescriptor lam) : 0 < lam
theorem hammond_sharp (lam : ℝ) : HammondDescriptor lam ↔ 0 < lam
theorem hammond_fails_of_nonpos {lam : ℝ} (hlam : lam ≤ 0) : ¬ HammondDescriptor lam
theorem exists_direction_reversal_of_neg {lam : ℝ} (hlam : lam < 0) :
    ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧ tsCoord lam x₁ < tsCoord lam x₂
theorem exists_direction_reversal_of_eq :
    ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧ ¬ (tsCoord 0 x₂ < tsCoord 0 x₁)
theorem conforms_requires_pos {lam x : ℝ} (h : HammondConforms lam x) : 0 < lam
```

**Proof sketch**: `hammond_lam_pos_of_descriptor` — `rcases lt_trichotomy lam 0`; the `λ = 0`
branch reduces the descriptor to `0 < 0` (division-by-zero convention `tsCoord 0 x = 0`); the
`λ < 0` branch contradicts the descriptor via `div_lt_div_right_of_neg` (probe-validated).
`hammond_sharp = ⟨hammond_lam_pos_of_descriptor, hammond_descriptor_holds⟩`.
Witnesses: `(0, 1)` in both branches (probe-validated).
**Acceptance**: strict gate + `#print axioms`; verifier must confirm the two witnesses are
genuine (kernel-level evaluation) and that no branch of `lt_trichotomy` is dropped.

---

## 7. H4 — microscopic conditions (`Hammond/Compose.lean`; owner prover_b)

**Goal**: replace the abstract premise `0 < λ` by microscopic conditions, reusing the delivered
`PhotoLean/Marcus/Reorg.lean` (no new physics is invented here).

```lean
theorem hammond_descriptor_of_inner {kk dq : ℝ} (hkk : 0 < kk) (hdq : dq ≠ 0) :
    HammondDescriptor (Marcus.lamInner kk dq)

theorem hammond_descriptor_of_microscopic {kk dq dE a1 a2 R nSq epsS : ℝ} (hkk : 0 ≤ kk)
    (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2) (hR : 0 < R)
    (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    HammondDescriptor (Marcus.lamInner kk dq + Marcus.lamOuter dE a1 a2 R nSq epsS)

theorem hammond_descriptor_of_nonoverlap {kk dq dE a1 a2 R nSq epsS : ℝ} (hkk : 0 ≤ kk)
    (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2) (hRge : a1 + a2 ≤ R) (hnSq : 0 < nSq)
    (hepsS : 0 < epsS) (hPekar : 1 / epsS < 1 / nSq) :
    HammondDescriptor (Marcus.lamInner kk dq + Marcus.lamOuter dE a1 a2 R nSq epsS)

theorem exists_reactionRegion_of_microscopic {kk dq dE a1 a2 R nSq epsS : ℝ} (hkk : 0 < kk)
    (hdq : dq ≠ 0) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2) (hR : 0 < R)
    (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    ∃ x : ℝ, ReactionRegion (Marcus.lamInner kk dq + Marcus.lamOuter dE a1 a2 R nSq epsS) x
```

**Proof sketch**: `lamInner_pos` / `lamOuter_pos` / `lam_total_pos` (all delivered) give the
positive curvature, then `hammond_descriptor_holds` (H2) and `exists_reactionRegion` (H2).
The composition carries **no** `A`, `kB`, `T` premises — strictly fewer than the Marcus
counterpart `Marcus.descriptor_holds_of_microscopic`.
**Acceptance**: strict gate + `#print axioms`; verifier checks that every physical premise is
visible in the signature (`hnSq`, `hepsS`, `hPekar`, `hgeom`) and that the used Marcus lemmas
really are the delivered ones.

---

## 8. H5 — instances and verdicts (owner prover_c)

### 8.1 Decision layer (`Hammond/RatModel.lean`)

Mirror the H1/H2 objects on `ℚ` (`tsCoordQ`, `gapReactantQ`, `lefflerSecantQ`, `hammondZoneQ`)
and prove the **transfer lemmas** that make a rational computation binding for the real theory:

```lean
theorem tsCoordQ_cast (lam x : ℚ) :
    ((tsCoordQ lam x : ℚ) : ℝ) = tsCoord (lam : ℝ) (x : ℝ)
theorem gapReactantQ_cast (lam x : ℚ) :
    ((gapReactantQ lam x : ℚ) : ℝ) = gapReactant (lam : ℝ) (x : ℝ)
theorem lefflerSecantQ_cast {lam x₁ x₂ : ℚ} (h : x₁ ≠ x₂) :
    ((lefflerSecantQ lam x₁ x₂ : ℚ) : ℝ) = lefflerSecant (lam : ℝ) (x₁ : ℝ) (x₂ : ℝ)
theorem hammondZoneQ_eq_hammondZone (lam x : ℚ) :
    hammondZoneQ lam x = hammondZone (lam : ℝ) (x : ℝ)
-- plus the seven rational zone-characterization lemmas and the Marcus cross-link
theorem hammondZoneQ_beyondReactant_iff_inverted {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.beyondReactant ↔ Marcus.Rat.zoneQ lam x = Marcus.Zone.inverted
```

### 8.2 Instance verdicts (`Hammond/Instances.lean`)

Every verdict is a kernel-checked theorem; "conforms" is `HammondConforms`, "does not conform"
is its negation (with the zone and the coordinate as the reason). `lam` and `x` in eV;
rational literals; `x = -ΔG°`.

| # | Instance | `lam` | `x` | model coordinate `q‡` | verdict (kernel) |
|---|---|---|---|---|---|
| I1 | thermoneutral textbook | 1 | 0 | `1/2` | conforms (`HZone.half`) |
| I2 | mildly exergonic textbook | 1 | `3/4` | `1/8` | conforms, reactant-like (`HZone.early`) |
| I3 | endergonic textbook | 1 | `-1/2` | `3/4` | conforms, product-like (`HZone.late`) |
| I4 | barrierless forward | 1 | 1 | `0` | **boundary**: `¬ HammondConforms` (strict regime fails) while the family descriptor still holds |
| I5 | literature MCC, normal region | `6/5` | `1/20` | `23/48` | conforms (`HZone.early`) |
| I6 | literature MCC, inverted region | `6/5` | `12/5` | `q‡ = -1/2` at `x = 12/5`; the **secant** over the MCC pair `3/5 → 12/5` is `-1/8` (its midpoint is `x = 3/2`) | **does not conform** (`HZone.beyondReactant`; also `Marcus.InvertedRegion`; the measured slope is negative) |
| I7 | literature reaction centre, deep inverted | `1/4` | `11/10` | `-17/10` | **does not conform** (`HZone.beyondReactant`) |
| I8 | non-physical curvature | `-1/2`, `0` | any | — | **rejected**: `¬ HammondDescriptor` in both branches; no `x` in the regime |
| I9 | MCC pair, Hammond direction | `6/5` | `3/5 → 12/5` | descending | `tsCoord (12/5) < tsCoord (3/5)` (descriptor instantiated) |
| I10 | non-vacuity on literature parameters | `6/5` | `±1/20` | — | `ReactantLike ∧ ProductLike` both inhabited |

Instances I5–I7 reuse the parameter pairs already *verified* in
`theories/Marcus/LITERATURE.md` §实例参数候选表 (MCC series `lam = 1.20 eV`, photosynthetic
reaction centre `lam = 0.25 eV`); the `literature_researcher` re-checks provenance and status
before delivery, and `theories/hammond/LITERATURE.md` §6 is the authority for the values.
**Verification note**: exact rational literals are checked by `norm_num`-style computation +
the transfer lemmas (the Marcus run showed `decide` is reliable only for integer literals).

**Acceptance**: strict gate + `#print axioms` per instance; verifier confirms each verdict comes
from kernel computation or theorem instantiation (not from a comment), and that no instance
theorem asserts anything about experimental data.

---

## 9. Dependency graph (critical path in bold)

```text
**H1 Basic ──► H2 Criterion ──► H3 Sharp ──┐**
      │              │                      ├──► H4 Compose (needs Marcus.Reorg)
      │              └──► H5b Instances ◄───┘
      └──► H5a RatModel ─────┘
```

- H5a depends on H1 only (parallel to the critical path).
- H4 depends on H2 (+ delivered Marcus modules) — it does **not** wait for H3.
- H5b depends on H5a and H3 (the non-physical verdicts use H3).

---

## 10. Sprint order and parallel boundaries

**Principle**: front-load the risk. The only genuinely non-trivial items in this theory are
(a) the seven-branch classifier transfer `hammondZoneQ_eq_hammondZone` and (b) the zone
characterization lemmas — both are in H1/H5a and are therefore scheduled first, not last.

| Sprint | Content | Owner (exclusive file) | Parallelism |
|---|---|---|---|
| **S0 (done)** | statement skeleton compiled; risk probe (0 error); contract + gate extended (`THEORIES="Marcus hammond"`); plan/board/leaves landed; literature + API calibration dispatched | lead | 3-way (lead + 2 researchers) |
| **S1** | H1 `Basic.lean` (critical path start) | prover_a | 1-way |
| **S2** | H2 `Criterion.lean`; H5a `RatModel.lean` (needs H1 only) | prover_a / prover_c | 2-way |
| **S3** | H3 `Sharp.lean` (needs H2); H5b `Instances.lean` written against the frozen skeleton (compiles once H3 lands) | prover_d / prover_c | 2-way |
| **S4** | H4 `Compose.lean` (needs H2 + Marcus.Reorg); independent cross-check probe re-deriving the instance verdicts from the definitions | prover_b / prover_a | 2-way |
| **S5** | per-batch verifier gates (H1+H5a, H2+H3, H4+H5b), frozen full-tree gate, board ticks, `RESULTS.md`, experience-bank write-back | verifier + lead | — |

**Hard parallel constraint**: one file, one owner at a time; hand-off requires verifier PASS +
a board update by the lead. Any `BLOCKED` goes to `proofs/EXPERIENCE.md` immediately, with the
failed paths, not just the successful one.

**Owner map**: `Basic.lean` + `Criterion.lean` → prover_a; `Sharp.lean` → prover_d;
`Compose.lean` → prover_b; `RatModel.lean` + `Instances.lean` → prover_c.
Lead owns: contract, `lakefile.toml`, plan/board/RESULTS, statement skeleton, risk probe.

---

## 11. Acceptance criteria (script level, not self-declared)

Per theorem, the contract's three-layer gate:

```bash
proofs/scripts/lake build <Module>                            # 1. compile
proofs/scripts/check.sh --strict <Module>                     # 2. build + placeholder/axiom scan
proofs/scripts/axioms.sh <Module> <fully.qualified.theorem>   # 3. #print axioms ⊆ ALLOWED_AXIOMS
git log -1 --oneline                                          # 4. feat(H<n>): <lemma>
```

Additional, milestone-specific:
- H1: verifier re-derives the seven zone lemmas from the classifier definition; confirms the
  geometry theorems really mention the surfaces (not a restated `tsCoord` identity).
- H2: verifier re-computes `lefflerSecant` numerically at two rational points from **barrier
  values only** and confirms the midpoint identity; confirms `barrier_eq_gapReactant` is `rfl`.
- H3: kernel-level check of both direction-reversal witnesses; check that `lt_trichotomy`'s
  three branches are all consumed.
- H4: confirm the physical premises are visible in the signature and that the used lemmas are
  the delivered Marcus ones.
- H5: every verdict must come from kernel computation or theorem instantiation; no instance
  theorem may assert anything about experimental measurement.
- Final: bare `check.sh --strict` on the frozen commit (documented as the only full-tree gate).

---

## 12. mathlib adaptation list (owned by `api_researcher` → `proofs/API-NOTES.md`)

| Class | Names to calibrate | Used by |
|---|---|---|
| Division/order | `div_lt_div_iff_of_pos_right`, `div_lt_div_right_of_neg`, `div_lt_iff_of_neg`, `lt_div_iff_of_neg`, `div_lt_iff₀`, `lt_div_iff₀`, `div_pos_iff_of_pos_right`, `div_lt_one`, `one_lt_div`, `div_eq_iff`, `eq_div_iff` | H1–H3 |
| **Missing name (measured)** | `div_neg_iff_of_pos_right` does **not** exist (v4.17); the working route for `a / c < 0 ↔ a < 0` in H2's `tsCoord_lt_zero_iff_inverted` must be recorded | H2 |
| Field normalization | `field_simp` + `ring` vs `ring_nf` on the five algebraic identities of H1/H2; which nonzero side conditions are really needed | H1, H2 |
| ℚ layer | `Rat.cast_lt`, `Rat.cast_le`, `Rat.cast_inv`, `Rat.cast_div`, `push_cast`; `norm_num [hammondZoneQ]` on rational literals; `decide` domain | H5a, H5b |
| Classifier transfer | `split_ifs` / `by_cases` recipe for the 7-branch `if`-chain on ℚ vs ℝ | H5a |
| Cross-module names | `Marcus.barrier`, `Marcus.InvertedRegion`, `Marcus.Zone`, `Marcus.Rat.zoneQ`, `Marcus.lamInner`, `Marcus.lamOuter`, `Marcus.lamInner_pos`, `Marcus.lamOuter_pos`, `Marcus.lam_total_pos`, `Marcus.hgeom_of_nonoverlap` | H2, H4, H5a |
| Tactics | `linarith`, `nlinarith`, `ring`, `field_simp`, `norm_num`, `positivity`, `split_ifs` | all |

**Rule**: no name from memory. Every recommended name must have been `#check`ed or used in a
compiling probe (the Hammond probe set is `theories/hammond/probes/hammond-api-*.lean`).

---

## 13. Literature anchors and explicit modeling assumptions

**Anchors** (loci and verbatim wording are owned by `theories/hammond/LITERATURE.md` §1):
Hammond 1955 `10.1021/ja01607a027` (the postulate, verbatim p. 334; his own later verdict that the
rules' weak point is the *similar-potential-functions* assumption, Citation Classic 1985);
IUPAC glossary `10.1515/pac-2018-1010` (normative terms: "Hammond–Leffler principle" as a
*hypothesis*, `α` as an approximate displacement measure, "many exceptions", the anti-Hammond /
Thornton perpendicular effect); Marcus 1956 `10.1063/1.1742723` (two-parabola model, barrier
Eq. (38) p. 974); Marcus 1960 `10.1039/df9602900021` (first statement of the inverted region, p. 28);
Marcus Nobel 1992 (barrier Eq. (5b) p. 78; the Brønsted/Tafel-plot analogy p. 82; slope 1/2 p. 85;
`λ_s`/`λ_v`/`ω` annotation p. 84; reaction-centre numbers p. 88; the atom/proton/methyl-transfer
scope limit p. 90); Cohen & Marcus 1968 `10.1021/j100858a052` and Marcus 1968 `10.1021/j100849a019`
(the α slope, applied to 16 experimental series), Marcus 1969 `10.1021/ja01054a003`
(slope ↔ TS position), **Marcus 1968 §"Meaning of the Brønsted Slope", p. 896, eq. (32)**
(`α = ½(1 + ΔF°'/λ)` when `|ΔF°'| ≲ λ`) — the primary locus of the central identity, of which
`lefflerSecant_eq_midpoint` is the finite-difference form, and whose stated applicability condition
`|ΔF°'| ≲ λ` **is** `ReactionRegion`; García-Padilla & Qiu 2025 `10.1039/d5sc04829j` (published analogue of
"inverted region = negative Brønsted slopes" and of the model's mirror symmetry);
Villegas-Escobar 2026 `10.1016/j.chemphys.2026.113488` (equality `α` = TS position is exact only in
the symmetric/equal-curvature approximation); Miller–Calcaterra–Closs 1984 `10.1021/ja00322a058`
(MCC data). **DOI correction**: Marcus & Sutin 1985 is `10.1016/0304-4173(85)90014-X`; the DOI
`10.1016/0005-2728(85)90039-9` is a 404 at Crossref and doi.org — never cite it.

**Assumptions that are NOT derived (and must be stated as such in every downstream claim)**:

| # | Assumption | Where it lives in Lean |
|---|---|---|
| 1 | one scalar reaction coordinate stands for "molecular structure" | `reactantSurface`/`productSurface`/`tsCoord` definitions (documented) |
| 2 | harmonic surfaces with **equal** curvature `2λ` | the surface definitions; unequal curvature is out of scope (§14) |
| 3 | the TS is the classical crossing point (no tunneling, no recrossing, static picture) | `tsCoord` = crossing coordinate; `crossing_iff` |
| 4 | `λ` is the Marcus reorganization energy (`λ = λ_in + λ_out`, Pekar form) | `Marcus.lamInner`, `Marcus.lamOuter`, reused in H4 |
| 5 | the `λ = 0` branch depends on Lean's `x / 0 = 0` **convention** | `tsCoord_zero_lam`, H3's `λ = 0` witness — a formal convention, not physics |
| 6 | the inverted-region verdict is a statement *inside the model*, not about a molecule | `HammondConforms` negation + `Marcus.InvertedRegion` |
| 7 | real systems with `x > λ` are not "anti-Hammond reactions"; the model simply leaves the domain where the structural reading applies | wording rule for `RESULTS.md` and instance doc comments |
| 8 | **`λ` is constant across the compared pair/series** (fixed intrinsic barrier). Without this, `HammondDescriptor lam` is not the right object: the postulate is not claimed between different intrinsic reactivities (S23, S24; also Marcus 1968's "conjecture") | implicit in `HammondDescriptor lam` / `lefflerSecant lam …`; documented in the module headers |
| 9 | **equal curvature** of the two parabolas (symmetric case). Asymmetric force constants make the thermoneutral TS position force-constant-dependent and break the exactness of `α = q‡` (S14, S15, S17; Hammond's own "similar potential functions" caveat, S2) | the shared `lam` in `reactantSurface`/`productSurface` |
| 10 | **one scalar coordinate** stands for molecular structure; the TS never coincides with either well, and off-path (perpendicular / anti-Hammond) effects are structurally inexpressible here (S16, S4, S32) | `tsCoord` definition + §1.3 |
| 11 | the inverted-region verdict is **model-internal**; `α < 0 ⟺ inverted region` is a **theorem of the equal-curvature model**, *not* a literature identity (LITERATURE.md §4.2: no source states it) — its statement-level support is Nobel p. 82 + Cohen & Marcus 1968 + Marcus 1968, with García-Padilla & Qiu 2025 as the modern published analogue | `lefflerSecant_neg_iff_inverted`, `inst_I6_*`; wording rule |
| 12 | **instance scope**: no proton/atom/methyl-transfer (bond-breaking) parameter set may receive a `beyondReactant` verdict as a physical claim — the parabolic model and its inverted region are not licensed there (Nobel p. 90; Marcus 1968 Appendix II). The delivered instances I5–I7 are electron-transfer parameter sets | instance table §8.2 + `RESULTS.md` |
| 13 | **`0 < α < 1` is a model-internal characterization, not an experimental criterion**: measured Brønsted coefficients lie outside `(0,1)` in real systems (nitroalkane anomaly, α ≈ 1.5, Mayr & Ofial 2023 `10.1002/ijch.202300054`; also S25/S26 sigmoid or deviating slopes). In the model, `α ∉ (0,1)` corresponds to the mirror branches `|x| ≥ λ`, so the equivalence `0 < α < 1 ↔ ReactionRegion` must never be read as a claim about measured slopes | `lefflerSecant_mem_iff`, `hammondZoneQ_eq_*_iff`; `RESULTS.md` wording rule |
| 14 | **"or neither"**: Hammond's original wording allows a TS resembling *reactants, products, or neither*. In the model, the exactly thermoneutral point (`q‡ = 1/2`, `HZone.half`) is the equal-resemblance ("neither") case, and the `beyond*` branches are the cases where the crossing point is not a structural intermediate at all (the resemblance reading is *undefined*, not "resembling neither") — the two must not be conflated in the report | `conforms_iff_zone`, `HZone.half`, wording rule |

**Wording rule (binding)**: instance verdicts say "the instance lies in/outside the Hammond
regime of the two-parabola model"; they never say "this molecule obeys/violates Hammond's
postulate".

---

## 14. Next stations (preview, not in H1–H5)

① **Unequal curvatures** `λ_R ≠ λ_P`: the crossing equation becomes quadratic; monotonicity
survives but the affine `α` does not (needs the implicit function theorem or `Real.sqrt`
manipulation). This is the sharpest boundary of the present theory.
② **Anharmonic surfaces**: the secant identity becomes an inequality (mean value theorem);
would need calculus in mathlib (available) but the model's exactness is lost.
③ **Dynamical recrossing / variational TS**: needs a dynamics layer (out of mathlib's scope).
④ **Empirical Brønsted `α` comparison — source found, stays outside the kernel**: Cohen & Marcus
1968 applied the model slope to Brønsted-slope data of 16 proton- and atom-transfer series
("consistent, but more data are needed"); modern measured-α series exist (rhenium-hydride hydride
transfer 2022; enzymatic proton transfer 2000). Comparing an *experimental* slope with the model's
`α` would be a **modelling claim about a real system**, not a theorem, and is therefore *not*
formalized — it is recorded in `LITERATURE.md` §4.1(iv)/§6 as documentation only.
