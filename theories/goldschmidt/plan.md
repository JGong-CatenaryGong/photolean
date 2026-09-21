# theories/goldschmidt/plan.md — PhotoLean formalization plan: the Goldschmidt tolerance factor and Goldschmidt's rules (G1–G6)

> Project: turn the **Goldschmidt tolerance factor** `t = (r_A + r_O) / (√2 (r_B + r_O))` of the
> `ABO₃` perovskite family — together with **Goldschmidt's rules of ionic substitution** — into a
> *machine-checked* theory of the ideal cubic perovskite geometry.
> Target system: Lean 4.17.0 + mathlib (`MODULE_PREFIX=PhotoLean`, contract `proofs/ENGINE.yml`).
> Status: **Sprint 0 in progress** (2026-09-21) — contract entry, statement authority, lead risk
> probe, API calibration, literature round 1, plan. Milestone status is tracked on the board
> `theories/goldschmidt/TASKS.md`; that file is the single source of truth, this file is the plan of
> record.
> Authority: contract `proofs/ENGINE.yml`; board `theories/goldschmidt/TASKS.md`; experience bank
> `proofs/EXPERIENCE.md`; literature `theories/goldschmidt/LITERATURE.md` with the printed radii
> tables in `theories/goldschmidt/literature/INSTANCE-DATA.md`.
> **Statement authority**: `theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean` —
> delivered signatures must match it word for word (check: `python3 theories/BEP/probes/bep-fidelity.py
> --theory goldschmidt [--milestone G<k>]`).
> **Sprint-0 kernel evidence**: `theories/goldschmidt/probes/goldschmidt-risk-probe.lean` — in
> flight (owner `prover_a`). Status recorded honestly: at the time the milestones were dispatched the
> probe did **not** compile, so it is **not** the evidence that gated them; what gated the dispatches
> was the authority skeleton compiling and the milestone provers' own kernel work. Four FALSE
> authority rows were found — three of them (`tolFac_mono_rO_of_lt`, `tolFac_anti_rO_of_lt`,
> `tolFac_rO_const_iff`, §3.1 items 6–8) by `prover_d` in the kernel while proving G3, one
> (`chiTol_anti`, item 9) by `prover_c` while proving G2. The probe is being brought to 0 error in
> parallel; until it is, no row of it may be cited as kernel evidence anywhere in this repository.

---

## 1. Overall goal and boundaries

### 1.1 The physical claim being formalized

Goldschmidt's geometric criterion for the `ABO₃` perovskite family is a statement about the
**packing of three ionic radii**: in the ideal cubic perovskite the `B` cation touches the six
face-centred oxygens (`r_B + r_O = a/2`, `a` the cubic lattice parameter) while the `A` cation sits
in the cuboctahedral cage whose `A`–`O` distance is `a/√2`; the ratio of the two contact distances,
normalized by the ideal one, is the **tolerance factor**

```
t = (r_A + r_O) / (√2 (r_B + r_O))     ("ideal" ⟺ t = 1 ⟺ both contacts hold simultaneously).
```

The empirical reading of `t` is a **band**: goldschmidtite-type work uses `0.8 ≤ t ≤ 1.0` for the
cubic (or pseudo-cubic) perovskite, above which the structure distorts (tetragonal/ferroelectric,
`1.0 < t < 1.1`) and below which it collapses into other structure types (hexagonal, ilmenite,
corundum, …). Alongside the factor, Goldschmidt's **rules of substitution** say when one ion may
replace another in a lattice: (i) *radius rule* — the radii must differ by less than about 15 %;
(ii) *charge rule* — an isovalent substitution needs no other change, a heterovalent one must be
accompanied by a compensating partner so that the total charge stays balanced; (iii) *chemical
rule* — the closer the electronegativities (chemical character), the larger the radius difference
that is still tolerated.

The three parts of the human request map onto:

> **Part ① — the formal description.** The tolerance factor as a function of the three radii, the
> ideal-packing condition (`t = 1`) with its geometric meaning, the band verdict as a Lean predicate
> `GoldschmidtConforms lo hi rA rB rO` (two-sided band with the band edges as *parameters*, so that
> `[0.8, 1.0]`, `[0.75, 1.0]`, `[1.0, 1.1]` and symmetric `1 ± δ` conventions are all instances of one
> definition), the three-way classifier `goldschmidtZone` (`tooSmall`/`ideal`/`tooLarge`), and the
> three substitution rules as predicates: `RadiusMatch τ r r'` (`|r - r'| ≤ τ * r`, the 15 % rule at
> `τ = 3/20`), `ChargeBalanced dz` (`∑ dz = 0` over the substitution set; the single-site
> specialization `dz = 0` is the isovalent case), and `Substitutable tol₀ k χ χ' r r'` (the
> electronegativity-dressed radius rule).

> **Part ② — proof and exact conditions.** The **law layer**: `t` is strictly increasing in `r_A`,
> strictly decreasing in `r_B`, and its dependence on `r_O` is a *sharp trichotomy* — increasing
> exactly for `r_A < r_B`, constant exactly for `r_A = r_B` (where `t = 1/√2` for every `r_O`),
> decreasing exactly for `r_B < r_A`; `t` is scale invariant (it depends only on the two ratios), and
> the exact affine shift law `t(r_A + d) - t(r_A) = d / (√2 (r_B + r_O))` holds. The **exact
> condition** for the band verdict is a *radius window*, and it is an equivalence:
> `GoldschmidtConforms lo hi rA rB rO ↔ rAMin lo rB rO ≤ r_A ∧ r_A ≤ rAMax hi rB rO` with the two
> edges written out in closed form; equivalently (and this is what makes the theory decidable in `ℚ`)
> a *squared* condition free of `√2`: `2 lo² (r_B+r_O)² ≤ (r_A+r_O)² ≤ 2 hi² (r_B+r_O)²`. The sharpness
> layer adds the band-monotonicity law (widening a band cannot lose a conforming candidate — the
> theorem that makes the band convention an explicit, changeable parameter), the emptiness of an
> inverted band, the *point band* characterization of the ideal case, the symmetric band
> `1 ± δ ↔ |r_A - idealA| ≤ δ √2 (r_B+r_O)`, the irrationality of `t` at rational radii (the reason the
> squared form is the decision form, not `t` itself), and the bridge that turns the 15 % **radius**
> rule into a bound on the **tolerance factor** shift.

> **Part ③ — instances and their verdicts.** A catalogue of instances — model-constructed rows (the
> ideal `A` radius `idealA rB rO`, the `r_A = r_B` degenerate row, non-vacuity rows for each zone,
> a band-flip row) and literature rows with Shannon's printed radii (`SrTiO₃`, `CaTiO₃`, `BaTiO₃`,
> `LaMnO₃`, `NaNbO₃`, `BaNiO₃`) — each decided by the kernel: does the triple conform to the band
> (`GoldschmidtConforms`), which zone does the classifier assign, and does the proposed substitution
> satisfy the radius rule / the charge-balance rule? Negative verdicts are delivered as such (e.g.
> the archetypal `SrTiO₃` row is *above* the classic `1.0` edge with Shannon radii, and `BaNiO₃` is
> outside even the tetragonal band — the literature's own hexagonal assignment), and every verdict
> that flips with the band convention is accompanied by the flip theorem rather than by prose.

### 1.2 The model (chosen, not derived)

| ingredient | formalization | status |
|---|---|---|
| ionic radii | three real scalars `rA`, `rB`, `rO` (Shannon's tabulated values are *instances*) | modelling choice (§12) |
| ideal cubic packing | `B`–`O` contact `r_B + r_O = a/2`, `A`–`O` distance `a/√2` | **declared modelling premise** (§12) |
| tolerance factor | `tolFac rA rB rO = (rA + rO) / (√2 * (rB + rO))` | definition (a *ratio*, not a fit) |
| ideal packing | `t = 1 ⟺ r_A + r_O = √2 (r_B + r_O) ⟺ r_A = idealA rB rO` | theorem |
| band verdict | `GoldschmidtConforms lo hi rA rB rO := lo ≤ tolFac rA rB rO ∧ tolFac rA rB rO ≤ hi` | definition (band edges are parameters) |
| zone classifier | `goldschmidtZone lo hi t ∈ {tooSmall, ideal, tooLarge}` | definition (three-way, decidable) |
| radius rule | `RadiusMatch τ r r' := |r - r'| ≤ τ * r`, the 15 % rule at `τ = 3/20` | definition (a *declared* rule) |
| charge rule | `ChargeBalanced dz := ∑ i, dz i = 0` over the substitution set | definition (integers, exact) |
| chemical rule | `Substitutable tol₀ k χ χ' r r'` with the electronegativity-dressed tolerance `chiTol` | declared *shape* (linear in `|Δχ|`), theorem = monotonicity |
| rational decision layer | `inBandQ` (the squared form on `ℚ`) + cast transfer to `conforms_iff_sq` | decision layer for instances |

The literature (`theories/goldschmidt/LITERATURE.md`) supports the *band* convention and the 15 %
figure as printed empirical statements; the **exact equivalences** of §6–§7 (radius window, squared
form, symmetric band, `r_O` trichotomy, irrationality) are this theory's own exactification and are
**absent from the literature** — that absence is recorded as a clean negative in the record (§12).

### 1.3 Human request → milestones

| Human request | Milestone | Deliverable |
|---|---|---|
| ① turn the tolerance factor and the rules into a formal description | **G1** (description layer) | `PhotoLean/Goldschmidt/Basic.lean`: `tolFac`, `idealAO`, `latticeOf`, `idealA`, `rAMin`, `rAMax`, `InBand`, `GoldschmidtConforms`, `GoldschmidtZone`, `goldschmidtZone`, band constants, the ideal-packing identifications and the classifier characterizations |
| ① the substitution rules as formal predicates | **G2** (rules layer) | `PhotoLean/Goldschmidt/Rules.lean`: `RadiusMatch` (15 % rule, window form, symmetry, transitivity/ratchet), `ChargeBalanced` (single-site isovalent characterization, two-site pairing, the compensating-partner existence theorem), `chiTol`/`Substitutable` (monotonicity in `|Δχ|`) |
| ②a prove the description | **G3** (law layer) | `PhotoLean/Goldschmidt/Criterion.lean`: strict monotonicity in `r_A` / `r_B`, the `r_O` trichotomy with `t = 1/√2 ⟺ r_A = r_B`, scale invariance and the ratio form, the exact shift law, the **radius-window equivalence** and its squared form, the symmetric `1 ± δ` band, the classic-band form, non-vacuity |
| ②b find the exact conditions / sharpen them | **G4** (sharp conditions) | `PhotoLean/Goldschmidt/Sharp.lean`: strict/non-strict band monotonicity, inverted-band emptiness, point-band iff (the ideal case), irrationality of `t` at rational radii, the radius-rule → `Δt` bound, the substitution-preserves-conformance transfer, and explicit failure witnesses for each way of leaving the band |
| ③a decide instances exactly | **G5** (rational decision layer) | `PhotoLean/Goldschmidt/RatModel.lean`: `tolFacSq`, `inBandQ`, `radiusMatchQ`, `zoneQ` — the `√2`-free criterion on `ℚ`, with the cast-transfer theorems showing the rational decision reproduces the real verdict (`inBandQ_cast`, `zoneQ_eq_zone`) |
| ③b plug in instances and decide | **G6** (instances & verdicts) | `PhotoLean/Goldschmidt/Instances.lean`: model rows and literature rows (Shannon radii), each with its kernel verdict: band conformance, zone, band-flip behaviour, radius-rule and charge-rule verdicts |

### 1.4 Explicit non-goals (scope control)

- **Not deriving the model.** That an `ABO₃` perovskite is described by three radii, that the ideal
  cubic geometry is the one of §1.2, and that a tolerance band is the right empirical criterion are
  modelling assumptions, not theorems; the formalized content is conditional on them (§12).
- **No claim that the tolerance factor is a theorem of crystallography or of quantum mechanics.** One
  geometric realization is made exact; nothing is said about stability energies, Goldschmidt's own
  "stability field", or DFT formation energies.
- **No continuous-deformation crystallography**: no tilting angles (`a⁻a⁻a⁻` Glazer systems), no
  octahedral rotation groups, no tolerance-factor refinements (Bartel's `τ`, the octahedral factor
  `μ = r_B/r_O`), no temperature/pressure dependence, no ionic-radius dependence on coordination
  number or spin state beyond the choice of the printed value used in a row.
- **No claim about measured structures.** Literature radii enter as *printed numbers with provenance*;
  the instances decide statements about those numbers, not about the materials.
- **No `sorry`, no custom `axiom`** in delivered files (enforced by `proofs/scripts/check.sh --strict`
  and `axioms.sh`).

---

## 2. Conventions and symbol table

Sign and unit convention: radii in ångström as printed by the source; a radius is an *ionic* radius
for a stated coordination number (A: 12-coordinate, B: 6-coordinate). The band edges `lo`, `hi` are
**parameters** of every statement, never hard-coded inside a definition — the classic `4/5`–`1`
convention and the tetragonal `1`–`11/10` convention are separate *instances*.

| symbol | Lean | meaning |
|---|---|---|
| `rA`, `rB`, `rO` | `rA rB rO : ℝ` | ionic radii of the A cation, the B cation and oxygen |
| `a` | `latticeOf rB rO = 2 * (rB + rO)` | cubic lattice parameter fixed by the B–O contact |
| `d_AO` | `idealAO rB rO = √2 * (rB + rO)` | ideal (cuboctahedral) A–O distance |
| `t` | `tolFac rA rB rO` | Goldschmidt tolerance factor |
| `r_A*` | `idealA rB rO = idealAO rB rO - rO` | A radius giving `t = 1` |
| `r_A^-`, `r_A^+` | `rAMin lo rB rO`, `rAMax hi rB rO` | the window edges of the band verdict |
| — | `InBand lo hi t := lo ≤ t ∧ t ≤ hi` | band predicate on the factor |
| — | `GoldschmidtConforms lo hi rA rB rO := InBand lo hi (tolFac ..)` | instance-level verdict |
| — | `GoldschmidtZone` / `goldschmidtZone lo hi t` | three-way classifier (`tooSmall`/`ideal`/`tooLarge`) |
| `τ` | `RadiusMatch τ r r' := |r - r'| ≤ τ * r` | radius rule (`τ = 3/20` is the 15 % rule) |
| `dz` | `ChargeBalanced dz := ∑ i, dz i = 0` | charge-balance rule (integer increments) |
| `χ` | `chiTol tol₀ k χ χ' = tol₀ - k * |χ - χ'|` | electronegativity-dressed radius tolerance |
| — | `Substitutable tol₀ k χ χ' r r'` | chemical rule + radius rule, composed |
| `t²` | `tolFacSq rA rB rO = (rA + rO)^2 / (2 * (rB + rO)^2)` | the `√2`-free rational decision object |
| — | `inBandQ lo hi rA rB rO` | squared band criterion on `ℚ` |

House conventions: ASCII identifiers only; parameter order "radii first, band edges next where they
appear, varying radius last"; physical premises (`0 < rB + rO`, `0 < rA + rO`, `0 ≤ lo`, `lo ≤ hi`)
are explicit hypotheses of every statement that needs them; classifier lemmas are `…_iff`
characterizations; the band-edge arguments come first in `…Conforms`/`…Zone` statements so that the
band is read as the theory-level parameter it is.

---

## 3. Statement authority and inventory

`theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean` (0 error, placeholder-only bodies)
is the authority: it declares the full declaration list, sectioned `## G1` … `## G6`. Milestone-scoped
fidelity is checked with the theory-generic checker:

```
python3 theories/BEP/probes/bep-fidelity.py --theory goldschmidt [--milestone G1|G2|G3|G4|G5|G6]
```

Auxiliary declarations in the delivered files are allowed and reported separately; a **signature
difference is a defect**.

### 3.1 Statement-correction log (the authority changes only through this log)

The authority declares **138 declarations** (Sprint 0). Three rows were corrected by hand-derivation
*before* the milestones were dispatched — every statement is spot-checked, not only the ones that
look risky (the Kasha/Hammond/BEP lesson); the Sprint-0 risk probe then re-checks them in the kernel.

1. **`radiusMatch_refl` — hypothesis added.** First draft: `RadiusMatch τ r r` under `0 ≤ τ`. FALSE
   as stated: `|r - r| = 0 ≤ τ * r` needs `0 ≤ r`, which the draft did not assume (a negative
   reference radius would flip it). Corrected row: `(htau : 0 ≤ tau) (hr : 0 ≤ r) → RadiusMatch τ r r`.
2. **`conforms_symmetric_band_iff` — hypothesis dropped.** First draft carried `0 ≤ delta`. The
   equivalence is `abs_le` applied to the window row `rAMin (1-δ) ≤ rA ≤ rAMax (1+δ)` with the two
   closed forms `idealA ∓ δ * idealAO`, which holds for **every** `δ` (at `δ > 1` the band is empty
   but the two sides of the equivalence are both false). Keeping the unused premise would have been a
   non-load-bearing hypothesis (a finding class the Sabatier verifier raised as F4), so it is removed
   rather than retained.
3. **`rAMin_le_iff_sq` / `le_rAMax_iff_sq` moved from G4 to G3.** The two per-edge squared rows are
   what `conforms_iff_sq` is proved *from*, and G4 (`Sharp.lean`) imports G3 (`Criterion.lean`) — the
   original placement would have inverted the dependency order. They now sit immediately above
   `conforms_iff_sq` in the G3 section; plan §7's table loses those two rows and §6 gains them.

4. **`goldschmidtZone_eq_tooLarge_iff` — FALSE as first drafted, corrected to the exact form
   (caught by `prover_b` in the kernel, before delivery).** The draft claimed
   `goldschmidtZone lo hi t = tooLarge ↔ hi < t`. FALSE: the classifier tests `t < lo` *first*, so on
   an inverted band (`hi < lo`) a small `t` is classified `tooSmall` even though `hi < t` holds — the
   kernel witness is `lo = 1, hi = 0, t = 1/2`. The other two rows (`…_tooSmall_iff ↔ t < lo`,
   `…_ideal_iff ↔ lo ≤ t ∧ t ≤ hi`) are true unconditionally (they are the trichotomy rows). The
   authority now carries the **exact unconditional** characterization
   `… = tooLarge ↔ lo ≤ t ∧ hi < t`, plus the degenerate form the band verdict actually uses,
   `goldschmidtZone_eq_tooLarge_iff_of_band (h : lo ≤ hi) : … = tooLarge ↔ hi < t`. This is the same
   pattern as `conforms_iff_radius_window` (exact, no band-nonemptiness premise) followed by its
   degenerate instances — the exact row is the authority, the band form is a corollary.
   `goldschmidtZone_ideal_iff_conforms` (G3) is unaffected: the *ideal* characterization is
   unconditional.

5. **`zoneQ_ideal_iff` — hypotheses dropped (same class as item 2, caught by hand before
   dispatch).** The draft carried `0 ≤ lo`, `0 ≤ hi`, `0 < rB + rO`, `0 ≤ rA + rO`. The row is a
   statement about the *squared* criterion alone (`zoneQ = ideal ↔ inBandQ`), and the three branches of
   the `ℚ` classifier are discharged by the trichotomy on `(rA+rO)^2` versus `2*lo^2*(rB+rO)^2` and
   `2*hi^2*(rB+rO)^2`; none of the four premises is used, so all four are removed rather than retained
   as non-load-bearing hypotheses. `zoneQ_eq_zone` (the transfer to the real classifier) genuinely
   needs them and keeps them.

6. **`tolFac_mono_rO_of_lt` / `tolFac_anti_rO_of_lt` — FALSE as first drafted, hypothesis replaced
   (caught by `prover_d` in the kernel, with counterexamples; before delivery).** Both drafts carried
   `(hrO : 0 < rO)`, which does **not** imply `0 < rB + rO`: the map `rO ↦ t` has a pole at
   `rO = -rB`, so it is monotone on each side of the pole but not across it. Kernel counterexamples:
   `rA = -2, rB = -1, rO = 1/2, rO' = 2` satisfies all three old premises and yet
   `t(rO') = 0 < 3/√2 = t(rO)` (the "increasing" row's conclusion fails); `rA = -1, rB = -2,
   rO = 1/2, rO' = 3` likewise refutes the "decreasing" row. Both rows now take
   `(hB : 0 < rB + rO)` — the premise the two denominators actually need — and `0 < rO` is dropped
   as non-load-bearing (item 2's discipline). The corrected rows are open on `[rO, rO')` only when
   the pole is unreachable, which is exactly what `0 < rB + rO` encodes, and their cross-multiplied
   residual `(rA - rB) * (rO - rO')` has a fixed sign.
7. **`tolFac_rO_const_iff` — FALSE as first drafted, hypothesis added.** The draft's
   `(hrO : 0 < rO)` does not make the pole unreachable in the **backward** direction: with
   `rA = rB = -1` the right side holds, while the quantified left side fails at `rO' = 2`
   (`t = 1/√2` at `rO = 1` versus `0/0 = 0` at the pole). Replacing `0 < rO` by `0 < rB + rO` is **not
   enough** (the quantifier ranges over positive `rO'` that can still hit the pole), so the delivered
   row takes `(hrB : 0 ≤ rB) (hrO : 0 < rO)`: with a nonnegative B radius every admissible `rO'`
   gives `rB + rO' > 0`, and the forward direction cancels through `rO' = rO + 1`. Both hypotheses are
   load-bearing (the backward direction needs `hrB` to keep `rA + rO' ≠ 0`).
8. **`chiTol_anti` — FALSE as first drafted, hypothesis orientation corrected (caught by `prover_c`
   in the kernel, with a counterexample).** The draft read
   `(h : |χ'' - χ| ≤ |χ' - χ|) : chiTol … χ'' ≤ chiTol … χ'`, i.e. it put the *closer* electronegativity
   on the smaller side of the conclusion while `chiTol = tol₀ - k|Δχ|` is **antitone** in `|Δχ|`
   (counterexample: `k = 1, χ = 0, χ' = 10, χ'' = 0` satisfies the draft's hypothesis and gives
   `0 ≤ -10`). The name says "antitone", so the delivered row keeps the name and fixes the direction
   of the hypothesis: `(h : |χ' - χ| ≤ |χ'' - χ|) : chiTol … χ'' ≤ chiTol … χ'` — "the nearer chemical
   character has the larger tolerance". This is also the direction `substitutable_mono_chi` consumes
   (that row was TRUE as drafted and is unchanged); its proof instantiates this row with the two
   `χ` arguments swapped, which is a one-liner.

Item 9 sits in G2, items 6–8 in G3; all four were caught by the milestone provers **before** the rows
were delivered, so no delivered declaration was ever invalidated. Process note, recorded because it
is the same failure class as items 1–5: the Sprint-0 risk probe was supposed to catch exactly these
rows before dispatch, and it did not, because the probe itself still had errors at that moment
(§1.2's honest status). The lesson is in `proofs/EXPERIENCE.md`: **a probe's "0 error" claim is an
artifact claim like any other — it must be measured after the last edit, not assumed from the
absence of a complaint.**

The instance layer's numbers were fixed by an **off-kernel exact-rational cross-check** before any
row was dispatched (see §9 and `theories/goldschmidt/probes/goldschmidt-instance-check.py`); its run
reproduced every asserted verdict with 0 mismatches, including the three rows a reader is most likely
to mis-read: `SrTiO₃` is *above* `t = 1` with Shannon radii (`t² = 161312/160801`), `BaTiO₃` sits in
`[1, 11/10]` but not in `[4/5, 1]` (`t² = 181202/160801`), and `BaNiO₃` is outside even the
tetragonal band (`t² = 90601/70688`).

---

## 4. G1 — description layer (`PhotoLean/Goldschmidt/Basic.lean`; owner lead; Sprint 0)

Definitions: `tolFac`, `latticeOf`, `idealAO`, `idealA`, `rAMin`, `rAMax`, `InBand`,
`GoldschmidtConforms`, `GoldschmidtZone` (inductive, with `DecidableEq`), `goldschmidtZone`, the band
constants `classicLo = 4/5`, `classicHi = 1`, `hiTetragonal = 11/10`, `tauGoldschmidt = 3/20`, plus
the geometric auxiliary `gapA rA rB rO = idealAO rB rO - (rA + rO)` (the A–O rattling gap).

Theorems:

| row | statement | sketch |
|---|---|---|
| `tolFac_pos` | `0 < rB + rO → 0 < tolFac rA rB rO` | needs `0 < rA + rO`; `div_pos` |
| `tolFac_eq_distRatio` | `latticeOf rB rO / √2 = idealAO rB rO` and `tolFac .. = (rA + rO) / idealAO ..` | `2/√2 = √2` (`Real.div_sqrt`); `field_simp` |
| `contact_iff_tolFac_one` | `0 < rB + rO → (rA + rO = idealAO rB rO ↔ tolFac rA rB rO = 1)` | `div_eq_one_iff_eq` |
| `idealA_eq` | `idealA rB rO = √2 * rB + (√2 - 1) * rO` | `ring` |
| `idealA_tolFac` | `0 < rB + rO → tolFac (idealA rB rO) rB rO = 1` | from `contact_iff_tolFac_one` |
| `gapA_pos_iff` | `0 < rB + rO → (0 < gapA rA rB rO ↔ tolFac rA rB rO < 1)` | affine rearrangement |
| `goldschmidtZone_eq_tooSmall_iff` / `…_ideal_iff` / `…_tooLarge_iff` | the classifier's three characterization rows — `t < lo`, `lo ≤ t ∧ t ≤ hi`, and the **exact** `lo ≤ t ∧ hi < t` (§3.1 item 4) | `if` splitting + `lt_or_ge` trichotomy |
| `goldschmidtZone_eq_tooLarge_iff_of_band` | the physically used degenerate form `lo ≤ hi → (… = tooLarge ↔ hi < t)` | from the exact row |
| `rAMin_one` / `rAMax_one` | `rAMin 1 rB rO = idealA rB rO` / `rAMax 1 rB rO = idealA rB rO` | `ring` |

## 5. G2 — rules layer (`PhotoLean/Goldschmidt/Rules.lean`; owner prover_a; Sprint 1)

Definitions: `RadiusMatch` (already G1), `chiTol`, `Substitutable`, `ChargeBalanced`, `isovalent`.

| row | statement | sketch |
|---|---|---|
| `radiusMatch_iff_window` | `RadiusMatch τ r r' ↔ (1 - τ) * r ≤ r' ∧ r' ≤ (1 + τ) * r` | `abs_le` + `linarith` |
| `radiusMatch_min_iff` | `0 ≤ τ → (RadiusMatch τ r r' ∧ RadiusMatch τ r' r ↔ |r - r'| ≤ τ * min r r')` | `min` case split |
| `radiusMatch_refl` / `radiusMatch_mono_tau` | reflexivity, monotonicity in `τ` | `abs_nonneg`, `mul_le_mul_of_nonneg_right` |
| `radiusMatch_fifteen_window` | `RadiusMatch (3/20) r r' ↔ 17 * r ≤ 20 * r' ∧ 20 * r' ≤ 23 * r` | `norm_num` arithmetic form of the window |
| `radiusMatch_comp` | `0 < r1 → 0 ≤ τ → RadiusMatch τ r1 r2 → RadiusMatch τ r2 r3 → RadiusMatch ((1+τ)^2 - 1) r1 r3` | the *ratchet*: two 15 % steps drift by more than 15 % |
| `radiusMatch_symm_iff` | `RadiusMatch τ r r' ↔ RadiusMatch τ r' r` under the *min* form (both directions) | from `radiusMatch_min_iff` |
| `chargeBalanced_single_iff` | `ChargeBalanced (fun _ : Unit => dz) ↔ dz = 0` | `Finset.sum_unit` |
| `chargeBalanced_pair_iff` | `ChargeBalanced (dz : Bool → ℤ) ↔ dz false + dz true = 0` | `Finset.sum_bool` |
| `isovalent_single` | a single-site substitution is charge-balanced iff it is isovalent | `chargeBalanced_single_iff` |
| `exists_negative_of_pos` | `∑ i, dz i = 0 → (∃ i, 0 < dz i) → ∃ j, dz j < 0` | `Finset.sum_eq_zero_iff_of_nonneg` (contrapositive) |
| `exists_compensating_partner` | `∑ i, dz i = 0 → 0 < dz i → ∃ j, j ≠ i ∧ dz j < 0` | sum over `erase i` is non-positive |
| `chiTol_anti` | `|χ'' - χ| ≤ |χ' - χ| → 0 ≤ k → chiTol tol₀ k χ χ'' ≤ chiTol tol₀ k χ χ'` | `sub_le_sub_left` |
| `substitutable_mono_chi` | the same monotonicity at the level of `Substitutable` (rule 3: closer electronegativity never loses a substitution) | from `chiTol_anti` + `radiusMatch_mono_tau` |
| `substitutable_iff_window` | `Substitutable tol₀ k χ χ' r r' ↔ (1 - chiTol ..) * r ≤ r' ∧ r' ≤ (1 + chiTol ..) * r` | `radiusMatch_iff_window` |

## 6. G3 — law layer (`PhotoLean/Goldschmidt/Criterion.lean`; owner prover_b; Sprint 1)

| row | statement | sketch |
|---|---|---|
| `tolFac_strictMono_rA` | `0 < rB + rO → rA < rA' → tolFac rA rB rO < tolFac rA' rB rO` | `div_lt_div_of_pos_right` |
| `tolFac_strictAnti_rB` | `0 < rA + rO → 0 < rB + rO → rB < rB' → tolFac rA rB' rO < tolFac rA rB rO` | `div_lt_div_of_pos_left` + monotone denominator |
| `tolFac_mono_rO_of_lt` / `tolFac_anti_rO_of_lt` | `rA < rB` (resp. `rB < rA`) → monotone (resp. antitone) in `rO` | sign of the derivative numerator `rB - rA` |
| `tolFac_rO_const_iff` | `0 < rB + rO → (∀ rO', tolFac rA rB rO' = tolFac rA rB rO) ↔ rA = rB` | two-instance argument |
| `tolFac_eq_invSqrtTwo_iff` | `0 < rB + rO → (tolFac rA rB rO = 1/√2 ↔ rA = rB)` | `div_eq_iff` + `√2·(1/√2) = 1` |
| `tolFac_scale_invariance` | `0 < c → tolFac (c*rA) (c*rB) (c*rO) = tolFac rA rB rO` | factor `c` out, cancel |
| `tolFac_ratio_form` | `0 < rO → tolFac rA rB rO = ((rA/rO) + 1) / (√2 * ((rB/rO) + 1))` | `field_simp` |
| `tolFac_shift` | `tolFac (rA + d) rB rO - tolFac rA rB rO = d / (√2 * (rB + rO))` | **exact** affine shift law |
| `tolFac_abs_shift_le` | `0 < rB + rO → |tolFac (rA + d) rB rO - tolFac rA rB rO| ≤ |d| / (√2 * (rB + rO))` | from the identity |
| `conforms_at_idealA_iff` | `0 < rB + rO → (GoldschmidtConforms lo hi (idealA rB rO) rB rO ↔ lo ≤ 1 ∧ 1 ≤ hi)` | `idealA_tolFac` |
| **`conforms_iff_radius_window`** | `0 ≤ lo → lo ≤ hi → 0 < rB + rO → (GoldschmidtConforms lo hi rA rB rO ↔ rAMin lo rB rO ≤ rA ∧ rA ≤ rAMax hi rB rO)` | **headline**: divide by the positive denominator, no squaring |
| `rAMin_le_iff_sq` | `0 ≤ lo → 0 < rB + rO → 0 ≤ rA + rO → (rAMin lo rB rO ≤ rA ↔ 2*lo^2*(rB+rO)^2 ≤ (rA+rO)^2)` | per-edge squared form (`mul_self_le_mul_self_iff` + `Real.sq_sqrt`) |
| `le_rAMax_iff_sq` | `0 ≤ hi → 0 < rB + rO → 0 ≤ rA + rO → (rA ≤ rAMax hi rB rO ↔ (rA+rO)^2 ≤ 2*hi^2*(rB+rO)^2)` | the upper edge |
| **`conforms_iff_sq`** | `0 ≤ lo → 0 ≤ hi → 0 < rB + rO → 0 ≤ rA + rO → (GoldschmidtConforms lo hi rA rB rO ↔ 2*lo^2*(rB+rO)^2 ≤ (rA+rO)^2 ∧ (rA+rO)^2 ≤ 2*hi^2*(rB+rO)^2)` | the `√2`-free form (`sq_le_sq'`) |
| `conforms_symmetric_band_iff` | `0 ≤ δ → δ < 1 → 0 < rB + rO → (GoldschmidtConforms (1-δ) (1+δ) rA rB rO ↔ |rA - idealA rB rO| ≤ δ * idealAO rB rO)` | from the window: `|·| ≤ y ↔ -y ≤ · ≤ y` |
| `conforms_classic_band_iff` | `0 < rB + rO → (GoldschmidtConforms (4/5) 1 rA rB rO ↔ (4/5) * idealAO rB rO - rO ≤ rA ∧ rA ≤ idealA rB rO)` | instantiate the window |
| `conforms_of_conforms_window_le` | `lo' ≤ lo → hi ≤ hi' → GoldschmidtConforms lo hi .. → GoldschmidtConforms lo' hi' ..` | intervals |
| `exists_conforming` / `exists_tooSmall` / `exists_tooLarge` | band-level non-vacuity (`lo ≤ hi` → ∃ rA conforming; ∃ rA below; ∃ rA above) | explicit witnesses |
| `conforms_at_idealA_classic` | `GoldschmidtConforms (4/5) 1 (idealA rB rO) rB rO` | the model's positive headline row |

## 7. G4 — sharp conditions (`PhotoLean/Goldschmidt/Sharp.lean`; owner prover_d; Sprint 2)

| row | statement | sketch |
|---|---|---|
| `conforms_iff_band_nonempty` | `hi < lo → ¬ GoldschmidtConforms lo hi rA rB rO` | `not_and_of_not_le` |
| `conforms_point_band_iff` | `0 < rB + rO → (GoldschmidtConforms lo lo rA rB rO ↔ tolFac rA rB rO = lo)` | antisymmetry |
| `not_conforms_of_lt_rAMin` / `not_conforms_of_rAMax_lt` | the two sharp failure characterizations: below the window / above the window | window equivalence |
| `witness_band_flip` | `GoldschmidtConforms classicHi tetragonalHi (161/100) (121/200) (7/5) ∧ ¬ GoldschmidtConforms classicLo classicHi (161/100) (121/200) (7/5)` | the band convention is a *parameter*: `BaTiO₃`'s two verdicts are both kernel facts |
| `tolFac_irrational` | `Irrational (Real.sqrt 2)` scaled by the rational ratio: for rational `rA rB rO` with `rB + rO ≠ 0` and `rA + rO ≠ 0`, `Irrational (tolFac rA rB rO)` | `Irrational.mul_ratCast`-type closure (API probe) |
| `tolFacFifteen_le` | `0 < rB + rO → RadiusMatch (3/20) rA rA' → |tolFac rA' rB rO - tolFac rA rB rO| ≤ (3/20) * rA / (√2 * (rB + rO))` | §6 shift + the radius window |
| `conforms_of_radiusMatch_window` | `0 < rB + rO → RadiusMatch τ rA rA' → rAMin lo rB rO ≤ (1 - τ) * rA → (1 + τ) * rA ≤ rAMax hi rB rO → GoldschmidtConforms lo hi rA' rB rO` | rule 1 ⟹ the band verdict survives the substitution |
| `witness_tooSmall` / `witness_tooLarge` / `witness_not_conforms_inverted` | explicit kernel-checked non-conformance rows | concrete numbers |

## 8. G5 — rational decision layer (`PhotoLean/Goldschmidt/RatModel.lean`; owner prover_c; Sprint 2)

Definitions: `tolFacSq`, `inBandQ`, `radiusMatchQ`, `chiTolQ`, `zoneQ` (computable classifier on `ℚ`).

| row | statement | sketch |
|---|---|---|
| `tolFacSq_cast` | `((tolFacSq rA rB rO : ℚ) : ℝ) = (tolFac ↑rA ↑rB ↑rO)^2` | cast push-through |
| `inBandQ_cast` | `inBandQ lo hi rA rB rO ↔ GoldschmidtConforms ↑lo ↑hi ↑rA ↑rB ↑rO` | from `conforms_iff_sq` (**the correctness theorem of the ℚ layer**) |
| `radiusMatchQ_cast` | `radiusMatchQ τ r r' ↔ RadiusMatch ↑τ ↑r ↑r'` | cast push-through |
| `radiusMatchQ_iff_window` | `radiusMatchQ τ r r' ↔ (1 - τ) * r ≤ r' ∧ r' ≤ (1 + τ) * r` | `radiusMatch_iff_window` + casts |
| `radiusMatchQ_fifteen` | `radiusMatchQ (3/20) r r' ↔ 17 * r ≤ 20 * r' ∧ 20 * r' ≤ 23 * r` | `norm_num` in `ℚ` |
| `zoneQ_eq_zone` | `zoneQ lo hi rA rB rO = goldschmidtZone ↑lo ↑hi (tolFac ↑rA ↑rB ↑rO)` | case analysis on the `ℚ` comparisons |
| `zoneQ_tooSmall_iff` / `…_ideal_iff` / `…_tooLarge_iff` | the computable classifier's characterization rows in `ℚ` | `zoneQ_eq_zone` + G1 |
| `chargeBalancedQ` rows | the charge rule in `ℚ`/`ℤ` (same statements, rational increments) | `chargeBalanced_single_iff` analogues |

## 9. G6 — instances & verdicts (`PhotoLean/Goldschmidt/Instances.lean`; owner prover_c; Sprint 3)

Row families (each row is a kernel-checked verdict, with the printed radii cited in the docstring):

| family | rows | content |
|---|---|---|
| I1 model | ideal-`A` row, `rA = rB` row (`t = 1/√2`), band-flip row | the model's own positives |
| I2 classic band | `SrTiO₃`, `CaTiO₃`, `LaMnO₃`, `NaNbO₃` (Shannon radii) | conformance and zone, decided in `ℚ` by `inBandQ` |
| I3 band flip | `BaTiO₃` | fails `[4/5, 1]`, conforms to `[1, 11/10]` (tetragonal) — the flip as two theorems |
| I4 negative | `BaNiO₃` (hexagonal in the literature) | outside every delivered band |
| I5 radius rule | substitution pairs inside/outside 15 %, and the ratchet row | rule 1 verdicts |
| I6 charge rule | the isovalent row, the uncompensated heterovalent row, the coupled/compensated pair (`Na⁺ + Nb⁵⁺ ↔ Ca²⁺ + Ti⁴⁺`), the compensating-partner row | rule 2 verdicts |
| I7 chemical rule | a row where a larger radius difference is admitted only by the electronegativity term | rule 3 verdicts |
| I8 non-vacuity | one conforming row per zone of the classic band | the classifier is total |

An independent, kernel-free exact-rational cross-check
(`theories/goldschmidt/probes/goldschmidt-instance-check.py`, the analogue of
`theories/BEP/probes/bep-instance-check.py`) recomputes every asserted number in `ℚ` **before** the
rows are dispatched, so a label or direction invert is caught off-kernel. Its Sprint-0 run reports
0 mismatches and fixes the exact squared values the rows decide (the comparison is on squares:
`t ≤ hi ⟺ t² ≤ hi²`, valid because `t ≥ 0`):

| compound | `rA + rO` | `rB + rO` | `t²` | verdict |
|---|---|---|---|---|
| `SrTiO₃` | `71/25` | `401/200` | `161312/160801` (`> 1`) | outside the classic band; inside `1 ± 1/50` |
| `CaTiO₃` | `137/50` | `401/200` | `150152/160801` | inside the classic band |
| `BaTiO₃` | `301/100` | `401/200` | `181202/160801` | outside the classic band; inside `[1, 11/10]` |
| `LaMnO₃` | `69/25` | `409/200` | `152352/167281` | inside the classic band |
| `NaNbO₃` | `279/100` | `51/25` | `8649/9248` | inside the classic band |
| `BaNiO₃` | `301/100` | `47/25` | `90601/70688` | outside even `[1, 11/10]` |

The `SrTiO₃` row is the honest headline of the instance layer: with Shannon's own printed radii the
archetypal cubic perovskite lands **just above** `t = 1`, so it *fails* the `0.8 ≤ t ≤ 1` band while
conforming to the symmetric `1 ± 0.02` band — a verdict that depends on the convention, delivered as
two kernel facts plus the band-monotonicity theorem of §6 rather than as prose. The radius-rule rows
are fixed the same way, including the row that makes the rule's *reference-radius* convention visible
(`Cs⁺`/`Ba²⁺`: allowed with `Cs⁺` as the reference, refused with `Ba²⁺`) — the ambiguity the
literature record flags rather than resolves.

## 10. Sprint order and owners

| sprint | milestone | file | owner |
|---|---|---|---|
| 0 | contract + skeleton + risk probe + API + literature + plan (lead), G1 | `Basic.lean` | lead |
| 1 | G2 rules, G3 law | `Rules.lean`, `Criterion.lean` | prover_a, prover_b |
| 2 | G4 sharp, G5 rational layer | `Sharp.lean`, `RatModel.lean` | prover_d, prover_c |
| 3 | G6 instances | `Instances.lean` | prover_c |
| 4 | closeout: relations node, README/AGENTS, RESULTS.md, verifier | `Relations.lean` + docs | lead |

Rationale for the order: the definitions (G1) are upstream of everything; the law layer (G3) carries
the two headline equivalences, so it is proved before anything that consumes them (G4's transfer rows,
G5's cast transfer, G6's verdicts). G2 is independent of G3 and runs beside it. The riskiest rows
(the window equivalence, the squared form, the irrationality row, the charge-compensation existence
theorem, the `ℚ` classifier transfer) are proved first — in the Sprint-0 risk probe and then in the
milestone that owns them — because early failure is cheaper.

## 11. Risks

| risk | mitigation |
|---|---|
| `√2` bookkeeping (`2/√2 = √2`, `√2 * (1/√2) = 1`, squaring) is where the algebra can go wrong | all of it is in the Sprint-0 risk probe; the squared form is proved as an equivalence, not one-sided |
| the `rO` trichotomy needs the *sign* of `rB - rA` and a non-strict variant | stated as three implication rows plus the constant row as an `↔` |
| `Irrational` closure API for `q * √2` may be missing in v4.17.0 | api_researcher calibration; fallback form recorded in the correction log |
| the charge-compensation existence theorem needs `Finset` sum APIs (`sum_eq_zero_iff_of_nonneg`) | probe first; fallback is the two-site pairing + the sign lemma |
| instance rows are decided by `norm_num` in `ℚ`; a mis-scaled decimal silently types the wrong verdict | each row's rationals are derived from the printed decimals in the docstring; the Python cross-check recomputes independently |
| a band-convention verdict may look like a defect to a reader (SrTiO₃ above 1) | the band is a *parameter*; the flip rows and the monotonicity theorem make the dependence explicit, and the docstrings state which convention is being applied |
| the `goldschmidtZone` classifier's `if`-characterization rows can be a tautology trap (S1/Hammond lesson) | only the three `…_iff` rows are delivered, each checked in the risk probe against the trichotomy |

## 12. Honesty table (premise vs theorem)

| claim | status |
|---|---|
| `t = (r_A + r_O) / (√2 (r_B + r_O))` | **definition** of the formalized object |
| `t` is the ratio of the `A`–`O` contact distance to the ideal cuboctahedral one | **theorem** (`tolFac_eq_distRatio`) given the modelling premise "ideal cubic geometry" |
| `t = 1 ⟺ r_A + r_O = √2 (r_B + r_O) ⟺ r_A = idealA rB rO` | **theorem** |
| the band `lo ≤ t ≤ hi` is the right empirical criterion | **declared modelling premise** (the band edges are parameters; the literature's several conventions are instances) |
| `GoldschmidtConforms ↔` radius window / squared form | **theorem** (this theory's own exactification; absent from the literature) |
| the 15 % radius rule | **declared rule** (`τ = 3/20`); the theorem content is its window form, its ratchet, and its transfer to `Δt` |
| the charge-balance rule | **declared rule**; the theorem content is the isovalent characterization, the pairing, and the existence of a compensating partner of opposite sign |
| the electronegativity rule | **declared shape** (`chiTol` linear in `|Δχ|`); the theorem content is monotonicity in `|Δχ|` |
| Shannon radii of a named compound | **printed number with provenance** (LITERATURE.md), not a derived quantity |
| `t` is irrational at rational radii | **theorem** (given `√2 ∉ ℚ`) |

## 13. Scope limits

No energy model, no structure prediction beyond the band verdict, no tolerance-factor refinement, no
temperature or pressure dependence, no coordination-number or spin-state modelling beyond the choice
of printed radius, no claim about any material's measured structure.

## 14. Leaves and acceptance criteria

- Theory leaves: `theories/goldschmidt/{plan.md,TASKS.md,LITERATURE.md,RESULTS.md,probes/}` — all five
  present (contract `proofs/ENGINE.yml` §multi-theory, `THEORIES` includes `goldschmidt`).
- Sources: `PhotoLean/Goldschmidt/*.lean`, namespace `PhotoLean.Goldschmidt`, registered in
  `lakefile.toml` `defaultTargets` one line per module.
- Gate per lemma: `proofs/scripts/lake build <Module>` → `proofs/scripts/check.sh --strict <Module>`
  → `proofs/scripts/axioms.sh <Module> <fully.qualified.theorem>` (only `ALLOWED_AXIOMS`) →
  commit `feat(<area>): <lemma>` with `<area>` the milestone id (`G1`…`G6`).
- Fidelity: `python3 theories/BEP/probes/bep-fidelity.py --theory goldschmidt [--milestone G<k>]`
  must report `signature differences: 0`.
- Board ticks only after an independent verifier PASS, by the lead.
