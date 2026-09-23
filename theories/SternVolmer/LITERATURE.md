# theories/SternVolmer/LITERATURE.md — literature record: Stern–Volmer quenching, the static/dynamic ambiguity, and the D1 identifiability boundary

> Discipline (engine contract §5): every entry names a **checkable locus** (DOI / printed page /
> URL) and a **reading status**; every entry carries the only column that matters for
> formalization — *what the source licenses as a premise, a declared approximation, or a scope
> limit*. Statuses: `verified (first-hand read here)` / `secondary` (read only as quoted by a
> named source) / `bibliographic-only` / `not-accessed`. Date of this survey: 2026-09-23.
>
> **STATEMENT-IMPACT items (read first): none.** No plan statement (SV-B/C/R/I inventory, plan §4)
> contradicts a verified source. The plan's model quantifiers ("within the two-mechanism model
> space") already match the literature's scope; see the scope notes under S2/S3.
>
> **Seed correction (registered, not a statement impact):** the seed's venue for the 1919 paper,
> "Z. phys. Chem.", is **wrong** — the canonical citation is *Physikalische Zeitschrift* **20**,
> 183–188 (1919) (S1). The theory's plan never names the venue, so no statement is affected.

## S1 — The origin paper (bibliographic; venue corrected)

| field | content |
|---|---|
| claim as used | The origin of the concentration-dependent fluorescence-decay law `F₀/F = 1 + K·[Q]` for collisional quenching (the "Abklingzeit" — decay time — of the title is exactly the lifetime channel). |
| **formalizable implication** | Historical anchor only: it licenses the names `svRatioDyn`/`KSV` and the D1 narrative ("the 1919 equation is the dynamic side"). **No premise and no number enters any Lean row.** The plan's `kq`, `Ka` are free parameters (plan §9 row 3) — nothing from 1919 is load-bearing. |
| status | `bibliographic-only` (body not accessed; no DOI; venue string `secondary` via the two anchors above). **Seed venue "Z. phys. Chem." not confirmed anywhere — corrected to Phys. Z.** |

## S2 — The textbook model: both plots linear, lifetime resolves them, coexistence curves upward (bibliographic, Crossref-verified)

| field | content |
|---|---|
| claim as used | (i) Dynamic (collisional) quenching: `I₀/I = τ₀/τ = 1 + kq·τ₀·[Q]`; (ii) static quenching (ground-state complex): `I₀/I = 1 + Ka·[Q]` while the lifetime of the uncomplexed fluorophores is unchanged (`τ₀/τ = 1`); (iii) both plots are linear — **linearity does not identify the mechanism**; (iv) combined static+dynamic quenching gives the product form `I₀/I = (1 + KD·[Q])(1 + KS·[Q])`, i.e. an upward-curving plot. |
| **formalizable implication** | (i) This is the source of SV-B1..B7 *as definitions*: `dynDecay`, `svRatioDyn`, `tauRatioDyn`, `svRatioStat`, `tauRatioStat`, `svRatioBoth` are the textbook two-mechanism model — **declared, never derived**. (ii) The static model's free fraction `1/(1 + Ka·q)` is the **linearized single-site binding isotherm**: a physical approximation (1:1 complexation, weak saturation) that must stay a declared premise (plan §9 row 2), not a theorem. (iii) Explicit Lean premises the textbook leaves implicit: `0 < k0` (division by the intrinsic decay), `0 < Ka` / `0 < kq` wherever strict monotonicity or the SV-C8 boundary is claimed — the plan already carries them; the survey confirms they are the *right* premises (at `Ka = 0` static quenching is invisible, matching SV-C8's note that `0 < Ka` is load-bearing). (iv) Not expressible / out of scope: diffusion theory (the Smoluchowski derivation of `kq`), sphere-of-action static models — plan §1.3 already registers both as non-goals; nothing in installed mathlib is needed beyond field algebra on ℝ. |
| status | `bibliographic-only` (book record Crossref-verified; chapter not read); the "linearity does not discriminate" sentence `secondary` via the named thesis quote |

## S3 — The centenary review and the SV quenching map (abstract read first-hand)

| field | content |
|---|---|
| source | M. H. Gehlen, "The centenary of the Stern-Volmer equation of fluorescence quenching: From the single line plot to the SV quenching map", *J. Photochem. Photobiol. C: Photochemistry Reviews* **42**, 100338 (2020), DOI `10.1016/j.jphotochemrev.2019.100338` (**Crossref-verified here**); abstract read first-hand via the FAPESP Virtual Library record (`https://bv.fapesp.br/en/publicacao/178844/`, HTTP 200 here) |
| claim as used | The review "summarizes the assumptions behind the Stern–Volmer equation and the extensions of the theory" and moves "from the single line plot to the **SV quenching map**" — the two-axis representation in which the *intensity* ratio and the *lifetime* ratio are read together; it covers probe/quencher association, distribution and diffusion effects (abstract, first-hand). |
| **formalizable implication** | (i) The "map" is the literature's own recognition that **(I₀/I, τ₀/τ) as a pair** is the informative observable — this is exactly the plan's `LifetimeTracks` discriminator (SV-B9) and the D1b boundary (SV-C8). The theory formalizes the two-axis insight as a theorem *inside the two-mechanism model space*. (ii) **Scope discipline the docstrings must keep:** the map literature exists precisely because real systems show distributions/diffusion/association beyond the two textbook forms; SV-C8's `∀ m : Mech` quantifier is model-space-closed, and no docstring may read it as "nature has only two mechanisms". (iii) The review's "assumptions behind the equation" framing supports the plan's honesty table: intensity ∝ yield and τ = 1/decay are **declared identifications** (plan §9 row 1). No premise changes. |
| status | `verified (abstract first-hand here)`; body closed (Elsevier), not read |

## S4 — What this survey did not find / did not need

| item | status | note |
|---|---|---|
| A modern paper stating *formally* "intensity-only SV analysis is non-injective on the mechanism space" | none located | the identifiability content exists in textbook form (S2) and as the SV-map practice (S3); the **iff** formulation (SV-C8) is this theory's own sharpening — register it as such in RESULTS, not as a literature quote |
| Diffusion-based derivation of `kq` (Smoluchowski) | out of scope by plan §1.3 | would need PDE machinery absent from the model; no literature row needed |
| Sphere-of-action / exponential static models | out of scope by plan §1.3 | registered as future extension; not surveyed |

## Statement-impact summary

- **Contradictions with verified sources: none.** SV-B1..B9, SV-C1..C10, SV-R1..R3, SV-I1..I4
  all survive the survey unchanged.
- **Seed correction:** Stern & Volmer 1919 venue is *Physikalische Zeitschrift* **20**, 183–188,
  **not** "Z. phys. Chem." (S1). No plan statement carries the venue, so nothing to fix there.
- **Scope notes for docstrings/RESULTS:** (1) SV-C8's iff is *within the declared two-mechanism
  model space* — the map literature (S3) is about richer real systems; (2) the static isotherm
  `1/(1+Ka·q)` is a declared linearized-binding approximation (S2); (3) the iff *formulation* of
  the identifiability boundary is the theory's own sharpening of textbook knowledge (S4) — present
  it that way.
