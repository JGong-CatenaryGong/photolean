# theories/FluorPhos/LITERATURE.md — literature record: fluorescence–phosphorescence competition, El-Sayed's rule as a parameter premise, and the heavy-atom direction

> Discipline (engine contract §5): every entry names a **checkable locus** (DOI / printed page) and
> a **reading status**; every entry carries the only column that matters for formalization — *what
> the source licenses as a premise, a declared approximation, or a scope limit*. Statuses:
> `verified (first-hand read here)` / `secondary` / `bibliographic-only` / `not-accessed`. Date of
> this survey: 2026-09-23.
>
> **STATEMENT-IMPACT items (read first):**
> - **None mathematical.** No plan statement (FP-B/C/R/I inventory, plan §4) contradicts a
>   verified source; the plan already declares El-Sayed's rule a parameter premise (honesty table
>   row 2), which is exactly what S1/S2 license.
> - **Two documentation flags (instance docstrings, no statement change):** the literature's
>   naphthalene landscape (S3/S5) has `kISC/kF ≈ 3–4` (ΦF ≈ 0.19–0.23, ΦT ≈ 0.75–0.8 — `secondary`
>   provenance), while FP-I1 `naphthaleneLike` uses `kISC/kF = 1`; and eosin's literature yields
>   give `kISC/kF` of order unity-to-few, while FP-I2 uses 10. Both instances are *zone-*
>   representative (fluorescence-dominant vs phosphorescence-competitive — the zones are right);
>   the docstrings must say the **rate ratios are not literature-faithful**, only the zones are.

## S1 — El-Sayed's rule at the source (record Crossref-verified; abstract first-hand)

| field | content |
|---|---|
| source | M. A. El-Sayed, "Spin–Orbit Coupling and the Radiationless Processes in Nitrogen Heterocyclics", *J. Chem. Phys.* **38**(12), 2834–2838 (1963), DOI `10.1063/1.1733610` (**Crossref-verified here**; the Crossref-deposited abstract was read first-hand in this session) |
| claim as used | To first order there is **no spin–orbit coupling between singlet and triplet states of the same configuration**; the efficient intersystem crossing in N-heterocyclics with a lowest (n,π*) singlet goes through a *different* configuration (S(n,π*)→T(π,π*)); by contrast, singlet and triplet (π,π*) states couple weakly (abstract, first-hand). This is the origin of "El-Sayed's rule": **kISC depends on the orbital character of the states involved**. |
| **formalizable implication** | (i) The rule is a theorem of *quantum chemistry* (spin–orbit matrix elements between orbital configurations) — the FluorPhos model has **no orbital structure at all**: `kISC` is a bare real parameter. El-Sayed's rule therefore enters the theory **only as a declared parameter premise** (exactly plan §9 row 2): when an instance asserts "this dye has a large `kISC`", the assertion is licensed by S1/S2 but is *asserted, never derived*. No Lean row may be phrased as deriving `kISC` from molecular structure. (ii) Nothing from this source is expressible over installed mathlib in the model's vocabulary — deliberately so; the branch rates stay free reals under `FPData` nonnegativity. |
| status | `verified (record + abstract first-hand here)`; body paywalled (AIP), not read |

## S2 — The systematization (bibliographic, Crossref-verified)

| field | content |
|---|---|
| source | M. A. El-Sayed, "Triplet state. Its radiative and nonradiative properties", *Acc. Chem. Res.* **1**(1), 8–16 (1968), DOI `10.1021/ar50001a002` (**Crossref-verified here**; 754 citing works); body not read |
| claim as used | The review that systematized the 1963 result into the general selection rule for intersystem crossing rates across (n,π*)/(π,π*) state pairs — the canonical citation for "El-Sayed's rule". |
| **formalizable implication** | Same as S1: a *parameter-premise license*, not a derivable row. It also underwrites the scope limit "no reverse ISC, no delayed fluorescence" (plan §1.2/§1.3): those are model choices, and S2's framework (higher triplets, vibronic routes) is precisely what the two-state truncation discards — the `FPData` docstring should note the truncation. |
| status | `bibliographic-only` |

## S3 — The heavy-atom effect and the triplet-yield landscape (bibliographic, Crossref-verified)

| field | content |
|---|---|
| source | S. K. Lower, M. A. El-Sayed, "The Triplet State and Molecular Electronic Processes in Organic Molecules", *Chem. Rev.* **66**(2), 199–241 (1966), DOI `10.1021/cr60240a004` (**Crossref-verified here**; body not read) |
| claim as used | The standard review of triplet-state photophysics: heavy-atom substitution (internal or external) **increases** the intersystem-crossing rate, moving the fluorescence/phosphorescence balance toward the triplet channel; it tabulates singlet–triplet yields for the aromatics (the source of the textbook landscape: naphthalene ΦF ≈ 0.2, ΦT ≈ 0.75–0.8). |
| **formalizable implication** | (i) **The heavy-atom effect is the direction of a parameter motion, not a theorem:** FP-C5 proves the balance is *monotone* in `kISC` (φF strictly antitone, φP strictly monotone); S3 licenses reading an increase of `kISC` as "heavy-atom substitution". That identification is a declared bridge (RESULTS/docstring), and the monotonicity rows stand on positivity premises only. (ii) The tabulated landscape is the zone evidence for the two documentation flags at the top: naphthalene is fluorescence-dominant with `kISC/kF ≈ 3–4` (`secondary` — the table was not read here), eosin-type dyes are phosphorescence-competitive. (iii) No premise changes: `FPData` stays nonnegativity + the two positivity fields. |
| status | `bibliographic-only`; the numeric landscape quoted from it is `secondary` (textbook-standard values; the table itself not read here) |

## S4 — Eosin: phosphorescence observable in fluid solution (bibliographic, Crossref-verified)

| field | content |
|---|---|
| source | C. A. Parker, C. G. Hatchard, "Triplet-singlet emission in fluid solutions. Phosphorescence of eosin", *Trans. Faraday Soc.* **57**, 1894–1904 (1961), DOI `10.1039/TF9615701894` (**Crossref-verified here**; 446 citing works); body paywalled (RSC), not read |
| claim as used | Eosin — a tetrabrominated fluorescein, the canonical internal-heavy-atom dye — shows observable phosphorescence **in fluid solution at room temperature**: for heavy-atom dyes the triplet branch is populated strongly enough that `φP` is a measurable competitor of `φF` (not only at 77 K). |
| **formalizable implication** | Zone evidence for FP-I2 `eosinLike` (`phosphorDominant`/`phosphorescence-competitive`): the *zone* is literature-backed; the instance's exact rates (kISC = 10, kF = 1) are representative rationals (plan §9 row 3) and must be labeled so. This is also the physical anchor of the crossover row FP-C6: the crossover `kF·(kP+kNR) < kISC·kP` is the model's closed form of "heavy-atom dyes can cross into phosphorescence dominance". No premise arises. |
| status | `bibliographic-only` |

## S5 — Naphthalene's fluorescence yield (secondary, aggregator)

| field | content |
|---|---|
| source | AAT Bioquest quantum-yield database entry "Naphthalene", `https://www.aatbio.com/resources/quantum-yield/naphthalene` (fetched here, HTTP 200): "The quantum yield (Φ) for Naphthalene is **0.23 in cyclohexane**" — an aggregator value tracing to Berlman's *Handbook of Fluorescence Spectra of Aromatic Molecules* (1971), itself `bibliographic-only` (seen as reference 44 in the IUPAC report of the QuantumYield record, S2 there) |
| claim as used | Naphthalene: ΦF ≈ 0.2 in cyclohexane — fluorescence-dominant with a substantial (majority) triplet branch (the complementary ΦT ≈ 0.75–0.8 is S3's landscape). |
| **formalizable implication** | Supports the FP-I1 zone (`fluorDominant`, φF = 2/5 ≫ φP = 2/55) and the second documentation flag (the instance's `kISC/kF = 1` is *not* the literature ratio ≈ 3–4; label the instance zone-representative only). No premise; no Lean number. |
| status | `secondary` (aggregator page read here; primary handbook not read) |

## S6 — Textbook photophysics baseline (bibliographic, Crossref-verified)

| field | content |
|---|---|
| source | J. R. Lakowicz, *Principles of Fluorescence Spectroscopy*, 3rd ed., Springer (2006), book DOI `10.1007/978-0-387-46312-4` (Crossref-verified here; chapter 1 Jablonski scheme; body not read) — the seed's "Lakowicz or Turro" baseline for naphthalene/eosin representative photophysics |
| claim as used | The two-multiplicity Jablonski scheme the model truncates to: S₁ branches {fluorescence kF, IC kIC, ISC kISC}, T₁ branches {phosphorescence kP, nonradiative kNR}; the competition law φP/φF = (kISC/kF)·(kP/(kP+kNR)) is the direct product-of-branches reading of that scheme. |
| **formalizable implication** | This is the definitional license for FP-B1..B5 and the physical reading of FP-C1/FP-C2: **the model is the textbook scheme with totalized division**, and the competition law is a *theorem of the model* (declared approximation: first-order branching, no reverse ISC, no delayed fluorescence — plan §9 row 1). Positivity premises (`0 < s1Decay`, `0 < kP + kNR`, `0 < kF`/`0 < kP` on the ratio rows) are the explicit form of "these denominators are physical rates". Nothing exceeds installed mathlib (field algebra over ℝ only). |
| status | `bibliographic-only` |

## Statement-impact summary

- **Contradictions with verified sources: none.** FP-B1..B6, FP-C1..C8, FP-R1..R2, FP-I1..I3 all
  survive the survey unchanged. (FP-C4's corrected losslessness boundary was already fixed at
  design time; no source here bears on it.)
- **Documentation flags:** (1) FP-I1 `naphthaleneLike` and FP-I2 `eosinLike` are
  **zone-representative only** — their exact rate ratios (1 and 10 for kISC/kF) are not the
  literature ratios (≈ 3–4, secondary provenance, S3/S5); say so in the instance docstrings;
  (2) El-Sayed's rule is a **declared parameter premise**, licensed by S1/S2, never a derivable
  row — this matches the plan's honesty table verbatim; (3) the heavy-atom effect enters as the
  *direction* of the `kISC` motion read onto FP-C5's monotonicity (S3).
- **Blocked:** publisher bodies of S1–S4 (AIP/ACS/RSC paywalls) — all rows graded accordingly;
  no `UNSUPPORTED` item is load-bearing.
