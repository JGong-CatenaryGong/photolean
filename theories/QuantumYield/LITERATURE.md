# theories/QuantumYield/LITERATURE.md — literature record: parallel-channel yields and the reference-standard values behind the instances

> Discipline (engine contract §5): every entry names a **checkable locus** (DOI / printed page /
> URL) and a **reading status**; every entry carries the only column that matters for
> formalization — *what the source licenses as a premise, a declared approximation, or a scope
> limit*. Statuses: `verified (first-hand read here)` / `verified (reused first-hand record of
> <theory>)` / `secondary` / `bibliographic-only` / `not-accessed`. Date of this survey: 2026-09-23.
>
> **STATEMENT-IMPACT items (read first): none.** No plan statement (QY-B/C/R/I inventory, plan §4)
> contradicts a verified source. The two numeric anchors the plan's instances approximate —
> fluorescein ΦF ≈ 0.9 (QY-I1 uses 9/10) and quinine ΦF ≈ 0.55 (QY-I2 uses 11/20) — are confirmed
> as *orderings* by the standards literature (S2–S4); see the honesty note in S2 about what is
> and is not first-hand about those decimals.

## S1 — The textbook branching identity and the common lifetime (bibliographic, Crossref-verified book)

| field | content |
|---|---|
| claim as used | For one excited state decaying by parallel first-order channels, the fluorescence quantum yield is `φF = kF / (kF + kIC + kISC + …)` and the observed lifetime is `τ = 1 / Σᵢ kᵢ` — one lifetime shared by all channels; yields of the radiative and nonradiative channels sum to one. |
| **formalizable implication** | (i) This is the definitional source of QY-B1..B3 (`totalRate`, `yieldOf`, `tauOf`) and the physical content of QY-C1 (Σφ = 1) and QY-C2 (`yieldOf = k·τ`): **in the model these become theorems**, because the model *defines* yield as the branch ratio — the literature licenses the definitions, the kernel discharges the algebra. (ii) Explicit premises the textbook leaves implicit: nonnegativity of every rate and positivity of the total (the plan's `QYData`); QY-C8's counterexample row (`k ≡ 0` breaks conservation under totalized division) documents why `total_pos` is load-bearing — the literature simply never writes the zero-rate corner. (iii) Declared, never proved: "parallel first-order channels, yields as time-integrated branching" (plan §9 row 1); the exponential decay itself is not modeled (plan §1.3). (iv) Nothing here exceeds installed mathlib: `Finset.univ` sums over `Fin n` and field algebra suffice. |
| status | `bibliographic-only` (book record verified; chapter not read) |

## S2 — The IUPAC standards report: which reference values are settled (record Crossref-verified; abstract first-hand; body blocked)

| field | content |
|---|---|
| source | A. M. Brouwer, "Standards for photoluminescence quantum yield measurements in solution (IUPAC Technical Report)", *Pure Appl. Chem.* **83**(12), 2213–2228 (2011), DOI `10.1351/PAC-REP-10-09-31` (**Crossref-verified here**; abstract read first-hand from the Crossref record). **Body blocked**: `publications.iupac.org` HTTP 403 (Cloudflare), `degruyterbrill.com` HTTP 202 with empty body — same obstacles as the kasha round measured. |
| claim as used | From the abstract (first-hand): "The use of standards for the measurement of photoluminescence quantum yields (QYs) in dilute solutions is reviewed. **Only three standards can be considered well established.**" The report's *recommended values* — quinine bisulfate in 0.5 M H₂SO₄, ΦF = **0.546**; fluorescein in 0.1 M NaOH, ΦF = **0.95** — are the numbers this theory's instances approximate, but the table printing them was **not read here**. Corroboration of practice: a Europe PMC full-text search on 2026-09-23 finds the string "0.546" together with "quinine sulfate" in **174** articles and "fluorescein in 0.1 M NaOH" together with "quantum yield" in **108** — i.e. the practicing literature measures relative yields against exactly these two solutions. |
| **formalizable implication** | (i) The instance values are **representative rationals, not fitted data** (plan §9 row 3): `fluoresceinS1 = ![18,1,1]` gives φF = 9/10 — consistent with the fluorescein *ordering* (ΦF ≈ 0.9–0.95, radiative channel dominant ~20:1); `quinineLike = ![11,5,4]` gives 11/20 — consistent with quinine ≈ 0.55. The docstrings must say "representative of the measured ordering", never "the recommended value". (ii) The abstract's "only three standards well established" supports the honesty stance: reference yields carry uncertainty, so no theorem may quantify over a "true" ΦF — the instances are models. (iii) The dilution practice of relative QY determination (comparing against a standard at matched absorption) is the experimental counterpart of QY-C5 (`yieldOf_div_yieldOf` — rate ratios are channel-pairwise); the theorem is algebraic, the measurement protocol is declared background. |
| status | `verified (record + abstract first-hand here)`; the two decimal values `secondary` (as recommended by the report, corroborated by the practice corpus; table not read) |

## S3 — Absolute determination of the fluorescein yield (bibliographic, Crossref-verified)

| field | content |
|---|---|
| source | D. Magde, R. Wong, P. G. Seybold, "Fluorescence Quantum Yields and Their Relation to Lifetimes of Rhodamine 6G and Fluorescein in Nine Solvents: Improved Absolute Standards for Quantum Yields", *Photochem. Photobiol.* **75**(4), 327–334 (2002), DOI `10.1562/0031-8655(2002)075<0327:FQYATR>2.0.CO;2` (**Crossref-verified here**; title and reference list read from the Crossref record; body not read) |
| claim as used | An absolute (not standard-relative) determination of the fluorescein yield and lifetime across solvents; it is one of the "several independent researchers" layers behind the IUPAC-recommended fluorescein value (S2). **Seed correction registered:** the seed's "fluorescein (ΦF ≈ 0.9 in basic ethanol/water)" — the current best value in 0.1 M NaOH is ≈ **0.95** (S2); "≈ 0.9" is the conventional textbook rounding. The plan's 9/10 sits inside this range; no conflict. |
| **formalizable implication** | Supports the QY-I1 docstring only: the radiative-dominant ordering `kF ≫ kIC + kISC` is the measured fluorescein photophysics; the exact ratio 18:1:1 is a modeling choice. Nothing becomes a premise. |
| status | `bibliographic-only` |

## S4 — The old quinine standard (bibliographic; the historical 0.55)

| field | content |
|---|---|
| source | W. H. Melhuish, "Quantum Efficiencies of Fluorescence of Organic Substances: Effect of Solvent and Concentration of the Fluorescent Solute", *J. Phys. Chem.* **65**, 229–235 (1961), DOI `10.1021/j100820a009` (Crossref record seen as reference 10 in S2's deposited reference list; body not read) |
| claim as used | The classical quinine sulfate standard: ΦF ≈ 0.55 in acidic aqueous solution — the historical basis of the "ΦF ≈ 0.55 in 0.5 M H₂SO₄" figure that S2 re-evaluated to 0.546. |
| **formalizable implication** | Same as S2(i): `quinineLike` (φF = 11/20 = 0.55) is representative of this ordering. No premise; the 0.55 ↔ 0.546 discrepancy is exactly why instances are not fitted values. |
| status | `bibliographic-only` |

## S5 — A first-hand measurement-theory locus: yields and lifetimes of standards (reused first-hand record of kasha §R1.5.3)

| field | content |
|---|---|
| source | J. B. Birks, "Fluorescence Quantum Yield Measurements", *J. Res. NBS A* **80A**(3), 389–399 (1976), DOI `10.6028/jres.080a.038`; NIST OA PDF `https://nvlpubs.nist.gov/nistpubs/jres/80A/jresv80An3p389_A1b.pdf` (fetched and read in the kasha round) |
| claim as used | Table 2 (printed p. 398): perylene in benzene, ΦF = 0.89 with τF = 4.9/4.79/5.02 ns (three laboratories) — from which kF ≈ 1.8 × 10⁸ s⁻¹ follows arithmetically (the kasha record's computation, labeled as such there). The paper's framework is exactly `Φ = k_F·τ` with `τ⁻¹ = Σk`. |
| **formalizable implication** | A first-hand, reachable demonstration that the literature's measured (Φ, τ) pairs satisfy the common-lifetime law QY-C2 (`yieldOf = k·τ`); licenses citing QY-C2 in RESULTS as "the identity the standards literature is built on". The perylene numbers themselves enter nothing. |
| status | `verified (reused first-hand record)` — Table 2 read in the kasha round; not re-read here |

## S6 — Not first-hand this round (registered, not hidden)

| source | status | note |
|---|---|---|
| Turro, Ramamurthy & Scaiano, *Modern Molecular Photochemistry of Organic Molecules* (2010) | `not-accessed` | seed's alternative textbook; no DOI, no OA copy reached; S1 covers the needed statement — do not cite until a page is read |
| Brouwer 2011 body (the recommended-values table) | `not-accessed` (403/202, see S2) | the decimals 0.546/0.95 remain `secondary`; a round-2 upgrade needs one OA full text quoting the table (174-candidate corpus identified) |
| Berlman, *Handbook of Fluorescence Spectra of Aromatic Molecules* (1971) | `bibliographic-only` | referenced inside S2's reference list (ref. 44); not needed for any row |

## Statement-impact summary

- **Contradictions with verified sources: none.** QY-B1..B4, QY-C1..C9, QY-R1..R3, QY-I1..I3
  all survive the survey unchanged.
- **Honesty notes for docstrings/RESULTS:** (1) instance yields (9/10, 11/20) are *representative
  of the measured orderings* fluorescein ≈ 0.9–0.95 and quinine ≈ 0.55 (S2–S4) — never write them
  as recommended values; (2) the recommended-value decimals 0.546 / 0.95 are `secondary` here
  (S2's table is behind a Cloudflare wall); (3) QY-C2 is the identity the measurement literature
  is built on (S5) — a good RESULTS citation; (4) the zero-total corner (QY-C8) is outside the
  physical domain the textbooks write about (S1) — the premise is honestly load-bearing, not
  pedantic.
