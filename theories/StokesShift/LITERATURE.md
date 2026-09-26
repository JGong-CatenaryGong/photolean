# theories/StokesShift/LITERATURE.md — literature record: the configuration-coordinate picture, the mirror-image rule, and the 2λ law

> Discipline (engine contract §5): every entry names a **checkable locus** (ISBN / DOI / printed
> page) and a **reading status**; every entry carries the only column that matters for
> formalization — *what the source licenses as an explicit Lean premise, a declared physical
> approximation, a scope limit, or a statement change to `theories/StokesShift/plan.md`*.
> Statuses: `verified (first-hand abstract/full text read here)` /
> `verified (catalog/Crossref bibliographic)` / `verified (reused first-hand record of Marcus)` /
> `bibliographic-only`.

## S1 — the textbook configuration-coordinate picture and the mirror-image rule (Lakowicz)

| field | content |
|---|---|
| source | J. R. Lakowicz, *Principles of Fluorescence Spectroscopy*, **3rd ed.**, Springer US, 2006; eBook ISBN 978-0-387-46312-4, DOI `10.1007/978-0-387-46312-4` [verified: NIMS Library catalog record read 2026-09-23 — author, edition, publisher, year, ISBN/DOI all match]. Locus: Chapter 1 (Introduction to Fluorescence), the Stokes-shift and mirror-image-rule sections [page-level locus **not** verified — the chapter full text is paywalled (Springer IdP redirect), so the chapter attribution is graded `bibliographic-only`]. |
| claim (as used) | Absorption and emission are vertical (Franck–Condon) transitions on a configuration-coordinate diagram; relaxation in the excited state makes emission emerge at lower energy than absorption (the Stokes shift); for similar ground/excited geometries the emission spectrum is an approximate **mirror image** of the absorption spectrum (the mirror-image rule). |
| **formalizable implication** | *Explicit Lean premises:* remarkably few — the SS-C rows are unconditional polynomial identities (`ring`-level); the physical reading needs `0 < lam` exactly where the shift's *positivity* is claimed, and SS-C4 (`0 < stokesShift lam e00 ↔ 0 < lam`) already makes this an exact iff — the literature licenses the "positive shift = physical curvature" reading, the kernel discharges the iff. *Declared approximations (never proved):* single-mode equal-curvature harmonic surfaces; vertical transitions at the two minima (`q = 0`, `q = 1`); `λ` collects *all* relaxation (inner + solvent) — plan §9 row 2. *Not expressible over installed mathlib:* band **envelopes/intensities** — the textbook mirror-image rule is a statement about spectral shapes (FC envelope progression), and this theory formalizes only band **positions** (maxima); plan §1.3 "No lineshape widths — maxima only" is exactly the right cut, and plan §10 already registers the intensity-level mirror symmetry as a look-alike (N-class) edge toward Einstein, not a theorem. |
| impact on plan statements | **None.** One wording discipline the source forces on docstrings (not on statements): every use of "mirror symmetry" in this theory must read as *mirror symmetry of the vertical transition energies* (SS-C6/C7), never of the spectra — the literature's mirror-image rule is the stronger, unformalized intensity claim. |
| status | `verified (catalog bibliographic)` for the book; `bibliographic-only` for the chapter locus |

## S2 — the configuration-coordinate diagram as the standard frame (Turro)

| field | content |
|---|---|
| source | N. J. Turro, *Modern Molecular Photochemistry*, Benjamin/Cummings Publishing Co., Menlo Park, 1978, 628 pp.; ISBN 0-8053-9354-4 (also 0-8053-9353-6) [verified: CSIR-National Chemical Library OPAC record read 2026-09-23 — author, title, publisher, place, year, extent, ISBNs all match]. Locus: the early chapters' potential-energy-curve/configuration-coordinate treatment of radiative transitions [section-level locus from the book's standard organization; page-level not verified — no full text accessed]. |
| claim (as used) | The potential-energy-curve (configuration-coordinate) diagram with vertical Franck–Condon transitions is the standard pictorial and quantitative frame for absorption/emission energies; displacement of the excited surface along the coordinate produces the Stokes shift, with the 0-0 transition common to both directions. |
| **formalizable implication** | *Explicit Lean premises:* none — the source licenses the **model definitions** themselves: `s0Surface lam q = lam * q^2`, `s1Surface lam e00 q = lam * (q-1)^2 + e00` (SS-B1/B2), verticality = evaluating both surfaces at the *same* coordinate (SS-B3/B4), `e00` as the shared 0-0 offset. The certificates `cert_s0Surface`/`cert_s1Surface` pin these to `PhotoLean.Kernel`, so the "standard frame" is a *certificate*, not an assumption. *Declared approximations:* harmonic, single-mode, equal curvatures (the unit displacement `q : 0 → 1` is the dimensionless normalization of the source's qualitative coordinate). *Not expressible:* anharmonic or multi-dimensional surfaces, Jahn–Teller-distorted minima — no such geometry layer is in scope. |
| impact on plan statements | **None.** |
| status | `verified (catalog bibliographic)`; content locus `bibliographic-only` |

## S3 — the same λ: Marcus's reorganization energy, cross-read optically (reused first-hand records)

| field | content |
|---|---|
| source | Marcus, *J. Chem. Phys.* **24**(5), 966–978 (1956), DOI `10.1063/1.1742723`; Marcus, *Annu. Rev. Phys. Chem.* **15**, 155–196 (1964), DOI `10.1146/annurev.pc.15.100164.001103`; Marcus Nobel Lecture 1992, p. 79 Eq. (6)–(8) (`λ = λ_o + λ_i`, the symmetrization approximation) [all verified first-hand in the Marcus round — local PDFs and rendered pages under `theories/Marcus/literature/`; record: `theories/Marcus/LITERATURE.md`, 2026-09-20]. |
| claim (as used) | On two equal-curvature parabolas with reorganization energy `λ`, the vertical gap at the ground minimum exceeds the 0-0 energy by `λ`, and the vertical gap at the excited minimum falls short of it by `λ` — hence the Stokes shift is exactly `2λ` and the two bands sit mirror-symmetrically about `E₀₀`. Marcus's own `λ` is the *same* quadratic-displacement constant (his Eq. (8): `λ_i = ½ Σ k_j (ΔQ_j)²` over the reduced force constants), so the optical and electron-transfer readings of λ coincide. |
| **formalizable implication** | *Explicit Lean premises:* none for SS-C1/C2/C3/C6/C7 (unconditional identities); the emission-window rows SS-C5/C8/C9 need no premises either (they are iffs/evaluations), and the *physical* reading "emission window open" is `lam < e00` — exactly the complement of the Marcus inverted region at the gap, which SS-C9 states as an `Iff` against `PhotoLean.Marcus.InvertedRegion`. *Declared approximations:* the identification `optical λ = Marcus λ` is licensed by the shared kernel certificates (SS-B1/B2 `rfl`), not assumed; the additivity `λ = λ_o + λ_i` is itself a separability approximation in the original literature (Marcus record, entry 4) — inherited here through plan §9 row 2. *Not expressible:* the derivation of λ from dielectric continuum / force-constant data (stays a parameter). |
| impact on plan statements | **None.** The cross-reading the seed asked for is already the plan's architecture (certificates to `PhotoLean.Kernel`/`PhotoLean.Marcus`); the literature confirms it is the standard reading, not a stretch. |
| status | `verified (reused first-hand record of Marcus)` |

## S4 — registered, not first-hand this round

| source | status | note |
|---|---|---|
| Lakowicz 3rd ed. Chapter 1 page-level locus | `bibliographic-only` | Springer chapter full text paywalled (IdP redirect); edition/ISBN/DOI verified via NIMS catalog (S1). |
| Per-dye experimental Stokes-shift values (any fluorescence handbook table) | `not accessed` | deliberately unused: SS-I1..I3 are **representative rational models**, not fitted dyes (plan §9 row 3); no instance row may cite a measured shift. |
| Original mirror-image-rule literature (pre-textbook) | `not accessed` | the textbook-level locus (S1/S2) suffices for the model frame; the intensity-level rule is out of scope anyway. |

## Statement-impact summary

**None** — no statement in `theories/StokesShift/plan.md` §4 contradicts any verified source. The
two textbook loci are bibliographically verified (catalog level) but their page-level content was
not read first-hand; nothing in the plan depends on page-level detail, because every SS-C row is
pure algebra over the *declared* surfaces. The one discipline the literature imposes is docstring
wording: "mirror symmetry" in this theory means the identity `(abs + em)/2 = e00` on transition
energies — never the (unformalized) spectral-envelope mirror-image rule.
