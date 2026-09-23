# theories/KashaVavilov/LITERATURE.md — literature record: Vavilov's rule, Kasha's rule, and the pair D2 adjudicates

> Discipline (engine contract §5): every entry names a **checkable locus** (DOI / printed page /
> repository URL) and a **reading status**; every entry carries the only column that matters for
> formalization — *what the source licenses as a premise, a declared approximation, or a scope
> limit*. Statuses: `verified (first-hand read here)` / `verified (reused first-hand record of
> <theory>)` / `secondary` (read only as quoted by a named source) / `bibliographic-only` /
> `not-accessed`. This theory reuses the delivered Kasha basis, so several rows reuse the
> first-hand records of `theories/kasha/LITERATURE.md` (round 1, 2026-09-20); those were read
> there, not re-read here.
>
> **STATEMENT-IMPACT items (read first):**
> - **None mathematical.** No plan statement (KV-B/C/I inventory, plan §4) contradicts a verified
>   source. The D2 witnesses are abstract rational ladders; the literature's documented *deviators*
>   (benzene, naphthalene, pyrene — S3) are not used as named instances, so the kasha round's
>   warning does not propagate here.
> - **One narration flag (docstring level, no statement change):** plan §1.1 writes "Vavilov's
>   rule: the fluorescence quantum yield (and, in its spectral form, the emission spectrum) is
>   independent of the excitation wavelength". The normative sources (S3, Birks 1976 p. 392) state
>   Vavilov's law for the **yield only**. The spectral form is *this theory's own* predicate
>   `SpecSame` (KV-B1); its excitation-independence theorem (KV-B7) follows from Kasha's rule
>   *inside the model*. The `SpecSame` docstring must not attribute spectral independence to
>   "Vavilov's rule".
>
> Seed-detail correction (registered, not a statement impact): the seed's "Vavilov 1922/1927" —
> the 1927 paper is verified (S1); a **1922 paper was not verified in this round** (the earlier
> paper of the documented pair is Zs. Phys. **22**, 266 (**1924**), known only via the reprint's
> editorial footnote, S1). Do not cite a 1922 Vavilov paper.

## S1 — Vavilov's own measurement: the rule, its window, and its tolerance (first-hand, reused record of kasha §R1.2.1)

| field | content |
|---|---|
| source | S. I. Vavilov, "Die Fluoreszenzausbeute von Farbstofflösungen als Funktion der Wellenlänge des anregenden Lichtes. II", *Z. Phys.* **42**, 311–318 (1927), DOI `10.1007/BF01397622` (Crossref-verified in the kasha round; author printed "Wawilow"); read via the Russian reprint, *УФН / Phys.-Uspekhi* **93**, 315–320 (1967), DOI `10.3367/UFNr.0093.196710f.0315`, PDF `https://ufn.ru/ufn67/ufn67_10/Russian/r6710f.pdf` |
| locus | reprint full text; editorial footnote: the 1927 paper continues the same-titled part I (Zs. Phys. **22**, 266 (1924)) and "in it the law that later came to be called 'Vavilov's law' is formulated" (this record's translation of the kasha round's) |
| claim as used | The fluorescence yield of dilute dye solutions is constant over a **window** of excitation wavelengths: esculin 250–405 mμ yield independent of λ; fluorescein yield constant from ~430 mμ up toward the emission maximum, **proportional to λ below ~430 mμ** (UV breakdown), then falling; the 1924 measurements held constant "to within about 8 %" over 446–519 mμ. |
| **formalizable implication** | (i) Vavilov's rule is a **windowed, approximate** empirical statement; the plan's `VavilovAt`/`VavilovUpTo` (exact equalities of `Kasha.fluoYield`) are the model's *idealization* of it — the docstrings must say "exact form of a ±tolerance empirical rule". (ii) The model has **no wavelength variable at all**: excitation enters as the ladder level index `N`, so "independent of λ_ex" becomes "independent of the excitation level" — a declared modeling identification, not a theorem about ℝ-valued wavelengths. (iii) Vavilov's printed "± 8 %" is about a dye-solution yield and must **not** be imported as any tolerance constant anywhere in this theory (KV has no `tol`; the kasha round's `tol = 1/100` warning carries over). (iv) The UV breakdown (yield ∝ λ) is a real violation *outside* the S₀→S₁ window: scope limit for reading KV rows physically. Not expressible in installed mathlib: nothing — the level-indexed ladder needs only `Finset`/field algebra. |
| status | `verified (reused first-hand record of kasha §R1.2.1)` for the reprint; `bibliographic-only` for the 1927 original (Crossref-verified, body not read); `not-accessed` for the 1924 part I |

## S2 — Kasha's rule: canonical statement and scope qualifiers (secondary quote + bibliographic)

| field | content |
|---|---|
| source | M. Kasha, "Characterization of electronic transitions in complex molecules", *Discuss. Faraday Soc.* **9**, 14–19 (1950), DOI `10.1039/df9500900014` (Crossref-verified in the kasha round; body not accessed — pubs.rsc.org is Cloudflare-403 to this environment); the canonical sentence as quoted verbatim by J. C. del Valle, J. Catalán, "Kasha's rule: a reappraisal", *Phys. Chem. Chem. Phys.* **21**(19), 10061–10069 (2019), DOI `10.1039/c9cp00739c` (abstract read first-hand via PubMed in the kasha round) |
| claim as used | "The emitting electronic level of a given multiplicity is the lowest excited level of that multiplicity" (quoted verbatim by del Valle & Catalán). Scope qualifiers (same abstract, first-hand): complex molecules, condensed phase, one photon per molecule, photostationary conditions; and "apart from azulene, the remaining [reported anomalous] molecules fulfill Kasha's rule". |
| **formalizable implication** | (i) `KashaRule rad ic N := upperYield rad ic N = 0` is the **exact** form of the rule — the model's sharpening of an empirical generalization; the D2 verdicts are statements *about the ladder model*, never about molecules. (ii) The four scope qualifiers (phase, photon count, stationarity, molecular complexity) have **no counterpart in the model** and cannot be premises: they belong in the `KashaRule`/`d2_verdict` docstrings as declared scope limits. (iii) The reappraisal's "apart from azulene" verdict is why S4's azulene numbers are the load-bearing anti-Kasha instance family. |
| status | `bibliographic-only` for Kasha 1950; `secondary (quoted by del Valle & Catalán 2019)` for the sentence; the 2019 abstract was read first-hand (kasha round), its body is closed |

## S3 — Vavilov's law with its documented deviation list (first-hand, reused record of kasha §R1.1.3/§R1.2.3)

| field | content |
|---|---|
| source | J. B. Birks, "Fluorescence Quantum Yield Measurements", *J. Res. NBS A* **80A**(3), 389–399 (1976), DOI `10.6028/jres.080a.038`; NIST OA PDF `https://nvlpubs.nist.gov/nistpubs/jres/80A/jresv80An3p389_A1b.pdf` (fetched and read in the kasha round) |
| locus | §2.5 "Vavilov's Law and Kasha's Rules", printed p. 392 |
| claim as used | Vavilov's law = "φ_FM is independent of the excitation wavelength λ_ex up to the ionization potential", with the assumption φ = 1 for IC between higher states; **major deviations documented** for benzene, toluene, p-xylene, mesitylene, fluorobenzene, naphthalene, 2-methylnaphthalene, 1,6-dimethylnaphthalene, tryptophan, tyrosine, phenylalanine (in each case φ'_FM/φ_FM = φ_MH < 1); the operational rule: "either to verify that Vavilov's law applies, or to limit the excitation to the region of the S₀→S₁ absorption spectrum". Same section states Kasha's rules in the two-multiplicity form (S₁→S₀ fluorescence, T₁→S₀ phosphorescence) and lists molecules with observed *weak* S₂→S₀ fluorescence. |
| **formalizable implication** | (i) This is the first-hand anchor for the **narration flag at the top**: Vavilov's law is yield-only; `SpecSame` (spectral agreement) is this theory's own predicate and must not be attributed to Vavilov. (ii) The deviation list licenses the **D2 framing**: the two rules are *not* universal truths, so adjudicating them as model predicates (with explicit `RateData`/`0 < ic 0` premises) is the honest formalization; `d2_verdict`'s boundary conjunct is a statement about the closed lossy regime, matching Birks' "verify or limit" practice. (iii) Birks' φ_MH (the level-resolved IC efficiency) is channel-resolved; the model's `cascade` is its aggregate — the identification is a declared modeling bridge (docstring of KV-C5). (iv) The documented deviators include benzene/naphthalene/pyrene: if any future row names a classical PAH as *conforming*, this page is the counter-evidence (none of the KV-I instances does — they are abstract rational ladders; plan §9 row 3). |
| status | `verified (reused first-hand record)` — printed p. 392 read in the kasha round; not re-read here |

## S4 — The anti-Kasha direction with numbers: azulene S₂→S₀ emission (first-hand, reused records of kasha §R1.4)

| field | content |
|---|---|
| source | (a) K. Veys, D. Escudero, "Computational Protocol To Predict Anti-Kasha Emissions: The Case of Azulene Derivatives", *J. Phys. Chem. A* **124**(36), 7228–7237 (2020), DOI `10.1021/acs.jpca.0c05205`, Table 2 (accepted manuscript, KU Leuven repository; Crossref-verified; read in the kasha round); (b) K. Tittelbach-Helmrich, PhD thesis, Univ. of Saskatchewan (1995), handle `10388/16065`, Table 3.1, printed p. 115 (PDF read in the kasha round) |
| claim as used | Azulene (cyclohexane): φ(S₂→S₀) = 3.5 ± 0.4 % (exp.) against φ(S₁→S₀) = 8.4 × 10⁻⁴ % (calc) — "fluorescence yield from S₂ is at least 1500 times larger than the yield from S₁" (Veys–Escudero, first-hand quote of the kasha record); k_r(S₂) = 2.3 ± 0.1 × 10⁷ s⁻¹ (exp.), k_IC(S₂→S₁) = 5.3 ± 1.2 × 10⁸ s⁻¹ (exp.); the thesis's independent row: Φ_f = 0.046, τ = 1330 ps, Σk_r = 3.5 × 10⁷ s⁻¹, Σk_nr = 7.2 × 10⁸ s⁻¹ (mutually consistent to ~30 %). |
| **formalizable implication** | (i) Anti-Kasha emission is **observable** — this is the physical content behind KV-C7 (`antiKasha_observable_iff`: `0 < upperYield ↔ ¬ KashaRule`): the literature confirms that a violation appears as a measurable upper-level yield, so the theorem's direction "violation ⇒ observable emission" is not vacuous physics. (ii) None of these numbers becomes a Lean premise: the KV-C1/C2/C3 and KV-I ladders are **representative rational models** (plan §9 row 3), and the kasha round's fourfold identification (ladder truncated at N = 1 for excitation into S₂; `ic 1` := k_IC(S₂→S₁); etc.) applies verbatim if an azulene-flavored docstring is ever added. (iii) Do **not** cite the `1500 ×` figure in any Lean statement; it belongs to RESULTS prose only. |
| status | `verified (reused first-hand record)` for both (a) and (b); a third consistent set (*Chem. Sci.* 2026, DOI `10.1039/d6sc00694a`, Table 3) is registered in kasha §R1.4.1(B) |

## S5 — The compound term "Kasha–Vavilov rule" (the conflation D2 adjudicates)

| field | content |
|---|---|
| source | (a) K. Veys, PhD thesis, KU Leuven (2023), OA, printed pp. 3–4 (first-hand record of kasha §R1.2.3): "Later, it was extended into the **Kasha–Vavilov rule**, stating that 'the quantum yield of luminescence is independent of the wavelength of exciting radiation'"; (b) IUPAC Gold Book, entries **K03370** ("Kasha rule") and **K03371** ("Kasha–Vavilov rule"), `goldbook.iupac.org` — body **HTTP 403 (Cloudflare)** here, same measurement as the kasha round |
| claim as used | The textbook literature runs the two rules together under one compound name; that is exactly the conflation whose **logical** content D2 decides (KV-C1..C4). |
| **formalizable implication** | The compound name is *explained*, not refuted, by the adjudication: inside the model the two predicates coincide exactly on the closed lossy regime (`kashaRule_iff_vavilovUpTo`, re-stated in KV-C4) and separate pointwise off it (KV-C1/C2) — this is the formal content of "run together in the textbooks". No premise arises; the Gold Book wording was not retrievable and is **not quoted** anywhere in this theory. |
| status | `verified (reused first-hand record)` for (a); `not-accessed (HTTP 403)` for (b) — registered, never used as a load-bearing locus |

## S6 — The counter-example-aware modern reading of Vavilov-type invariance (first-hand, reused record of kasha §R1.2.2)

| field | content |
|---|---|
| source | M. Maafi, R. G. Brown, "On photokinetics under monochromatic light", *Front. Chem.* **11**, 1233151 (2023), DOI `10.3389/fchem.2023.1233151` (OA, `PMC10538970`; read via Europe PMC in the kasha round) |
| claim as used | The Kasha–Vavilov rule "concerned fundamentally photophysical processes and has not been expanded … to photochemistry"; many systems show wavelength-dependent quantum yields; Vavilov-type invariability "needs to be proven experimentally and not assumed" (kasha record's first-hand quotes). |
| **formalizable implication** | Reinforces the scope discipline of every KV row: the theorems are **conditional on the ladder model** (`RateData` bundle); nothing in this theory may be phrased as an unconditional claim that real yields are excitation-independent. No statement change. |
| status | `verified (reused first-hand record)` |

## S7 — Not first-hand this round (registered, not hidden)

| source | status | note |
|---|---|---|
| Vavilov 1922 (the seed's date) | `not verified` | no 1922 paper located; the documented early paper is Zs. Phys. **22**, 266 (**1924**) — known only via the S1 reprint footnote (`secondary`). **Seed corrected accordingly.** |
| IUPAC Gold Book K03370 / K03371 | `not-accessed (HTTP 403)` | see S5(b); the reachable two-multiplicity locus is Birks 1976 p. 392 (S3) |
| Vavilov's original German text (1927, Zs. Phys.) | `bibliographic-only` | Crossref-verified; read through the 1967 УФН reprint (S1) |

## Statement-impact summary

- **Contradictions with verified sources: none.** Every KV row (KV-B1..B7, KV-C1..C7, KV-I1..I5)
  survives the survey unchanged.
- **Narration flags (docstring/RESULTS level):** (1) `SpecSame` is the theory's own spectral
  predicate — do not attribute spectral independence to Vavilov's law, which is yield-only (S3);
  (2) `VavilovAt`/`VavilovUpTo` are *exact* idealizations of a windowed, ±tolerance empirical rule
  (S1); (3) the compound name "Kasha–Vavilov" is the practice-side explanation of why D2 is needed
  and of why its boundary lands on the closed lossy regime (S5); (4) all physical reading is
  conditional on the ladder model (S6); (5) the KV-I ladders are representative rational models,
  not fitted data (S4).
- **Seed corrections:** Vavilov 1922 → not found; use 1924 (secondary) / 1927 (verified).
- **Blocked:** IUPAC Gold Book entries (HTTP 403) — registered, not load-bearing.
