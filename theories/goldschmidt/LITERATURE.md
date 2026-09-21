# theories/goldschmidt/LITERATURE.md — literature record: the Goldschmidt tolerance factor and Goldschmidt's rules

> Written by `literature_researcher` (owner of this leaf). Every entry carries: **source**
> (checkable DOI/ISBN/title), **conclusion**, and the **formalizable implication** — which
> assumptions become explicit Lean hypotheses, which are physical approximations that must be
> *declared* rather than proved, which are not expressible in the installed mathlib, and what
> impact the source has on the statements of `theories/goldschmidt/plan.md`.
> Printed numerical tables live in `theories/goldschmidt/literature/INSTANCE-DATA.md`;
> raw PDFs are kept under `theories/goldschmidt/literature/` (never pasted into context).

Status: **round 1 — retrieval record delivered** (§S1–§S6 plus §NOT and §IMPACT). Date: **2026-09-21**.

> ⭐ **Headline of the round.** The **primary text was retrieved and read**: Goldschmidt, Barth, Lunde
> & Zachariasen, *Geochemische Verteilungsgesetze der Elemente VII: Die Gesetze der Krystallochemie*,
> Skrifter … Oslo **1926, No. 2** (Frankfurt OPUS scan) — see **§S1.1b**. It settles four things the
> round otherwise could only have guessed: (i) the factor `t` **is** Goldschmidt's, printed as
> `R_A + R_X = t√2(R_B + R_X)` and named "Toleranz der Perowskitsstruktur"; (ii) his band **is**
> `0.8–1.0` (corundum below, aragonite above); (iii) the 15 % radius rule is taken **"in Prozenten des
> kleinsten Radius"** — of the *smallest* radius; (iv) his charge condition is **stoichiometric**, and
> he **explicitly folds valency into the apparent radii**, so the plan's `∑ dz = 0` is a later
> systematization rather than his criterion. §IMPACT items 7, 9, 10, 11, 12 are the consequences.

> **Evidence vocabulary** — `first-hand` (the text was retrieved in this round and the passage was
> searched locally) · `second-reader` (retrieved by a delegate of this round, quoted to me with its
> locus, **not** re-read here) · `abstract-only` · `secondary` (read only as quoted by a named
> retrieved source) · `bibliographic-only` · `not-accessed` · `unverified`.
> **No PDF of any paper is stored in this repository**; scratch is `/tmp/goldschmidt/`.
> **Citation discipline of this round**: every DOI below was resolved through
> `api.crossref.org/works/<DOI>` and the volume/page/date columns are what Crossref returned. Where
> a text was read from `arXiv` instead of the publisher, that is said explicitly. **Nothing here is a
> proof**: this record fixes *statements and premises* only; the kernel discharges proofs.
> **Shape of this record** (for a reader in a hurry): §S1 = provenance of the factor itself ·
> §S2 = the band convention (**the round's cleanest negative**) · §S3 = the three substitution rules
> plus the radius-ratio rule · §S4 = Shannon radii, one by one · §S5 = printed `t` per compound ·
> §S6 = modern refinements as scope boundaries · §NOT = **what the literature does NOT contain** —
> the claims that are this theory's own exactification — and §IMPACT = the net change this round
> forces on `theories/goldschmidt/plan.md`.

## §S0 Source index (checkable)

| id | source | DOI / locus | status | used for |
|---|---|---|---|---|
| `S2` | R. D. Shannon, *Revised effective ionic radii and systematic studies of interatomic distances in halides and chalcogenides*, Acta Cryst. A **32** (5), 751–767 (1976-09-01) | `10.1107/S0567739476001551` | **bibliographic-only** (IUCr HTTP 403; not in PMC) | the radius table's *existence and coordinate-number convention* (§S4) |
| `S3` | W. Travis, E. N. K. Glover, H. Bronstein, D. O. Scanlon, R. G. Palgrave, *On the application of the tolerance factor to inorganic and hybrid halide perovskites: a revised system*, Chem. Sci. **7**, 4548–4556 (2016) | `10.1039/c5sc04845a` (CC-BY, `PMC6016328`) | **first-hand** | the `0.8 ≤ t ≤ 1` band, the octahedral factor `μ`, the "no boundary" caveat (§S2, §S3, §S6) |
| `S4` | band sources `S4a`–`S4e` (Kim 2023; Yentekakis 2022; Vu 2023; Rogalski 2024; Lê 2023) | `10.3390/ma16186317`; `10.3390/nano12071042`; `10.1021/acs.inorgchem.3c02798`; `10.3390/ma17164029`; `10.1186/s40580-023-00395-1` | **second-reader** (delegate, full text retrieved and grepped) | the spread of printed bands and the multi-band tables (§S2) |
| `S5` | H. Muñoz, S. Korili, A. Gil, *Materials* **15**, 3288 (2022) | `10.3390/ma15093288` | **second-reader** | `0.75 ≤ t ≤ 1.0` and the `1.00–1.13` hexagonal range (§S2) |
| `S6` | M. Johnsson, P. Lemmens, *Crystallography and Chemistry of Perovskites*, in *Handbook of Magnetism and Advanced Magnetic Materials* vol. 4, Wiley (2007) | `10.1002/9780470022184.hmm411`; text read via **`arXiv:cond-mat/0506606`** | **first-hand** (the arXiv text; the Wiley record is `bibliographic-only`) | ⭐ printed `SrTiO₃ t = 1.00` and `BaNiO₃ t = 1.13` with **our exact radii**; `0.89 < t < 1`; "only a rough estimate" (§S5) |
| `S7` | C. J. Bartel, C. Sutton, B. R. Goldsmith, R. Ouyang, C. B. Musgrave, L. M. Ghiringhelli, M. Scheffler, *New tolerance factor to predict the stability of perovskite oxides and halides*, Sci. Adv. **5** (2), eaav0693 (2019-02) | `10.1126/sciadv.aav0693` (CC-BY, `PMC6368436`) | **first-hand** | the `0.825 < t < 1.059` decision-tree bound, 74 % accuracy, the `τ` refinement (§S6) |
| `S8` | A. Kumar, A. S. Verma, S. R. Bhardwaj, *Prediction of Formability in Perovskite-Type Oxides*, The Open Applied Physics Journal **1**, 11–19 (2008-12-16) | `10.2174/1874183500801010011` | **first-hand** (publisher PDF read here; Crossref record verified) | ⭐ a 173-compound printed table with `t`, `rB/rO` and structure; several bands in one paper; `r(O²⁻) = 1.35 Å` (§S1, §S2, §S3, §S4, §S5) |
| `S9` | ⭐ **PRIMARY TEXT, RETRIEVED**: V. M. Goldschmidt, T. Barth, G. Lunde & W. Zachariasen, *Geochemische Verteilungsgesetze der Elemente VII: Die Gesetze der Krystallochemie*, **Skrifter utgitt av Det Norske Videnskaps-Akademi i Oslo, I. Mat.-Naturv. Klasse 1926, No. 2**, 116 pp., Oslo: Jacob Dybwad | `https://publikationen.ub.uni-frankfurt.de/opus4/frontdoor/index/index/docId/19275`; PDF `/opus4/files/19275/E001387465.pdf`; URN `urn:nbn:de:hebis:30-1038510` | **first-hand via OCR** (delegate, multi-variant consensus; OPUS is behind an Anubis bot wall for this session — the locus and the key sentence were independently corroborated here by a web-index hit on the same PDF) | ⭐ Goldschmidt's own `t` and `R_A + R_X = t√2(R_B + R_X)`; his band `0.8–1.0`; the 15 % rule with `(in Prozenten des kleinsten Radius)`; the stoichiometric charge condition and his **refusal** to make valency a separate criterion; the `Feldwirkungen` compensation sentence; the `CaTiO₃ → Sr/Ba` isovalent example (§S1.1b–c, §S3.1–§S3.3, §NOT) |
| `S10` | C. Li, K. C. K. Soh, P. Wu, *J. Alloys Compd.* **372**, 40–48 (2004) | `10.1016/j.jallcom.2003.10.017` | **secondary** (via `S3`) | the `0.8 ≤ t ≤ 1` attribution; `S3` is the first-hand source |
| `S11` | A. M. Glazer, *The classification of tilted octahedra in perovskites*, Acta Cryst. B **28**, 3384–3392 (1972-11-15) | `10.1107/S0567740872007976` | **bibliographic-only** | the tilting notation, as an explicit non-goal (§S6) |
| `S12` | E. W. Parker & M. Fleischer, *Geochemistry of niobium and tantalum*, **U.S. Geological Survey Professional Paper 612 (1968)**, §"Isomorphous substitution", printed p. 13 | `10.3133/pp612`; PDF `pubs.usgs.gov/pp/0612/report.pdf` | **first-hand** | the three-rule statement of "Goldschmidt (1937a, 1954)" rules: the 15 % radius rule, the charge-difference rule, the higher-charge rule; Ringwood's electronegativity modification and the `Δχ ≈ 0.1` gloss (§S3.1–§S3.3) |
| `S13` | J. M. Jackson & N. V. Solomatova, *Mineral Physics 1: Earth Mineralogy and Phase Diagrams*, **CIDER 2016** short-course slides (Goldschmidt-rules slides credited to **A. Kavner**, UCLA) | `seismo.berkeley.edu/wiki_cider/images/e/eb/Jackson_CIDER_MinPhys.pdf` | **first-hand** | the `< 15 % / 15–30 % / > 30 %` three-way classification; the `\|Δz\| = 1` charge rule; the four-rule list including Ringwood's electronegativity rule; Pauling's radius-ratio table (`1.0–0.732` → 8-fold cubic; `0.732–0.414` → 6-fold octahedral) (§S1.3, §S3.1–§S3.3) |
| `S14` | Ankara University lecture notes, *İyonik yer değiştirme (Substitution) — Goldschmidt kuralları* | `acikders.ankara.edu.tr/pluginfile.php/16721/mod_resource/content/0/MKK-7.pdf` | **first-hand** | an independent-language statement of the 15 % radius rule and the `\|Δz\| = 1` charge rule, plus a printed "coupled substitution" heading (§S3.1, §S3.2) |
| `S19` | ⭐ **documented coupled-substitution examples** (E1–E3; see §S3.2.1) | `10.1002/advs.202516938` · `10.1021/acsami.5c12016` · `10.1039/d5ra07356a` | **first-hand** | the printed `A²⁺B⁴⁺O₃` charge-balance statement, the printed `3/1` compensating arithmetic, and the "self-compensating mechanism" statement (§S3.2.1) |
| `S15` | Reda, El-Dek, Arman, *J. Mater. Sci.: Mater. Electron.* **33**, 16753–16776 (2022) | `10.1007/s10854-022-08541-x` | **first-hand** | printed `BaTiO₃ t = 1.071`; `0.77 ≤ t ≤ 1.10` (§S2, §S5) |
| `S16` | Talebkeikhah, Rad, Faghani, Zokaeian, Hernádi, Melchionna, Fornasiero, Nishioka, *Beyond SrTiO₃: Emerging Perovskite Photocatalysts for Solar Water Splitting*, Materials **19** (17), 3635 (2026-08-26) | `10.3390/ma19173635` | **first-hand** | ⭐ our exact radius triple `Sr²⁺(1.44, CN 12)`, `Ti⁴⁺(0.605, CN 6)`, `O²⁻(1.40)`, "tolerance factor close to unity" (§S4, §S5) |
| `S17` | *Hidden Hydroxides in KOH-Grown BaNiO₃ Crystals: A Potential Link to Their Catalytic Behaviour* | `arXiv:2306.05488` | **first-hand** | `BaNiO₃` is a 2H hexagonal perovskite, `P6₃/mmc`, face-sharing `[NiO₆]` (§S5) |
| `S18` | band sources `S4`'s companion set (Lim 2024; Manchón-Gordón 2025; Molenda 2026; Rahmani 2022; Dey & Mehta 2022; Rout 2025; Pai & Angmo 2025; Rafiu 2026; Zhang 2023; Li 2025) | `10.1039/d3ee03638c`; `10.3390/ma18163862`; `10.1021/acs.chemrev.5c00782`; `10.1039/d2ra06478b`; `10.1016/j.soh.2022.100002`; `10.1002/smll.202503138`; `10.1002/advs.202412666`; `10.1039/d6ra00473c`; `10.3390/ma16062214`; `10.3390/ma18091937` | **second-reader** | the multi-band tables and the `t > 1` half-open motif (§S2) |

---

# §S1 — The provenance of the tolerance factor itself

### S1.1 Goldschmidt 1926 — the primary source

- **Source.** V. M. Goldschmidt, *Die Gesetze der Krystallochemie*, **Die Naturwissenschaften 14 (21),
  477–485, May 1926**, DOI `10.1007/BF01507527`. Crossref-verified first-hand: single author
  `Goldschmidt`, journal `Die Naturwissenschaften`, ISSN `0028-1042` / `1432-1904`, volume `14`,
  issue `21`, pages `477-485`, `published-print 1926-05`, type `journal-article`, copyright
- **Conclusion.** The article exists at exactly this locus and is the canonical citation for
  (`Access this article` / `Buy article`), the PDF endpoint returns the HTML paywall, and no free
  scan was reachable from this host (archive.org, HathiTrust and Wikipedia were all unreachable from
  this host). **Therefore this round does NOT claim what *this* article says.**
- **But the primary text behind it WAS reached — see `S9` below.** Its `citation_reference`
  metadata names the companion work: "V. M. Goldschmidt, *Geochemische Verteilungsgesetze der
  Elemente, VII, Die Gesetze der Krystallochemie*, nach Untersuchungen gemeinsam mit T. Barth,
  G. Lunde, W. Zachariasen". `S1` is therefore an announcement/report of the longer memoir, and the
  German noun is *Krystallochemie* (period spelling `Krystall-`), which is the string a future
  retrieval must search for.

### S1.1b ⭐ `S9` — the primary memoir, **retrieved and read**

- **Source.** V. M. Goldschmidt, T. Barth, G. Lunde & W. Zachariasen, ***Geochemische
  Verteilungsgesetze der Elemente VII: Die Gesetze der Krystallochemie***, **Skrifter utgitt av Det
  Norske Videnskaps-Akademi i Oslo, I. Mat.-Naturv. Klasse 1926, No. 2**, 116 pp., Oslo: Jacob Dybwad.
  Public domain; **full scan** (image-only, no text layer) at
  `https://publikationen.ub.uni-frankfurt.de/opus4/frontdoor/index/index/docId/19275`, PDF
  `/opus4/files/19275/E001387465.pdf`, URN `urn:nbn:de:hebis:30-1038510`.
- **Access status of this round — stated precisely.** The delegate of this round downloaded the
  scan and OCR'd it (rapidOCR, three resolutions, multi-variant consensus). **I could not re-open
  the OPUS URL myself**: the host returns a `techaro.lol` / **Anubis proof-of-work bot wall**
  (`<title>Making sure you're not a bot!</title>`) to this session's client. **Independent
  corroboration of the locus and of the key sentence was nevertheless obtained here**: a web index
  resolves the *same PDF URL* and returns from it the verbatim string
  *"worin die Größe `t` sozusagen als Toleranz der Perowskitsstruktur zu bezeichnen ist"* and the
  table rows of the same pages. So the document is real, at that URL, and contains the key phrasing —
  but the German sentences below are marked **`first-hand` via OCR** where the delegate read them and
  **`corroborated`** where this session's index query also returned them. The column values of the
  printed table are marked **OCR-variant** (see below) and must not be cited as exact.
- **Conclusion — this changes §S1.1, §S2.2, §S3.1, §S3.2 and §S3.3 materially.** Details in
  §S1.1c (§S1) and §S3.1–§S3.3 below. In one line: **the tolerance factor, its ideal form, its band
  `0.8–1.0`, the 15 % radius rule (with its reference ion), the "empirical rule" label, and a
  *stoichiometric* charge condition are all in the primary text**, and the radius rule's percentage is
  taken **of the smallest radius**.

### S1.1c What the primary text actually prints (the provenance question, answered)

- **The factor is his, and he names it.** The retrieved text contains (corroborated by this
  session's index query) *"worin die Größe `t` sozusagen als Toleranz der Perowskitsstruktur zu
  bezeichnen ist"* — "where the quantity `t` is so to speak to be designated as the tolerance of the
  perovskite structure". And the relation is printed as **`R_A + R_X = t·√2·(R_B + R_X)`**, which
  rearranged is exactly the modern `t = (R_A + R_X)/(√2 (R_B + R_X))`. **So the plan's `tolFac` is
  Goldschmidt's own object in Goldschmidt's own notation**, not merely a modern shorthand — the
  round-1 §S1.1 caution can be lifted, with the source being `S9` rather than the paywalled `S1`.
- **The band is his.** Printed verbatim (printed pp. 79–80 / scan pp. 78–79):
  *"Sinkt der Toleranzfaktor unterhalb ca. 0,8, so tritt statt der Perowskitstruktur eine Struktur
  vom Korundtypus auf … steigt der Toleranzfaktor über 1,0 so wird der Perowskitbau durch wieder
  andere Strukturtypen ersetzt … durch die Aragonitstruktur."* — below ≈ 0.8 the **corundum**
  structure type appears instead of the perovskite structure, above 1.0 the perovskite structure is
  replaced by yet other types, **through the aragonite structure**. And, printed p. 79:
  *"liegt der Toleranzfaktor … stets tiefer als 1,00, und zwar durchwegs zwischen 0,8 und 1"*.
  ⇒ **`0.8 ≤ t ≤ 1.0` is Goldschmidt's own band**, first-hand — not a modern convention.
- **His own table, and where `SrTiO₃` sits in it.** A 14-row table (CaTiO₃, SrTiO₃, BaTiO₃, KIO₃,
  RbIO₃, NaNbO₃, KNbO₃, CaZrO₃, CaSnO₃, FeMnO₃, KMgF₃, YAlO₃, LaAlO₃, LaGaO₃) prints `R_A`, `R_B`,
  `R_X`, `t` and the lattice constant. Cells reported as verified by OCR: `CaTiO₃ t = 0.86`
  (`a = 3.85`), `KNbO₃ 0.93`, `KIO₃ 0.83`, `RbIO₃ 0.88`, `NaNbO₃ 0.81`, `CaZrO₃ 0.77`,
  `CaSnO₃ 0.82`, `LaAlO₃ 0.95`. ⚠️ **`SrTiO₃`'s printed `t` is OCR-ambiguous** ("`0,9x`"); the
  delegate's recomputation from the printed radii gives `≈ 0.93`.
  ⚠️ **A numerological caution, recorded so that nobody trusts these digits.** Two OCR-reported cells
  are *not* consistent with the printed relation `R_A + R_X = t√2(R_B + R_X)` under the radii stated
  alongside them: `CaTiO₃ 0.86` with `R_A = 1.06`, `R_B = 0.64`, `R_X = 1.32` recomputes to `0.874`,
  and the `SrTiO₃ ≈ 0.93` figure does not follow from `1.27 / 0.64 / 1.32`. As the source is an
  image-only scan read by OCR, the likely explanations are a misread `R_A` digit or a
  coordination-dependent radius convention, and the record **cannot** settle which. ⇒ **Every cell of
  this table is `OCR-variant`**: usable as evidence that Goldschmidt computed `t` from **his own**
  radii and placed `SrTiO₃` **below** 1, and **not** usable as an exact number. No Lean row may be
  built on them, and a round-2 re-read of the page images should replace this paragraph with verified
  digits.
- **Formalizable implication.** The provenance question in §S1.1 is **answered**: `tolFac` is
  documented as Goldschmidt's `t`, the ideal relation as his eq. (3), and `[4/5, 1]` as his band.
  What changes in Lean: **nothing** — the plan already makes the band a parameter and `tolFac` a
  definition. What changes in the *record*: §S2.4 can now say the classic band is **first-hand
  anchored in the primary source**, not merely "best-attested". What must still be **declared**: that
  the plan's instance rows use **Shannon** radii while Goldschmidt's table uses his own — so the
  plan's `SrTiO₃` verdict (`t = 1.0016 > 1`, "too large for the classic band") is a statement about
  *Shannon radii*, while the primary text's cells (as OCR'd; see the caution above) put `SrTiO₃`
  **inside** the band.
  **This is the sharpest printed-vs-derived fact of the round and belongs in the `SrTiO₃` docstring**:
  the same compound's verdict flips with the radius compilation, which is exactly the
  convention-dependence `S6` warns about ("the `t` values also depend on what values are taken for the
  ionic radii").

### S1.2 The modern form, as printed

- **Source.** Five independent first-hand or second-reader texts print the same object:
  - `S7` (first-hand): "`t = (r_A + r_X) / (√2 (r_B + r_X))`" — its eq. (1), with `X = O²⁻, F⁻, Cl⁻,
    Br⁻, I⁻`, calling it "the Goldschmidt tolerance factor, `t` (9)";
  - `S6` (first-hand): its eq. (1) `a = 2(r_A + r_O) = 2√2 (r_B + r_O)` and eq. (2)
    `t = (r_A + r_O)/(√2 (r_B + r_O))` — the source's own typesetting renders `√2` as a bare `2`,
    so the *printed* glyph stream must be read as the standard form;
  - `S8` (first-hand): its eq. (1) `t = (r_A + r_X)/√2(r_B + r_X)`;
  - `S16` (first-hand): uses `Sr²⁺`, `Ti⁴⁺`, `O²⁻` with `r(O²⁻) = 1.40` to obtain a factor "close to
    unity";
  - `S3` (first-hand): "the Goldschmidt tolerance factor, `t`, defined as follows: … where `r_A` and
    `r_B` are the ionic radius of the A and B site cations respectively, and `r_X` is the ionic
    radius of the anion" (the displayed equation is an image in the PMC XML and was not recoverable
    as text; the surrounding prose is unambiguous).
- **Conclusion.** `t = (r_A + r_O)/(√2 (r_B + r_O))` is the modern printed form, with `r_A` the
  12-coordinate A cation, `r_B` the 6-coordinate B cation and `r_O` the anion radius. **The `ABO₃`
  case and the `ABX₃` case are the same formula with a different anion**, so the plan's `tolFac` is
  the general form, not an oxide special case. ⚠️ **Six sources misprint the formula** (missing
  `√2`, or `r_A + r_X` in the numerator with `r_A + r_X /` division-precedence damage — see `S8`'s
  neighbours in `INSTANCE-DATA.md` §T1); the *formula must be fixed by the formalization*, not read
  off the literature.
- **Formalizable implication.** What becomes an **explicit Lean premise**: nothing about the formula
  — `tolFac` is defined (plan §2, §12). What must be **declared**: (i) the geometric picture
  (`r_B + r_O = a/2` for the B–O contact and `a/√2` for the A–O distance) is a **modelling premise**,
  (`S6` prints it, which makes it *attributable*, not *derived*); (ii) the choice to use **Shannon
  radii with the coordination numbers the rows state** (`r_O = 1.40` with A = XII and B = VI) is a
  convention, because `r_O = 1.35` is printed elsewhere (`S8`). What **cannot** be expressed: no
  source's `t` is an exact rational or irrational *number* — the literature prints 2–3 decimals, so
  the plan's exact-`ℚ` decision layer is a formalization refinement, not a transcription of any
  printed digit. **Impact:** §2's convention sentence should add "every printed `t` is quoted together
  with the radius triple its source used" (see `INSTANCE-DATA.md` §T3b, last paragraph).

### S1.3 The radius-ratio rule is a *different* criterion — do not conflate

- **Source.** `S8` (first-hand): "It is well known, `rB/rX` value of octahedron `BX6` is ranging from
  **0.414 to 0.732**"; and it builds a **two-axis** structure map: "Another important octahedron
  factor (`rB/rO`) is as important as the tolerance factor to form cubic perovskites, so octahedron
  factor constructs another axe of the two-dimension structure map." `S3` (first-hand) prints the
  same object as `μ`: "several authors have utilised the octahedral factor `μ` defined as: …" with
  "perovskites forming when `μ > 0.41`" (iodides; `μ > 0.425` for oxides) and "the boundary line
  found for the iodides corresponds exactly to the geometric limit for octahedral coordination of the
  B site of `μ = 0.41`".
- **Conclusion.** `μ = r_B/r_O ≥ 0.414` is the **short-contact / octahedral** criterion, necessary
  but not sufficient; `t` is the **A-fit** criterion. They are different ratios on different ions.
  ⭐ The 8-fold `r_cation/r_anion ≥ 0.732` form the dispatch asked about **was retrieved this round**:
  `S13` prints Pauling's radius-ratio table in its own form (`1.0` → 12-fold; `1.0–0.732` → 8-fold
  cubic; `0.732–0.414` → 6-fold octahedral; `0.414–0.225` → 4-fold; `0.225–0.155` → 3-fold;
  `< 0.155` → 2-fold). Note that `S8` prints the *same* `0.414–0.732` interval as a **6-fold**
  statement about `r_B/r_X` — so the number is agreed and the **role** differs (Pauling: the 8-fold
  threshold; `S8`/`S3`: the octahedral-factor interval). See `INSTANCE-DATA.md` §T5.
- **Formalizable implication.** This is a **declared non-goal**, not a premise: plan §1.4 already
  excludes "the octahedral factor `μ = r_B/r_O`", and this record confirms that exclusion is
  *correct* rather than merely conservative, because the literature treats `μ` as an independent
  axis. **What must not happen in Lean:** the radius-window equivalence `conforms_iff_radius_window`
  must never be phrased as, or cross-referenced with, a statement about `μ`; and the value `0.732`
  must **not** be introduced as an 8-fold cations/anion threshold, because the only retrieved
  occurrence of `0.732` is `S8`'s *upper end of the 6-fold octahedral-factor interval*. **Impact on
  `plan.md`:** none of §6's statements change; §1.4's non-goal list should gain the sentence "the
  `r_cation/r_anion ≥ 0.732` radius-ratio rule is a criterion on a different ratio and is not
  formalized here" so that the boundary is *recorded*.

---

# §S2 — The band convention: the round's cleanest negative

### S2.1 The conclusion, stated once

**The literature does not use one band, and it does not even use one *kind* of object.** Across the
verified sources this round found (i) closed bands with both edges printed (`0.8 ≤ t ≤ 1.0`,
`0.75 ≤ t ≤ 1.0`, `0.9 ≤ t ≤ 1.0`, `0.89 < t < 1`, `0.825 < t < 1.059`, `0.77 ≤ t ≤ 1.10`,
`0.8 < t < 1.1`), (ii) **half-open thresholds** with no upper edge at all (`t > 1.00 → hexagonal`,
`t > 1.05 → hexagonal`, `t > 1.13 → face-sharing chains`, `t < 0.8 → non-perovskite`,
`t < 0.75 → ilmenite`), and (iii) **whole multi-band tables** that partition the line (Vu's
`t<0.97 / 0.97≤t<1 / 1≤t<1.05 / t≥1.05`; Rout's `t=1 / 0.75–0.9 / 0.9–1.0 / 1.00–1.13`). Two sources
print the **same interval with different labels**: `0.9 < t < 1.0` is **cubic** in `S18`/Lim and in
Vu, but **orthorhombic** in Rout. The full transcriptions are in `INSTANCE-DATA.md` §T1–§T1a.

### S2.2 The two named bands that are *not* attested

- **`0.8 ≤ t ≤ 1.05`** — **not found verbatim** in ~1400 retrieved full texts plus Crossref/web
  searches. Nearest printed: `0.78 < t < 1.05` (Chem. Sci. **15** 11166), `0.75 < t < 1.05`
  (Nat. Commun. **16** 8587), `0.85 < t < 1.05` (Chem. Rev. **126** 9725). Status of these three:
  **second-reader**; they are recorded so that a future round does not re-derive them, and **none of
  them may be cited as `0.8 ≤ t ≤ 1.05`**.
- **`1.0 ≤ t ≤ 1.1` as the tetragonal / ferroelectric band** — **not found as a band.** What *is*
  printed is the **half-open** motif `t > 1`, attached to *contested* names: "`t > 1` favors a
  tetragonal or hexagonal structure" (Materials **18** 1937), "a tetragonal phase may be formed if
  `t > 1.0`" (Materials **16** 2214), "orthorhombic or tetragonal phases dominate at lower
  (`0.7 < t < 0.9`) or higher (`t > 1.0`) values" (Adv. Sci. **12** 2412666) — but also
  `0.97 < t < 1.0` **tetragonal** (RSC Adv. **12** 34503) and `0.81 < t < 0.9` **tetragonal**
  (Materials **17** 4029). All **second-reader**. ⚠️ One naming collision to keep out of the record:
  two sources write the **Goldschmidt** factor as `τ` (Adv. Mater. **37** 2418620; ACS Catal. **14**
  14974), which collides with Bartel's `τ` — a Lean reader who greps `τ` in the literature will
  confuse two different objects.
- **The one place a `1.1`-type edge *is* printed as a rejection threshold** (first-hand, `S15`,
  `S18`): "If `t ≥ 1.1`, this indicates that the A site cation is too large and a perovskite
  structure is not formed" (`S15`); "as the `t`-factor exceeds `1.1`, it suggests that the A site
  cation is overly large, typically impeding the perovskite formation" (Molecules **29** 3355). Note
  these state **formation**, not **tetragonal distortion** — so even these do not license the plan's
  parenthetical.

### S2.3 The caveats that make the band a *declared approximation*

- ⭐ **`S9` (the primary text, first-hand) is itself the strongest caveat**, because it prints the
  band *and* the reasons it is approximate in the same memoir, and it labels the radius rule an
  **"empirische Regel"** (§S3.1). It also states the band's *replacement* structures rather than a
  distortion: below ≈ 0.8 → **corundum type**; above 1.0 → other types, "**durch die
  Aragonitstruktur**".
- `S6` (first-hand): "Since perovskites are not truly ionic compounds and since the `t` values also
  depend on what values are taken for the ionic radii, **the tolerance factor is only a rough
  estimate**."
- `S3` (first-hand): "**There is no boundary on the tolerance factor scale that separates perovskites
  from non-perovskites.**" and `S3`'s count: "Out of 192 compounds, 163 (85 %) were categorised
  correctly … using the tolerance factor criterion for perovskite stability `0.8 ≤ t ≤ 1`."
- `S7` (first-hand): "the optimal bounds … using the Goldschmidt tolerance factor (`t`) are
  `0.825 < t < 1.059`" with **74 %** accuracy and, in its own words, a high false-positive rate in
  that region; `S7` also warns "the stability of the perovskite structure does not increase or
  decrease monotonically with `t`".
- `S15` (first-hand) prints the band as a mere sufficient-looking condition: "However for
  `0.77 ≤ t ≤ 1.10`, the perovskite structure remains stable also [31]." — cited to a reference, i.e.
  **printed as a received rule**, not derived.
- **Formalizable implication.** The band becomes, in Lean, exactly what the plan already says: **two
  parameters `lo hi` of `GoldschmidtConforms`/`GoldschmidtZone`**, never a constant inside a
  definition. `S3`'s "no boundary" sentence and `S6`'s "rough estimate" sentence are the literature
  backing for the plan's §12 row "the band `lo ≤ t ≤ hi` is the right empirical criterion —
  **declared modelling premise**". **What cannot be expressed in the installed mathlib:** "the `t`
  values depend on what values are taken for the ionic radii" is a *meta*-statement about the choice
  of input numerals; Lean has no way to quantify over radius conventions. It must be handled
  procedurally (one convention per row, stated in the docstring) `INSTANCE-DATA.md` §T3b now makes
  that a written rule.
- **Impact on `plan.md` — concrete, three items.**
  1. **§1.1's prose must change.** It currently says "above which the structure distorts
     (tetragonal/ferroelectric, `1.0 < t < 1.1`)". The literature prints the **half-open** `t > 1`
     with contested names, and no source prints `[1.0, 1.1]` as a tetragonal band. Reword to: "above
     which the literature reports a distorted or non-cubic structure, most often as the half-open
     `t > 1`, with the distortion named tetragonal in some sources and hexagonal in others".
  2. **`hiTetragonal = 11/10` stays** — but as an explicitly *declared model parameter* whose
     §12 honesty-table row must read "a **declared** band edge chosen for the instance layer; the
     literature prints no `[1, 11/10]` band — see `LITERATURE.md` §S2.2". The constant is legitimate
     **because** the band is a parameter; the honesty table must stop implying it was printed.
  3. **§12's band row is strengthened**, not weakened: the several conventions are *instances* of one
     definition, and this round can now enumerate them (eleven printed forms, `INSTANCE-DATA.md`
     §T1). That is the evidence base for the plan's central design decision.

### S2.4 A defensible two-band default for the instance layer

For `G6`'s rows the record recommends exactly two printed bands, each traceable:
`classicLo/classicHi = 4/5, 1` — ⭐ **and this is now the strongest-attested band of the whole round,
because it is Goldschmidt's own**: `S9` (primary text, first-hand) prints *"durchwegs zwischen 0,8 und
1"* and states the corundum (`< 0.8`) and aragonite (`> 1.0`) replacements (`S3`, `S4a`, `S5`, `S18`
are additional modern attestations) — and the **tetragonal/stability upper edge** `11/10`, the latter
**declared**, with `S15`'s `t ≥ 1.1` rejection sentence (`first-hand`) as the nearest printed support
for the *number* and no printed support at all for the *name*.

⭐ **A provenance fact the plan should now record.** Goldschmidt's own table (`S9`, §S1.1c) computes
`t` from **his** radii and places `SrTiO₃` at `0,9x` (OCR-ambiguous; **below 1**) —
**inside** the band — while the plan's `SrTiO₃` row uses **Shannon** radii and lands at `1.00159`,
**outside** it. So the plan's `inst_SrTiO3_tooLarge_classic` verdict is a statement about *Shannon
radii*, and the same compound's verdict flips with the radius compilation. This is the concrete
instance of `S6`'s caveat ("the `t` values also depend on what values are taken for the ionic
radii") and of `S9` itself, and it belongs in the `SrTiO₃` docstring.

---

# §S3 — Goldschmidt's three substitution rules

> ⭐ **Superseded warning.** An earlier draft of this section said "`S1` was paywalled and `S9` was not
> reached, so no rule is quoted from Goldschmidt's own text here." **`S9` was reached** (the Frankfurt
> OPUS scan; see §S1.1b) and its rules **are** quoted below, verbatim and with printed page numbers,
> with the access caveat stated there. The primary text also **overturns** part of the plan's framing
> (see §S3.1 item 3 and §S3.2 Form 0) and **the plan's own description of this round's finding**: the
> `Na⁺ + Nb⁵⁺ ↔ Ca²⁺ + Ti⁴⁺` pair is undocumented.

*(§S3.1–§S3.3 are delivered below.)*

## S3.1 Rule (i) — the radius rule, and the **ambiguity the plan must state**

- **Source — the printed form that states the rule as a rule.** E. W. Parker & M. Fleischer,
  *Geochemistry of niobium and tantalum*, **U.S. Geological Survey Professional Paper 612 (1968)**,
  DOI `10.3133/pp612` (Crossref-verified: authors `Parker`, `Fleischer`, publisher USGS, 1968;
  the PDF is served free by `pubs.usgs.gov`), §"Isomorphous substitution", printed p. 13. **Its exact
  sentence, quoted from the retrieved PDF:**

  > "1. For two ions to be able to replace one another in a crystal structure, the ionic radii must
  > not differ by more than **15 percent**."

  The report says this is what "**Goldschmidt (1937 a, 1954) proposed**" — i.e. the attribution is
  Goldschmidt's *1937* works, not the 1926 article, and this is a `secondary` attribution in the sense
  that Parker & Fleischer are quoting him rather than my reading him. **No reference ion is named: the
  source says "must not differ by more than 15 percent" and nothing about 15 % *of what*.**
- **Source — the same rule with both variants printed side by side.** J. M. Jackson & N. V. Solomatova,
  *Mineral Physics 1: Earth Mineralogy and Phase Diagrams*, **CIDER 2016 short course** (slides,
  `seismo.berkeley.edu/wiki_cider/images/e/eb/Jackson_CIDER_MinPhys.pdf`), slides "Goldschmidt's
  Rules" (credited on the slide to **A. Kavner**, UCLA). **Printed as a three-way classification:**

  > "1. Ions of similar size can extensively substitute for each other in an ionic crystal. If size
  > difference is • **< 15 %: free substitution** • **15–30 %: limited substitution** • **> 30 %:
  > little to no substitution**"

  This is the first source retrieved that prints a **second threshold (30 %)** — useful, because it
  shows the 15 % figure is the *edge of one regime*, not a hard physical cut. Again **no reference ion
  is named**.
- **Source — an independent-language statement of the same rule.** Ankara University lecture notes,
  *İyonik yer değiştirme (Substitution) — Goldschmidt kuralları*
  (`acikders.ankara.edu.tr/pluginfile.php/16721/mod_resource/content/0/MKK-7.pdf`). Verbatim:
  "**Yarıçapları (Angström: 10⁻¹⁰ m) arasındaki fark %15'den küçük olmalı**" — "the difference between
  their radii must be smaller than 15 %". **Still no reference ion.**
- **Where 10 % and 20 % appear.** Within everything retrieved this round, the 15 % figure is the
  printed one; the **10 %** figure appears only in a *different* rule (the electronegativity threshold:
  the USGS report's "the above rule was applicable where electronegativities differed by **one-tenth**
  or more"), and the **20 %** figure was **not found** in any retrieved source. The dispatch's
  suspicion that the number varies across sources is therefore only **partly** borne out: **15 % is
  stable, and the real variability is the *reference ion*, which no source fixes.**

### The ambiguity, stated precisely — and why the *rule* is nonetheless symmetric

Write the candidate readings out. The claim "the radii differ by less than 15 %" admits at least three
interpretations for the admissible `r'` given a reference `r` — and then the primary source picks one
(see item 3 below):

| reading | predicate | admissible window in `r'` for a *larger* reference ion (`r' ≥ r`) | for a *smaller* reference ion (`r' ≤ r`) |
|---|---|---|---|
| (α) relative to the **larger** ion | `|r − r'| ≤ τ·max(r, r')` | `r' ≤ r/(1−τ)` | `r' ≥ r·(1−τ)` |
| (β) relative to the **smaller** ion ⭐ **printed by `S9`** | `|r − r'| ≤ τ·min(r, r')` | `r' ≤ r·(1+τ)` | `r' ≥ r/(1+τ)` |
| (γ) relative to the **first-listed** ion | `|r − r'| ≤ τ·r` (the plan's literal `RadiusMatch`) | `r' ≤ r·(1+τ)` if `r` is the larger | `r' ≥ r·(1−τ)` if `r` is the smaller |

**The mathematical facts that must be recorded, because they decide how the plan should state this:**

1. Readings (α) and (β) are **not equivalent**: for `τ = 3/20`, `r' ≤ r/(1−τ) = r·1.1765` versus
   `r' ≤ r·(1+τ) = r·1.15`. The 15 %-window is **asymmetric**: measured against the larger ion it
   admits a bigger absolute difference than measured against the smaller one. So the reference ion is
   a **real** semantic parameter, not a cosmetic one.
2. **However**, both are expressible as `|r − r'| ≤ τ·r` — by choosing `r` to be the ion the source
   names. `RadiusMatch τ r r'` with `r :=` the larger ion *is* reading (α); with `r :=` the smaller ion
   *is* reading (β). The delivered `radiusMatch_min_iff`
   (`RadiusMatch τ r r' ∧ RadiusMatch τ r' r ↔ |r − r'| ≤ τ * min r r'`) is exactly the **conjunction**
   of both readings, and it is *strictly stronger* than `RadiusMatch τ r r'`. This is the honest
   reading of the plan's G2 row: the conjunction is a **stricter** criterion than either single
   convention, and the kernel will report a verdict that no single printed source would.
3. ⭐ **The primary text resolves it.** The retrieved primary memoir (`S9`) prints the rule with the
   reference ion named, verbatim (printed p. 83 / scan p. 82):

   > **"Isomorphe Mischbarkeit in erheblichem Ausmaße und bei Temperaturen, welche nicht sehr nahe den
   > Schmelzkurven liegen, tritt ein, wenn die Radien der betreffenden Bausteine um nicht mehr als
   > etwa 15 % (in Prozenten des kleinsten Radius) voneinander verschieden sind."**

   — "isomorphous miscibility to a considerable extent, and at temperatures not very close to the
   melting curves, occurs when the radii of the constituents differ by **not more than about 15 %
   (in per cent of the smallest radius)**." The numeral was read as `15` in 8/8 independent OCR
   variants; the parentheses `(in Prozenten des kleinsten Radius)` are the part that matters.

   ⇒ **Total order over the three readings above:** `(β) relative to the smaller ion` is the one the
   primary source prints, i.e. **`|r − r'| ≤ (3/20) · min(r, r')`**. Reading `(γ)` (the plan's literal
   `RadiusMatch τ r r'` with an arbitrary first argument) and reading `(α)` (relative to the larger
   ion) are **both refuted as transcriptions of Goldschmidt**, though `(γ)` remains a legitimate
   *declared* parameterization. The delivered `radiusMatch_min_iff`, whose right-hand side is
   `|r − r'| ≤ τ * min r r'`, is therefore **the faithful formalization of the printed rule** — a much
   stronger statement than "one of several defensible readings".
4. **Three premises the original makes explicit and the plan should carry** (same sentence and its
   neighbourhood): (a) the comparison is made **at temperatures not very close to the melting
   curves**; (b) the memoir's discussion is restricted to the **simplest compound types** (`AX`, `AX₂`);
   (c) only **ion lattices whose ions are of analogous structure** ("Ionen analogen Baues") are
   compared. The rule is labelled an **"empirische Regel"** — an *empirical* rule, not a theorem.
5. **Consequence for the delivered row `radiusMatch_min_iff`.** Its hypothesis form is now
   literature-faithful, and its *name* is slightly misleading: it reads as "the `min` form", but the
   `min` form **is the rule**. A future round may want a docstring line saying so. Everything else
   (symmetry `radiusMatch_symm_iff`, the ratchet `radiusMatch_comp`, the window
   `radiusMatch_fifteen_window` at `17 r ≤ 20 r' ∧ 20 r' ≤ 23 r`) is this theory's own exactification
   and stays under §NOT.

- **Formalizable implication.** What becomes an **explicit Lean premise**: the three premises `(a)`,
   `(b)`, `(c)` above are **physical applicability conditions**, not arithmetic — they cannot be
  formalized as inequalities about radii, and the plan should therefore **not** try to make them
  Lean hypotheses. They belong in the docstring/honesty layer as the *domain of validity* of the
  declared rule. ⚠️ What **does** become a sharpened design decision: since the printed rule is the
  `min` form, the plan's §5 pair `radiusMatch_min_iff` / `radiusMatch_symm_iff` is the **right pair to
  lead with**, and `RadiusMatch τ r r'` with an unconstrained first argument should be documented as
  the *declared* parameterization whose `min`-conjunction is the rule. What must be **declared**: the
  rule is `empirische` (Goldschmidt's own word) — i.e. a **declared empirical rule**, which is exactly
  plan §12's status for it. What **cannot** be expressed in the installed mathlib: 15 % *of the
  smallest radius* is expressible, but "about 15 %" (the printed `etwa`) is a **fuzzy** threshold, and
  neither `ℝ` nor `ℚ` has a Lean object for "about"; the plan's sharp `τ = 3/20` is a *declared
  sharpening* of an explicitly approximate printed number, and §12 must say so. **Impact on
  `plan.md`:** (i) §2's `τ` row and §12's radius-rule row should record that the reference ion **is**
  printed by the primary source (`min`), superseding the round-1 "declared convention" framing;
  (ii) §5's `radiusMatch_min_iff` gains a literature locus in its docstring; (iii) §12 should note
  `etwa`/`about` — the 15 % is approximate in the source and sharp in the theory. **No Lean statement
  changes**; three docstrings/honesty rows are strengthened, and one round-1 recommendation is
  *withdrawn* (the reference ion is not an ambiguity to declare — it is a literature datum).

## S3.2 Rule (ii) — the charge rule, with documented coupled substitutions

⚠️ **THREE different printed statements travel under the name "the charge rule", and the primary text
prints only one of them — not the one the plan formalizes.** This is the round's most consequential
premise finding after §S3.1.

- **Form 0 — what the primary memoir (`S9`) actually says: NOT the modern compensation rule.**
  The original does **not** state "a heterovalent substitution requires a compensating partner".
  What it states is a **stoichiometric matching condition**, verbatim (printed p. 80 / scan p. 79):

  > "Vorbedingung für Isomorphie in unserem Sinne ist neben der Analogie der Bruttoformel noch die
  > Forderung, daß in beiden Formeln entsprechende Mengen positiver Bausteine und entsprechende Mengen
  > negativer Bausteine auftreten."

  ("A precondition for isomorphism in our sense is, besides the analogy of the gross formula, the
  requirement that in both formulae **corresponding amounts of positive building blocks and
  corresponding amounts of negative building blocks** occur.") And, printed p. 81, with the
  plagioclase pair as the documented coupled example: *"…wie dem Paare `NaAlSi₃O₈` und
  `CaAl₂Si₂O₈`, in welchem aber auch die wesentliche Bedingung aus unserer Definition erfüllt ist, daß
  in beiden Krystallen die Anzahl der positiven, sowohl wie die der negativen Bausteine einander
  entsprechen müssen. Letztere Bedingung für Isomorphie scheint bisher übersehn zu sein."*

  ⭐ **And — decisively for the plan — the memoir explicitly declines to make valency an independent
  criterion**, printed p. 81: *"Wir dürfen uns aber nicht wundern, daß ein Unterschied der Valenz in
  unserem Isomorphiegesetz nicht Ausdruck findet. Der Unterschied der Valenz ist nämlich bereits in
  unsern Größen der scheinbaren Radien mit einkalkuliert."* ("we must not be surprised that a
  difference of valency finds no expression in our law of isomorphism: the difference of valency is
  already **calculated into** our quantities of the apparent radii.")

  ⇒ **`ChargeBalanced dz` (`∑ dz = 0`) is a later systematization, not Goldschmidt's criterion.**
  Goldschmidt's own condition is *stoichiometric* ("corresponding amounts of positive and negative
  building blocks"), and he folds valence difference into the radii. The plan's §12 row must say this
  plainly rather than attributing `∑ dz = 0` to him.
- **Form A — the *magnitude-of-charge-difference* rule.** CIDER 2016 (slides above), verbatim:
  > "2. Ions whose charges differ by **one unit** substitute readily for one another, as long as
  > **electrical neutrality of the crystal is maintained**. If the charges differ by more than one
  > unit, substitution is generally slight. **Fe²⁺ ↔ Fe³⁺ : very common / Na⁺ ↔ Al³⁺ : extremely
  > unlikely!**"

  The Ankara notes print the same rule ("**yük farkı 1 olursa yer değiştirme gerçekleşir**; iyonların
  yük farkı > 1 ise, yer değiştirme düşük derecede olur"), and the USGS report's rule 3 gives the
  *selection* half: "**When two ions that possess similar radii but different charges compete for a
  lattice site, the ion with the higher charge is incorporated.**" **None of these three is the
  plan's `∑ dz = 0`.** Form A is a statement about `|Δz| = 1` made *conditional on* neutrality; it is
  **not** a theorem that neutrality forces a compensating partner.
- **Form B — the *charge-balance* rule, which is what the plan formalizes.** Statable in the
  comparison form:
  - `S3` (first-hand, §S3.1's source for the tolerance factor), Travis et al. 2016, states the
    requirement as "as long as … the total positive charge balances the total negative charge"
    *(the retrieved PMC text places this sentence in the site-substitution discussion; treated as
    `first-hand` prose, not as a verbatim-numbered locus)*;
  - the modern perovskite literature states it as a design constraint, and this is where the
    **documented examples** live — below.

### S3.2.1 Documented coupled-substitution examples

**Q. Do the sources document the plan's `Na⁺ + Nb⁵⁺ ↔ Ca²⁺ + Ti⁴⁺` pair?**
**A. No.** No retrieved source — and not the primary memoir — prints that pair. The primary memoir's
documented coupled example is instead **the plagioclase pair `NaAlSi₃O₈` / `CaAl₂Si₂O₈`**
(`S9`, printed p. 81, quoted above), i.e. `Na⁺ + Si⁴⁺ ↔ Ca²⁺ + Al³⁺` in a framework silicate — a
`(+1,+4) ↔ (+2,+3)` swap, **not** an oxide perovskite and **not** the `NaNbO₃`/`CaTiO₃` pair. That
pair, or `A²⁺+B⁴⁺ ↔ A³⁺+B³⁺`, **is** documented in the modern perovskite literature, and so are
`(+1)`-for-`(+2)` swaps in oxides. Four `first-hand` examples, in increasing explicitness:

| # | printed example, verbatim | source | status |
|---|---|---|---|
| **E1** | "The introduction of **La** and **Na** as **heterovalent** ions into the perovskite also satisfies the **charge balance**, as represented by **A²⁺B⁴⁺O₃**." | Li, Zhao, Fan, Li, Tan, Wang et al., *Rational A-Site Entropy Engineering in Perovskites: Dual-Exchange Enhanced Magnetoelectric Coupling*, **Adv. Sci. 13**, e16938 (2025-10-17), DOI `10.1002/advs.202516938` (`PMC12766988`) | **first-hand** |
| **E2** | "half of Sm was designed to partially substitute Bi, and the other half of Sm to partially replace Na. The specific amounts of Bi and Na replaced were determined based on **the charge balance condition**. … in BNTS0.5, the amount of Sm³⁺ is 0.0054 moles. Since half of Sm³⁺ replaces Bi³⁺, the amount of the latter after doping is given by 0.5 – 0.0027 = 0.4973 moles. Instead, the amount of Na⁺ is given by **0.5 – 0.0027 × 3/1 = 0.4919 moles**." | Tang, Hu, Koval, Zeng et al., *Effect of Samarium Doping on the Energy Storage Properties of Bismuth Sodium Titanate-Based Lead-Free Ceramics*, **ACS Appl. Mater. Interfaces 17**, 53780–53790 (2025-09-10), DOI `10.1021/acsami.5c12016` (`PMC12464909`) | **first-hand** |
| **E3** | "Ni²⁺ substitutes for Pb²⁺ at the B-site and Pr³⁺ for Cs⁺ at the A-site, **keeping charge balance**." / "The **self-compensating mechanism** of Ni²⁺/Pr³⁺ codoping (**Ni²⁺ ↔ Pb²⁺, Pr³⁺ ↔ Cs⁺**) maintains overall **charge neutrality** by complementing itself. The total cationic charge … remains +4 per unit cell." | *Dynamical stability and multifunctional properties of Ni²⁺/Pr³⁺ co-doped CsPbCl₃*, **RSC Adv. 15** (2025), DOI `10.1039/d5ra07356a` (`PMC12757862`) — a **halide** perovskite | **first-hand** |

**Which pair the sources actually document, and with what increments:**

- **E1** documents the `(A²⁺) ↔ (A³⁺ + A⁺)` structure in an **oxide** perovskite: `La³⁺` on the A
  site gives `Δz = +1` against the host `A²⁺`, and `Na⁺` on the A site gives `Δz = −1`; the equal
  proportions cancel. ⭐ **This is the closest documented analogue of the plan's charge-increment
  structure in an oxide perovskite** — and note it is a **`+1`-for-`+2` paired with `+3`-for-`+2`**
  swap (an `A²⁺+A²⁺ ↔ A³⁺+A⁺` pairing), whereas the plan's example `Na⁺ + Nb⁵⁺ ↔ Ca²⁺ + Ti⁴⁺` is a
  **cross-site** `(+1,+5) ↔ (+2,+4)` pairing. Both are `∑ dz = 0`; they are **not the same pair**, and
  the plan's specific pair remains **undocumented**. E1 also does **not** print the two increments —
  it prints the host formula `A²⁺B⁴⁺O₃` and the conclusion that charge balance holds, so the site
  assignment above is a **reading of the source, not a printed statement**.
- **E2** is the cleanest for `ChargeBalanced` because it prints the arithmetic: `Sm³⁺` replaces
  `Bi³⁺` (isovalent, 1:1) **and** `Na⁺` at the printed ratio `3/1` — i.e. **three `Na⁺` per one
  `Sm³⁺`**, which is the compensating-partner arithmetic of the plan's `exists_compensating_partner`
  in explicit numerical form (`−0.0027 × 3/1`). It is an oxide perovskite
  (`Bi₀.₅Na₀.₅TiO₃`-based) and the substitution is deliberately **split** between an isovalent and a
  heterovalent partner — exactly the plan's two-site pairing (`chargeBalanced_pair_iff`), with the
  heterovalent half being again a **`+1`-for`+3`** swap (`3 Na⁺ ↔ 1 Sm³⁺`).
- **E3** is the complementary `(Δz = +2) + (Δz = 0)` case in a **halide**: `Pr³⁺ ↔ Cs⁺` paired with the
  isovalent `Ni²⁺ ↔ Pb²⁺`, i.e. a **single** heterovalent substitution made charge-balanced by an
  isovalent partner on the other site. It explicitly names the "**self-compensating mechanism**" and
  states an invariant ("the total cationic charge … remains `+4` per unit cell") — a printed
  instance of `∑ dz = 0` in the *formula-unit* reading.
- ⭐ **The primary memoir's own documented coupled example** (`S9`, printed p. 81, quoted in §S3.2
  Form 0) is **`NaAlSi₃O₈` / `CaAl₂Si₂O₈`** — the plagioclase pair, a `(+1,+4) ↔ (+2,+3)` swap in a
  framework silicate. It is **not** a perovskite and **not** an oxide, but it is the example the
  *primary source* uses for the charge condition, and its increments are the plan's
  `A²⁺+B⁴⁺ ↔ A³⁺+B³⁺` **structure** with the roles of A and B swapped between the two sublattices.

- **Formalizable implication.** What becomes an **explicit Lean premise**: `ChargeBalanced dz :=
  ∑ i, dz i = 0` is a **declared rule** — and after reading the primary text, that phrase must be
  taken seriously: **Goldschmidt's own condition is stoichiometric matching of positive and negative
  building blocks, and he explicitly folds valence difference into the radii** (`S9`, printed p. 81,
  quoted above). So `∑ dz = 0` is a **later systematization**, and the plan must not docstring it as
  "Goldschmidt's rule". What the primary source *does* license is the **existence of a balancing
  condition**; what it does **not** license is the arithmetic form `∑ dz = 0` or the existence
  theorem `exists_compensating_partner`. ⚠️ **The plan's premise "the substitution set is the right
  set"** (which sites participate) is the modelling choice, and it is invisible in the math: for
  `Unit` the theorem is trivial (`chargeBalanced_single_iff`), for `Bool` it is the pairing
  (`chargeBalanced_pair_iff`). What **cannot** be expressed in the installed mathlib: "corresponding
  amounts of positive and negative building blocks" is a statement about **formula units** (a
  stoichiometric bookkeeping object), and Lean has no type for a chemical formula; the plan reduces
  it to a finite sum of integer increments over an *abstract* index type, and the correspondence
  between that index set and real lattice sites is a **declared** modelling step expressible only in
  prose. **Impact on `plan.md`:** §5's rows (`chargeBalanced_single_iff`, `chargeBalanced_pair_iff`,
  `isovalent_single`, `exists_negative_of_pos`, `exists_compensating_partner`) require **no statement
  change**; but (i) §9's row family I6 should cite **E1** for the `A²⁺ ↔ (A³⁺, A⁺)` oxide structure,
  **E2** for the printed `3/1` compensating arithmetic, and the plagioclase pair for the primary
  locus, and should **mark the specific pair `Na⁺ + Nb⁵⁺ ↔ Ca²⁺ + Ti⁴⁺` as undocumented** (or replace
  it with E1's pair, which *is* documented); (ii) §12's charge-rule row must be rewritten from
  "**declared rule**" to "**declared rule, and NOT Goldschmidt's own criterion** — the primary text
  (`S9`, p. 80–81) states a stoichiometric matching condition and explicitly folds valency into the
  apparent radii; `∑ dz = 0` is a later systematization; the literature also prints a `|Δz| = 1`
  variant (§S3.2 Form A)" — **this is the §S3 finding that most changes the plan's honesty table.**

## S3.3 Rule (iii) — the chemical rule is **qualitative**, and the primary text calls it *field effects*, not electronegativity

- ⭐ **Source — the primary analogue (`S9`, printed pp. 82–83 / scan pp. 81–82), verbatim:**
  > "Diese Gleichheit der Wirkungen braucht … durchaus nicht dadurch bedingt zu sein, daß beide
  > Partikel, der ursprüngliche und der ersetzende, gleichen Radius und gleiche elektrische
  > Feldwirkungen aufweisen, sondern es können und werden Unterschiede der Radien durch Unterschiede
  > der Feldwirkungen kompensiert."

  — "this equality of effects need by no means be conditioned on both particles, the original and the
  replacing one, having the **same radius and the same electric field effects**; rather, differences
  of the radii *can be and are* **compensated by differences of the field effects**."
  ⇒ ⭐ **This is the plan's `chiTol` idea in Goldschmidt's own words**: a radius mismatch can be
  offset by a difference in the other property. **But his currency is `Feldwirkungen`
  (field effects / polarizability), *not* electronegativity** — the electronegativity wording is a
  **modern rephrasing** (Ringwood 1955 via the USGS report; CIDER 2016). The plan's `χ` should
  therefore be documented as "the modern electronegativity surrogate for Goldschmidt's
  `Feldwirkungen`", not as his own quantity.
- **Source — the modern *preference* form.** USGS Professional Paper 612 (1968), p. 13, describing
  **Ringwood's 1955 modification** of Goldschmidt's rules, verbatim:
  > "Ringwood noted that Goldschmidt's rules did not always apply, and suggested that these rules do
  > not adequately consider the partial covalent bonding that coexists with ionic bonding in most
  > lattices. To allow for the partial covalent bonding, Ringwood utilised the property of
  > electronegativity (Pauling, 1940) and thus formulated the following rule (Ringwood, 1955a,
  > p. 193): **Whenever diadochy in a crystal is possible between two elements possessing appreciably
  > different electronegativities, the element with the lower electronegativity will be preferentially
  > incorporated because it forms a stronger and more ionic bond than the other.**"

  and the quantitative gloss: "Ringwood found that the Goldschmidt rules commonly applied where
  electronegativities were nearly the same, but the above rule was applicable where **electronegativities
  differed by one-tenth or more**."
- **Source — the same rule as a *tolerance* statement.** CIDER 2016, verbatim:
  > "4. Substitutions may be limited, even when the size and charge criteria are satisfied, when the
  > competing ions have different electronegativities and form bonds of different ionic character.
  > For example, **Na⁺ and Cu⁺ have the same radius and charge, but do not substitute for one
  > another**."
- **Conclusion.** The rule is printed **everywhere as prose** — as a *compensation* statement
  (`S9`: radius differences are compensated by field-effect differences), as a *preference* rule
  (USGS/Ringwood: the lower-electronegativity ion wins), or as a *limitation* rule (CIDER:
  substitution may be limited despite size and charge being satisfied). The **only** number attached
  to it anywhere retrieved is the `Δχ ≳ 0.1` threshold of Ringwood as reported by the USGS report.
  `S8` (first-hand) confirms the tradition's use of the descriptor: "the factors they used were the
  difference of electronegativity […]" in a two-dimensional formability map. **No source retrieved
  proposes a functional form.**
- ⭐ **A printed isovalent A-site example in a perovskite** (`S9`, printed p. 91 / scan p. 90):
  *"Beispielsweise können wir im `CaTiO₃` das `Ca` durch `Sr` oder `Ba` ersetzen, unter Beibehaltung
  des Strukturtypus"* — "for example, in `CaTiO₃` we can replace the `Ca` by `Sr` or `Ba`, preserving
  the structure type"; and *"wir können sogar, durch geeignete Wahl der Substituenten, alle Atomarten
  des Perowskits gleichzeitig substituieren … wie das Beispiel `KMgF₃` zeigt"*. This is a `first-hand`
  printed statement about **isovalent A-site substitution in a perovskite** — useful as the positive
  instance of the radius rule (Ca²⁺ → Sr²⁺ → Ba²⁺ at the A site), and it is *the primary source*, so
  §9's row family I5 can cite it.
- **Formalizable implication.** This is the clearest "declared shape" of the three rules. What becomes
  an **explicit Lean premise**: nothing — `Substitutable tol₀ k χ χ' r r'` is a definition, and the
  theorem content is **monotonicity in `|Δχ|`** (`chiTol_anti`, `substitutable_mono_chi`), which is a
  fact about the *declared* linear shape, not a literature claim. What must be **declared rather than
  proved**: that the rule's effect on the admissible radius window is **linear** in `|Δχ|`. After
  reading the primary text, the record can say precisely how much the literature supports:
  (i) **monotone compensation in the right direction** — `S9`'s "differences of the radii are
  compensated by differences of the field effects" is *literally* the plan's monotonicity claim;
  (ii) the **preference direction** and the `Δχ ≈ 0.1` **threshold** (USGS/Ringwood); (iii)
  **nothing about linearity**. ⚠️ So `chiTol tol₀ k χ χ' = tol₀ − k|χ − χ'|` is an **extrapolation**:
  the linear shape is *consistent* with `S9`'s compensation sentence and with (i)–(ii), and is not
  printed anywhere; the threshold reading (ii) would instead suggest a **step-ish** shape. What
  **cannot** be expressed in the installed mathlib: `Feldwirkungen` / electronegativity is not a
  physical quantity with a Lean type — `χ` is an abstract real the theory supplies, and "the closer
  the electronegativities, the larger the tolerated radius difference" is expressible only as the
  declared `chiTol` monotonicity. **Impact on `plan.md`:** §2's `chiTol` row and §12's "declared shape
  (linear in `|Δχ|`)" row are **correct as written**; this round's contribution is (i) the **primary
  locus** `S9` pp. 82–83 for the compensation sentence, which makes "declared shape" *checkable* and
  shows the plan's *monotonicity* theorem is literature-backed even though the linear shape is not;
  (ii) the note that Goldschmidt's quantity is `Feldwirkungen`, so §2's `χ` row should say "the modern
  electronegativity surrogate"; (iii) §12 should read "declared shape (**linearity not attested in any
  retrieved source**; the primary text states only compensation, and the modern sources a monotone
  direction plus a `Δχ ≈ 0.1` threshold)". **No Lean statement changes.**


---

# §S4 — Shannon's ionic radii: what is confirmed and what is not

### S4.1 The primary record

- **Source.** R. D. Shannon, *Revised effective ionic radii and systematic studies of interatomic
  distances in halides and chalcogenides*, Acta Crystallographica Section A **32** (5), 751–767,
  1976-09-01, DOI `10.1107/S0567739476001551`. **Crossref-verified first-hand**: single author
  `Shannon`, ISSN `0567-7394`. The full text is **not reachable from this host** (IUCr's
  `journals.iucr.org/a/issues/1976/05/00/a12967/a12967.pdf` and its `scripts.iucr.org` mirror both
  return HTTP 403; the paper is not in PMC and no open-access copy was found).
- **Conclusion.** The compilation exists at that locus and is the standard source of *effective*
  ionic radii as a function of **coordination number and spin state** — that structure is the whole
  point of the paper and is what makes "A = XII, B = VI, `r(O²⁻) = 1.40 Å`" a *convention* rather
  than a fact about ions. **The four-decimal values themselves were not read from this PDF in this
  round.**
- **Formalizable implication.** The plan's choice "radii in ångström as printed by the source; a
  radius is an *ionic* radius for a stated coordination number (A: 12-coordinate, B: 6-coordinate)"
  (plan §2) is a **convention that must be carried by every instance row**, and — crucially — the
  coordination number and spin state are **not Lean variables**: there is no `r(Sr²⁺, CN=12)` in the
  theory, only a literal `36/25`. That is the honest formalization of "a printed number with
  provenance" (plan §12) and it is why the plan's §1.4 non-goal "no ionic-radius dependence on
  coordination number or spin state beyond the choice of the printed value used in a row" is exactly
  right. **Cannot be expressed in mathlib:** the coordination-number *function*
  `r : Ion → CN → ℝ` with Shannon's table as data would require either a huge finite table or an
  axiom; both are out of scope, and the plan correctly excludes them.
- **Mismatch flagged:** none. But the *spin state* of `Mn³⁺` matters: the plan's rows use
  `Mn³⁺(VI, high spin) = 0.645`. `S6` (first-hand) notes in the same chapter that "the different
  ionic radii of the spin states also couple the electronic …" properties — i.e. the literature
  treats high-spin and low-spin `Mn³⁺` as **different radii**, so the docstring of the `LaMnO₃` row
  must name the spin state or the number is not well-defined.

### S4.2 The ten radii, one by one

The per-radius evidence table is `INSTANCE-DATA.md` §T2. Summary:

| verdict | radii |
|---|---|
| **confirmed** against ≥ 1 retrieved first-hand source | `Sr²⁺(XII) = 1.44` · `Ti⁴⁺(VI) = 0.605` · `O²⁻ = 1.40` · `Ba²⁺(XII) = 1.61` · `Ni⁴⁺(VI) = 0.48` · `Ca²⁺(XII) = 1.34` · `La³⁺(XII) = 1.36` · `Na⁺(XII) = 1.39` · `Nb⁵⁺(VI) = 0.64` |
| **unverified** this round | `Mn³⁺(VI, high spin) = 0.645` |

Three sources independently print the **exact triple** `Sr²⁺ 1.44` / `Ti⁴⁺ 0.605` / `O²⁻ 1.40` —
`S6` (first-hand; with `SrTiO₃ t = 1.00`), `S16` (first-hand; with the CNs spelled out) — and `S6`
additionally prints `Ba²⁺ 1.61` / `Ni⁴⁺ 0.48` on the same page. **No value differs from the plan's.**

⚠️ **The `r_O` convention is not universal and this is the round's sharpest numerical caution.**
`S8` (first-hand) states: "The ionic radius of `rA`, `rB` and `rX` (X = O⁻² **is 1.35 Å**)", and its
whole 173-row table is computed with that. The effect is not small: for `SrTiO₃`,
`t(1.35) = 1.0091` versus `t(1.40) = 1.0016`. Every "printed vs derived" gap in
`INSTANCE-DATA.md` §T3b is explained by this alone — **including `S15`'s whole `BaTi₁₋ₓZrₓO₃`
series, which reproduces to all four printed values with `rO = 1.35`.**

---

# §S5 — Literature-reported `t` values as a cross-check

Full transcription: `INSTANCE-DATA.md` §T3. The six rows, with the literature's own verdict:

| compound | printed `t` | printed by | structure the source assigns | our exact `t²` (same radii as the plan) | kernel band verdict, classic `[4/5,1]` |
|---|---|---|---|---|---|
| **SrTiO₃** | ⭐ **`0,9x`** (≈ `0.93`) / **`1.00`** / `1.009` | **`S9`** (Goldschmidt's **own radii** `1.27/0.64/1.32`) / **`S6`** (`rO=1.40`, our radii) / `S8` (`rO=1.35`) | **cubic**, "the ideal cubic perovskite"; `S8` marks it `F` (cubic perovskite forms) | `161312/160801`, `t = 1.00159…` | **fails** (`t > 1`) with Shannon radii — **holds** (`0,9x`) with Goldschmidt's |
| CaTiO₃ | `0.973` | `S8` | `S8` marks it `NF` (no cubic perovskite); `S6` calls it "the mineral perovskite itself … orthorhombic" | `150152/160801`, `0.96632…` | holds |
| BaTiO₃ | `1.071` · `1.071` | `S8` · `S15` | `S15`: "tetragonal phase"; `S8` marks it `NF` | `181202/160801`, `1.06154…` | **fails** |
| LaMnO₃ | `0.961` | `S8` | `S8` marks it `NF` | `152352/167281`, `0.95433…` | holds |
| NaNbO₃ | `0.974` | `S8` | `S8` marks it `NF` | `8649/9248`, `0.96707…` | holds |
| **BaNiO₃** | **`1.13`** | **`S6`** (twice, printed text and Figure 2b caption), with `rA = 1.61`, `rB = 0.48`, `rO = 1.40` | **hexagonal** variants, face-sharing `[NiO₆]`; `S17` calls it "an ideal 2H hexagonal perovskite … space group `P6₃/mmc`" | `90601/70688`, `1.13212…` | **fails** |

### S5.1 SrTiO₃ — the printed discrepancy, recorded honestly

This is the row the dispatch asks about, and the answer is clean **once the radius convention is
attached**:

- The plan's `t² = 161312/160801` (`t = 1.00159`) is **exactly** what `S6`'s and `S16`'s radius
  triple gives. `S6` prints `t = 1.00` and `S16` writes "a Goldschmidt tolerance factor close to
  unity": **both rounded to two decimals.** The unrounded value is *above* 1 — the plan's row
  `inst_SrTiO3_tooLarge_classic` (`¬ inBandQ 4/5 1 1.44 0.605 1.40`) is therefore **correct and
  not in conflict with the literature**.
- `S8` prints `1.009` for the same compound — and I recomputed `S8`'s own convention
  (`rO = 1.35`) and got `1.0091`. So `S8`'s number is **internally exact, not a misprint**; it is a
  *different radius convention*, not a disagreement about `t`.
- The plan's `inst_SrTiO3_conforms_symmetric` uses `1 ± 1/50` (`δ = 0.02 > 0.00159`) and **holds**.
  A narrower symmetric band would fail — which is itself a good sign that the delivered rows are not
  vacuously chosen.
- ⭐ **The primary text closes the loop** (`S9`, §S1.1c): Goldschmidt's own table computes `t` from
  **his** radii (`R_A = 1.27`, `R_B = 0.64`, `R_X = 1.32` as OCR'd) and places `SrTiO₃` at `0,9x`
  (OCR-ambiguous, but **below 1**) — i.e. **inside** his own `[0.8, 1]` band. Moving to Shannon radii
  (`1.44`, `0.605`, `1.40`) pushes `SrTiO₃` **above** 1. So the same compound is "in" or "out" of the
  same band depending purely on the radius compilation, and `S9`'s own numbers make the effect
  visible. This is the sharpest single illustration of `S6`'s caveat and it must appear in the
  docstring.
- **Formalizable implication.** Nothing new becomes a premise; what becomes required is a
  **docstring obligation** with three literature loci: `t = 1.00` (`S6`, same radii, two-decimal
  rounding); `t = 1.009` (`S8`, `rO = 1.35`); `t = 0,9x` (`S9`, Goldschmidt's own radii). With our
  radii the exact value is `1.00159 > 1`, so the classic upper edge is exceeded — **and the
  literature does not contradict this, it simply used different radii.** Without that sentence a
  reader (or a verifier) will read the delivered `tooLarge` verdict as a defect.**Impact on
  `plan.md`:** §9's row family I2 and §11's risk row "a band-convention verdict may look like a
  defect to a reader (SrTiO₃ above 1)" can now cite three literature loci instead of merely asserting
  the parameter design.

### S5.2 BaNiO₃ — the negative row, confirmed by the literature's own number

`S6` prints, twice, "The `t` value for `BaNiO₃` is `1.13` (`rA = 1.61 Å` and `rB = 0.48 Å`)" — with
precisely the radii the plan's row uses — and assigns it to **hexagonal variants** with face-sharing
octahedra. Our exact value is `1.13212 → 1.13`: the literature's number and the kernel's number are
the same to the printed precision. `S17` confirms the structure independently (`2H` hexagonal,
`P6₃/mmc`). Therefore:
- `inst_BaNiO3_not_tetragonal` (`¬ inBandQ 1 11/10 1.61 0.48 1.40`) is **confirmed**, and by
  `0.032` of margin — not a marginal negative;
- the plan's characterisation of `BaNiO₃` as "the literature's own hexagonal assignment" is
  **attributable to a specific sentence in `S6`**, which the docstring should cite.

### S5.3 Rows where the theory and the literature *do* part company — declared, not reconciled

`S8`'s `NF` marks for `CaTiO₃`, `BaTiO₃`, `LaMnO₃`, `NaNbO₃` mean "this compound does **not** form a
cubic perovskite", and the plan's classic-band verdicts are `holds / fails / holds / holds`. These
are **not** contradictions of the kind that matter, because the two statements are different:
- `GoldschmidtConforms 4/5 1 …` in Lean says "the radius triple satisfies the band" — an arithmetic
  statement about printed numbers;
- `NF` in `S8` says "the compound does not crystallize cubic at room temperature and 1 atm" — a
  statement about a material.
`CaTiO₃` is the clearest case: it **satisfies** the classic band (`t = 0.966`) yet is orthorhombic
(it is the mineral *perovskite* itself, and `S6` says so). So "in the band" must never be docstringed
as "cubic in nature". **Impact on `plan.md`:** §1.4's "No claim about measured structures.
Literature radii enter as printed numbers with provenance; the instances decide statements about
those numbers, not about the materials" already says exactly this — the record's contribution is the
**evidence** that the distinction is not pedantic: `S8`'s own `F/NF` column would otherwise look like
a set of counterexamples to the delivered rows.

---

# §S6 — Modern refinements, as scope boundaries (not as machinery)

Each of these gets one line on what it is and one line on why this theory does **not** formalize it.
The point is that the boundary is *recorded*, not silently omitted — the plan's §1.4 already lists
them as non-goals, and this section supplies the citation and the reason.

| refinement | what it is | why not formalized here |
|---|---|---|
| **Bartel's `τ`** (`S7`, first-hand) | "We developed an accurate, physically interpretable, and one-dimensional tolerance factor, `τ`, that correctly predicts 92 % of compounds … for an experimental dataset of 576 `ABX₃` materials … using … SISSO"; `τ < 4.18` is its band, and `S7`'s own comparison is `t`-band `0.825 < t < 1.059` (74 %) versus `τ` | It is a **fitted 1-D descriptor depending on oxidation states and both the A–B and B–X radius ratios**; formalizing it would require the fitting data and the `ε`-form, and `S7` itself says `t`'s deficiency "arises from its functional form and not the input features". The theory formalizes `t`; `τ` is a declared non-goal (plan §1.4). **Also a naming hazard:** several later papers call the Goldschmidt factor `τ` (Adv. Mater. **37** 2418620; ACS Catal. **14** 14974, second-reader) — keep `τ` for Bartel only |
| **Travis's revised system** (`S3`, first-hand) | A revised cation-radius system for inorganic **and hybrid** halide perovskites, with a `t`–`μ` structure map, `μ > 0.41`, and boundary lines `t = 0.875` / `t ≤ 1.06`; `S3` also names its own limits | It is a **halide-specific re-parameterization**, including molecular A-site cations whose "radius" is not an ionic radius at all; and `S3` explicitly says "There is no boundary on the tolerance factor scale that separates perovskites from non-perovskites". Formalizing it would mean formalizing a different (and self-undermining) empirical system, not the geometric criterion. Non-goal |
| **octahedral factor `μ = r_B/r_O`** (`S8`, `S3`, both first-hand) | A second, independent axis of the perovskite structure map; `μ > 0.414` is the short-contact geometric limit | It is a criterion on a **different ratio**; the plan's window equivalence is about the A-fit and must not be read as a `μ` statement. §1.4 non-goal; see §S1.3 above |
| **Glazer tilting notation** (`S11`, `bibliographic-only`) | The classification of the octahedral tilting systems (`a⁻a⁻a⁻` etc.) that describe *how* a perovskite leaves cubic symmetry when the A ion is too small | It is **discrete crystallography** (`a`/`b`/`c` tilt magnitudes and rotation axes of the `BO₆` network), not a statement about three radii; the theory states the band verdict only, and `S6` shows the two live at different levels ("the `[BO₆]` octahedra will tilt in order to fill space"). §1.4 non-goal |

**Formalizable implication.** These four are the plan's **scope boundary** and they require no Lean
change; what this round adds is that each boundary now has a checkable citation, so a verifier can
confirm the theory is not claiming to supersede them. **What cannot be expressed** in the installed
mathlib is not the issue for any of them — they *could* be formalized; they are excluded by scope,
which is a different (and honest) reason.

---

# §NOT — Clean negatives: the claims the literature does NOT contain

This is the round's most valuable output and the plan's most important honesty input. **Each row is a
claim this theory makes that no retrieved source makes.** "Absent" means: searched in the retrieved
first-hand texts and in ~1400 delegate-retrieved full texts, plus Crossref/OpenAlex/web; not found.

| plan statement | literature status | why it is absent |
|---|---|---|
| `conforms_iff_radius_window` — `GoldschmidtConforms lo hi rA rB rO ↔ rAMin lo rB rO ≤ rA ∧ rA ≤ rAMax hi rB rO` | **absent.** No source prints the band verdict as an interval in `r_A`; every source applies `t` numerically and compares | the literature never inverts the criterion. **This is the theory's own exactification** |
| `conforms_iff_sq` — the `√2`-free squared criterion `2 lo² (r_B+r_O)² ≤ (r_A+r_O)² ≤ 2 hi² (r_B+r_O)²` | **absent**, entirely | algebraic rewriting is not a published object; it exists to make the verdict decidable in `ℚ` |
| `conforms_symmetric_band_iff` — `1 ± δ ↔ |r_A − idealA| ≤ δ √2 (r_B+r_O)` | **absent** as a printed statement. The **symmetric band itself** appears nowhere in the retrieved sources; the closest printed thing is `0.825 < t < 1.059` (`S7`, an *asymmetric*, *fitted* band) | no source uses a symmetric `1 ± δ` convention at all |
| `tolFac_rO_const_iff` / the `r_O` trichotomy — `t` increasing / constant / decreasing in `r_O` according to `r_A < r_B` / `r_A = r_B` / `r_A > r_B`, with `t = 1/√2` exactly when `r_A = r_B` | **absent.** No source discusses the dependence of `t` on `r_O` | the literature treats `r_O` as a fixed constant (and even disagrees about its value, §S4.2); that `r_O` is a *variable* with a sign-changing effect is invisible in the printed corpus |
| `tolFac_shift` — the exact affine law `t(r_A + d) − t(r_A) = d/(√2 (r_B+r_O))` | **absent as a statement.** (`S15`'s `BaTi₁₋ₓZrₓO₃` series *illustrates* it numerically — see `INSTANCE-DATA.md` §T3b — but no source states or proves the identity.) | the identity is trivial once `t` is written as a ratio; the literature never needs it |
| `tolFac_irrational` — `t` is irrational at rational radii (`√2 ∉ ℚ`) | **absent.** No source raises the question | the literature prints 2–3 decimals; exactness is not a question it can ask |
| the 15 % radius rule → a `Δt` bound (`tolFacFifteen_le`) | **absent.** No source turns the substitution radius rule into a bound on the tolerance factor | the two rules (band criterion, substitution rule) are printed in **separate literatures** and are never combined |
| `radiusMatch_comp` — the *ratchet* (two 15 % steps drift by more than 15 %) | **absent** | the 15 % rule is printed as a one-step rule with no iterability discussion at all |
| `exists_compensating_partner` — the existence of an opposite-sign partner from `∑ dz = 0` | **absent** as a mathematical statement (the *rule* is printed in prose; its quantifier structure is not) — and ⭐ the primary text's own charge condition is **stoichiometric**, not `∑ dz = 0` (§S3.2 Form 0) | the charge rule is stated as advice to the chemist, never as an existence theorem; and Goldschmidt **explicitly declines** to make valency a separate criterion |
| the electronegativity term as an explicit **formula** (`chiTol tol₀ k χ χ' = tol₀ − k |χ − χ'|`) | **absent.** The chemical rule is printed **qualitatively** everywhere retrieved, and the primary text phrases it as compensation by `Feldwirkungen`, not as a formula | no source proposes a functional form; the plan's linear shape is a **declared** choice |
| the `t²`-based rational decision layer (`tolFacSq`, `inBandQ`, `zoneQ`) | **absent** | a formalization artifact by construction |
| "*Goldschmidt defined the factor as `(r_A+r_O)/(√2(r_B+r_O))` and used a band*" | ✅ **NO LONGER A NEGATIVE — RESOLVED IN THE AFFIRMATIVE.** The primary text `S9` prints the factor as `R_A + R_X = t√2(R_B + R_X)` and the band as *"durchwegs zwischen 0,8 und 1"*, with corundum below 0.8 and aragonite above 1.0 | this row **left the negative list** in round 1; see §S1.1c. ⚠️ The `[0.75, 1]` lower edge remains a *modern oxide-catalysis* convention with **no** primary support |

⭐ **What is now POSITIVE (was negative in the round-1 plan text).** Three items the plan presented as
merely "supported by the literature" are now **first-hand sourced**, and the theory should say so:
(i) the factor's identity and notation (`S9`); (ii) the classic band `[0.8, 1]` (`S9`); (iii) the
15 % figure **and its reference ion** (`S9`). What remains the theory's own is: the equivalences, the
squared form, the symmetric band, the `r_O` trichotomy, the shift law, the irrationality, the
radius-rule → `Δt` bridge, the ratchet, the compensating-partner existence theorem, and the linear
`chiTol` shape.

**What this table is for.** It is the evidence that plan §1.2's sentence "the exact equivalences of
§6–§7 … are this theory's own exactification and are **absent from the literature**" is *literally
true and now checkable*, and that plan §12's honesty table can point at a locus instead of an
assertion. **No statement of `plan.md` changes because of this table** — the table is what makes the
existing statements honest. ⭐ **One row left the negative list** (see the struck-through row): the
provenance of the factor and of the band `[0.8, 1]` is now **first-hand**, so the theory's
`classicLo`/`classicHi` are transcriptions of a printed band, while the equivalences remain its own.

---

# §IMPACT — net effect of round 1 on `theories/goldschmidt/plan.md`

| # | plan locus | change forced | why |
|---|---|---|---|
| 1 | §1.1 prose: "above which the structure distorts (tetragonal/ferroelectric, `1.0 < t < 1.1`)" | **reword** to the attested half-open form (`t > 1`, name contested) | `1.0 < t < 1.1` is **not attested as a band** (§S2.2); the printed upper-side motif is `t > 1` and even *which* distortion is disputed. The primary text says above 1.0 the perovskite structure is replaced "durch die Aragonitstruktur" — **aragonite**, not tetragonal |
| 2 | §4 constant `hiTetragonal = 11/10` | **keep the definition**, add a §12 honesty row: "declared band edge, chosen for the instance layer; **no printed `[1, 11/10]` band exists**" | the band is a *parameter* by design; what was wrong was presenting this edge as the literature's tetragonal band. Nearest printed support: `S15`'s `t ≥ 1.1` rejection sentence |
| 3 | §2 conventions | **add** "every printed `t` is quoted together with the radius triple its source used; two `t` values for one compound from sources with different `r_O` are two different numbers" | `rO = 1.35` (`S8`, `S15`) vs `1.40` (`S6`, `S16`) moves every `t` by ≈ 0.5–1 % (`INSTANCE-DATA.md` §T3b) |
| 4 | §9 rows I2/I3/I4 docstrings | **add** the literature locus: `SrTiO₃` `t = 1.00` (`S6`, same radii, rounded), `1.009` (`S8`, `rO = 1.35`), and ⭐ **Goldschmidt's own `0,9x`** (`S9`, his radii); `BaNiO₃` `t = 1.13` (`S6`) hexagonal | a delivered `tooLarge` verdict for the archetype otherwise reads as a defect (§S5.1); and the radius-compilation dependence is now first-hand |
| 5 | §1.4 non-goals | **add** the `r_cation/r_anion ≥ 0.732` / radius-ratio rule as a criterion on a **different ratio**, and note that `0.732` in `S8` is the *upper end of the 6-fold octahedral-factor interval* | the plan must not be read as conflating the two criteria (§S1.3) |
| 6 | §12 honesty table | **strengthen** the "declared modelling premise" rows by citing `S3`'s "There is no boundary on the tolerance factor scale that separates perovskites from non-perovskites" and `S6`'s "the tolerance factor is only a rough estimate" | these are the printed statements that license treating the band as declared rather than proved (§S2.3) |
| 7 | §1.1 / §12 attribution to Goldschmidt | ✅ **no longer a weakening — a strengthening.** Cite `S9` for the factor, the band, and the rules | the primary text **was** read (§S1.1b–c); the round-1 "soften the attribution" recommendation is **withdrawn** |
| 8 | §1.2 / §6–§7 / §12 | **no change** | the "absent from the literature" claim is now *evidenced* by §NOT and the statements themselves are correct as written |
| 9 | §2 `τ` row and §5 `radiusMatch_*` docstrings | ⭐ **record that the printed rule is the `min` form**, `\|r − r'\| ≤ (3/20)·min(r, r')` (`S9` p. 83: "in Prozenten des kleinsten Radius"), and that `radiusMatch_min_iff` is therefore the *faithful* form; `RadiusMatch τ r r'` is the declared parameterization | the round-1 recommendation to "declare the reference ion as a convention" is **withdrawn** — the reference ion is a literature datum (§S3.1 item 3) |
| 10 | §12 charge-rule row | ⭐ **rewrite**: `ChargeBalanced dz` (`∑ dz = 0`) is a **later systematization, NOT Goldschmidt's criterion** — `S9` (pp. 80–81) states a *stoichiometric* matching condition and **explicitly folds valency into the apparent radii**; the literature also prints a `\|Δz\| = 1` variant | this is the §S3 finding that most changes the honesty table (§S3.2 Form 0) |
| 11 | §9 row family I6 | **replace or mark as undocumented** the pair `Na⁺ + Nb⁵⁺ ↔ Ca²⁺ + Ti⁴⁺`; cite instead the primary plagioclase pair `NaAlSi₃O₈`/`CaAl₂Si₂O₈` (`S9` p. 81), the oxide `A²⁺ ↔ (A³⁺, A⁺)` statement E1, and the printed `3/1` arithmetic E2 | no retrieved source prints the plan's specific pair (§S3.2.1) |
| 12 | §9 row family I5 | **add** the primary isovalent example `CaTiO₃` → `Sr`/`Ba` at the A site (`S9` p. 91) as the positive instance of the radius rule | first-hand locus for a row family that currently cites only Shannon radii (§S3.3) |
| 13 | §12 radius-rule row and §2 `χ` row | **add** that the 15 % is printed as *"etwa 15 %"* ("about"), and that the plan's `τ = 3/20` is a **declared sharpening**; and that Goldschmidt's quantity is `Feldwirkungen`, with electronegativity a modern surrogate | the source is explicit about both (§S3.1, §S3.3) |

**Statements that this round confirms need NO change** (worth recording, so round 2 does not revisit
them): the parameterized-band design (§2), the radius-window equivalence and its squared form as
*theorems* (§6), the `r_O` trichotomy and the shift law as *theorems* (§6), the 15 % figure as
`τ = 3/20` (§5), the charge-balance *definition* as a declared rule (§5), the qualitative chemical
rule with a declared linear shape (§2, §12), and the delivered `SrTiO₃` / `BaNiO₃` verdicts
themselves.

---

# §OUT — outstanding work for round 2 (ordered by value)

1. ✅ **DONE — `S9` retrieved and read** (§S1.1b). The round-2 task is now the *reverse*: **re-open
   the Frankfurt OPUS scan through a client that can pass the Anubis bot wall** and confirm the OCR
   readings in §S1.1c and §S3.1–§S3.3 against the page images, in particular (a) the `SrTiO₃` cell of
   Goldschmidt's table (currently `0,9x`, OCR-ambiguous), (b) the full 14-row table, and (c) the
   `15 %` numeral. Also read the paywalled `S1` (Naturwissenschaften **14**, 477–485) to record how the
   short version differs from the memoir.
2. ✅ **DONE — the charge rule's documented example and the chemical rule's wording** (§S3.2, §S3.3).
3. **`Mn³⁺(VI, high spin) = 0.645`** — the one radius not confirmed first-hand (`INSTANCE-DATA.md`
   §T2). Any paper that computes a `LaMnO₃` tolerance factor with Shannon radii will print it.
4. ✅ **DONE — the 8-fold `r_cation/r_anion ≥ 0.732` statement** was retrieved (`S13`, Pauling's
   radius-ratio table: `1.0–0.732` → 8-fold cubic, `0.732–0.414` → 6-fold octahedral). Update §S1.3
   and `INSTANCE-DATA.md` §T5 to cite `S13` alongside `S8`, and note that `S13` is the source that
   prints the table **as Pauling's** rather than as an octahedral-factor interval.
5. **The `10 %` / `20 %` radius-rule variants** — this round found **15 % only** in retrieved sources
   (the `10 %` figure belongs to the electronegativity threshold, §S3.3). A second parcel on this is
   still running; if it reports a printed `10 %` or `20 %` radius rule, §S3.1 gains rows.
6. **`S10` (Li, Soh & Wu 2004)** — Elsevier paywall; the `0.8 ≤ t ≤ 1` attribution currently rests on
   `S3`. Retrieve to close the loop on the `0.75`-vs-`0.8` lower edge's provenance.
7. **`S11` (Glazer 1972)** — `bibliographic-only`; obtain if the round-2 record wants to state
   precisely what the tilting notation excludes.
8. **Europe PMC REST full-text search** was HTTP 503 throughout this round (delegate finding); NCBI
   E-utilities was the working substitute. Retry next round — literal phrase search over PMC would
   make band-hunting much cheaper.
9. **The OPUS `/opus4/frontdoor/deliver/...` PDF path** (note: `deliver`, not `files`) appears in the
   web index and may bypass the bot wall where `/files/` did not — worth trying first in round 2.
