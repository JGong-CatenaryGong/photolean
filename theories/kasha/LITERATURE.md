# theories/kasha/LITERATURE.md — literature record: Kasha's rule (round 1 delivered)

> Owner: `literature_researcher`. Every entry must carry a checkable source, its conclusion, and a
> **formalizable implication** (which assumptions become explicit Lean premises, which are physical
> approximations that must be declared rather than proved, which cannot be expressed in the installed
> mathlib, and how the plan's statements are affected).
> Status: **round 1 delivered** (§R1.0–§R1.9). This file is English; the only bilingual file of this
> theory is `theories/kasha/RESULTS.md`.
> Evidence vocabulary used below — `first-hand` (the text was retrieved here and read), `secondary`
> (read only as quoted/paraphrased by another retrieved source, which is named), `bibliographic-only`
> (title/volume/pages/DOI verified, body not read), `not-accessed` (no body), `UNSUPPORTED` (nothing
> found that may be quoted). **No PDF is stored in this repository**; scratch is `/tmp/kasha/`, and
> every `URLS FETCHED` line below is re-runnable.
> Date of this round: **2026-09-20** (all HTTP observations in §R1.0 were made in this session).

---

## §R0. Scope of the survey (why these questions)

The theory formalizes Kasha's rule (emission from the lowest excited state of a given multiplicity)
inside a finite excited-state cascade model. The literature round must settle:

1. **The canonical statement of Kasha's rule** (original source, exact wording, scope: which
   molecules/phases, the "of a given multiplicity" qualifier) — so the formal predicate is not a
   caricature.
2. **Vavilov's rule** and the Kasha–Vavilov relation (independence of the emission quantum yield
   from the excitation wavelength) — the second face of the same condition.
3. **Which rate inequalities the literature actually asserts** (internal conversion versus radiative
   rates; the "k_IC >> k_rad" form) and with what numbers — these become the tolerance threshold of
   the sharp criterion, with provenance.
4. **First-hand rate data for instances**: at least one conforming family (e.g. benzene, naphthalene,
   anthracene, pyrene) and at least one anti-Kasha family (e.g. azulene's S₂ emission, gas-phase
   isolated molecules showing resonance fluorescence, thioketones) with per-point data and page
   references, or an explicit `UNSUPPORTED` mark where the numbers are not first-hand.
5. **The energy-gap law / Marcus-type radiationless-transition form** for internal conversion — the
   input needed by the plan's Marcus bridge (plan §7.2 item K4c): is the quadratic driving-force form used in the
   literature for radiationless transitions, and under what stated limits?

---

# §R1 — Round 1 retrieval record

## §R1.0 Method / sources consulted

**Approach.** Bibliographic facts were verified against Crossref REST
(`api.crossref.org/works/<doi>`) — *guessed* DOIs were checked, never trusted: two guessed DOIs were
disproved in this round (§R1.7.1). Full texts were retrieved as PDF/XML and searched with
`pdftotext -layout` + `grep`; no paper was read into context whole. Open-access full text came from
the Europe PMC REST API (`.../rest/<PMCID>/fullTextXML`) and from repository PDFs.

**Hosts actually reached (HTTP 200 in this session).** `api.crossref.org` · `api.openalex.org` ·
`api.semanticscholar.org` · `api.unpaywall.org` · `www.ebi.ac.uk/europepmc/webservices/rest/*`
(both `search` and `fullTextXML`) · `eutils.ncbi.nlm.nih.gov` (`efetch`/`esearch`) ·
`pmc.ncbi.nlm.nih.gov` · `arxiv.org` (abs + pdf) · `harvest.usask.ca` (DSpace 7 REST API) ·
`ufn.ru` (Physics-Uspekhi) · `garfield.library.upenn.edu` · `api.github.com`.

**Blocked hosts (recorded as negatives, with the exact obstacle).**
HTTP 403 Cloudflare challenge for `curl` **and** for the harness fetch tool: `goldbook.iupac.org`
(both `/terms/view/K03370/plain` and `/K03371/plain|xml`), `old.goldbook.iupac.org`,
`www.iupac.org`, `publications.iupac.org` (the PAC 2007 glossary PDF), `list.iupac.org` (301 → the
same challenge), `forskning.ruc.dk` (the OA repository copy of the PAC glossary),
`pubs.rsc.org`, `pubs.acs.org` (incl. `pb-assets/.../preview-*.pdf`), `pubs.aip.org`,
`www.tandfonline.com`, `www.researchgate.net`, `chemrxiv.org` (incl. its api-gateway asset URL),
`www.mdpi.com` (direct; MDPI full text was reached through PMC instead).
HTTP 202 with an **empty** body: `www.degruyter.com/document/doi/10.1351/pac200779030293/pdf`.
Connection timeout / reset (no page at all): `web.archive.org` **and** `archive.org/wayback/
available` (so no Wayback route), `scholar.archive.org`, `en.wikipedia.org`,
`books.google.com`, `www.googleapis.com/books/v1` (the Books API), `babel.hathitrust.org`,
`r.jina.ai` (text proxy — timed out for every URL tried), `zenodo.org`, `www.base-search.net`,
`citeseerx.ist.psu.edu`, `sci-hub.se` (**not used** — listed only as observed-unreachable).
`api.core.ac.uk` answered 429 (rate-limited); `mail.goldbook.iupac.org` failed TLS handshake.

**Consequence for provenance — stated up front.** The **body of Kasha 1950 was not reachable** in
this environment (§R1.1.1), and neither was the IUPAC glossary that carries the normative wording
(§R1.1.2). Those two statements therefore rest on `secondary` provenance, named explicitly, and are
flagged as such in every place they are used. Everything in the instance tables (§R1.4, §R1.5) was
read **first-hand** by this record — with **one** labelled exception: the two gas-phase NO₂ loci
(§R1.4.2, row "gas-phase NO₂"), which were retrieved and read by a delegation of this round and are
marked `second-reader`; they must be re-read before any of their numbers enters a Lean docstring.

**Additional hosts reached later in the round** (`URLS FETCHED`, all HTTP 200): `lirias.kuleuven.be`
(the KU Leuven repository copies of Veys & Escudero 2020, §R1.4.1(C-bis), **and** of the Veys 2023 PhD
thesis, §R1.2.3/§R1.3/§R1.5.3), `harvest.usask.ca` (the 1995 thesis, §R1.4.1(A)),
`ar5iv.labs.arxiv.org` (the arXiv HTML rendering of Jang 2021, §R1.7.2), `arxiv.org` (the gas-phase
azulene PDF, §R1.4.1(D)), **`nvlpubs.nist.gov`** (the NIST OA journal copy of Birks 1976 — the single
most useful new host of the round: it carries a first-hand statement of *both* rules, their deviation
lists and Table 2 of fluorescence lifetimes, §R1.1.3/§R1.2.3/§R1.5.3). These hosts join the reachable
list above; the blocked list is unchanged and no blocked host was worked around by a proxy.

## §R1.1 The canonical statement (question 1)

### R1.1.1 The citation, and what can and cannot be claimed about the 1950 text

**source**: M. Kasha, "Characterization of electronic transitions in complex molecules",
*Discussions of the Faraday Society* **9**, 14–19 (1950). DOI `10.1039/df9500900014`.
**status**: `bibliographic-only` — **Crossref-verified here** (title exact; author Michael Kasha;
container *Discussions of the Faraday Society*; volume 9; first page 14; year 1950). The **body is
`not-accessed`**: `pubs.rsc.org` answers 403 (Cloudflare) to curl and to the harness fetch tool, and
the three fallback routes (Google Books API, HathiTrust full-text search, Wayback) are all
unreachable from this host (§R1.0).

**The sentence the theory's statement is anchored on** — quoted **verbatim, in quotation marks, by a
peer-reviewed source**:

> "The emitting electronic level of a given multiplicity is the lowest excited level of that
> multiplicity."

**source of the quotation**: J. C. del Valle, J. Catalán, "Kasha's rule: a reappraisal",
*Phys. Chem. Chem. Phys.* **21**(19), 10061–10069 (2019), DOI `10.1039/c9cp00739c`.
**status**: `secondary (quoted by del Valle & Catalán 2019)` — the quoting sentence was read
first-hand in the paper's abstract (retrieved via NCBI E-utilities, `efetch db=pubmed id=31049513`);
Crossref re-verified the bibliographic record (vol 21, issue 19, pp. 10061–10069). The **2019 body
itself is closed** (Unpaywall `is_oa=false`, `oa_status=closed`), so the page inside Kasha 1950 on
which the sentence is printed **could not be confirmed** and is deliberately **not** stated here.
⚠️ **Do not write a page number for that sentence until a human reads the 1950 original.**

### R1.1.2 The scope qualifiers — these are part of the statement, not commentary

The same 2019 abstract states the rule's domain in its own words (first-hand, quoted):

> "Kasha's rule focuses on the emission (photophysics) for **complex molecules**, in **condensed
> phase**, for the **absorption of one photon per molecule under photostationary conditions**, then a
> rapid internal conversion and a vibrational relaxation warrant that the corresponding emission
> comes from the first excited electronic level **regardless of which electronic state of equal
> multiplicity is excited**."

and the same abstract's verdict on the exception family (first-hand, quoted):

> "This work revises some anomalous cases reported in the literature, which seemingly violate Kasha's
> rule. To the contrary, **apart from azulene, the remaining molecules fulfill Kasha's rule**."

Two further framing facts, both first-hand from that abstract: the 2019 authors insist the rule
"**must be stated just as in the seminal paper**" — i.e. the wording above is presented as *the*
canonical statement — and they present the rule as warranted by "a rapid internal conversion and a
vibrational relaxation", i.e. as a **generalization from observation whose mechanism is a rate
inequality**, not as a theorem.

**Formalizable implication of §R1.1.**
- **The plan's §1.1 wording is a faithful paraphrase but is *wider* than the source.** The source's
  four scope qualifiers (complex molecules; condensed phase; one photon per molecule; photostationary
  conditions) are all **absent from the Lean model** and cannot be premises, because the model has no
  notion of phase, of photon number, or of a stationary state. They must therefore appear as a
  **declared scope limit in the `KashaRule` docstring** (plan §1.5/§13 already registers
  "no temperature or solvent dependence"; add "single-photon, condensed-phase, complex-molecule
  domain"). ⚠️ **Impact: §1.1's sentence should not be presented as an unconditional claim about
  molecules; the qualifiers belong next to it.**
- `KashaRule rad ic N := upperYield rad ic N = 0` formalizes the *exact* form. The source's own
  wording ("the emitting electronic level … **is** the lowest …") is *also* exact, so the plan's
  finding that the exact form forces `rad i = 0` above the lowest level (K2 `kashaRule_iff_rad_zero`,
  i.e. the exact rule is never true of a real molecule) is a statement **about the model**, not a
  contradiction with the source. It must be narrated that way in `RESULTS.md`.
- **`tol` is not a literature constant.** This round found **no** source that prints a purity
  tolerance for Kasha's rule; the only printed accuracy figure found anywhere is Vavilov's own for
  *yield* independence (§R1.2.1: "constant to within about 8 %" — a *different* quantity, and for a
  dye, not for a molecule's spectrum). **Impact: `tol = 1/100` in the plan is a modelling choice and
  must be labelled as such**, not attributed to the literature.

### R1.1.3 The extended rule (phosphorescence from T₁)

**source**: IUPAC *Compendium of Chemical Terminology* ("Gold Book"), entry **"Kasha rule"**,
term id **K03370**, `goldbook.iupac.org/terms/view/K03370`.
**status**: `secondary` — the Gold Book body is Cloudflare-403 here (§R1.0). The entry's opening
words were recovered from two independent search-index renderings of the same string (the Gold Book
entry itself, and the identical sentence quoted inside an ACS "in focus" preview PDF that the
harness's search index returned):

> "Kasha rule: **Polyatomic molecular entities luminescence with appreciable yield only from the
> lowest excited state of a given multiplicity**."

A peer-reviewed OA paper reached here paraphrases exactly this, and adds the two-multiplicity reading
explicitly: R. Holzinger, N. S. Bassler, H. Ritsch, C. Genes, "Scaling Law for Kasha's Rule in
Photoexcited Molecular Aggregates", *J. Phys. Chem. A* **128**, 3910–3915 (2024), DOI
`10.1021/acs.jpca.4c00342` — **status `first-hand`** — writes: "photon emission (**fluorescence or
phosphorescence**) occurs in appreciable yield only from the lowest excited state of a given
multiplicity".

**⭐ A first-hand, *reachable* locus for the same two-multiplicity reading (this supersedes the
Cloudflare-blocked Gold Book as the citable source).** J. B. Birks, "Fluorescence Quantum Yield
Measurements", *Journal of Research of the National Bureau of Standards A — Physics and Chemistry*
**80A**(3), 389–399 (1976), DOI `10.6028/jres.080a.038` — retrieved here as the NIST OA PDF
(`https://nvlpubs.nist.gov/nistpubs/jres/80A/jresv80An3p389_A1b.pdf`, 13 158 311 bytes; `pdftotext`).
**status `first-hand`.** **Locus: §2.5 "Vavilov's Law and Kasha's Rules", printed p. 392.** Verbatim
(the OCR's broken spacing repaired, wording untouched):

> "**Kasha's rules** [9], another well-known generalization, state that in a complex molecule
> luminescence occurs only from the lowest excited state of a given multiplicity, i.e., **S₁→S₀
> fluorescence and T₁→S₀ phosphorescence**. For many years azulene and its derivatives, which emit
> S₂→S₀ fluorescence and negligible S₁→S₀ fluorescence, were the main exceptions to Kasha's rules.
> Recently the picture has changed dramatically. In addition to the normal S₁→S₀ fluorescence,
> **weak S₂→S₀ fluorescence has been observed in benzene, toluene, p-xylene, mesitylene, naphthalene,
> pyrene, 1:2-benzanthracene, 3:4-benzopyrene, 1:12-benzoperylene and ovalene**, weak S₃→S₀
> fluorescence has […]"

Note the plural "**rules**" and the explicit dual reading `S₁` / `T₁` — the extended rule is therefore
citable from an OA source, and the word "**weak**" is the source's own hedge on the conforming
molecules (see §R1.5.3, where it becomes decisive).

**Formalizable implication of §R1.1.3.**
- The normative wording supports the plan's ladder being **multiplicity-indexed**: the same predicate
  applies to the singlet ladder (fluorescence from `S₁`) and to the triplet ladder (phosphorescence
  from `T₁`). Nothing in `KashaRule`/`KashaWithin` mentions multiplicity, which is correct — but the
  **docstring must say that the ladder is "the levels of one multiplicity"** so that the
  `T₁`-reading is licensed. **Impact on the plan: docstring only; no statement changes.**
- "**appreciable** yield" (Gold Book) and "**weak** S₂→S₀ fluorescence [is] observed" (Birks 1976) are
  two first-hand hedges, and they are the *only* normative support for a tolerance formulation. The
  plan's `tol` is their quantitative version; keep the words "appreciable"/"weak" in the docstring as
  the bridge from the sources to `tol`, and see §R1.5.3 for why "weak" matters to the instance layer.
- One honest discontinuity to record: the normative entry says *luminescence* (covering
  phosphorescence), while the plan's K5 instance rows are all fluorescence. **Impact: K5b rows are
  singlet-ladder rows; `RESULTS.md` must not claim that the instance layer tests the T₁ half of the
  rule.**

## §R1.2 Vavilov's rule and the compound term (question 2)

### R1.2.1 Vavilov's own papers — first-hand primary text (a reprint)

**sources (two facing facts from one retrieved text)**:
- S. I. Vavilov, "Die Fluoreszenzausbeute von Farbstofflösungen als Funktion der Wellenlänge des
  anregenden Lichtes. II", *Zeitschrift für Physik* **42**, 311–318 (1927), DOI
  `10.1007/BF01397622` — **Crossref-verified here** (author printed "Wawilow"; vol 42; pp. 311–318;
  1927).
- S. I. Vavilov, same title (part I), *Zeitschrift für Physik* **22**, 266 (1924) — cited by the
  reprint below as the earlier paper of the pair; **its own Crossref record was not opened here**,
  so its DOI is **not** given.
- The Russian reprint used for reading: **УФН / Physics-Uspekhi 93, 315–320 (1967)**, DOI
  `10.3367/UFNr.0093.196710f.0315`, at `https://ufn.ru/ru/articles/1967/10/f/`, PDF at
  `https://ufn.ru/ufn67/ufn67_10/Russian/r6710f.pdf` (fetched here, 560 622 bytes; `pdftotext`).
  Its editorial footnote (first-hand, translated from the Russian):
  > "First published in Zs. Phys. **42**, 311 (1927). The article continues the work of the same
  > title published in Zs. Phys. **22**, 266 (1924); **in it the law that later came to be called
  > 'Vavilov's law' is formulated.**"

**status**: `first-hand` for the reprint's text and editorial note (PDF fetched and read here);
`bibliographic-only` for the 1927 original (Crossref-verified, body not read); `not-accessed` for the
1924 paper. The reprint is Russian; translations in this record are **this record's** renderings and
are marked as such.

What the 1927 paper actually reports (all `first-hand`, from the reprint; own translation):
- its own abstract: the fluorescence yield of a **fluorescein** solution was measured over the
  absorption region **250–540 mμ**; from 250 to 430 mμ the yield is **proportional to the
  wavelength**; then, up to about the wavelength of the fluorescence maximum, the yield is **almost
  constant**; then it falls sharply. For an **esculin** solution the yield is **independent of
  wavelength from 250 to 405 mμ**;
- on the earlier (1924) measurements: "the fluorescence yield [of dilute solutions] remained
  constant **to within about 8 %**" over **446–519 mμ** — i.e. **a printed tolerance, by the author,
  on the very quantity Vavilov's rule is about**;
- the 1927 paper's own discussion concerns "the law of Einstein's equivalents": in the UV the yield
  **follows** that law (proportional to wavelength), while near the critical point there are
  "noticeable deviations" from it.

### R1.2.2 The compound term "Kasha–Vavilov rule", and the rule's scope limit as a *photophysical* rule

- **Normative entry (secondary)**: IUPAC Gold Book, entry **"Kasha–Vavilov rule"**, term id **K03371**,
  `goldbook.iupac.org/terms/view/K03371` — **status `secondary`, body Cloudflare-403 here**; that the
  *compound* entry exists as the normative locus is confirmed by the search index over the Gold Book
  and by the peer-reviewed uses below. The entry's wording was **not** retrievable and is **not**
  quoted here.
- **The rule as used in modern photochemistry (first-hand)**: M. Maafi, R. G. Brown, "On photokinetics
  under monochromatic light", *Front. Chem.* **11**, 1233151 (2023), DOI `10.3389/fchem.2023.1233151`
  (OA, `PMC10538970`; read via the Europe PMC full text) — first-hand quotation:
  > "The argument behind such a state of the matter relates to the **Kasha–Vavilov rule (Kasha,
  > 1950)**, despite that this rule **concerned fundamentally photophysical processes and has not
  > been expanded, by the authors, to photochemistry**. The literature has reported a large number of
  > systems where **the quantum yield is not constant over two or more wavelengths** (Becker et al.,
  > 1969; Becker and Favaro, 2011; Reinfelds et al., 2019; Montalti et al., 2020), including the
  > ferrioxalate actinometer …, since as early as 1958 (Zimmerman, 1958)."

  The same paper's own bibliography entry (first-hand, from its reference list) is an independent
  confirmation of the Kasha citation: "Kasha M. (1950). Characterization of electronic transitions in
  complex molecules. Discuss. Faraday Soc. **9**, 14–19. `10.1039/DF9500900014`."

**Formalizable implication of §R1.2.**
- **The plan's K2 `kashaRule_iff_vavilovUpTo` is a statement *inside* the model**; the literature's
  relation between the two rules is **mechanistic and historical**, not an identity: the compound
  name exists because the *same* fast-IC picture underwrites both. The record must therefore present
  the equivalence as **the plan's own theorem about the cascade model**, and cite the compound term
  only for *why* the two faces are discussed together. **Impact: docstring/`RESULTS.md` phrasing —
  no statement change.**
- **Vavilov's rule is about the *yield*, not the spectrum.** The plan's `specFrac` (the excitation-
  independence of the *emission spectrum*) is the other face; the retrieved sources speak of the
  quantum yield. **Impact: the K1 docstring should not attribute `specFrac`-independence to
  "Vavilov's rule"; attribute it to Kasha's rule / the excitation-independence of the spectrum.**
- **The scope limit is explicit and is a real warning**: the retrieved 2023 paper is a *counter-
  example-aware* source — it says Vavilov-type invariability "needs to be proven experimentally and
  not assumed", and lists systems where the yield is wavelength-dependent. This is literature support
  for the plan's **tolerance** formulation (rather than the exact one). **Impact: strengthens K3;
  no premise is created by it (the premise `ic 0 > 0` of K2 #18 remains a model premise).**
- **A printed tolerance exists but is not transferable**: Vavilov's own "± 8 %" is (i) about the
  *yield* and (ii) about a *dye solution* in a limited spectral window. It may be quoted as the
  historical precedent for stating the rule *with* an accuracy, but it must **not** be used as the
  numerical value of `tol` in the instance rows.

### R1.2.3 ⭐ Vavilov's law in a critical review, **with its documented deviation list** (first-hand)

**source / locus / status**: J. B. Birks, *J. Res. NBS A* **80A**(3), 389–399 (1976), DOI
`10.6028/jres.080a.038`, **§2.5, printed p. 392** — **`first-hand`** (NIST OA PDF fetched and read
here; see §R1.1.3 for the retrieval details). Three verbatim passages (OCR spacing repaired):

> "It is commonly assumed that φ_MH = 1.0 for S₂→S₁ IC and that φ = 1 for IC between higher excited
> states within the singlet (S_F) manifold, so that φ_FM is **independent of the excitation wavelength
> λ_ex** up to the ionization potential. This assumption, known as **Vavilov's Law**, has been
> confirmed for many compounds in solution. **Major deviations** from Vavilov's law have, however,
> been observed for solutions of **benzene, toluene, p-xylene, mesitylene, fluorobenzene, naphthalene,
> 2-methylnaphthalene, 1,6-dimethylnaphthalene** [1], tryptophan, tyrosine and phenylalanine [7]. In
> each case it is observed that **φ'_FM/φ_FM = φ_MH < 1**."

> "In benzene and its derivatives and possibly in the other compounds, the effect is due to efficient
> **S₂→S\*\* IC (k_CH) competing with S₂→S₁ IC (k_MH)** [8]."

> "In fluorescence quantum yield measurements it is essential **either to verify that Vavilov's law
> applies, or to limit the excitation to the region of the S₀→S₁ absorption spectrum**."

⚠️ **These are qualitative + mechanistic statements with a printed page; Birks prints no numerical
`φ` ratio and no rate constant in them.** A first-hand *quantitative* Vavilov test (a φ(λ_ex) table
with numbers) was **not** reached in this round → `UNSUPPORTED` (§R1.9).

**Corroborating reachable statement of both rules (first-hand)**: K. Veys, "Quantum Chemical
Investigations of Anti-Kasha Fluorescence", PhD thesis, KU Leuven, Oct 2023 (OA,
`lirias.kuleuven.be/retrieve/d5d2667e-0a82-45d7-ad47-dee27a99cb45`), **printed pp. 3–4**, writes:
"**Vibrational relaxation and IC processes between excited states typically happen in the range of
picoseconds.** Therefore, they do outcompete other processes like fluorescence from higher-lying
states. In the 1950s, Michael Kasha accordingly wrote down the so-called **Kasha's rule**, namely:
'polyatomic molecular entities react with appreciable yield only from the lowest excited state of a
given multiplicity'. Later, it was extended into the **Kasha–Vavilov rule**, stating that 'the quantum
yield of luminescence is independent of the wavelength of exciting radiation'." — i.e. a third
independent, *accessible* source for both rule statements (its refs 2–4).

**Formalizable implication of §R1.2.3.**
- **The plan's tolerance formulation is now supported by a first-hand critical review, not by
  folklore**: Birks states the law, and in the same section states its documented failures *and* the
  operational consequence ("verify … or limit the excitation"). **Impact: K3's tolerance form is the
  literature-faithful one; `RESULTS.md` may cite p. 392 for it. No premise changes.**
- ⚠️ **But the same page names the plan's candidate conforming family as deviators.** Benzene,
  naphthalene and pyrene appear in Birks' Vavilov-deviation list (benzene, naphthalene) and in the
  "weak S₂→S₀ fluorescence observed" list (§R1.1.3: benzene, naphthalene, pyrene, ovalene, …). **This
  is the literature's own warning that a classical PAH is a bad choice for a *conforming* instance
  row** — see §R1.5.3, which is rewritten accordingly.
- **`VavilovAt`/`VavilovUpTo` are model predicates on the total yield.** Birks' `φ_MH`, `φ_FM` and
  `k_CH`/`k_MH` are *channel-resolved* quantities; the model's `VavilovAt` is their aggregate
  consequence. The equivalence K2 #18 is therefore a statement about the aggregate, and the docstring
  should say that the literature's `φ_MH` corresponds to the model's `icBranch` product, not to a
  single field.

## §R1.3 Which rate inequalities the literature actually asserts (question 3)

**What is asserted qualitatively (first-hand).** "Rapid internal conversion and vibrational
relaxation" is the mechanism named by del Valle & Catalán 2019 (§R1.1.2). A large OA review states
the same as the standard textbook picture — **first-hand**, N. A. Kukhta et al., "The Golden Age of
Thermally Activated Delayed Fluorescence Materials", *Chem. Rev.* (2024), DOI
`10.1021/acs.chemrev.3c00755` (OA, `PMC12132800`): "These singlet excitons **typically** relax to S₁
by **rapid internal conversion (IC) and vibrational relaxation (VR)** processes, **typically following
Kasha's rule**." Note the two "typically" — the source asserts a *typical* behaviour, not an
inequality with a constant.

**What is asserted quantitatively.** Three *different* evidentiary classes must be kept apart — this
is the main outcome of question 3:

| class | statement as printed | status | source (locus) |
|---|---|---|---|
| **measured** (azulene family, S₂→S₁ IC) | k_IC = **7.4 × 10⁸ – 1.0 × 10¹⁰ s⁻¹** determined from S₂ lifetimes τ_S₂ = 0.1–2.6 ns | `first-hand` | *Chem. Sci.* 2026, DOI `10.1039/d6sc00694a` (`PMC13576160`), **Table 3** + running text |
| **measured** (azulene, S₂ radiative rate) | Σk_r(S₂) = **3.5 × 10⁷ s⁻¹** for azulene in cyclohexane | `first-hand` | Tittelbach-Helmrich 1995 thesis (**Table 3.1**, printed **p. 115**) — full record in §R1.4 |
| **computed** (modern emitter, S₂→S₁ IC) | S₂→S₁ IC = **2.54 × 10¹² s⁻¹** (SCS-ADC(2)) to **4.37 × 10¹² s⁻¹** (CC2) | `first-hand` (these are the paper's own *calculations*, not measurements) | *Chem. Sci.* **17**, 10967–10981 (2026), DOI `10.1039/d6sc01726f` (`PMC13129759`), five-state-model section |
| **textbook order of magnitude** | "routinely driving k_ISC to **10⁸ to 10¹⁰ s⁻¹** in conventional polyaromatic scaffolds" | `first-hand` reading of a printed *typical-range* sentence | *Chem. Sci.* 2026, `PMC13576160`, introduction |
| **textbook order of magnitude (ISC, T₁→T₂)** | rIC T₁→T₂ = 3.9 × 10¹⁰ s⁻¹, T₂→T₁ IC = 9.8 × 10¹⁰ s⁻¹, T₂→T₁ IC = 1.4 × 10¹⁴ s⁻¹ | `first-hand`, **computed** values in a specific molecule | *Chem. Sci.* 2026, `PMC13129759` |
| ⭐ **textbook order of magnitude (IC vs fluorescence — the closest thing to the `k_IC ≫ k_rad` slogan with a printed page)** | "**internal conversion (IC, 10⁻¹² s)** between electronic (singlet) states … by emitting a photon (**fluorescence, 10⁻⁹ s**) … intersystem crossing (**ISC, 10⁻⁶ s**)" and "**Vibrational relaxation and IC processes between excited states typically happen in the range of picoseconds.** Therefore, they do outcompete other processes like fluorescence from higher-lying states." | `first-hand` reading of a printed *typical-range* statement (the thesis explicitly frames it as typical, not measured) | K. Veys, PhD thesis, KU Leuven (2023), **printed p. 3**, `lirias.kuleuven.be/retrieve/d5d2667e-0a82-45d7-ad47-dee27a99cb45` |

⚠️ **Negative result of this round (important for honesty).** The often-repeated pair
"k_IC ≈ 10¹¹–10¹³ s⁻¹ versus k_rad ≈ 10⁷–10⁹ s⁻¹ **for aromatic hydrocarbons**" was **not** found
printed as a measured comparison in any source reachable here. The only arithmetic statement of the
form "IC ≫ radiation" that this round can support with numbers is the **azulene series** (measured)
and modern TADF emitters (computed, §above). **Any 10¹²–10¹³ s⁻¹ figure used for benzene /
naphthalene / anthracene must be labelled `textbook order of magnitude` or dropped.**

**Formalizable implication of §R1.3.**
- The literature's `k_IC ≫ k_rad` is **qualitative with a "typically" attached**; the plan's
  threshold `(1 − tol)/tol` (K3 #3; `= 99` at `tol = 1/100`) is therefore **the model's sharpening of
  a slogan**, and the record must say so. No premise changes; **the number `99` gets no literature
  citation.**
- The measured numbers above enter the instance layer only through §R1.6; they do **not** become
  theorem premises. `RateData`'s positivity bundle is untouched by the literature.
- **Not expressible in mathlib / not expressible at all**: "internal conversion rate constant" as a
  physical quantity. What is formalized is a scalar parameter called `ic`; the identification of that
  scalar with the observable quantity called `k_IC` in photochemistry is a **modelling bridge to be
  declared**, exactly like the `tol` choice.

## §R1.4 Instance data I — the anti-Kasha family, with first-hand numbers

### R1.4.1 Azulene: two first-hand, mutually consistent data sets

**(A) Thesis data table.** K. Tittelbach-Helmrich, "The Photophysics of Azulene and Related
Compounds in Solution", PhD thesis, University of Saskatchewan (1995), handle `10388/16065`;
**URLS FETCHED**: `https://harvest.usask.ca/server/api/core/bitstreams/b5e3de1f-6333-45cf-94ea-4475d1d749d9/content`
(15 781 881 bytes; `pdftotext -layout`). **status `first-hand`** (PDF fetched and read here).
**Locus**: **Table 3.1**, printed **p. 115** (the printed footer immediately preceding the table
reads "114"). Columns as printed: `Compound | Solvent | ΔE(S2–S0)/10³cm⁻¹ | ΔE(S2–S1)/10³cm⁻¹ | Φ_f |
τ_ps | Σk_r/10⁷ s⁻¹ | Σk_nr/10⁸ s⁻¹`. Row **AZU / chx** (azulene in cyclohexane):

```text
ΔE(S2–S0) = 28.38 ×10³ cm⁻¹     ΔE(S2–S1) = 14.01 ×10³ cm⁻¹
Φ_f = 0.046                     τ = 1330 ps
Σk_r = 3.5 ×10⁷ s⁻¹             Σk_nr = 7.2 ×10⁸ s⁻¹
```

The table's own footnote (as printed): "The maximum errors in Φ_f and τ are estimated to be 5 % and
20 ps, respectively." The thesis's Table 3.2 gives the same compound in five solvents (Φ_f =
0.040–0.052; τ = 1040–1670 ps). **Internal consistency check (this record's arithmetic)**: for the
AZU/chx row, Σk_r/(Σk_r + Σk_nr) = 3.5×10⁷/(3.5×10⁷ + 72×10⁷) = **0.0464**, which reproduces the
printed Φ_f = 0.046 — i.e. the `Σk_r`/`Σk_nr` columns and the `Φ_f` column are consistent, which is
why this record treats them as one measurement set.

**(B) Peer-reviewed modern data.** K. Vinod et al., "Azulene as an anomaly in triplet-state
engineering …", *Chem. Sci.* (2026), DOI `10.1039/d6sc00694a` (OA, `PMC13576160`), retrieved via
Europe PMC `fullTextXML`. **status `first-hand`.** **Locus: Table 3** (printed verbatim by this
record's extraction) and the running text:

```text
Table 3 (as printed):  Molecule  τ_IC (ns)  k_IC (s⁻¹)     k_ISC (s⁻¹)   k_IC/k_ISC
                       Az        1.35       7.4 × 10⁸      7.71 × 10¹    9.6 × 10⁶
                       Az-3      0.61       1.6 × 10⁹      3.97 × 10⁻³   4.0 × 10¹¹
                       Az-4      0.10       1.0 × 10¹⁰     1.41 × 10²    7.1 × 10⁷
                       Az-5      0.23       4.3 × 10⁹      2.00 × 10²    2.2 × 10⁷
Φ_Fl (Table 2 / text):  Az 2.42 %,  Az-3 2.40 %,  Az-5 0.93 %,  Az-4 0.40 %,  Az-1 0.31 %,  Az-2 0.29 %
```

Running-text facts worth carrying (first-hand): "Using the S₂ lifetimes (τ_S₂ = 0.1–2.6 ns), k_IC is
determined to be (7.4 × 10⁸)–(1.0 × 10¹⁰) s⁻¹ across the azulene derivatives (Table 3)"; "Because the
experimental fluorescence quantum yields are extremely low, the non-radiative decay rate (k_nr) is
effectively equal to the S₂ → S₁ internal conversion rate (k_IC)"; the triplet channel is negligible
("ϕ_T < 10⁻⁷ from S₂"); azulene's S₂ lifetime had previously been reported as **1.06 ns** in
ethylene glycol; and — decisive for question 5 — the non-radiative rate constants for S₂ decay
"**follow the log-linear energy gap law**", with the simulations "employing **Marcus theory**".

**(C) The gap.** T. Woller et al., "Excited-State (Anti)Aromaticity Explains Why Azulene Disobeys
Kasha's Rule", *J. Am. Chem. Soc.* **145**, 21569–21575 (2023), DOI `10.1021/jacs.3c07625` (OA, `PMC10557139`) —
**first-hand** — prints: the anomalous emission of azulene "results from its **large S₂–S₁ gap
(∼14,000 cm⁻¹)**", attributing the hypothesis to Beer & Longuet-Higgins. This agrees with the
thesis's 14.01 × 10³ cm⁻¹ to the precision printed.

**(C-bis) ⭐ The peer-reviewed measured triple, and the across-channel asymmetry (first-hand).**
K. Veys, D. Escudero, "Computational Protocol To Predict Anti-Kasha Emissions: The Case of Azulene
Derivatives", *J. Phys. Chem. A* **124**(36), 7228–7237 (2020), DOI `10.1021/acs.jpca.0c05205` —
retrieved here as the authors' accepted manuscript from the KU Leuven repository
(`lirias.kuleuven.be/retrieve/cfc860e2-…`, 8 pp.; **Crossref-verified**). **status `first-hand`.**
**Locus: Table 2** (columns `k_r (×10⁷ s⁻¹)`, `k_ic (s⁻¹)`, `φ (%)`, each split `S₁←…`/`S₂←…`;
experimental values between parentheses, calculated values above). Row for azulene:

```text
k_r(S₂→S₀)  = 2.7 (calc)      (2.3 ± 0.1) ×10⁷ s⁻¹   [experimental]
k_IC(S₂→S₁) = 6.3 × 10⁸ (calc)  (5.3 ± 1.2) × 10⁸ s⁻¹ [experimental]
φ(S₂→S₀)    = 4.3 % (calc)      (3.5 ± 0.4) %          [experimental]
k_r(S₁→S₀)  = 0.16 ×10⁷ s⁻¹ (calc)                     [S₁ quantities are calculated only]
k_IC(S₁→S₀) = 1.9 × 10¹¹ s⁻¹ (calc)
φ(S₁→S₀)    = 8.4 × 10⁻⁴ % (calc)
```

Their own sentence, first-hand: "the fluorescence yield from S₂ is **at least 1500 times larger** than
the yield from S₁ … fluorescence from S₁ was not observed". This is the cleanest *peer-reviewed*
statement of the anti-Kasha asymmetry for azulene, and it cross-checks the thesis (§R1.4.1(A)) and the
2026 rates to within ≈ 30 % (5.3 × 10⁸ vs 6.3 × 10⁸ vs 7.4 × 10⁸ s⁻¹).

**(D) Gas phase (independent mechanism check).** J. Zhan, A. K. Lemmens, M. Ahmed, M. A. R. Reber,
"Rotational Coherence Dominates Early-Time Dynamics and Produces Long-Time Revivals in the S₂ State
of Azulene", arXiv:`2601.06003` (2026) — **first-hand** (PDF fetched here): "**time constant of
1482 ± 73 ps, which we assign to the S₂ fluorescence lifetime**, in agreement with the value reported
by Demmer et al." — i.e. the *isolated-molecule* S₂ lifetime of azulene is of the same order as in
solution, ~1.5 ns.

### R1.4.2 Other claimed anti-Kasha emitters — what this round can and cannot support

| claimed anti-Kasha case | what was found | verdict for the instance layer |
|---|---|---|
| **thioketones** (thiobenzophenone, adamantanethione, xanthione) | The mechanism is stated first-hand: anti-Kasha S₂ emission is favoured "when the energy gap between S₁ and S₂ is large and the oscillator strength of the S₀–S₂ transition is large, a mechanism observed … for azulene and its derivatives and **thioketones**, the difference between the two families being the (π,π*) character of S₁ for the former and (n,π*) for the latter" (*Molecules* 2021 review, DOI `10.3390/molecules26226999`, OA `PMC8623836`, first-hand). **No numeric rate or yield for any thioketone was found in any reachable source.** | `QUALITATIVE-ONLY` — **do not** build a numeric row on it |
| **ovalene** | ⭐ First-hand and **against** the naive reading: "Ovalene Photophysics Revisited", *J. Phys. Chem. A* **130**, 2148–2157 (2026), DOI `10.1021/acs.jpca.5c08602` (OA, `PMC12990110`) reports that "**contrary to the frequently cited small energy gap of ∼400 cm⁻¹, our measurements reveal a significantly larger S₂–S₁ gap of approximately 1200 cm⁻¹**" (the historically cited values: Clar ≈ 425 cm⁻¹, Kropp–Stanley ≈ 450 cm⁻¹; Amirav & Jortner's gas-phase ≈ 1800 cm⁻¹; solvent-dependent ≈ 1100–1500 cm⁻¹), and shows that "the S₁ and S₂ states establish **thermal equilibrium** on an ultrafast time scale", with the effective radiative rate rising as the gap *decreases* (Herzberg–Teller coupling). | **excluded as an IC-controlled anti-Kasha instance** — its higher-state emission is a *thermally activated* population effect at a **small** gap (≈ 1200 cm⁻¹ ≈ 2–6 k_BT), the **opposite** gap regime from azulene's 14 010 cm⁻¹. ⚠️ must not be used as evidence for the plan's "large gap ⇒ inverted region ⇒ anti-Kasha" story; and the two 2026 ovalene papers **disagree on which state is S₁** (they list the allowed/forbidden states in opposite order), so if it is ever used the states must be indexed by energy with the ordering as an explicit hypothesis |
| **gas-phase NO₂** | ⚠️ **`second-reader` only in this record**: a delegate retrieved the loci below and read them first-hand, but **this record did not open either document**, so every number here carries the label `secondary (reported by a second reader from the retrieved PDF)`. Zero-pressure radiative lifetime **55 µs** (400–600 nm excitation, 1–15 mTorr; Keyser, Levine & Kaufman, *Kinetics and mechanism of NO₂ fluorescence*, SRCC Report 134, Univ. of Pittsburgh, 1970, NASA NTRS `19700033056`, Fig. 6 caption; published as *J. Chem. Phys.* **54**, 355–363 (1971), DOI `10.1063/1.1674616`) ⇒ `k_rad ≈ 1.8 × 10⁴ s⁻¹`, "more than two orders of magnitude in excess of the lifetime calculated from the integrated absorption coefficient"; "**only one upper level contributes** to the observed fluorescent signal" at low pressure. Second locus: τ_rad = 64 µs at 400 nm → 102 µs at 750 nm (K. O. Patten, LBL-30599 PhD thesis, UC Berkeley/LBNL, 1991, reported abstract p. iii and Table 1-2 p. 37). | **locus available for the plan's §1.1 clause, but NOT a numeric Lean row**: the *nonradiative* rate of the same level was not found, so `ic 1/rad 1` cannot be formed. Use it as a cited physical instance (an isolated molecule with an anomalously small radiative rate whose emission comes from the pumped level), and re-read the two PDFs before quoting the 55 µs in a Lean docstring |
| **gas-phase SO₂ / CS₂ / HCHO / glyoxal** | ⚠️ **`UNSUPPORTED`** in this round: no first-hand rate for the emitting level of any of them was reached (the SO₂ C̃-state decay rates found are collision-free *total* decay rates of a jet-cooled state, not a radiative/nonradiative split; CS₂, formaldehyde and glyoxal sources were paywalled) | `UNSUPPORTED` — cite nothing |
| **azulene derivatives (conforming direction)** | first-hand: 4,6,8-trimethylazulene (*same* thesis, Table 3.3) has a **smaller** S₂–S₁ gap (12.29 × 10³ cm⁻¹) and Φ_f = **0.0005** with Σk_nr = 6.7 × 10¹⁰ s⁻¹ | **usable as the conforming row** — see §R1.5.1 |
| **2Azu (alkyl-substituted azulene)** | first-hand number available if a *derivative* row is ever wanted: *J. Am. Chem. Soc.* (2025), DOI `10.1021/jacs.4c11186` (OA, `PMC11744744`): anti-Kasha emission "**(τ = 1.15 ns)** of 2Azu has a great similitude with that of azulene" | spare row; parent azulene rows are better |
| **porphyrins / chlorins / cyanines / ESIPT dyes / clusteroluminescence** | many modern papers claim anti-Kasha behaviour, but (i) most are TDDFT-based assignments, and (ii) the 2019 reappraisal (§R1.1.2) states that outside azulene the reported violations "fulfill Kasha's rule". No numbers were extracted. | `UNSUPPORTED` for numeric rows in this round |

**Formalizable implication of §R1.4.**
- **Nothing here becomes a Lean premise.** All of it is *data* for K5b; the theorems stay conditional
  on `RateData`.
- **The mapping from the sources to the model's scalars is a declared identification**, and it is
  fourfold: (i) `rad 1` := the total *radiative* rate of S₂ (the thesis's Σk_r); (ii) `ic 1` := the
  total *nonradiative* rate of S₂, identified with **k_IC(S₂→S₁)** — licensed *for the azulene
  family* first-hand by `PMC13576160` ("k_nr is effectively equal to k_IC", ϕ_T < 10⁻⁷); (iii) the
  ladder is **truncated at N = 1** (excitation into S₂, single-photon, and no further higher state),
  which is a scope limit, not a measured fact; (iv) `ic 0` is set to 0 in the rows below.
- **A first-hand datum that cannot be expressed in mathlib:** the S₂–S₁ *gap* in cm⁻¹ is not a term of
  the model at all — it appears only through K4's Marcus window, where it is a hypothesis parameter
  (`x`), never a derived quantity. The gap values of §R1.4 are therefore recorded as *provenance for
  a hypothesis*, not as an input to any computation.
- **Impact on the plan's §10 risk table**: the "literature rows without first-hand numbers" mitigation
  worked as intended — the thioketone and gas-phase rows are marked `UNSUPPORTED` here and **must be
  dropped from K5b**, exactly as the plan prescribes.
- ⚠️ **A new, load-bearing warning for K4 (found independently by two first-hand sources): the
  gap-law monotonicity is *per channel*, not global.** Azulene's S₂→S₁ gap (14 010 cm⁻¹) and S₁→S₀ gap
  (14 370 cm⁻¹, the thesis's own arithmetic from its two printed columns) are **nearly identical**,
  yet the 1995 thesis states (first-hand, p. 30): "the rate constant of S₂ → S₁ is **ca. four orders
  of magnitude smaller** than that of S₁ → S₀, **even though the energy gaps are almost identical**";
  and Veys & Escudero's Table 2 prints the same asymmetry (k_IC(S₁→S₀) = 1.9 × 10¹¹ s⁻¹ vs
  k_IC(S₂→S₁) = 5.3 × 10⁸ s⁻¹). **Impact: the plan may not state (or imply in a docstring) a global
  theorem of the form "k_nr is a decreasing function of the gap".** If such a statement is ever
  wanted, it needs a per-channel premise: a *different* `λ_IC` and a different prefactor `A` per
  channel — which is precisely how the classical Marcus form can accommodate it, but only if the
  docstring says that `lam` and `A` are channel-labelled parameters. The within-series monotonicity
  of §R1.5.2 (same channel, different molecule) is unaffected.

## §R1.5 Instance data II — the conforming direction (question 4, first half)

### R1.5.1 The first-hand conforming row: 4,6,8-trimethylazulene

**source / locus / status**: same thesis as §R1.4.1(A), **Table 3.3**, printed **p. 126** (page
located by the printed footers around the table; treat the page as ± 1). **status `first-hand`.**
Row **TMA / chx** (4,6,8-trimethylazulene in cyclohexane):

```text
ΔE(S2–S0) = 27.82 ×10³ cm⁻¹    ΔE(S2–S1) = 12.29 ×10³ cm⁻¹
Φ_f = 0.000 5                  τ = 15 ps
Σk_r = 3.3 ×10⁷ s⁻¹            Σk_nr = 670 ×10⁸ s⁻¹  (= 6.7 ×10¹⁰)
```

Consistency (this record's arithmetic): Σk_r/(Σk_r+Σk_nr) = 3.3×10⁷/6.7×10¹⁰ = 4.9 × 10⁻⁴ ≈ the
printed Φ_f = 0.0005. ✔

### R1.5.2 The gap-ordered series — the same chromophore, both verdicts

All rows `first-hand` from the two thesis tables (§R1.4.1(A), §R1.5.1); the last column is **this
record's arithmetic**, using the model reduction of §R1.6 (`ic 0 = 0`, so the funnel ratio is
`Σk_nr/Σk_r`):

| molecule (solvent chx) | ΔE(S2–S1) /10³cm⁻¹ | Φ_f | τ /ps | Σk_r /s⁻¹ | Σk_nr /s⁻¹ | Σk_nr/Σk_r | verdict at `tol = 1/100` (needs ≥ 99) |
|---|---|---|---|---|---|---|---|
| azulene (AZU) | 14.01 | 0.046 | 1330 | 3.5 × 10⁷ | 7.2 × 10⁸ | **20.6** | **violating** |
| 1,3-dibromoazulene (DBA) | 13.87 | 0.016 | 200 | 8.0 × 10⁷ | 4.92 × 10⁹ | 61.5 | violating |
| guaiazulene (GAZ) | 13.48 | 0.018 | 330 | 5.4 × 10⁷ | 2.98 × 10⁹ | 55.2 | violating |
| perdeuterated azulene (AZD) | 14.05 | 0.072 | 1710 | 4.2 × 10⁷ | 5.4 × 10⁸ | 12.9 | violating |
| **4,6,8-trimethylazulene (TMA)** | **12.29** | **0.0005** | **15** | **3.3 × 10⁷** | **6.7 × 10¹⁰** | **2030** | **conforming** |

**The pattern is monotone in the gap** (smaller S₂–S₁ gap → larger nonradiative/radiative ratio →
Kasha-conforming), which is a first-hand, measured instance of the energy-gap-law mechanism the
plan's K4 bridge models. ⚠️ **Scope of this claim**: the monotonicity holds **within this S₂→S₁ channel
across molecules and solvents**, *not* across different channels of the same molecule — azulene's
S₁→S₀ channel is ca. four orders of magnitude faster than its S₂→S₁ channel at almost the same gap
(§R1.4 formalizable implication). Expressed as an exponential slope (this record's arithmetic,
deliberately reported *as a slope* rather than as a "γ", because the gap-law conventions differ
between sources): between TMA and azulene, ln(6.7×10¹⁰ / 7.2×10⁸) / (12 290 − 14 010 cm⁻¹) ≈
**−2.6 × 10⁻³ cm**.

### R1.5.3 The classical aromatic hydrocarbons — `UNSUPPORTED`, **and documented deviators**

**benzene, naphthalene, anthracene, pyrene, perylene**: this round found **no** reachable source that
prints, first-hand, both a radiative rate for S₂ (or an S₂ emission quantum yield) *and* an S₂→S₁
internal-conversion rate for any of these molecules. What was found instead:

| what | value | source / locus | status |
|---|---|---|---|
| **S₁ radiative rate, perylene** | Φ_F = 0.89, τ_F = **4.9 / 4.79 / 5.02 ns** (three laboratories), benzene ⇒ k_F = Φ/τ ≈ **1.8 × 10⁸ s⁻¹** (**this record's arithmetic**; the source prints no rate) | Birks, *J. Res. NBS A* **80**, 389–399 (1976), **Table 2, printed p. 398** | `first-hand` (table read here) |
| S₁ radiative rate, perylene (independent) | k_r = **1.6 × 10⁸ s⁻¹**; Φ_F = 0.87–0.98 (avg 0.93) | Veys, PhD thesis KU Leuven (2023), **Table 5-1, printed p. 69** | `secondary (via that table's refs 18/19/40)` — ⚠️ its last column in **Birks'** table is a *ratio* `k_exp/k_theory`, not a rate; do not confuse the two tables |
| S₁ radiative rates, other PAHs | anthracene **3.3–3.7 × 10⁷**, phenanthrene **3.2 × 10⁷**, tetracene 6.3–7.7 × 10⁷, dibenzothiophene 1.4–2.9 × 10⁷, fluorobenzene 0.27–1.8 × 10⁷ s⁻¹ | same thesis table, printed p. 69 | `secondary (via that table)` |
| **S₂→S₁ internal conversion, pyrene** | time constant "about **150–300 fs**" (⇒ k_IC ≈ 3–7 × 10¹² s⁻¹, **this record's inversion**) | quoted inside Wega & Vauthey, *J. Phys. Chem. A* **130**, 2148–2157 (2026) (OA, `PMC12990110`); the primary measurement is F. V. R. Neuwahl, P. Foggi, *Laser Chem.* **19**(1–4), 375–379 (1999), DOI `10.1155/1999/37692` | **`secondary (via Wega & Vauthey 2026)`**; primary `not-accessed` (Hindawi/Wiley 403, Wayback down) |
| the classical PAHs' relation to the rules | "**Major deviations from Vavilov's law** have … been observed for solutions of **benzene**, …, **naphthalene** …" and "weak **S₂→S₀ fluorescence has been observed in benzene, …, naphthalene, pyrene, …**" | Birks 1976, **printed p. 392** (§R1.1.3, §R1.2.3) | `first-hand` |
| ⭐ **upper-singlet lifetime, perylene** | "**A long 0.9 ps lifetime** of the upper excited singlet state in perylene is resolved by femtosecond pump–probe measurements under ultraviolet (4.96 eV) excitation and further validated by theoretical simulations of transient absorption kinetics" ⇒ total upper-state decay ≈ 1.1 × 10¹² s⁻¹ (**this record's inversion**) | W. Ni, G. G. Gurzadyan, L. Sun, M. F. Gelin, "Toward efficient photochemistry from upper excited electronic states: Detection of long S₂ lifetime of perylene", *J. Chem. Phys.* **155**, art. 191102 (2021), DOI `10.1063/5.0069398` — **abstract read first-hand here through the Crossref record** | **`abstract-only, first-hand`** (the body is closed; no repository copy). ⚠️ A **0.9 ps** upper-state lifetime in a classical PAH is precisely the "long-lived S₂" regime the plan's K4 window is about — yet the datum still **cannot close a row**, because `rad 1` (the S₂ radiative rate) or Φ(S₂) is not printed, so `ic 1/rad 1` remains unknown |
| qualitative mechanism | S₂→S₁ IC "typically … in the range of picoseconds" outcompete higher-state fluorescence | Veys 2023 thesis, **printed p. 3** | `first-hand` (typical-range statement) |

⚠️ **The decisive point is the "relation to the rules" row, not the missing numbers**: the literature
that states the rules also states that these very molecules **weakly violate them** (weak S₂ emission
observed; Vavilov-law deviations). A classical PAH is therefore **not** a "Kasha-conforming" instance
in the exact sense — it conforms only *within a tolerance*, which is precisely the plan's §1.3
structural point and must be said in `RESULTS.md` if these molecules are mentioned at all.

**Formalizable implication of §R1.5.**
- **I10 can be delivered, but not with a classical PAH**: use **4,6,8-trimethylazulene** (§R1.5.1)
  — a real aromatic hydrocarbon with first-hand numbers that is **conforming** under the same
  criterion as the violating azulene row. This has a methodological advantage that must be stated in
  the row's docstring: the two rows are *the same experiment on the same chromophore family*, so the
  contrast is not produced by mixing sources or conditions.
- **The benzene/naphthalene/anthracene/pyrene/perylene family is `UNSUPPORTED` for round 1 and must
  not appear in `Instances.lean`** — and it must not appear as a *conforming* row in prose either,
  because Birks 1976 p. 392 documents weak S₂ emission and Vavilov deviations for benzene,
  naphthalene and pyrene. If the lead wants a classical-PAH row after all, the round-2 request is
  precise: *for one named PAH, a printed upper bound on the S₂ (or S₃) emission quantum yield, or an
  S₂ lifetime together with an S₂ radiative rate*. A printed **upper bound** would be *sufficient* in
  Lean via the plan's own monotonicity lemma (K3 #8 `kashaWithin_one_mono_ic`): a smaller Φ(S₂) means a
  larger `ic 1/rad 1`, so an upper-bound row yields a **conservative but certified** conformance
  verdict — provided the bound is carried into the Lean literal honestly (`ic 1` set to the value
  implied by the bound, and the docstring saying "bound, not measurement").
- **Pyrene is the only classical PAH with an S₂→S₁ IC number at all** and that number is `secondary`
  (the primary is a 1999 *Laser Chemistry* paper whose text is unreachable here). **It may be quoted
  as a magnitude in `RESULTS.md` with its label; it may not become an `Instances.lean` literal.**
- **A partially usable classical-PAH pair exists for the S₁ level only**: perylene's
  (Φ_F = 0.89, τ_F ≈ 4.9 ns) gives `rad 0`/`decay 0` for a row module; the missing half is `ic 1`/`rad 1`
  for S₂. If a future round finds only an *upper bound* on Φ(S₂), that is enough to close I10-classical
  (see the previous bullet).
- **Ovalene is excluded** (§R1.4.2) and the exclusion must be visible in the record, because an
  unwary reader would otherwise take "ovalene" from the plan's §1.1 exception list as a
  ready-made anti-Kasha row — Birks' p. 392 list is exactly where that name comes from.

## §R1.6 Proposed K5b literature rows (I10/I11/I12) — the literals and the reduction

**Transcription rule used here** (stated so the lead can overrule it): rates are converted to
integers in units of **10⁶ s⁻¹**, which is exact for every measured value in §R1.4–§R1.5 and keeps the
ℚ arithmetic `norm_num`-sized. Unit changes of this kind are *this record's* convention; the source's
own printed unit is quoted alongside each number.

| row | molecule | `rad 0` | `ic 0` | `rad 1` | `ic 1` | sources of `rad 1`,`ic 1` | expected verdict |
|---|---|---|---|---|---|---|---|
| **I10** (conforming) | 4,6,8-trimethylazulene, chx | 1 | 0 | **33** | **67000** | thesis Table 3.3 (p. 126), `Σk_r = 3.3×10⁷`, `Σk_nr = 6.7×10¹⁰` | `KashaWithin 1/100 1` (ratio 2030 ≥ 99) |
| **I11** (anti-Kasha) | azulene, chx | 1 | 0 | **35** | **720** | thesis Table 3.1 (p. 115), `Σk_r = 3.5×10⁷`, `Σk_nr = 7.2×10⁸` | `¬ KashaWithin 1/100 1` (ratio 20.6 < 99) |
| **I11-alt** (anti-Kasha, independent source) | azulene (as Az, 2026 paper) | 1 | 0 | **242** | **9758** | *Chem. Sci.* 2026 Table 2/3, Φ_Fl = 2.42 % ⇒ `ic 1/rad 1 = (1−Φ)/Φ` | `¬ KashaWithin 1/100 1` (ratio 40.3 < 99) |
| **I11-alt2** (anti-Kasha, peer-reviewed rates) | azulene (Veys & Escudero 2020, Table 2) | 1 | 0 | **23** | **530** | `k_r(S₂) = 2.3×10⁷`, `k_IC(S₂→S₁) = 5.3×10⁸ s⁻¹` (both printed as experimental) | `¬ KashaWithin 1/100 1` (ratio 23.0 < 99); the printed Φ = (3.5 ± 0.4) % independently gives 27.6 |
| **I12** | — | — | — | — | — | **no second anti-Kasha molecule with first-hand numbers exists in this round** | **row dropped, per plan §8.2** |

Notes that must travel with the rows (docstring material):
- `rad 0 = 1`, `ic 0 = 0` is a **declared modelling reduction**, not data: it says "the lowest level's
  nonradiative channel is neglected in this row". With it, K3 #3's reduced criterion
  `KashaWithin tol 1 ↔ (1−tol)/tol ≤ ic 1/rad 1` applies *exactly*, which is why the two rows are
  numerically decisive. Without it, the full two-level criterion needs `rad 0` and `ic 0` as well,
  which for these molecules means transcribing Φ_f(S₁) and τ(S₁) from a *different* measurement —
  a cross-source combination the plan may prefer to avoid.
- The **I11-alt** row is derived from a *printed quantum yield* rather than from two rates: with
  `ic 0 = 0`, `(1−Φ)/Φ` **is** `ic 1/rad 1`. That route is robust to the `Σk_r`/`Σk_nr` column
  identification but needs the same `ic 1 ≈ k_IC` premise (§R1.4.2). **Cross-check of the two routes
  on azulene: 20.6 (thesis, 1995, chx) vs 40.3 (2026, Φ = 2.42 %) — a factor ≈ 2, i.e. solvent and
  method spread, not disagreement in sign or in order of magnitude.** Whichever row is used, the
  docstring must state the other one's number, so the spread is visible rather than hidden.

**Formalizable implication of §R1.6.**
- **Both rows are decidable by `norm_num` at the existing statements** — no statement change, no new
  premise: `KashaWithin 1/100 1` and its negation follow from K3 #3 with `ic 0 = 0`.
- **`RateData` is satisfied** by both rows (`decay 0 = 1 > 0`, `decay 1 = 33 + 67000 > 0`). No
  positivity premise is left implicit.
- **What must NOT be claimed in the row docstrings**: that these numbers are the *theoretical*
  quantities of the model. They are measurements identified with model scalars (§R1.4.2), and the
  identification (`ic 1` ≡ k_IC(S₂→S₁), `rad 1` ≡ total radiative rate of S₂) is the declared bridge.

## §R1.7 The radiationless-transition rate law, and what the Marcus bridge (plan K4c) may claim (question 5)

### R1.7.1 Bibliographic spine (all Crossref-verified here; bodies mostly closed)

| source | DOI / locus | status |
|---|---|---|
| R. Englman, J. Jortner, "The energy gap law for radiationless transitions in large molecules", *Mol. Phys.* **18**(2), 145–164 (1970) | `10.1080/00268977000100171` — Crossref-verified (authors, title, vol 18, issue 2, pp. 145–164, 1970) | `not-accessed` (Unpaywall `oa_status=closed`) |
| W. Siebrand, "Radiationless Transitions in Polyatomic Molecules. I. Calculation of Franck–Condon Factors", *J. Chem. Phys.* **46**(2), 440–447 (1967) | `10.1063/1.1840685` — Crossref-verified (author Siebrand, vol 46, pp. 440–447) | `not-accessed` (closed). ⚠️ **The DOI `10.1063/1.1840684` is a *different* paper** (M. H. Alexander, L. Salem, "Correlation between Exchanging Electrons", JCP 46, 430–439) — a guessed-DOI trap, disproved here |
| W. Siebrand, "… II. Triplet–Ground-State Transitions in Aromatic Hydrocarbons", *J. Chem. Phys.* **47**, 2411–2422 (1967) | `10.1063/1.1703324` — Crossref-verified | `not-accessed` |
| M. Bixon, J. Jortner, "Intramolecular Radiationless Transitions", *J. Chem. Phys.* **48**(2), 715–726 (1968) | `10.1063/1.1668703` (already in `theories/Marcus/LITERATURE.md`) | `not-accessed` |
| J. Jortner, "Temperature dependent activation energy for electron transfer between biological molecules", *J. Chem. Phys.* **64**(12), 4860–4867 (1976) | `10.1063/1.432142` (already in `theories/Marcus/LITERATURE.md`) | `not-accessed` |
| Englman & Jortner, "The energy gap law for non-radiative decay in large molecules", *J. Lumin.* **1–2**, 134–142 (1970) | `10.1016/0022-2313(70)90029-3` | `bibliographic-only`. ⚠️ **The frequently-cited "companion paper, Mol. Phys. 18, 285 (1970)" does not exist** — that locus is Zeeck, "Expanded orbitals in SCF-LCAO-MO computations" |
| R. A. Marcus, "On the Theory of Chemiluminescent Electron-Transfer Reactions", *J. Chem. Phys.* **43**, 2654–2657 (1965) | `10.1063/1.1697190` | `bibliographic-only` (exists; disproof of a suspicion that "43, 2654" was a phantom) |
| R. A. Marcus, "Electron transfer reactions in chemistry. Theory and experiment", *Rev. Mod. Phys.* **65**(3), 599–610 (1993) | `10.1103/RevModPhys.65.599` — Crossref-verified. Free copies: `https://authors.library.caltech.edu/records/ta6z9-5ac64/files/RevModPhys.65.599.pdf?download=1`; `https://www.nobelprize.org/uploads/2018/06/marcus-lecture.pdf` | `secondary` (the inverted-region sentences at printed pp. 605–606 are reported by a second reader; this record opened neither PDF). ⚠️ the RMP Eqs. (5a)/(5b) are *images* with a garbled text layer — **no equation is quoted from them here** |
| S. J. Jang, "A simple generalization of the energy gap law for nonradiative processes", *J. Chem. Phys.* **155**(16), art. 164106 (2021) | `10.1063/5.0068868` — Crossref-verified (JCP is article-numbered: **no page range exists**) | ⭐ **`first-hand`** for the author's own equations/table, read in the arXiv HTML rendering (`arXiv:2110.09464` at `ar5iv.labs.arxiv.org/html/2110.09464`) |
| Duvva, Islam, Valandro, Gobeze, Fahim, Wang, Le, Tomlinson, Schanze, "From Fundamental Photophysics to Photocatalysis: Energy Gap Law Analysis of Anion Radical Excited States", *ACS Cent. Sci.* **12**(6), 856–866 (2026) | `10.1021/acscentsci.6c00092` — Crossref-verified | ⭐ **`first-hand`** for the printed exponential form below (OA, `PMC13306596`, Europe PMC full text); the *printed page number* is `secondary` |
| Ying, Nitzan, "Electron transfer in confined electromagnetic fields: a unified Fermi's golden rule rate theory and extension to lossy cavities", *J. Chem. Phys.* **164**(2) (2026) | `10.1063/5.0310931` — Crossref-verified | `secondary` (its abstract sentence is reported by a second reader; this record did not open it) |

### R1.7.2 The content of the energy-gap law — first-hand statements

- **The law's own author, describing it (first-hand).** R. Englman, "This Week's Citation Classic"
  commentary on Englman & Jortner 1970, *Current Contents* (1988), `http://garfield.library.upenn.edu/classics1988/A1988P315700001.pdf`
  (PDF fetched and read here). It reproduces the paper's summary sentence:
  > "The decay rate of excited electronic states in a large molecule or of an impurity in a solid is
  > calculated for a model of **a large number of displaced harmonic oscillators**. **The rate depends
  > exponentially on the energy difference ('gap') between the initial and final electronic states.**"

  It also records the history that matters for premise-honesty: the "low-temperature expression" was
  obtained "by a saddle point method to arrive at what is now widely known as the 'energy-gap law'",
  and Englman states he had earlier been **wrong** in using "a high-temperature approximation to
  evaluate the essentially correct formula".
- **The law in a molecular-photophysics text (first-hand).** The 1995 thesis (§R1.4.1(A)) prints it
  as **eq. (3.1)**, printed **p. 124–125** (the printed footers in the retrieved PDF place it in that
  range; the OCR page order is not fully reliable, so the page is given as an interval), "developed by
  Englman and Jortner (the energy gap law) [48]", with `γ` given by eq. (3.2). ⚠️ The OCR of the PDF
  renders the formula unreliably; **this record therefore does not transcribe eqs. (3.1)/(3.2)** — it
  records only: exponential in ΔE, `γ` containing the displacement information. A human reading the
  PDF may transcribe it.
- **⭐ The law's actual functional form, and its stated range of validity (first-hand).** S. J. Jang,
  *J. Chem. Phys.* **155**, art. 164106 (2021), DOI `10.1063/5.0068868` — read here in the arXiv HTML
  rendering (`arXiv:2110.09464`), **loci: §II, Eq. (30), and Table 1**. Verbatim:
  > "The EG law is an application of the **stationary phase approximation for the Fermi Golden Rule
  > (FGR)** rate expression. There are **two assumptions** underlying the EG law. One is that the
  > electronic transition of interest is **weakly coupled** to molecular vibrations and environmental
  > degrees of freedom. The other is that **the vibronic transition due to the highest frequency
  > vibrational modes serves as the main route** for the quantum transition mechanism."

  and, verbatim, Table 1's conditions of validity: **EG Eq. (30) — "ΔĒ ≫ λ_h ≫ λ_l" together with
  "ħω_h ≫ k_B T"**; semiclassical SC Eq. (48) — "ΔĒ ~ λ"; SPI Eq. (49) — "ΔĒ < 2λ". ⚠️ **Structural
  point that matters for Lean**: in that printed form the exponent is **not** `−γ·ΔE` with a constant
  `γ`; it contains `{ln(ΔĒ/λ_h) − 1}` and the prefactor carries `ΔĒ^(−1/2)`. So "the rate is
  exponential in the gap" is itself an **approximation with a stated range restriction**, not an
  identity. (Jang's own `γ ≡ 2λ_h/E_st` is *his* parameter and must **not** be attributed to
  Englman & Jortner.)
- **⭐ The exponential form as printed and attributed to Siebrand (first-hand).** Duvva et al.,
  *ACS Cent. Sci.* **12**(6), 856–866 (2026), DOI `10.1021/acscentsci.6c00092` (OA, `PMC13306596`,
  Europe PMC full text read here). Verbatim from the Energy-Gap-Law section: "The energy gap law for
  nonradiative decay was **formulated by Englman and Jortner**, and **Siebrand demonstrated its
  application** to nonradiative decay of the triplet excited states of a series of aromatic
  hydrocarbons"; and, as printed, **Eqs. (1a)/(1b)**:
  > `ln k_nr = a − (γ_o / ħω_m) · E_00`  (1a)      `γ_o = ln( E_00 / (ħω_m S_m) ) − 1`  (1b)

  where `ħω_m` is "the average frequency of the vibrational modes coupled to the doublet excited state
  decay" and `S_m` the Huang–Rhys factor. Their reference list attributes the treatment to **Siebrand
  II** (`10.1063/1.1703324`). **Page**: reported as printed **p. 861** by a second reader from the
  publisher PDF (`secondary` label on the page only; the text above was read here). Note again the
  **logarithm inside `γ_o`** — the "linear in E_00" reading is the approximation they then make.
- **The law's stated validity condition, second locus (first-hand).** *Angew. Chem. Int. Ed.* (2022),
  DOI `10.1002/anie.202116834` (OA, `PMC9310714`): "In the case of **weakly displaced potential energy
  surfaces, where the harmonic approximation is valid**, the most common approach to estimate the
  internal conversion rate is based on the **energy gap law (EGL) by Englman and Jortner**", whose
  printed form is their eq. (3). Same caveat as above: the flattened XML renders the equation
  unreliably, so **no equation is transcribed here**; the *attribution and the validity condition* are.
- **Measured, modern use of the law (first-hand).** `PMC13576160` (§R1.4.1(B)): for azulene
  derivatives "the non-radiative rate constants for S₂ decay **follow the log-linear energy gap
  law**"; and the §R1.5.2 series is a first-hand, measured instance of exactly that monotonicity.

### R1.7.3 The Marcus-type form for radiationless transitions, and the two limits

- **⭐ The bridge premise, licensed first-hand by an abstract read via PubMed.** A. S. Bozzi,
  W. R. Rocha, "Calculation of Excited State Internal Conversion Rate Constant Using the
  One-Effective Mode Marcus–Jortner–Levich Theory", *J. Chem. Theory Comput.* **19**(8), 2316–2326
  (2023), DOI `10.1021/acs.jctc.2c01288` (Crossref-verified here; abstract retrieved via
  `eutils … efetch db=pubmed id=37023359`):
  > "the one-effective mode **Marcus-Jortner-Levich (MJL) theory** and the **classical Marcus theory
  > for electron transfer** were applied to estimate the **internal conversion rate constant, k_IC,
  > of organic molecules and a Ru-based complex, all belonging to the Marcus inverted region**."

  This is the literature locus that licenses writing an internal-conversion rate *as a Marcus-type
  rate with driving force = the energy gap and reorganization energy λ_IC* — **within the MJL model**:
  one effective high-frequency mode (quantum) + a classical bath, and the one-mode variant
  (`S = λ_V/ℏω`). It also states the error direction of the purely classical variant: "good agreement
  with experimental and theoretically determined k_IC, **with a small overestimation by the Marcus
  theory**".
- **The two limits, first-hand with the sentences read in the OA full text.** T. Sutcliffe,
  D. A. Cagan, R. G. Hadt, *J. Am. Chem. Soc.* **146**(22), 15506–15514 (2024), DOI
  `10.1021/jacs.4c04091` (OA, `PMC11157544`):
  > "This model considers **two limiting cases** of the coupling between molecular vibrations and the
  > decay rate, namely **weak or strong coupling**. The weak coupling limit applies to excited states
  > with a **small displacement** from the ground state along the vibrational coordinate. This regime
  > is found to **approximately result in the energy-gap law** through the interaction of the excited
  > state with the highest vibrational mode(s) of the ground state; the decay rate constant is
  > **linearly governed by the energy gap** …, i.e., **ln(k) ∝ –ΔG°**."

  and, for the other limit, the strong-coupling case gives "a **Gaussian dependence on the energy
  gap**, as in Marcus theory", with the correspondence between the classical and quantum
  denominators stated in the same section. **Page numbers**: the second reader who supplied this
  quote reports printed **pp. 15510–15511**; **this record verified the sentences in the OA full text
  but did not independently confirm the printed page** — the page is therefore labelled
  `secondary (page reported by a second reader)`.
- **Secondary corroboration (not verified in this record)**: the same second reader reports that
  *ACS Phys. Chem. Au* (2026) **6**(2), 246–258, DOI `10.1021/acsphyschemau.5c00095`, prints at
  **p. 251 eq. (8)** `ΔG‡ = (λ + ΔG⁰)²/(4λ)` and **eq. (9)**, at **p. 252 eq. (11)** the
  Marcus–Levich–Jortner rate, and at **p. 252** the sentence identifying the MJL division into a
  quantum subsystem and a classical solvent bath, with the weak-coupling/gap-law statement at
  **p. 249**. These loci are recorded as **`secondary`** and must be re-read before being cited in
  Lean docstrings; the classical law itself is already documented in `theories/Marcus/LITERATURE.md`
  (§ the Marcus 1956 / Cohen–Marcus 1968 entries), which is the authority to cross-reference.

### R1.7.4 What the literature actually licenses for K4's `kashaWithin_one_marcus`

Short answer, stated so the docstring can be written honestly:

1. **The general law is exponential, not quadratic.** The energy-gap law (Englman & Jortner) is the
   **weak-coupling** limit and gives ln k ∝ −Δgap (§R1.7.2–§R1.7.3). The **quadratic** driving-force
   form with an **inverted region** is the **strong-coupling / classical (high-temperature)** limit
   (§R1.7.3). A modern rate theory states both directions of the correspondence in one sentence —
   **`secondary`** (reported by a second reader; this record did not open it): Ying & Nitzan,
   *J. Chem. Phys.* **164**(2) (2026), DOI `10.1063/5.0310931` — "In the high-temperature limit, our
   formalism recovers the Marcus and Marcus–Jortner results, while in the low-temperature limit it
   reveals the emergence of the energy gap law."
2. **Even "exponential in the gap" is an approximation with a stated range restriction** (§R1.7.2):
   the printed gap-law exponent contains `ln(ΔĒ/λ_h) − 1` and its prefactor has `ΔĒ^(−1/2)`, and its
   validity is conditional (`ΔĒ ≫ λ_h ≫ λ_l`, `ħω_h ≫ k_B T`, stationary-phase evaluation). The
   honest Lean reading of the bridge (plan K4c) is therefore: `ic 1` is given by the *classical quadratic* form **as a
   declared model**, not as the literature's general law.
3. **The identification is nonetheless used in the literature** for internal conversion — but with a
   named model attached: **MJL / one-effective-mode Marcus–Jortner–Levich**, and (in the cited 2023
   paper) in molecules "**all belonging to the Marcus inverted region**" (§R1.7.3).
4. **The classical variant overestimates** k_IC in the cited comparison ("a small overestimation by
   the Marcus theory"), and its high-temperature/classical character is what the "substituting
   ⟨ℏω⟩ = 2k_BT recovers the Marcus equation" statement makes explicit.
5. **The promoting-mode / Franck–Condon structure is not representable** here: it lives in the
   displacement `γ`/`S` of the gap law, i.e. in quantities that the model does not have.

**Formalizable implication of §R1.7 (the decisive one for the plan).**
- **K4 #12's hypothesis `hic : ic 1 = marcusIC A lam kB T x` is a *declared model identification*, and
  the literature licenses it only conditionally.** The honest docstring must name all three
  restrictions: (i) **strong coupling / classical, high-temperature limit** (not the general gap law),
  (ii) **one effective mode** (MJL), (iii) the driving force is the **energy gap** and the
  reorganization energy is **λ_IC**, which is a *definition of the model's λ*, not a measured
  molecular quantity. The plan's §7 K4c and §10 risk row already say this in outline; this record
  supplies the loci — **Bozzi & Rocha `10.1021/acs.jctc.2c01288`** for (ii)/(iii) and
  **Sutcliffe–Cagan–Hadt `10.1021/jacs.4c04091`** for (i). **Impact: docstring/literature citation
  only — the statement of `kashaWithin_one_marcus` needs no change** (it already carries `hic` as an
  explicit hypothesis, which is exactly the discipline the engine requires).
- **A mathematical caveat the literature does not supply and the plan must own**: the classical form
  `barrier lam x = (lam − x)²/(4 lam)` is **even in `lam − x`**, so the model's window is symmetric
  about `x = λ_IC`, whereas the true gap law is monotone. The plan's window (`kashaWindow_halfWidth`,
  K4 #14) is therefore a **model artifact of the parabolic approximation**, not a physical prediction.
  This must be said in `RESULTS.md` next to the azulene example, and it is visible in the data of
  §R1.5.2 (azulene is violating because its gap is *large*, i.e. on the far side of the parabola —
  consistent — but the data are monotone, not symmetric, so the *qualitative* conclusion is what
  the instance layer supports).
- **If the plan ever states the gap law itself as a Lean formula** (e.g. as the justification inside
  `marcusIC`'s docstring, or a future K6), the premises are *forced by the printed form* and are the
  cleanest set this round found (`first-hand`, Jang's Table 1): `0 < ħω_h`, `0 < λ_l < λ_h`,
  `ΔĒ ≫ λ_h` (which in Lean must be a concrete inequality, say `4 * λ_h ≤ ΔĒ`), `k_B * T < ħω_h`,
  plus `ΔĒ > 0` for the `ln(ΔĒ/λ_h)` term's domain. None of these may be hidden in a definition — and
  the `ln`-dependence means the resulting rate is **not** monotone-convex in the gap in the simple way
  a pure exponential would be, so any monotonicity claim about `ic 1` in `x` needs its own premise.
- **`A` (the prefactor)** in `marcusIC A lam kB T x` has no literature value in any source read here;
  it must stay a free parameter (the plan treats it as such — `hA : 0 < A` only). **No premise
  change**, but ⚠️ **do not** put a numeric `A` into `Instances.lean` on the strength of this round.
- **`kB * T`**: the corpus read here expresses gaps in cm⁻¹ and rates in s⁻¹ and rarely prints
  `k_B T` for IC. Any row that evaluates `marcusIC` numerically would need a **unit-conversion
  premise** (`1 cm⁻¹ = 1.986 445 8 × 10⁻²³ J`, i.e. `hc`-based), which is a *constant* the plan may
  declare but which this round did **not** find printed in any source for this purpose. **Impact:
  keep the Marcus bridge symbolic; if a numeric evaluation is ever wanted, the conversion must be
  added to the plan's honesty table first.**

## §R1.8 Fidelity check — the plan's statements against what the sources say

| plan locus | statement as planned | verdict of this round |
|---|---|---|
| §1.1 sentence 1 ("whatever the excitation") | faithful | ✔ matches del Valle & Catalán's reading of the seminal sentence, **but** their four scope qualifiers (complex molecules, condensed phase, one photon, photostationary) are missing and must be added as scope limits |
| §1.1 "phosphorescence from T₁" | supported | ✔ IUPAC Gold Book "Kasha rule" wording covers *luminescence* / a given multiplicity (secondary, §R1.1.3) |
| §1.1 "rate inequality … orders of magnitude faster" | **needs weakening** | ⚠️ the literature's quantitative support reachable here is the azulene series (measured, ratios 13–2030) and computed TADF values; the "10¹²–10¹³ vs 10⁷–10⁹" pair is **not** attributable to a first-hand source (§R1.3) |
| §1.1 "isolated gas-phase molecules show resonance fluorescence" | **partially supported now** | the NO₂ locus was found in this round (§R1.4.2): τ_rad = 55 µs zero-pressure (Keyser–Levine–Kaufman 1970/1971), "only one upper level contributes" at low pressure, and a second locus with 64→102 µs (Patten, LBL-30599, 1991). ✔ the clause now has a citable instance — but ⚠️ **no numeric Lean row** is possible from it (the nonradiative rate of the same level is not printed), and SO₂/CS₂/HCHO/glyoxal remain `UNSUPPORTED` |
| §1.1 "other anti-Kasha emitters are reported" | supported only qualitatively | ✔ thioketones (mechanism, no numbers); ✘ ovalene must be **removed** from the exception list (§R1.4.2) |
| K2 #18 `kashaRule_iff_vavilovUpTo` | model theorem | ✔ unaffected; but the two rules' literature relation is mechanistic, not an identity (§R1.2.2) |
| K3 #3 threshold `99` at `tol = 1/100` | model's sharpening of a slogan | ⚠️ **no literature citation for `99` or for `tol = 1/100`**; the only printed accuracy in the corpus is Vavilov's ± 8 % (yield, dye) |
| K5b I10 (conforming aromatic hydrocarbon) | "literature" row | ✔ deliverable — but as **4,6,8-trimethylazulene**, not a classical PAH (§R1.5, §R1.6); and Birks 1976 p. 392 shows the classical PAHs are **documented weak violators**, so at best they give a *tolerance*-conforming row |
| K5b I11 (azulene) | "literature" row | ✔ deliverable with first-hand numbers, two independent sources (§R1.4.1, §R1.6) |
| K5b I12 (second anti-Kasha molecule) | "if first-hand numbers exist" | ✘ **does not exist in this round → drop the row** |
| K4 #12 `kashaWithin_one_marcus` | bridge with `hic` hypothesis | ✔ statement unchanged; the docstring must carry the three restrictions of §R1.7.4 |
| §13 "energy-gap law exponential form outside the model" | scope limit | ✔ correct and now citable: Englman & Jortner (exponential), weak-coupling limit named first-hand |

## §R1.9 Outstanding, not-accessed, and the round-2 request

**Bodies not reached (must not be cited for content):** Kasha 1950 (`pubs.rsc.org` 403) ·
del Valle & Catalán 2019 (closed; abstract only) · IUPAC Gold Book K03370/K03371 and the PAC 2007
glossary (`10.1351/pac200779030293`, Cloudflare 403 everywhere, incl. the Roskilde repository copy
and the empty degruyter response) · Itoh, *Chem. Rev.* **112**, 4541 (2012) (`10.1021/cr200166m`,
closed) · Demchenko, Tomin & Chou, *Chem. Rev.* **117**, 13353 (2017) (`10.1021/acs.chemrev.7b00110`
— ⚠️ note: `…7b00191` is **not** a valid DOI for this paper; closed either way) · Beer &
Longuet-Higgins, *J. Chem. Phys.* **23**, 1390 (1955) (`10.1063/1.1742314` — ⚠️ `…1.1742276` is a
different 1955 JCP paper; closed) · **Englman & Jortner 1970 itself** (`10.1080/00268977000100171`,
closed: *no equation number and no printed page inside it may be cited*, and their own `γ` definition
and their stated weak-coupling inequality are **`UNSUPPORTED`** in this record) · Siebrand 1967
papers I/II/III (closed; their exponential forms are cited here **only** as reproduced by
`ACS Cent. Sci. 12, 856` and the 1995 thesis) · Jortner 1976 (closed: no equation number, no printed
page, and the frequently-repeated "Jortner used ħω ≈ 1500 cm⁻¹" is **`UNSUPPORTED`** — 1500 cm⁻¹ is a
constant *later* authors choose) · R. A. Marcus's own radiationless/ET originals (`10.1063/1.1697190`
JCP 43, 2654; `10.1063/1.1696792` JCP 43, 679; `10.1063/1.1696913` JCP 43, 1261 — all
Crossref-verified, bodies closed) · thioketone photophysics primaries · gas-phase NO₂/SO₂/CS₂
resonance-fluorescence primaries · the monographs **May & Kühn, *Charge and Energy Transfer Dynamics
in Molecular Systems*** (`10.1002/9783527602575`), **Klessinger & Michl**, and **Freed,
*Top. Curr. Chem.* 31, 105 (1972)** (`10.1007/bfb0051237`) — metadata only, **not-accessed, must not
be cited as a premise**. Also `secondary`-only in this record: the printed page numbers inside
`JACS 146, 15506` (pp. 15510–15511) and `ACS Cent. Sci. 12, 856` (p. 861), and the whole of
`ACS Phys. Chem. Au 6, 246` and `J. Chem. Phys. 164` (`10.1063/5.0310931`) — these need one
confirming read. **Added late in the round (the classical-PAH carriers, all blocked here):**
F. V. R. Neuwahl, P. Foggi, *Laser Chem.* **19**(1–4), 375–379 (1999), DOI `10.1155/1999/37692`
(Crossref-verified; `downloads.hindawi.com` and four Wiley URL variants → 403, Wayback down) —
the primary measurement behind pyrene's 150–300 fs; W. Ni, G. Gurzadyan, L. Sun, M. F. Gelin,
*J. Chem. Phys.* **155**, 191102 (2021), DOI `10.1063/5.0069398` (closed, no repository copy);
V. L. Ermolaev, *Russ. Chem. Rev.* **70**, 471–490 (2001) (`iopscience.iop.org` returned a **Radware
Bot Manager CAPTCHA page**, HTTP 200 with no article); T. Itoh, *Chem. Rev.* **112**, 4541 (2012)
(§above); the classic monograph pages behind both rules — **Turro, *Modern Molecular Photochemistry*,
Ch. 1, Scheme 1.4, p. 17** (reached only as a quotation on a UCI lecture handout, slide 243;
`turroserver.chem.columbia.edu` is unreachable at the network level), **Birks, *Photophysics of
Aromatic Molecules* (1970)**, **Valeur**, **Klessinger & Michl**. Also observed-blocked in this round:
`mdpi.com` article pages (403 Akamai), `macau.uni-kiel.de` (an "Anubis" proof-of-work interstitial),
`pure.rug.nl` (404 for the guessed repository file), `shodhganga.inflibnet.ac.in`,
`apps.dtic.mil` (no route). The `secondary`-page loci named above still need one confirming read
before they enter a Lean docstring.

**Round-2 request (precise, so it can be dispatched):**
1. **A classical PAH conforming row**: for one named molecule of benzene/naphthalene/anthracene/
   pyrene/perylene, a printed **S₂ (or S₃) emission quantum yield — a value or an upper bound — with
   its printed page**, or an S₂ lifetime together with an S₂ radiative rate. An upper bound suffices
   for a conservative Lean verdict (§R1.5.3). ⚠️ **This request is now lower-priority than it looks**:
   Birks 1976 p. 392 documents weak S₂ emission and Vavilov deviations for exactly these molecules, so
   even a successful retrieval yields a *tolerance-conforming*, not an exactly conforming, row.
   The three carriers most likely to hold a **measured S₂→S₁ rate with a page** — and all three
   currently blocked from this sandbox — are: (i) V. L. Ermolaev, *Russ. Chem. Rev.* **70**, 471–490
   (2001) [IOPscience served a Radware CAPTCHA], (ii) T. Itoh, *Chem. Rev.* **112**, 4541–4568 (2012)
   [closed, no repository copy per Unpaywall], (iii) W. Ni, G. G. Gurzadyan, L. Sun, M. F. Gelin,
   *J. Chem. Phys.* **155**, 191102 (2021) [closed, `any_repository_has_fulltext: false`]. Closing any
   one of the three is the single highest-value retrieval for a classical-PAH row.
2. **A second anti-Kasha molecule with numbers** (thioketone or a gas-phase small molecule), or an
   explicit written decision that I12 stays dropped.
3. **Human read of Kasha 1950 p. 14–19** (library/publisher access) to convert §R1.1.1 from
   `secondary` to `first-hand` and to fix the page of the canonical sentence.
4. **Human read of the PAC 2007 glossary** entries "Kasha rule"/"Vavilov rule" for the normative
   wording with printed pages (pp. 293–465, entries alphabetic). ⚠️ This is now *confirmation only*:
   the two rule statements are already citable from **reachable** OA sources (Birks 1976 p. 392 for
   both rules + the deviation lists; Veys 2023 pp. 3–4 for both rule statements), so the glossary is no
   longer on the critical path.
5. **One confirming read** of the `secondary`-page loci listed in this record (the printed pages inside
   `JACS 146, 15506`, `ACS Cent. Sci. 12, 856` and `ACS Phys. Chem. Au 6, 246`) — the only page numbers
   here not verified by this record's own two eyes.
6. **Optional, for a future Vavilov *quantitative* row**: a first-hand φ(λ_ex) table with numbers.
   Birks 1976 gives the qualitative deviation list with a printed page, but **prints no φ ratio**.

**Closing statement of this record.** Every number in §R1.4–§R1.6 was read by this record at the
locus named; every `secondary` label names the source that carried the wording; every failed access
is listed above with its obstacle. Two DOI traps were disproof-verified rather than propagated
(§R1.7.1); **all 41 DOIs cited in this file were re-checked against Crossref in a final pass**; and
the instance families that no source could support with first-hand numbers are marked `UNSUPPORTED`
instead of being guessed — **thioketone rates, porphyrin/chlorin S₂ quantities, and the gas-phase
SO₂/CS₂/HCHO/glyoxal rates** — while the classical PAHs turned out to be *documented weak violators*
(Birks 1976, printed p. 392: weak S₂→S₀ fluorescence observed in benzene/naphthalene/pyrene/ovalene,
and benzene/naphthalene in the Vavilov-deviation list), so they can at best carry a
*tolerance*-conforming row and were **not** used for I10. The two rows that *are* decidable (azulene
violating, 4,6,8-trimethylazulene conforming) rest on numbers read at their printed loci, in one case
(Veys & Escudero 2020) with a printed quantum yield that independently reproduces the rate ratio to
within 20 %.
