# theories/BEP/LITERATURE.md — Bell–Evans–Polanyi: sources, statements, formalizable implications

> Owner: `literature_researcher` (engine role). This file is the authority for the loci and the
> wording of the Bell–Evans–Polanyi (BEP) principle used by `theories/BEP/plan.md`, and for the
> provenance of every number used by the instance layer `PhotoLean/BEP/Instances.lean`.
> Language: English (contract `proofs/ENGINE.yml`; the only bilingual file is `RESULTS.md`).
> Status: **round 1 — retrieval record delivered below** (§R1). Every dispatch item (a)–(d) is
> resolved: (a) IUPAC glossary read first-hand over all 182 printed pages; (b) Brønsted 1928 read
> (third-party OCR copy, provenance flagged) and Brønsted 1924 `not-accessed`; (c) Leffler 1953
> `not-accessed`, its equation reproduced at three OA loci (flagged as secondary, single group);
> (d) the complementarity identity located first-hand in peer-reviewed OA sources and in the IUPAC
> 2014 Technical Report, with the restriction that IUPAC itself attaches to it. Nothing in this file
> is a claim that was not read at the locus quoted; every `not-accessed` is stated explicitly.
> **No PDF is stored in this repository** — scratch is `/tmp/bep-work/`; every `URLS FETCHED` line
> is re-runnable. Language of quotes: as printed (including the source's own hyphenation/ligatures).

---

## Record format (every source entry carries)

1. `source` — author, year, journal, volume, pages, DOI (checkable).
2. `locus` — equation/table/page where the content is printed.
3. `status` — `first-hand` (verified in the text) or `not-accessed` (must not be cited for content).
4. `conclusion` — what the source actually says, in its own terms.
5. `formalizable implication` — which Lean premise/theorem of `theories/BEP/plan.md` it fixes,
   which physical approximation must be declared as an explicit premise, and what is out of scope.

## Required content of round 1

- primary sources (Evans–Polanyi, Bell, Semenov) with printed formulas;
- the modern normative statement (IUPAC glossary) and the definition of the transfer coefficient,
  Brønsted/Leffler coefficient and the complementarity relation;
- the derivation context (Marcus 1956; Cohen–Marcus 1968; Marcus 1968) for the barrier law and the
  slope ↔ transition-state-position identification;
- documented limitations and failure modes (curved BEP plots, inverted region, barrierless and
  diffusion-limited steps, family heterogeneity, tunneling/recrossing);
- a data table of at least four families with ≥ 2 (driving force, barrier) pairs in kJ/mol,
  each with provenance status, for the instance layer;
- a "Fidelity check" section judging the four formalized claims (i)–(iv) of the dispatch.

---

# §R1 — Round 1 retrieval record (2026-09-20)

Dispatch covered by this pass: (a) IUPAC glossary 2021 verbatim entries; (b) Brønsted 1924 + 1928;
(c) Leffler 1953; (d) the complementarity identity `β_f + β_r = 1` and its electrochemical analogue.
Items **not** in this dispatch (still outstanding for round 1, owner to be assigned): the **B5b data
table** of ≥ 4 families in kJ/mol, and the **derivation-context** entries for Marcus 1956 / Cohen–Marcus
1968 / Marcus 1968 — the latter already exist with printed loci in the sibling records
(`theories/Marcus/LITERATURE.md` records 1–4 and `theories/hammond/LITERATURE.md` S6–S11) and are only
cross-referenced here, not duplicated.

## §R1.1 Method, statuses actually achieved, and the block list

Read first-hand in this pass: the **publisher's version of record** of the IUPAC glossary (182 printed
pages, full text extracted and grepped), the JATS full text of *Chem. Sci.* **16**(37):17494 (OA), one
thesis (full text). Retrieved at bibliographic level only: the IUPAC Gold Book transfer-coefficient
entries and two *Chemistry International* notes (all Cloudflare-blocked bodies). The Brønsted 1924 and
1928 bodies and the Leffler 1953 body are reported in §R1.4/§R1.5.

**Blocked hosts (recorded as negatives, not as refutations)** — HTTP 403 Cloudflare challenge for
`curl` with a browser UA *and* for the harness fetch tool: `www.iupac.org`, `publications.iupac.org`,
`old.iupac.org`, `media.iupac.org`, `goldbook.iupac.org`, `mail.goldbook.iupac.org`,
`pubs.rsc.org`, `pmc.ncbi.nlm.nih.gov`, `europepmc.org/articles/*?pdf=render`. HTTP 202 with empty
body: `degruyter.com` / `degruyterbrill.com` (PAC PDF and both CI PDFs). Connection timeout:
`archive.org` (incl. the Wayback availability API), `ocw.snu.ac.kr`.

## §R1.2 (a) IUPAC "Glossary of terms used in physical organic chemistry (IUPAC Recommendations 2021)" — verbatim

**source**: Perrin, C. L.; Agranat, I.; Bagno, A.; Braslavsky, S. E.; Fernandes, P. A.; Gal, J.-F.;
Lloyd-Jones, G. C.; Mayr, H.; Murdoch, J. R.; Nudelman, N. S.; Radom, L.; Rappoport, Z.; Ruasse, M.-F.;
Siehl, H.-U.; Takeuchi, Y.; Tidwell, T. T.; Uggerud, E.; Williams, I. H. — "Glossary of terms used in
physical organic chemistry (IUPAC Recommendations 2021)", *Pure Appl. Chem.* **94**(4), 353–534 (2022),
DOI `10.1515/pac-2018-1010`. **Crossref-verified here** (title / vol. 94 / issue 4 / pages 353–534 /
issued 2022-04-01; Unpaywall `is_oa=true`, hybrid).

**status**: `first-hand` — publisher's version of record (Edinburgh Research Explorer copy), **all 182
printed pages** scanned via `pdftotext` (10 335 lines) + `grep`.

**locus mapping** (applies to every page number in §R1): PDF page `n ≥ 2` carries printed page `n + 351`;
verified against running heads (pdf 17 = 368, pdf 18 = 369, pdf 24 = 375, pdf 25 = 376, pdf 77 = 428,
pdf 78 = 429, pdf 102 = 453, pdf 103 = 454, pdf 106 = 457, pdf 183 = 534) and against the first text
page, which prints "Pure Appl. Chem. 2022; 94(4): 353–534".

**URLS FETCHED**:
`https://www.pure.ed.ac.uk/ws/files/281522413/20220617_Lloyd_Jones_10.1515_pac_2018_1010_VoR.pdf`
(6 752 732 bytes; 183 PDF pages = cover + pp. 353–534); second mirror
`https://escholarship.org/content/qt2rx9m9pg/qt2rx9m9pg.pdf` (UC San Diego author-manuscript copy).
Mirror list obtained from the OpenAIRE REST query `api.openaire.eu/search/publications?doi=10.1515/pac-2018-1010`.

### R1.2.1 Entry "Bell–Evans–Polanyi principle" — printed p. 369

**status** `first-hand`. The entry is three lines; quoted in full:
> "Linear relation between energy of activation (EA) and enthalpy of reaction (ΔrH), sometimes observed
> within a series of closely related reactions." — displayed: `EA = a + bΔrH` — "See [64–67]."

The entry's own reference list: [64] M. J. S. Dewar, *Molecular Orbital Theory of Organic Chemistry*
(1969); [65] W. P. Jencks, *Chem. Rev.* **85**, 511 (1985); [66] R. P. Bell, *Proc. R. Soc. Lond. Ser. A*
**154**, 414 (1936); [67] "M. G. Evans, M. Polanyi. *J. Chem. Soc. Faraday Trans.* **32**, 1340 (1936)".

**conclusion**: the normative modern statement of BEP is **activation energy vs enthalpy of reaction,
for a series of closely related reactions**. ⚠️ **The entry carries no Note, no bound on the slope and
no caveat about linearity.** The name in the glossary is "Bell–Evans–Polanyi principle"; there is **no**
"Semenov" entry and **no** separate "Evans–Polanyi relation" entry (see R1.2.5).
⚠️ The reference [67] is printed with a garbled journal name: the 1936 Evans–Polanyi paper is
*Trans. Faraday Soc.* **32**, 1333–1360 (Crossref `10.1039/tf9363201333`, re-checked here: title
"Further considerations on the thermodynamics of chemical equilibria and reaction rates", authors
M. G. Evans, M. Polanyi, vol. 32, first page 1333 — the IUPAC "1340" is an interior page). Reference
[66] is exact: Crossref `10.1098/rspa.1936.0060`, *Proc. R. Soc. Lond. A* **154**(882), 414–429.

### R1.2.2 Entry "Brønsted relation" — printed p. 375 (+ the α and β entries)

**status** `first-hand`. Two displayed equations, then verbatim:
> `lg({kHA}/p) = C + α lg(q{KHA}/p)` and `lg({kA}/q) = C + β lg(q{KHA}/p)`
> "where α, β, and C are constants for a given reaction series (**α and β are called Brønsted exponents
> or Brønsted parameters**)."
> "Note 2: The Brønsted relation is often termed the Brønsted catalysis law. Although justifiable on
> historical grounds, use of this name is not recommended, since Brønsted relations are known to apply
> to many uncatalyzed and pseudo-catalyzed reactions (such as simple proton [hydron] transfer reactions)."

Companion entries, same glossary, printed pages **368** and **376** respectively:
> "**α (alpha)** — … (3) Parameter in a Brønsted relation expressing the sensitivity of the rate of
> protonation to acidity. (4) Parameter in Leffler's relation expressing the sensitivity of changes in
> Gibbs activation energy to changes in overall Gibbs energy for an elementary reaction."
> "**β, βnuc, βlg** — Parameter in a Brønsted relation expressing the sensitivity of the rate of
> deprotonation to basicity. Note: βnuc and βlg are used to correlate nucleophilic reactivity and
> leaving-group ability, respectively."

**NEGATIVES inside this glossary** (exact strings, full extracted text of pp. 353–534):
`Brønsted coefficient` → **0 hits** (the normative term is "Brønsted exponents or Brønsted parameters",
p. 375); `Brønsted slope` → **0 hits** (`Bronsted slope` likewise); `Leffler coefficient` → **0 hits**;
`Brønsted exponent` → **2 hits only** (inside the Brønsted relation entry, p. 375, and inside
"general acid catalysis", p. 425).

### R1.2.3 Entry "transfer coefficient" — **NOT FOUND** (clean negative)

Searched strings over the whole extracted text of the 182 printed pages, case-insensitive:
`transfer coefficient` → 0 · `transfer coeff` → 0 · `Tafel` → 0 · `symmetry factor` → 0 ·
`electrode` → 0 · `overpotential` → 0 · `Butler` → 0 · `Volmer` → 0 · `electrochemical` → 0.
(The bare word "transfer" occurs 88 times, all inside *electron transfer / charge-transfer complex /
Förster resonance-energy transfer / group transfer / chain transfer / magnetization transfer* entries
and their cross-references; the **only** entry heading beginning with "transfer" is **"transferability"**.)

**conclusion — this is the definitional answer the plan needs**: the IUPAC *physical-organic* glossary
**does not define the transfer coefficient at all**; in particular it does **not** define it for
electrode reactions, and the word "electrode" never occurs in it. In this glossary the rate–equilibrium
coefficient of a series is called **α / β, "Brønsted exponent / Brønsted parameter"** (pp. 368, 375, 376),
and the transition-state-position reading of α is **Leffler's relation** (pp. 453–454). The
electrochemical transfer coefficient is a different normative object in a different IUPAC document →
see §R1.6.2.

### R1.2.4 Entries "Leffler's relation" / "Leffler's assumption" — printed pp. 453–454

**status** `first-hand`. Headings at the foot of printed p. 453, body at the top of printed p. 454;
quoted in full (the body is short):
> "In a series of elementary reactions, the changes in Gibbs activation energies are often found to be
> proportional to the changes in Gibbs energies for the overall reaction." — displayed: `δΔ‡G = α Δ_r G°` —
> "This relation was interpreted in terms of the simple assumption that a small change in any
> transition-state property P‡ is a linear combination of changes in reactant- and product-state
> properties, PR and PP." — displayed: `δP‡ = α δP_P + (1 − α) δP_R` —
> "Within the limits of this assumption, the parameter α is an **approximate measure of the fractional
> displacement of the transition state** along the minimum-energy reaction path from reactants to products."
> "See [109]." — Note: "**There are many exceptions** to the validity of Leffler's assumption that α is
> a measure of the position of the transition state." — "See [287]."

[109] = J. E. Leffler, E. Grunwald, *Rates and Equilibria of Organic Reactions*, Wiley, New York (1963);
[287] = A. Pross, *Theoretical and Physical Principles of Organic Reactivity*, pp. 177–182, Wiley (1995).

**conclusion**: this is the normative locus for the **α-as-Leffler-coefficient** identification and for
the equation form the plan's α-identity needs, and it concedes two things in its own words: α is an
"**approximate** measure" of the TS displacement, and there are "**many exceptions**".
For completeness: there is **no** entry naming α a "Leffler coefficient"; and the "Hammond postulate /
Hammond-Leffler principle" entry (printed pp. 428–429) is the qualitative companion, with Note 3's
"simply a consequence of adding a linear perturbation to the parabola".

### R1.2.5 "Evans–Polanyi" / "Semenov" entries — **NOT FOUND**; entry "linear free-energy relation (LFER)" — printed p. 457

- `Semenov` / `Semenow` / `Semjonow` / `Semenoff` → **0 hits** in all 182 printed pages.
- `Evans-Polanyi` / `Evans–Polanyi` → the only occurrence is the "Bell–Evans–Polanyi principle"
  heading (p. 369) and its index entries (pp. 460, 528, 533, 534). **No separate Evans–Polanyi entry.**
- Entry "**linear free-energy relation**" (alias "**linear Gibbs-energy relation**"), printed p. 457:
> "Linear correlation between the logarithm of a rate constant or equilibrium constant for a series of
> reactions and the logarithm of the rate constant or equilibrium constant for a related series of reactions."
> "Typical examples of such relations are the Brønsted relation and the Hammett equation (see also σ-value)."
> "Note: The name arises because the logarithm of the value of an equilibrium constant (at constant
> temperature and pressure) is proportional to a standard Gibbs energy (free energy) change, and the
> logarithm of the value of a rate constant is a linear function of the Gibbs energy (free energy) of
> activation."

### R1.2.6 Formalizable implication of §R1.2

- **Explicit Lean premises** that the normative wording itself forces:
  - a **"reaction series"** with **α, β constant across it** ("constants for a given reaction series",
    p. 375; "within a series of closely related reactions", p. 369) — the plan already declares this as
    the fixed-`λ` premise; the glossary confirms it is *by definition of the object*, not a derived fact;
  - the Brønsted relation as printed divides by `p`, `q` (numbers of equivalent acidic protons / basic
    sites), so a literal transcription needs `p ≠ 0`, `q ≠ 0`; with reduced coefficients it needs
    `0 < {kHA}`, `0 < {kA}`, `0 < {KHA}`;
  - for the secant/Δ-form of Leffler's relation, non-degeneracy of the compared pair (`x₁ ≠ x₂`).
    **No premise from the BEP entry itself is usable — it is an empirical linear act–enthalpy relation.**
- **Physical approximations to declare** (none of these is provable):
  1. **ΔH is not ΔG**: the normative BEP statement is *activation energy vs enthalpy of reaction*
     (p. 369), while the model is stated in **Gibbs** energies. `ΔH ≈ ΔG°` within a family (constant
     `TΔS`) is exactly the literature-dependent bridge the plan's honesty table lists — the glossary
     now supplies the printed wording for it.
  2. **Logarithmic plot over a series vs derivative at a point**: the glossary defines α/β on a
     *logarithmic plot*; the plan's `transfer lam x` is a *derivative*. They agree only if the LFER is
     exactly linear.
  3. **"Approximate measure"**: the TS-position reading of α is approximate *by the source's own
     wording*, with "many exceptions" (p. 454). It must be a declared interpretation, never a definition.
  4. **Leffler's linear closure** `δP‡ = α δP_P + (1 − α) δP_R` — a first-order linear-response
     assumption about TS properties; everything derived from α inherits it.
- **Not expressible in mathlib**: nothing blocks the scalar content (all statements are about `ℝ → ℝ`
  functions). The physical substrate is not expressible: "molecular entity", "transition-state property
  `P‡`", "position along the minimum-energy reaction path", "energy of activation"/"enthalpy of reaction"
  as thermodynamic quantities. Only their scalar surrogates can appear.
- **Impact on the plan**: (i) the BEP wording to cite is **p. 369** (and it is an **activation-energy vs
  enthalpy** statement — the plan's §13 row "`ΔH ≈ ΔG°` within a family" may now carry this locus);
  (ii) the α-identification to cite is **pp. 453–454** (Leffler's relation); (iii) the plan's docstring
  should attribute **"Brønsted exponent/parameter"** (not "transfer coefficient") to this glossary and
  reserve "transfer coefficient" for the electrochemical object (§R1.6.2); (iv) the glossary's own
  hedges ("approximate", "many exceptions", "for a given reaction series") are the **declared
  approximation register**; (v) do **not** cite this glossary for the electrochemical transfer
  coefficient — it has none (§R1.2.3).

## §R1.3 Primary BEP sources (printed formulas) — what is first-hand and what is not

| source | record | status |
|---|---|---|
| R. P. Bell, "The theory of reactions involving proton transfers", *Proc. R. Soc. Lond. Ser. A* **154**(882), 414–429 (1936) | DOI `10.1098/rspa.1936.0060` — **Crossref-verified here** (title/volume/issue/pages/year/authors exact) | `bibliographic-only` — body not read; **no formula is attributed to it here**. It is the [66] reference of the IUPAC BEP entry (p. 369). |
| M. G. Evans, M. Polanyi, "Further considerations on the thermodynamics of chemical equilibria and reaction rates", *Trans. Faraday Soc.* **32**, 1333–1360 (1936) | DOI `10.1039/tf9363201333` — **Crossref-verified here** (title/volume/first page/authors/year) | `bibliographic-only` — body not read; **no formula attributed**. It is the [67] reference of the IUPAC BEP entry, printed there as "32, 1340" with a garbled journal name (§R1.2.1). |
| M. G. Evans, M. Polanyi, "Some applications of the transition state method to the calculation of reaction velocities, especially in solution", *Trans. Faraday Soc.* **31**, 875–894 (1935) | DOI `10.1039/tf9353100875` — **Crossref-verified here** (title/volume/first page/authors/year) | `bibliographic-only` |
| N. N. Semenov, *Chemical Kinetics and Chain Reactions*, Oxford University Press (1935) | no Crossref DOI for the 1935 edition; reviews are indexed (`10.1021/ed012p298.3`, *J. Chem. Educ.* 12, 298 (1935); `10.2307/3608050`, *Math. Gazette* 19, 153 (1935)). English translation carried chapter DOIs in the 1958/59 Elsevier volume *Some Problems of Chemical Kinetics and Reactivity* (e.g. `10.1016/b978-1-4831-6747-3.50010-x`) | `not-accessed` — **no first-hand text, no formula, no page**. The name "Semenov relation" does **not** occur in the IUPAC glossary (0 hits, §R1.2.5); the printed BEP formula available in this pass is the IUPAC one (`EA = a + bΔrH`, p. 369). |

**conclusion**: the plan may cite **Bell 1936 / Evans–Polanyi 1936** as the primary literature of BEP
(bibliographically verified) and must cite **IUPAC p. 369** for the *printed formula*, because no
primary body text was read in this pass. A "Semenov relation" formula **cannot** be cited here.

## §R1.4 (b) Brønsted 1924 and Brønsted 1928 — **delivered** (Brønsted 1928 read; 1924 not-accessed)

Verified (Crossref, here):
- Brönsted, J. N.; Pedersen, K. J., "Die katalytische Zersetzung des Nitramids und ihre
  physikalisch-chemische Bedeutung", *Z. Phys. Chem.* **108U**(1), 185–235 (1924),
  DOI **`10.1515/zpch-1924-10814`** — **Crossref-verified here** (title / volume string "108U" / pages
  185–235 / 1924-01-01 / authors "J. N. Brönsted", "Kai Pedersen" / Walter de Gruyter). Unpaywall:
  `is_oa=false` (`closed`); Semantic Scholar `CLOSED`; OpenAlex `closed`, `has_fulltext=false`,
  cited-by 305. *(For the record: the sibling DOI `10.1515/zpch-1924-10813` is a different article, by
  Szegvari, pp. 175–184 — do not use it.)*
- Bronsted, J. N., "Acid and Basic Catalysis.", *Chem. Rev.* **5**(3), 231–338 (1928),
  DOI `10.1021/cr60019a001` — **Crossref-verified here** (title / volume 5 / issue 3 / pages 231–338 /
  issued 1928-10-01 / author J. N. Bronsted / ACS). Unpaywall: `is_oa=false` (`closed`); OpenAlex
  `closed`, cited-by 954.

**Status of the 1924 original**: `bibliographic-only` — **no text obtained; `not-accessed`; NONE quoted.**
Negatives (all blocked from this machine, exact strings and hosts recorded below): `archive.org`
advancedsearch + `ia-fts.archive.org` + `web.archive.org` + `openlibrary.org/search/inside` →
connection timeouts; HathiTrust (`babel…/cgi/ls`, `catalog…/api/volumes/brief`, `solr-sdr-search`) →
timeouts; Google Books API / `books.google.com` / `scholar.google.com` → timeouts;
`api.core.ac.uk` → HTTP 429; `zenodo.org` → connection refused; `degruyter.com` → 301 →
`degruyterbrill.com` → HTTP 202, empty body; `digizeitschriften.de` → 404, `gdz.sub.uni-goettingen.de`
→ generic hit list, Z. Phys. Chem. vol. 108 not located. ⚠️ **Citation-hygiene warning for the lead**:
a modern paper (PMC8921852) cites this 1924 work under a wrong title ("Stöchimetrie und
Berwandtschaftslehre") and a wrong page range ("185–125"); the Crossref record is the authority.
Search-engine hits exposed sci-hub/libgen corpus paths for this DOI — **not fetched, not used.**

**Status of the 1928 article**: `first-hand` — **read in full**, from a **third-party OCR copy**, not the
publisher's PDF. **Provenance caveat (binding on any quotation):** the copy is hosted at
`https://datapdf.com/acid-and-basic-catalysis-chemical-reviews-acs-publicationsd40f435c03d19cd1120fb713dbf3287123110.html`
(218 867 bytes); its fidelity evidence is internal: the contents list prints the section pages
"231, 234, 245, 252, 265, 278, 291 …", matching the Crossref range 231–338; running heads of the form
"ACID AND BASIC CATALYSIS <page>" appear throughout; the copy carries the credit line "**TRANSLATED BY
KARL H. SANDVED AND VICTOR K. LAMER, Columbia University, New York**"; and it ends with the article's
reference list. Formula glyphs in it are **partly destroyed by OCR** and are marked as such below.
The publisher copy (`pubs.acs.org`) answers HTTP 403.

**Locus** (running heads verified inside the copy): pp. **320–321**, equations (3)–(5), section
"VII. On the strength of acids and bases"; and p. **327**, the application to the nitramide data.

**VERBATIM** (prose is clean; the formula fragments are reproduced exactly as the OCR gives them —
**the algebra must not be reconstructed from them**):
> (p. 320) "If the proportionality between the velocities of dissociation and of catalysis is introduced
> into equation (2) we get: k, = GI K: (3) as the relation which may be anticipated to exist between the
> catalytic constant and the dissociation constant of an acid."
> (pp. 320–321) "It follows from these equations first, that the value of x is independent of the nature
> of the substrate. Secondly the equations give information concerning the relation between the catalysis
> of conjugate acids and bases. **It follows from the derivation that x has the same value in the two
> equations for conjugate acids and bases**: k, = GIKZ, kb = a&;-'."
> (p. 321 — the complementarity, **as actually worded**) "**If x-as a proper fraction-varies from 0 to 1
> the sensitivity of the acid catalysis to changes in K, will rise gradually'from 0 to 1, while a t the
> same time the sensitivity of the basic catalysis will fall gradually from 1 to 0.** A sensitivity equal
> to zero means that the catalytic constant does not change with the strength of the catalyst, whereas a
> sensitivity equal to unity means that the variation is directly proportional to it."
> (p. 321) "However, it appears from the formula, that if the acid catalysis displays great sensitivity to
> changes in the strength constant, the basic catalysis will display low sensibility and vice versa."
> (p. 321 — **the article's own disclaimer of its premises**) "It must be admitted, however, that **the
> premises which lie a t the root of t'he theory, although plausible, are not absolutely cogent in their
> nature**, and it might therefore prove necessary on closer examination to modify these assumptions in
> different directions."
> (p. 327) "These equations conform to formula (5), deduced from theoretical considerations, **the
> exponent 1 - x being a proper fraction** … the measurements give the interesting result that **1 - x is
> constant within every group of bases**, despite the considerable changes (from 2.10-6 to 10-2 for the
> anions and from 0.7.10-6 to 2.10-3 for the amines) in the dissociation constants."

**Answer to (ii) — is 1928 the English locus?** The article **is in English, but it is explicitly a
*translation*** ("TRANSLATED BY KARL H. SANDVED AND VICTOR K. LAMER"); it states the Brønsted catalysis
relation as eq. (3) on p. 320 with exponent `x`, and the conjugate acid/base pair `x` / `1 − x` on
pp. 320–321 and 327. Whether it is the *first* English statement of the relation **could not be
determined** (`not-accessed` on that sub-question).

**Answer to (iii) — is `β_f + β_r = 1` stated there, and in what words?** ⚠️ **NO.** The article states
complementarity as "**x has the same value in the two equations for conjugate acids and bases**" with
one exponent `x` and the other `1 − x`, and as a sensitivity that "rise[s] gradually from 0 to 1" for
acid catalysis while the basic catalysis "fall[s] gradually from 1 to 0" (pp. 320–321). **The phrase
"the sum of the two exponents is unity", or any equivalent sum sentence, does not occur.** Full-text scan
of the copy: `sum of` 3× (sum of two rate constants; sum of radii; logarithm of a sum — none an identity),
`unity` 8× (none asserting a sum-of-exponents identity), `complementa` 0×, `selectivity` 0×.
Independent Europe PMC full-text negatives: `"exponents add up to one"` → 0 hits;
`"sum of the two exponents"` → 2 hits, both unrelated (small-angle scattering; cytochrome P-450);
`"Brønsted exponent" AND "one"` → 0 hits.
⇒ **Impact (flagged for the plan): do not write "Brønsted asserted `β_f + β_r = 1`".** Write instead
"Brønsted expressed the complementarity as a pair of exponents `x` and `1 − x`" and cite
*Chem. Rev.* **5**(3):320–321 (1928). The same article supplies, in its own words (p. 321), the
**statement that the premises are assumptions** ("although plausible, are not absolutely cogent") — a
direct literature basis for this project's rule that physical approximations must be *declared* rather
than proved.

**URLS FETCHED** (this pass, first-hand): `api.crossref.org/works/10.1515/zpch-1924-10814` (200),
`api.crossref.org/works/10.1021/cr60019a001` (200), `api.unpaywall.org/v2/…` (200, both `closed`),
`https://datapdf.com/acid-and-basic-catalysis-chemical-reviews-acs-publicationsd40f435c03d19cd1120fb713dbf3287123110.html`
(200 — the text read; `pdftotext`-equivalent extraction via HTML strip, grepped), plus the blocked hosts
listed above.

## §R1.5 (c) Leffler, J. E., "Parameters for the Description of Transition States", *Science* **117**(3039), 340–341 (1953) — **delivered** (original not-accessed; equation reproduced by three OA papers)

Verified (**Crossref, here**): title "Parameters for the Description of Transition States";
container *Science*; volume **117**; issue **3039**; pages **340–341**; issued **1953-03-27**;
author John E. Leffler; DOI **`10.1126/science.117.3039.340`**; publisher AAAS; reference-count 3;
is-referenced-by 520.
Unpaywall: `is_oa = false`, `oa_status = closed` (`api.unpaywall.org/v2/10.1126/science.117.3039.340`);
Semantic Scholar `CLOSED`; OpenAlex `closed`, `has_fulltext=false`; PubMed `PMID 17741025` is
"PubMed-not-MEDLINE" with bibliographic fields only, no abstract; `science.org/doi/…` → HTTP 403.
⇒ **The original body is `not-accessed`; `VERBATIM: NONE` from Leffler's own text.**

**SECONDARY quotations of Leffler's equation — all three read first-hand by me in OA full texts**
(each source's own reference list points at Leffler 1953; these are other authors' transcriptions of the
equation form, **not** Leffler's sentences, and must be labelled as such in any citation):
- **[Q1]** G. Qiu, "Exceptions, Paradoxes, and Their Resolutions in Chemical Reactivity",
  *J. Org. Chem.* **89**(22), 16307–16316 (2024), DOI `10.1021/acs.joc.4c02246`, OA `PMC11574852`:
  > "… in the linear approximation (ΔG⧧ = ΔG₀⧧ + αΔG) known as the Leffler equation."
  and, a few lines later, "For constant ΔG₀⧧ and α, the Leffler equation is reduced to the BEP principle".
- **[Q2]** G. Qiu, P. R. Schreiner, "The Intrinsic Barrier Width and Its Role in Chemical Reactivity",
  *ACS Cent. Sci.* **9**(11), 2129–2137 (2023), DOI `10.1021/acscentsci.3c00926`, OA `PMC10683502`:
  > "The Marcus dissection was quantitatively expressed in the linear approximation
  > Δ⧧G = Δ⧧G₀ + αΔG as the Leffler equation."
- **[Q3]** F. Barasits, G. Qiu, "Identifying Quantum Tunneling at Ambient Temperature through
  Rate–Driving Force Responsiveness", *J. Am. Chem. Soc.* **148**(32), 34038–34044 (2026),
  DOI `10.1021/jacs.6c08355`, OA `PMC13495758`:
  > "Within the Leffler approximation, the activation free energy can be written as
  > ΔG‡ = ΔG₀‡ + αΔG, where ΔG₀‡ is the intrinsic barrier corresponding to a thermoneutral reaction
  > (ΔG = 0)."
  > (same paper, relevant to §R1.7(iv)) "Under classical transition state theory, this responsiveness is
  > **bounded between 0 and 1**, as expected from the Hammond postulate."
  ⚠️ **[Q1]–[Q3] share the same corresponding author (G. Qiu); they are three loci but not three
  independent groups.** The fourth statement, in *Chem. Sci.* **16**(37):17494 (2025) (§R1.5 below and
  §R1.6.1), is likewise from that group. **No source was found that reproduces Leffler's own sentences
  from *Science* 117, 340–341** (Europe PMC searches `"Leffler" AND "Hammond"` → 88 hits,
  `"Leffler" AND "selectivity" AND "Brønsted"` → 15 hits; the OA full texts fetched and scanned contain
  no such reproduction).
  ⇒ **Citation rule for the plan: the linear form `ΔG‡ = ΔG₀‡ + α·ΔG` may be cited to these OA loci and
  to the IUPAC glossary's `δΔ‡G = α Δ_r G°` (printed p. 454), but never with a page/equation number
  inside Leffler 1953 itself** (e.g. do not write "Leffler 1953, eq. (1), p. 340" — unverified).

**URLS FETCHED**: `https://www.ebi.ac.uk/europepmc/webservices/rest/{PMC11574852,PMC10683502,PMC13495758,PMC12406046}/fullTextXML`
(200 each; the four texts were grepped directly — the three quotes above were re-read from the returned XML,
not taken on report).

**Partial answer to the dispatch question (c) — an accessible source does reproduce Leffler's equation.**
Read first-hand in *Chem. Sci.* **16**(37):17494 (2025) (same OA paper as §R1.6.1; Introduction, first
paragraph of the model discussion), with its reference `2` = Leffler 1953:
> "For example, the most experimentally relevant is the Leffler equation (Fig. 1a), which expresses the
> energy of activation ΔE‡ by a combination of the reaction energy ΔE and the intrinsic barrier ΔE‡₀,
> which corresponds to ΔE‡ for ΔE = 0, **in the linear approximation, ΔE‡ = ΔE‡₀ + α ΔE**."
> "**For constant ΔE‡₀ and α, the Leffler equation is reduced to the Bell–Evans–Polanyi (BEP) principle**,
> describing the kinetic–thermodynamic relationship within the same family of reactions."

This is a **modernised transcription with attribution (ref. 2 = Leffler 1953), not a facsimile of the
1953 typography** — it is recorded as a secondary locus for the *form* of the equation and must not be
quoted as Leffler's own words. It is nevertheless the formula-level support the plan needs, and it is
**the same equation the IUPAC glossary prints** (`δΔ‡G = α Δ_r G°`, p. 454) once the series variation is
written additively. The same paper's reference list also gives the bibliographic record
"Leffler J. E. Science. 1953;117:340–341. doi: 10.1126/science.117.3039.340" (matches §R1.5 exactly).
**URLS FETCHED**: `https://www.ebi.ac.uk/europepmc/webservices/rest/PMC12406046/fullTextXML`.

⚠️ **Reference-list discrepancy noted for the lead** (do not propagate blindly): the same paper's
reference list prints the 1936 *Trans. Faraday Soc.* **32**, 1333–1360 paper as "**Eyring H. Polanyi M.**"
(DOI `10.1039/TF9363201333`), whereas **Crossref** (re-checked here) and the IUPAC glossary's reference
[67] both give "**M. G. Evans, M. Polanyi**" for that DOI/title. Three sources, two attributions →
the plan should cite the DOI and the title, and may attribute the paper to Evans & Polanyi
(Crossref + IUPAC agreement).

## §R1.6 (d) The complementarity identity β_f + β_r = 1

### R1.6.1 First-hand, peer-reviewed, open-access statement

**source**: García-Padilla, E.; Qiu, G., "The global kinetic–thermodynamic relationship derived from
first principles", *Chem. Sci.* **16**(37), 17494–17505 (2025), DOI `10.1039/d5sc04829j` — **Crossref-verified
here** (title/vol. 16/issue 37/pages 17494–17505/2025/authors/licence CC-BY 3.0). Open access full text:
Europe PMC `PMC12406046`.

**status**: `first-hand` (JATS full-text XML; the RSC and Europe PMC **PDF** endpoints are 403 here, so
the locus is given by **equation number and section name** inside the article's page range 17494–17505).

**locus**: the paragraph following eqns (1)–(3) (displayed eqn (2) is the differentiated reversal
relation), and again in §2.2 near eqn (5).

**conclusion / VERBATIM** (two decisive sentences):
> "By differentiating eqn (1) once and twice, we obtain eqn (2) and (3), respectively. **The first
> derivative shows that the gradients of the forward and reverse reactions are complementary, adding up
> to one.**"
> "Drawing an analogy to microscopic reversibility, as the forward and backward factor transmission
> influences constitute the total origin of all factors acting on the TS from either minimum, **they must
> add to 1**."

Eqn (1) as extracted states the barrier-reversal relation (`ΔE‡₋₁(−ΔE_r) = ΔE‡(ΔE_r) − ΔE_r`), which is
exactly the plan's `eact_neg_eq_add` (`eact lam (-x) = eact lam x + x`); eqn (2) is the differentiated
form. Symbols are flattened by XML extraction: the **equation numbers (1)–(3)** and the two sentences are
what this pass verifies; an equation transcription has **not** been image-checked.

**URLS FETCHED**: `https://www.ebi.ac.uk/europepmc/webservices/rest/PMC12406046/fullTextXML`.

**Independent second statement with a printed page locus** (non-peer-reviewed, explicitly worded):
Dodd, B. J., "Mechanistic studies of leaving group effects on enzymatic catalysis by methylglyoxal
synthase", Doctoral thesis, Durham University (2004), `etheses.durham.ac.uk/id/eprint/4764/` — **status**
`first-hand` (full PDF, 11 MB, text layer) — **locus** printed **p. 27**:
> "… must be −0.31 and −0.61 respectively, since **the sum of Brønsted coefficients for the forward and
> reverse reactions must equal unity**."
(Text layer mangles "Brønsted" as "Bransted"/"Brensted"; spelling normalised, flagged.)
**URLS FETCHED**: `http://etheses.dur.ac.uk/4764/1/4764_2233.pdf`.

### R1.6.2 Electrochemical analogue α_a + α_c = 1 — **the normative IUPAC locus, read first-hand**

**source A (the assessment)**: Guidelli, R.; Compton, R. G.; Feliu, J. M.; Gileadi, E.; Lipkowski, J.;
Schmickler, W.; Trasatti, S., "Defining the transfer coefficient in electrochemistry: An assessment
(IUPAC Technical Report)", *Pure Appl. Chem.* **86**(2), **245–258** (2014), DOI `10.1515/pac-2014-5026`.
**Crossref-verified here** (title / vol. 86 / issue 2 / pages 245–258 / 2014 / the seven authors).
**status**: `first-hand` — full publisher PDF (14 printed pages, pp. 245–258; PDF page `n` carries printed
page `n + 244`, verified against running heads: pdf 2 = 246, pdf 3 = 247, pdf 4 = 248, pdf 5 = 249,
pdf 13 = 257).
**VERBATIM** (three loci):
> (printed **p. 247**, immediately after eq. (9)) "Since at equilibrium the Nernst equation applies, from
> eq. 9 it follows that **(αc + αa) = 1** and ka/kc = exp(−nFE°/RT), where E° is the formal potential of the
> O/R couple."
> (printed **p. 249**, eqs. (16) and (17)) "Since the sum nf+nr+nb is necessarily equal to the number, n, of
> electrons involved in the overall electrode reaction, summing αa in eq. 15 to αc in eq. 13, with ν = 1,
> yields — `αc + αa = n` (16) — In the more general case in which the rds occurs ν times in the electrode
> reaction, αc + αa is given by — `αc + αa = n / ν` (17)"
> (printed **p. 249**, the restriction that follows eq. (17)) "**It must be stressed that eqs. 16 and 17 hold
> only if the forward and backward electrode reactions are characterized by the same rds**, a situation that
> is not necessarily encountered when the negative overpotential for the cathodic process and the positive
> overpotential for the corresponding anodic process are relatively high [11]."
(pp. 257, the Summary, repeats eqs. (16)/(17); and pp. 248/257 repeat the same-rds restriction.)
**URLS FETCHED** (open repository copy, Universidad de Alicante RUA, handle `10045/35665`):
`https://rua.ua.es/server/api/core/bitstreams/57bdc35e-96c3-4973-a166-8ef4db5700e4/content`
(1 461 735 bytes). Unpaywall reports the publisher PDF at
`https://www.degruyter.com/document/doi/10.1515/pac-2014-5026/pdf` (`bronze`), which returns HTTP 202 with
an empty body here.

**source B (the recommendation)**: same task group, "Definition of the transfer coefficient in
electrochemistry (IUPAC Recommendations 2014)", *Pure Appl. Chem.* **86**(2), **259–262** (2014),
DOI `10.1515/pac-2014-5025` — **Crossref-verified here**. **status** `first-hand` (full PDF, 4 printed
pages, pp. 259–262).
**VERBATIM** (printed **p. 259**, §2 "Definition", eq. (1)):
> "The anodic transfer coefficient αa and the cathodic transfer coefficient αc are defined by the following
> equations: `αa = (RT/F)(dln ja / dE); αc = −(RT/F)(dln|jc| / dE)` (1)"
and the abstract: "An unambiguous definition of the transfer coefficient, independent of any mechanistic
consideration and exclusively based on experimental data, is proposed. … This recommendation aims at
clarifying and improving the definition of the transfer coefficient reported in the 3rd edition of the IUPAC
Green Book."
⚠️ **Definitional conflict inside IUPAC, recorded deliberately**: this 2014 Recommendation states that its
definition "differs from that presently reported in the 3rd edition of IUPAC Green Book [1] and in some
textbooks [2–5], and also from the different definition reported in the IUPAC Gold Book [6]" (printed
p. 259, §1 Preamble); §3 explains the two differences (current density instead of rate constant; the
number `n` **removed**). The 2014 Recommendation itself **does not state any sum rule** — the sum rule
lives in its companion Technical Report (source A).
**URLS FETCHED**: `https://rua.ua.es/server/api/core/bitstreams/a424f518-e715-4ef8-8e9b-bbc55dbea1ce/content`
(449 234 bytes; same repository, handle `10045/35666`).

**Textbook cross-check (independent of IUPAC)**: Inzelt, G., "Kinetics of Electrochemical Reactions"
(Chapter I.3), in F. Scholz (ed.), *Electroanalytical Methods — Guide to Experiments and Applications*,
DOI `10.1007/978-3-642-02915-8` — **status** `first-hand` (text layer, two extraction modes agree), **locus**
printed p. **36**:
> "where αa and αc are the anodic and cathodic transfer or symmetry coefficients, respectively. In general,
> α is called the transfer coefficient (it can be determined from the current–potential function); the name
> symmetry factor refers to the fact that its value depends on the symmetry of the potential barrier. For a
> symmetric barrier, αa = αc = 0.5, but, in general, 0 ≤ α ≤ 1 and, **for a simple reaction αa + αc = 1**."
(text layer prints "1and"; space restored). Same page, eqn (I.3.9) `dΔ‡G = α dΔG` — the electrode analogue of
the Leffler/Brønsted derivative statement.
**URLS FETCHED**: `https://ndl.ethernet.edu.et/bitstreams/25a3d7e2-480a-4fda-9343-f42a57766431/download`
(third-party mirror; licenses page/equation **location** only — the canonical object is the DOI).

**Normative IUPAC pointers for the same object — `bibliographic-only` (bodies NOT accessed):**
- Gold Book "**transfer coefficient**" (term 12283), DOI `10.1351/goldbook.t06442`-adjacent record:
  the entry key is `12283`; also Gold Book "**anodic transfer coefficient**" DOI `10.1351/goldbook.a00371`
  and "**cathodic transfer coefficient**" DOI `10.1351/goldbook.c00906` — both **Crossref-verified here**
  (container "The IUPAC Compendium of Chemical Terminology", 3rd ed., online version 3.0.1, 2019). The
  2014 Recommendation (source B) states its own definition **differs** from this Gold Book definition.
- *Chemistry International* **34**(2) (2012) p. 21, "Definitions of Transfer Coefficient and of Partial
  Charge Transfer Coefficient in Electrode Kinetics", DOI `10.1515/ci.2012.34.2.21a` — **Crossref-verified**;
  and *Chemistry International* **35**(1) (2013) p. 23, "Definition of the Transfer Coefficient",
  DOI `10.1515/ci.2013.35.1.23a` — **Crossref-verified** (the free PDFs are Cloudflare-blocked here).
- **NEGATIVE**: `goldbook.iupac.org` and `mail.goldbook.iupac.org` answer HTTP 403 (Cloudflare) to `curl`
  with a browser UA and to the harness fetch tool; the Crossref-deposited abstracts of the Gold Book entries
  contain only the citation line, **not** the definition; `old.iupac.org/goldbook/*.pdf` → 403; Wayback/
  `archive.org` → connection timeout. ⇒ the Gold Book's transfer-coefficient **definitional text** stays
  `not-accessed`; the 2014 Recommendation + Technical Report above are used instead (both IUPAC, both read
  first-hand, both openly accessible).

### R1.6.3 Sources that warn the identity fails or is only approximate

1. **García-Padilla & Qiu 2025** (same source as R1.6.1), Conclusions, VERBATIM:
   > "Consequently, the observed Brønsted slopes and intercepts of the linear approximations of a system
   > constitute **local descriptors, dependent on the underlying parameters and the studied thermodynamic
   > range**."
   and the Abstract:
   > "Classical models, such as the Marcus equation and Leffler equations, either rely on under-realistic
   > assumptions or only capture the local behaviour, failing outside narrow regimes."
   ⇒ forward and reverse coefficients of a real series are **range-dependent**; a sum rule read off two
   plots measured over *different* ranges is at best approximate. This is the accessible statement of the
   caveat the dispatch asked for.
2. **IUPAC Technical Report 2014 (R1.6.2 source A), printed p. 249 — the strongest and most normative
   warning found**, VERBATIM:
   > "**It must be stressed that eqs. 16 and 17 hold only if the forward and backward electrode reactions
   > are characterized by the same rds**, a situation that is not necessarily encountered when the negative
   > overpotential for the cathodic process and the positive overpotential for the corresponding anodic
   > process are relatively high [11]."
   ⇒ the identity is **conditional**: same rate-determining step for both directions, i.e. the forward and
   reverse coefficients must be *measured on the same elementary step and over comparable ranges*. This is
   exactly the "measured over different ranges" failure the dispatch asked about, stated by IUPAC itself.
   Same document, printed pp. 257/248: eqs. (16)/(17) are restated with the same restriction. And
   Inzelt (R1.6.2, printed p. 36) phrases the same condition as "**for a simple reaction**".
3. **IUPAC glossary, entry "imbalance"** — printed p. **437**, VERBATIM:
   > "Example: the nitroalkane anomaly, where the Brønsted β exponent for hydron removal is smaller than
   > the Brønsted α for the nitroalkane as acid because of imbalance between the extent of bond breaking
   > and the extent of resonance delocalization in the transition state."
   ⇒ the two coefficients need not describe the same progress variable. The glossary's companion entry
   "**principle of nonperfect synchronization**" is on the **same printed page 437** ("Consideration
   applicable to reactions in which there is a lack of synchronization between bond formation or bond
   rupture and other changes …, such as resonance, solvation, electrostatic, hydrogen bonding, and
   polarizability effects"; Note: a lagging product-stabilizing factor "increases the intrinsic barrier
   and decreases the rate constant").
4. **Dodd 2004** (R1.6.1, second source), printed p. 27, on Bernasconi's non-perfect synchronization:
   coefficients of one series fall **outside (0,1)** — "a negative Brønsted coefficient for a plot of
   log kr vs. log Ka (α = −0.7) and a coefficient larger than 1 for a plot of log kr vs. log K_a^{H+}
   (α = 1.7)" — i.e. the *value*, and hence any sum, depends on which axis the coefficient was measured
   against. Same page, on where the `(0,1)` restriction comes from (verbatim):
   > "Restriction of the Brønsted coefficients to values between 0 and 1 arose from the application of the
   > Brønsted relationship predominantly to oxygen or nitrogen acids and bases such as carboxylic acids and
   > carboxylate ions, amines and ammonium ions, pyridinium ions and pyridines."
   ⇒ the `(0,1)` bound is **empirical in origin** (a property of the families usually studied), **not** a
   law of chemical families. This is the literature support for the §R1.7 (iv) warning.

### R1.6.4 Formalizable implication of §R1.6 — and the sign convention the plan must print

- **The identity is a theorem of the model, not an empirical premise.** With the plan's own definitions
  (`eact lam x = (lam - x)^2/(4*lam)`, `transfer lam x = 1/2 - x/(2*lam)`,
  `reverseTransfer lam x = 1/2 + x/(2*lam)`), the content of the literature sentence "the gradients of
  the forward and reverse reactions are complementary, adding up to one" is
  `transfer lam x + reverseTransfer lam x = 1` — the plan's B2 §5 #8. **No physical hypothesis is needed**;
  the mathematical input is the barrier-reversal identity `eact lam (-x) = eact lam x + x` (SOURCE A's
  eqn (1)) plus the derivative/difference computation.
- **Premises to keep explicit**: `lam ≠ 0` (division) — already in the skeleton; for the secant form, a
  non-degenerate pair `x₁ ≠ x₂`; and a declared restriction to a **single elementary step** ("for a
  simple reaction", Inzelt; IUPAC 2014: "hold only if the forward and backward electrode reactions are
  characterized by the same rds") with a **coefficient constant across the series** (IUPAC p. 375).
  The electrochemical generalisation is `αc + αa = n/ν` (IUPAC Technical Report 2014, eq. (17), printed
  p. 249, ν = number of times the rds occurs) — **not** a form the plan should formalize (see below).
- ⚠️ **Sign convention (must appear in the Lean docstring).** The sum form holds when each coefficient
  is the barrier slope w.r.t. **its own** driving force, oriented exergonically for its own direction —
  i.e. exactly the plan's `reverseTransfer lam x = transfer lam (-x)`. If instead **both** coefficients
  are differentiated w.r.t. **one common variable** with the same orientation, the relation is
  `β_f − β_r = 1`; SOURCE B's printed pair (+1.31 forward, −0.31 reverse, summing to 1) is the sum form
  with signed values on a shared log-K axis. The plan's convention is self-consistent and matches
  SOURCE A; it must be stated, because a reader using the other convention will read the lemma as an error.
- **Physical approximations to declare**: none for the identity itself. What *is* approximate is
  (a) reading a *linear* BEP/Brønsted plot as a derivative (exact only for a linear plot) and
  (b) applying the identity across a finite driving-force range (SOURCE A's "local descriptors").
- **Not expressible in mathlib**: electrode-kinetic objects (overpotential, current density,
  Butler–Volmer form, the Gold Book partial-charge-transfer coefficient, the stoichiometric number ν) —
  no electrochemistry layer; and the physical predicate "this is a simple (single-step) reaction" or
  "forward and reverse share the same rds" — it can only be a *declared* hypothesis or a scope
  restriction, never derived.

## §R1.6b Documented limitations and failure modes of BEP (first-hand, peer-reviewed)

**source**: García-Padilla, E.; Qiu, G., *Chem. Sci.* **16**(37), 17494–17505 (2025), DOI `10.1039/d5sc04829j`
(same OA paper as §R1.6.1; **Crossref-verified**). **status** `first-hand` (JATS full text; PDF endpoints
403, so loci below are section/paragraph positions inside pp. 17494–17505, with the source's own reference
numbers as printed).

**VERBATIM** (each is one sentence of the Introduction / Conclusions, quoted as printed):
> "Although the linear kinetic–thermodynamic relationship is commonly observed experimentally, it is the
> approximation over a limited range of thermodynamic driving force. As the driving force becomes highly
> exergonic or endergonic, the linearity breaks down." (ref. 6)
> "In the extreme limits, the behaviour of α reveals distinct kinetic regimes. For highly exergonic
> reactions, α approaches 0; conversely, for very endergonic reactions, α approaches 1." (ref. 7)
> "BEP plots often show deviations from linearity." (ref. 8)
> "This model predicts a Brønsted slope α near 0.5 for reactions close to zero driving force. A serious
> assumption in the Marcus formation of the curve is that the parabolas of the reactant and the product
> states have identical shape."
> "Koeppl and Kresge demonstrated that allowing bond strengths and reaction distances to vary realistically
> produces a sigmoid Brønsted slope, better reflecting real systems, which would deviate from Marcus
> predictions. Similarly, Richard and Jencks found significant deviations in Brønsted slopes for general
> base catalysis, attributing them to differential charge development in the transition state …"
> "The value of α is often used to probe how early or late in a reaction the transition state develops,
> with **values lower than 0.5 corresponding to an earlier transition state**."

**conclusion (what this fixes for the plan)**: this one accessible, peer-reviewed source supplies, in its
own words, (1) the equation form of the linear law (`ΔE‡ = ΔE‡₀ + α ΔE`, §R1.5), (2) the statement that
**BEP = the Leffler equation at constant `ΔE‡₀` and constant `α`** (§R1.5) — which is exactly the plan's
framing — (3) the **failure mode** ("the approximation over a limited range of thermodynamic driving
force", "BEP plots often show deviations from linearity") that motivates the plan's tolerance/window
formulation (B3 §6.2), (4) the **extreme-limit behaviour** `α → 0` exergonic / `α → 1` endergonic, and
(5) the **sign/direction convention**: `α < 0.5` ⇔ earlier transition state, which **agrees** with the
plan's `transfer lam x = 1/2 - x/(2*lam)` and `tsCoord lam x = (lam - x)/(2*lam)` for `x > 0`.
It does **not** state `0 ≤ α ≤ 1` as a law (see §R1.7(iv)).

## §R1.7 Fidelity check — the plan's four formalized claims vs what the sources say

Judged against the sources read in this pass (`theories/BEP/plan.md` §1.1, §4–§8; claims (i)–(iv) of the
dispatch — the dispatch text itself is not reproduced here, the plan's versions are):

| # | plan's claim (as written) | verdict from this pass |
|---|---|---|
| (i) | BEP as an **affine** barrier–driving-force description inside the model | **Faithful to the normative wording** (IUPAC p. 369 "Linear relation … sometimes observed within a series of closely related reactions"), including the plan's decision to treat it as an approximation: the glossary's "sometimes … within a series" is the same qualification. **Independently supported** by *Chem. Sci.* 16(37):17494 (§R1.6b): the Leffler equation at constant `ΔE‡₀`, `α` "is reduced to the Bell–Evans–Polanyi (BEP) principle". ⚠️ One wording gap: the glossary's relation is **activation energy vs enthalpy**, the model's is **Gibbs** energy — the plan's honesty-table row `ΔH ≈ ΔG°` is the right place; attach p. 369 there. |
| (ii) | slope `α = 1/2 - x/(2*lam)` equals the TS coordinate (= Leffler/Brønsted identification) | **The identification is normative**: IUPAC p. 454, "α is an approximate measure of the fractional displacement of the transition state …". ⚠️ It is "**approximate**" and has "**many exceptions**" *in the source's own words*, and the plan proves it as an exact *algebraic* identity inside the model — so the plan must keep the disclaimer that the exactness is a property of the model, not of molecules (plan §13 already does; the quote belongs there). |
| (iii) | complementarity `α_f + α_r = 1` | **Supported first-hand**: peer-reviewed statement in *Chem. Sci.* 16(37):17494 (eqn (1)–(2) and "complementary, adding up to one"); normative electrochemical form in the IUPAC Technical Report 2014 (p. 247 `(αc + αa) = 1`; p. 249 eqs. (16)/(17) `= n`, `= n/ν`); and it is **provable** in the model from the barrier-reversal identity (`eact lam (-x) = eact lam x + x`). ⚠️ Requires the sign-convention note (R1.6.4) and, for the reverse-direction reading, the single-elementary-step / same-rds restriction. |
| (iv) | `0 ≤ α ≤ 1` as the Evans–Polanyi bound, with a sharp regime | **Partly supported, with an explicit condition.** The bound is *not* stated in the IUPAC physical-organic glossary (which prints no bound at all, §R1.2.1), and a documented series has Brønsted coefficients **outside** `(0,1)` (R1.6.3 item 4: −0.7 and 1.7 on different axes). Two first-hand loci do state it: [Q3] (JACS 2026, `PMC13495758`) "**Under classical transition state theory, this responsiveness is bounded between 0 and 1**, as expected from the Hammond postulate" — i.e. bounded *under classical TST and within a family*; and Inzelt p. 36, `0 ≤ α ≤ 1` for the **electrochemical** transfer coefficient. ⇒ keep the plan's presentation as a **proved property of the model** (`α ∈ [0,1] ⟺ -λ ≤ x ≤ λ`) and, if the plan calls it "the Evans–Polanyi bound", attach [Q3]'s "under classical transition state theory" qualifier — **not** a law of chemical families. |

## §R1.8 Delegated retrieval (Brønsted 1924/1928; Leffler 1953; further β_f+β_r sources) — **resolved**

*The delegated retrievals of this pass returned; their load-bearing quotes were **re-read first-hand by
me** before being written into §R1.4 and §R1.5 (the Brønsted 1928 sentences were re-extracted from the
same copy and the three Leffler transcriptions were re-read from the returned Europe PMC XML). The two
Brønsted volumes and the Leffler note are closed at their publishers; the statuses recorded above are
final for this round, and no wording is attributed to a source that was not read.*

## §R1.9 Outstanding for round 1 (not in this dispatch)

- the **B5b data table** (≥ 4 families, ≥ 2 (driving force, barrier) pairs in kJ/mol with provenance) —
  not retrieved in this pass; **must not be filled from memory**. Candidate first-hand families are the
  ones already in `theories/Marcus/LITERATURE.md` (Miller–Calcaterra–Closs 1984 series; reaction-centre
  numbers) once converted to kJ/mol **with their own provenance status**.
- the **derivation-context** entries (Marcus 1956 eq. (38) p. 974 and eq. (44) p. 975; Cohen–Marcus 1968;
  Marcus 1968 eq. (32) p. 896) with printed loci — already first-hand in the sibling records
  (`theories/Marcus/LITERATURE.md`, `theories/hammond/LITERATURE.md` S6–S11); cross-reference rather than
  re-retrieve.

---

# §R1.10 Round-1b — the B5b data table: five first-hand families with model-consistency verdicts

## R1.10.1 Conversion, provenance, and the consistency test (read this before the table)

**Unit conversion (stated, not asserted):** `1 kcal/mol = 4.184 kJ/mol` (thermochemical calorie, exact by
definition). Every family below prints the **source's own kcal/mol** numbers first and the kJ/mol values
second; the kJ/mol column is **this record's arithmetic**, and a converted value inherits `first-hand` only
where the original number was read first-hand.

**Sign convention (fixed once for the whole file):** `ΔG° < 0` = exergonic; the model's driving force is
`x = -ΔG°`, so `x > 0` = exergonic and `x < 0` = the endergonic branch.

**The consistency test used for every family.** With `Ea(x) = (λ - x)²/(4λ)`, `λ > 0`, a single pair
`(x, Ea)` determines `λ` from `0 = λ² − (2x + 4Ea)λ + x²`, i.e. `λ̂ = (x + 2Ea) ± 2√(Ea² + x·Ea)`. Two
verdicts per family:

1. **per-pair `λ̂ > 0`** — the pair *admits* a positive reorganization energy (the weaker test);
2. **family curvature** — the model's second derivative is `d²Ea/dx² = 1/(2λ) > 0` **for every** `λ > 0`,
   so a family whose fitted curvature is **negative** cannot be reproduced by *any* positive-`λ`
   two-parabola law (the stronger, λ-independent test).

⚠️ **Two-convention label (added round 1j; the record uses both and they differ by exactly a factor 2).**
The verdicts above are computed in **two different normalizations** of the same law:

| label | normalization | how a fitted curvature becomes a `λ` | used for |
|---|---|---|---|
| **(A) curvature convention** | `Ea(x) = λ/4 − x/2 + x²/(4λ)` at the level of the *second derivative*, so `d²Ea/dx² = 1/(2λ)` | `λ = 1/(2·curvature)` | the family-curvature verdicts (`−0.0160` ⇒ `λ = −31.3 kcal/mol`, etc.) |
| **(B) quadratic-coefficient convention** | the fitted polynomial `y = a + b·x + c·x²` with `c = 1/(4λ)` | `λ = 1/(4·curvature)` | the per-pair `λ̂` columns and the 2-butanol family's constants |

Both are negative in every family, and the **conclusion (negative curvature ⇒ no positive `λ` exists) is
invariant under either label** — the factor 2 changes the *value* of the implied `λ`, never its sign. Any
figure quoted from this record must therefore carry its label; e.g. §R1.10.2's water family reads
`λ = −15.6 kcal/mol` under (B) and `λ = −31.3 kcal/mol` under (A) — the ~0.5 % difference between the
printed `−15.7` and the exact `−15.625` is rounding of the *curvature* to two significant figures, not a
convention difference. **Rule for this record: report `λ̂` cells to the precision they are computed at
(three decimals below), and always name the label when a `λ` is derived from a fitted curvature.**

Both tests are **our arithmetic** on the sources' numbers; they are not literature claims.

## R1.10.2 Family F1 — f-HAT from phenolic antioxidants to `•OOH`, water

**source**: *Antioxidants* **15**(7), 840–860 (2026), DOI `10.3390/antiox15070868` (OA, `PMC13405240`),
"Computational Study of the Peroxyl Radical Scavenging Ability of Phenolic Antioxidants".
**locus**: **Table 1**, "Water" columns (`ΔG°`, `ΔG≠`), 298.15 K. **status**: `first-hand` (JATS full text,
`https://www.ebi.ac.uk/europepmc/webservices/rest/PMC13405240/fullTextXML`). **Reaction family**: H-atom
transfer from a phenolic O–H to a peroxyl radical (`f-HAT`); 20 substrates, 31 solvated rows with a printed
water barrier.

| substrate | `ΔG°` /kcal·mol⁻¹ | `ΔG‡` /kcal·mol⁻¹ | `ΔG°` /kJ·mol⁻¹ | `ΔG‡` /kJ·mol⁻¹ | `λ̂` /kcal·mol⁻¹ |
|---|---|---|---|---|---|
| 16(2) | −0.3 | 15.6 | −1.3 | 65.3 | 63.0 |
| 16(1) | −0.9 | 15.7 | −3.8 | 65.7 | 64.6 |
| 19(2) | **+1.9** | 17.3 | **+7.9** | 72.4 | 65.3 |
| 14(1) | −2.3 | 15.7 | −9.6 | 65.7 | 67.3 |
| 12 | −4.9 | 13.9 | −20.5 | 58.2 | 65.0 |
| 2 | −6.7 | 12.4 | −28.0 | 51.9 | 62.3 |
| 7 | −11.6 | 8.2 | −48.5 | 34.3 | 53.5 |
| 8 | −12.9 | 8.8 | −54.0 | 36.8 | 58.1 |
| 10† | −19.1 | (none) | −79.9 | (none) | — |

† no printed water barrier for that row (only the PE barrier), so it cannot enter the water family.
**Family verdicts (ours):** all 31 printed pairs admit `λ̂ > 0` (`λ̂` mean **61.5**, sd 4.5, range
53.5–67.3 kcal/mol ≈ **257 kJ/mol**, range 224–282); fitted curvature `d²Ea/dx² = −0.0160` ⇒ `λ = −15.7
kcal/mol` ⇒ **INCONSISTENT with the constant-λ two-parabola law**. Free linear BEP fit:
`Ea = 16.6 − 0.613x` kcal/mol, **R² = 0.934**.

## R1.10.3 Family F2 — same reaction, solvent pentyl ethanoate (PE)

**source / locus / status**: same paper, **Table 1**, "PE" columns; 34 printed pairs; `first-hand`.

| substrate | `ΔG°` /kcal·mol⁻¹ | `ΔG‡` /kcal·mol⁻¹ | `ΔG°` /kJ·mol⁻¹ | `ΔG‡` /kJ·mol⁻¹ | `λ̂` /kcal·mol⁻¹ |
|---|---|---|---|---|---|
| 16(2) | +1.0 | 14.0 | +4.2 | 58.6 | 54.0 |
| 13 | −2.2 | 13.3 | −9.2 | 55.6 | 57.5 |
| 19(2) | +3.1 | 14.6 | +13.0 | 61.1 | 52.0 |
| 2 | −4.6 | 10.0 | −19.2 | 41.8 | 48.8 |
| 1 | −6.3 | 9.1 | −26.4 | 38.1 | 48.2 |
| 8 | −9.2 | 8.5 | −38.5 | 35.6 | 50.7 |
| 10 | **−14.3** | **5.1** | −59.8 | 21.3 | 44.4 |

**Family verdicts (ours):** all 34 pairs admit `λ̂ > 0` (mean **50.3**, sd 3.7, range 44.4–57.5 kcal/mol
≈ **211 kJ/mol**); curvature `−0.0253` ⇒ `λ = −9.9` ⇒ **INCONSISTENT**; linear fit `Ea = 14.5 − 0.498x`,
**R² = 0.548**.

**Solvent comparison (ours — the cleanest new fact here):** with the *same* substrates, the implied
reorganization energy is solvent-dependent: water **61.5** vs pentyl ethanoate **50.3** kcal/mol
(Δλ ≈ 11 kcal/mol ≈ 47 kJ/mol). "The family" must therefore be indexed by **solvent** as well as by the
reacting pair; one `λ` cannot cover both solvents.

## R1.10.4 Families F3/F4 — the same substrates with `•OOCH₃` (a second radical)

**source / locus / status**: same paper, **Table 2** ("Water" and "PE" columns), 31 and 34 printed pairs,
`first-hand`.

| solvent | n | mean `λ̂` /kcal·mol⁻¹ | `λ̂` range | curvature | curvature verdict | linear BEP fit | R² |
|---|---|---|---|---|---|---|---|
| water | 31 | **59.4** (≈249 kJ/mol) | 46.9–68.2 | −0.0074 ⇒ `λ = −33.6` | **INCONSISTENT** | `Ea = 15.5 − 0.651x` | **0.934** |
| PE | 34 | **53.4** (≈223 kJ/mol) | 43.8–57.9 | −0.0046 ⇒ `λ = −54.8` | **INCONSISTENT** | `Ea = 13.7 − 0.585x` | **0.952** |

Representative water rows (kcal/mol): `16(1)` `ΔG° +0.8`, `ΔG‡ 15.6`; `19(2)` `+3.6`, `17.7`;
`1` `−7.1`, `11.0`; `7` `−9.9`, `7.3`; `10` `−17.3`, no printed water barrier.
**Table 3** of the same paper is a **single-electron-transfer** series: it is **not** a HAT/BEP family and
is **deliberately excluded** from this table.

## R1.10.5 Family F5 — site-resolved C–H abstraction, classical CCSD(T) energies

**source**: *Chem. Sci.* **6**(10), 5866–5881 (2015), DOI `10.1039/c5sc01848j` (OA, `PMC5950756`).
**locus**: **Table 1**, row `CCSD(T)-F12a/jun-cc-pVTZ`. **status**: `first-hand` (JATS full text).
**Reaction family**: H abstraction from the five distinct C–H sites of **2-butanol** by `•OOH`. The table
prints a **classical reaction energy `ΔE`** and a **classical forward barrier `V‡f`** — `ΔE` is an
*energy*, **not** a Gibbs energy (the `ΔE`-vs-`ΔG` caveat applies to every row).

The five rows below were re-verified against the source in round 1j (`V‡f` = 20.32, 12.38, 17.57, 17.47,
21.72 and `ΔE` = 15.80, 7.62, 13.14, 14.56, 19.82 kcal·mol⁻¹, for (R1)–(R5)); the `λ̂` column was
**corrected** in that round (see the correction note after the table).

| site | `ΔE` /kcal·mol⁻¹ | `V‡f` /kcal·mol⁻¹ | `ΔE` /kJ·mol⁻¹ | `V‡f` /kJ·mol⁻¹ | `λ̂` /kcal·mol⁻¹ |
|---|---|---|---|---|---|
| R2 | 7.62 | 12.38 | 31.9 | 51.8 | 32.493 |
| R3 | 13.14 | 17.57 | 55.0 | 73.5 | 39.645 |
| R4 | 14.56 | 17.47 | 60.9 | 73.1 | **34.640** |
| R1 | 15.80 | 20.32 | 66.1 | 85.0 | 44.007 |
| R5 | 19.82 | 21.72 | 82.9 | 90.9 | **36.468** |

**Family verdicts (ours):** all five pairs admit `λ̂ > 0` (mean 37.4507, range 32.493019–44.007305
kcal/mol ≈ **157 kJ/mol**; spread 137–184 kJ/mol); curvature `−0.0203` ⇒ `λ = −12.3` under the curvature
convention (label note in §R1.10.1) ⇒ **INCONSISTENT**.

**CORRECTION (round 1j), caught by the cross-check script `theories/BEP/probes/bep-instance-check.py`.**
The two cells previously printed as `R4 = 41.6` and `R5 = 32.5` were **wrong** and are superseded by
`R4 = 34.640112` and `R5 = 36.468035`. **Verified for `R5`:** its wrong value is reproduced exactly by
evaluating that row with the **opposite sign orientation** of the driving force,
`λ̂(x = +19.82, Ea = 21.72) = 32.4930` — and the large root `λ̂ = x + 2Ea + 2√(Ea² + x·Ea)` is **not**
invariant under `x → −x`, so the orientation change silently replaces the correct root (`36.4680`) by a
mixture of the two. ⚠️ Two traps made this hard to see, recorded so they are not re-litigated: (i) the wrong
`R5` cell coincides numerically with the **correct** `R2` root (both `32.4930`); (ii) for `R4` the wrong
value `41.6` is **not reproducible from that row's own two printed numbers under any sign orientation or
column order** tried here (`97.8`, `92.3`, `34.6`, `6.1`, and the column swap has a negative discriminant),
so the proximate cause of that one cell is **not established** and is recorded as an unexplained
transcription-level defect rather than as a diagnosable convention error. Recomputed uniformly under
**`x = −ΔE`** (printed `ΔE > 0` ⇒ `x < 0`, i.e. the endergonic branch under the model's `x = -ΔG°`), the
large roots are `(R1, R2, R3, R4, R5) = (44.007305, 32.493019, 39.644841, 34.640112, 36.468035)`, mean
**37.4507**, range **32.493–44.007** — exactly the family summary printed *before* the correction, which
confirms the error was confined to those two cells. The conclusion (`λ̂ > 0` for every pair, negative family
curvature) is unchanged. **The record and the script now agree cell by cell** (R1/R2/R3 were already within
rounding: drifts +0.0073, −0.0070, +0.0448). The remaining families (§R1.10.2–§R1.10.4) were re-checked in
the same round against the same formula and are **correct as printed** (spot-checks: water `16(2)` → 62.999
vs 63.0; water `19(2)` → 65.345 vs 65.3; PE `10` → 44.394 vs 44.4).

## R1.10.6 The honest consequence for the instance layer

- **The BEP side works**: in four of five families a straight line through the printed pairs has
  R² = 0.93–0.95 (F2 is the exception at 0.55). Claim (i) — BEP as a first-order LFER — is what these data
  show.
- **The two-parabola side does not**: every family's fitted curvature is **negative**, while the model
  requires `d²Ea/dx² = 1/(2λ) > 0`. **No positive `λ` can reproduce any of these five families' shape**,
  however it is fitted. Equivalently, the barriers fall off **more slowly** than `λ/4 − x/2` over the
  observed `x`-range: a `λ̂` estimated at small `|x|` over-predicts the fall-off at large `x`.
- Consequence for claim (iv): "accuracy improves with larger `λ`" is a statement about the **model**; these
  data lie in a regime where the model's curvature has the **wrong sign** entirely. The instance layer may
  use these numbers as `(x, Ea)` **data rows**, but must not present them as a fit of the two-parabola law,
  and must not report a family `λ̂` as a measured reorganization energy.
- Consequence for `PhotoLean/BEP/Instances.lean`: families that must be *model-consistent by construction*
  should take their `λ` from the **model input** sets of the sibling records, while the five families above
  belong to a **data-validation** layer whose verdict is exactly "affine yes, constant-λ parabola no".

## R1.10.7 Families deliberately left unfilled (per the lead's instruction to report them)

| family | why it stays unfilled |
|---|---|
| Miller–Calcaterra–Closs 1984 series (dispatch option (b)) | the sibling record's `λ = 1.20 eV` and `x ∈ {0.05, 1.23, 2.40} eV` are **our own fit-derived `x` values**, not printed `(ΔG°, Ea)` pairs, and the primary series is paywalled; converting them would pass model-derived numbers off as data. **`not-accessed` for the pair table.** |
| reaction-centre numbers (Nobel 1992 p. 88) | printed with `~` as **quoted modelling numbers inside a lecture** (an overall exothermicity, not a family driving force), not a `(ΔG°, Ea)` table. **`not-accessed` for the pair table.** |
| Evans–Polanyi 1938 halogen/H₂ exchange data (§R1.3) | body `not-accessed` (RSC 403). **No numbers invented.** |
| combustion-model H-abstraction barriers (`J. Phys. Chem. A` **119**, 7652 (2015), Table 6) | barriers are printed as fitted `E/R`; the corresponding `ΔrH` were **`not-accessed`**, so **no pair can be formed**. |
| Denisov 2012 `(ΔH, Ee)` (`Russ. Chem. Rev.` **81**, 1117, Table 6) | barriers are **computed by that paper's own intersecting-parabola model**: usable as a self-consistency check, never as evidence. |
| HER BEP form (`npj Comput. Mater.` **10**, 98 (2024)) | the 14 metal points exist **only in a figure**; the printed `ΔG‡₀ = 0.7 eV`, `α = 0.5` are **fitted parameters, not point data**. |

---

# §R1.11 Naming caveat box — "Evans–Polanyi bounds" and the `0 ≤ α ≤ 1` claim

> **Naming caveat (binding on `theories/BEP/plan.md`).** The plan's `EPBounds` / `0 ≤ α ≤ 1` is a
> **model-side naming convention**. **No source read in this survey states `0 ≤ α ≤ 1` as a law of chemical
> families.** The literature analogues are:
> 1. the **electrochemical** transfer coefficient, where the bound *is* printed — Inzelt, in Scholz (ed.),
>    "For a symmetric barrier, `αa = αc = 0.5`, but, in general, `0 ≤ α ≤ 1` and, for a simple reaction
>    `αa + αc = 1`" (§R1.6.2, read first-hand) — with the IUPAC Technical Report 2014 (p. 249) adding that
>    the sum rule holds "only if the forward and backward electrode reactions are characterized by the same
>    rds". Inzelt's `α` is tied to current density and electrode potential, **not** to a
>    barrier-vs-driving-force slope;
> 2. the boundedness **under classical TST inside a family** (§R1.7(iv), source [Q3]): "Under classical
>    transition state theory, this responsiveness is bounded between 0 and 1, as expected from the Hammond
>    postulate" — a statement about *the family's* responsiveness under a stated theory, not a law over all
>    chemical series;
> 3. **documented series with a coefficient outside `(0,1)`**: Dodd 2004, printed p. 27, reports `α = −0.7`
>    and `α = 1.7` for one system depending on the axis, and states the origin of the `(0,1)` habit —
>    "Restriction of the Brønsted coefficients to values between 0 and 1 arose from the application of the
>    Brønsted relationship predominantly to oxygen or nitrogen acids and bases …" (§R1.6.3 item 4);
>    Kresge 1974's abstract reports a **negative** Brønsted exponent *and* exponents greater than unity for
>    nitroalkane series; García-Padilla & Qiu 2025 give the **extreme-limit** behaviour `α → 0` exergonic,
>    `α → 1` endergonic (§R1.6b);
> 4. **no slope bound anywhere** in the IUPAC physical-organic glossary's BEP entry, which has no Note at
>    all (0 hits for `transfer coefficient`, `Tafel`, `overpotential`, `electrode`; §R1.2.1, §R1.2.3).
>
> **Therefore:** `0 ≤ α ≤ 1 ⟺ -λ ≤ x ≤ λ` is a **theorem about the model's own coefficient** (with
> `EPBounds` documented as a plan-internal name); the electrochemical bound may be cited as the source of
> the **name** together with its `α_a + α_c = 1` / same-rds context; and the outside-`(0,1)` series above
> belong in the plan's honesty table as the counterexamples. The lead has mirrored this caveat in
> `theories/BEP/plan.md` §1.2 item 4 and its §13 honesty table; this box is the record-side counterpart.

---

# §R1.12 Status of every outstanding round-1 item (as of the round-1b pass)

| item | status now |
|---|---|
| B5b data table (≥ 4 families, ≥ 2 pairs, kJ/mol, provenance) | **DELIVERED — §R1.10**: five families, **all five `first-hand`**; per-pair `λ̂ > 0` in all five, and the **stronger curvature test fails in all five** (reported, not fixed) |
| naming caveat on `0 ≤ α ≤ 1` | **DELIVERED — §R1.11** |
| complementarity `β_f + β_r = 1` | §R1.6 (first-hand: *Chem. Sci.* 2025 eqn (1)–(2); IUPAC TR 2014 pp. 247/249; Inzelt p. 36) |
| IUPAC glossary entries verbatim | §R1.2 (first-hand, version of record) |
| Brønsted 1924 / 1928 **bodies** | **`not-accessed`** — closed at the publisher (Crossref records verified, §R1.4). *No wording is attributed to either paper anywhere in this file*; the relation they are cited for is carried by the IUPAC entry (§R1.2.2) |
| Leffler 1953 **body** | **`not-accessed`** (closed, §R1.5). Its equation *form* is carried by (i) the IUPAC glossary `δΔ‡G = α Δ_rG°` (p. 454, first-hand) and (ii) an **attributed modern reproduction** in *Chem. Sci.* 16(37):17494 (2025) — **not** from Leffler's own typography |
| Semenov relation | **`not-accessed`** — no formula, no lettering, no page (§R1.3) |
| Evans–Polanyi 1938/1936, Bell 1936 **bodies** | **`not-accessed`** (RSC / Royal Society 403; §R1.3). Accessible mirrors of these classics included **pirated copies, deliberately not used** — hence `not-accessed` rather than "read" |
| derivation-context entries (Marcus 1956 eq. (38) p. 974 / eq. (44) p. 975; Cohen–Marcus 1968; Marcus 1968 eq. (32) p. 896) | cross-referenced, not re-retrieved (`theories/Marcus/LITERATURE.md` §3.1–§3.3; `theories/hammond/LITERATURE.md` S6–S11). **Added from the round-1b pass:** Marcus 1968's abstract verbatim (`ΔF* = (λ(1 + Δ/λ)²)/4`; additivity `λ₁₂ = (λ₁₁+λ₂₂)/2`; 45 barriers from ten) and Cohen & Marcus 1968's (instantaneous slope `(1/2)[1 + (ΔF°'/4ΔF₀*)]`, 16 series, "more data are needed"); Marcus 1992 Nobel **p. 82** (inverted region; "similar to the usual trend in 'Bronsted plots' … and in 'Tafel plots'") and **p. 85** ("a slope of 1/2, when [ΔG°] is small") re-read first-hand |
| tunnelling / KIE / entropy-prefactor breaking the common-prefactor premise | **deliberately unfilled** — no first-hand source obtained; the nearest verified support is indirect (IUPAC TR 2014's same-rds restriction, §R1.6.3 item 2; *Faraday Discuss.* on coverage/RDS giving non-constant Tafel slopes). **Do not cite a source for this premise.** |
| experimental (non-computed) `(ΔH, Ea)` pairs | **deliberately unfilled** — none retrieved. Every family in §R1.10 is a **computed** (DFT/CCSD(T)) series; no number in this file comes from an experimental measurement |
| Semenov's `b ≈ 0.25` | **deliberately unfilled** — no locus could be verified; §R1.3 stays `not-accessed` |

---

# §R1.13 Round-1c — three first-hand corrections with printed equation numbers (supersede earlier entries)

## R1.13.1 ⚠️ The quadratic barrier formula is **Marcus 1968 eq. (2), p. 891** — it is **NOT in Marcus 1956**

**What was checked.** Local PDF `theories/Marcus/literature/Marcus1956_ET_theory_I.pdf` (13 pp.), extracted
three ways (`pdftotext` plain / `-layout` / `-raw`), all whitespace collapsed, case-insensitive counts:

| string | hits in Marcus 1956 |
|---|---|
| `parabola`, `intersect`, `quadratic`, `slope`, `alpha`, `Bronsted`, `Semenov`, `Bell`, `Polanyi` | **0 each** |
| `Evans` | **1** — and it is footnote 9(b), "D. D. Eley and M. G. Evans, *Trans. Faraday Soc.* **34**, 1093 (1938)" — a paper on the **page 1093 of the same volume**, not the 1938 *page 11* BEP paper |
| `(1 + …` | 4 hits, **all dielectric**: Eq. (48)/(54)/(59)-type expressions `E*(r) = E_t*(r)/(1 + 4πa…)`, not a barrier formula |

⇒ **The identity `ΔF* = λ(1 + ΔF⁰'/λ)²/4` does not occur in Marcus 1956 in any extractable form.** The 1956
paper supplies Eq. (38) (electronic barrier, printed p. 974) and the rate form Eq. (44)/(47)
(`k = Z exp(−ΔF*/kT)`, pp. 975/976) — the two-parabola *picture* is there, the *quadratic law and its
slope* are not.

**Correct home of the quadratic law** (both read first-hand, §R1.13.2 and the sibling record):
**Marcus 1968, Eq. (2), printed p. 891**: `ΔF* = w_r + λ(1 + ΔF⁰'/λ)²/4`.

**Impact**: any plan text, Lean docstring or `RESULTS` sentence that attributes
`λ(1 + ΔF⁰'/λ)²/4` (equivalently `(λ - x)²/(4λ)`) to **Marcus 1956** is a **mis-citation** and must be
re-pointed to **Marcus 1968 eq. (2), p. 891**, with 1956 cited only for the barrier derivation Eq. (38),
p. 974. This is the same class of correction the Hammond record already applied for the α formula
(`theories/hammond/LITERATURE.md` §9 item 2).

## R1.13.2 ⭐ The decisive new locus: Cohen & Marcus 1968, **eqs. (5a)–(5c), printed p. 4250**

**source**: Cohen, A. O.; Marcus, R. A., "On the slope of free energy plots in chemical kinetics",
*J. Phys. Chem.* **72**(12), 4249–4256 (1968), DOI `10.1021/j100858a052`.
**status**: `first-hand` — **full-text scan of the issue** (`http://lib3.dss.go.th/fulltext/scan_ebook/j.of_physical_1968_v72_n12.pdf`,
60 296 299 bytes, HTTP 200), page map verified against running heads (`printed = PDF + 3938`; PDF 311 = 4249).
Symbols: the OCR prints `λ` as `X` and the Greek alpha as `a` / `7 2` for `½`.

**VERBATIM** (printed p. 4250, all four displayed equations as the scan gives them):

> "`A = ΔF°' + RT ln(s_r/s_p)` (2)"
>
> "If the Bronsted slope `a` is defined as the slope of `ΔF*` vs. `A` or of the corresponding plot based on
> eq 4, we have — **`a = ½[1 + (A/λ)]` (|A| < λ) (5a)** — **`a = 0` (`A < −λ`) (5b)** — **`a = 1` (`A > λ`) (5c)**
> — where in the case of eq 4 `λ` is replaced by `λ_E` and `A` by `ΔE°`."

and, on the same page, the datum that this is an empirical comparison: "**Data for 16 series of reactions
are considered, 11 of them being proton transfers**"; and the authors' own caveat (printed p. 4254):
"…the data are consistent with eq 1 or its counterpart." / "**There is no assurance that λ should be
constant** … additional data could force a different view."

**Why this is the most useful single locus in the whole record:**
1. it is the **primary source of the coefficient formula** in the *same author's* series (not an abstract);
2. it states the **range clause as a strict inequality**, `|A| < λ` — exactly the model's
   `-λ < x < λ`, sharpening the previously recorded "`|ΔF°'| ≲ λ`";
3. it states **the extreme branches explicitly** — `α = 0` for `A < −λ`, `α = 1` for `A > λ` — i.e. the
   model's boundary values `α = 0` at `x = λ` and `α = 1` at `x = −λ` **are printed in the primary
   literature** as the outside-range behaviour, *not* as members of the `(0,1)` family;
4. `A` carries an explicit statistical/work term, `RT ln(s_r/s_p)`, so the model's identification
   `x = −A` (rather than `x = −ΔF⁰'`) is the faithful one; and the same paper's footnote 9 says its
   eqs 1–3 "differ from eq 1, 2, and 6 in ref 7 only in that we have **excluded work and steric terms**"
   — i.e. the reference formula and the model's zero-work-term form are the *same* object.

**Impact**: cite **Cohen & Marcus 1968, eqs. (5a)–(5c), printed p. 4250** — not the abstract — for (a) the
coefficient formula `α = ½ + A/(2λ)`, (b) the strict range `|A| < λ`, and (c) the branch values `0` and `1`.
The same locus also **replaces** the abstract's normalized form `(1/2)[1 + (ΔF°'/4ΔF₀*)]` as the primary
statement (the abstract is the `ΔF₀* = λ/4` rewriting of the same sentence).

## R1.13.3 ⭐ Primary-source locus for the "two intersecting parabolas" and the resemblance reading

Both first-hand in **Marcus 1968**, `10.1021/j100849a019` (issue scan
`http://lib3.dss.go.th/fulltext/scan_ebook/j.of_physical_1968_v72_n3.pdf`, `printed = PDF + 766`):

- **printed p. 892, Eq. (8a)**: from `λ₁₂ = E(1 + ΔE°/4E)²` (the cross-relation form of the same law);
- **the parabola picture is named on printed p. 894**: "… the other (see Appendix II) having a **pair of
  intersecting potential energy parabolas**."; and **printed p. 897 (Appendix II)**: "If the potential
  energy of a reaction along the reaction coordinate involves a pair of intersecting parabolas, eq 8a is
  obtained." ⇒ the model's two-parabola **picture** is citable to Marcus 1968 pp. 892/894/897 (and, for the
  projection caveat, to Appendix II p. 897–898 per the sibling record) — **not** to Marcus 1956;
- **printed p. 896**: the already-recorded "α would characterize the **product-like character** of both
  types of coordinates", plus the textbook-grade sentence that "the Brønsted slope reflects the extent to
  which the activated complex resembles the reaction products (e.g., our eq 31)" — a **third** independent
  statement of the slope↔resemblance reading, alongside IUPAC's Leffler entry and Cohen & Marcus (5a).

**Clean negative carried forward (and it is a strong one)**: in Marcus 1968 the names
`Evans`, `Polanyi`, `Semenov`, `Hammond` occur **0 times**; in Cohen & Marcus 1968 the only occurrence of
Evans & Polanyi (1936/1938) and of Semenov (1958, p. 8) is **footnote 3 on printed p. 4249**, and their 17
`Bell` hits are all other R. P. Bell works — **Bell 1936 is not cited there**. So the two papers that
supply the model's quantitative law do **not** themselves connect it to the BEP name: the naming link is
supplied only by **IUPAC's glossary entry (p. 369, §R1.2.1)** and its "captures earlier ideas …
(1936-38)" note on the Marcus-equation entry.

## R1.13.4 Bell 1936 and Evans–Polanyi 1938 — access status (final for this round)

- **Bell 1936**, `10.1098/rspa.1936.0060`: body **`not-accessed`**. Additional negative from the round-1c
  pass: **not cited by either 1968 Marcus paper** (§R1.13.3). What *is* first-hand is only its
  **bibliographic role**: IUPAC's BEP entry reference `[66]` (§R1.2.1) and the reference lists of two
  accessible modern papers (an *npj Comput. Mater.* **10**, 60 (2024) reference `12`, and arXiv:0705.0838
  ref. `[4]`). **No claim about its content is made anywhere in this file.**
- **Evans & Polanyi 1938**, `10.1039/TF9383400011`: body **`not-accessed`** — RSC landing **and** the
  `/articlepdf/1938/tf/tf9383400011` route both HTTP **403** (with browser headers and Referer); `doi.org`
  403; Unpaywall `is_oa=false`, `oa_locations=[]`; Semantic Scholar `openAccessPdf = CLOSED`; OpenAlex
  `oa_status = closed`, `any_repository_has_fulltext = false`, and its `abstract_inverted_index` contains
  only the placeholder "The first page of this article is displayed as the abstract."; `archive.org` /
  `web.archive.org` / `ia*.us.archive.org` / HathiTrust / Biodiversity Heritage Library time out or 403;
  the DSS library scan collection (9 109 files) contains **no** Faraday Society volume (`grep -i faraday`
  = 0). ⇒ **no wording, no equation number and no page of the 1938 paper is attributed anywhere in this
  file**, and the plan may not describe what the 1938 paper "says".
- **Semenov 1935/1958–59**: still `not-accessed` (no formula, no lettering); Polanyi 1963 *Science* **141**,
  1010 also `not-accessed` (publisher 403, not OA anywhere reachable).

## R1.13.5 Net effect of §R1.13 on the plan (delta to §R1.12 and to §R1.11)

| item | change |
|---|---|
| the quadratic barrier law `(λ - x)²/(4λ)` | cite **Marcus 1968 eq. (2), p. 891** (and Cohen & Marcus 1968 eqs (5a)–(5c), p. 4250). **Remove any attribution to Marcus 1956.** |
| the range clause for the affine coefficient | upgrade to **`\|A\| < λ`, strict, printed** (Cohen & Marcus 1968 eq. (5a), p. 4250), with `A = ΔF°' + RT ln(s_r/s_p)` (their eq. (2), p. 4249) ⇒ the model's `x` corresponds to `−A`, work terms excluded by their own footnote 9 |
| the branch values `α = 0` / `α = 1` at the range ends | now have a **primary locus** (eqs (5b)/(5c), same page) as the *outside-range* behaviour; **this reinforces §R1.11**: the `(0,1)` interval is exactly the interval where the **linearization is being used**, not a law about families |
| the two-parabola picture | cite Marcus 1968 pp. 892 (Eq. (8a)), 894 and 897 (Appendix II) |
| the slope↔"product-like character" reading | third independent locus: Marcus 1968 p. 896 (plus p. 894's "resembles the reaction products") |
| Bell 1936 / Evans–Polanyi 1938 / Semenov / Polanyi 1963 | **no content may be cited** from any of them; naming/attribution only, from IUPAC's entry |

---

# §R1.14 Round-1d — the "is `β = 1/2` a law?" locus, and one anti-circularity clarification

## R1.14.1 ⭐ Ooka, Huang & Exner 2021 — printed **pp. 9–10** (first-hand, gold OA)

**source**: Ooka, C.; Huang, J.; Exner, K. S., "The Sabatier Principle in Electrocatalysis: Basics,
Limitations, and Extensions", *Front. Energy Res.* **9**, 654460 (2021), DOI `10.3389/fenrg.2021.654460`.
**status**: `first-hand` — gold-OA PDF (`https://www.frontiersin.org/journals/energy-research/articles/10.3389/fenrg.2021.654460/pdf`,
3 605 851 bytes, HTTP 200), 20 pp.; **page map exact** (the running footers print
"Frontiers in Energy Research | www.frontiersin.org *n* May 2021 | Volume 9 | Article 654460" with *n* = the
PDF page number, verified for all 20 pages). OCR caveat: `pdftotext` renders `Δ` as `1`, `‡` as `#`, and
flattens the fraction in eq. (2); the sentences below are what is verified, symbol restoration is flagged.

**Locus 1 — §"Validity of the BEP Relationship", printed p. 9 (sentence continues onto p. 10):**

> "… the BEP relationship is in **direct contradiction to the Marcus theory of electron transfer**, and
> therefore, in some cases, it does not depict the free-energy landscape accurately."

**Locus 2 — printed p. 10, verbatim (OCR-restored symbols in brackets):**

> "[In the case where] ΔG_RI‡ = β ΔG_RI, where β denotes the so-called **BEP coefficient (0 < β < 1)** …"
>
> "As for the value of the BEP coefficient, **β = 0.5 is a frequent assumption, although there is no
> physical basis for why β should be 0.5 or why it should be independent of the material** … There is also
> **no basis for why β should be constant throughout the various elementary steps** of [a reaction]."
>
> "… once the overpotential is increased beyond a certain point, the free energy of activation starts to
> increase. **This corresponds to a negative BEP coefficient, which is a direct contradiction to the
> assumption of 0 < β < 1.**"
>
> "… β = 0.5 is only a convenient assumption for theoretical analysis and **should be treated as such**."

**Locus 3 — printed p. 7, their eq. (2)**: the quadratic law in the form
"ΔG_RI‡ = (λ + ΔG_RI)²/(4λ)" (the OCR prints `1GRI # = (λ+1G 4λ RI ) )`; the fraction is flattened).

**Why this matters for the plan (three consequences):**
1. the printed quadratic form `(λ + ΔG_RI)²/(4λ)` is **verbatim the model's law** with `ΔG_RI = -x`, giving
   the plan's `Ea = (λ - x)²/(4λ)` a **modern, first-hand, open-access locus** in addition to Marcus 1968
   eq. (2) p. 891 and IUPAC p. 419;
2. **`β = 1/2` has an explicit published disclaimer** — "no physical basis for why β should be 0.5 or why it
   should be independent of the material" and "no basis for why β should be constant throughout the various
   elementary steps". So the model's exact `α(0) = 1/2` may be stated **only at thermoneutrality**, never as
   an unconditional `α = 1/2`; this is the strongest single citation for that restriction;
3. **the `0 < β < 1` reading of the literature is itself an assumption** on their account, and they document
   the regime where it fails ("a negative BEP coefficient, which is a direct contradiction to the assumption
   of 0 < β < 1") — a third independent counterexample class alongside §R1.11's Dodd/Kresge entries and
   §R1.10's negative curvatures.

## R1.14.2 Anti-circularity clarification on the Denisov 2012 table (§R1.10.7, and a caution for the instance layer)

The `(ΔH, Ee)` table quoted in the round-2 delegation (`Russ. Chem. Rev.` **81**, 1117 (2012), Table 6,
printed pp. 1125–1126) is **computed from that review's own intersecting-parabola equations (23)–(24)**
(the table is titled as such). Consequently:

- any "two-point BEP slope" computed from those rows (e.g. `≈ +0.50 … +0.56` within the saturated subset,
  or `≈ −0.74` across to an allylic C–H) is a **property of the parabola model that produced the table**,
  *not* an independent experimental slope. Using such a number as evidence that the model works would be
  **circular**: the same functional form is on both sides of the comparison;
- the same objection does **not** apply to §R1.10's families F1–F5, whose barriers come from
  DFT/CCSD(T) electronic-structure calculations (a different theory from the two-parabola law);
- therefore the record's standing rule is unchanged and now explicit: **Denisov 2012 rows may be used only
  as a self-consistency check of the algebra, and must never be entered in the instance layer as
  `provenance: literature` data.**

## R1.14.3 Cross-reference on the electrochemical complementarity (no change to §R1.6.2)

The general electrochemical relation is **`α_c + α_a = n/ν`** (IUPAC Technical Report 2014, eq. (17),
printed p. 249, read first-hand via the Universidad de Alicante repository copy), with eq. (16)
`α_c + α_a = n` for `ν = 1`; **`β_f + β_r = 1` is the single-electron / `n = ν = 1` special case.** The
repository's `transfer lam x + reverseTransfer lam x = 1` is a **model theorem** (§R1.6.4) and needs no
literature premise; if `RESULTS.md` places it beside citations, the naming caveat of §R1.11 should be
extended from "the `0 ≤ α ≤ 1` bound" to **also cover the sum rule** — i.e. state that the literature form
is `n/ν` and that the `= 1` form presupposes one electron in one rate-determining step.

---

# §R1.15 Round-1e — the outliers `α > 1` and `α < 0`: the bounded-coefficient claim settled by primary sources

## R1.15.1 ⭐ Pogorelyi & Vishnyakova 1984, printed **p. 1160** (first-hand) — and its formalizable consequences

**source**: Pogorelyi, V. K.; Vishnyakova, T. B., "The Hydrogen Bond and CH Acidity",
*Russ. Chem. Rev.* **53**(12), 1154–1167 (1984), DOI `10.1070/rc1984v053n12abeh003145` — Crossref-verified
here (title/volume/issue/pages/year/authors exact). **status**: `first-hand` — free PDF
(`https://www.russchemrev.org/RCR3145pdf`, 1 963 068 bytes, HTTP 200); the page header inside the text layer
prints "1160 Russian Chemical Reviews, 53 (12), 1984", so the locus is a **printed page, not a PDF offset**.
OCR renders "Brønsted" as `Brdnsted` / `Br^nsted`.

**VERBATIM (printed p. 1160):**

> "**Anomalous values of the Brønsted coefficient (`α < 0` and `α > 1`) are most characteristic of CH acids
> containing the nitro-group.**"
>
> "… the relative rates of abstraction of protons by hydroxide ions diminish (111 : 18 : 1) in the same
> sequence. **The coefficients `α = −0.7` and `β = 1.7` are anomalous.**"
>
> "For example, **`α = 1.67`, `1.61`, `1.42`, and `1.56` have been found for nitroalkanes having the formulae
> R(CH₃)₂NO₂, ArCH₂CH(CH₃)NO₂, ArCH(CH₃)NO₂ and ArCH₂NO₂**, respectively."
>
> "It must also be emphasised that **all systems with `α > 1` included a fixed base. If the base is varied for
> the same nitroalkane, then the Brønsted coefficient returns to the range within the "normal" limits, i.e.
> `0 < α < 1`.**"

**Formalizable implications (this is the strongest single item for the plan's premises):**

1. **`0 ≤ α ≤ 1` is not a law of chemical families** — with printed values `α = −0.7` and `β = 1.7` on the
   *same* page, plus `1.42–1.67` for four named nitroalkanes. Together with §R1.11 this closes verdict (ii):
   the bound is a **model theorem**, and the literature counterexamples now have page-level loci.
2. **⭐ NEW PREMISE (the delegate's point (d), now first-hand): a "family" must vary exactly one parameter.**
   The "fixed base" sentence says the anomalous slopes appear when the **substituent** varies at fixed base,
   and that varying the **base** for the same nitroalkane restores `0 < α < 1`. Hence a substituent series and
   a base series are **different objects** and a verdict obtained on one may not be transferred to the other.
   In Lean this can only be a *declared* restriction on the family index (a chemistry-level predicate), so it
   belongs in the premise register and in the instance-layer doc comments.
3. **The `(0,1)` interval is an empirical habit, not a theorem** — the same 1984 review writes the "normal"
   range as `0 < α < 1` and documents when it fails, which is exactly the shape §R1.11 records.

## R1.15.2 Mayr & Ofial 2023, printed **pp. 7–8** (first-hand) — `α` is a **partial** function

**source**: Mayr, H.; Ofial, A. R., "When Does Hammond's Postulate Predict Stabilities of Carbocations?",
*Isr. J. Chem.* **63**, e202300054 (2023), DOI `10.1002/ijch.202300054` — Crossref-verified; Unpaywall
`is_oa=true`, repository copy (read here): `epub.ub.uni-muenchen.de/108875/1/Israel_Journal_of_Chemistry_-_2023_-_Mayr_-_When_Does_Hammond_s_Postulate_Predict_Stabilities_of_Carbocations.pdf`
(5 654 849 bytes, HTTP 200, 11 PDF pp.; the Wiley watermark on each page reads
"18695868, 2023, **7-8**, Downloaded from https://onlinelibrary.wiley.com/doi/10.1002/ijch.202300054").

**VERBATIM:**

> "Bordwell's observation that deprotonations of **nitroalkanes have `α` values around 1.5** clearly shows that
> **`α` is not limited to the range `0 < α < 1`, and therefore cannot be an indicator of the position of the
> transition state**."
>
> "Pross pointed out that in **identity reactions**, e.g. isotope exchange reactions of the type
> `R–Cl + *Cl → R–*Cl + Cl`, substituent variation affects `ΔG‡` while **`δΔG_r° = 0` with the consequence
> that `α = δΔG‡/0 = ∞`**."

**Formalizable implication (the delegate's point (c), now first-hand): the empirical `α` is a *partial*
function.** A vanishing driving-force difference makes the fitted coefficient undefined (`0/0`-style), so any
Lean statement that reads a coefficient off a family must carry an explicit **non-degeneracy** hypothesis —
exactly the `h : x₁ ≠ x₂` already required by the repository's secant forms. The requirement is therefore not
new *mathematically*, but it is now **literature-forced**, and the plan may cite this locus for it.

## R1.15.3 The remaining premises the round-1e retrieval supports (status per item)

| premise the plan must declare | first-hand support | status |
|---|---|---|
| family = **exactly one parameter varied**; substituent series ≠ base series | Pogorelyi & Vishnyakova 1984, printed p. 1160 ("all systems with `α > 1` included a **fixed base** …") | `first-hand` |
| coefficient **non-degeneracy** (`δΔG° ≠ 0`; the analogue of `x₁ ≠ x₂`) | Mayr & Ofial 2023, printed pp. 7–8 (`α = δΔG‡/0 = ∞`) | `first-hand` |
| coefficient is a **measured interval**, not a point value | Gathmann, "Catalytic Resonance Theory…", PhD diss., Univ. of Minnesota (2024), OA `conservancy.umn.edu`, printed **p. 134**: 95 % confidence intervals of reported BEP slopes "ranging from ±0.02 to ±1.0" | `verified (delegated read)` — **not re-read here** |
| linearity needs **equal force constants and invariant H-transfer distance**, else the slope becomes a **sigmoid** function of `ΔE` | Koeppl & Kresge 1973, *J. Chem. Soc., Chem. Commun.* (11), 371–373, `10.1039/C39730000371` (quoted from its abstract) | `verified (delegated read)`; full text `not-accessed` |
| classical single-coordinate theory **cannot reproduce** an anomalous `α ≈ 1.4`; the authors attribute it to **reaction dynamics** | Yamataka & Ammal, *ARKIVOC* **2003**(x), 59–68, `10.3998/ark.5550190.0004.a08` (diamond OA), printed p. 60 / abstract p. 59 | `verified (delegated read)`; one retrieval returned HTTP 406, so treated as delegate-only |
| `w_r = w_p = 0` (no work terms) is an **approximation** that anomaly analyses may need | Agmon 1980, *J. Am. Chem. Soc.* **102**, 2164, `10.1021/ja00527a003` — abstract attributes the anomaly to **work terms** | `verified (delegated read)`; body `not-accessed` (closed) |
| a journal-version locus for the inverted region and the thermoneutral slope | Marcus, *Rev. Mod. Phys.* **65**, 599–610 (1993), `10.1103/RevModPhys.65.599`, CaltechAUTHORS `ta6z9-5ac64`: inverted region at printed **p. 605**, the slope-`1/2` sentence at printed **p. 607** (that scan's text layer is badly garbled — **for the slope value keep quoting Nobel 1992 p. 85**) | `verified (delegated read)`; **Nobel 1992 pp. 82/84/85 remain `first-hand` here** |

**Note on Nobel 1992 pagination (correction of a detail, not a locus):** the lecture PDF is **24 pages**
(printed pp. 69–92); an earlier round's "12 pages" came from a truncated `file(1)` header. The three verified
loci (pp. 82, 84, 85) are unchanged, and the slope sentence on p. 85 carries its own restriction in the same
sentence — "with a slope of 1/2, **when [ΔG°] is small**" — which is precisely the qualification the plan
needs for `α(0) = 1/2` (together with §R1.14's "no physical basis for why β should be 0.5").

## R1.15.4 Effect on the plan (delta to §R1.11/§R1.12)

| # | action | why |
|---|---|---|
| 1 | inline the `α ∉ [0,1]` caveat **into the displayed formula** in plan §1.1, not only in §1.2 item 4 / §13 | the counterexamples are now page-level: `−0.7`, `1.42`, `1.56`, `1.61`, `1.67` (1984 p. 1160), `≈1.5` (Mayr 2023 pp. 7–8), `α → 0 / 1` (Cohen & Marcus 1968 eq. (5b)/(5c), p. 4250) |
| 2 | add the **non-degeneracy** premise for any "coefficient read off a family" statement, citing Mayr & Ofial pp. 7–8 | the empirical coefficient is a partial function (`δΔG‡/0`) |
| 3 | add the **one-parameter family** restriction to the premise register, citing Pogorelyi p. 1160 | substituent series and base series are different objects |
| 4 | if the instance layer asserts a measured slope for a family, carry its **confidence interval**, not a point value (delegate's Gathmann p. 134, `verified (delegated read)`) | reported slopes are interval-valued; this mirrors the plan's tolerance-window formulation |
| 5 | record that the **dynamics/single-coordinate approximation is needed twice over**: sigmoid slopes under unequal force constants (Koeppl & Kresge 1973) and anomalous `α ≈ 1.4` attributed to reaction dynamics (Yamataka & Ammal 2003) | both are `verified (delegated read)`; the plan should cite them as *reasons for the declared approximations*, not as data |
| 6 | no change to any proved or planned **theorem** | every item above is a premise-register or wording matter; the model's own identities (complementarity, `α = q‡`, the bounds) are unaffected |

---

# §R1.16 Round-1f — the bimodal (broken) EP family, and the npj-2024 metal family

## R1.16.1 ⭐⭐ The documented **violation** family: bimodal Evans–Polanyi in hydrogen-atom transfer

**source**: Salamone, M.; Galeotti, M.; Romero-Montalvo, E.; van Santen, J. A.; Groff, B. D.; Mayer, J. M.;
DiLabio, G. A.; Bietti, M., "**Bimodal Evans–Polanyi Relationships in Hydrogen Atom Transfer from
C(sp³)–H Bonds to the Cumyloxyl Radical. A Combined Time-Resolved Kinetic and Computational Study**",
*J. Am. Chem. Soc.* **143**(30), 11759–11776 (2021), DOI `10.1021/jacs.1c05566`.
**status**: `first-hand` — CC-BY full text via Europe PMC (`https://www.ebi.ac.uk/europepmc/webservices/rest/PMC8343544/fullTextXML`);
**locus**: review-level statement in the article's **abstract (opening printed page 11759)** plus the
Results discussion; the per-substrate `(k_H, BDE)` values live in the article's **Tables 1–3, which are
bitmaps in the OA copy — `not-accessed`** (no numbers are transcribed here).

**VERBATIM:**

> "The `log k_H′` vs C–H BDE plot shows **two distinct EP relationships**, one for substrates bearing benzylic
> and allylic C–H bonds (**unsaturated group**) and the other one, **with a steeper slope**, for saturated
> hydrocarbons, alcohols, ethers, diols, amines, and carbamates (**saturated group**), in line with the bimodal
> behavior observed previously in theoretical studies of reactions promoted by other HAT reagents."
>
> "**A good fit to the Marcus equation is observed only for the saturated group, with `λ = 58 kcal mol⁻¹`**
> (= 242.7 kJ/mol), indicating that with the unsaturated group **`λ` must increase with increasing driving
> force**."

**Why this is the most important single item in the whole record:**
1. it is a **documented, same-laboratory, same-conditions break** of the EP line into two branches, with the
   dividing line being **which kind of C–H bond is broken** (benzylic/allylic vs. saturated). That is the
   first-hand, page-level justification for the plan's "**same family / same bond type / same mechanism**"
   premise — not an inference from a computational screening, but a 56-substrate experimental + computational
   study;
2. **`λ` is explicitly not constant within a nominal family**: the Marcus fit works *only* for the saturated
   branch (`λ = 58 kcal mol⁻¹`), and the unsaturated branch requires **`λ` increasing with driving force**.
   So the record's fixed-`λ` premise must be marked as a **default contradicted in the literature**, not as a
   harmless idealization;
3. it supplies a **literature "violation" family** for the instance layer — i.e. the plan's non-conforming
   instance need not be model-constructed;
4. it also gives a third reason (after sigmoid slopes under unequal force constants, and the dynamics
   attribution of anomalous `α`) why the **two-parabola/equal-curvature** treatment is an approximation whose
   failure mode is documented rather than hypothetical.

## R1.16.2 The npj-2024 metal family — use the pairs, and mind what the `α` column is

**source**: "The Bell-Evans-Polanyi relation for hydrogen evolution reaction from first-principles",
*npj Comput. Mater.* **10**, 98 (2024), DOI `10.1038/s41524-024-01244-3` — Crossref-verified here
(vol. 10, article 98, 2024). **status**: `first-hand` for the supplementary table;
**locus**: **Supplementary Table 1** (SI PDF, 10 pp.,
`https://media.springernature.com/original/springer-static/esm/art%3A10.1038%2Fs41524-024-01244-3/MediaObjects/41524_2024_1244_MOESM1_ESM.pdf`,
HTTP 200), columns `Metal | ΔG_H (eV) | ΔG‡_DFT (eV) | R-type | α | ΔG₀‡ (eV) | ΔG‡_EXP (eV)`:

| metal | `ΔG_H` /eV | `ΔG‡_DFT` /eV | route | `α` | `ΔG₀‡` /eV | `ΔG‡_EXP` /eV |
|---|---|---|---|---|---|---|
| Pt | −0.082 | 0.6628 | H-Ⅲ | 0.48 | 0.608 | 0.65 |
| Ir | −0.136 | 0.7241 | H-Ⅱ | 0.42 | 0.6045 | 0.66 |
| Rh | −0.159 | 0.7055 | H-Ⅲ | **0.66** | 0.6117 | 0.72 |
| Pd | −0.176 | 0.7669 | H-Ⅲ | 0.50 | 0.678 | 0.77 |
| Re | −0.195 | 0.7013 | H-Ⅱ | 0.55 | 0.787 | 0.89 |
| Ru | −0.220 | 0.8418 | H-Ⅰ | 0.53 | 0.679 | 0.80 |
| Co | −0.252 | 0.9090 | H-Ⅱ | **0.37** | 0.671 | 0.76 |
| Ni | −0.280 | 1.0309 | H-Ⅰ | 0.47 | 0.764 | 0.90 |
| Ag | +0.559 | 1.0757 | V-Ⅲ | (blank) | — | — |
| Au | +0.532 | 0.9147 | V-Ⅱ | 0.42 | 0.583 | 0.81 |
| Cd | +1.031 | 1.1062 | V-Ⅲ | 0.43 | 0.692 | 1.14 |
| In | +0.912 | 1.1205 | V-Ⅲ | 0.48 | 0.742 | 1.18 |
| Bi | +1.071 | 1.3428 | V-Ⅲ | 0.46 | 0.782 | 1.27 |
| Cu | +0.250 | 0.7839 | V-Ⅲ | (blank) | — | — |

**This is the only family in the record whose driving force spans both signs** (`x = -ΔG_H` runs from
−51.3 kJ/mol for Bi to +27.0 kJ/mol for Ni), so it is the only one that can exercise the thermoneutral point.
Representative kJ/mol conversions (ours, ×96.485): Pt `(x = +7.91, ΔG‡ = 63.95)`; Ni `(+27.02, 99.47)`;
Au `(−51.33, 88.26)`; Bi `(−103.34, 129.56)`.

**⚠️ Caveat that must travel with the `α` column (this corrects a delegated reading of it).** SI Table 1's
own header says its `α` and `ΔG₀‡` values are "**obtained from fitting experimental cyclic voltammograms**"
for computing `ΔG‡_EXP`. They are therefore **electrochemical transfer coefficients fitted to
current–potential data of individual electrodes** — *not* BEP slopes fitted to this metal family's
`(ΔG_H, ΔG‡)` scatter, and therefore **`α` in this table is not comparable with the model's `α = ∂Ea/∂x`
without an additional modelling step**. What the column *does* establish, verbatim and usefully, is that the
apparent coefficient is **material-dependent, ranging 0.37–0.66 within one reaction class** (Co 0.37 … Rh 0.66),
which matches Exner's "ß may vary within a class of materials" (§R1.14.1) from a second independent group —
and it shows that the paper's own family treatment uses **fixed** "universal parameters
`ΔG₀‡ = 0.7 eV and α = 0.5`" (main text), i.e. the constancy there is an **assumption of the analysis**, not a
measured family slope.

**Precede with two explicit premises (they apply to every family in this file):**
- state **which thermodynamic quantity `x` is**: `−ΔH` (Pogorelyi-type series), `−ΔE` (classical CCSD(T) rows),
  or `−ΔG°` (this npj family and the phenolic-antioxidant family) — the model's `x` is free-energy-like;
- state **what `Ea` is**: an *elementary-step* barrier, an *apparent* barrier, or a **value computed by a
  model** (as in §R1.10's Denisov family, §R1.14.2).

## R1.16.3 Two reader warnings for anyone re-opening the sources

1. **Denisov 2012 (`Russ. Chem. Rev.` 81, 1117), Table 6 text layer mangles the minus sign as the digit `7`**
   (`719.5` should read `−19.5`). Anyone re-reading that file must correct this or will turn exothermic rows
   into endothermic ones. The same table's `Ee` values are model-computed (§R1.14.2) — **still not instance
   data**.
2. **`api.catalysis-hub.org` now requires an API key** (returns "Missing API key"), so that route for
   tabulated adsorption/dissociation energies is no longer available; `MDPI` direct 403s but Europe PMC
   serves the same OA articles. Both facts are recorded so the next round does not re-discover them.

## R1.16.4 Final status of the four round-1 deliverables

| deliverable | state |
|---|---|
| (1) primary sources with printed formulas and loci | **partly blocked, fully documented**: Evans–Polanyi 1938/1936, Bell 1936, Semenov 1935/1958, Polanyi 1963 all `not-accessed` (naming/attribution only); **the formula layer is carried instead by** Marcus 1968 eq. (2) p. 891, Cohen & Marcus 1968 eqs. (5a)–(5c) p. 4250, IUPAC p. 419, Ooka/Exner 2021 p. 7 and pp. 9–10 |
| (2) the normative statement + the coefficients | **done first-hand**: IUPAC pp. 369/375/453–454 + "Brønsted relation"/Leffler entries; complementarity via *Chem. Sci.* 2025 and IUPAC TR 2014 pp. 247/249; electrochemical bound Inzelt p. 36; outliers with printed pages |
| (3) the derivation context | **done**: Marcus 1968 (abstract + eq. (32) p. 896 + eq. (8a) p. 892 + picture pp. 894/897), Cohen & Marcus 1968 (abstract + eqs (5a)–(5c) p. 4250), Marcus 1992 Nobel pp. 82/85 (24 pp., pp. 69–92), Marcus 1956 **negatives** (no quadratic law) |
| (4) limits/violations | **done, with the strongest items read here**: bimodal/broken EP line + non-constant `λ` (§R1.16.1), negative slopes (§R1.10.2, §R1.10.3), outliers `α = −0.7 … 1.67` (§R1.15.1), `α>1` "unphysical" and zero-slope = barrierless (§R1.12/§R1.14), `β = 1/2` has "no physical basis" (§R1.14.1), material-dependent `α` 0.37–0.66 (§R1.16.2), partial-function `α` (§R1.15.2) |
| data table (5+ families, all first-hand) | **done**: §R1.10 (4 families: water/PE × `•OOH`/`•OOCH₃`) + §R1.10.5 (CCSD(T) sites) + §R1.16.2 (14 metals, both signs of `x`); per-family λ̂ verdicts; **all five tested families fail the constant-`λ` curvature test**, and the one literature violation family (§R1.16.1) states the same conclusion independently |

---

# §R1.17 Round-1g — the three `α` objects, and the electrochemical evidence that `α` is neither 1/2 nor constant

## R1.17.1 The electrochemical loci (second reader's page confirmation, and the sharpest sentence)

**source**: Guidelli, R.; Compton, R. G.; Feliu, J. M.; Gileadi, E.; Lipkowski, J.; Schmickler, W.;
Trasatti, S., "Defining the transfer coefficient in electrochemistry: An assessment (**IUPAC Technical
Report**)", *Pure Appl. Chem.* **86**(2), **245–258** (2014), DOI `10.1515/pac-2014-5026`.
**status**: `first-hand` — read here in §R1.6.2 and **independently re-read in round-1g** through the same
open repository route (Universidad de Alicante RUA, DSpace 7,
`https://rua.ua.es/server/api/core/bitstreams/57bdc35e-96c3-4973-a166-8ef4db5700e4/content`, 1 461 735 B,
HTTP 200; the page header inside the text layer prints "DOI 10.1515/pac-2014-5026  Pure Appl. Chem.
2014; 86(2): 245–258", so the printed page numbers are self-identifying).

**New VERBATIM locus — §5 Conclusions, printed p. 257:**

> "The numerical value of the transfer coefficient `α` **can by no means be assumed**; it can only be
> obtained by measuring the Tafel slope `dE/dln|j|`."
>
> "For an electrode process with the same rds in the cathodic and anodic directions, we have
> **`αc + αa = n/ν` (43)** where `n` is the total number of electrons involved and `ν` is the number of
> occurrences of the rds in the electrode reaction, as written. **The use of the cathodic symmetry factor,
> `βc`, and the anodic one, `βa`, should be confined to an overall electrode reaction consisting exclusively
> of a one-electron transfer step.**"

⇒ **`α_f + α_r = 1` holds in the literature only under `n = ν = 1` with the same rds in both directions.**
The general printed relation is `n/ν` (and, for multi-step reactions, the sum is not even a fixed number).
The repository's `transfer lam x + reverseTransfer lam x = 1` remains a **model theorem** (§R1.6.4) and needs
no literature premise — but any sentence that places it *beside* citations must add the `n = ν = 1` +
same-rds qualification.

## R1.17.2 ⭐ Three distinct `α`-like objects — keep them apart in the plan's wording

| object | definition / locus | what it is |
|---|---|---|
| (1) **observable electrochemical transfer coefficient** | IUPAC **Recommendations** 2014, §2 eq. (1), printed p. 259 (`10.1515/pac-2014-5025`, same volume 259–262): `αa = (RT/F)(dln ja/dE)`, `αc = −(RT/F)(dln|jc|/dE)` | an experimental quantity obtained from a Tafel slope; its value "can by no means be assumed" (p. 257) |
| (2) **the model's BEP slope** | this repository: `transfer lam x = 1/2 − x/(2λ)`, a theorem of the equal-curvature two-parabola model | a **model-internal** coefficient; equals `q‡`; `= 1/2` only at `x = 0` |
| (3) **Butler–Volmer symmetry factor / `β`** | IUPAC TR 2014 §3, printed pp. 255–256: "**if the two force constants are different, according to the asymmetric Marcus theory, then large deviations of `β` from 0.5 can be predicted**"; and Fletcher, *J. Solid State Electrochem.* **13**, 537–549 (2009) — the BV symmetry factor and the electron-transfer-theory symmetry factor **are not the same object** and need a conversion formula | a *different* coefficient again; equating (1) and (3) requires an extra premise |

**Formalizable implication**: the plan's docstrings must not write "`α`" as if it were one object. Object (2)
is what the Lean development proves things about; (1) is what a measurement yields; (3) is a third
convention. The three coincide **only** under stated symmetry/one-electron/same-rds assumptions.

## R1.17.3 ⭐ Electrochemical evidence that `α` is neither 1/2 nor constant (first-hand)

**source**: Shinagawa, T.; Garcia-Esparza, A. T.; Takanabe, K., "Insight on Tafel slopes from a microkinetic
analysis of aqueous electrocatalysis for energy conversion", *Sci. Rep.* **5**, 13801 (2015),
DOI `10.1038/srep13801`. **status**: `first-hand` — OA full text via Europe PMC
(`https://www.ebi.ac.uk/europepmc/webservices/rest/PMC4642571/fullTextXML`); **locus**: printed pp. 5–6
(the article's own rate-determining-step analysis).

**VERBATIM:**

> "The Tafel slopes used to evaluate the rate determining steps **generally assume extreme coverage of the
> adsorbed species (`θ ≈ 0` or `≈1`), although, in practice, the slopes are coverage-dependent.**"
>
> "**the same Tafel slopes can be obtained for different elementary steps with varied coverages.**"
>
> "… for the Heyrovsky rate determining step, **a Tafel slope of 120 mV dec⁻¹ was observed in the higher
> coverage region** (`θ_H > 0…`)" — and, quoted from the literature there, "Pt electrocatalysts supported on
> carbon (Pt/C) … exhibits a **Tafel slope of 30 mV dec⁻¹**" in acid, "**120 mV dec⁻¹** under PEMFC
> conditions, and "**125 mV dec⁻¹**" in another medium.

**Why this matters here:** a transfer coefficient read off a Tafel slope is (i) **coverage-dependent** and
(ii) **not unique to a rate-determining step** — the same slope can arise from different steps at different
coverages. Both statements are about the *apparent* coefficient of a real electrode, i.e. exactly the
quantity the plan's "same family, same mechanism" premise would need to be constant. So:

- the plan's "constant coefficient across the family" premise has a **third** independent literature
  counterexample class (after §R1.16.1's non-constant `λ` and §R1.11/§R1.15's out-of-range values), and this
  one is **kinetic** rather than thermodynamic (coverage/site change);
- it also reinforces why `transfer + reverseTransfer = 1` must stay a model theorem: the two coefficients
  would have to be measured on the same coverage regime and the same rds.

**Supporting delegated loci (not re-read here; `verified (delegated read)`)**:
Razzaq & Exner, *iScience* **27**(2), 108848 (2024) — `α₁ = α₂ = 0.50` is a **modelling assumption**, and
Tafel slopes jump (≈47 → ≈112 mV/dec) when the step ordering changes; Usama et al. (with Exner),
*Nat. Commun.* **16**, 6137 (2025) — measured OER Tafel slopes "**49 mV/dec. and 78 mV/dec.** … on
IrO₂(110) in acid", together with their own caution that inferring the rds from a Tafel slope requires
evaluating all transition states (a **declarative** limitation, not formalizable).

## R1.17.4 What this adds to the plan (final delta — no theorem changes)

| # | action | support |
|---|---|---|
| 1 | extend the §1.2 item 4 / §13 caveat from "the `0 ≤ α ≤ 1` bound is not a family law" to **"and neither is the complementarity `α_f + α_r = 1`"**, adding the `n = ν = 1` + same-rds qualification whenever it is placed beside citations | IUPAC TR 2014 eq. (43), printed p. 257 |
| 2 | keep the three `α` objects separate in docstrings/wording: observable transfer coefficient / model BEP slope / BV symmetry factor | §R1.17.2 |
| 3 | if RESULTS asserts constancy of a coefficient across a family, carry a **kinetic** caveat too (coverage- and site-dependence), not only a thermodynamic one | Shinagawa et al. 2015, printed pp. 5–6 |
| 4 | treat "this coefficient cannot be assumed; it must be measured" as a **wording rule** for the record: the model *derives* its coefficient, so any comparison with experiment must say which object is being compared | IUPAC TR 2014 p. 257 |
| 5 | no change to any proved or planned theorem | — |

---

# §R1.18 Round-1h — the premise set for "equal `λ`, equal work terms, same family", and the quantitative two-branch family

## R1.18.1 ⭐ The literature anchor for the **equal-`λ` / equal-work-terms / same-family** premise set

**source**: Migliore, A.; Polizzi, N. F.; Therien, M. J.; Beratan, D. N., "**Wires and Biologics**"… i.e.
"**Tuning the Optical and Electronic Properties of Molecules, Materials, and Devices by Quantum
Interference**" — correct title of the record: *Chem. Rev.* **114**(7), 3381–3465 (2014),
DOI `10.1021/cr4006654`. **status**: `first-hand` here (OA full text via Europe PMC
`https://www.ebi.ac.uk/europepmc/webservices/rest/PMC4317057/fullTextXML`; this is the same source already
recorded as **S23** in `theories/hammond/LITERATURE.md`, verified independently there).
**locus**: §"Implications of the Extended Marcus Theory: Brønsted Slope, Kinetic Isotope Effect, and
Cross-Relation" (§6.2 of the review), around its eqs. (6.23)–(6.25).

**VERBATIM:**

> "For a **homologous set of reactions with approximately equal reorganization energies and work terms**,
> the Brønsted (or the Leffler) slope … correlates the reaction rate with equilibrium properties …"
>
> "Equations 6.23 and 6.24 **hold if the reorganization energy is constant for a reaction series**, and `β`
> is a measure of the position of `Q_t` along the reaction path in this circumstance."
>
> "… where **`∂λ/∂ΔG_R°`** is used to describe the variation in the intrinsic barrier that results from
> changing a reactant that modifies `ΔG_R°`."

**Formalizable implication — this is the premise set of the whole theory, in one printed source:**
1. **family/homology** — the coefficient is defined for a *homologous set* (the same restriction the plan
   must declare; §R1.15.1 adds that the set may vary exactly **one** parameter);
2. **equal work terms** — the plan's zero-work-term model (`w_r = w_p = 0`) is the special case of
   "approximately equal work terms"; this is the printed warrant for that declared approximation, replacing
   the earlier weaker support (Agmon 1980's attribution of anomalies to work terms, which is
   `verified (delegated read)` only);
3. **`λ` constant across the series** — stated as a *condition of validity*, and the **failure branch is
   printed**: `∂λ/∂ΔG_R° ≠ 0` replaces the constant-`λ` equations. So "fixed `λ`" must be registered as an
   assumption with a named failure mode, exactly as §R1.16.1's bimodal JACS family exemplifies.

## R1.18.2 ⭐ The quantitative two-branch family: slope, intercept **and** `λ` all differ between branches

**source**: Salamone et al., *J. Am. Chem. Soc.* **143**(30), 11759–11776 (2021), `10.1021/jacs.1c05566`
(same CC-BY article as §R1.16.1; **first-hand** via `…/PMC8343544/fullTextXML`).
**locus**: **Figure 3 caption and the Results text**; numbers read verbatim here.

**VERBATIM (figure caption and surrounding text):**

> "The black circles are for the **saturated** substrates, and the best linear fit (black solid line) has a
> **Brønsted slope `α = 0.39`** with an intercept **`ΔG‡₀ = 13.9 ± 0.6 kcal mol⁻¹`** … The unsaturated data
> are shown in blue, and the fit line has **`α = 0.23`** with **`ΔG‡₀ = 14.3 ± 0.7 kcal mol⁻¹`**."
>
> "The best fit to the Marcus equation for the saturated (black dashed curve) and unsaturated (blue dashed
> curve) substrates is obtained with **`λ = 58 ± 1` and `76 ± 1 kcal mol⁻¹`**, respectively."
>
> "In contrast, the best fit for the **unsaturated** substrates **does not match the slope of the data**
> (`λ = 76 ± 1 kcal mol⁻¹`)."

**Formalizable implication**: within one experimental family (56 substrates, one reagent, one laboratory),
**the slope, the intercept and the reorganization energy all take different values on the two branches** —
`α = 0.39` vs `0.23` (both inside `(0,1)`, so this is **not** an out-of-range case), `ΔG‡₀ = 13.9` vs
`14.3 kcal mol⁻¹` (≈58 vs 60 kJ/mol), `λ = 58` vs `76 kcal mol⁻¹` (≈243 vs 318 kJ/mol). Consequently:
a **single affine law with a single constant `λ`** can only be a *premise* of the model, never a fact about
the chemistry — and the branch separation is forced by **the kind of bond broken** (benzylic/allylic vs
saturated C–H), which is precisely what the plan's "same family / same bond type" premise must say.

## R1.18.3 The `α → 0` / `α → 1` limits, and what they are **not**

- **Literature limit, first-hand** (García-Padilla & Qiu 2025, §R1.6b, §R1.17): "For highly exergonic
  reactions, `α` approaches 0; conversely, for very endergonic reactions, `α` approaches 1", and "the
  linearity breaks down" outside a limited driving-force range.
- **The model's corresponding values**: `transfer lam x = 0` at `x = λ` and `= 1` at `x = -λ` — the same
  limits, derived rather than fitted.
- ⚠️ **What they are not**: the model has **no diffusion floor**. Its `α = 0` at `x = λ` is the *model
  analogue* of the empirical `α → 0` limit, and its `α < 0` branch for `x > λ` is the **inverted-region
  analogue** (real for electron transfer, §R1.13.3 and the sibling record). Neither is a **diffusion-controlled**
  plateau, so a model instance with `α = 0` **must not** be presented as a stand-in for a
  diffusion-controlled step.
- **The literature's diffusion-control criterion is about the *reverse* step**, not about `λ`: Mayr & Ofial
  2023 (same LMU OA copy as §R1.15.2), **first-hand**, p. 1: "… Hammond referred to S_N1 [reactions] **if the
  reverse reaction is diffusion-controlled** (Figure 2a)", and p. 3–4: "… because only in the first case the
  rates of ion recombination are diffusion-controlled or close to diffusion control." If the plan ever maps
  this criterion onto the model's `|x| = λ` boundary, it must be declared an **explicit modelling premise**
  (the mapping assumption the sibling record already flags), never a theorem.

## R1.18.4 Two negatives and two don't-cite items from this round

| item | status |
|---|---|
| the textbook sentence "diffusion control ⇒ `Ea` = activation energy of solvent viscous flow" | **not found** in any open-access primary source (exact-phrase search: 0 hits) ⇒ **do not cite** |
| DOI `10.1021/cr300511u` | is **Carpenter, "Energy Disposition in Reactive Intermediates"**, *not* a recrossing review — the earlier dispatch's description was wrong; not used here |
| KIE/entropy-prefactor loci (isotope effect on `Ea` from the slope and on `A` from the intercept; an apparent `Ea(H₂) = −0.023 ± 0.005 eV` vs a DFT barrier of 0.37 eV; IUPAC entries "entropy of activation", "compensation effect", "isokinetic relationship") | `verified (delegated read)` only — **not re-read here**; usable as pointers, not as quoted numbers |
| §R1.12's "tunnelling / KIE / entropy-prefactor" gap | **partially closed**: the delegated items above are the pointers; the *named premise* remains unfilled first-hand, so the record still says "do not cite a source for the constant-prefactor premise" |

## R1.18.5 Final plan delta (all eight rounds) — no theorem changes

1. **§13, "model assumption" row**: cite **Migliore §6.2** for the three-part premise set (homologous set;
   approximately equal work terms; `λ` constant across the series) and record its printed failure branch
   `∂λ/∂ΔG_R° ≠ 0`.
2. **§13, "`ΔH ≈ ΔG°`" row**: keep as a declared premise but attach the loci — the IUPAC BEP entry is an
   **enthalpy** statement (p. 369) while the model (and Cohen & Marcus eq. (5a), p. 4250) is a
   **Gibbs-energy** statement.
3. **§13, split the current combined caveat row** into three: (a) tunnelling/recrossing/entropy-prefactor;
   (b) `α` out of range (with §R1.11, §R1.15 loci); (c) diffusion control — stating explicitly that the model
   has **no diffusion floor**, so `α = 0` at `x = λ` is the model analogue of the empirical limit and the
   `x > λ` branch is the inverted-region analogue, **not** a diffusion plateau.
4. **§8.2 / I11**: the violation instance may now be a **real** family — JACS 2021 with both branches'
   fitted constants (`α = 0.39` / `0.23`, `ΔG‡₀ = 13.9` / `14.3 kcal mol⁻¹`, `λ = 58` / `76 kcal mol⁻¹`),
   labelled as *fitted family constants*, not point data.
5. **Optional**: register "piecewise/branching BEP relations" as a §14 next station rather than reopening the
   delivered milestones — the branching is now documented in two independent fields (molecular HAT, JACS 2021;
   surface catalysis, Vojvodic 2011's per-site lines and their "piecewise linear" averaged relation).

---

# §R1.19 Round-1i (closing) — one normative locus re-confirmed, one branching family verified, one site-decoupling case verified

## R1.19.1 The normative `Marcus equation` locus, re-confirmed against the extracted text (already §R1.2/§R1.6b)

The IUPAC entry **"Marcus equation"** (B5, DOI `10.1515/pac-2018-1010`) was already read first-hand in the §R1
pass of this file; it prints, on its own page of the version of record,
`Δ‡G = (l/4)(1 + ΔrGº/l)² = Δ‡Gº + ½ΔrGº + (ΔrGº)²/(16Δ‡Gº)` with `l = 4Δ‡Gº`, and its Note contains the
sentence "It also implies that **changes in intrinsic barriers may dominate over changes of reaction Gibbs
energies** and thus account for the fact that reaction rates may not be controlled by the relative
thermodynamic stabilities of the products." **Status unchanged: `first-hand`** (the extracted text carries the
equations with the flattened glyphs `l`/`D`, which is why §R1.2 reproduces them in that form). No new
verification claim is made here — this item is recorded only to close the delegated loop.

## R1.19.2 ⭐ A **branching** Brønsted correlation in RNA transesterification (verified here via NCBI EUtils)

**source**: Huang, W.-J.; York, D. M., "Linear free energy relationships in RNA transesterification:
theoretical models to aid experimental interpretations", *Phys. Chem. Chem. Phys.* **16**, 15846–15855
(2014), DOI `10.1039/c4cp01050g` (PMC `PMC4366550`).
**status**: `first-hand` — **retrieval note that matters for reproducibility**: Europe PMC's
`…/PMC4366550/fullTextXML` returned **HTTP 500** and its `oa.fcgi` route **404** (service migration), but the
**NCBI EUtils** route worked: `https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=pmc&id=PMC4366550&rettype=xml`
(HTTP 200, 166 668 B).

**VERBATIM** (Introduction, reporting the analysed kinetic data and the paper's own model results):

> "… analyzed original measured kinetic data of **uridine 3′-phosphate diester cleavage** and derived a
> **non-linear Brønsted correlation with a convex break at `pKa` of 12.58**; two significantly different
> Brønsted values (`β_lg1` and `β_lg2`) of **−0.52 and −1.34** were obtained for model reactions with aryl and
> alkyl leaving groups, respectively."
>
> "At this point a **convex break point in the LFERs occurs**, and for reactions involving leaving groups with
> `pKa` values lower than the break point, the value of `β_lg1` is **smaller in magnitude** than `β_lg2`,
> reflecting a **diminished sensitivity** to variation of the leaving group."

**Formalizable implication**: a second, chemically unrelated field (phosphodiester transesterification)
documents the same qualitative phenomenon the record already has from HAT (JACS 2021) and from surface
catalysis (Vojvodic 2011): **the LFER is piecewise, with two slopes separated by a break point**, and the
slopes here are **negative and of different magnitude** (`−0.52` vs `−1.34`) — so this family also falls
**outside** the `(0,1)` interval that §R1.11 refuses to treat as a law. **Attribution caveat**: the quoted
sentences report (a) an *analysis of literature kinetic data* and (b) the paper's own computed values; the
present record therefore cites it as a **branching-correlation locus**, not as an experimental point table
(no `(x, Ea)` pairs are taken from it).

## R1.19.3 ⭐ "Same site / same adsorption mode" has a measured counterexample (verified here)

**source**: "**Breaking the Brønsted–Evans–Polanyi Relation with Dual-Metal Sites**", *J. Phys. Chem. Lett.*
**16**, 11302–11307 (2025), DOI `10.1021/acs.jpclett.5c02446` (PMC `PMC12581165`).
**status**: `first-hand` (same EUtils route, HTTP 200, 79 638 B).

**VERBATIM** (abstract):

> "We found that many heteronuclear DMSCs **break the BEP linear scaling** due to a **mixed
> low-affinity/high-affinity coadsorption** of the two methyl groups, **decoupling the step responsible for
> the activation energy (`Ea`) at the low-affinity site from the overall reaction energy (`ΔE`) determined by
> both sites**."

**Formalizable implication**: this is the sharpest available statement of *why* the plan's "same site" premise
is load-bearing — the barrier is set by one site while the reaction energy is set by two, so the two axes of a
BEP plot cease to refer to the same local process. In the model this can only be a **declared** scope
restriction (one scalar coordinate, one family, one site); the paper is the citation for the restriction, not
for any number in the instance layer.

## R1.19.4 Closing statement of this record (round status)

**Rounding rule honoured throughout**: every entry carries `source` with a checkable locus, `status`,
`conclusion`, and a `formalizable implication`; every unread body is `not-accessed` and carries **no** content
claim; every number is either read at a named locus or computed here and marked as such.

**What remains unfilled, deliberately (and why):**

| unfilled item | reason |
|---|---|
| Evans & Polanyi 1938 and 1936, Bell 1936, Semenov 1935/1958, Polanyi 1963 | bodies unreachable from this machine (RSC/RS/Science 403; archive.org family times out). Naming/attribution only; the formula layer is carried by Marcus 1968 eq. (2) p. 891, Cohen & Marcus eqs. (5a)–(5c) p. 4250, IUPAC p. 419 and Ooka/Exner 2021 p. 7 |
| Bligaard et al. 2004 body | Elsevier paywall, Unpaywall closed; **no slope value attributed anywhere in this file** |
| Pu/Gao/Truhlar *Chem. Rev.* 106, 3140 (2006) body | PMC serves a JS placeholder and the EUtils/EPMC XML routes fail for it; recrossing is instead covered by the sibling record's OA sources |
| experimental `(ΔH, Ea)` tables with printed loci | none retrieved; all families in §R1.10/§R1.16 are **computed** energies (stated per family) |
| a first-hand source for the "constant prefactor / constant activation entropy" premise | **not found** as a direct statement; only the IUPAC glossary entries ("entropy of activation", "compensation effect", "isokinetic relationship") synthesise it ⇒ the record says **do not cite a source for this premise** |
| the textbook sentence "diffusion control ⇒ `Ea` = viscous-flow activation energy" | 0 hits in open primary sources ⇒ **do not cite** |
| Denisov 2012 `(ΔH, Ee)` as instance data | Ee is computed by that review's own parabola equations ⇒ self-consistency check only (§R1.14.2) |
| DOI `10.1021/cr300511u` | is Carpenter, "Energy Disposition in Reactive Intermediates" — **not** a recrossing review; not used |

**Plan-level conclusion of this record (unchanged across all rounds): no proved or planned theorem needs to
change.** Every correction concerns (i) **attribution** (the quadratic law is Marcus 1968 eq. (2) p. 891, not
Marcus 1956), (ii) the **premise register** (homologous one-parameter family, constant `λ` and equal work terms,
non-degeneracy of the compared pair, same site/coverage/mechanism, `ΔH` vs `ΔG°`, computed vs measured `Ea`),
and (iii) **wording** (three distinct `α` objects; `0 ≤ α ≤ 1` and `α_f + α_r = 1` are model-side statements;
`α(0) = 1/2` is a thermoneutrality statement only; `α = 0` at `x = λ` is not a diffusion plateau).
