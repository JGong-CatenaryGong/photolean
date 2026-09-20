# theories/Sabatier/LITERATURE.md — literature record: the Sabatier principle and the volcano plot

> Owner: `literature_researcher` (engine role). Authority for (i) the loci and wording of the Sabatier
> principle and of the volcano model, (ii) the provenance of every number that may enter the instance
> layer `PhotoLean/Sabatier/RatModel.lean` / `Instances.lean`.
> Language: English (contract `proofs/ENGINE.yml`; the only bilingual file is `RESULTS.md`).
> Status: **round 1 — retrieval record delivered** (§R0–§R6). Date: **2026-09-21**.
> Evidence vocabulary — `first-hand` (text retrieved here and read) · `second-reader` (retrieved by a
> delegate of this round, not re-read here) · `abstract-only` · `secondary` (read only as quoted by a
> named retrieved source) · `bibliographic-only` · `not-accessed` · `UNSUPPORTED`.
> **No PDF of any paper is stored in this repository**; scratch is `/tmp/sabatier/`; every
> `URLS FETCHED` line is re-runnable. Sibling records cross-referenced and **not** duplicated:
> `theories/BEP/LITERATURE.md` (the Brønsted/BEP coefficient `α` and its counterexamples) and
> `theories/Marcus/LITERATURE.md` (the two-parabola barrier). Long secondary tables live in the
> companion note `theories/Sabatier/literature/INSTANCE-DATA.md`.
> **Shape of this record** (for a reader in a hurry): §R0 = the model + source index (S1–S30) ·
> §R1 = statements and loci, each entry carrying a *formalizable implication* · §R2 = instance
> parameters for the `ℚ` layer · **§R3 = what the literature does NOT support (the round's sharpest
> output)** · §R4 = delegated parcels · §R5 = net effect on `plan.md` · §R6 = outstanding.
> Size note: ~900 lines for 30 sources. If a shorter leaf is wanted, §R2's data tables and §R1's long
> quote blocks are what can move into `literature/INSTANCE-DATA.md` without losing a locus.

---

## §R0 Scope, and the model these sources are read against

`theories/Sabatier/plan.md` as landed carries only §1–§2 (goal + milestone table); **the model sketch
below is the one dispatched by the lead**, and all impact statements are keyed to it.

```
branch A (weak-binding-penalized):   Ea_A(dE) = alphaA * dE + betaA
branch B (strong-binding-penalized): Ea_B(dE) = betaB - alphaB * dE
effective barrier:                   Ea(dE) = max(Ea_A(dE), Ea_B(dE))    <- DECLARED approximation
apex (derived):                      dE* = (betaB - betaA) / (alphaA + alphaB)
activity ∝ exp(-Ea(dE) / (kB * T))   (Arrhenius / transition-state form)
sharp target:  Ea has a unique global minimum at dE*  iff  0 < alphaA * alphaB
physically oriented case: 0 < alphaA ∧ 0 < alphaB   |   variant: two Marcus parabolas, BEP lines = tangents
dE is the binding energy of the key intermediate; more negative dE = stronger binding
```

The round must settle: **(1)** what the sources state and where (volcano as max/intersection of two
BEP branches? legs of slope ±α? optimum as "the two steps equally difficult" or "ΔG ≈ 0"?);
**(2)** the condition/validity side (is the effective barrier a max of step barriers? is a sign/range
condition on the slope asserted as *necessary*? where does the single-descriptor volcano fail?);
**(3)** instance parameters with per-number provenance.

**Math check of the sharp target** (this record's algebra, *not* a literature claim): with
`f = alphaA·dE + betaA`, `g = betaB − alphaB·dE`, the convex function `max(f,g)` tends to `+∞` at
**both** ends iff the two slopes `alphaA`, `−alphaB` have opposite signs, i.e. iff
`alphaA·alphaB > 0`; the kink `dE*` is then the unique global minimum. If `alphaA·alphaB < 0` the
envelope is monotone; if `alphaA = 0` or `alphaB = 0` the minimum is attained on a ray, not uniquely.
The mathematics is fine; **what the literature can supply is only the premises** (§R3).

### §R0.1 Source index (checkable)

| id | source | locus / DOI | status | used for |
|---|---|---|---|---|
| S1 | Sabatier, Nobel Lecture, 11 Dec 1912 | `nobelprize.org/prizes/chemistry/1912/sabatier/lecture/` | first-hand | original wording: **negative** (§R1.1.1) |
| S2 | Sabatier, *La catalyse en chimie organique*, 1913 / 1920² | Gallica ark `bpt6k9615479v` / `bpt6k90295w` | first-hand (1913 OCR index); 1920 not-accessed | original wording (§R1.1.2) |
| S3 | Batis & Chastrette, *L'actualité chimique* **276**, 52–58 (2004) | `new.societechimiquedefrance.fr/wp-content/uploads/2019/12/2004-276-juin-juil-Batis-p.52.pdf` | first-hand (as a secondary quoter) | the disputed "combinaison temporaire instable" sentence (§R1.1.2) |
| S4 | Ooka, Huang & Exner, *Front. Energy Res.* **9**, 654460 (2021) | `10.3389/fenrg.2021.654460` | first-hand (OA) | modern statement + limitations (§R1.1.3, §R1.3.5) |
| S5 | Balandin, *Adv. Catal.*, 1–210 (1969) | `10.1016/S0360-0564(08)60029-2` | bibliographic-only | earliest "volcano" (§R1.2.0) |
| S6 | Trasatti, *J. Electroanal. Chem.* **39**, 163–184 (1972) | `10.1016/S0022-0728(72)80485-6` | bibliographic-only | historical HER volcano (§R1.2.1) |
| S7 | Bligaard et al., *J. Catal.* **224**, 206–217 (2004) | `10.1016/j.jcat.2004.02.034` | bibliographic-only | canonical BEP+volcano citation (§R1.2.2) |
| S8 | Nørskov et al., *J. Electrochem. Soc.* **152**, J23–J26 (2005) | `10.1149/1.1856988`; PDF via `backend.orbit.dtu.dk` | **first-hand (publisher PDF)** | the kinetic volcano; Table I (§R1.2.3, §R2.1) |
| S9 | Nørskov, Bligaard, Rossmeisl & Christensen, *Nat. Chem.* **1**, 37–46 (2009) | `10.1038/nchem.121` | abstract-only | review framing only (§R1.2.4) |
| S10 | Cheng & Hu (& Ellis), *J. Phys. Chem. C* **112**, 1308–1311 (2008) | `10.1021/jp711191j` | abstract-only | two-step reduction to BEP branches (§R1.2.5) |
| S11 | Cheng & Hu, *J. Am. Chem. Soc.* **130**, 10868–10869 (2008) | `10.1021/ja803555g` | bibliographic-only | 3D (multi-descriptor) volcano (§R1.2.5, §R3.4) |
| S12 | Yang, Patil, McKone & Saidi, *Catal. Sci. Technol.* **11**, 6832 (2021) | `10.1039/d1cy01170g`; arXiv:`2109.04219P` | **first-hand (arXiv + SI)** | ⭐ opposite-slope branches; Table S2 (§R1.2.6, §R2.1) |
| S13 | Zheng, Sheng, Zhuang, Xu & Yan, *Sci. Adv.* **2**, e1501602 (2016) | `10.1126/sciadv.1501602` (`PMC4803484`) | **first-hand (OA)** | ⭐ `0 < β < 1` printed; β table (§R2.4) |
| S14 | Man, DTU PhD thesis (2011); Man et al., *ChemCatChem* **3**, 1159–1165 (2011) | `10.1002/cctc.201000397`; thesis via `backend.orbit.dtu.dk/.../Isabela%20Man.pdf` | **first-hand (thesis)** | ⭐ OER `max` of two branches (§R1.2.7, §R2.2) |
| S15 | Kozuch & Shaik, *Acc. Chem. Res.* **44**, 101–110 (2011) | `10.1021/ar1000956` | abstract-only | energetic span ≠ max of step barriers (§R1.3.1) |
| S16 | Exner, *Angew. Chem. Int. Ed.* **59**, 10236–10240 (2020) | `10.1002/anie.202003688` | abstract-only | apex vs thermoneutral (§R1.3.2) |
| S17 | Schmickler & Trasatti's comment and Nørskov et al.'s reply, *J. Electrochem. Soc.* **153**, L31 / L33 (2006) | `10.1149/1.2358294` / `10.1149/1.2358292` | bibliographic-only | the printed dispute over S8's dataset (§R4) |
| S18 | sibling records | `theories/BEP/LITERATURE.md`, `theories/Marcus/LITERATURE.md` | first-hand (in repo) | `α` bounds and counterexamples (§R2.4, §R3.1) |
| S19 | Martínez-Alonso, Guevara-Vela & LLorca, *Phys. Chem. Chem. Phys.* **24**, 4832–4842 (2022) | `10.1039/D1CP05436H`; arXiv:`2202.01647` | **second-reader (arXiv)** | printed `G_adsH` **including Fe and Ru** (§R2.1c) |
| S20 | Greeley, Jaramillo, Bonde, Chorkendorff & Nørskov, *Nat. Mater.* **5**, 909–913 (2006) | `10.1038/nmat1752`; reprint in Bonde's DTU thesis | **second-reader (thesis reprint)** | the +0.24 eV rule; figure-only values (§R2.1d) |
| S21 | Yan, Maark, Khorshidi, Sethuraman, Peterson & Guduru, *Angew. Chem. Int. Ed.* **55**, 6175–6181 (2016) | `10.1002/anie.201508613`; arXiv:`2003.04085` | second-reader (arXiv) | "the peak of the volcano … occurs at ΔG_H of 0 eV" (§R2.1) |
| S22 | Calle-Vallejo, *Acc. Chem. Res.* **58**(17), 2749–2759 (2025) | `10.1021/acs.accounts.5c00439` (`PMC12409882`, CC-BY) | **second-reader (OA)** | ⭐ printed `Eq. (12)`: apex `= 3.20/2 = 1.60 eV`; two-line intersection (§R2.2) |
| S23 | Azcona-Aliende, Rodriguez & Calle-Vallejo, *ChemSusChem* **18**(19) (2025) | `10.1002/cssc.202501198` (`PMC12487758`) | **second-reader (OA)** | printed per-material OER descriptors (§R2.2) |
| S24 | Noh, Back, Kim & Jung, *Chem. Sci.* **9**, 5152–5159 (2018) | `10.1039/c7sc03422a` (`PMC5998799`, CC-BY) | **second-reader (OA)** | printed CO₂RR optimum `*CO ≈ −0.5 eV`, attributed to Peterson & Nørskov 2012 (§R2.2) |
| S25 | Liu, Xiao, Peng, Hong, Chan & Nørskov, *Nat. Commun.* **8**, 15438 (2017) | `10.1038/ncomms15438` (`PMC5458145`) | second-reader (OA) | CO₂RR optimum given as a **figure only** (§R2.2) |
| S26 | Azcona-Aliende, Rodriguez & Calle-Vallejo, *ACS Catal.* **16**(6), 5805–5815 (2026) | `10.1021/acscatal.5c08978` (`PMC13010250`) | **second-reader (OA)** | ⭐ "two lines, one with a negative slope and another with a positive slope, **the hinge point being the ideal catalyst**" (§R1.3.4) |
| S27 | Steiner & Reiher, *Top. Catal.* **65**(1–4), 6–39 (2022) | `10.1007/s11244-021-01543-9` (`PMC8816766`) | second-reader (OA) | "TDTS and TDI **maximize** the energetic span"; the one-pair approximation can fail (§R1.3.1) |
| S28 | Wang, Jiang, Wang & Hu, *ACS Catal.* **6**(2), 733–741 (2016) | `10.1021/acscatal.5b01714` (Just-Accepted copy only) | second-reader | a volcano built on **BEP slopes −2.32 / 1.16** (§R3.1) |
| S29 | Polynski & Kozlov, *Adv. Sci.* (2026), e75932 | `10.1002/advs.75932` (`PMC13336856`) | second-reader (OA) | a **printed `max`-form** activity law in two descriptors (§R1.3.4) |
| S30 | Abild-Pedersen et al., *Phys. Rev. Lett.* **99**, 016105 (2007) | `10.1103/PhysRevLett.99.016105` (PDF via `backend.orbit.dtu.dk`) | second-reader | "no general rigorous proof of the scaling" (§R3.4) |

## §R1.0 Method, hosts reached, blocks

**Method.** Bibliographic facts verified against Crossref (`api.crossref.org/works/<doi>`) and OpenAlex;
**guessed DOIs were checked, never trusted** — three DOIs supplied in the dispatch were *disproved*
(§R1.2.0, §R1.2.3, and the `jp0621110` of §R1.3.1). Full texts were retrieved into `/tmp/sabatier/`
and searched with `pdftotext -layout` + `grep` / narrow Python windows; **no paper was read into
context whole**. **Reached (HTTP 200)**: the Crossref/OpenAlex/SemanticScholar/Unpaywall APIs ·
`backend.orbit.dtu.dk` (the **publisher PDF** of S8, S14's thesis, S30's PRL copy) · `arxiv.org` ·
`eutils.ncbi.nlm.nih.gov` (`efetch`) · `europepmc.org/webservices/rest/*` · `www.nobelprize.org` ·
`www.frontiersin.org` (S4) · `gallica.bnf.fr/services/ContentSearch` (S2; intermittent 429s).
**Blocked (negatives, with the obstacle)**: `pubs.acs.org` 403 · `onlinelibrary.wiley.com` 403 (pdf
**and** full-xml) · `sciencedirect.com` 403 / 302-to-paywall · `iopscience.iop.org` 200 but a *"Radware
Bot Manager Captcha"* page (S8's IOP copy; S17) · `orbit.dtu.dk/en/publications/*` 200 but `/files/...`
403 *"Just a moment…"* · `gallica.bnf.fr/ark:/12148/*.texteBrut` = **Altcha proof-of-work gate** + 429 ·
`goldbook.iupac.org` 403 and `old.goldbook.iupac.org` TLS failure · `archive.org`, `par.nsf.gov`,
`www.osti.gov`, `scholar.archive.org`, `api.fatcat.wiki`, `ddd.uab.cat` connection failures ·
`core.ac.uk` 400/404/500 · `colab.ws` 403 · `www.scilit.com` 403 · `ouci.dntb.gov.ua` 502 ·
`mdpi.com` 403 (its articles were reached through PMC instead) · Wiley/De Gruyter book platforms 403/202.

# §R1 — Sources: statements and primary loci

## §R1.1 The Sabatier principle itself

### R1.1.1 Sabatier's Nobel lecture (1912) — ⚠️ NEGATIVE RESULT

**source/locus/status**: S1; the English text printed in *Nobel Lectures, Chemistry 1901–1921*,
Elsevier (1966), hosted by the Nobel Foundation; **first-hand** — the whole lecture body (≈26 300
characters) was retrieved and searched exhaustively here.
`URLS FETCHED`: `https://www.nobelprize.org/prizes/chemistry/1912/sabatier/lecture/` (188 992 bytes).

**Result.** Over the whole lecture: `unstable` → **0 hits**; `moderate`, `average`, `optimum/optimal` →
**0 each**; `stabil*` → **0**; `too` → 5–6 hits, none in the sense "not too stable" (the two hits a
delegate found are about *preparation temperature*: "nickel prepared at too high a temperature" / "at a
not too high temperature"). **The lecture does not contain the sentence usually quoted as the Sabatier
principle** ("…neither too strong nor too weak"), nor any two-sided optimum. ⚠️ **Correction to an
earlier draft of this record**: an earlier version reported "`stable/stability` → 1 hit (the stability
of the acetones)" — that hit belongs to the **1913 book** (§R1.1.2), not to the lecture; the lecture
body contains no `stabil*` token at all (re-verified by a delegate against the same URL).
**Independent corroboration** (`second-reader`): a delegate searched the same page and reached the
same conclusion; its nearest argument is *one-sided* — "well-prepared and pure nickel might produce the perhydride NiH₂
which is capable of hydrogenating benzene. On the other hand, nickel prepared at too high a
temperature or containing some impurities, would give only a poorer hydride … which would be
**incapable of reacting with benzene**" — i.e. "too weak ⇒ no reaction". The delegate also reports
that only the English translation is hosted (`/lecture/fr/` is a soft 404), so **the French original
was not obtained**.

What the lecture *does* state, verbatim (`first-hand`):
> "I assume that hydrogen acts upon the metal by very rapidly producing a compound on its surface.
> The hydride thus produced is **readily and rapidly dissociated**, and if it is placed in the presence
> of substances capable of using hydrogen it gives it up to them, at the same time regenerating the
> metal, which again produces the same effect, and so on."
> "…the decisive cause of the catalytic activity of porous platinum is … that it is a **real chemical
> combination of the surface of the metal with the surrounding gas**."

**Formalizable implication.** ⚠️ **Impact on the plan: no docstring may cite the 1912 lecture for the
quantitative principle or for the two-sided wording.** What it licenses is the *mechanistic* premise —
a surface intermediate that can decompose and regenerate the catalyst — i.e. the existence of the
two-step cycle. "Chemical combination of the surface with the gas" is **not expressible** in a model
whose entire state is a scalar `dE`; the identification `dE := binding energy of the key intermediate`
is a **declared bridge**.

### R1.1.2 *La catalyse en chimie organique* (1913; 2nd ed. 1920)

**source/locus/status**: S2/S3. 1913 first edition = **first-hand via Gallica's OCR phrase-search
index** (`gallica.bnf.fr/services/ContentSearch?ark=ark:/12148/bpt6k9615479v&query=<phrase>`, quoted
phrases supported); 1920² edition = `not-accessed` (every probe returns `countResults = 0`).
**Page mapping = image number − 28**, verified here on two running heads and independently by a
delegate on **five** (folio 35 → p. 7, 148 → 120, 267 → 239, 280 → 252, 283 → 255). ⚠️ **Caveat**: the
endpoint is an *OCR search index*, and Gallica's full-page `.texteBrut` sits behind an **Altcha
proof-of-work gate** plus HTTP 429 — so a 0-hit result is strong evidence but not a full scan.

**⚠️ The commonly circulated general sentence is NOT in the 1913 edition as quoted.** The wording
« … qui donne avec l'un des éléments du système primitif une combinaison temporaire instable dont la
destruction … » appears only **inside a secondary source** (S3, Batis & Chastrette 2004, `first-hand`
for S3, `secondary` for the attribution to Sabatier) whose page numbers are **self-contradictory**
("p. 46" in its reference list vs "(p. 65)" in its text; its "p. 55" is the *journal* footer; its
"p. 66" quote "phare directeur", and its "staircase" quote, resolve to **printed pp. 255 and 242**),
and whose wording differs from the edition's (« de composés intermédiaires fournis par les
catalyseurs » vs « des composés intermédiaires ainsi engendrés ») — so it probably cites the
**1920² edition or a translation**. A phrase search of the 1913 edition returns **0 hits for
« donne avec l'un des éléments »**.

**⭐ The two page anchors to use instead** (found here by quoted-phrase search, re-verified by a
delegate), and **what the edition states**: the unstable intermediate, always **one-sidedly**, never as
a two-sided optimum —

| printed p. | verbatim (French, as OCR'd) |
|---|---|
| **242** | « … cette dégradation par échelons est fréquemment bien plus facile que la dégradation directe immédiate, de la même manière que l'usage d'un **escalier** facilite la descente » — preceded by « La création **des composés intermédiaires ainsi engendrés**, puis leur destruction ultérieure, correspondent le plus souvent l'une et l'autre à une diminution d'énergie » (`escalier`: 1 hit in the book) |
| **255** | « … cette explication par des combinaisons **temporaires instables** a été le **phare directeur** de tous mes travaux sur la catalyse : sa lueur s'éteindra peut-être dans l'avenir… » |
| **148** | « Nous avons expliqué les hydrogénations directes sur les métaux divisés par la formation d'un **hydrure instable** fourni rapidement par le métal, et capable de céder facilement son hydrogène » |
| **254** | « … tendance qu'il possède à fournir avec l'oxyde de carbone un **composé temporaire instable** à la température de réaction, le conduit à provoquer la scission des aldéhydes et des acétones » |
| **203** | « … la facilité avec laquelle l'alcool contracte avec l'oxyde catalyseur la **combinaison temporaire instable** » (the phrase's only occurrence, in a page-specific discussion of etherification) |

**Clean negatives inside the 1913 edition**: « peu stables » · « assez stable » · « donne avec l'un des
éléments » (0 hits each) · « trop stable » (25 hits, none an optimum statement) · « stabilité moyenne » ·
« trop forte » (41, all about reagent amounts/temperatures) · « trop faible » (43) · « ni trop » (20) ·
« modéré » (4) — **no two-sided optimum formulation anywhere**.

**Formalizable implication.** Citable: "the catalyst forms an **unstable** intermediate which
decomposes and regenerates it" (pp. 148, 203, 242, 254, 255) — the two-step-cycle premise. **Not
citable: the two-sided optimum as Sabatier's own formulation** (neither the lecture nor the 1913 book).
**Impact on the plan: attribute the two-sided *qualitative* form to the modern literature (§R1.1.3,
§R1.2.6) and the unstable-intermediate mechanism to Sabatier (pp. 148/254/255); the bridge "unstable
intermediate ⇔ branch B (strong-binding penalty)" is a modelling choice, since the model has no
decomposition step.**

### R1.1.3 The modern formulation (dictionary/authoritative use)

**source/locus/status**: S4, H. Ooka, J. Huang, K. S. Exner, "The Sabatier Principle in
Electrocatalysis: Basics, Limitations, and Extensions", *Front. Energy Res.* **9**, 654460 (2021),
DOI `10.3389/fenrg.2021.654460` — **first-hand** (OA full text retrieved here;
`URLS FETCHED`: `https://www.frontiersin.org/journals/energy-research/articles/10.3389/fenrg.2021.654460/full`).
Verbatim from the abstract:
> "The Sabatier principle, which states that **the binding energy between the catalyst and the reactant
> should be neither too strong nor too weak**, has been widely used as the key criterion in designing
> and screening electrocatalytic materials … The widespread success of density functional theory (DFT)
> has made binding energy calculations a routine practice, **turning the Sabatier principle from an
> empirical principle into a quantitative predictive tool**."

and, for its own scope: "…we have attempted to introduce the reader to the fundamental concepts of the
Sabatier principle with **a highlight on the limitations and challenges in its current thermodynamic
context**." A delegate read the **same paper's PDF and locates the dictum on its printed p. 2**:
> "This principle states that **'an ideal catalyst must bind to the reactant at an intermediate
> strength which is neither too weak nor too strong.'**"

⭐⭐ **⚠️ There is NO IUPAC entry for the Sabatier principle — this round closes the question with a
negative** (`second-reader`; raw data `/tmp/sabatier/goldbook/goldbook_terms.tsv`): a full cursor sweep
of the Gold Book through Crossref (`filter=prefix:10.1351,type=book-section`) yielded **22 045 unique
DOIs / 21 882 unique titles**; a case-insensitive title grep for `sabatier` → **0**; a targeted
`query.bibliographic` → **0** results; and the ID space has **no gap** where such an entry could hide
(`s05440 = "S"`, `s05441 = "saccharides"`, and neighbouring unregistered IDs probe 404). **Therefore
the plan, any docstring and any honesty table must contain no "normative IUPAC wording" for the
Sabatier principle.** For contrast, the Gold Book *does* hold entries for the neighbouring concepts —
`Bell–Evans–Polanyi principle` (**B00628**), `Hammond principle` (**H02734**), `Marcus equation` /
inverted region (**M03702**/**M03704**), `Kasha rule` (**K03370**), `Brønsted relation` (**B00746**)
— but their **texts** are unreachable here (Cloudflare), so only "the entry exists, with this DOI" may
be cited for them. (Same class of result as `theories/BEP/LITERATURE.md` §R1.2.3, where the searched
physical-organic glossary had no "transfer coefficient" entry.)

**Textbook substitutes actually reachable** (`second-reader`; Chorkendorff & Niemantsverdriet 2003 and
Niemantsverdriet's *Spectroscopy in Catalysis* both `not-accessed`, Wiley 403, **no page invented**):
MIT OCW 10.426/10.626 course reader, **printed p. 200** — "Plotting ln I₀ vs. ln K_ads yields … a
'volcano plot'. This plot represents the Sabatier principle, which states that **the binding energy of
adsorbate and surface is optimally neither too strong nor too weak**"; a Chalmers licentiate thesis,
**pp. 6–7** (rate-versus-descriptor, **two linear branches, extremum at their intersection**);
LibreTexts Chem1 §17.6 derivation, **p. 12**.

**Formalizable implication.** The modern, citable formulation is **two-sided and qualitative**; the
source itself calls the principle **empirical**, and calls its quantitative use a *tool*, not a
theorem. **Impact: the plan's §1 may quote this sentence with the DOI; the phrase "empirical
principle" belongs in the honesty table, and no normative (IUPAC) status may be claimed unless §R4.1
produces an entry.**

## §R1.2 The quantitative volcano — the canonical chain

### R1.2.0 Balandin 1969 (earliest "volcano") — DOI correction
**source**: A. A. Balandin, "Modern State of the Multiplet Theory of Heterogeneous Catalysis",
*Advances in Catalysis*, pp. **1–210** (1969). DOI **`10.1016/S0360-0564(08)60029-2`**,
Crossref-verified here (`book-chapter`, ISBN 9780120078196, issued 1969). ⚠️ **The DOI supplied in the
dispatch, `10.1016/S0360-0564(08)60004-7`, is disproved (Crossref 404).** ⚠️ Crossref prints the
**volume field empty**, so the customary "*Adv. Catal.* **19**" is the printed series volume, not a
Crossref datum. **status**: `bibliographic-only` (no OA route; archive.org / Google Books /
HathiTrust unreachable). **Status: no sentence and no number may be used.** **Impact: the plan may
cite it as the origin of the volcano *shape*, and nothing more.**

### R1.2.1 Trasatti 1972 (H₂-evolution volcano on metals)
**source**: S. Trasatti, "Work function, electronegativity, and electrochemical behaviour of metals:
III. Electrolytic hydrogen evolution in acid solutions", *J. Electroanal. Chem.* **39**, 163–184
(1972), DOI `10.1016/S0022-0728(72)80485-6` — Crossref-verified (the dispatch's guessed DOI was not
the one Crossref returns; cite **volume and part number**). **status**: `bibliographic-only`
(Elsevier 403). **secondary evidence, named**: Yang et al. 2021 (S12, first-hand) says verbatim:
> "…Krishtalik and Trasatti used a compilation of experimental data to validate Parsons volcano
> relationship using the metal-hydrogen interaction strength based on Eley-Stevenson method. However,
> this approach had **limited success because the maximum exchange current was not associated with
> Δg_H = 0**, as proposed by Parsons."
**Formalizable implication.** The historical experimental volcano **did not** put its maximum at zero
adsorption free energy. **Impact: the instance layer must not present "apex at 0" as experimentally
established.**

### R1.2.2 ⭐ Nørskov et al. 2005 — the strongest first-hand kinetic locus
**source**: S8, *J. Electrochem. Soc.* **152**(3), **J23–J26** (2005), DOI `10.1149/1.1856988`
(Crossref-verified; the retrieved PDF's running head reads "152 (3) J23-J26 (2005)").
`URLS FETCHED`: `https://backend.orbit.dtu.dk/ws/files/4378376/Kehlet.pdf` (199 654 bytes, "Publisher's
PDF, also known as Version of record"). **status**: **`first-hand`** (read here; two-column layout
reassembled by hand).

**(a) The descriptor and its transformation** (printed p. J24): "ΔG_H* = ΔE_H + ΔE_ZPE − TΔS_H **[8]**"
… "This means that **ΔG_H* = ΔE_H + 0.24 eV**"; Fig. 1 caption: "…free energy for hydrogen adsorption,
**ΔG_H* = ΔE_H + 0.24 eV, Eq. 8**".

**(b) ⚠️ The two legs are different in kind** (printed p. J25):
> "…we can understand the **two branches of the volcano curve** in the following way: **To the left of
> the maximum, the rate decreases with decreasing ΔE_H due to a lack of available sites for H⁺ + H
> recombination at the surface.** Here hydrogen bonds too strongly. **To the right of the maximum, the
> rate decreases with increasing ΔE_H because proton transfer becomes more and more difficult** as
> hydrogen becomes more and more unstable on the surface. Here hydrogen bonds too weakly. **Pt is very
> close to optimum, because all reaction steps of the hydrogen evolution process on this metal are
> thermo-neutral.**"

**(c) The optimum** (p. J25): "**Clearly ΔG_H* = 0 separates the two legs of the volcano.**"

**(d) ⚠️ The strong-binding leg is a Langmuir saturation factor, not a BEP line** (p. J25, Eqs.
[10]–[14]): "θ = K/(1+K) [10] where K = exp(−ΔG_H*/kT) [11]" … "we would expect the rate constant
k₁ = k₀ to be large and independent of ΔG_H*" … "i₀ = −e k₀ · 1/(1 + exp(−ΔG_H*/kT)) **[12]**" … "For
the other case where the proton transfer is endothermic (ΔG_H* > 0, e.g., Au in Fig. 2), we would
expect the proton transfer to be **activated by at least ΔG_H***" … "k₁ = k₀ exp(−ΔG_H*/kT) **[13]**" …
"i₀ = −k₀ · 1/(1 + exp(−ΔG_H*/kT)) · exp(−ΔG_H*/kT) **[14]**", with "the single unknown parameter
k₀ = 200 s⁻¹ site⁻¹ fitted"; **(e) loose away from the peak** (p. J25): the model "**underestimate[s]
the current density for the metals furthest away from the maximum**"; **(f) coverage** (pp. J25–J26):
Fig. 3 compares θ = 0.25 and θ = 1 for Pt(111) with `ΔE_H^diff(1) = 2ΔE_H(1) − ΔE_H(0.25)` **[15]** —
"**the overall activation energy is smaller for the high coverage state**"; **(g) experimental spread**
(p. J24): "some variations from one measurement to the next on the same metal".
**Tables retrieved**: Table I (→ §R2.1), Table II (→ §R2.2, `literature/INSTANCE-DATA.md` §T2),
Table A-1 (ZPE/entropy corrections).

**Formalizable implication.**
- ⭐ **`Ea = max(two BEP branches)` is NOT the structure of the canonical HER model.** Its
  strong-binding leg is a **coverage factor** `1/(1+K)`; only the weak-binding leg is activated
  (Eq. [13], barrier `≈ ΔG_H*`, i.e. **slope 1 in this convention**) — and the paper attributes the
  strong-binding leg to **site blocking**, not to a barrier. **Impact: the plan's `max` is a declared
  approximation; each branch's docstring must name its physical effect (A ↔ activated proton transfer;
  B ↔ strong binding).**
- ⭐ **The Arrhenius premise is anchored *and* qualified**: `k₁ = k₀ exp(−ΔG_H*/kT)` [13] gives
  `activity ∝ exp(−Ea/kT)` with `Ea = ΔG_H*`, but the *same paper* multiplies by `1/(1+K)` [14].
  **A row using only `exp(−Ea/kT)` silently drops the site factor.**
- **Premises fixed**: one scalar descriptor; the switch **exactly at `ΔG_H* = 0`**; `k₀` fitted and
  *assumed* metal-independent here.
- ⭐ **Axis impact (instance layer)**: Eq. [8] fixes `ΔG_H* = ΔE_H + 0.24 eV`, so the apex
  `ΔG_H* = 0` sits at **`dE = −0.24 eV` on the Table-I `ΔE_H` axis**; rows must carry the shift or be
  given as `ΔG_H*` (§R2.1).
- **Not expressible**: "site", "coverage θ", "step/defect site" have no counterpart in a one-scalar
  state space; the coverage analysis (Eq. [15]) belongs in the scope list.

### R1.2.3 Bligaard et al. 2004 — the canonical citation, and its DOI corrected
**source**: S7, T. Bligaard, J. K. Nørskov, S. Dahl, J. Matthiesen, C. H. Christensen, J. Sehested,
"The Brønsted–Evans–Polanyi relation and the volcano curve in heterogeneous catalysis",
*J. Catal.* **224**(1), 206–217 (2004). **DOI `10.1016/j.jcat.2004.02.034`**, Crossref-verified by
title query. ⚠️ **DOI DISPROVED**: the dispatch's `10.1016/j.jcat.2004.02.005` resolves to
"N₂O-mediated propane oxidative dehydrogenation over steam-activated iron zeolites", *J. Catal.*
**223**(2), 382–388 (2004). **status**: `bibliographic-only` — closed access; ScienceDirect 403 for
curl and for the harness fetch tool; no repository copy. **No sentence is quoted.**
**Secondary anchor**: Nørskov et al. 2005 cites it as ref. 14 ("*J. Catal.*, **224**, 206 (2004)")
for the statement that **steps and low-coordination defects bind hydrogen more strongly than
close-packed surfaces**.
**Formalizable implication.** ⚠️ **Impact: no docstring may say "Bligaard et al. state that the volcano
is the intersection of two BEP lines"** — the paper is the citation the later first-hand sources use,
but its own sentence was not read. Round-2 request: one printed sentence + equation number. What *is*
supported on Nørskov's authority is the **same-family premise**: a BEP line is a property of a family
(close-packed surfaces), and defects deviate.

### R1.2.4 Nørskov, Bligaard, Rossmeisl & Christensen 2009 (review)
**source**: S9, *Nat. Chem.* **1**(1), 37–46 (2009), DOI `10.1038/nchem.121` — Crossref-verified.
**status**: `abstract-only` (closed; no file at Nature or DTU Orbit; abstract via `efetch
id=21378799`). The abstract states that theory can "understand variations in catalytic activity from
one catalyst to another" and reviews "the first steps towards using computational methods to design
new catalysts". ⚠️ **It contains no volcano equation, no `max` of two branches and no slope
statement.** **Formalizable implication: citation-only; no claim may be attached in round 1.**

### R1.2.5 Cheng & Hu 2008 — the two-step reduction (abstract-only) and the 3D volcano
**sources**: S10 (JPCC **112**, 1308–1311, DOI `10.1021/jp711191j`; OpenAlex `bronze` OA but ACS 403
here → **`abstract-only`**, retrieved via the OpenAlex abstract index) and S11 (JACS **130**,
10868–10869, DOI `10.1021/ja803555g`, **`bibliographic-only`**).
**S10 abstract, verbatim**: "Multistep surface processes involving a number of association reactions
and desorption processes may be considered as hypothetical one-step desorption processes. Thus,
**heterogeneous catalytic reactions can be treated kinetically as consisting of two steps: adsorption
and desorption**. It is also illustrated that the hypothetical one-step desorption process **follows
the BEP relation**. A volcano curve can be obtained from **kinetic analysis by including both
adsorption and desorption processes**."
**Formalizable implication.** ⭐ This is the closest thing to a **literature licence for reducing a
multistep cycle to two BEP branches** — the reduction is a move the literature itself makes.
⚠️ Abstract-level only: no equation, no slope, no page. **Impact: citable as precedent, not as a
premise.** S11 is the **multi-descriptor** extension: **impact — the plan's single-descriptor scope
limit must be named explicitly.**

### R1.2.6 ⭐⭐ Yang, Patil, McKone & Saidi 2021 — the opposite-slope branch sentence
**source**: S12, *Catal. Sci. Technol.* **11**, 6832–6838 (2021), DOI `10.1039/d1cy01170g`
(Crossref-verified). Green OA: **arXiv:2109.04219**, fetched here (978 567 bytes; 8 pages **including**
the SI tables quoted below). **status**: `first-hand` for the arXiv text; the journal pagination was
not opened. Loci below are the arXiv preprint's equations/tables.

1. ⭐ **Two branches, opposite slopes, switching rate-limiting step**:
   > "…the Brønsted–Evans–Polanyi (BEP) relation, a linear relation between a reaction's free energy and
   > its activation energy E_a, is confirmed for the HER on pure metal surfaces⁴³ … For example, **for
   > the metals with ΔG_H < 0 (ΔG_H > 0), the activation barrier of the rate-limiting Heyrovsky
   > (Volmer) reaction decreases with increasing (decreasing) ΔG_H.**"
   In the plan's notation: for `dE < 0` (strong binding) the limiting branch is Heyrovsky with
   **falling** barrier → slope `−alphaB`; for `dE > 0` the limiting branch is Volmer with **rising**
   barrier → slope `+alphaA`.
2. **The optimum, as a property of that model**: "The Nørskov model of Eq. (1) shows that **the maximum
   catalytic activity is at ΔG_H = 0** and the activity decreases when ΔG_H moves away from zero, thus
   reproducing the volcano relationship…".
3. **The classical two-sided formulation** (introduction): "Motivated by **Sabatier's principle that
   the maximum catalytic rate is achieved when the interaction between the reactants and catalyst is
   neither too strong nor too weak**,¹⁷ Parsons and Gerischer independently proposed the free energy of
   hydrogen adsorption, Δg_H, as an HER descriptor such that **the maximum rate corresponds to a
   minimum in the magnitude of Δg_H** under equilibrium conditions.¹⁸,¹⁹"
4. ⚠️ **Historical negative and modern qualification**: "…the maximum exchange current was **not
   associated with Δg_H = 0**, as proposed by Parsons"; "…several studies have argued that **Pt is not a
   thermoneutral catalyst with ΔG_H that deviates from zero**" (refs 31–33 = Lindgren, Kastlunger &
   Peterson, *ACS Catal.* **10**, 121 (2020); Kronberg & Laasonen, *ACS Catal.* (2021); Ooka, Wintzer &
   Nakamura, *ACS Catal.* **11**, 6298 (2021) — `secondary`, as printed in S12's reference list).
5. ⚠️ **The prefactor is not universal**: "**k₀ is not universal but is material-specific** … when
   restricted to metals with a similar range of H-binding energies, this effect is diminished –
   **hence the fit is relatively good near the peak of the volcano only**"; fitted
   `ln(k₀) = 23.16|ΔG_H| + 3.17`, `r² = 0.82`, with "**a careful derivation is needed**".
6. **Data tiers**: "(Pt, Ir, Pd and Rh) near |ΔG_H| = 0.1 eV, the metals near 0.5 eV, and the HER inert
   metals near 1 eV"; **descriptor construction**: Eq. (2) `ΔG_H = ΔE_H + ΔE_ZPE − TΔS`; "ΔE_ZPE is
   found to be less than 0.05 eV for all metals".

**Formalizable implication.** ⭐⭐ This is the round's strongest formalizable locus: it fixes
(i) the *existence* of two branches, (ii) their **opposite signs**, (iii) the **switch at `ΔG_H = 0`**
— i.e. the premises `0 < alphaA`, `0 < alphaB`, and **not** the product condition (§R3.1).
- The source states the **switch point**, not the closed-form apex: **impact — the docstring for `apex`
  must say "derived here from the crossing of the two branches; the literature states the crossing"**.
- ⭐ **`βA = βB` is what puts the apex at zero**: the source's optimum-at-zero is a property of a
  symmetric model. **Impact: the sharp statement must be about `dE*` as defined by the parameters; any
  "= 0" specialisation needs the explicit premise `betaA = betaB`.**
- **Impact on `activity`**: given S12's material-dependent prefactor, the formalized quantity must be
  defined **up to a positive constant**, and the volcano claim must be stated as the monotone relation
  between `Ea` and activity (which is what the plan proves).

### R1.2.7 ⭐ Man 2011 (DTU thesis = pre-print of Man et al. 2011) — the OER `max` of two branches
**sources**: S14 — thesis: I. C. Man, "Theoretical study of Electro-catalysts for oxygen evolution",
PhD thesis, DTU (2011), `URLS FETCHED`:
`https://backend.orbit.dtu.dk/ws/portalfiles/portal/6443470/Isabela%20Man.pdf` (21 648 216 bytes;
"Early version, also known as pre-print") → **`first-hand`**; and Man et al., *ChemCatChem* **3**(7),
1159–1165 (2011), DOI `10.1002/cctc.201000397`, Crossref-verified → **`bibliographic-only`** (closed).
⚠️ Equations/pages quoted below are the **thesis's**.

1. ⭐ **Volcano as a maximum of two branches of one descriptor** — Eq. 4.16 (printed p. 37):
   > "G⁰,OER = **max**[ΔG₂⁰, ΔG₃⁰] = **max**[(ΔG_O*⁰ − ΔG_HO*⁰), (ΔG_HOO*⁰ − ΔG_O*⁰)]  (4.16)"
   after the scaling relation, Eq. 4.17 (p. 37): "= **max**[ΔG_O*⁰ − ΔG_HO*⁰, **3.2** − (ΔG_O*⁰ − ΔG_HO*⁰)]";
   and the overpotential, Eq. 4.18 (p. 38): "η⁰,OER = {**max**[(ΔG_O*⁰ − ΔG_HO*⁰), **3.2 eV** −
   (ΔG_O*⁰ − ΔG_HO*⁰)]/e} − **1.23 V**".
2. **Descriptor**: "At this point we have simplified the situation sufficiently to define a
   **descriptor**, namely **ΔG⁰_O* − ΔG⁰_HO***."
3. **Scaling relation** (p. 36): "the binding energies of HOO* and HO* species on the various oxides
   are **linearly correlated, with a slope of approximately 1 and an intercept of 3.2 eV. The Mean
   Absolute Error (MAE) of the linear fit is 0.17 eV**"; "ΔG⁰_O* scales approximately linearly with
   ΔG⁰_HO* with a **slope of 0.5**".
4. ⭐ **The apex as an equality of the two steps** (p. 40): "If we start at the lower left hand side …
   the rate determining step is ΔG⁰_HOO*−ΔG⁰_O*. As we go up it moves towards the HOO* side, **whereas
   the peak of the volcano is situated between the two levels**. Then, as we go down on the right side
   … the rate determining step is ΔG_O*−ΔG_HO*."
5. ⚠️ **It is a thermodynamic `max` and the source says so** (p. 38): "From a theoretical standpoint,
   **the barriers between the intermediates are not included** … this thermodynamic analysis … capture
   trends in activity due to **cancellation of errors** when similar surfaces are compared. However, we
   cannot expect to obtain **absolute activities at this level of modeling**."
6. **Multi-site min–max**, Eq. 4.19 (p. 38): the OER overpotential over several site types is a **min**
   over sites of a **max** over steps ("the **attainable minimum** of all sites" / "the **attainable
   maximum**"); **a floor from scaling** (pp. 40–41): the constant 3.2 eV "**defines a lower limit for
   the OER overpotential**" — with the perfect separation "2.46 eV" it gives "a **minimum overpotential
   of 0.37 - 0.2 V**"; **mechanism change near the top** (p. 41): "For the oxides close to the top, a
   **change in mechanism** … is expected."

**Formalizable implication.** ⭐ First-hand source for the plan's `max` construction in a second
family: **two branches, one descriptor, slopes +1 and −1** — but over **step free energies**, not
barriers, with `alpha = 1` exactly. **Impact: the plan may state the max-of-two-branches structure as
literature-supported *for the thermodynamic overpotential*, and must state that `±alpha` with
`alpha ∈ (0,1)` comes from the kinetic version (§R1.2.6); citing Eq. 4.16 for
`Ea = max(step barriers)` would be a misattribution.** The apex statement is the **equality of the two
branches** (the plan's `Ea_A(dE*) = Ea_B(dE*)`) — with Eq. 4.18's printed 3.2 eV this is
`ΔG_O* − ΔG_HO* = 1.6 eV` (printed as 1.60 eV in S4/S22/S23, §R2.2). **Impact: the single-site,
single-descriptor scope limits must be stated (Eq. 4.19 is the multi-site reality), and the plan's
asymmetric `dE*` formula is the strict generalisation of both sources' symmetric special case.**

## §R1.3 The condition/validity side

### R1.3.1 ⚠️ The effective barrier is NOT a max of the step barriers (energetic span)
**source**: S15, S. Kozuch, S. Shaik, "How to conceptualize catalytic cycles? The energetic span
model", *Acc. Chem. Res.* **44**(2), 101–110 (2011) [Crossref records the online year 2010],
DOI `10.1021/ar1000956`; **`abstract-only`** (retrieved by `efetch id=21067215`). Verbatim:
> "**The TDTS-TDI energy difference and the reaction driving force define the energetic span (δE) of
> the cycle. Whenever the TDTS appears after the TDI, δE is the energy difference between these two
> states; when the opposite is true, we must also add the driving force** to this difference. Having
> δE, **the TOF is expressed simply in the Arrhenius-Eyring fashion, wherein δE serves as the apparent
> activation energy of the cycle.**"
> "…**neither one transition state nor one reaction step possess all the kinetic information** that
> determines the efficiency of a catalyst. Additionally, **the TDI and TDTS are not necessarily the
> highest and lowest states, nor do they have to be adjoined as a single step**. … **in catalysis,
> there are no rate-determining steps, but rather rate-determining states.**"
**First-hand derivative loci** (`second-reader`; the body itself is closed): S27 (Steiner & Reiher
2022) writes "The two states, TDTS and TDI, **maximize** the energetic span δE of a catalytic cycle"
with `TOF ≈ (k_BT/h)·e^(−βδE)`; the delegate's *ChemistryOpen* 2019 text gives the degree of TOF
control `X_TOF,i = (1/TOF)(∂TOF/∂E_i)` and both warn that the single-pair approximation **can fail**
("it is not possible to univocally identify the TDTS … we used the complete equation … without any
approximation"), the naive span (highest TS − lowest intermediate) being exact "only if … ΔG_r° = 0".

**Formalizable implication.** The cycle's apparent activation energy is a *maximum over (TS,
intermediate) pairs* and a **TDTS − TDI difference (+ driving force when inverted)** — a span, **not**
`max` of the per-step barriers. **Impact: the plan's `Ea = max(Ea_A, Ea_B)` must be declared as an
approximation; the docstring should name the energetic span as the refinement this theory does not
formalize, and the plan's scope list should say that its "rate-determining step" is a two-branch
surrogate.**

### R1.3.2 ⚠️ The apex is not the thermoneutral point in general
**source**: S16, K. S. Exner, "Does a Thermoneutral Electrocatalyst Correspond to the Apex of a
Volcano Plot for a Simple Two-Electron Process?", *Angew. Chem. Int. Ed.* **59**(26), 10236–10240
(2020), DOI `10.1002/anie.202003688` (Crossref-verified; Wiley pdf and full-xml **403 Cloudflare**
here) — **`abstract-only`** (`efetch id=32182397`). Verbatim:
> "The apex of the volcano curve … is **commonly defined by a hypothetical ideal material** that binds
> its reaction intermediates thermoneutrally at zero overpotential, in accordance with Sabatier's
> principle. However, recent studies report **a right shift of the apex** in a volcano curve, in which
> the most active electrocatalysts bind their reaction intermediates **endergonically** rather than
> thermoneutrally … this Viewpoint addresses the question of how the definition of an optimum catalyst
> needs to be modified … when **kinetic effects and the applied overpotential** are included."
**Formalizable implication.** "Apex at thermoneutral" is a **definition/idealisation**, and it shifts
once kinetics and overpotential enter. **Impact: keep the sharp statement about `dE*`; make
"`dE* = 0`" a corollary under the symmetry premise `betaA = betaB`; put the apex-shift finding in the
honesty table.**

### R1.3.3 ⭐ `0 < β < 1` printed, in an Arrhenius+BEP-derived leg equation
**source**: S13, J. Zheng, W. Sheng, Z. Zhuang, B. Xu, Y. Yan, "Universal dependence of hydrogen
oxidation and evolution reaction activity of platinum-group metals on pH and hydrogen binding energy",
*Sci. Adv.* **2**(3), e1501602 (2016), DOI `10.1126/sciadv.1501602`; **`first-hand`** — OA full text
via `europepmc.org/webservices/rest/PMC4803484/fullTextXML`. Verbatim:
> "From the Arrhenius equation and the Brønsted-Evans-Polanyi (BEP) relation, we can derive the
> following equation … (1) i₀ = A exp(−βFE_peak/RT) where A is the preexponential coefficient,
> **β characterizes the position of transition state along the reaction coordinate (0 < β < 1)**."
> "**Volcano-shaped curves** have been obtained when plotting HER activity versus HBE on various
> monometallic metals in base as well as in acid, **suggesting that an optimal HBE exists (Sabatier's
> principle)**."
> "**Similar β values (0.5 to 0.8)** support the fact that a similar HOR/HER mechanism is at play on
> all four metals", and its Eq. (2) `ΔE_a = βFΔE_peak`.
**Formalizable implication.** This is the round's best first-hand support for the *premise*
`0 < alphaA, alphaB`: a printed `0 < β < 1` inside an Arrhenius+BEP-derived leg equation, with
**measured** values 0.5/0.8/0.6/0.6 (§R2.4). ⚠️ It is (i) a **phenomenological** coefficient of an
activity–descriptor line, not a single-step transfer coefficient, (ii) for **four metals, all on one
leg** (no kink shown), (iii) a *measured range*, not a law. **Impact: the plan may carry `α` instance
rows from it, and may say `0 < α < 1` is *usual and transportable to this model only as a declared
identification*, never necessary (§R3.1).**

### R1.3.4 ⭐⭐ The volcano *is* two affine lines meeting at the optimum — the freshest first-hand statement

**source** (S26, `second-reader`, OA): Azcona-Aliende, Rodriguez & Calle-Vallejo, *ACS Catal.* **16**(6),
5805–5815 (2026), DOI `10.1021/acscatal.5c08978`. Verbatim (abstract and running text):
> "…segmentation creates **two lines, one with a negative slope and another with a positive slope, the
> hinge point being the ideal catalyst** … one part with a positive slope and another with a negative
> slope, and **the hinge point is the ideal catalyst**, for which (ΔG_O^ideal, ΔG_OH^ideal) =
> (2.46, 1.23) eV."

⭐ This is the literature's own **two-affine-lines-with-a-hinge** statement — i.e. the plan's
`max(branchA, branchB)` with the apex at the crossing — obtained by *segmentation* of the volcano.
**source** (S29, `second-reader`, OA): Polynski & Kozlov, *Adv. Sci.* (2026) e75932,
DOI `10.1002/advs.75932`, prints a **max-form activity law** in two descriptors:
> "lgTOF(x,y) = lg(TOF_opt) − **max**{a_x⁺(x−x₀), a_x⁻(x₀−x)} − **max**{a_y⁺(y−y₀), a_y⁻(y₀−y)},
> where x₀ and y₀ define the location of the Sabatier optimum (the apex of the volcano)."

Also reachable in the delegate's set (all `second-reader`): Oguz et al., *ACS Catal.* **15**, 19461
(2025) — "a Gibbs free energy of hydrogen adsorption (ΔG_H) **close to zero** … **lies at the apex of the
volcano curve**"; Suvarna et al., *ACS Catal.* **15**, 7296 (2025) — the peak "corresponds to a
situation in which **all the reaction steps are balanced**"; Beckers & De Vos, *iScience* **26**, 105790
(2023) — "The overall rate is maximized when **both steps are equally fast**" (a homogeneous, two-step
case, not a volcano).

⚠️ **Clean negative**: the literal English phrase "**the two steps are equally difficult**" (or
"barriers are equal") was searched in the delegate's corpus and returns **0 hits** — the optimum is
stated as *ΔG ≈ 0*, as *balanced steps*, as *the intersection of two lines*, or as *equal coverages*
(Wang et al., S28: "the optimal E_ad^I is 0.43 eV where the surface coverages of free sites and iodine
atoms are equal"), never in the "equally difficult" wording.

**Formalizable implication.** ⭐ **The plan's core shape now has a direct, quotable literature locus
(S26) and a printed `max`-form analogue in the multi-descriptor case (S29).** The apex is the *hinge /
crossing*, exactly the plan's `Ea_A(dE*) = Ea_B(dE*)`. **Impact: the plan's §3 statement can be
introduced as the formalisation of S26's two-line segmentation (with the DOIs), and the docstring for
`apex` can cite S26 for "the hinge point is the ideal catalyst" instead of relying on the plan's own
construction.** ⚠️ S26's own ideal point is printed as `(2.46, 1.23) eV` for a **two-descriptor**
(O, OH) picture — **multi-descriptor, hence out of this theory's one-descriptor scope**; only the
*shape* ("two lines with opposite slopes, hinge = optimum") transfers.

### R1.3.5 The sources' own list of where the volcano fails (S4, first-hand)
Verbatim from S4's "Challenges of the Sabatier Principle and Approaches Forward":
> "…the Sabatier principle has its basis on the thermodynamics because the binding energy is in essence
> an equilibrium constant between the adsorption and desorption of a reactant. However, thermodynamics
> alone cannot explain how quickly electron-transfer reactions occur. **Conventionally, kinetic factors
> such as activation barrier heights are assumed to scale universally with the thermodynamics. However,
> if this assumption is not valid, activity trends can no longer be predicted from thermodynamic
> criteria such as the thermodynamic overpotential, binding energies, or scaling relations.**"
> "**Coverage Dependence of the Binding Energy** — When evaluating the binding energy of intermediate
> species, it is also important to account for the chemical environment of the adsorbate. For example,
> the hydrogen binding energy on Pt(111) was shown to **shift from strong-binding to weak-binding when
> the coverage was increased**."
> "…the so-called **scaling relationships, which impose physical limitations on how the free-energy
> landscape can be tuned**" (the OER's four-electron pathway cannot be made thermoneutral).
> "Finally, there are some chemical processes which **the Sabatier principle does not consider at all** …
> the observed electrocatalytic behavior is not purely due to the intrinsic activity. For example,
> **mass transport**…"
Same paper, on the two-step case and on the refinement (`first-hand`):
> "**If we assume that the efficiency of the overall reaction is determined by the most
> thermodynamically unfavorable step**, a thermoneutral landscape … corresponds to the ideal situation …
> In the case of a two-step reaction, η_TD = |ΔG_RI|/e."
> "…an overpotential-dependent activity descriptor … denoted **G_max(η)** … makes use of the
> **free-energy span model** (Kozuch and Shaik, 2011 …) by assessing the free-energy difference between
> the intermediate with smallest free energy and the intermediate with highest free energy…"
**Formalizable implication.** ⭐ S4 supplies (i) the **`max`-over-steps structure as an explicit
assumption** ("If we assume that the efficiency … is determined by the most thermodynamically
unfavorable step") — i.e. the plan's `max` is the literature's own *assumption*, not a derivation;
(ii) the **kinetic-scaling assumption** that the plan's Arrhenius branch construction needs
("activation barrier heights are assumed to scale universally with the thermodynamics"); (iii) the
**coverage**, **scaling** and **mass-transport** scope limits. **Impact: the plan's premise list should
carry these three assumptions verbatim-adjacent (with the DOI and the section names), and the honesty
table should say that a model whose `Ea` is a max of two BEP branches presupposes exactly the
universal kinetic–thermodynamic scaling that S4 flags as questionable.**

---

### R1.3.6 Cross-reference on the BEP coefficient `α` (no duplication)
`theories/BEP/LITERATURE.md` already fixes, first-hand: the normative Brønsted relation and its
"α/β are constants **for a given reaction series**" (§R1.2.2); that the IUPAC physical-organic glossary
does **not** define the electrochemical transfer coefficient (§R1.2.3); `0 ≤ α ≤ 1` for the
electrochemical coefficient (Inzelt, printed p. 36, §R1.6.2); the bound is **"partly supported, with an
explicit condition"** — "Under classical transition state theory, this responsiveness is bounded
between 0 and 1" (§R1.7 (iv)); documented coefficients **outside** `(0,1)` with the source's own
explanation that the `(0,1)` restriction "**arose from the application of the Brønsted relationship
predominantly to oxygen or nitrogen acids and bases**" (Dodd 2004, printed p. 27, §R1.6.3 item 4); and
that apparent `α` values read off Tafel slopes are **coverage-dependent and not unique to a
rate-determining step** (Shinagawa et al. 2015, §R1.17.3). **Impact: "same family, constant α" is a
premise of the model, and the literature documents its failures — it belongs in the plan's premises
with a citation, not in the prose as an assumption.**

# §R2 — Instance parameters for the kernel-checked `ℚ` layer

**Rules.** Every number is printed in the source cited; a number that is *this record's arithmetic on
printed values* is marked **[arith]**. Figure-only values are marked `figure-only, not transcribable`.
Transcribe the printed decimal exactly (e.g. `-0.33` is `-33/100`).

## §R2.1 HER: reported `ΔG_H*` per metal

**(a) Nørskov et al. 2005, Table I, printed p. J24** — **DFT** (RPBE, 3-layer fcc(111), 0.25 ML unless
noted); column 3 is **[arith]** = column 2 + 0.24 eV by the paper's own Eq. [8]; column 5 is the
source's **experimental** compilation.

| metal | ΔE_H (0.25 ML)/eV | ΔG_H* [arith, Eq. 8]/eV | ΔE_H (1 ML)/eV | exp. log(i₀/A cm⁻²) as printed |
|---|---|---|---|---|
| Au(111) | 0.21 | 0.45 | 0.39 | −6.6 / −6.8; poly-Au −5.4 |
| Ag(111) | 0.27 | 0.51 | 0.34 | −5.0; poly-Ag −7.85 |
| Cu | −0.05 | 0.19 | 0.03 | −5.37 |
| Ir | −0.21 | 0.03 | −0.16 | −3.7; −3.46 |
| Pd | −0.38 | −0.14 | −0.33 | −3; −3 |
| Pt | −0.33 | −0.09 | −0.27 | −3.1; −2.63; Pt(111) −3.34 |
| Rh | −0.34 | −0.10 | −0.30 | −3.6; −3.22 |
| Re | −0.56 | −0.32 | −0.45 | −2.87 |
| Co | −0.51 | −0.27 | −0.49 | −5.32 |
| Ni | −0.51 | −0.27 | −0.47 | −5.2; −5.21 |
| W | −0.67 (bcc(110)) | −0.43 | −0.83 | −5.9; −5.9 |
| Mo | −0.61 (bcc(110)) | −0.37 | −0.77 | −7.07 |
| Nb | −0.80 (bcc(110)) | −0.56 | −0.80 | −6.8 |

⚠️ `a` in the printed table marks bcc(110) for W, Mo, Nb; **Fe and Ru are absent**; the paper's caveat
is that for Mo, W, Nb "the measured values are most probably not representative of the metal in the
metallic state" (surface oxide). **(b) Yang et al. 2021, Table S2** — **DFT** `ΔG_H` (eV) under
PBE / RPBE / PBE+vdW / RPBE+vdW for Ag, Au, Bi, Cd, Co (two polymorphs), Cu, In, Ir, Mo, Ni, Pd, Pt,
Re, Rh, Ru; **full table: `theories/Sabatier/literature/INSTANCE-DATA.md` §T1** (`first-hand`).
Reference values under RPBE+vdW: **Pt −0.082 · Ir −0.136 · Rh −0.159 · Pd −0.176 · Ru −0.220 ·
Co −0.252 · Ni −0.280 · Mo −0.352 · Cu 0.147 · Ag 0.527 · Au 0.532 · In 0.912 · Cd 1.031 · Bi 1.099**
⚠️ its printed `Mo / PBE+vdW = 3.620` is a manifest outlier; and (a)/(b) are **not interchangeable**
(Pt: −0.192 PBE / −0.038 RPBE there vs −0.33 for ΔE_H here) — **different functionals, coverages and
reference states; do not mix them in one Lean family**. **(c) S19, Table 1, printed p. 13**
(`second-reader`; DFT at 300 K; Eq. (4) = `G_adsH = E_adsH + 0.24 eV`): Pt −0.25 · Au 0.33 · Cu −0.01 ·
Ag 0.41 · Pd −0.30 · Ni −0.28 · Ir −0.15 · Rh −0.29 · Cd 1.05 · Zn 0.91 · Co −0.27 · Nb −0.65 ·
Mo −0.50 · W −0.51 · Re −0.56 · **Ru −0.40 · Fe −0.35** · Os −0.35 · Hf −0.84 · Ta −0.75 · V −0.66 ·
Cr −0.82 · Tc −0.48 (eV) — ⭐ **the only source found that prints Fe**. **(d) Greeley et al. 2006**
(S20, `second-reader` via the DTU thesis reprint) states the rule verbatim ("**0.24 eV is added to the
calculated binding energies … to give adsorption free energies**") and fixes the reference state as
"1 bar of H₂ (298 K) and … a coverage of either 1/4 or 1/3 ML" — but ⚠️ **its per-metal values exist
only in Figure 1 → `figure-only, not transcribable`.**

**⚠️ No source prints a `ΔG_H*` column at all**: S8 prints `ΔE_H`, and the `+0.24 eV` rule is stated in
prose (S8 Eq. [8]; S20 methods; S19 Eq. (4)). **Every `ΔG_H*` value in column 3 is *derived*, not
transcribed**, and the rule's ingredients are approximate (`ΔE_ZPE = 0.04 eV` taken as "representative
for all the metals"; `−TΔS_H = 0.20 eV` at 300 K / 1 bar H₂ / pH 0).

**Reported optimum for HER — a condition, not a number**: "**ΔG_H* = 0 separates the two legs of the
volcano**" (S8, p. J25); "the maximum catalytic activity is at **ΔG_H = 0**" (S12); "**the peak of the
volcano (maximum activity) occurs at ΔG_H of 0 eV**" (S21, `second-reader`). In the model's notation
`dE* = 0` **on the `ΔG_H*` axis**, i.e. **`dE* = −0.24 eV` on the Table-I `ΔE_H` axis**; `Pt` is the
practical optimum (`ΔG_H* = −0.09` **[arith]**), "very close to optimum" (S8).

**Formalizable implication of §R2.1 (instance layer).**
- **Premises the rows must carry** (all declared, none provable): the affine rule
  `ΔG_H*(E) = E + 0.24`; the reference state (300 K vs 298 K across sources); the **coverage** (0.25 ML
  in S8's figures, 1 ML also tabulated, 1/4 or 1/3 ML in S20 — coverage moves `ΔE_H` by up to ~0.16 eV,
  e.g. W −0.67 → −0.83); and that "optimum at zero" is a conclusion of S8's kinetic model with its own
  hypotheses (metal-independent `k₁ = k₀` for `ΔG_H* < 0`; single-site Langmuir coverage; only
  thermochemical barriers; fitted `k₀ = 200 s⁻¹ site⁻¹`).
- ⚠️ **Source-index, do not treat the numbers as physical constants**: the same metal has different
  printed values (Pt −0.09 in S8 vs −0.25 in S19; Mo −0.37 vs −0.50). **Impact: each Lean row carries
  its source tag and any verdict is relative to its own source.**
- **Fe/Ru**: possible only with S19's provenance (`second-reader`; must be re-read before use).

## §R2.2 The second family: OER/ORR via `ΔG_O − ΔG_OH`

**Apex, printed** — S4 (Ooka, Huang & Exner 2021, `first-hand`, §"…", text of the `G_max(η)` discussion):
> "…the application of **G_max(η)** to OER electrocatalysts predicts that the volcano apex is situated
> at about **ΔG₂ = 1.40 eV** (Exner, 2020g). Following the discussion … the thermodynamic analysis at
> zero overpotential in terms of η_TD purports **ΔG₂ = 1.60 eV** as the optimum situation in the OER,
> indicating **a shift of the volcano top by about 200 meV**."
With `ΔG₂ = ΔG_O − ΔG_OH` (S14 Eq. 4.16), this is the **printed optimal descriptor value 1.60 eV** for
OER plus a printed **apex shift to 1.40 eV** once the overpotential-dependent descriptor is used —
⭐ and 1.60 eV is exactly what this record derived independently from S14 Eq. 4.18 (`3.2/2`). Also
printed in S14: the OER overpotential's **lower bound 0.37 V** (pp. 40–41; 0.37 V as RuO₂'s value,
p. 92); ⚠️ S14's per-oxide values are **figure-only** (Figs. 4-4/4-5).

**⭐ Second printed locus — the apex printed *as arithmetic*** (`second-reader`, S22, Calle-Vallejo,
*Acc. Chem. Res.* **58**, 2749 (2025)). Its Eqs. (5)–(8) define `ΔG₁ = ΔG_OH`, `ΔG₂ = ΔG_O − ΔG_OH`,
`ΔG₃ = ΔG_OOH − ΔG_O`, `ΔG₄`, and Eq. (9) `η_OER = max(ΔG₁..ΔG₄)/e⁻ − U⁰`; then **Eq. (12)**:
> "**(ΔG_O − ΔG_OH)^optimal = (ΔG_OOH − ΔG_OH)/2 ≈ 3.20 eV / 2 = 1.60 eV**"

with the sentinels "Statistically speaking, the most common PLSs are eqs 2 and 3. Therefore, **the
least overpotential is found when ΔG₂ = ΔG₃**" ← *the intersection of the two lines, in words* — and
"the ideal catalyst at (1.23 eV, 0 V) while **the volcano apex is at (1.60 eV, −0.37 V)**"; for the ORR,
"the coordinates of the top are (ΔG_OH, −η_ORR) = **(0.86 eV, −0.37 V)**".
**⭐ Third printed locus** (`second-reader`, S23, *ChemSusChem* 2025): "materials with n = 3 are close to
the summit and span a narrow range of **ΔG₂ around 1.60 eV**", with its Eq. (9)
`η_OER = max(ΔG₁,…,ΔG₄)/e⁻ − E⁰` and "volcano **lines**" in the captions.

**Per-material OER descriptor values (DFT)** — S23, running text (`second-reader`), `ΔG₂ = ΔG_O − ΔG_OH`:

| material | ΔG_OH/eV | ΔG_O − ΔG_OH/eV | n | η_OER/V |
|---|---|---|---|---|
| SrRuO₃ | 1.37 | **1.23** | 2 | 0.75 |
| Sr₀.₈₈Na₀.₁₂RuO₃ (calc) | 1.56 | **1.60** | 3 | 0.37 |
| Ni–H porphyrin | 1.82 | **1.84** | 2 | 0.61 |
| Ni porphyrin with —OH | 1.58 | **1.63** | 3 | 0.40 |
| δ-opt. SrRuO₃ (predicted, δ = 0.31) | 1.67 | **1.54** | 3 | 0.44 |
| δ-opt. Ni porphyrin (predicted, δ = −0.24) | 1.58 | **1.60** | 3 | 0.37 |

**CO₂ reduction — a third family, and its optimum is an *assumption*** (`second-reader`, S24, Noh et
al. 2018, `Chem. Sci.` **9**, 5152, verbatim):
> "Considering that **the optimal \*CO binding energy** to achieve facile \*COOH formation and \*CO
> desorption **is approximately –0.5 eV** based on the scaling relation and the volcano plot,⁴⁸ we
> selected candidates for which the \*CO binding energies are in the range of **–0.60 to –0.43 eV**."

The delegate verified at the JATS `<ref>` level that S24's `cit48` is **Peterson & Nørskov,
*J. Phys. Chem. Lett.* **3**(2), 251–258 (2012)** (`10.1021/jz201461p`) — so the −0.5 eV is a
**quotation of another paper's fitted optimum**, not a printed equation; ⚠️ S24 gives **no leg
equations** either. **Negative**: S25 (Liu et al. 2017, *Nat. Commun.* **8**, 15438) states the optimum
only qualitatively — "the optimal value of this descriptor to be **very close to that of copper**" —
and its figure is `not transcribable`.

**Formalizable implication of §R2.2.**
- ⭐ **The OER family is a *derivable* instance**: given the declared premises
  (`ΔG_OOH − ΔG_OH = 3.20 eV`, `U⁰ = 1.23 V`, `ΔG₂ = ΔG_O − ΔG_OH`), the apex `= 3.20/2 = 1.60 eV`
  and `η* = 1.60 − 1.23 = 0.37 V` are **pure arithmetic on `min` of `max` of two affine functions** —
  mathlib can discharge it (`min_le_iff`, `le_max_iff`, `linarith`). Three printed loci agree on it
  (S14 Eq. 4.18 + S4; S22 Eq. (12); S23).
- ⚠️ **The CO₂RR optimum is an *assumed* number** (−0.5 eV, window [−0.60, −0.43] eV) with no printed
  two-branch equation. **Impact: the instance layer must distinguish "derived optimum" (OER:
  premises ⇒ theorem) from "assumed optimum" (CO₂RR: an axiom-free numeric hypothesis field); one
  shape for both families would present a literature *fit* as a theorem of the model.**
- ⚠️ **Apex shift with kinetics**: 1.40 eV (`G_max(η)`) vs the thermodynamic 1.60 eV (S4) — 200 meV,
  toward **stronger** binding. **Impact: the OER row must say which convention it uses.**

**Metals' `ΔG_O − ΔG_OH`** — S8 Table II (printed p. J25; DFT, 0.25 ML, fcc(111)), `[arith]` column =
`ΔG_O − ΔG_OH`: Pt 0.22 · Rh −0.20 · Ir 0.07 · Pd 0.31 · Ni −0.09 · Cu 0.53 · Ag 1.10 · Au 0.96 ·
Co −0.44 · W −1.56 · Mo −1.31 (eV). **Full table with `ΔG_OH`, `ΔG_O` and the reference-state
definition: `theories/Sabatier/literature/INSTANCE-DATA.md` §T2** (`first-hand`).
⚠️ **Convention warning**: these are **metal** surfaces referenced to gas-phase H₂O and they sit far
below the **oxide** apex (1.60 eV). **Impact: a different family from S14's oxides — keep two separate
Lean families with separate provenance notes, or drop the table.**

## §R2.3 Experimental reference data (context only)

Collected experimental `j₀` from S12's Table 1 (Pt(111) `4.5×10⁻⁴`, Pt/C `1.2×10⁻¹`, Ir/C `3.6×10⁻²`,
Pd `1.9×10⁻⁴`, Rh/C `6.7×10⁻³`, Ru `4.5×10⁻³`, Cu `1.45×10⁻⁷`, Co `3.6×10⁻⁶`, Ni `2.6×10⁻⁶` A cm⁻²,
each with its electrolyte and temperature) — **full table: `literature/INSTANCE-DATA.md` §T3**.

## §R2.4 Transfer / BEP coefficients (`α` of the volcano legs)

**S13 (Zheng et al. 2016) Table 1** — `β`, `A` from `i₀ = A exp(−βFE_peak/RT)`; `E_a` by RDE in 0.1 M
KOH and by an H₂-pump at pH 0; `β_Ea` from `ΔE_a = βFΔE_peak` (**full table: `INSTANCE-DATA.md` §T4**):

| catalyst | β | A | E_a (KOH)/kJ mol⁻¹ | E_a (H₂ pump)/kJ mol⁻¹ | ΔE_peak/V | β_Ea |
|---|---|---|---|---|---|---|
| Pt/C | 0.5 | 59 | 29.6 ± 0.4 | 16 ± 2 | 0.17 | 0.8 |
| Ir/C | 0.8 | 68 | 32.8 ± 0.4 | 19 ± 3 | 0.20 | 0.7 |
| Pd/C | 0.6 | 37 | 38.9 ± 3.0 | 31 ± 2 | 0.14 | 0.6 |
| Rh/C | 0.6 | 36 | 26.6 ± 0.7 | 28 ± 1 | — | — |

**S14 (Man thesis) is the only source here that fixes both slopes exactly**: Eq. 4.17/4.18's branches
have slopes **+1 and −1** in the descriptor `ΔG_O* − ΔG_HO*` — i.e. `alpha = 1` in the thermodynamic
limit. **S12** states the slopes' **signs** (opposite) but prints no number for them apart from the
descriptor tiers (§R1.2.6 item 6). **Impact: an instance row may carry `α` from S13's `β` values
(measured, HOR/HER, four metals) and the bound `alpha = 1` from S14 (thermodynamic, OER); there is
**no** source found here that prints a kinetic `α ∈ (0,1)` *together with* a two-branch volcano.**

---

# §R3 — What the literature does NOT support

Each item is a **clean negative** produced by searching for the claim and failing to find it.

**(1) `0 < alphaA * alphaB` is NOT a literature statement.** No source read here states the volcano
shape as equivalent to, or as following from, a **product/same-sign condition on the two slopes**. What
exists instead: opposite-sign branches with an RDS switch (S12); `max` of two branches with slopes
+1/−1, i.e. `alpha = 1` exactly, so no condition arises (S14); `0 < β < 1` for a *fitted* leg
coefficient of four metals (S13); `0 ≤ α ≤ 1` for the **electrochemical** transfer coefficient (BEP
record §R1.6.2); documented `α = −0.7` and `1.7` in one series (ibid. §R1.6.3), with the source's own
explanation that `(0,1)` is **empirical in origin**; coverage-dependent, non-unique Tafel slopes
(ibid. §R1.17.3) — and, from this round, a first-hand **counterexample class in catalysis itself**:
S28 fits "E_ad^IS = **−2.32**·E_ad^I + 1.00, which is a typical BEP relation … **E_ad^IS = 1.16·ΔH +
1.00**" and still obtains a volcano (slopes **outside** `(0,1)`, negative and >1). **Impact:
`volcano_shape ↔ 0 < alphaA·alphaB` must be presented as the plan's own sharpening of a modelling
hypothesis; the literature is cited for the *physics* (two branches penalizing opposite ends), never
for the equivalence.**

**(2) The literature does NOT justify `Ea = max(step barriers)` as a kinetic law.** The energetic-span
model gives a TDTS − TDI difference (+ driving force when inverted) as the apparent activation energy
and concludes that "there are no rate-determining steps, but rather rate-determining states" (S15);
the canonical HER paper's strong-binding leg is a Langmuir coverage factor, not a barrier (S8); the
first-hand `max` equations are over **step free energies**, with barriers explicitly excluded (S14);
and the `max` structure appears in a review as an explicit **assumption** — "If we assume that the
efficiency of the overall reaction is determined by the most thermodynamically unfavorable step" (S4).
**Impact: `max` is a declared premise of this theory; the docstring must say so in those words.**

**(3) "Apex at `dE = 0`" is not a source-established law.** It is (i) "**commonly defined by a
hypothetical ideal material**" and known to shift under kinetics/overpotential (S16, right shift;
S4 prints the concrete shift 1.60 → 1.40 eV for OER); (ii) a property of a *specific symmetric* kinetic
model (S12); (iii) contradicted by the historical experimental compilation ("the maximum exchange
current was not associated with Δg_H = 0", S12 §R1.2.1) and by "Pt is not a thermoneutral catalyst"
(refs 31–33 of S12, `secondary`). **Impact: the plan's sharp statement must be about
`dE* = (βB − βA)/(αA + αB)`; "`dE* = 0`" is a corollary under `betaA = betaB`.**

**(4) No source states the volcano as a theorem.** The strongest algebraic statement found is S14
Eqs. 4.16–4.18, identities **given** the assumption "either step 2 or step 3 is potential determining"
**plus** the empirical scaling relation (`ΔG_HOO* = ΔG_HO* + 3.2 eV`, slope ≈ 1, **MAE 0.17 eV**), and
the source explicitly excludes barriers and says one "cannot expect to obtain absolute activities at
this level of modeling". Everything else is a model, a fit, or a rule of thumb; the single-descriptor
reduction fails for multi-descriptor systems (S11, 3D volcano); the literature calls the principle
"**empirical**" (S4) and "the **customary but unsafe** use of **heuristic rules**" (S23); S30 states
outright that "**We cannot provide a general rigorous proof of the scaling** … **most likely no such
proof exists**"; and S25's neighbours concede that "it is still **often assumed** that catalyst
activity for a multi-step reaction can be reduced to one rate-determining intermediate".

**(5) The two-sided wording is not Sabatier's own.** Neither the 1912 lecture (`unstable` → 0 hits) nor
the 1913 book (« peu stables », « assez stable », « trop stable », « donne avec l'un des éléments » →
0 hits each) contains it; the book's own statements are **one-sided** ("an unstable hydride", pp. 148,
254). The modern two-sided sentence is a *modern* formulation (S4's abstract, and the attribution
chain Parsons/Gerischer in S12), so **the plan must cite it as such**.

---

# §R4 Delegated parcels of this round (`second-reader` unless re-read)

1. **Canonical wording** — Balandin 1969: DOI corrected, `bibliographic-only`, no OA route (§R1.2.0).
   Sabatier 1912: the delegate's independent search **corroborates §R1.1.1's negative**; the **French
   original is not hosted** (`/lecture/fr/`, `?lang=fr` are soft 404s) → its wording is `UNSUPPORTED`.
   Sabatier 1913: the delegate re-verified the page mapping (`printed = folio − 28`, five running
   heads) and supplied the **printed anchors p. 242 / p. 255**, showing the secondary source's page
   numbers and wording to be unusable (§R1.1.2). **IUPAC Gold Book: no entry exists** — a
   high-confidence clean negative from a 22 045-DOI sweep (§R1.1.3); the two candidate textbooks
   (Chorkendorff & Niemantsverdriet; Niemantsverdriet) stay `not-accessed` with **no invented page**,
   and print-verified substitutes are recorded in §R1.1.3.
2. **Instance data** — **Fe** is in no first-hand HER table here and is supplied by S19's printed
   `G_adsH` (**Fe −0.35 eV, Ru −0.40 eV**); no value may be invented. The **OER apex** has three
   printed loci agreeing on **1.60 eV** (S14 Eq. 4.18 + S4; S22 Eq. (12) as `3.20/2`; S23) plus a
   printed kinetic shift to **1.40 eV**; per-material descriptors are in S23. The **CO₂-reduction**
   optimum is printed only as a quotation of another paper's fit ("approximately **–0.5 eV**", S24;
   its `cit48` = Peterson & Nørskov 2012, verified at the JATS `<ref>` level), and all four designated
   primary sources are `not-accessed` → **the CO₂RR row is an *assumed* premise and its leg structure
   cannot be cited**.
3. **Validity side** — S4 was retrieved first-hand and supplies the coverage / scaling /
   mass-transport / kinetic-scaling caveats (§R1.3.5); the delegate added the first-hand derivative
   span loci S27 (and the *ChemistryOpen* 2019 `X_TOF` text) and S26/S28/S29/S30 (§R1.3.1, §R1.3.4,
   §R3). **Medford et al. 2015** and the **printed dispute over S8's dataset** (S17) are
   `not-accessed`; **impact: the plan should not treat S8's kinetic model or its experimental
   compilation as uncontested.**

# §R5 Net effect on `theories/Sabatier/plan.md`

*(The plan file as landed contains only §1–§2; these are the deltas the model sketch must absorb when
§3+ is written.)*

1. **Keep as planned**: the sharp criterion "`Ea` has a unique global minimum at `dE*` ⟺
   `0 < alphaA * alphaB`" — the algebra is correct (§R0) and nothing found contradicts it.
2. **New explicit premises / docstring obligations**: (i) `Ea = max(Ea_A, Ea_B)` is a **declared
   premise** (S4 states the same structure as an assumption; S14 uses it for *free energies*, not
   barriers; S15 says the kinetic object is a span), with branch A ↔ activated proton transfer /
   weak binding (S8 Eq. [13], S12) and branch B ↔ strong binding, which S8 attributes to **site
   blocking**; (ii) the **Arrhenius** form presupposes the universal kinetic–thermodynamic scaling
   S4 flags as questionable, and `activity` must be defined **up to a positive constant** (S12's `k₀`
   is material-specific); (iii) the **axis convention** `ΔG_H* = ΔE_H + 0.24 eV` (S8 Eq. [8]);
   (iv) **symmetry**: `dE* = 0` needs `betaA = betaB` (S12's model is symmetric; S16 shows the apex
   can shift and S4 quantifies a 200 meV shift); (v) **scope limits** — one descriptor (S11's 3D
   volcano), one site type (S14 Eq. 4.19 is a min over sites of a max over steps), one family with
   constant `α` (BEP record §R1.2.2, §R1.6.3), intrinsic activity only (S4: mass transport).
3. **Claims that must not be attributed to the literature**: the product condition (§R3.1); the
   max-of-barriers as a kinetic law (§R3.2); apex-at-zero as a law (§R3.3); the volcano as a theorem
   (§R3.4); the two-sided wording to Sabatier himself (§R3.5); **any "IUPAC normative wording" of the
   principle — no Gold Book entry exists (§R1.1.3)**; Bligaard 2004's content and the dispatch's DOIs
   for Bligaard 2004 and Balandin (§R1.2.0, §R1.2.3).
4. ⭐ **Instance layer — the S5 statements must split into two kinds of optimum.** (a) *Derived*: the
   OER apex is `3.20/2 = 1.60 eV` and `η* = 0.37 V`, provable from the declared premises
   (`ΔG_OOH − ΔG_OH = 3.20 eV`, `U⁰ = 1.23 V`) — the kernel can discharge it. (b) *Assumed*: the
   CO₂RR optimum `*CO ≈ −0.5 eV` (window −0.60…−0.43 eV) is a literature fit and **can only be an
   explicit numeric premise**. HER data (S8 Table I + Eq. [8], coverage- and source-tagged; S12
   Table S2; S19 for Fe/Ru) and the printed `α` range (S13: 0.5–0.8; S14: `alpha = 1`) are instance
   inputs, not theorems. **Impact: a single `optimalDescriptor` definition used for both families
   without a derived/assumed tag would present a fit as a theorem; the definition (or its docstring)
   must carry the distinction.**

---

# §R6 Outstanding for round 2

**Closed in round 1** (do not re-open): the IUPAC question — **no Gold Book entry exists** (§R1.1.3),
so no IUPAC wording may be cited; the Balandin and Bligaard DOIs — **corrected** (§R1.2.0, §R1.2.3);
the Sabatier 1912 wording — **the two-sided dictum is not there** (§R1.1.1); the 1913 page anchors —
**p. 242 / p. 255 replace the secondary source's numbers** (§R1.1.2).

Still open:
1. Sabatier 1920² (Gallica `bpt6k90295w`): does the general sentence appear there? (page + wording) —
   the 1913 search suggests the secondary quotation may come from this edition or a translation.
2. Nørskov 2009: one printed volcano sentence + page (§R1.2.4); Bligaard 2004: one printed sentence +
   equation number (§R1.2.3) — both bodies are closed here.
3. Kozuch & Shaik 2011 body: the `δE` equation and `X_TOF`, with page (§R1.3.1); Exner 2020 body: the
   criterion for the apex shift (§R1.3.2) — for both, first-hand *derivative* loci exist in S27 and
   S4, so the plan is not blocked.
4. **Re-read the `second-reader` rows before they enter Lean**: S19's Fe/Ru `G_adsH`, S22's Eq. (12),
   S23's per-material OER table, S26's two-line sentence, S27's span sentence, S29's `max`-form
   activity law (§R2.1, §R2.2, §R1.3.4).
