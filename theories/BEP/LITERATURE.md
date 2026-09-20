# theories/BEP/LITERATURE.md — Bell–Evans–Polanyi: sources, statements, formalizable implications

> Owner: `literature_researcher` (engine role). This file is the authority for the loci and the
> wording of the Bell–Evans–Polanyi (BEP) principle used by `theories/BEP/plan.md`, and for the
> provenance of every number used by the instance layer `PhotoLean/BEP/Instances.lean`.
> Language: English (contract `proofs/ENGINE.yml`; the only bilingual file is `RESULTS.md`).
> Status: **round 1 in progress** — the survey (primary loci, IUPAC wording, transfer coefficient,
> limitations, and the data table for B5b) lands in this file. Nothing below the line is a claim.

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
