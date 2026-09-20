# theories/kasha/literature — source artifacts of the Kasha literature record

This directory holds the *source artifacts* behind `theories/kasha/LITERATURE.md`, so that the
sentences quoted there can be re-checked without re-fetching a paywalled page. Only conclusions and
loci go into `LITERATURE.md`; the artifacts here are the raw evidence.

Convention (English, per `proofs/ENGINE.md` §1.5 — this is a proof-process artifact):

- file name: `<FirstAuthor><Year>_<short-title>.<ext>`;
- every file here is named in the `LITERATURE.md` entry that uses it, with the printed locus
  (page / table / equation number);
- **large files do not enter the repository** (the Marcus record states the same rule): a source is
  committed as *extracted text* when the quoted loci are text, and only the URL/DOI is recorded when
  the artifact is a many-megabyte PDF that can be re-fetched.

| file | source | why text, not PDF |
|---|---|---|
| `Birks1976_NIST_JRes80A_p389.txt` | J. B. Birks, "Photophysics of Aromatic Molecules" — the NIST open-access journal copy, *J. Res. NBS A* **80A**(3), 389–399 (1976), DOI `10.6028/jres.080a.038` | the record quotes its abstract and §2.5 (printed p. 392) verbatim; the 13 MB PDF was fetched from the NIST OA server, read, and deliberately **not** committed (size); the `.txt` is the extracted text of the same PDF, 81 KB |

Removed from the working tree on 2026-09-20: `nist80A389.pdf` (13 MB, above this repository's
recorded size convention; re-fetchable from the DOI above).
