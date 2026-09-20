# Notes on Storing the Primary Literature Sources

> *English translation of `proofs/literature/README.md`. The Chinese original at `proofs/literature/README.md` is authoritative — the formalization engine's contract (`proofs/ENGINE.yml`) reads the Chinese paths.*

This directory holds the original texts of the surveyed papers (PDF / LaTeX sources).
**Large files are not checked into the repository** (see `.gitignore`); only the conclusions
go into `proofs/LITERATURE.md`.

Conventions:

- Naming: `<FirstAuthor><Year>_<ShortTitle>.pdf`, for example `Guan2020_AIE_mechanism.pdf`;
- Each reference has a corresponding entry in `LITERATURE.md`, and that entry records the local file name;
- Do not read the contents of these files in full into the context — cite only the conclusions and the section locations.
