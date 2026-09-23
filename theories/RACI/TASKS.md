# theories/RACI/TASKS.md — PhotoLean task board: RACI (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/RACI/plan.md`.
- Status of this theory: **integration in progress** — the RACI (Restricted Access to a Conical
  Intersection ⇒ aggregation-induced emission) work is being ported from the independent
  ChemLean repository (`[local path removed]`, same Lean 4.17.0 / mathlib v4.17.0
  toolchain) as PhotoLean's 17th theory, following the repository's standards.

## Sprint 0 — integration

- [ ] Modules ported to `PhotoLean/RACI/` with imports adapted (11 modules)
- [ ] Statement authority extracted from the delivered signatures; compiles at 0 errors
- [ ] Instances + rational decision layer (PhotoLean-standard additions)
- [ ] Edges registered into `PhotoLean/Relations.lean` §17 + `theories/RELATIONS.md`
- [ ] Gates: build, strict scan, `#print axioms` on every row, fidelity 0 differences, verifier run
