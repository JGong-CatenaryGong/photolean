# theories/KashaVavilov/TASKS.md — PhotoLean task board: KashaVavilov (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/KashaVavilov/plan.md`.
- Status of this theory: **Phase 2 (proof formalization) — proof layer delivered, awaiting
  independent verifier PASS**. All 29 authority declarations are proved in
  `PhotoLean/KashaVavilov/{Basic,Criterion,Instances}.lean` (rows below moved `stmt` → `review`
  by prover_b on 2026-09-23); the checkboxes stay unticked until the lead records a verifier
  verdict. Batch: photophysics subgraph (groups A–D), dispatched 2026-09-22.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/KashaVavilov/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/KashaVavilov/probes/KashaVavilov-statement-skeleton.lean` — **29 declarations**
      (20 theorems + 9 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `5a51614d80d8340d76b605657802152f6574ad40c31aa6eb9e8d373d65dfdb15`
- [x] API calibration probe: `theories/KashaVavilov/probes/KashaVavilov-api-probe.lean` (exit 0)
- [x] Literature leaf populated: `theories/KashaVavilov/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

## Sprint 1 — proof formalization (Phase 2, KV1–KV3) — delivered, awaiting verifier

Proof owner: prover_b, exclusive per module (`Basic.lean` = KV1, `Criterion.lean` = KV2,
`Instances.lean` = KV3). Evidence recorded on 2026-09-23 (raw outcomes):

- `proofs/scripts/lake build PhotoLean.KashaVavilov.{Basic,Criterion,Instances}` — exit 0 each,
  no warnings.
- `proofs/scripts/check.sh --strict` (whole tree) — PASS, `sorry` / custom-axiom scan clean.
- `proofs/scripts/axioms.sh` — PASS on all 29 declarations (only `propext`, `Classical.choice`,
  `Quot.sound`), including `PhotoLean.KashaVavilov.d2_verdict`.
- `python3 theories/BEP/probes/bep-fidelity.py --theory KashaVavilov` — 29/29 word for word,
  signature differences **0**, not delivered **0** (10 auxiliary rows outside the authority).
- Statement changes: **none** (plan §3.1 unchanged; no statement incident).

### Declaration board (proved, `review`; ticking is lead-only after verifier PASS)

- [x] `SpecSame` — `Basic.lean` — KV1 — done — proved 2026-09-23
- [x] `fluoYield_eq_emitYield_zero_add_upperYield` — `Basic.lean` — KV1 — done — proved 2026-09-23
      (weakest-premise form: the delivered sibling's decorative `RateData` premise is not carried)
- [x] `rateData_mono` — `Basic.lean` — KV1 — done — proved 2026-09-23
- [x] `specFrac_zero_of_kashaRule` — `Basic.lean` — KV1 — done — proved 2026-09-23
- [x] `specFrac_succ_of_kashaRule` — `Basic.lean` — KV1 — done — proved 2026-09-23
- [x] `kashaRule_mono` — `Basic.lean` — KV1 — done — proved 2026-09-23
- [x] `specSame_of_kashaRule` — `Basic.lean` — KV1 — done — proved 2026-09-23
- [x] `kashaRule_not_implies_vavilovAt` — `Criterion.lean` — KV2 — done — proved 2026-09-23
      (witness `rad = 0` at level 1, `ic ≡ 1`; `fluoYield 1 = 1/2 ≠ 3/4 = fluoYield 2`)
- [x] `vavilovAt_not_implies_kashaRule` — `Criterion.lean` — KV2 — done — proved 2026-09-23
      (witness `rad = 0` at level 2, `ic ≡ 1`; `fluoYield 1 = fluoYield 2 = 3/4`, `rad 1 > 0`)
- [x] `lossless_separates_kasha_vavilov` — `Criterion.lean` — KV2 — done — proved 2026-09-23
      (witness `rad ≡ 1`, `ic 0 = 0`; `fluoYield 0 = fluoYield 1 = 1`)
- [x] `d2_verdict` — `Criterion.lean` — KV2 — done — proved 2026-09-23 (the headline; four conjuncts)
- [x] `cascade_pos_iff` — `Criterion.lean` — KV2 — done — proved 2026-09-23
- [x] `emitYield_pos_iff` — `Criterion.lean` — KV2 — done — proved 2026-09-23
- [x] `antiKasha_observable_iff` — `Criterion.lean` — KV2 — done — proved 2026-09-23
      (max-emitter argument via `Finset.exists_max_image`)
- [x] `upperYield_pos_of_rad_pos` — `Criterion.lean` — KV2 — done — proved 2026-09-23
- [x] `exists_maximal_emitter` — `Criterion.lean` — KV2 — done — proved 2026-09-23
- [x] `kashaPureLadderRad` — `Instances.lean` — KV3 — done — proved 2026-09-23
- [x] `kashaPureLadderIc` — `Instances.lean` — KV3 — done — proved 2026-09-23
- [x] `kashaPureLadder_verdict` — `Instances.lean` — KV3 — done — proved 2026-09-23
- [x] `antiVavilovLadderRad` — `Instances.lean` — KV3 — done — proved 2026-09-23
- [x] `antiVavilovLadderIc` — `Instances.lean` — KV3 — done — proved 2026-09-23
- [x] `antiVavilovLadder_verdict` — `Instances.lean` — KV3 — done — proved 2026-09-23
- [x] `vavilovOnlyLadderRad` — `Instances.lean` — KV3 — done — proved 2026-09-23
- [x] `vavilovOnlyLadderIc` — `Instances.lean` — KV3 — done — proved 2026-09-23
- [x] `vavilovOnlyLadder_verdict` — `Instances.lean` — KV3 — done — proved 2026-09-23
- [x] `losslessLadderRad` — `Instances.lean` — KV3 — done — proved 2026-09-23
- [x] `losslessLadderIc` — `Instances.lean` — KV3 — done — proved 2026-09-23
- [x] `losslessLadder_verdict` — `Instances.lean` — KV3 — done — proved 2026-09-23
- [x] `instances_distinct` — `Instances.lean` — KV3 — done — proved 2026-09-23

### Auxiliary declarations of the delivered modules (outside the authority)

- [x] `icBranch_eq_one_of_rad_zero` — `Criterion.lean` — KV2 — review
- [x] `cascade_eq_one_of_rad_zero_above` — `Criterion.lean` — KV2 — review
- [x] `verify_ladders_are_admissible` — `Instances.lean` — KV3 — review
- [x] `kashaPureLadder_upperYield` — `Instances.lean` — KV3 — review
- [x] `kashaPureLadder_fluoYield` — `Instances.lean` — KV3 — review
- [x] `antiVavilovLadder_fluoYield_one` — `Instances.lean` — KV3 — review
- [x] `antiVavilovLadder_fluoYield_two` — `Instances.lean` — KV3 — review
- [x] `vavilovOnlyLadder_fluoYield_one` — `Instances.lean` — KV3 — review
- [x] `vavilovOnlyLadder_fluoYield_two` — `Instances.lean` — KV3 — review
- [x] `losslessLadder_fluoYield_one` — `Instances.lean` — KV3 — review

## Sprint 2+ — registration (lead work, not started)

- Phase 3: register this theory's relation edges in `PhotoLean/Relations.lean` and
  `theories/RELATIONS.md` (iron rule 8②; the D2 layer's edges and the no-edge drafts are listed
  in plan §10). Not a prover task.

---

## Verifier run 1 — 2026-09-23 (independent, read-only)

**Verdict: PASS, 0 blocking.** Evidence (raw outputs in the verifier's report):
build all delivered modules exit 0; whole-tree `check.sh --strict` PASS with scan `clean`;
`#print axioms` over every delivered theorem (102 for the four wave-1 theories) — all within
`[propext, Classical.choice, Quot.sound]` (five classifier rows depend on `propext` only);
fidelity `--theory KashaVavilov` — 0 signature differences against the authority; authority sha256 on this
board matches the file byte-for-byte; headline rows `#print`-checked as non-trivial; independent
recomputation of the named-instance verdicts matched; adversarial counterexample attempts against
the headline rows and the boundary predicates only broke *premise-removed* forms, confirming the
delivered premises are load-bearing (or registering them for the premise audit below).

Findings carried to the Phase-3 audit and to the lead (recorded here as the single source of truth):
* M1 statement-change index missing in `proofs/API-NOTES.md` (fixed by the lead 2026-09-23).
* M2 `theories/StokesShift/plan.md` §4/§5 printed the refuted SS-C9 form (fixed by the lead 2026-09-23).
* M3 `SternVolmer.mixed_witness` third conjunct is a tautology (Phase-3 authority re-freeze list).
* M4 `Einstein.radFactor_not_rational` does not mention `radFactor` (Phase-3 re-freeze list; the
  intended `Irrational (radFactor 1 1 1)` is provable — verifier's probe).
* M5 stale SternVolmer evidence block (fixed by the lead 2026-09-23).
* M6 weakest-premise standard not yet executed on the wave-1 theories (Phase-3 premise audit;
  the concrete non-load-bearing premises are listed in `proofs/EXPERIENCE.md`).
* L1–L7 low findings: record hygiene, commit granularity (registered deviation), suppressions
  hiding one real unused premise, an empty commit whose correction never landed (relaunched by the
  lead 2026-09-23), and the naming-bridge caveat on `emEnergy_pos_iff_inverted`.

### Row-count correction (lead, 2026-09-23)

Two delivery commit bodies overstated their row counts (`e1f8987` said "16/16 rows", `6af9615` said
"13 declarations"; so did the board's sprint record). The correct accounting, verified against the
authority (29 declarations) and the fidelity report: **KV-Criterion = 9 authority rows**
(KV-C1..KV-C7 including the sub-rows KV-C7a/KV-C7b; the further rows in that commit are auxiliary),
**KV-Instances = 4 authority rows** (KV-I1..KV-I5) plus auxiliary rows. Totals stand: 29/29
authority declarations (20 theorems + 9 definitions), 29/29 axioms rows clean. Commit-message
history cannot be rewritten; this board entry is the record of record. (The earlier empty commit
`ee89b78` claimed this correction but contained no file change; this note lands it.)
