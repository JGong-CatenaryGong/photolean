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
- [ ] Literature leaf populated: `theories/KashaVavilov/LITERATURE.md` (literature_researcher, batch
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

- [ ] `SpecSame` — `Basic.lean` — KV1 — review — proved 2026-09-23
- [ ] `fluoYield_eq_emitYield_zero_add_upperYield` — `Basic.lean` — KV1 — review — proved 2026-09-23
      (weakest-premise form: the delivered sibling's decorative `RateData` premise is not carried)
- [ ] `rateData_mono` — `Basic.lean` — KV1 — review — proved 2026-09-23
- [ ] `specFrac_zero_of_kashaRule` — `Basic.lean` — KV1 — review — proved 2026-09-23
- [ ] `specFrac_succ_of_kashaRule` — `Basic.lean` — KV1 — review — proved 2026-09-23
- [ ] `kashaRule_mono` — `Basic.lean` — KV1 — review — proved 2026-09-23
- [ ] `specSame_of_kashaRule` — `Basic.lean` — KV1 — review — proved 2026-09-23
- [ ] `kashaRule_not_implies_vavilovAt` — `Criterion.lean` — KV2 — review — proved 2026-09-23
      (witness `rad = 0` at level 1, `ic ≡ 1`; `fluoYield 1 = 1/2 ≠ 3/4 = fluoYield 2`)
- [ ] `vavilovAt_not_implies_kashaRule` — `Criterion.lean` — KV2 — review — proved 2026-09-23
      (witness `rad = 0` at level 2, `ic ≡ 1`; `fluoYield 1 = fluoYield 2 = 3/4`, `rad 1 > 0`)
- [ ] `lossless_separates_kasha_vavilov` — `Criterion.lean` — KV2 — review — proved 2026-09-23
      (witness `rad ≡ 1`, `ic 0 = 0`; `fluoYield 0 = fluoYield 1 = 1`)
- [ ] `d2_verdict` — `Criterion.lean` — KV2 — review — proved 2026-09-23 (the headline; four conjuncts)
- [ ] `cascade_pos_iff` — `Criterion.lean` — KV2 — review — proved 2026-09-23
- [ ] `emitYield_pos_iff` — `Criterion.lean` — KV2 — review — proved 2026-09-23
- [ ] `antiKasha_observable_iff` — `Criterion.lean` — KV2 — review — proved 2026-09-23
      (max-emitter argument via `Finset.exists_max_image`)
- [ ] `upperYield_pos_of_rad_pos` — `Criterion.lean` — KV2 — review — proved 2026-09-23
- [ ] `exists_maximal_emitter` — `Criterion.lean` — KV2 — review — proved 2026-09-23
- [ ] `kashaPureLadderRad` — `Instances.lean` — KV3 — review — proved 2026-09-23
- [ ] `kashaPureLadderIc` — `Instances.lean` — KV3 — review — proved 2026-09-23
- [ ] `kashaPureLadder_verdict` — `Instances.lean` — KV3 — review — proved 2026-09-23
- [ ] `antiVavilovLadderRad` — `Instances.lean` — KV3 — review — proved 2026-09-23
- [ ] `antiVavilovLadderIc` — `Instances.lean` — KV3 — review — proved 2026-09-23
- [ ] `antiVavilovLadder_verdict` — `Instances.lean` — KV3 — review — proved 2026-09-23
- [ ] `vavilovOnlyLadderRad` — `Instances.lean` — KV3 — review — proved 2026-09-23
- [ ] `vavilovOnlyLadderIc` — `Instances.lean` — KV3 — review — proved 2026-09-23
- [ ] `vavilovOnlyLadder_verdict` — `Instances.lean` — KV3 — review — proved 2026-09-23
- [ ] `losslessLadderRad` — `Instances.lean` — KV3 — review — proved 2026-09-23
- [ ] `losslessLadderIc` — `Instances.lean` — KV3 — review — proved 2026-09-23
- [ ] `losslessLadder_verdict` — `Instances.lean` — KV3 — review — proved 2026-09-23
- [ ] `instances_distinct` — `Instances.lean` — KV3 — review — proved 2026-09-23

### Auxiliary declarations of the delivered modules (outside the authority)

- [ ] `icBranch_eq_one_of_rad_zero` — `Criterion.lean` — KV2 — review
- [ ] `cascade_eq_one_of_rad_zero_above` — `Criterion.lean` — KV2 — review
- [ ] `verify_ladders_are_admissible` — `Instances.lean` — KV3 — review
- [ ] `kashaPureLadder_upperYield` — `Instances.lean` — KV3 — review
- [ ] `kashaPureLadder_fluoYield` — `Instances.lean` — KV3 — review
- [ ] `antiVavilovLadder_fluoYield_one` — `Instances.lean` — KV3 — review
- [ ] `antiVavilovLadder_fluoYield_two` — `Instances.lean` — KV3 — review
- [ ] `vavilovOnlyLadder_fluoYield_one` — `Instances.lean` — KV3 — review
- [ ] `vavilovOnlyLadder_fluoYield_two` — `Instances.lean` — KV3 — review
- [ ] `losslessLadder_fluoYield_one` — `Instances.lean` — KV3 — review

## Sprint 2+ — registration (lead work, not started)

- Phase 3: register this theory's relation edges in `PhotoLean/Relations.lean` and
  `theories/RELATIONS.md` (iron rule 8②; the D2 layer's edges and the no-edge drafts are listed
  in plan §10). Not a prover task.
