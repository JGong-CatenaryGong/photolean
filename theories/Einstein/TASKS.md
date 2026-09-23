# theories/Einstein/TASKS.md — PhotoLean task board: Einstein (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/Einstein/plan.md`.
- Status of this theory: **Phase 2 (proof formalization) delivered by prover_d 2026-09-23** —
  all 33 declarations are proved (22 theorems + 11 definitions), all four modules build at exit 0,
  every theorem passes the `#print axioms` gate, and the statement-fidelity checker reports
  33/33 word-for-word with 0 differences. Awaiting independent verifier PASS (lead ticks).
  Batch: photophysics subgraph (groups A–D), dispatched 2026-09-22.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/Einstein/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/Einstein/probes/Einstein-statement-skeleton.lean` — **33 declarations**
      (22 theorems + 11 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `de13f5b3850513efdc7fa5f46de1371386a07c574364c425a5967ed619be286d`
- [x] API calibration probe: `theories/Einstein/probes/Einstein-api-probe.lean` (exit 0)
- [ ] Literature leaf populated: `theories/Einstein/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

## Sprint 1 — proof delivery (Phase 2, prover_d, 2026-09-23)

Modules delivered (owner prover_d, exclusive):

- `PhotoLean/Einstein/Basic.lean` — EB-B1..EB-B6 (6 definitions) — `lake build` exit 0
- `PhotoLean/Einstein/Criterion.lean` — EB-C1..EB-C8 (13 theorems) — `lake build` exit 0
- `PhotoLean/Einstein/RatModel.lean` — EB-R1..EB-R2 (5 definitions + 7 theorems) — exit 0
- `PhotoLean/Einstein/Instances.lean` — EB-I1..EB-I2 (2 theorems) — exit 0

Gate evidence (raw outcomes in the delivery report of 2026-09-23):

| Gate | Result |
|---|---|
| `proofs/scripts/lake build PhotoLean.Einstein.{Basic,Criterion,RatModel,Instances}` | exit 0 (only two `unused variable` linter warnings, EB-C8 — see note 2) |
| `proofs/scripts/axioms.sh PhotoLean.Einstein.Criterion <each of 13 theorems>` | 13/13 PASS (only `propext`, `Classical.choice`, `Quot.sound`) |
| `proofs/scripts/axioms.sh PhotoLean.Einstein.{RatModel,Instances} <each of 9 theorems>` | 9/9 PASS (same three) |
| `proofs/scripts/check.sh --strict PhotoLean.Einstein.<module>` | PASS, scan clean |
| `python3 theories/BEP/probes/bep-fidelity.py --theory Einstein` | 33 delivered word-for-word, 0 signature differences, 0 missing |

### Declaration board (all `review`; ticking is lead-only after verifier PASS)

- [ ] `radFactor` — `PhotoLean/Einstein/Basic.lean` — Phase 2 — review — proved (EB-B1)
- [ ] `aOfB` — `PhotoLean/Einstein/Basic.lean` — Phase 2 — review — proved (EB-B2)
- [ ] `b12OfB21` — `PhotoLean/Einstein/Basic.lean` — Phase 2 — review — proved (EB-B3)
- [ ] `fOfA` — `PhotoLean/Einstein/Basic.lean` — Phase 2 — review — proved (EB-B4)
- [ ] `aOfInt` — `PhotoLean/Einstein/Basic.lean` — Phase 2 — review — proved (EB-B5)
- [ ] `tauR` — `PhotoLean/Einstein/Basic.lean` — Phase 2 — review — proved (EB-B6)
- [ ] `radFactor_pos` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — review — proved (EB-C1)
- [ ] `bOfA_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — review — proved (EB-C2)
- [ ] `aOfb_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — review — proved (EB-C2)
- [ ] `detailed_balance` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — review — proved (EB-C3)
- [ ] `degeneracy_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — review — proved (EB-C3)
- [ ] `af_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — review — proved (EB-C4)
- [ ] `fa_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — review — proved (EB-C4)
- [ ] `int_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — review — proved (EB-C5)
- [ ] `aOfInt_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — review — proved (EB-C5)
- [ ] `full_chain_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — review — proved (EB-C6)
- [ ] `f_pos_iff_a_pos` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — review — proved (EB-C7)
- [ ] `yield_radiative` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — review — proved (EB-C8)
- [ ] `lifetime_pos` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — review — proved (EB-C8)
- [ ] `aOfB` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — review — proved (EB-R1)
- [ ] `b12OfB21` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — review — proved (EB-R1)
- [ ] `fOfA` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — review — proved (EB-R1)
- [ ] `aOfInt` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — review — proved (EB-R1)
- [ ] `tauR` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — review — proved (EB-R1)
- [ ] `aOfB_cast` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — review — proved (EB-R1)
- [ ] `b12OfB21_cast` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — review — proved (EB-R1)
- [ ] `fOfA_cast` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — review — proved (EB-R1)
- [ ] `aOfInt_cast` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — review — proved (EB-R1)
- [ ] `tauR_cast` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — review — proved (EB-R1)
- [ ] `rat_roundtrip_verdicts` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — review — proved (EB-R2)
- [ ] `radFactor_not_rational` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — review — proved (EB-R2)
- [ ] `twoLevelDyeLike` — `PhotoLean/Einstein/Instances.lean` — Phase 2 — review — proved (EB-I1)
- [ ] `degeneracySwap` — `PhotoLean/Einstein/Instances.lean` — Phase 2 — review — proved (EB-I2)

### Notes raised at delivery (lead decisions, none is a statement change by prover_d)

1. **Plan §3.1 gap on EB-C6 (documentation plane).** The authority carries the corrected middle
   conjunct `aOfB K (aOfB K A / K) / K = A` and its docstring cites "plan §3.1 item 1", but
   `theories/Einstein/plan.md` has no §3.1 correction log and its §4 EB-C6 row still shows the
   false `… = A / K` (false at `K = 2`, `A = 1`). The delivered row follows the authority
   verbatim; the plan row and the missing log entry are the lead's to sync.
2. **Non-load-bearing premises in EB-C8 `yield_radiative`.** `lake build` reports
   `unused variable hA` / `unused variable hkNR`: the identity `A * (1/(A+kNR)) = A/(A+kNR)` holds
   unconditionally under totalized division (`mul_one_div`), so both premises are non-load-bearing.
   The signature is kept verbatim (statement-first; the authority is frozen and the fidelity
   checker compares word for word). Iron rule 3's weakest-premise revision would delete both
   premises and add the §3.1 log entry — a lead/authority edit, flagged here rather than done.
3. **`lakefile.toml` `defaultTargets` does not list the four Einstein modules** (lead-owned
   infrastructure, not in prover_d's ownership): a bare `proofs/scripts/check.sh --strict` builds
   every other theory but not these; the per-module gate commands cover them meanwhile.
4. **Statement-fidelity checker**: the bare-name keying that produced five false differences on
   Einstein (nested `Rat` shadowing) was reported by prover_d and fixed by the lead in `7f24a1c`;
   the re-run reports 33/33 with 0 differences.
