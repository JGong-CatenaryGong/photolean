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
- [x] Literature leaf populated: `theories/Einstein/LITERATURE.md` (literature_researcher, batch
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

- [x] `radFactor` — `PhotoLean/Einstein/Basic.lean` — Phase 2 — done — proved (EB-B1)
- [x] `aOfB` — `PhotoLean/Einstein/Basic.lean` — Phase 2 — done — proved (EB-B2)
- [x] `b12OfB21` — `PhotoLean/Einstein/Basic.lean` — Phase 2 — done — proved (EB-B3)
- [x] `fOfA` — `PhotoLean/Einstein/Basic.lean` — Phase 2 — done — proved (EB-B4)
- [x] `aOfInt` — `PhotoLean/Einstein/Basic.lean` — Phase 2 — done — proved (EB-B5)
- [x] `tauR` — `PhotoLean/Einstein/Basic.lean` — Phase 2 — done — proved (EB-B6)
- [x] `radFactor_pos` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — done — proved (EB-C1)
- [x] `bOfA_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — done — proved (EB-C2)
- [x] `aOfb_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — done — proved (EB-C2)
- [x] `detailed_balance` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — done — proved (EB-C3)
- [x] `degeneracy_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — done — proved (EB-C3)
- [x] `af_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — done — proved (EB-C4)
- [x] `fa_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — done — proved (EB-C4)
- [x] `int_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — done — proved (EB-C5)
- [x] `aOfInt_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — done — proved (EB-C5)
- [x] `full_chain_roundtrip` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — done — proved (EB-C6)
- [x] `f_pos_iff_a_pos` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — done — proved (EB-C7)
- [x] `yield_radiative` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — done — proved (EB-C8)
- [x] `lifetime_pos` — `PhotoLean/Einstein/Criterion.lean` — Phase 2 — done — proved (EB-C8)
- [x] `aOfB` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — done — proved (EB-R1)
- [x] `b12OfB21` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — done — proved (EB-R1)
- [x] `fOfA` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — done — proved (EB-R1)
- [x] `aOfInt` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — done — proved (EB-R1)
- [x] `tauR` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — done — proved (EB-R1)
- [x] `aOfB_cast` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — done — proved (EB-R1)
- [x] `b12OfB21_cast` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — done — proved (EB-R1)
- [x] `fOfA_cast` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — done — proved (EB-R1)
- [x] `aOfInt_cast` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — done — proved (EB-R1)
- [x] `tauR_cast` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — done — proved (EB-R1)
- [x] `rat_roundtrip_verdicts` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — done — proved (EB-R2)
- [x] `radFactor_not_rational` — `PhotoLean/Einstein/RatModel.lean` — Phase 2 — done — proved (EB-R2)
- [x] `twoLevelDyeLike` — `PhotoLean/Einstein/Instances.lean` — Phase 2 — done — proved (EB-I1)
- [x] `degeneracySwap` — `PhotoLean/Einstein/Instances.lean` — Phase 2 — done — proved (EB-I2)

### Notes raised at delivery (lead decisions, none is a statement change by prover_d)

1. **Plan §3.1 gap on EB-C6 (documentation plane). RESOLVED (lead, 2026-09-23, `937f636`).** The
   authority carried the corrected middle conjunct `aOfB K (aOfB K A / K) / K = A` while
   `theories/Einstein/plan.md` had no §3.1 log and its §4 row still printed the false `… = A / K`
   (false at `K = 2`, `A = 1`). The lead added §3.1 entry 1 and corrected the §4 text; the failed
   claim is recorded as false evidence in the log.
2. **Non-load-bearing premises in EB-C8 `yield_radiative` — carried to the Phase-3 premise audit
   (M6 in verifier run 1).** `lake build` reports
   `unused variable hA` / `unused variable hkNR`: the identity `A * (1/(A+kNR)) = A/(A+kNR)` holds
   unconditionally under totalized division (`mul_one_div`), so both premises are non-load-bearing.
   The signature is kept verbatim (statement-first; the authority is frozen and the fidelity
   checker compares word for word). Iron rule 3's weakest-premise revision would delete both
   premises and add the §3.1 log entry — a lead/authority edit, flagged here rather than done.
3. **`lakefile.toml` `defaultTargets` does not list the four Einstein modules. RESOLVED (lead,
   2026-09-23, `937f636`)**: the four targets are in `defaultTargets`; the whole-tree gate builds
   them, and verifier run 1 (2026-09-23) exercised the build evidence.
4. **Statement-fidelity checker**: the bare-name keying that produced five false differences on
   Einstein (nested `Rat` shadowing) was reported by prover_d and fixed by the lead in `7f24a1c`;
   the re-run reports 33/33 with 0 differences.

---

## Verifier run 1 — 2026-09-23 (independent, read-only)

**Verdict: PASS, 0 blocking.** Evidence (raw outputs in the verifier's report):
build all delivered modules exit 0; whole-tree `check.sh --strict` PASS with scan `clean`;
`#print axioms` over every delivered theorem (102 for the four wave-1 theories) — all within
`[propext, Classical.choice, Quot.sound]` (five classifier rows depend on `propext` only);
fidelity `--theory Einstein` — 0 signature differences against the authority; authority sha256 on this
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
