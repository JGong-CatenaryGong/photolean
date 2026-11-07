# R8 bounded relation-audit independent validation

**Status: `PASS`; acceptance: `accepted-R8`.**

accepted-R8

## Artifact hashes

| Artifact | SHA-256 |
| --- | --- |
| `relation_audit/registry.accepted.json` | `894fa88a56de663e5447c9ec9667dc3461531535427ba5c492df9a8ba972c1ba` |
| `relation_audit/schema.accepted.json` | `95f60be6f1f0aa96d454bfb77fd5628c7e3da620ca018a13142db632ef197e1d` |
| `relation_audit/legacy-dispositions.accepted.json` | `98f0a4e1b384089acb9cf8ac6d51f453f017af820e2d5998ee2bbb933d379c1d` |
| `docs/RELATION-AUDIT-ACCEPTED.md` | `a6d7d6182e9a41b933fe89ddfca8d6f58088054a9f42e2796deb2cf3ff286b18` |
| `bounded_audit/coverage.json` | `7d4c4f2f6df6a50e3aa20ac510dddaebf3e0d63272cb8c9d3a83e90022b48e2d` |
| `relation_audit/registry.json` | `25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0` |
| `bounded_audit/r4/coverage-accepted.json` | `d1e44bf7bbb5e81c7b85f610d6ffc1d4d3fed0fcde5cd1ab3202fb23ca6c32fa` |

## Five separate dimensions

### Pair coverage

- Pair universe: 136
- Pairs with screening record: 136
- Pairs with any active statement-level record (named query or statement-level outOfScope): 136
- Pairs with a non-outOfScope query: 94
- Pairs whose only active record is a statement-level outOfScope: 42
- Remaining pairs: 0
- Every R1 pair has a named statement-level query or a statement-level outOfScope record; this is not a certification count and not a claim that every pair has a non-outOfScope query.

### Proposition-level query outcomes

- Active named queries: 152
- Outcomes: {'certified': 67, 'refuted': 0, 'unresolved': 39, 'notEstablished': 2, 'outOfScope': 44}
- Proposition-level bounded query outcomes, not pair coverage and not a completeness claim.

### Certified relation discovery

- Certified queries: 67
- Pairs with at least one certified relation: 53
- Certified relation kinds: {'definitionalIdentity': 12, 'implication': 4, 'equivalence': 13, 'conditionalComposition': 2, 'observationalEquivalence': 36}
- Active certified evidence classes: {'deliveredModule': 12, 'boundedProbe': 55}
- Distinct certified statement-level relations discovered; 67 certified queries over 53 pairs is not 136/136 certification.

### Retained legacy evidence

- Legacy records disposed exactly once: 151
- Named queries / pair anchors: 26 / 125
- Intra-theory records: 5
- Delivered certificates retained / active: 26 / 12
- Old absence/new evidence reconciliations: 44
- Alias repairs / corrected legacy views: 4 / 3
- Retained historical evidence; pair anchors and intra-theory records contribute zero active coverage.

### Unresolved candidates

- Candidate declarations: 3
- Attached queries: Q-XD1-SEG-01, Q-XD1-SIC-01, Q-XD1-SSS-01
- The three XD1 candidate declarations are unresolved evidence, never certificate library members.

## Counts

| Item | Value |
| --- | ---: |
| Pairs / queries / records | 136 / 152 / 152 |
| Screening packages | 10 |
| Certificate library total / legacy / probe | 93 / 38 / 55 |
| Active certified evidence total / probe / legacy | 67 / 55 / 12 |
| Probe files / reviewed declarations | 9 / 58 |

## External gates

| Gate | Command | Exit | Result |
| --- | --- | ---: | --- |
| `r1` | `python3 audit_boundary/validate_boundary.py` | 0 | PASS |
| `r2` | `python3 bounded_audit/validate_screening.py` | 0 | PASS |
| `r3_derived_content` | `python3 bounded_audit/r4/validate_r3_content.py` | 0 | PASS |
| `r4_frozen_snapshot` | `python3 bounded_audit/r4/validate_coverage.py --coverage bounded_audit/r4/coverage-accepted.json --skip-package-validators` | 0 | PASS |
| `r4_e1` | `python3 bounded_audit/r4/excited-01/validate.py` | 0 | PASS |
| `r4_e2` | `python3 bounded_audit/r4/excited-02/validate.py` | 0 | PASS |
| `r4_ci_derived_content` | `python3 bounded_audit/r5/validate_r4_ci_content.py` | 0 | PASS |
| `r5_rad1` | `python3 bounded_audit/r5/radiative-01/validate.py` | 0 | PASS |
| `r5_rad2` | `python3 bounded_audit/r5/radiative-02/validate.py` | 0 | PASS |
| `r5_rad3` | `python3 bounded_audit/r5/radiative-03/validate.py` | 0 | PASS |
| `r5_xd1` | `python3 bounded_audit/r5/cross-domain-01/validate.py` | 0 | PASS |
| `r5_xd2` | `python3 bounded_audit/r5/cross-domain-02/validate.py` | 0 | PASS |
| `r5_current_coverage` | `python3 bounded_audit/r5/validate_coverage.py` | 0 | PASS |
| `r3_raw_historical` | `python3 bounded_audit/validate_r3.py` | 1 | PASS |
| `r4_ci_raw_historical` | `python3 bounded_audit/r4/conical-01/validate.py` | 1 | PASS |
| `strict_build_scan` | `proofs/scripts/check.sh --strict` | 0 | PASS |
| `legacy_full_lean` | `python3 tools/relation_audit.py --manifest relation_audit/registry.json --schema relation_audit/schema.json --mode full --json-out <isolated-temp>/production-full-r8.json --lean-source-out <isolated-temp>/production-full-r8-lean-checks.lean` | 0 | PASS |
| `adversarial_mutations` | `python3 tools/relation_audit_bounded/tests/test_adversarial.py` | 0 | PASS |
| `probe:bounded_audit/r3/probes/R3-probe.lean` | `./proofs/scripts/lake env lean bounded_audit/r3/probes/R3-probe.lean` | 0 | PASS |
| `probe:bounded_audit/r4/conical-01/probes/R4-CI-probe.lean` | `./proofs/scripts/lake env lean bounded_audit/r4/conical-01/probes/R4-CI-probe.lean` | 0 | PASS |
| `probe:bounded_audit/r4/excited-01/probes/E1-probe.lean` | `./proofs/scripts/lake env lean bounded_audit/r4/excited-01/probes/E1-probe.lean` | 0 | PASS |
| `probe:bounded_audit/r4/excited-02/probes/E2-probe.lean` | `./proofs/scripts/lake env lean bounded_audit/r4/excited-02/probes/E2-probe.lean` | 0 | PASS |
| `probe:bounded_audit/r5/cross-domain-01/probes/XD1-probe.lean` | `./proofs/scripts/lake env lean bounded_audit/r5/cross-domain-01/probes/XD1-probe.lean` | 0 | PASS |
| `probe:bounded_audit/r5/radiative-01/probes/RAD1-probe.lean` | `./proofs/scripts/lake env lean bounded_audit/r5/radiative-01/probes/RAD1-probe.lean` | 0 | PASS |
| `probe:bounded_audit/r5/radiative-02/probes/RAD2-probe.lean` | `./proofs/scripts/lake env lean bounded_audit/r5/radiative-02/probes/RAD2-probe.lean` | 0 | PASS |
| `probe:bounded_audit/r5/radiative-03/probes/RAD3-probe.lean` | `./proofs/scripts/lake env lean bounded_audit/r5/radiative-03/probes/RAD3-probe.lean` | 0 | PASS |
| `probe:bounded_audit/wp-surface-01/probes/Surface-probe.lean` | `./proofs/scripts/lake env lean bounded_audit/wp-surface-01/probes/Surface-probe.lean` | 0 | PASS |
| `deterministic_rebuild` | `python3 tools/relation_audit_bounded/build.py --acceptance accepted-R8` | 0 | PASS |

## Probe compilation and axiom audit

| Probe | Declarations | Exit | Allowed-axiom audit |
| --- | ---: | ---: | --- |
| `bounded_audit/r3/probes/R3-probe.lean` | 7 | 0 | PASS |
| `bounded_audit/r4/conical-01/probes/R4-CI-probe.lean` | 8 | 0 | PASS |
| `bounded_audit/r4/excited-01/probes/E1-probe.lean` | 6 | 0 | PASS |
| `bounded_audit/r4/excited-02/probes/E2-probe.lean` | 5 | 0 | PASS |
| `bounded_audit/r5/cross-domain-01/probes/XD1-probe.lean` | 3 | 0 | PASS |
| `bounded_audit/r5/radiative-01/probes/RAD1-probe.lean` | 11 | 0 | PASS |
| `bounded_audit/r5/radiative-02/probes/RAD2-probe.lean` | 4 | 0 | PASS |
| `bounded_audit/r5/radiative-03/probes/RAD3-probe.lean` | 10 | 0 | PASS |
| `bounded_audit/wp-surface-01/probes/Surface-probe.lean` | 4 | 0 | PASS |

## Adversarial mutations

- Mutations rejected fail-closed: 17
- Positive controls passed: 5
- Required minimum mutations: 12
- All mutations fail-closed: True

The suite covers missing/duplicate pair, pair-anchor substitution, wrong outcome, certified without evidence, candidate promotion, unknown alias endpoint, unrepaired legacy record, missing legacy disposition, absence/new-evidence reconciliation removal, stale probe hash, forbidden axiom footprint, wrong evidence class, partial acceptance flip, self-hash cycle, legacy-anchor coverage inflation and missing probe declaration. Every input lives under a temporary directory.

## Deterministic rebuild

- Isolated rebuild builder exit: 0
- Byte-identical outputs: True
- `relation_audit/registry.accepted.json`: generated `894fa88a56de663e5447c9ec9667dc3461531535427ba5c492df9a8ba972c1ba`, rebuilt `894fa88a56de663e5447c9ec9667dc3461531535427ba5c492df9a8ba972c1ba`
- `relation_audit/schema.accepted.json`: generated `95f60be6f1f0aa96d454bfb77fd5628c7e3da620ca018a13142db632ef197e1d`, rebuilt `95f60be6f1f0aa96d454bfb77fd5628c7e3da620ca018a13142db632ef197e1d`
- `relation_audit/legacy-dispositions.accepted.json`: generated `98f0a4e1b384089acb9cf8ac6d51f453f017af820e2d5998ee2bbb933d379c1d`, rebuilt `98f0a4e1b384089acb9cf8ac6d51f453f017af820e2d5998ee2bbb933d379c1d`
- `docs/RELATION-AUDIT-ACCEPTED.md`: generated `a6d7d6182e9a41b933fe89ddfca8d6f58088054a9f42e2796deb2cf3ff286b18`, rebuilt `a6d7d6182e9a41b933fe89ddfca8d6f58088054a9f42e2796deb2cf3ff286b18`

## Invariants

- Legacy registry SHA-256: `25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0`
- Accepted coverage SHA-256: `7d4c4f2f6df6a50e3aa20ac510dddaebf3e0d63272cb8c9d3a83e90022b48e2d`
- Backup SHA-256: `c72fbc4cb134e57cde379f2a10011c9a27f0f7a3497af50fd6c4c404bdf2745a`
- Original repository HEAD: `7ad25a5f03a88acc3af03f65149cf2ac102e7dac` (clean=True)
- Delivered PhotoLean files / mismatches: 102 / 0

## Deviations and blockers

- **DEV-R8-01**: Ten accepted screening packages: R2 one, R3 one, R4 three, R5 five. Plan said: The plan describes eight accepted R2-R5 screening packages. Resolution: Use all ten actual accepted packages; no package was dropped or invented. The plan-metadata miscount is recorded and does not change the 136/58 counts. Blocking: False.

## Checks and failures

- Checks executed: 31347
- Checks failed: 0
- No failures.

## Non-claims

- 136/136 pair coverage means every pair has a named statement-level record, not that every pair is certified.
- Unresolved, notEstablished and outOfScope are outcomes, not failures and not refutations.
- The 55 bounded-probe certificates are package-local evidence, not additions to the frozen delivered PhotoLean tree.
- The three XD1 candidate declarations are unresolved evidence, not certificates.
- The legacy registry and its 151 records remain historical inputs; dispositions are additive interpretations.
- The bounded protocol does not exhaust all propositions of the seventeen theories.
- This report is validator evidence. When acceptanceState is pending it is not an acceptance record; only two independent reviewers and the lead may accept.

