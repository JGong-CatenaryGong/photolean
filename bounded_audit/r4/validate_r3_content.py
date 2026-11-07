#!/usr/bin/env python3
"""Derived fail-closed R3 *content* validator (historical package, current ledger).

This validator is a derivative of the accepted ``bounded_audit/validate_r3.py``. It
exists because the accepted R3 package pins the *mutable* cumulative ledger
(``snapshot.coverageLedgerSha256``) and the R3 round state (``round`` / 21 screened /
115 remaining / byRound / remaining ids), so it cannot stay green once R4 advances the
same ledger to 67/69. The accepted R3 artifacts are not edited and the ledger is not
rolled back.

Exactly the seven current-ledger freshness checks below are excluded; every other R3
check -- schema/vocabulary, the eleven pairs, the twelve queries, endpoints, statement
versions/signature/source hashes, aliases, shared contexts/translations, premises,
scopes, observation channels, five-status/seven-kind outcome rules, probe source and
axiom print-outs, search-log provenance and recompute records, counts and non-claims --
is preserved unchanged:

    snapshot.coverageLedgerSha256
    coverage.round
    coverage.cumulative
    coverage.remaining
    coverage.byRound
    coverage.remainingCount
    coverage.remainingSet

The excluded checks are printed as ``EXCLUDED [...]`` lines and the exclusion list is
itself asserted to be exactly the seven codes. Current cumulative coverage belongs to
``bounded_audit/r4/validate_coverage.py``, which independently re-derives the accepted
R2/R3 pair/query/status entries. The derived validator still reads the current ledger
for every non-freshness ledger check (accepted-entry reconciliation, annotations,
work-package presence).

Usage:
    python3 bounded_audit/r4/validate_r3_content.py
    python3 bounded_audit/r4/validate_r3_content.py /tmp/mut/screening.json

The validator re-derives its facts from the frozen R1 inventory, the frozen pair queue,
the accepted legacy registry, the accepted R2 package, the current coverage ledger, the
R3 search log, and the R3 probe. It does not trust the package's own counts or prose.
"""

import argparse
import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))   # bounded_audit/r4
ROOT = os.path.dirname(os.path.dirname(HERE))       # repository root

EXPECTED_PAIRS = [
    'P-Marcus-SymmetryFactor',
    'P-Marcus-Kasha',
    'P-Marcus-SternVolmer',
    'P-Marcus-QuantumYield',
    'P-Marcus-FluorPhos',
    'P-Kasha-SternVolmer',
    'P-Kasha-QuantumYield',
    'P-Kasha-FluorPhos',
    'P-SternVolmer-QuantumYield',
    'P-SternVolmer-FluorPhos',
    'P-QuantumYield-FluorPhos',
]
R2_PAIRS = [
    'P-Marcus-Hammond', 'P-Marcus-BEP', 'P-Marcus-Sabatier',
    'P-Hammond-BEP', 'P-Hammond-Sabatier', 'P-Hammond-SymmetryFactor',
    'P-BEP-Sabatier', 'P-BEP-SymmetryFactor', 'P-Kasha-Sabatier',
    'P-Sabatier-SymmetryFactor',
]
STATUSES = ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope']
KINDS = ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition',
         'observationalEquivalence', 'distinguishability', 'refutation']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
ENDPOINT_FORMS = {'definition', 'theorem', 'theorem-lhs-predicate',
                  'theorem-rhs-predicate', 'theorem-rhs-term'}
TRANSLATION_IDS = {'identity', 'rfl-pin', 'coordinate-map', 'rat-to-real',
                   'surface-to-barrier', 'descriptor-endpoint', 'energy-window',
                   'observational-setup', 'candidate-not-total', 'none-declared'}
ALIAS_CLASSES = {'r1-legacy-dangling', 'certificate-internal-endpoint'}
ALIAS_KINDS = {'theorem-rhs-term', 'theorem-lhs-predicate', 'theorem-rhs-predicate',
               'definition-zero-locus'}

INV_REL = 'audit_boundary/statement-inventory.json'
QUEUE_REL = 'audit_boundary/pair-queue.json'
CLUSTER_REL = 'audit_boundary/cluster-plan.json'
BOUNDARY_REL = 'audit_boundary/BOUNDARY.md'
REGISTRY_REL = 'relation_audit/registry.json'
R2_REL = 'bounded_audit/wp-surface-01/screening.json'
COVERAGE_REL = 'bounded_audit/coverage.json'
SCREENING_REL = 'bounded_audit/r3/screening.json'
SEARCH_REL = 'bounded_audit/r3/search-log.json'
PROBE_REL = 'bounded_audit/r3/probes/R3-probe.lean'
PROBE_LOG_REL = 'bounded_audit/r3/probes/compile.log'
EXPECTED_REGISTRY_SHA = '25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0'
EXPECTED_LEAN_FILES = 102
EXPECTED_SCREENED = 21
EXPECTED_REMAINING = 115

# The seven current-ledger freshness checks this derived validator intentionally
# excludes. They pin the *mutable* cumulative ledger to its R3 state and are owned by
# bounded_audit/r4/validate_coverage.py, which validates the advanced R4 ledger and
# independently re-derives the accepted R2/R3 entries. Nothing else is excluded.
EXCLUDED_CHECKS = [
    'snapshot.coverageLedgerSha256',
    'coverage.round',
    'coverage.cumulative',
    'coverage.remaining',
    'coverage.byRound',
    'coverage.remainingCount',
    'coverage.remainingSet',
]
EXCLUDED_CHECK_SET = set(EXCLUDED_CHECKS)


def sha_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def load_rel(rel):
    with open(os.path.join(ROOT, rel), encoding='utf-8') as fh:
        return json.load(fh)


def read_rel(rel):
    with open(os.path.join(ROOT, rel), encoding='utf-8') as fh:
        return fh.read()


class Checker:
    def __init__(self):
        self.failures = []
        self.excluded = []

    def check(self, cond, code, message):
        if not cond:
            self.failures.append((code, message))

    def exclude(self, code, message):
        """Record an intentionally excluded current-ledger freshness check."""
        self.excluded.append((code, message))

    def nonempty(self, value, code, message):
        self.check(isinstance(value, str) and value.strip() != '', code, message)

    def summary(self):
        print('R3 bounded screening content validation (derived)')
        print('  root: %s' % ROOT)
        print('  excluded current-ledger freshness checks: %d' % len(self.excluded))
        for code, message in self.excluded:
            print('EXCLUDED [%s] %s' % (code, message))
        print('  checks failed: %d' % len(self.failures))
        if self.failures:
            for code, message in self.failures:
                print('FAIL [%s] %s' % (code, message))
            print('RESULT: FAIL (%d failed checks)' % len(self.failures))
            return 1
        print('RESULT: PASS (all R3 package-content checks passed; '
              '7 current-ledger freshness checks excluded)')
        return 0


def parse_probe_axioms(text):
    """Parse `#print axioms` output, tolerating Lean's line wrapping."""
    blocks = {}
    joined = re.sub(r'\s*\n\s*', ' ', text)
    for m in re.finditer(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", joined):
        axioms = {a.strip() for a in m.group(2).split(',') if a.strip()}
        blocks[m.group(1)] = axioms
    return blocks


def short_name(decl):
    return decl.rsplit('.', 1)[-1]


def _status_counts(queries):
    counts = {}
    for q in queries:
        status = q.get('outcome', {}).get('status')
        counts[status] = counts.get(status, 0) + 1
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('screening', nargs='?', default=SCREENING_REL)
    args = parser.parse_args()

    c = Checker()
    for rel in [INV_REL, QUEUE_REL, CLUSTER_REL, BOUNDARY_REL, REGISTRY_REL, R2_REL,
                COVERAGE_REL, args.screening, SEARCH_REL, PROBE_REL, PROBE_LOG_REL]:
        if not os.path.exists(os.path.join(ROOT, rel)):
            print('FAIL [file.missing] required artifact not found: %s' % rel)
            print('RESULT: FAIL')
            return 1

    screening = load_rel(args.screening)
    inv = load_rel(INV_REL)
    queue = load_rel(QUEUE_REL)
    cluster = load_rel(CLUSTER_REL)
    registry = load_rel(REGISTRY_REL)
    r2 = load_rel(R2_REL)
    coverage = load_rel(COVERAGE_REL)
    search_log = load_rel(SEARCH_REL)
    probe_text = read_rel(PROBE_REL)
    probe_log = read_rel(PROBE_LOG_REL)

    inv_by_id = {row['id']: row for row in inv['statements']}
    dangling_ids = {d['id'] for d in inv.get('legacyDanglingStatements', [])}
    queue_by_id = {row['pairId']: row for row in queue['pairs']}
    all_pairs = [row['pairId'] for row in queue['pairs']]
    r2_pairs = [p['pairId'] for p in r2['pairs']]
    reg_certs = {x['id']: x for x in registry['certificates']}
    probe_axioms = parse_probe_axioms(probe_log)

    # ---------------------------------------------------------------- vocabulary
    c.check(screening.get('schemaVersion') == '1.0.0', 'schema.version',
            'unexpected schemaVersion')
    c.check(screening.get('artifactKind') == 'bounded-screening-package',
            'schema.kind', 'unexpected artifactKind')
    c.check(screening.get('round') == 'R3', 'schema.round', 'unexpected round')
    c.check(screening.get('statusVocabulary') == STATUSES, 'schema.statusVocabulary',
            'status vocabulary drift')
    c.check(screening.get('kindVocabulary') == KINDS, 'schema.kindVocabulary',
            'kind vocabulary drift')
    c.check(set(screening.get('allowedAxioms', [])) == ALLOWED_AXIOMS,
            'schema.allowedAxioms', 'allowed-axiom list drift')

    # ---------------------------------------------------------------- snapshot
    snap = screening.get('snapshot', {})
    c.check(snap.get('id') == 'snap-bounded-audit-2026-11-04', 'snapshot.id',
            'snapshot id drift')
    for rel, key in [(INV_REL, 'inventorySha256'), (QUEUE_REL, 'pairQueueSha256'),
                     (CLUSTER_REL, 'clusterPlanSha256'),
                     (BOUNDARY_REL, 'boundarySha256'),
                     (REGISTRY_REL, 'legacyRegistrySha256'),
                     (COVERAGE_REL, 'coverageLedgerSha256')]:
        if key == 'coverageLedgerSha256':
            # Excluded freshness check: the cumulative ledger is mutable and is pinned
            # by bounded_audit/r4/validate_coverage.py, not by this historical validator.
            c.exclude('snapshot.%s' % key,
                      'current-ledger hash pin on %s (accepted pin %s, current %s; '
                      'owned by r4/validate_coverage.py)'
                      % (rel, snap.get(key), sha_file(os.path.join(ROOT, rel))))
            continue
        actual = sha_file(os.path.join(ROOT, rel))
        c.check(snap.get(key) == actual, 'snapshot.%s' % key,
                '%s hash drift: %s != %s' % (rel, snap.get(key), actual))
    c.check(snap.get('legacyRegistrySha256') == EXPECTED_REGISTRY_SHA,
            'snapshot.registryPinned', 'legacy registry hash is not the accepted hash')
    lean_files = []
    for dirpath, _dirnames, filenames in os.walk(os.path.join(ROOT, 'PhotoLean')):
        for name in filenames:
            if name.endswith('.lean'):
                lean_files.append(os.path.join(dirpath, name))
    c.check(len(lean_files) == EXPECTED_LEAN_FILES, 'snapshot.leanFileCount',
            'delivered Lean tree has %d files, expected %d'
            % (len(lean_files), EXPECTED_LEAN_FILES))

    # ---------------------------------------------------------------- references
    inv_ref = screening.get('inventoryReference', {})
    c.check(inv_ref.get('sha256') == sha_file(os.path.join(ROOT, INV_REL)),
            'inventoryReference.sha256', 'inventory reference hash drift')
    c.check(inv_ref.get('statementRows') == len(inv['statements']),
            'inventoryReference.rows', 'inventory row count drift')
    c.check(inv_ref.get('screeningEligibleRows') ==
            sum(1 for s in inv['statements'] if s['screeningEligible']),
            'inventoryReference.eligible', 'eligible row count drift')
    reg_ref = screening.get('legacyRegistryReference', {})
    c.check(reg_ref.get('sha256') == sha_file(os.path.join(ROOT, REGISTRY_REL)),
            'legacyRegistryReference.sha256', 'registry reference hash drift')
    c.check(reg_ref.get('certificateCount') == len(registry['certificates']),
            'legacyRegistryReference.certs', 'registry certificate count drift')
    search_ref = screening.get('searchLogReference', {})
    c.check(search_ref.get('sha256') == sha_file(os.path.join(ROOT, SEARCH_REL)),
            'searchLogReference.sha256', 'search-log hash drift')
    probe_ref = screening.get('probeReference', {})
    c.check(probe_ref.get('sha256') == sha_file(os.path.join(ROOT, PROBE_REL)),
            'probeReference.sha256', 'probe hash drift')

    # ---------------------------------------------------------------- coverage ledger
    c.check(coverage.get('schemaVersion') == '1.0.0', 'coverage.version',
            'coverage ledger schemaVersion drift')
    c.check(coverage.get('artifactKind') == 'bounded-coverage-ledger',
            'coverage.kind', 'coverage ledger artifactKind drift')
    # Excluded freshness check: the accepted R3 package froze the ledger at round R3,
    # but R4 advances the same ledger to round R4. Current state belongs to
    # bounded_audit/r4/validate_coverage.py.
    c.exclude('coverage.round',
              'current-ledger round: accepted package pinned R3, current %r '
              '(owned by r4/validate_coverage.py)' % coverage.get('round'))
    c.check(coverage.get('universe', {}).get('pairCount') == len(all_pairs),
            'coverage.universe', 'coverage universe pair count drift')
    c.check(coverage.get('universe', {}).get('sourceSha256') ==
            sha_file(os.path.join(ROOT, QUEUE_REL)), 'coverage.universeSha',
            'coverage universe source hash drift')
    screened = coverage.get('screenedPairs', [])
    screened_ids = [e.get('pairId') for e in screened]
    c.check(len(screened_ids) == EXPECTED_SCREENED, 'coverage.screenedCount',
            'coverage has %d screened pairs, expected %d'
            % (len(screened_ids), EXPECTED_SCREENED))
    c.check(len(screened_ids) == len(set(screened_ids)), 'coverage.duplicate',
            'coverage ledger has a duplicate screened pair')
    c.check(set(screened_ids) <= set(all_pairs), 'coverage.unknownPair',
            'coverage ledger names a pair outside the R1 queue')
    for entry in screened:
        c.nonempty(entry.get('acceptance'), 'coverage.acceptance',
                   'coverage entry for %r has no acceptance status' % entry.get('pairId'))
        c.nonempty(entry.get('overlapNote'), 'coverage.overlapNote',
                   'coverage entry for %r has no overlap note' % entry.get('pairId'))
        c.check(entry.get('packagePath') in (R2_REL, SCREENING_REL), 'coverage.packagePath',
                'coverage entry for %r names an unexpected package path'
                % entry.get('pairId'))
        c.check(entry.get('round') in ('R2', 'R3'), 'coverage.round',
                'coverage entry for %r has an unexpected round' % entry.get('pairId'))
    # Per-pair ledger reconciliation against the two packages.
    r2_status = {p['pairId']: dict(_status_counts(p['queries'])) for p in r2['pairs']}
    r2_counts = {p['pairId']: len(p['queries']) for p in r2['pairs']}
    r3_status = {p['pairId']: dict(_status_counts(p['queries']))
                 for p in screening.get('pairs', [])}
    r3_counts = {p['pairId']: len(p['queries'])
                 for p in screening.get('pairs', [])}
    for entry in screened:
        pid = entry.get('pairId')
        if entry.get('round') == 'R2' and pid in r2_status:
            c.check(entry.get('queryCount') == r2_counts[pid], 'coverage.r2QueryCount',
                    'coverage queryCount for %r does not match the R2 package' % pid)
            c.check(entry.get('byStatus') == r2_status[pid], 'coverage.r2ByStatus',
                    'coverage byStatus for %r does not match the R2 package' % pid)
        if entry.get('round') == 'R3' and pid in r3_status:
            c.check(entry.get('queryCount') == r3_counts[pid], 'coverage.r3QueryCount',
                    'coverage queryCount for %r does not match the R3 package' % pid)
            c.check(entry.get('byStatus') == r3_status[pid], 'coverage.r3ByStatus',
                    'coverage byStatus for %r does not match the R3 package' % pid)
    kasha_sab = next((e for e in screened if e.get('pairId') == 'P-Kasha-Sabatier'), None)
    c.check(kasha_sab is not None and kasha_sab.get('round') == 'R2'
            and 'cross-domain' in (kasha_sab.get('overlapNote') or '').lower(),
            'coverage.earlyPairNote', 'early cross-domain pair is not annotated in the ledger')
    marcus_sym = next((e for e in screened if e.get('pairId') == 'P-Marcus-SymmetryFactor'), None)
    c.check(marcus_sym is not None and marcus_sym.get('round') == 'R3'
            and 'surface-gap' in (marcus_sym.get('overlapNote') or '').lower(),
            'coverage.surfaceGapNote',
            'surface-gap reconciliation is not annotated in the ledger')
    cov_r2 = [e['pairId'] for e in screened if e.get('round') == 'R2']
    cov_r3 = [e['pairId'] for e in screened if e.get('round') == 'R3']
    c.check(set(cov_r2) == set(R2_PAIRS), 'coverage.r2Set',
            'coverage R2 pairs are not exactly the accepted R2 pairs')
    c.check(set(cov_r3) == set(EXPECTED_PAIRS), 'coverage.r3Set',
            'coverage R3 pairs are not exactly the eleven R3 pairs')
    c.check(not (set(cov_r2) & set(cov_r3)), 'coverage.overlap',
            'coverage ledger overlaps R2 and R3 pairs')
    cum = coverage.get('cumulative', {})
    # Excluded freshness checks: the following four pin the ledger's R3 cumulative
    # state (21/115, byRound {R2, R3}). R4 legitimately advances them to 67/69 with
    # byRound {R2, R3, R4}; current coverage is owned by r4/validate_coverage.py.
    c.exclude('coverage.cumulative',
              'current-ledger cumulative screened count: pinned %d, current %r '
              '(owned by r4/validate_coverage.py)'
              % (EXPECTED_SCREENED, cum.get('screenedPairCount')))
    c.exclude('coverage.remaining',
              'current-ledger cumulative remaining count: pinned %d, current %r '
              '(owned by r4/validate_coverage.py)'
              % (EXPECTED_REMAINING, cum.get('remainingPairCount')))
    c.exclude('coverage.byRound',
              'current-ledger by-round counts: pinned %r, current %r '
              '(owned by r4/validate_coverage.py)'
              % ({'R2': 10, 'R3': 11}, cum.get('byRound')))
    c.check(cum.get('surfaceGapReconciliation') == 'P-Marcus-SymmetryFactor',
            'coverage.surfaceGap', 'surface-gap reconciliation not recorded')
    c.check(cum.get('earlyCrossDomainPair') == 'P-Kasha-Sabatier',
            'coverage.earlyPair', 'early cross-domain pair not recorded')
    remaining = coverage.get('remainingPairIds', [])
    expected_remaining = [pid for pid in all_pairs if pid not in set(screened_ids)]
    c.exclude('coverage.remainingCount',
              'current-ledger remaining list length: pinned %d, current %d '
              '(owned by r4/validate_coverage.py)'
              % (EXPECTED_REMAINING, len(remaining)))
    c.exclude('coverage.remainingSet',
              'current-ledger remaining list contents: pinned queue-minus-screened '
              '(%d), current %d (owned by r4/validate_coverage.py)'
              % (len(expected_remaining), len(remaining)))
    c.check(not (set(remaining) & set(screened_ids)), 'coverage.remainingOverlap',
            'remainingPairIds overlaps the screened pairs')
    work_packages = coverage.get('acceptedWorkPackages', [])
    c.check(len(work_packages) >= 2, 'coverage.workPackages',
            'coverage ledger has fewer than two work packages')
    r2_wp = next((w for w in work_packages if w.get('round') == 'R2'), None)
    r3_wp = next((w for w in work_packages if w.get('round') == 'R3'), None)
    c.check(r2_wp is not None, 'coverage.r2WorkPackage', 'missing R2 work package')
    c.check(r3_wp is not None, 'coverage.r3WorkPackage', 'missing R3 work package')
    if r2_wp is not None:
        c.check(r2_wp.get('pairCount') == 10, 'coverage.r2PairCount',
                'R2 work-package pair count drift')
        c.check(r2_wp.get('sha256') == sha_file(os.path.join(ROOT, R2_REL)),
                'coverage.r2Sha', 'R2 work-package hash drift')
    if r3_wp is not None:
        c.check(r3_wp.get('pairCount') == 11, 'coverage.r3PairCount',
                'R3 work-package pair count drift')
        c.check(r3_wp.get('path') == SCREENING_REL, 'coverage.r3Path',
                'R3 work-package path drift')

    # ---------------------------------------------------------------- pair coverage
    pair_work = screening.get('workPackage', {})
    c.check(pair_work.get('id') == 'R3-QUENCH-01', 'workPackage.id',
            'work package id drift')
    c.check(pair_work.get('pairIds') == EXPECTED_PAIRS, 'workPackage.pairIds',
            'work package pair list is not the approved eleven')
    c.check(pair_work.get('pairCount') == len(EXPECTED_PAIRS), 'workPackage.pairCount',
            'work package pair count drift')
    c.check(not (set(pair_work.get('pairIds', [])) & set(R2_PAIRS)),
            'workPackage.r2Overlap', 'R3 pair list overlaps the accepted R2 pairs')
    c.check('P-Marcus-SymmetryFactor' in pair_work.get('pairIds', []),
            'workPackage.surfaceGap', 'surface-gap pair missing from the R3 list')
    c.check('P-Kasha-Sabatier' not in pair_work.get('pairIds', []),
            'workPackage.rescreen', 'R2 early cross-domain pair is rescreened in R3')

    pairs = screening.get('pairs', [])
    pair_ids = [p.get('pairId') for p in pairs]
    c.check(len(pair_ids) == len(set(pair_ids)), 'pairs.duplicate',
            'duplicate pair id in screening package')
    c.check(set(pair_ids) == set(EXPECTED_PAIRS), 'pairs.coverage',
            'screening pair set is not exactly the approved eleven')
    c.check(len(pair_ids) == len(EXPECTED_PAIRS), 'pairs.count',
            'screening pair count is not eleven')

    all_query_ids = []
    query_by_id = {}
    for pair in pairs:
        pid = pair.get('pairId')
        c.nonempty(pid, 'pair.id', 'pair row without pairId')
        qrow = queue_by_id.get(pid)
        c.check(qrow is not None, 'pair.queueMissing',
                'pair %r is not in the R1 pair queue' % pid)
        if qrow is not None:
            c.check(pair.get('theories') == qrow['theories'], 'pair.theories',
                    'pair %r theories do not match the R1 queue' % pid)
            c.check(pair.get('primaryCluster') == qrow['screeningCluster'],
                    'pair.cluster', 'pair %r primary cluster does not match the R1 queue'
                    % pid)
        qids = pair.get('queryIds', [])
        c.check(isinstance(qids, list) and len(qids) >= 1, 'pair.noQuery',
                'pair %r has no named query or outOfScope record' % pid)
        c.check(qids == [q.get('queryId') for q in pair.get('queries', [])],
                'pair.queryIds', 'pair %r queryIds do not match its query rows' % pid)
        c.check(len(qids) == len(set(qids)), 'pair.queryDuplicate',
                'pair %r has duplicate query ids' % pid)
        c.check(len(pair.get('queries', [])) >= 1, 'pair.noQueryRow',
                'pair %r has no query row' % pid)
        for q in pair.get('queries', []):
            qid = q.get('queryId')
            all_query_ids.append(qid)
            query_by_id[qid] = q
            c.check(q.get('pairId') == pid, 'query.pairId',
                    'query %r pairId does not match its pair row' % qid)

    c.check(len(all_query_ids) == len(set(all_query_ids)), 'queries.duplicate',
            'duplicate query id in screening package')

    # ---------------------------------------------------------------- aliases
    alias_rows = screening.get('aliasResolutions', [])
    alias_ids = [a.get('id') for a in alias_rows]
    c.check(len(alias_ids) == len(set(alias_ids)), 'aliases.duplicate',
            'duplicate alias resolution id')
    resolved_aliases = set()
    for a in alias_rows:
        aid = a.get('id')
        klass = a.get('aliasClass')
        c.check(klass in ALIAS_CLASSES, 'alias.class',
                'alias %r has unknown aliasClass' % aid)
        alias_stmt = a.get('aliasStatementId')
        if klass == 'r1-legacy-dangling':
            c.check(alias_stmt in dangling_ids, 'alias.legacyDangling',
                    'alias %r claims r1-legacy-dangling but is not in the R1 dangling list'
                    % aid)
            resolved_aliases.add(alias_stmt)
        resolved = a.get('resolvedStatementId')
        c.check(resolved in inv_by_id, 'alias.resolved',
                'alias %r resolvedStatementId is not an inventory statement' % aid)
        if resolved in inv_by_id:
            c.check(a.get('resolvedDeclaration') == inv_by_id[resolved]['declaration'],
                    'alias.resolvedDeclaration',
                    'alias %r resolvedDeclaration drift' % aid)
        c.check(a.get('resolutionKind') in ALIAS_KINDS, 'alias.resolutionKind',
                'alias %r has unknown resolutionKind' % aid)
        c.nonempty(a.get('note'), 'alias.note', 'alias %r has no note' % aid)
    c.check(resolved_aliases == dangling_ids, 'aliases.coverage',
            'alias resolutions do not cover exactly the four R1 dangling aliases')

    # ---------------------------------------------------------------- per-query checks
    non_certified = []
    certified_decls = set()
    for pair in pairs:
        for q in pair.get('queries', []):
            qid = q.get('queryId')
            c.nonempty(qid, 'query.id', 'query row without queryId')
            for field in ['title', 'chemicalQuestion', 'chemicalRationale',
                          'expectedKindRationale', 'falsificationCondition']:
                c.nonempty(q.get(field), 'query.%s' % field,
                           'query %r missing %s' % (qid, field))

            kind = q.get('expectedKind')
            c.check(kind in KINDS, 'query.kind',
                    'query %r expectedKind %r is not a seven-kind value' % (qid, kind))
            c.check(kind != 'refuted', 'query.kindRefuted',
                    'query %r uses the status refuted as an evidence kind' % qid)

            # endpoints
            endpoints = q.get('endpoints', {})
            for side in ['source', 'target']:
                ep = endpoints.get(side, {})
                stmt = ep.get('statementId')
                c.check(stmt in inv_by_id, 'endpoint.missing',
                        'query %r %s endpoint %r is not an inventory statement'
                        % (qid, side, stmt))
                if stmt not in inv_by_id:
                    continue
                row = inv_by_id[stmt]
                for key in ['theory', 'declaration', 'declarationKind', 'sourceArtifact',
                            'sourceLine', 'version', 'signatureSha256',
                            'sourceArtifactSha256']:
                    c.check(ep.get(key) == row[key], 'endpoint.%s' % key,
                            'query %r %s endpoint field %s drifts from the inventory'
                            % (qid, side, key))
                src_path = os.path.join(ROOT, row['sourceArtifact'])
                c.check(os.path.exists(src_path), 'endpoint.sourceMissing',
                        'query %r %s source artifact is missing' % (qid, side))
                if os.path.exists(src_path):
                    c.check(sha_file(src_path) == row['sourceArtifactSha256'],
                            'endpoint.sourceHash',
                            'query %r %s source artifact hash drift' % (qid, side))
                c.check(ep.get('endpointForm') in ENDPOINT_FORMS, 'endpoint.form',
                        'query %r %s has unknown endpointForm' % (qid, side))
                c.check(stmt not in dangling_ids, 'endpoint.danglingAlias',
                        'query %r %s cites a dangling legacy alias as an endpoint'
                        % (qid, side))
            src_theory = endpoints.get('source', {}).get('theory')
            tgt_theory = endpoints.get('target', {}).get('theory')
            c.check(src_theory != tgt_theory, 'endpoint.sameTheory',
                    'query %r endpoints are not cross-theory' % qid)
            c.check({src_theory, tgt_theory} == set(pair.get('theories', [])),
                    'endpoint.pairTheories',
                    'query %r endpoints do not belong to the pair theories' % qid)

            # shared context and translations
            ctx = q.get('sharedContext', {})
            ctx_id = ctx.get('id')
            c.check(ctx_id in screening.get('contextLibrary', {}), 'context.missing',
                    'query %r shared context %r is not in the context library'
                    % (qid, ctx_id))
            c.check(isinstance(ctx.get('fields'), list) and len(ctx.get('fields')) >= 1,
                    'context.fields', 'query %r shared context has no fields' % qid)
            c.nonempty(ctx.get('physicalReading'), 'context.reading',
                       'query %r shared context has no physical reading' % qid)
            c.nonempty(ctx.get('provenance'), 'context.provenance',
                       'query %r shared context has no provenance' % qid)
            trans = q.get('translations', {})
            for side in ['left', 'right']:
                tr = trans.get(side, {})
                tid = tr.get('id')
                c.check(tid in TRANSLATION_IDS, 'translation.id',
                        'query %r %s translation id %r is not admissible'
                        % (qid, side, tid))
                if tid in {'none-declared', 'candidate-not-total'}:
                    c.nonempty(tr.get('reason'), 'translation.reason',
                               'query %r %s translation %r has no reason'
                               % (qid, side, tid))
                else:
                    c.nonempty(tr.get('term'), 'translation.term',
                               'query %r %s translation has no term' % (qid, side))
                c.nonempty(tr.get('requirement'), 'translation.requirement',
                           'query %r %s translation has no requirement note' % (qid, side))

            # premises
            prem = q.get('premises', {})
            c.nonempty(prem.get('predicate'), 'premise.predicate',
                       'query %r has no premise predicate' % qid)
            pids = prem.get('premiseIds')
            defs = prem.get('definitions')
            c.check(isinstance(pids, list), 'premise.ids', 'query %r premiseIds is not a list'
                    % qid)
            c.check(isinstance(defs, list), 'premise.defs',
                    'query %r premise definitions is not a list' % qid)
            def_ids = []
            for d in defs or []:
                def_ids.append(d.get('id'))
                c.nonempty(d.get('predicate'), 'premise.defPredicate',
                           'query %r premise definition has no predicate' % qid)
                c.nonempty(d.get('statement'), 'premise.defStatement',
                           'query %r premise definition has no statement' % qid)
                c.nonempty(d.get('loadBearing'), 'premise.defLoadBearing',
                           'query %r premise definition has no load-bearing note' % qid)
            c.check(sorted(def_ids) == sorted(pids or []), 'premise.defIds',
                    'query %r premiseIds and definitions do not match' % qid)
            if not pids:
                c.check('True' in (prem.get('predicate') or ''), 'premise.emptyPredicate',
                        'query %r has no premise ids but its predicate is not True' % qid)

            # scope and snapshot
            scope = q.get('scope', {})
            sid = scope.get('id')
            c.check(sid in screening.get('scopeLibrary', {}), 'scope.missing',
                    'query %r scope %r is not in the scope library' % (qid, sid))
            c.nonempty(scope.get('description'), 'scope.description',
                       'query %r scope has no description' % qid)
            c.nonempty(scope.get('domain'), 'scope.domain',
                       'query %r scope has no domain' % qid)
            c.check(scope.get('snapshot') == snap.get('id'), 'scope.snapshot',
                    'query %r scope snapshot does not match the package snapshot' % qid)

            # observation channels
            channels = q.get('observationChannels', [])
            c.check(isinstance(channels, list), 'channel.list',
                    'query %r observationChannels is not a list' % qid)
            if kind in {'observationalEquivalence', 'distinguishability'}:
                c.check(len(channels) >= 1, 'channel.required',
                        'query %r has kind %s but no observation channel' % (qid, kind))
            for ch in channels or []:
                c.nonempty(ch.get('id'), 'channel.id',
                           'query %r has a channel without id' % qid)
                c.nonempty(ch.get('observedValueType'), 'channel.valueType',
                           'query %r channel has no observed-value type' % qid)
                c.nonempty(ch.get('inputDomain'), 'channel.inputDomain',
                           'query %r channel has no input domain' % qid)
                c.check(ch.get('domainNonempty') is True, 'channel.domainNonempty',
                        'query %r channel domain is not declared nonempty' % qid)
                c.nonempty(ch.get('leftObs'), 'channel.leftObs',
                           'query %r channel has no left observation' % qid)
                c.nonempty(ch.get('rightObs'), 'channel.rightObs',
                           'query %r channel has no right observation' % qid)

            # outcome
            outcome = q.get('outcome', {})
            status = outcome.get('status')
            c.check(status in STATUSES, 'outcome.status',
                    'query %r outcome status %r is not one of the five' % (qid, status))
            c.nonempty(outcome.get('rationale'), 'outcome.rationale',
                       'query %r outcome has no rationale' % qid)
            evidence = outcome.get('evidence', {})
            c.check(isinstance(evidence, dict), 'outcome.evidence',
                    'query %r outcome evidence is not an object' % qid)

            if status == 'certified':
                etype = evidence.get('type')
                c.check(etype == 'r3-probe-certificate', 'evidence.type',
                        'query %r certified evidence has unsupported type %r'
                        % (qid, etype))
                c.check(evidence.get('kind') == kind, 'evidence.kindMatch',
                        'query %r evidence kind %r does not match expectedKind %r'
                        % (qid, evidence.get('kind'), kind))
                c.check(evidence.get('kind') in KINDS, 'evidence.kind',
                        'query %r evidence kind is not a seven-kind value' % qid)
                footprint = set(evidence.get('axiomFootprint', []))
                c.check(footprint <= ALLOWED_AXIOMS, 'evidence.axioms',
                        'query %r evidence footprint contains disallowed axioms: %s'
                        % (qid, sorted(footprint - ALLOWED_AXIOMS)))
                c.check(set(evidence.get('allowedAxioms', [])) == ALLOWED_AXIOMS,
                        'evidence.allowedAxioms',
                        'query %r evidence allowed-axiom list drift' % qid)
                probe = evidence.get('probe', {})
                c.check(probe.get('path') == PROBE_REL, 'evidence.probePath',
                        'query %r probe path drift' % qid)
                c.check(probe.get('sha256') == sha_file(os.path.join(ROOT, PROBE_REL)),
                        'evidence.probeHash', 'query %r probe source hash drift' % qid)
                decl = probe.get('declaration', '')
                certified_decls.add(decl)
                c.check(decl.startswith(
                    'PhotoLean.RelationAudit.BoundedAudit.R3.'), 'evidence.probeDecl',
                    'query %r probe declaration is outside the expected namespace' % qid)
                short = short_name(decl)
                c.check(re.search(r'\bdef\s+%s\b' % re.escape(short), probe_text)
                        is not None, 'evidence.probeDeclMissing',
                        'query %r probe declaration is not in the probe source' % qid)
                kind_thm = probe.get('kindCheckTheorem', '')
                c.check(re.search(r'\btheorem\s+%s\b' % re.escape(short_name(kind_thm)),
                                  probe_text) is not None,
                        'evidence.probeKindMissing',
                        'query %r probe kind-check theorem is missing' % qid)
                c.check(probe.get('buildCommand', '').startswith(
                    'proofs/scripts/lake env lean '), 'evidence.probeBuild',
                    'query %r probe build command drift' % qid)
                log_rel = probe.get('log', '')
                c.check(log_rel == PROBE_LOG_REL, 'evidence.probeLog',
                        'query %r probe log path drift' % qid)
                axioms = probe_axioms.get(decl)
                c.check(axioms is not None, 'evidence.probeAxiomLog',
                        'query %r probe declaration has no axiom print-out' % qid)
                if axioms is not None:
                    c.check(axioms == footprint, 'evidence.probeAxiomMatch',
                            'query %r probe axiom print-out %r does not match the '
                            'declared footprint %r' % (qid, sorted(axioms), sorted(footprint)))
                    c.check(axioms <= ALLOWED_AXIOMS, 'evidence.probeAxiomDisallowed',
                            'query %r probe certificate has disallowed axioms: %s'
                            % (qid, sorted(axioms - ALLOWED_AXIOMS)))
                theorems = evidence.get('underlyingTheorems', [])
                c.check(isinstance(theorems, list) and len(theorems) >= 1,
                        'evidence.underlying',
                        'query %r probe evidence cites no underlying theorem' % qid)
                for thm in theorems or []:
                    d = thm.get('declaration', '')
                    rel = thm.get('sourceArtifact', '')
                    line = thm.get('sourceLine')
                    c.nonempty(d, 'evidence.underlyingDecl',
                               'query %r underlying theorem has no declaration' % qid)
                    path = os.path.join(ROOT, rel)
                    c.check(os.path.exists(path), 'evidence.underlyingSource',
                            'query %r underlying theorem source is missing' % qid)
                    c.check(isinstance(line, int) and line >= 1,
                            'evidence.underlyingLine',
                            'query %r underlying theorem has no positive source line'
                            % qid)
                    if os.path.exists(path) and isinstance(line, int):
                        text = open(path, encoding='utf-8').read().splitlines()
                        c.check(line <= len(text), 'evidence.underlyingLineRange',
                                'query %r underlying theorem line is outside its source'
                                % qid)
                        if line <= len(text):
                            c.check(short_name(d) in text[line - 1],
                                    'evidence.underlyingLineMatch',
                                    'query %r underlying theorem is not at its declared '
                                    'source line' % qid)
            elif status in {'unresolved', 'notEstablished'}:
                non_certified.append((qid, status, evidence))
                c.check(evidence.get('type') == 'scoped-search', 'evidence.searchType',
                        'query %r status %s requires a scoped-search evidence record'
                        % (qid, status))
                c.nonempty(evidence.get('searchLogRef'), 'evidence.searchRef',
                           'query %r status %s has no search-log reference' % (qid, status))
                c.nonempty(evidence.get('candidateSummary'), 'evidence.candidateSummary',
                           'query %r status %s has no candidate metadata summary'
                           % (qid, status))
            elif status == 'outOfScope':
                c.check(evidence.get('type') == 'jurisdiction', 'evidence.jurisdictionType',
                        'query %r outOfScope requires a jurisdiction evidence record' % qid)
                c.nonempty(evidence.get('jurisdictionRationale'),
                           'evidence.jurisdictionRationale',
                           'query %r outOfScope has no statement-level rationale' % qid)
            elif status == 'refuted':
                c.check(evidence.get('type') == 'refutation-certificate',
                        'evidence.refutationType',
                        'query %r refuted requires a refutation certificate' % qid)
                c.check(evidence.get('kind') == 'refutation', 'evidence.refutationKind',
                        'query %r refuted evidence kind is not refutation' % qid)
                c.nonempty(evidence.get('counterexampleWitness'),
                           'evidence.counterexample',
                           'query %r refuted has no explicit counterexample witness' % qid)

    c.check(certified_decls == set(probe_axioms), 'probe.declarationCoverage',
            'probe axiom declarations %r do not match the certified query declarations %r'
            % (sorted(set(probe_axioms)), sorted(certified_decls)))
    c.check(probe_ref.get('declarationCount') == len(probe_axioms),
            'probe.declarationCount', 'probe reference declaration count drift')
    c.check(probe_ref.get('log') == PROBE_LOG_REL, 'probe.logPath',
            'probe reference log path drift')

    # ---------------------------------------------------------------- search log
    entries = search_log.get('entries', [])
    c.check(search_log.get('artifactKind') == 'bounded-search-log', 'search.kind',
            'search-log artifactKind drift')
    c.check(search_log.get('round') == 'R3', 'search.round', 'search-log round drift')
    c.check(search_log.get('snapshot') == snap.get('id'), 'search.snapshot',
            'search-log snapshot drift')
    entry_ids = [e.get('searchId') for e in entries]
    c.check(len(entry_ids) == len(set(entry_ids)), 'search.duplicate',
            'duplicate search id')
    entry_by_id = {e.get('searchId'): e for e in entries}
    for e in entries:
        sid = e.get('searchId')
        qid = e.get('queryId')
        c.check(qid in query_by_id, 'search.queryMissing',
                'search entry %r points to unknown query %r' % (sid, qid))
        q = query_by_id.get(qid)
        if q is not None:
            c.check(e.get('pairId') == q.get('pairId'), 'search.pairId',
                    'search entry %r pairId drift' % sid)
            c.check(e.get('status') == q.get('outcome', {}).get('status'),
                    'search.status', 'search entry %r status does not match its query' % sid)
            c.check(q.get('outcome', {}).get('evidence', {}).get('searchLogRef') == sid,
                    'search.backref',
                    'query %r does not point back to search entry %r' % (qid, sid))
        c.check(e.get('scope') in screening.get('scopeLibrary', {}), 'search.scope',
                'search entry %r has unknown scope' % sid)
        c.check(e.get('snapshot') == snap.get('id'), 'search.entrySnapshot',
                'search entry %r snapshot drift' % sid)
        stmts = e.get('searchedStatements')
        c.check(isinstance(stmts, list) and len(stmts) >= 1, 'search.searchedStatements',
                'search entry %r has no searched statements' % sid)
        for st in stmts or []:
            c.check(st in inv_by_id, 'search.searchedStatementMissing',
                    'search entry %r cites unknown inventory statement %r' % (sid, st))
        kinds = e.get('searchedKinds')
        c.check(isinstance(kinds, list) and len(kinds) >= 1, 'search.searchedKinds',
                'search entry %r has no searched kinds' % sid)
        c.check(set(kinds or []) <= set(KINDS), 'search.kindVocabulary',
                'search entry %r searches an unknown kind' % sid)
        ctxs = e.get('contextsConsidered')
        c.check(isinstance(ctxs, list) and len(ctxs) >= 1, 'search.contexts',
                'search entry %r has no considered context' % sid)
        deps = e.get('dependenciesConsulted')
        c.check(isinstance(deps, list) and len(deps) >= 1, 'search.dependencies',
                'search entry %r has no consulted dependencies' % sid)
        for dep in deps or []:
            c.nonempty(dep.get('artifact'), 'search.depArtifact',
                       'search entry %r dependency has no artifact' % sid)
            c.nonempty(dep.get('locator'), 'search.depLocator',
                       'search entry %r dependency has no locator' % sid)
            c.nonempty(dep.get('finding'), 'search.depFinding',
                       'search entry %r dependency has no finding' % sid)
            art = dep.get('artifact', '')
            if art.startswith(('PhotoLean/', 'tools/', 'bounded_audit/', 'audit_boundary/',
                               'relation_audit/')):
                c.check(os.path.exists(os.path.join(ROOT, art)), 'search.depMissing',
                        'search entry %r dependency artifact is missing: %s' % (sid, art))
        cmds = e.get('commands')
        c.check(isinstance(cmds, list) and len(cmds) >= 1, 'search.commands',
                'search entry %r has no recorded commands' % sid)
        for cmd in cmds or []:
            c.nonempty(cmd.get('command'), 'search.command',
                       'search entry %r command is empty' % sid)
            c.nonempty(cmd.get('purpose'), 'search.commandPurpose',
                       'search entry %r command has no purpose' % sid)
            c.nonempty(cmd.get('result'), 'search.commandResult',
                       'search entry %r command has no result' % sid)
        strategies = e.get('strategiesAttempted')
        c.check(isinstance(strategies, list) and len(strategies) >= 1,
                'search.strategies', 'search entry %r has no attempted strategies' % sid)
        for st in strategies or []:
            c.nonempty(st.get('strategy'), 'search.strategy',
                       'search entry %r strategy is empty' % sid)
            c.nonempty(st.get('outcome'), 'search.strategyOutcome',
                       'search entry %r strategy has no outcome' % sid)
        candidates = e.get('candidateEvidence')
        c.check(isinstance(candidates, list) and len(candidates) >= 1,
                'search.candidates', 'search entry %r has no candidate evidence' % sid)
        c.nonempty(e.get('remainingGap'), 'search.remainingGap',
                   'search entry %r has no remaining gap' % sid)
        rec = e.get('recomputeCommands')
        c.check(isinstance(rec, list) and len(rec) >= 1, 'search.recompute',
                'search entry %r has no recompute command' % sid)
        c.nonempty(e.get('rationale'), 'search.rationale',
                   'search entry %r has no rationale' % sid)

    for qid, status, evidence in non_certified:
        sid = evidence.get('searchLogRef')
        c.check(sid in entry_by_id, 'search.missing',
                'query %r status %s has no search-log entry %r' % (qid, status, sid))
        if sid in entry_by_id:
            c.check(entry_by_id[sid].get('queryId') == qid, 'search.mismatch',
                    'search entry %r queryId does not match %r' % (sid, qid))
    for e in entries:
        q = query_by_id.get(e.get('queryId'))
        if q is not None:
            c.check(q.get('outcome', {}).get('status') != 'certified',
                    'search.certifiedEntry',
                    'certified query %r has a search-log entry' % e.get('queryId'))

    # ---------------------------------------------------------------- counts
    status_counts = {}
    kind_counts = {}
    for pair in pairs:
        for q in pair.get('queries', []):
            status_counts[q['outcome']['status']] = \
                status_counts.get(q['outcome']['status'], 0) + 1
            kind_counts[q['expectedKind']] = kind_counts.get(q['expectedKind'], 0) + 1
    declared = screening.get('counts', {})
    c.check(declared.get('pairs') == len(pairs), 'counts.pairs', 'pair count drift')
    c.check(declared.get('queries') == len(all_query_ids), 'counts.queries',
            'query count drift')
    c.check(declared.get('byStatus') == status_counts, 'counts.byStatus',
            'status counts drift: %r != %r' % (declared.get('byStatus'), status_counts))
    c.check(declared.get('byExpectedKind') == kind_counts, 'counts.byExpectedKind',
            'kind counts drift: %r != %r' % (declared.get('byExpectedKind'), kind_counts))
    for status in STATUSES:
        c.check(declared.get(status) == status_counts.get(status, 0),
                'counts.%s' % status, 'declared %s count drift' % status)
    c.check(search_log.get('counts', {}).get('entries') == len(entries),
            'counts.searchEntries', 'search-log entry count drift')
    c.check(search_ref.get('entryCount') == len(entries), 'searchLogReference.entryCount',
            'search-log reference entry count drift')

    # ---------------------------------------------------------------- forbidden tokens
    forbidden = re.compile(r'sorry|admit|^[ \t]*(private[ \t]+|protected[ \t]+)?'
                           r'(axiom|constant)([ \t]|$)', re.M)
    c.check(forbidden.search(probe_text) is None, 'probe.forbiddenToken',
            'probe source contains a forbidden token')

    # ---------------------------------------------------------------- non-claims
    c.check(isinstance(screening.get('nonClaims'), list)
            and len(screening.get('nonClaims')) >= 1, 'nonClaims.missing',
            'screening package has no non-claims statement')
    c.check(isinstance(coverage.get('nonClaims'), list)
            and len(coverage.get('nonClaims')) >= 1, 'coverage.nonClaims',
            'coverage ledger has no non-claims statement')

    # ---------------------------------------------------------------- exclusions
    # Fail closed on the exclusion list itself: it must be exactly the seven enumerated
    # current-ledger freshness checks, each recorded exactly once. Any extra exclusion
    # (or a missing one) fails here, so this derived validator cannot silently weaken
    # the accepted R3 content gate.
    excluded_codes = [code for code, _message in c.excluded]
    c.check(len(excluded_codes) == len(EXCLUDED_CHECKS)
            and set(excluded_codes) == EXCLUDED_CHECK_SET,
            'validator.exclusions',
            'excluded checks are %r, expected exactly %r'
            % (sorted(excluded_codes), EXCLUDED_CHECKS))

    return c.summary()


if __name__ == '__main__':
    sys.exit(main())
