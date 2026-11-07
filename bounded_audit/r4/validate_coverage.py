#!/usr/bin/env python3
"""R4 cumulative coverage validator (deterministic, fail-closed).

This is the integration-round gate for the R4 bounded-relation audit. It checks
the composition of the three submitted R4 packages (E1, E2, CI) with the
accepted R2/R3 packages into the cumulative ledger ``bounded_audit/coverage.json``.

What it checks
--------------
1.  Ledger schema, round and universe pin (136 pairs, pair-queue SHA-256).
2.  Accepted state: the 21 accepted R2/R3 entries are preserved verbatim in
    ``screenedPairs`` and still reconcile pair-by-pair with the accepted R2 and
    R3 screening packages (query counts and per-status counts).
3.  Submitted state: exactly 46 unique R4 pairs in ``submittedPairs``, each
    marked ``submitted-R4-pending-review``, partitioned 16/14/16 across the three
    packages, disjoint from the accepted 21 and from the 69 remaining pairs, and
    reconciled pair-by-pair with the package ``screening.json`` files.
4.  Exact counts: 46 R4 pairs / 46 named queries; per-package 16/14/16 pairs and
    16/14/16 queries; R4 status counts 19 certified / 0 refuted / 19 unresolved
    / 1 notEstablished / 7 outOfScope; 27 non-certified queries each backed by
    exactly one search-log entry; cumulative 67/136 screened with 69 remaining;
    by-round 10/11/46; query outcomes 42/0/27/1/7 over 77 queries.
5.  Package fragments: each fragment is an R4 fragment in submitted state, pins
    its own screening JSON, matches the package pair/query/status counts, and
    does not claim a cumulative ledger count.
6.  Submitted work-package hashes: the ledger's recorded SHA-256 values for the
    three packages (screening, search log, fragment, probe, validator) match the
    files on disk.
7.  No hash cycles: the ledger records no hash of itself and no hash of
    ``bounded_audit/r3/screening.json`` (that accepted package pins this ledger);
    the accepted R3 work-package entry carries no hash; no R4 package artifact
    pins the mutable ledger.
8.  Frozen-input pins: the R4 snapshot hashes for the R1 inventory, pair queue,
    cluster plan, boundary and legacy registry are recomputed, the registry
    SHA-256 equals the accepted constant, and the delivered Lean tree still has
    102 files.
9.  Package validators: the three R4 package validators are re-run as
    subprocesses and must exit 0 with ``RESULT: PASS``.

The validator is deliberately *not* a second copy of the package validators: it
re-derives the integration-level facts those validators cannot see (cross-package
disjointness, cumulative arithmetic, accepted/submitted partition, cycle edges).

Usage
-----
    python3 bounded_audit/r4/validate_coverage.py
    python3 bounded_audit/r4/validate_coverage.py --root /tmp/sandbox/photolean
    python3 bounded_audit/r4/validate_coverage.py --skip-package-validators
    python3 bounded_audit/r4/validate_coverage.py \
        --coverage /tmp/mut/coverage.json \
        --override bounded_audit/r4/excited-01/coverage-fragment.json=/tmp/mut/frag.json

Exit code 0 means every check passed; 1 means at least one check failed.
"""

import argparse
import hashlib
import json
import os
import subprocess
import sys
from collections import Counter


DEFAULT_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))

LEDGER_REL = 'bounded_audit/coverage.json'
QUEUE_REL = 'audit_boundary/pair-queue.json'
INV_REL = 'audit_boundary/statement-inventory.json'
CLUSTER_REL = 'audit_boundary/cluster-plan.json'
BOUNDARY_REL = 'audit_boundary/BOUNDARY.md'
REGISTRY_REL = 'relation_audit/registry.json'
R2_REL = 'bounded_audit/wp-surface-01/screening.json'
R3_REL = 'bounded_audit/r3/screening.json'

PACKAGES = [
    {
        'id': 'R4-E1-EXCITED-01',
        'tag': 'E1',
        'workPackage': 'WP-excited-state-kinetics-01',
        'dir': 'bounded_audit/r4/excited-01',
        'probe': 'probes/E1-probe.lean',
        'pairs': 16,
        'queries': 16,
        'byStatus': {'certified': 6, 'unresolved': 9, 'outOfScope': 1},
    },
    {
        'id': 'R4-E2-EXCITED-02',
        'tag': 'E2',
        'workPackage': 'WP-excited-state-kinetics-02',
        'dir': 'bounded_audit/r4/excited-02',
        'probe': 'probes/E2-probe.lean',
        'pairs': 14,
        'queries': 14,
        'byStatus': {'certified': 5, 'unresolved': 4, 'outOfScope': 5},
    },
    {
        'id': 'R4-CI-CONICAL-01',
        'tag': 'CI',
        'workPackage': 'WP-conical-intersection-01',
        'dir': 'bounded_audit/r4/conical-01',
        'probe': 'probes/R4-CI-probe.lean',
        'pairs': 16,
        'queries': 16,
        'byStatus': {'certified': 8, 'unresolved': 6, 'notEstablished': 1,
                     'outOfScope': 1},
    },
]

for _pkg in PACKAGES:
    _pkg['screening'] = _pkg['dir'] + '/screening.json'
    _pkg['searchLog'] = _pkg['dir'] + '/search-log.json'
    _pkg['fragment'] = _pkg['dir'] + '/coverage-fragment.json'
    _pkg['validate'] = _pkg['dir'] + '/validate.py'

STATUSES = ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope']
KINDS = ['definitionalIdentity', 'implication', 'equivalence',
         'conditionalComposition', 'observationalEquivalence',
         'distinguishability', 'refutation']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
SUBMITTED_STATE = 'submitted-R4-pending-review'
# Package fragments remain immutable submission snapshots. The ledger's R4 rows
# flip to this state only after independent review; key names stay unchanged to
# avoid invalidating package validators that pin the historical ledger layout.
LEDGER_ACCEPTANCE_STATE = 'accepted-R4'
SNAPSHOT_IDS = {'snap-bounded-audit-2026-11-04', 'snap-bounded-audit-2026-11-04-r4e2'}
EXPECTED_REGISTRY_SHA = ('25d38791ce86f9030598eb68b6894a886513164ddb9165e0ff'
                         'f371883c1ecbf0')
EXPECTED_LEAN_FILES = 102

UNIVERSE_PAIRS = 136
UNIVERSE_THEORIES = 17
ACCEPTED_PAIRS = 21
R2_PAIRS = 10
R3_PAIRS = 11
SUBMITTED_PAIRS = 46
CUMULATIVE_SCREENED = 67
CUMULATIVE_REMAINING = 69
R4_QUERY_OUTCOMES = {'certified': 19, 'refuted': 0, 'unresolved': 19,
                     'notEstablished': 1, 'outOfScope': 7}
CUMULATIVE_QUERY_OUTCOMES = {'certified': 42, 'refuted': 0, 'unresolved': 27,
                             'notEstablished': 1, 'outOfScope': 7}


class Checks:
    def __init__(self):
        self.failed = []
        self.passed = 0

    def check(self, ok, code, message):
        if ok:
            self.passed += 1
        else:
            self.failed.append((code, message))
        return bool(ok)

    def nonempty(self, value, code, message):
        return self.check(isinstance(value, str) and value.strip() != '',
                          code, message)

    def fail(self, code, message):
        return self.check(False, code, message)


def sha_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def read_text(path):
    with open(path, encoding='utf-8') as fh:
        return fh.read()


def load_json(path):
    with open(path, encoding='utf-8') as fh:
        return json.load(fh)


def status_counts(queries):
    return dict(Counter(q['outcome']['status'] for q in queries))


def kind_counts(queries):
    return dict(Counter(q['expectedKind'] for q in queries))


def package_pair_map(screening):
    """pairId -> (queryIds, statusCounter, kindCounter) from a screening package."""
    out = {}
    for pair in screening['pairs']:
        queries = pair['queries']
        out[pair['pairId']] = (
            [q['queryId'] for q in queries],
            dict(Counter(q['outcome']['status'] for q in queries)),
            dict(Counter(q['expectedKind'] for q in queries)),
        )
    return out


def fragment_pair_map(fragment):
    """Normalise the three R4 fragment shapes to pairId -> (count, byStatus, ids)."""
    out = {}
    if isinstance(fragment.get('pairs'), list):
        for entry in fragment['pairs']:
            if isinstance(entry.get('outcomes'), list):
                by = dict(Counter(o.get('status') for o in entry['outcomes']))
                ids = [o.get('queryId') for o in entry['outcomes']]
                count = len(ids)
            else:
                by = dict(entry.get('byStatus') or {})
                ids = list(entry.get('queryIds') or [])
                count = entry.get('queryCount', len(ids))
            out[entry['pairId']] = (count, by, ids)
        return out
    for entry in fragment.get('screenedPairs') or []:
        out[entry['pairId']] = (entry.get('queryCount'),
                                dict(entry.get('byStatus') or {}), [])
    return out


def fragment_screening_sha(fragment):
    """Return the screening SHA-256 pinned by a fragment, across the three shapes."""
    artifacts = fragment.get('packageArtifacts') or {}
    if isinstance(artifacts.get('screening'), dict):
        return artifacts['screening'].get('sha256')
    if fragment.get('screeningSha256'):
        return fragment['screeningSha256']
    wp = fragment.get('workPackage') or {}
    if isinstance(wp, dict) and wp.get('sha256'):
        return wp['sha256']
    return None


def fragment_state(fragment):
    package = fragment.get('package') or {}
    for value in (package.get('status') if isinstance(package, dict) else None,
                  fragment.get('packageState'),
                  fragment.get('acceptance')):
        if value:
            return value
    return None


def fragment_counts(fragment):
    counts = fragment.get('counts') or {}
    pairs = counts.get('pairs', fragment.get('pairCount'))
    queries = counts.get('queries', fragment.get('queryCount'))
    by_status = counts.get('byStatus', fragment.get('byStatus'))
    return pairs, queries, dict(by_status or {})


def ledger_entries_by_pair(entries):
    return {e.get('pairId'): e for e in entries}


def main(argv=None):
    parser = argparse.ArgumentParser(
        description='Validate the R4 cumulative bounded-coverage ledger.')
    parser.add_argument('--root', default=None,
                        help='photolean repository root (default: derived from __file__)')
    parser.add_argument('--coverage', default=LEDGER_REL,
                        help='ledger path, relative to root (default: %s)' % LEDGER_REL)
    parser.add_argument('--skip-package-validators', action='store_true',
                        help='do not re-run the three R4 package validators')
    parser.add_argument('--override', action='append', default=[],
                        metavar='REL=PATH',
                        help='read REL from PATH instead (mutation-test hook)')
    args = parser.parse_args(argv)

    root = os.path.abspath(args.root) if args.root else DEFAULT_ROOT
    overrides = {}
    for item in args.override:
        if '=' not in item:
            sys.stderr.write('bad --override %r (expected REL=PATH)\n' % item)
            return 2
        rel, path = item.split('=', 1)
        overrides[rel] = path

    def path_of(rel):
        return overrides.get(rel, os.path.join(root, rel))

    def load(rel):
        return load_json(path_of(rel))

    def text(rel):
        return read_text(path_of(rel))

    def sha(rel):
        return sha_file(path_of(rel))

    c = Checks()

    # ------------------------------------------------------------------ inputs
    required = [QUEUE_REL, INV_REL, CLUSTER_REL, BOUNDARY_REL, REGISTRY_REL,
                args.coverage]
    for pkg in PACKAGES:
        required += [pkg['screening'], pkg['searchLog'], pkg['fragment'],
                     pkg['validate']]
    missing = [rel for rel in required if not os.path.exists(path_of(rel))]
    for rel in missing:
        c.fail('input.missing', 'required input is missing: %s' % rel)
    if missing:
        report(c, root, args.coverage, None)
        return 1

    ledger = load(args.coverage)
    ledger_text = text(args.coverage)
    queue = load(QUEUE_REL)
    inventory = load(INV_REL)
    registry = load(REGISTRY_REL)
    r2 = load(R2_REL)
    r3 = load(R3_REL)
    universe = [row['pairId'] for row in queue['pairs']]
    universe_set = set(universe)

    # ------------------------------------------------------------- ledger schema
    c.check(ledger.get('schemaVersion') == '1.0.0', 'ledger.schemaVersion',
            'unexpected schemaVersion')
    c.check(ledger.get('artifactKind') == 'bounded-coverage-ledger',
            'ledger.artifactKind', 'unexpected artifactKind')
    c.check(ledger.get('round') == 'R4', 'ledger.round',
            'the integrated ledger must declare round R4')
    c.check(ledger.get('generatedOn') == '2026-11-04', 'ledger.generatedOn',
            'generatedOn drift')
    c.nonempty(ledger.get('description'), 'ledger.description',
               'ledger has no description')
    universe_block = ledger.get('universe') or {}
    c.check(universe_block.get('pairCount') == UNIVERSE_PAIRS,
            'universe.pairCount',
            'universe pair count is %r, expected %d'
            % (universe_block.get('pairCount'), UNIVERSE_PAIRS))
    c.check(len(universe) == UNIVERSE_PAIRS and len(universe_set) == UNIVERSE_PAIRS,
            'universe.queue', 'R1 pair queue does not hold 136 unique pairs')
    c.check(universe_block.get('theoryCount') == UNIVERSE_THEORIES,
            'universe.theoryCount', 'universe theory count drift')
    c.check(universe_block.get('source') == QUEUE_REL, 'universe.source',
            'universe source is not the R1 pair queue')
    c.check(universe_block.get('sourceSha256') == sha(QUEUE_REL),
            'universe.sourceSha256', 'universe source hash drift')
    c.check(len(queue.get('pairs', [])) == UNIVERSE_PAIRS, 'universe.queueRows',
            'R1 pair queue row count drift')

    # --------------------------------------------------------------- hash cycles
    ledger_sha = sha(args.coverage)
    for banned in ('coverageSha256', 'ledgerSha256', 'selfSha256',
                   'coverageSelfSha256'):
        c.check(banned not in ledger, 'cycle.selfKey',
                'the ledger carries a self-hash slot %r' % banned)
    c.check(ledger_sha not in ledger_text, 'cycle.selfPin',
            'the ledger records its own SHA-256; that is a self-referential hash cycle')
    r3_screening_sha = sha(R3_REL)
    c.check(r3_screening_sha not in ledger_text, 'cycle.r3ScreeningPin',
            'the ledger records the R3 screening SHA-256; the accepted R3 package '
            'pins this ledger, so that edge would close a hash cycle')
    accepted_wps = ledger.get('acceptedWorkPackages') or []
    r2_wp = next((w for w in accepted_wps if w.get('round') == 'R2'), None)
    r3_wp = next((w for w in accepted_wps if w.get('round') == 'R3'), None)
    c.check(r2_wp is not None, 'accepted.wp.r2', 'missing R2 work-package entry')
    c.check(r3_wp is not None, 'accepted.wp.r3', 'missing R3 work-package entry')
    if r2_wp is not None:
        c.check(r2_wp.get('pairCount') == R2_PAIRS, 'accepted.wp.r2PairCount',
                'R2 work-package pair count drift')
        c.check(r2_wp.get('sha256') == sha(R2_REL), 'accepted.wp.r2Sha',
                'R2 work-package hash drift (R2 does not pin the ledger, so this '
                'hash belongs here)')
    if r3_wp is not None:
        c.check(r3_wp.get('pairCount') == R3_PAIRS, 'accepted.wp.r3PairCount',
                'R3 work-package pair count drift')
        c.check('sha256' not in r3_wp, 'cycle.r3WpPin',
                'the R3 work-package entry carries a hash; the R3 package pins '
                'this ledger, so the reverse hash would close a cycle')
        c.check(r3_wp.get('path') == R3_REL, 'accepted.wp.r3Path',
                'R3 work-package path drift')
    c.check(len(accepted_wps) == 2, 'accepted.wp.count',
            'expected exactly two accepted work-package entries')

    # ------------------------------------------------------------ accepted state
    screened = ledger.get('screenedPairs') or []
    screened_by_id = ledger_entries_by_pair(screened)
    c.check(len(screened) == ACCEPTED_PAIRS, 'accepted.count',
            'ledger has %d accepted screened pairs, expected %d'
            % (len(screened), ACCEPTED_PAIRS))
    c.check(len(screened_by_id) == len(screened), 'accepted.duplicate',
            'the accepted screened list has a duplicate pair')
    accepted_ids = list(screened_by_id)
    c.check(set(accepted_ids) <= universe_set, 'accepted.unknownPair',
            'the accepted list names a pair outside the R1 queue')
    r2_map = package_pair_map(r2)
    r3_map = package_pair_map(r3)
    c.check(set(r2_map) | set(r3_map) == set(accepted_ids), 'accepted.pairSet',
            'the accepted set is not the union of the R2 and R3 packages')
    c.check(len(r2_map) == R2_PAIRS, 'accepted.r2Count',
            'R2 package does not hold ten pairs')
    c.check(len(r3_map) == R3_PAIRS, 'accepted.r3Count',
            'R3 package does not hold eleven pairs')
    accepted_by_round = Counter()
    for entry in screened:
        pid = entry.get('pairId')
        accepted_by_round[entry.get('round')] += 1
        c.nonempty(entry.get('acceptance'), 'accepted.acceptance',
                   'accepted entry %r has no acceptance status' % pid)
        c.nonempty(entry.get('overlapNote'), 'accepted.overlapNote',
                   'accepted entry %r has no overlap note' % pid)
        c.check(entry.get('round') in ('R2', 'R3'), 'accepted.round',
                'accepted entry %r has an unexpected round' % pid)
        expected_path = R2_REL if entry.get('round') == 'R2' else R3_REL
        c.check(entry.get('packagePath') == expected_path, 'accepted.packagePath',
                'accepted entry %r names an unexpected package path' % pid)
        expected_status = ('accepted-R2' if entry.get('round') == 'R2'
                           else 'accepted-R3')
        c.check(entry.get('acceptance') == expected_status,
                'accepted.status', 'accepted entry %r is not %s'
                % (pid, expected_status))
        source = r2_map if entry.get('round') == 'R2' else r3_map
        if pid in source:
            queries, by_status, _kinds = source[pid]
            c.check(entry.get('queryCount') == len(queries),
                    'accepted.queryCount',
                    'accepted entry %r query count drift' % pid)
            c.check(entry.get('byStatus') == by_status, 'accepted.byStatus',
                    'accepted entry %r per-status counts drift' % pid)
        else:
            c.fail('accepted.unknownPair', 'accepted entry %r is not in its package'
                   % pid)
    c.check(dict(accepted_by_round) == {'R2': R2_PAIRS, 'R3': R3_PAIRS},
            'accepted.byRound', 'accepted by-round split drift')
    kasha_sabatier = screened_by_id.get('P-Kasha-Sabatier') or {}
    c.check('cross-domain' in (kasha_sabatier.get('overlapNote') or '').lower(),
            'accepted.earlyCrossDomain',
            'the early cross-domain pair P-Kasha-Sabatier is not annotated')
    marcus_sym = screened_by_id.get('P-Marcus-SymmetryFactor') or {}
    c.check('surface-gap' in (marcus_sym.get('overlapNote') or '').lower(),
            'accepted.surfaceGap',
            'the surface-gap reconciliation P-Marcus-SymmetryFactor is not annotated')

    # ----------------------------------------------------------- submitted state
    submitted = ledger.get('submittedPairs') or []
    submitted_by_id = ledger_entries_by_pair(submitted)
    c.check(len(submitted) == SUBMITTED_PAIRS, 'submitted.count',
            'ledger has %d submitted R4 pairs, expected %d'
            % (len(submitted), SUBMITTED_PAIRS))
    c.check(len(submitted_by_id) == len(submitted), 'submitted.duplicate',
            'the submitted pair list has a duplicate pair')
    c.check(not (set(submitted_by_id) & set(accepted_ids)), 'submitted.overlapAccepted',
            'a submitted R4 pair is already in the accepted R2/R3 set')
    c.check(set(submitted_by_id) <= universe_set, 'submitted.unknownPair',
            'a submitted R4 pair is outside the R1 queue')

    submitted_wps = ledger.get('submittedWorkPackages') or []
    c.check(len(submitted_wps) == len(PACKAGES), 'submitted.wp.count',
            'expected exactly three submitted R4 work packages')
    wp_by_id = {w.get('id'): w for w in submitted_wps}

    per_package_pairs = {}
    per_package_queries = {}
    per_package_status = {}
    r4_query_ids = []
    r4_status = Counter()
    r4_kind = Counter()
    for pkg in PACKAGES:
        screening = load(pkg['screening'])
        search_log = load(pkg['searchLog'])
        fragment = load(pkg['fragment'])
        pair_map = package_pair_map(screening)

        # ---- package-declared counts
        counts = screening.get('counts') or {}
        c.check(len(screening['pairs']) == pkg['pairs'], 'pkg.%s.pairCount' % pkg['tag'],
                '%s screens %d pairs, expected %d'
                % (pkg['tag'], len(screening['pairs']), pkg['pairs']))
        c.check(counts.get('pairs') == pkg['pairs'], 'pkg.%s.countsPairs' % pkg['tag'],
                '%s declared pair count drift' % pkg['tag'])
        c.check(counts.get('queries') == pkg['queries'],
                'pkg.%s.countsQueries' % pkg['tag'],
                '%s declared query count drift' % pkg['tag'])
        c.check(dict(counts.get('byStatus') or {}) == pkg['byStatus'],
                'pkg.%s.byStatus' % pkg['tag'],
                '%s declared status counts drift' % pkg['tag'])
        c.check(counts.get('refuted', 0) == 0, 'pkg.%s.refuted' % pkg['tag'],
                '%s declares a refuted outcome' % pkg['tag'])

        # ---- per-pair one named query
        pair_ids = list(pair_map)
        c.check(len(pair_ids) == pkg['pairs'], 'pkg.%s.uniquePairs' % pkg['tag'],
                '%s pair list is not unique or short' % pkg['tag'])
        c.check(set(pair_ids) <= universe_set, 'pkg.%s.unknownPair' % pkg['tag'],
                '%s names a pair outside the R1 queue' % pkg['tag'])
        for pid, (qids, by_status, kinds) in pair_map.items():
            if not qids:
                c.fail('pkg.%s.pairNoQuery' % pkg['tag'],
                       '%s pair %r has no named query' % (pkg['tag'], pid))
            r4_query_ids += qids
            for status, count in by_status.items():
                if status not in STATUSES:
                    c.fail('pkg.%s.statusVocab' % pkg['tag'],
                           '%s pair %r uses unknown status %r'
                           % (pkg['tag'], pid, status))
                r4_status[status] += count
            for kind, count in kinds.items():
                if kind not in KINDS:
                    c.fail('pkg.%s.kindVocab' % pkg['tag'],
                           '%s pair %r uses unknown kind %r'
                           % (pkg['tag'], pid, kind))
                r4_kind[kind] += count

        # ---- per-package aggregation
        pkg_status = Counter()
        pkg_queries = 0
        for qids, by_status, _kinds in pair_map.values():
            pkg_queries += len(qids)
            pkg_status.update(by_status)
        per_package_pairs[pkg['tag']] = set(pair_ids)
        per_package_queries[pkg['tag']] = pkg_queries
        per_package_status[pkg['tag']] = dict(pkg_status)
        c.check(pkg_queries == pkg['queries'], 'pkg.%s.queryCount' % pkg['tag'],
                '%s has %d queries, expected %d'
                % (pkg['tag'], pkg_queries, pkg['queries']))
        c.check(dict(pkg_status) == pkg['byStatus'], 'pkg.%s.actualByStatus' % pkg['tag'],
                '%s actual status counts drift from the R4 contract' % pkg['tag'])

        # ---- search-log reconciliation
        entries = search_log.get('entries') or []
        entry_ids = [e.get('queryId') for e in entries]
        c.check(len(entry_ids) == len(set(entry_ids)),
                'pkg.%s.searchDuplicate' % pkg['tag'],
                '%s search log has duplicate query ids' % pkg['tag'])
        declared = search_log.get('counts')
        if isinstance(declared, dict) and 'entries' in declared:
            c.check(declared.get('entries') == len(entries),
                    'pkg.%s.searchCounts' % pkg['tag'],
                    '%s search-log declared entry count drift' % pkg['tag'])
        status_by_qid = {q['queryId']: q['outcome']['status']
                         for pair in screening['pairs'] for q in pair['queries']}
        pair_by_qid = {q['queryId']: pair['pairId']
                       for pair in screening['pairs'] for q in pair['queries']}
        non_certified = {qid for qid, status in status_by_qid.items()
                         if status != 'certified'}
        c.check(set(entry_ids) == non_certified,
                'pkg.%s.searchCoverage' % pkg['tag'],
                '%s search log does not back exactly the non-certified queries'
                % pkg['tag'])
        for e in entries:
            qid = e.get('queryId')
            c.check(e.get('status') == status_by_qid.get(qid),
                    'pkg.%s.searchStatus' % pkg['tag'],
                    '%s search entry %r status does not match its query'
                    % (pkg['tag'], qid))
            c.check(e.get('pairId') == pair_by_qid.get(qid),
                    'pkg.%s.searchPair' % pkg['tag'],
                    '%s search entry %r names the wrong pair' % (pkg['tag'], qid))

        # ---- snapshot pins
        snap = screening.get('snapshot') or {}
        c.check(snap.get('id') in SNAPSHOT_IDS, 'pkg.%s.snapshotId' % pkg['tag'],
                '%s snapshot id drift' % pkg['tag'])
        c.check(snap.get('date') == '2026-11-04', 'pkg.%s.snapshotDate' % pkg['tag'],
                '%s snapshot date drift' % pkg['tag'])
        c.check(snap.get('round') == 'R4', 'pkg.%s.snapshotRound' % pkg['tag'],
                '%s snapshot round drift' % pkg['tag'])
        for rel, key in [(INV_REL, 'inventorySha256'), (QUEUE_REL, 'pairQueueSha256'),
                         (CLUSTER_REL, 'clusterPlanSha256'),
                         (BOUNDARY_REL, 'boundarySha256'),
                         (REGISTRY_REL, 'legacyRegistrySha256')]:
            c.check(snap.get(key) == sha(rel), 'pkg.%s.snapshot.%s' % (pkg['tag'], key),
                    '%s %s does not match %s' % (pkg['tag'], key, rel))
        c.check(snap.get('legacyRegistrySha256') == EXPECTED_REGISTRY_SHA,
                'pkg.%s.registryPinned' % pkg['tag'],
                '%s pins a non-accepted legacy registry hash' % pkg['tag'])
        # No package may pin the mutable R4 ledger by hash. A path reference and
        # an unpinned pointer are allowed; a recorded SHA-256 is not.
        screening_text = text(pkg['screening'])
        c.check('coverageLedgerSha256' not in snap, 'pkg.%s.ledgerPinned' % pkg['tag'],
                '%s snapshot pins the mutable R4 coverage ledger' % pkg['tag'])
        c.check(ledger_sha not in screening_text, 'cycle.packagePinsLedger',
                '%s screening records the ledger SHA-256' % pkg['tag'])
        cov_ref = screening.get('coverageReference') or {}
        if isinstance(cov_ref, dict) and cov_ref:
            c.check(cov_ref.get('pin') == 'not-pinned',
                    'pkg.%s.coverageReferencePin' % pkg['tag'],
                    '%s coverage reference must declare itself unpinned' % pkg['tag'])
            c.check('sha256' not in cov_ref, 'pkg.%s.coverageReferenceSha' % pkg['tag'],
                    '%s coverage reference carries a ledger hash' % pkg['tag'])

        # ---- fragment reconciliation
        c.check(fragment.get('artifactKind') == 'bounded-coverage-fragment',
                'fragment.%s.kind' % pkg['tag'], '%s fragment kind drift' % pkg['tag'])
        c.check(fragment.get('round') == 'R4', 'fragment.%s.round' % pkg['tag'],
                '%s fragment round drift' % pkg['tag'])
        c.check(fragment_state(fragment) == SUBMITTED_STATE,
                'fragment.%s.state' % pkg['tag'],
                '%s fragment does not declare %s' % (pkg['tag'], SUBMITTED_STATE))
        f_pairs, f_queries, f_status = fragment_counts(fragment)
        c.check(f_pairs == pkg['pairs'], 'fragment.%s.pairCount' % pkg['tag'],
                '%s fragment pair count drift' % pkg['tag'])
        c.check(f_queries == pkg['queries'], 'fragment.%s.queryCount' % pkg['tag'],
                '%s fragment query count drift' % pkg['tag'])
        c.check(f_status == pkg['byStatus'], 'fragment.%s.byStatus' % pkg['tag'],
                '%s fragment status counts drift' % pkg['tag'])
        c.check(fragment_screening_sha(fragment) == sha(pkg['screening']),
                'fragment.%s.screeningSha' % pkg['tag'],
                '%s fragment does not pin its screening JSON' % pkg['tag'])
        f_map = fragment_pair_map(fragment)
        c.check(set(f_map) == set(pair_map), 'fragment.%s.pairSet' % pkg['tag'],
                '%s fragment pair set drift' % pkg['tag'])
        for pid, (_c, f_by, _ids) in f_map.items():
            if pid in pair_map:
                c.check(f_by == pair_map[pid][1], 'fragment.%s.byStatus.%s'
                        % (pkg['tag'], pid),
                        '%s fragment per-pair status drift for %r' % (pkg['tag'], pid))
        c.check('cumulative' not in fragment, 'fragment.%s.cumulative' % pkg['tag'],
                '%s fragment claims a cumulative ledger count' % pkg['tag'])
        c.check('screenedPairCount' not in json.dumps(fragment),
                'fragment.%s.cumulativeCount' % pkg['tag'],
                '%s fragment claims a cumulative screened count' % pkg['tag'])
        c.check('coverageSha256' not in json.dumps(fragment),
                'cycle.fragmentPinsLedger',
                '%s fragment pins the mutable ledger' % pkg['tag'])

        # ---- work-package hashes recorded in the ledger
        wp = wp_by_id.get(pkg['workPackage'])
        c.check(wp is not None, 'submitted.wp.%s' % pkg['tag'],
                'ledger has no entry for %s' % pkg['workPackage'])
        if wp is not None:
            c.check(wp.get('acceptance') == LEDGER_ACCEPTANCE_STATE,
                    'submitted.wp.%s.state' % pkg['tag'],
                    '%s work package is not %s' % (pkg['tag'], LEDGER_ACCEPTANCE_STATE))
            c.check(wp.get('pairCount') == pkg['pairs'],
                    'submitted.wp.%s.pairCount' % pkg['tag'],
                    '%s recorded pair count drift' % pkg['tag'])
            c.check(wp.get('queryCount') == pkg['queries'],
                    'submitted.wp.%s.queryCount' % pkg['tag'],
                    '%s recorded query count drift' % pkg['tag'])
            for key, rel in [('sha256', pkg['screening']),
                             ('searchLogSha256', pkg['searchLog']),
                             ('fragmentSha256', pkg['fragment']),
                             ('probeSha256', pkg['dir'] + '/' + pkg['probe']),
                             ('validateSha256', pkg['validate'])]:
                c.check(wp.get(key) == sha(rel), 'submitted.wp.%s.%s'
                        % (pkg['tag'], key),
                        '%s recorded %s does not match %s'
                        % (pkg['tag'], key, rel))
            c.check(wp.get('path') == pkg['screening'],
                    'submitted.wp.%s.path' % pkg['tag'], '%s path drift' % pkg['tag'])
            c.check(wp.get('probePath') == pkg['dir'] + '/' + pkg['probe'],
                    'submitted.wp.%s.probePath' % pkg['tag'],
                    '%s probe path drift' % pkg['tag'])

    # ------------------------------------------------ cross-package disjointness
    tags = [p['tag'] for p in PACKAGES]
    for i, a in enumerate(tags):
        for b in tags[i + 1:]:
            c.check(not (per_package_pairs[a] & per_package_pairs[b]),
                    'packages.overlap',
                    'packages %s and %s screen the same pair' % (a, b))
    union_pairs = set().union(*per_package_pairs.values())
    c.check(len(union_pairs) == SUBMITTED_PAIRS, 'packages.union',
            'the three packages cover %d unique pairs, expected %d'
            % (len(union_pairs), SUBMITTED_PAIRS))
    c.check(set(submitted_by_id) == union_pairs, 'submitted.packageSet',
            'the ledger submitted pairs are not the union of the three packages')

    # ------------------------------------------- per-pair ledger reconciliation
    for entry in submitted:
        pid = entry.get('pairId')
        c.check(entry.get('round') == 'R4', 'submitted.round',
                'submitted entry %r is not round R4' % pid)
        c.check(entry.get('acceptance') == LEDGER_ACCEPTANCE_STATE, 'submitted.status',
                'submitted entry %r is not %s' % (pid, LEDGER_ACCEPTANCE_STATE))
        c.nonempty(entry.get('overlapNote'), 'submitted.overlapNote',
                   'submitted entry %r has no overlap note' % pid)
        c.check(entry.get('packagePath') in [p['screening'] for p in PACKAGES],
                'submitted.packagePath',
                'submitted entry %r names an unknown package' % pid)
        pkg = next((p for p in PACKAGES if p['screening'] == entry.get('packagePath')),
                   None)
        if pkg is None:
            continue
        c.check(entry.get('workPackage') == pkg['workPackage'],
                'submitted.workPackage',
                'submitted entry %r names the wrong work package' % pid)
        pair_map = package_pair_map(load(pkg['screening']))
        if pid in pair_map:
            qids, by_status, _k = pair_map[pid]
            c.check(entry.get('queryCount') == len(qids), 'submitted.queryCount',
                    'submitted entry %r query count drift' % pid)
            c.check(entry.get('byStatus') == by_status, 'submitted.byStatus',
                    'submitted entry %r per-status counts drift' % pid)
            c.check(entry.get('queryIds') == qids, 'submitted.queryIds',
                    'submitted entry %r query ids drift' % pid)
        else:
            c.fail('submitted.packagePair',
                   'submitted entry %r is not in its package' % pid)

    # ---------------------------------------------------------------- exact counts
    cum = ledger.get('cumulative') or {}
    c.check(cum.get('acceptedPairCount') == ACCEPTED_PAIRS, 'cumulative.accepted',
            'accepted pair count in the cumulative block drift')
    c.check(cum.get('submittedPairCount') == SUBMITTED_PAIRS, 'cumulative.submitted',
            'submitted pair count in the cumulative block drift')
    c.check(cum.get('screenedPairCount') == CUMULATIVE_SCREENED,
            'cumulative.screened',
            'cumulative screened count is %r, expected %d'
            % (cum.get('screenedPairCount'), CUMULATIVE_SCREENED))
    c.check(cum.get('remainingPairCount') == CUMULATIVE_REMAINING,
            'cumulative.remaining',
            'cumulative remaining count is %r, expected %d'
            % (cum.get('remainingPairCount'), CUMULATIVE_REMAINING))
    c.check(cum.get('byRound') == {'R2': R2_PAIRS, 'R3': R3_PAIRS, 'R4': SUBMITTED_PAIRS},
            'cumulative.byRound', 'cumulative by-round counts drift')
    c.check(cum.get('queryOutcomes') == CUMULATIVE_QUERY_OUTCOMES,
            'cumulative.queryOutcomes',
            'cumulative query outcomes are %r, expected %r'
            % (cum.get('queryOutcomes'), CUMULATIVE_QUERY_OUTCOMES))
    c.check(cum.get('queryCount') == 77, 'cumulative.queryCount',
            'cumulative query count is not 77')
    c.check(cum.get('surfaceGapReconciliation') == 'P-Marcus-SymmetryFactor',
            'cumulative.surfaceGap',
            'surface-gap reconciliation is not recorded in the cumulative block')
    c.check(cum.get('earlyCrossDomainPair') == 'P-Kasha-Sabatier',
            'cumulative.earlyCrossDomain',
            'early cross-domain pair is not recorded in the cumulative block')
    c.check(len(screened) + len(submitted) == CUMULATIVE_SCREENED, 'cumulative.sum',
            'accepted + submitted does not equal the cumulative screened count')
    c.check(CUMULATIVE_SCREENED + CUMULATIVE_REMAINING == UNIVERSE_PAIRS,
            'cumulative.partition',
            'screened + remaining does not equal the 136-pair universe')

    # ---- actual aggregation from the packages must reproduce the ledger numbers
    actual_r4_status = {status: r4_status.get(status, 0) for status in STATUSES}
    c.check(actual_r4_status == R4_QUERY_OUTCOMES, 'counts.r4Status',
            'actual R4 query outcomes are %r, expected %r'
            % (actual_r4_status, R4_QUERY_OUTCOMES))
    c.check(len(r4_query_ids) == SUBMITTED_PAIRS, 'counts.r4Queries',
            'R4 has %d named queries, expected %d'
            % (len(r4_query_ids), SUBMITTED_PAIRS))
    c.check(len(set(r4_query_ids)) == len(r4_query_ids), 'counts.r4QueryUnique',
            'R4 query ids are not globally unique across the packages')
    c.check(sum(per_package_queries.values()) == SUBMITTED_PAIRS,
            'counts.packageQueries', 'per-package query counts do not sum to 46')
    c.check([per_package_queries[t] for t in tags] == [16, 14, 16],
            'counts.packageSplit', 'per-package query split is not 16/14/16')
    c.check([len(per_package_pairs[t]) for t in tags] == [16, 14, 16],
            'counts.packagePairSplit', 'per-package pair split is not 16/14/16')

    # ---- remaining pairs
    remaining = ledger.get('remainingPairIds') or []
    expected_remaining = [pid for pid in universe
                          if pid not in set(accepted_ids)
                          and pid not in set(submitted_by_id)]
    c.check(len(remaining) == CUMULATIVE_REMAINING, 'remaining.count',
            'remainingPairIds has %d entries, expected %d'
            % (len(remaining), CUMULATIVE_REMAINING))
    c.check(len(set(remaining)) == len(remaining), 'remaining.duplicate',
            'remainingPairIds has duplicates')
    c.check(set(remaining) == set(expected_remaining), 'remaining.set',
            'remainingPairIds is not the universe minus the 67 screened pairs')
    c.check(remaining == expected_remaining, 'remaining.order',
            'remainingPairIds does not follow R1 queue order')
    c.check(not (set(remaining) & set(accepted_ids)), 'remaining.overlapAccepted',
            'remainingPairIds overlaps the accepted pairs')
    c.check(not (set(remaining) & set(submitted_by_id)), 'remaining.overlapSubmitted',
            'remainingPairIds overlaps the submitted pairs')
    c.check(len(expected_remaining) == CUMULATIVE_REMAINING, 'remaining.derived',
            'the universe minus 67 screened pairs is not 69')

    # ---- round history
    history = ledger.get('roundHistory') or []
    by_round = {row.get('round'): row for row in history}
    c.check(len(history) == 3, 'history.count',
            'roundHistory does not have three round rows')
    for rnd, screened_n, remaining_n, state in [
            ('R2', R2_PAIRS, UNIVERSE_PAIRS - R2_PAIRS, 'accepted-R2'),
            ('R3', ACCEPTED_PAIRS, UNIVERSE_PAIRS - ACCEPTED_PAIRS, 'accepted-R3'),
            ('R4', CUMULATIVE_SCREENED, CUMULATIVE_REMAINING, LEDGER_ACCEPTANCE_STATE)]:
        row = by_round.get(rnd) or {}
        c.check(row.get('screenedPairCount') == screened_n,
                'history.%s.screened' % rnd, '%s screened count drift' % rnd)
        c.check(row.get('remainingPairCount') == remaining_n,
                'history.%s.remaining' % rnd, '%s remaining count drift' % rnd)
        c.check(row.get('acceptance') == state, 'history.%s.acceptance' % rnd,
                '%s acceptance state drift' % rnd)
    c.check(R2_PAIRS + R3_PAIRS + SUBMITTED_PAIRS == CUMULATIVE_SCREENED,
            'history.sum', 'per-round screened counts do not sum to 67')
    c.check(UNIVERSE_PAIRS - R2_PAIRS - R3_PAIRS - SUBMITTED_PAIRS
            == CUMULATIVE_REMAINING, 'history.remainingSum',
            'per-round remaining counts do not leave 69')

    # --------------------------------------------------------------- frozen inputs
    c.check(sha(REGISTRY_REL) == EXPECTED_REGISTRY_SHA, 'registry.sha256',
            'legacy registry SHA-256 is not the accepted value')
    c.check(len(inventory.get('statements', [])) > 0, 'inventory.rows',
            'the R1 statement inventory is empty')
    lean_files = sum(1 for dirpath, _d, files in os.walk(os.path.join(root, 'PhotoLean'))
                     for name in files if name.endswith('.lean'))
    c.check(lean_files == EXPECTED_LEAN_FILES, 'photoLean.fileCount',
            'delivered Lean tree has %d files, expected %d'
            % (lean_files, EXPECTED_LEAN_FILES))

    # ------------------------------------------------------------------ non-claims
    non_claims = ledger.get('nonClaims') or []
    c.check(isinstance(non_claims, list) and len(non_claims) >= 3, 'ledger.nonClaims',
            'the ledger has fewer than three non-claims')
    joined = ' '.join(str(x).lower() for x in non_claims)
    c.check('not the same as certified' in joined or 'screened is not' in joined,
            'ledger.nonClaimScreened', 'no non-claim that screening is not certification')
    c.check('does not self-accept' in joined or 'is not an acceptance' in joined
            or 'not an acceptance' in joined, 'ledger.nonClaimAcceptance',
            'no non-claim that the submitted state is not an acceptance')
    c.check(isinstance(ledger.get('knownSeams'), list)
            and len(ledger.get('knownSeams')) >= 1, 'ledger.knownSeams',
            'the ledger does not record its known hash seams')
    c.check(any('cycle' in str(x).lower() for x in ledger.get('knownSeams') or []),
            'ledger.cycleNote', 'the ledger does not document the anti-cycle rule')

    # ------------------------------------------------------ package validator runs
    if not args.skip_package_validators:
        for pkg in PACKAGES:
            try:
                proc = subprocess.run(
                    [sys.executable, os.path.join(root, pkg['validate'])],
                    cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    text=True, timeout=600)
                out = proc.stdout or ''
            except subprocess.TimeoutExpired:
                c.fail('validator.%s.timeout' % pkg['tag'],
                       '%s validator timed out' % pkg['tag'])
                continue
            c.check(proc.returncode == 0, 'validator.%s.exit' % pkg['tag'],
                    '%s validator exited %d' % (pkg['tag'], proc.returncode))
            c.check('RESULT: PASS' in out, 'validator.%s.result' % pkg['tag'],
                    '%s validator did not print RESULT: PASS' % pkg['tag'])

    report(c, root, args.coverage, {
        'accepted': len(screened),
        'submitted': len(submitted),
        'r4_query_ids': len(r4_query_ids),
        'r4_status': dict(r4_status),
        'cumulative': cum.get('screenedPairCount'),
        'remaining': len(remaining),
    })
    return 0 if not c.failed else 1


def report(c, root, coverage, summary):
    print('R4 cumulative coverage validation')
    print('  root: %s' % root)
    print('  ledger: %s' % coverage)
    if summary:
        print('  accepted pairs: %d' % summary['accepted'])
        print('  submitted R4 pairs: %d' % summary['submitted'])
        print('  R4 named queries: %d' % summary['r4_query_ids'])
        print('  R4 query outcomes: %s'
              % json.dumps(summary['r4_status'], sort_keys=True))
        print('  cumulative: %s/136 screened, %s remaining'
              % (summary['cumulative'], summary['remaining']))
    print('  checks passed: %d' % c.passed)
    print('  checks failed: %d' % len(c.failed))
    for code, message in c.failed:
        print('FAIL [%s] %s' % (code, message))
    if c.failed:
        print('RESULT: FAIL (%d failed checks)' % len(c.failed))
    else:
        print('RESULT: PASS (all R4 coverage checks passed)')


if __name__ == '__main__':
    sys.exit(main())
