#!/usr/bin/env python3
"""R5 cumulative coverage validator (deterministic, fail-closed).

This is the integration-round gate for the R5 bounded-relation audit. It closes the
136-pair universe: the 67 pairs accepted in R2/R3/R4 plus the 69 pairs submitted in the
five R5 packages.

What it checks
--------------
1.  Ledger schema, round and universe pin (136 pairs, 17 theories, pair-queue SHA-256).
2.  Accepted prior state: the 21 accepted R2/R3 entries are preserved *content-identically*
    in ``screenedPairs`` and still reconcile pair-by-pair with the accepted R2 and R3
    screening packages (pair set, query counts, per-status counts, package path, state).
3.  Accepted R4 state: the 46 R4 entries are preserved content-identically in
    ``submittedPairs`` (accepted-R4), reconcile pair-by-pair with the E1/E2/CI packages
    (including query ids), and remain disjoint from R2/R3.
4.  Frozen snapshot: ``bounded_audit/r4/coverage-accepted.json`` is unmodified (pinned
    SHA-256), still declares the R4 67/69 state, and the current ledger's R2/R3/R4 blocks
    are byte-equal (as JSON values) to the snapshot's blocks. The R4 accepted ledger is
    never rewritten by R5.
5.  R5 packages, directly from their own artifacts: the exact assigned pair lists
    (16/16/13/15/9 = 69 pairs, including the R1 work-package cross-check and the
    ``P-Kasha-Sabatier`` exclusion for XD1), pairwise disjointness, disjointness from the
    accepted 67, unique query ids (17/16/16/15/11 = 75 queries), exactly one five-status
    outcome per query, the seven-kind vocabulary, endpoint/inventory/source-hash agreement,
    shared context, translations, premises, scopes, snapshots, observation channels and the
    complete semantic fields.
6.  Evidence links: every non-certified query links to exactly one search-log entry that
    links back, carries the required provenance fields and recompute commands; every
    certified query links to a real probe declaration under its declared axioms, whose
    per-declaration axiom print-out matches the declared footprint; ``outOfScope`` is a
    statement-level jurisdiction record and ``refuted`` is absent (no failed proof is
    relabelled).
7.  Package hashes: the ledger's recorded SHA-256 values for every R5 package (screening,
    search log, fragment, probe, validator) match the files on disk, and each R5 work
    package's pair/query/status counts match its artifact.
8.  R5 ledger rows: exactly 69 unique R5 rows, each reconciled with its package
    (query ids, query count, per-status counts, work package, path), with a uniform
    acceptance state.
9.  Acceptance neutrality: the 69 R5 rows must be uniformly ``submitted-R5-pending-review``
    before review or uniformly ``accepted-R5`` after lead acceptance. The validator derives
    ``acceptedPairCount``/``submittedPairCount`` from the row states (67/69 before review,
    136/0 after acceptance) and needs no edit for the flip. Package fragments remain
    immutable submission snapshots and are *not* required to flip.
10. Cumulative arithmetic: 136/136 screened, zero remaining, by-round 10/11/46/69, query
    outcomes 67/0/39/2/44 over 152 named queries, round history and the 136-pair partition.
11. No hash cycles: the ledger records no hash of itself and no hash of
    ``bounded_audit/r3/screening.json`` (the accepted R3 package pins this ledger); the R3
    work-package entry carries no hash; no R5 package or fragment reads or pins the mutable
    ledger. The ledger records the R2 and R4/R5 package hashes because those packages do not
    pin the ledger.
12. Frozen inputs: the legacy registry SHA-256 equals the accepted constant, the delivered
    Lean tree still has 102 files, and the five R5 package validators are re-run as
    subprocesses (each must exit 0 with ``RESULT: PASS``).

Usage
-----
    python3 bounded_audit/r5/validate_coverage.py
    python3 bounded_audit/r5/validate_coverage.py --root /tmp/sandbox/photolean
    python3 bounded_audit/r5/validate_coverage.py --skip-package-validators
    python3 bounded_audit/r5/validate_coverage.py \
        --coverage /tmp/mut/coverage.json \
        --override bounded_audit/r5/radiative-01/screening.json=/tmp/mut/rad1.json

Exit code 0 means every check passed; 1 means at least one check failed.
"""

import argparse
import hashlib
import json
import os
import re
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
R3_REL = 'bounded_audit/r3/screening.json'
R4_SNAPSHOT_REL = 'bounded_audit/r4/coverage-accepted.json'

STATUSES = ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope']
KINDS = ['definitionalIdentity', 'implication', 'equivalence',
         'conditionalComposition', 'observationalEquivalence',
         'distinguishability', 'refutation']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
ENDPOINT_FORMS = {'definition', 'theorem', 'theorem-lhs-predicate',
                  'theorem-rhs-predicate', 'theorem-rhs-term'}
TRANSLATION_IDS = {'identity', 'rfl-pin', 'coordinate-map', 'rat-to-real',
                   'surface-to-barrier', 'descriptor-endpoint', 'energy-window',
                   'observational-setup', 'candidate-not-total', 'none-declared'}

PENDING_STATE = 'submitted-R5-pending-review'
ACCEPTED_R5_STATE = 'accepted-R5'
R5_ALLOWED_STATES = {PENDING_STATE, ACCEPTED_R5_STATE}

EXPECTED_REGISTRY_SHA = ('25d38791ce86f9030598eb68b6894a886513164ddb9165e0ff'
                         'f371883c1ecbf0')
EXPECTED_R4_SNAPSHOT_SHA = ('d1e44bf7bbb5e81c7b85f610d6ffc1d4d3fed0fcde5cd1ab'
                            '3202fb23ca6c32fa')
EXPECTED_LEAN_FILES = 102

UNIVERSE_PAIRS = 136
UNIVERSE_THEORIES = 17
PRIOR_ACCEPTED_PAIRS = 67
R5_PAIRS = 69
CUMULATIVE_SCREENED = 136
CUMULATIVE_REMAINING = 0
R5_QUERY_COUNT = 75
CUMULATIVE_QUERY_COUNT = 152
R5_QUERY_OUTCOMES = {'certified': 25, 'refuted': 0, 'unresolved': 12,
                     'notEstablished': 1, 'outOfScope': 37}
CUMULATIVE_QUERY_OUTCOMES = {'certified': 67, 'refuted': 0, 'unresolved': 39,
                             'notEstablished': 2, 'outOfScope': 44}

PRIOR_PACKAGES = [
    {
        'tag': 'R2',
        'round': 'R2',
        'path': 'bounded_audit/wp-surface-01/screening.json',
        'pairs': 10,
        'queries': 19,
        'byStatus': {'certified': 16, 'unresolved': 3},
        'acceptance': 'accepted-R2',
        'ledgerList': 'screenedPairs',
    },
    {
        'tag': 'R3',
        'round': 'R3',
        'path': 'bounded_audit/r3/screening.json',
        'pairs': 11,
        'queries': 12,
        'byStatus': {'certified': 7, 'unresolved': 5},
        'acceptance': 'accepted-R3',
        'ledgerList': 'screenedPairs',
    },
    {
        'tag': 'R4-E1',
        'round': 'R4',
        'path': 'bounded_audit/r4/excited-01/screening.json',
        'pairs': 16,
        'queries': 16,
        'byStatus': {'certified': 6, 'unresolved': 9, 'outOfScope': 1},
        'acceptance': 'accepted-R4',
        'ledgerList': 'submittedPairs',
    },
    {
        'tag': 'R4-E2',
        'round': 'R4',
        'path': 'bounded_audit/r4/excited-02/screening.json',
        'pairs': 14,
        'queries': 14,
        'byStatus': {'certified': 5, 'unresolved': 4, 'outOfScope': 5},
        'acceptance': 'accepted-R4',
        'ledgerList': 'submittedPairs',
    },
    {
        'tag': 'R4-CI',
        'round': 'R4',
        'path': 'bounded_audit/r4/conical-01/screening.json',
        'pairs': 16,
        'queries': 16,
        'byStatus': {'certified': 8, 'unresolved': 6, 'notEstablished': 1,
                     'outOfScope': 1},
        'acceptance': 'accepted-R4',
        'ledgerList': 'submittedPairs',
    },
]

R5_PACKAGES = [
    {
        'tag': 'RAD1',
        'dir': 'bounded_audit/r5/radiative-01',
        'workPackage': 'WP-radiative-energy-transfer-01',
        'r1WorkPackage': 'WP-radiative-energy-transfer-01',
        'primaryCluster': 'radiative-energy-transfer',
        'pairs': 16,
        'queries': 17,
        'byStatus': {'certified': 11, 'unresolved': 2, 'outOfScope': 4},
        'probe': 'probes/RAD1-probe.lean',
        'pairIds': [
            'P-Marcus-KashaVavilov', 'P-Marcus-EnergyGapLaw',
            'P-Marcus-StokesShift', 'P-Marcus-ICvsISC', 'P-Marcus-Forster',
            'P-Marcus-Einstein', 'P-Kasha-KashaVavilov', 'P-Kasha-EnergyGapLaw',
            'P-Kasha-StokesShift', 'P-Kasha-ICvsISC', 'P-Kasha-Forster',
            'P-Kasha-Einstein', 'P-KashaVavilov-SternVolmer',
            'P-KashaVavilov-QuantumYield', 'P-KashaVavilov-FluorPhos',
            'P-KashaVavilov-EnergyGapLaw',
        ],
    },
    {
        'tag': 'RAD2',
        'dir': 'bounded_audit/r5/radiative-02',
        'workPackage': 'WP-radiative-energy-transfer-02',
        'r1WorkPackage': 'WP-radiative-energy-transfer-02',
        'primaryCluster': 'radiative-energy-transfer',
        'pairs': 16,
        'queries': 16,
        'byStatus': {'certified': 4, 'unresolved': 6, 'outOfScope': 6},
        'probe': 'probes/RAD2-probe.lean',
        'pairIds': [
            'P-KashaVavilov-StokesShift', 'P-KashaVavilov-ICvsISC',
            'P-KashaVavilov-Forster', 'P-KashaVavilov-Einstein',
            'P-SternVolmer-EnergyGapLaw', 'P-SternVolmer-StokesShift',
            'P-SternVolmer-ICvsISC', 'P-SternVolmer-Forster',
            'P-SternVolmer-Einstein', 'P-QuantumYield-EnergyGapLaw',
            'P-QuantumYield-StokesShift', 'P-QuantumYield-ICvsISC',
            'P-QuantumYield-Forster', 'P-QuantumYield-Einstein',
            'P-FluorPhos-EnergyGapLaw', 'P-FluorPhos-StokesShift',
        ],
    },
    {
        'tag': 'RAD3',
        'dir': 'bounded_audit/r5/radiative-03',
        'workPackage': 'WP-radiative-energy-transfer-03',
        'r1WorkPackage': 'WP-radiative-energy-transfer-03',
        'primaryCluster': 'radiative-energy-transfer',
        'pairs': 13,
        'queries': 16,
        'byStatus': {'certified': 10, 'unresolved': 1, 'notEstablished': 1,
                     'outOfScope': 4},
        'probe': 'probes/RAD3-probe.lean',
        'pairIds': [
            'P-FluorPhos-ICvsISC', 'P-FluorPhos-Forster', 'P-FluorPhos-Einstein',
            'P-EnergyGapLaw-StokesShift', 'P-EnergyGapLaw-ICvsISC',
            'P-EnergyGapLaw-Forster', 'P-EnergyGapLaw-Einstein',
            'P-StokesShift-ICvsISC', 'P-StokesShift-Forster',
            'P-StokesShift-Einstein', 'P-ICvsISC-Forster', 'P-ICvsISC-Einstein',
            'P-Forster-Einstein',
        ],
    },
    {
        'tag': 'XD1',
        'dir': 'bounded_audit/r5/cross-domain-01',
        'workPackage': 'XD1-CROSS-DOMAIN-01',
        'r1WorkPackage': 'WP-cross-domain-screening-01',
        'primaryCluster': 'cross-domain-screening',
        'pairs': 15,
        'queries': 15,
        'byStatus': {'unresolved': 3, 'outOfScope': 12},
        'probe': 'probes/XD1-probe.lean',
        'excludedAcceptedPair': 'P-Kasha-Sabatier',
        'pairIds': [
            'P-Marcus-Goldschmidt', 'P-Hammond-Goldschmidt',
            'P-BEP-Goldschmidt', 'P-Kasha-Goldschmidt',
            'P-Sabatier-Goldschmidt', 'P-Sabatier-KashaVavilov',
            'P-Sabatier-SternVolmer', 'P-Sabatier-QuantumYield',
            'P-Sabatier-FluorPhos', 'P-Sabatier-EnergyGapLaw',
            'P-Sabatier-StokesShift', 'P-Sabatier-ICvsISC',
            'P-Sabatier-Forster', 'P-Sabatier-Einstein',
            'P-Goldschmidt-SymmetryFactor',
        ],
    },
    {
        'tag': 'XD2',
        'dir': 'bounded_audit/r5/cross-domain-02',
        'workPackage': 'WP-cross-domain-screening-02',
        'r1WorkPackage': 'WP-cross-domain-screening-02',
        'primaryCluster': 'cross-domain-screening',
        'pairs': 9,
        'queries': 11,
        'byStatus': {'outOfScope': 11},
        'probe': None,
        'pairIds': [
            'P-Goldschmidt-KashaVavilov', 'P-Goldschmidt-SternVolmer',
            'P-Goldschmidt-QuantumYield', 'P-Goldschmidt-FluorPhos',
            'P-Goldschmidt-EnergyGapLaw', 'P-Goldschmidt-StokesShift',
            'P-Goldschmidt-ICvsISC', 'P-Goldschmidt-Forster',
            'P-Goldschmidt-Einstein',
        ],
    },
]

for _pkg in R5_PACKAGES:
    _pkg['screening'] = _pkg['dir'] + '/screening.json'
    _pkg['searchLog'] = _pkg['dir'] + '/search-log.json'
    _pkg['fragment'] = _pkg['dir'] + '/coverage-fragment.json'
    _pkg['validate'] = _pkg['dir'] + '/validate.py'


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


def load_json(path):
    with open(path, encoding='utf-8') as fh:
        return json.load(fh)


def read_text(path):
    with open(path, encoding='utf-8') as fh:
        return fh.read()


def status_counts(queries):
    return dict(Counter(q['outcome']['status'] for q in queries))


def kind_counts(queries):
    return dict(Counter(q['expectedKind'] for q in queries))


def zero_filled(mapping):
    return {status: mapping.get(status, 0) for status in STATUSES}


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
    """Normalise the two R5 fragment shapes to pairId -> (count, byStatus, queryIds)."""
    out = {}
    rows = fragment.get('pairs')
    if not isinstance(rows, list):
        rows = fragment.get('screenedPairs')
    for entry in rows or []:
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


def fragment_screening_sha(fragment):
    """Return the screening SHA-256 pinned by an R5 fragment, across its two shapes."""
    artifacts = fragment.get('packageArtifacts') or {}
    if isinstance(artifacts.get('screening'), dict):
        return artifacts['screening'].get('sha256')
    if fragment.get('screeningSha256'):
        return fragment['screeningSha256']
    wp = fragment.get('workPackage')
    if isinstance(wp, dict) and wp.get('sha256'):
        return wp['sha256']
    if fragment.get('packageSha256'):
        return fragment['packageSha256']
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


def ledger_entries_by_pair(entries):
    return {e.get('pairId'): e for e in entries}


def main(argv=None):
    parser = argparse.ArgumentParser(
        description='Validate the R5 cumulative bounded-coverage ledger.')
    parser.add_argument('--root', default=None,
                        help='photolean repository root (default: derived from __file__)')
    parser.add_argument('--coverage', default=LEDGER_REL,
                        help='ledger path, relative to root (default: %s)' % LEDGER_REL)
    parser.add_argument('--skip-package-validators', action='store_true',
                        help='do not re-run the five R5 package validators')
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

    sha_cache = {}

    def path_of(rel):
        return overrides.get(rel, os.path.join(root, rel))

    def load(rel):
        return load_json(path_of(rel))

    def text(rel):
        return read_text(path_of(rel))

    def sha(rel):
        path = path_of(rel)
        if path not in sha_cache:
            sha_cache[path] = sha_file(path)
        return sha_cache[path]

    def exists(rel):
        return os.path.exists(path_of(rel))

    c = Checks()

    # ------------------------------------------------------------------ inputs
    required = [QUEUE_REL, INV_REL, CLUSTER_REL, BOUNDARY_REL, REGISTRY_REL,
                R3_REL, R4_SNAPSHOT_REL, args.coverage]
    for pkg in PRIOR_PACKAGES:
        required.append(pkg['path'])
    for pkg in R5_PACKAGES:
        required += [pkg['screening'], pkg['searchLog'], pkg['fragment'],
                     pkg['validate']]
        if pkg['probe']:
            required.append(pkg['dir'] + '/' + pkg['probe'])
    missing = [rel for rel in required if not exists(rel)]
    for rel in missing:
        c.fail('input.missing', 'required input is missing: %s' % rel)
    if missing:
        report(c, root, args.coverage, None)
        return 1

    ledger = load(args.coverage)
    ledger_text = text(args.coverage)
    ledger_sha = sha(args.coverage)
    snapshot = load(R4_SNAPSHOT_REL)
    queue = load(QUEUE_REL)
    inventory = load(INV_REL)
    cluster = load(CLUSTER_REL)
    registry = load(REGISTRY_REL)

    universe = [row['pairId'] for row in queue['pairs']]
    universe_set = set(universe)
    inv_by_id = {row['id']: row for row in inventory['statements']}
    dangling_ids = {d['id'] for d in inventory.get('legacyDanglingStatements', [])}
    queue_by_id = {row['pairId']: row for row in queue['pairs']}
    cluster_wp = {}
    for cl in cluster['clusters']:
        for wp in cl.get('workPackages', []):
            cluster_wp[wp['id']] = (cl['id'], list(wp['pairIds']))

    # ------------------------------------------------------------- ledger schema
    c.check(ledger.get('schemaVersion') == '1.0.0', 'ledger.schemaVersion',
            'unexpected schemaVersion')
    c.check(ledger.get('artifactKind') == 'bounded-coverage-ledger',
            'ledger.artifactKind', 'unexpected artifactKind')
    c.check(ledger.get('round') == 'R5', 'ledger.round',
            'the integrated ledger must declare round R5')
    c.check(ledger.get('generatedOn') == '2026-11-04', 'ledger.generatedOn',
            'generatedOn drift')
    c.nonempty(ledger.get('description'), 'ledger.description',
               'ledger has no description')
    universe_block = ledger.get('universe') or {}
    c.check(universe_block.get('pairCount') == UNIVERSE_PAIRS, 'universe.pairCount',
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

    # ------------------------------------------------------------- hash cycles
    for banned in ('coverageSha256', 'ledgerSha256', 'selfSha256',
                   'coverageSelfSha256', 'ledgerSelfSha256'):
        c.check(banned not in ledger, 'cycle.selfKey',
                'the ledger carries a self-hash slot %r' % banned)
    c.check(ledger_sha not in ledger_text, 'cycle.selfPin',
            'the ledger records its own SHA-256; that is a self-referential hash cycle')
    r3_screening_sha = sha(R3_REL)
    c.check(r3_screening_sha not in ledger_text, 'cycle.r3ScreeningPin',
            'the ledger records the R3 screening SHA-256; the accepted R3 package '
            'pins this ledger, so that edge would close a hash cycle')

    # ---------------------------------------------- frozen R4 snapshot (preserved)
    c.check(sha(R4_SNAPSHOT_REL) == EXPECTED_R4_SNAPSHOT_SHA,
            'snapshot.sha256',
            'the frozen R4 accepted-ledger snapshot was modified')
    c.check(snapshot.get('round') == 'R4', 'snapshot.round',
            'the frozen snapshot no longer declares round R4')
    snap_cum = snapshot.get('cumulative') or {}
    c.check(snap_cum.get('screenedPairCount') == 67, 'snapshot.cumulative',
            'the frozen snapshot no longer records 67 screened pairs')
    c.check(snap_cum.get('remainingPairCount') == 69, 'snapshot.remaining',
            'the frozen snapshot no longer records 69 remaining pairs')
    for key in ('acceptedWorkPackages', 'submittedWorkPackages',
                'screenedPairs', 'submittedPairs'):
        c.check(ledger.get(key) == snapshot.get(key), 'snapshot.preserved.%s' % key,
                'the ledger no longer preserves the frozen R4 %s block' % key)

    # --------------------------------------------------- accepted prior packages
    prior_maps = {}
    prior_status = Counter()
    accepted_prior_ids = []
    for pkg in PRIOR_PACKAGES:
        screening = load(pkg['path'])
        pair_map = package_pair_map(screening)
        prior_maps[pkg['tag']] = pair_map
        c.check(len(pair_map) == pkg['pairs'], 'prior.%s.pairCount' % pkg['tag'],
                '%s screens %d pairs, expected %d'
                % (pkg['tag'], len(pair_map), pkg['pairs']))
        actual_status = Counter()
        query_total = 0
        for qids, by_status, _kinds in pair_map.values():
            query_total += len(qids)
            actual_status.update(by_status)
        c.check(query_total == pkg['queries'], 'prior.%s.queryCount' % pkg['tag'],
                '%s has %d queries, expected %d'
                % (pkg['tag'], query_total, pkg['queries']))
        c.check(dict(actual_status) == pkg['byStatus'],
                'prior.%s.byStatus' % pkg['tag'],
                '%s actual status counts drift' % pkg['tag'])
        prior_status.update(actual_status)
        accepted_prior_ids += list(pair_map)
        c.check(set(pair_map) <= universe_set, 'prior.%s.unknownPair' % pkg['tag'],
                '%s names a pair outside the R1 queue' % pkg['tag'])
    prior_tags = [p['tag'] for p in PRIOR_PACKAGES]
    for i, a in enumerate(prior_tags):
        for b in prior_tags[i + 1:]:
            c.check(not (set(prior_maps[a]) & set(prior_maps[b])),
                    'prior.overlap',
                    'accepted packages %s and %s share a pair' % (a, b))
    c.check(len(accepted_prior_ids) == PRIOR_ACCEPTED_PAIRS
            and len(set(accepted_prior_ids)) == PRIOR_ACCEPTED_PAIRS,
            'prior.count', 'the accepted R2/R3/R4 packages do not hold 67 unique pairs')

    # ----------------------------------------------- ledger accepted prior state
    screened = ledger.get('screenedPairs') or []
    submitted = ledger.get('submittedPairs') or []
    screened_by_id = ledger_entries_by_pair(screened)
    submitted_by_id = ledger_entries_by_pair(submitted)
    c.check(len(screened) == 21 and len(screened_by_id) == 21, 'accepted.count',
            'the ledger does not hold the 21 accepted R2/R3 pairs')
    c.check(len(submitted) == 46 and len(submitted_by_id) == 46, 'r4.count',
            'the ledger does not hold the 46 accepted-R4 pairs')
    c.check(set(screened_by_id) == set(prior_maps['R2']) | set(prior_maps['R3']),
            'accepted.pairSet', 'the accepted set is not the R2/R3 union')
    c.check(set(submitted_by_id) == (set(prior_maps['R4-E1'])
                                     | set(prior_maps['R4-E2'])
                                     | set(prior_maps['R4-CI'])),
            'r4.pairSet', 'the R4 ledger set is not the E1/E2/CI union')
    c.check(not (set(screened_by_id) & set(submitted_by_id)), 'r4.overlapAccepted',
            'an R4 ledger row repeats an accepted R2/R3 pair')
    pkg_path_by_tag = {p['tag']: p['path'] for p in PRIOR_PACKAGES}
    for pkg in PRIOR_PACKAGES:
        entries = (screened if pkg['ledgerList'] == 'screenedPairs' else submitted)
        by_id = {e.get('pairId'): e for e in entries}
        for pid, (qids, by_status, _kinds) in prior_maps[pkg['tag']].items():
            entry = by_id.get(pid)
            if entry is None:
                c.fail('prior.ledgerMissing',
                       'ledger has no %s row for %r' % (pkg['tag'], pid))
                continue
            c.check(entry.get('round') == pkg['round'], 'prior.ledgerRound',
                    'ledger row %r has the wrong round' % pid)
            c.check(entry.get('acceptance') == pkg['acceptance'],
                    'prior.ledgerAcceptance',
                    'ledger row %r is not %s' % (pid, pkg['acceptance']))
            c.check(entry.get('packagePath') == pkg_path_by_tag[pkg['tag']],
                    'prior.ledgerPath',
                    'ledger row %r names the wrong package path' % pid)
            c.check(entry.get('queryCount') == len(qids), 'prior.ledgerQueryCount',
                    'ledger row %r query count drift' % pid)
            c.check(entry.get('byStatus') == by_status, 'prior.ledgerByStatus',
                    'ledger row %r per-status counts drift' % pid)
            if pkg['ledgerList'] == 'submittedPairs':
                c.check(entry.get('queryIds') == qids, 'prior.ledgerQueryIds',
                        'ledger row %r query ids drift' % pid)

    # -------------------------------------------------- R5 package pair coverage
    per_package_pairs = {}
    per_package_queries = {}
    per_package_status = {}
    per_package_query_ids = {}
    r5_query_ids = []
    r5_status = Counter()
    r5_kind = Counter()
    r5_pair_ids = []

    for pkg in R5_PACKAGES:
        tag = pkg['tag']
        screening = load(pkg['screening'])
        search_log = load(pkg['searchLog'])
        fragment = load(pkg['fragment'])
        pair_map = package_pair_map(screening)
        screening_text = text(pkg['screening'])
        fragment_text = text(pkg['fragment'])

        # ---- package vocabulary / snapshot
        c.check(screening.get('schemaVersion') == '1.0.0',
                'pkg.%s.schema' % tag, '%s schemaVersion drift' % tag)
        c.check(screening.get('artifactKind') == 'bounded-screening-package',
                'pkg.%s.kind' % tag, '%s artifactKind drift' % tag)
        c.check(screening.get('round') == 'R5', 'pkg.%s.round' % tag,
                '%s must declare round R5' % tag)
        c.check(screening.get('statusVocabulary') == STATUSES,
                'pkg.%s.statusVocab' % tag, '%s status vocabulary drift' % tag)
        c.check(screening.get('kindVocabulary') == KINDS,
                'pkg.%s.kindVocab' % tag, '%s kind vocabulary drift' % tag)
        c.check(set(screening.get('allowedAxioms', [])) == ALLOWED_AXIOMS,
                'pkg.%s.allowedAxioms' % tag, '%s allowed-axiom list drift' % tag)

        snap = screening.get('snapshot') or {}
        c.check(snap.get('date') == '2026-11-04', 'pkg.%s.snapshot.date' % tag,
                '%s snapshot date drift' % tag)
        c.check(snap.get('round') == 'R5', 'pkg.%s.snapshot.round' % tag,
                '%s snapshot round drift' % tag)
        c.check(snap.get('deliveredLeanFileCount') == EXPECTED_LEAN_FILES,
                'pkg.%s.snapshot.leanCount' % tag,
                '%s snapshot Lean file count drift' % tag)
        for rel, key in [(INV_REL, 'inventorySha256'),
                         (QUEUE_REL, 'pairQueueSha256'),
                         (CLUSTER_REL, 'clusterPlanSha256'),
                         (BOUNDARY_REL, 'boundarySha256'),
                         (REGISTRY_REL, 'legacyRegistrySha256')]:
            c.check(snap.get(key) == sha(rel), 'pkg.%s.snapshot.%s' % (tag, key),
                    '%s %s does not match %s' % (tag, key, rel))
        c.check(snap.get('legacyRegistrySha256') == EXPECTED_REGISTRY_SHA,
                'pkg.%s.registryPinned' % tag,
                '%s pins a non-accepted legacy registry hash' % tag)

        # ---- work package / exact pair set
        work = screening.get('workPackage') or {}
        c.check(work.get('id') == pkg['workPackage'], 'pkg.%s.workPackage' % tag,
                '%s work-package id drift' % tag)
        c.check(work.get('pairCount') == pkg['pairs'], 'pkg.%s.wpPairCount' % tag,
                '%s work-package pair count drift' % tag)
        pair_ids = [p.get('pairId') for p in screening['pairs']]
        c.check(len(pair_ids) == len(set(pair_ids)), 'pkg.%s.pairDuplicate' % tag,
                '%s screening pair ids are not unique' % tag)
        c.check(pair_ids == pkg['pairIds'], 'pkg.%s.pairList' % tag,
                '%s pair list/order is not the assigned list' % tag)
        c.check(len(screening['pairs']) == pkg['pairs'], 'pkg.%s.pairCount' % tag,
                '%s screens %d pairs, expected %d'
                % (tag, len(screening['pairs']), pkg['pairs']))
        if work.get('pairIds') is not None:
            c.check(list(work.get('pairIds')) == pkg['pairIds'],
                    'pkg.%s.wpPairIds' % tag,
                    '%s work-package pairIds drift from the pair rows' % tag)
        c.check(set(pair_ids) <= universe_set, 'pkg.%s.unknownPair' % tag,
                '%s names a pair outside the R1 queue' % tag)
        c.check(not (set(pair_ids) & set(accepted_prior_ids)),
                'pkg.%s.acceptedOverlap' % tag,
                '%s overlaps the accepted 67 pairs' % tag)
        c.check('P-Kasha-Sabatier' not in pair_ids, 'pkg.%s.kashaSabatier' % tag,
                '%s rescreens the accepted P-Kasha-Sabatier pair' % tag)
        if pkg.get('excludedAcceptedPair'):
            c.check(pkg['excludedAcceptedPair'] not in pair_ids,
                    'pkg.%s.excludedPair' % tag,
                    '%s includes the explicitly excluded accepted pair' % tag)
            r1_list = cluster_wp.get(pkg['r1WorkPackage'], (None, []))[1]
            c.check(set(r1_list) - set(pair_ids) == {pkg['excludedAcceptedPair']},
                    'pkg.%s.r1Difference' % tag,
                    '%s is not exactly the R1 work package minus the excluded pair'
                    % tag)
        if pkg['r1WorkPackage'] in cluster_wp:
            r1_set = set(cluster_wp[pkg['r1WorkPackage']][1])
            if pkg.get('excludedAcceptedPair'):
                c.check(r1_set - set(pair_ids) == {pkg['excludedAcceptedPair']},
                        'pkg.%s.r1Exclusion' % tag,
                        '%s is not the R1 work package minus exactly the excluded '
                        'accepted pair' % tag)
            else:
                c.check(r1_set == set(pair_ids), 'pkg.%s.r1List' % tag,
                        '%s pair set is not the R1 work-package pair set' % tag)
            c.check(cluster_wp[pkg['r1WorkPackage']][0] == pkg['primaryCluster'],
                    'pkg.%s.r1Cluster' % tag,
                    '%s R1 work package belongs to another cluster' % tag)
        else:
            c.fail('pkg.%s.r1Missing' % tag,
                   '%s names an unknown R1 work package' % tag)

        # ---- per-pair queue agreement
        for pair in screening['pairs']:
            pid = pair.get('pairId')
            qrow = queue_by_id.get(pid)
            c.check(qrow is not None, 'pkg.%s.queueMissing' % tag,
                    '%s pair %r is not in the R1 queue' % (tag, pid))
            if qrow is not None:
                c.check(pair.get('theories') == qrow['theories'],
                        'pkg.%s.pairTheories' % tag,
                        '%s pair %r theories drift' % (tag, pid))
                c.check(pair.get('primaryCluster') == qrow['screeningCluster'],
                        'pkg.%s.pairCluster' % tag,
                        '%s pair %r primary cluster drift' % (tag, pid))
            qids = pair.get('queryIds') or []
            c.check(qids == [q['queryId'] for q in pair.get('queries', [])],
                    'pkg.%s.pairQueryIds' % tag,
                    '%s pair %r queryIds do not match its query rows' % (tag, pid))
            c.check(len(qids) >= 1, 'pkg.%s.pairNoQuery' % tag,
                    '%s pair %r has no named query' % (tag, pid))

        # ---- queries
        pkg_certified_decls = set()
        pkg_candidate_decls = set()
        probe_axioms = {}
        if pkg['probe']:
            probe_rel = pkg['dir'] + '/' + pkg['probe']
            probe_text = text(probe_rel)
            log_rel = pkg['dir'] + '/probes/compile.log'
            c.check(exists(log_rel), 'pkg.%s.probeLog' % tag,
                    '%s probe compile log is missing' % tag)
            if exists(log_rel):
                probe_axioms = parse_probe_axioms(text(log_rel))
            probe_ref = screening.get('probeReference') or {}
            c.check(probe_ref.get('sha256') == sha(probe_rel),
                    'pkg.%s.probeRefSha' % tag,
                    '%s probe reference hash drift' % tag)
            if probe_ref.get('declarationCount') is not None:
                c.check(probe_ref.get('declarationCount') == len(probe_axioms),
                        'pkg.%s.probeDeclCount' % tag,
                        '%s probe declaration count drift' % tag)
            forbidden = re.compile(
                r'sorry|admit|^[ \t]*(private[ \t]+|protected[ \t]+)?'
                r'(axiom|constant)([ \t]|$)', re.M)
            c.check(forbidden.search(probe_text) is None,
                    'pkg.%s.probeForbidden' % tag,
                    '%s probe contains a forbidden token' % tag)
        else:
            probe_rel = None
            probe_text = None
            c.check(not os.path.exists(os.path.join(root, pkg['dir'], 'probes')),
                    'pkg.%s.noProbe' % tag,
                    '%s ships a probes directory although it certifies nothing' % tag)
            c.check(screening.get('probeReference') is None,
                    'pkg.%s.probeRefNull' % tag,
                    '%s declares a probe reference although it certifies nothing' % tag)

        for pair in screening['pairs']:
            for q in pair.get('queries', []):
                qid = q.get('queryId')
                r5_query_ids.append(qid)
                c.nonempty(qid, 'query.id', '%s query row without queryId' % tag)
                c.check(q.get('pairId') == pair['pairId'], 'query.pairId',
                        '%s query %r pairId drift' % (tag, qid))
                for field in ['title', 'chemicalQuestion', 'chemicalRationale',
                              'expectedKindRationale', 'falsificationCondition']:
                    c.nonempty(q.get(field), 'query.%s' % field,
                               '%s query %r is missing %s' % (tag, qid, field))
                kind = q.get('expectedKind')
                c.check(kind in KINDS, 'query.kind',
                        '%s query %r expectedKind %r is not a seven-kind value'
                        % (tag, qid, kind))
                c.check(kind != 'refuted', 'query.kindStatusLeak',
                        '%s query %r uses the status refuted as an evidence kind'
                        % (tag, qid))
                if kind is not None:
                    r5_kind[kind] += 1

                # endpoints
                endpoints = q.get('endpoints') or {}
                for side in ['source', 'target']:
                    ep = endpoints.get(side) or {}
                    stmt = ep.get('statementId')
                    c.check(stmt in inv_by_id, 'endpoint.missing',
                            '%s query %r %s endpoint %r is not an inventory statement'
                            % (tag, qid, side, stmt))
                    if stmt not in inv_by_id:
                        continue
                    row = inv_by_id[stmt]
                    for key in ['theory', 'declaration', 'declarationKind',
                                'sourceArtifact', 'sourceLine', 'version',
                                'signatureSha256', 'sourceArtifactSha256']:
                        c.check(ep.get(key) == row[key], 'endpoint.%s' % key,
                                '%s query %r %s endpoint %s drifts from the inventory'
                                % (tag, qid, side, key))
                    src_rel = row['sourceArtifact']
                    c.check(exists(src_rel), 'endpoint.sourceMissing',
                            '%s query %r %s source artifact is missing'
                            % (tag, qid, side))
                    if exists(src_rel):
                        c.check(sha(src_rel) == row['sourceArtifactSha256'],
                                'endpoint.sourceHash',
                                '%s query %r %s source artifact hash drift'
                                % (tag, qid, side))
                    c.check(ep.get('endpointForm') in ENDPOINT_FORMS,
                            'endpoint.form',
                            '%s query %r %s has unknown endpointForm'
                            % (tag, qid, side))
                    c.check(stmt not in dangling_ids, 'endpoint.dangling',
                            '%s query %r %s cites a dangling legacy alias'
                            % (tag, qid, side))
                src_theory = (endpoints.get('source') or {}).get('theory')
                tgt_theory = (endpoints.get('target') or {}).get('theory')
                c.check(src_theory != tgt_theory, 'endpoint.sameTheory',
                        '%s query %r endpoints are not cross-theory' % (tag, qid))
                c.check({src_theory, tgt_theory} == set(pair.get('theories') or []),
                        'endpoint.pairTheories',
                        '%s query %r endpoints do not belong to the pair theories'
                        % (tag, qid))

                # shared context and translations
                ctx = q.get('sharedContext') or {}
                c.check(ctx.get('id') in (screening.get('contextLibrary') or {}),
                        'context.missing',
                        '%s query %r shared context %r is not in the library'
                        % (tag, qid, ctx.get('id')))
                c.check(isinstance(ctx.get('fields'), list)
                        and len(ctx.get('fields') or []) >= 1, 'context.fields',
                        '%s query %r shared context has no fields' % (tag, qid))
                c.nonempty(ctx.get('physicalReading'), 'context.reading',
                           '%s query %r shared context has no physical reading'
                           % (tag, qid))
                c.nonempty(ctx.get('provenance'), 'context.provenance',
                           '%s query %r shared context has no provenance' % (tag, qid))
                trans = q.get('translations') or {}
                for side in ['left', 'right']:
                    tr = trans.get(side) or {}
                    tid = tr.get('id')
                    c.check(tid in TRANSLATION_IDS, 'translation.id',
                            '%s query %r %s translation id %r is not admissible'
                            % (tag, qid, side, tid))
                    c.nonempty(tr.get('requirement'), 'translation.requirement',
                               '%s query %r %s translation has no requirement note'
                               % (tag, qid, side))
                    if tid in {'none-declared', 'candidate-not-total'}:
                        c.nonempty(tr.get('reason'), 'translation.reason',
                                   '%s query %r %s translation %r has no reason'
                                   % (tag, qid, side, tid))
                    else:
                        c.nonempty(tr.get('term'), 'translation.term',
                                   '%s query %r %s translation has no term'
                                   % (tag, qid, side))

                # premises
                prem = q.get('premises') or {}
                c.nonempty(prem.get('predicate'), 'premise.predicate',
                           '%s query %r has no premise predicate' % (tag, qid))
                pids = prem.get('premiseIds')
                defs = prem.get('definitions')
                c.check(isinstance(pids, list), 'premise.ids',
                        '%s query %r premiseIds is not a list' % (tag, qid))
                c.check(isinstance(defs, list), 'premise.defs',
                        '%s query %r premise definitions is not a list' % (tag, qid))
                def_ids = []
                for d in defs or []:
                    def_ids.append(d.get('id'))
                    for key in ['predicate', 'statement', 'loadBearing']:
                        c.nonempty(d.get(key), 'premise.def',
                                   '%s query %r premise definition has no %s'
                                   % (tag, qid, key))
                c.check(sorted(def_ids) == sorted(pids or []), 'premise.defIds',
                        '%s query %r premiseIds and definitions do not match'
                        % (tag, qid))
                if not pids:
                    c.check('True' in (prem.get('predicate') or ''),
                            'premise.emptyPredicate',
                            '%s query %r has no premise ids but its predicate is not True'
                            % (tag, qid))

                # scope and snapshot
                scope = q.get('scope') or {}
                c.check(scope.get('id') in (screening.get('scopeLibrary') or {}),
                        'scope.missing',
                        '%s query %r scope %r is not in the library'
                        % (tag, qid, scope.get('id')))
                c.nonempty(scope.get('description'), 'scope.description',
                           '%s query %r scope has no description' % (tag, qid))
                c.nonempty(scope.get('domain'), 'scope.domain',
                           '%s query %r scope has no domain' % (tag, qid))
                c.check(scope.get('snapshot') == snap.get('id'), 'scope.snapshot',
                        '%s query %r scope snapshot does not match the package snapshot'
                        % (tag, qid))

                # observation channels
                channels = q.get('observationChannels') or []
                c.check(isinstance(channels, list), 'channel.list',
                        '%s query %r observationChannels is not a list' % (tag, qid))
                if kind in {'observationalEquivalence', 'distinguishability'}:
                    c.check(len(channels) >= 1, 'channel.required',
                            '%s query %r has kind %s but no observation channel'
                            % (tag, qid, kind))
                for ch in channels:
                    c.nonempty(ch.get('id'), 'channel.id',
                               '%s query %r has a channel without id' % (tag, qid))
                    c.nonempty(ch.get('observedValueType'), 'channel.valueType',
                               '%s query %r channel has no observed-value type'
                               % (tag, qid))
                    c.nonempty(ch.get('inputDomain'), 'channel.inputDomain',
                               '%s query %r channel has no input domain' % (tag, qid))
                    c.check(ch.get('domainNonempty') is True,
                            'channel.domainNonempty',
                            '%s query %r channel domain is not declared nonempty'
                            % (tag, qid))
                    c.nonempty(ch.get('leftObs'), 'channel.leftObs',
                               '%s query %r channel has no left observation'
                               % (tag, qid))
                    c.nonempty(ch.get('rightObs'), 'channel.rightObs',
                               '%s query %r channel has no right observation'
                               % (tag, qid))

                # outcome / evidence
                outcome = q.get('outcome') or {}
                status = outcome.get('status')
                c.check(status in STATUSES, 'outcome.status',
                        '%s query %r outcome status %r is not one of the five'
                        % (tag, qid, status))
                r5_status[status] += 1
                c.nonempty(outcome.get('rationale'), 'outcome.rationale',
                           '%s query %r outcome has no rationale' % (tag, qid))
                evidence = outcome.get('evidence') or {}
                c.check(isinstance(evidence, dict), 'outcome.evidence',
                        '%s query %r outcome evidence is not an object' % (tag, qid))
                add_provenance_checks(c, tag, qid, q)

                if status == 'certified':
                    etype = evidence.get('type') or ''
                    c.check(etype.endswith('probe-certificate'), 'evidence.type',
                            '%s query %r certified evidence has unsupported type %r'
                            % (tag, qid, etype))
                    c.check(evidence.get('kind') == kind, 'evidence.kindMatch',
                            '%s query %r evidence kind %r does not match expectedKind %r'
                            % (tag, qid, evidence.get('kind'), kind))
                    footprint = set(evidence.get('axiomFootprint') or [])
                    c.check(footprint <= ALLOWED_AXIOMS, 'evidence.axioms',
                            '%s query %r footprint contains disallowed axioms: %s'
                            % (tag, qid, sorted(footprint - ALLOWED_AXIOMS)))
                    c.check(set(evidence.get('allowedAxioms') or []) == ALLOWED_AXIOMS,
                            'evidence.allowedAxioms',
                            '%s query %r allowed-axiom list drift' % (tag, qid))
                    probe = evidence.get('probe') or {}
                    raw_path = probe.get('path')
                    c.check(isinstance(raw_path, str)
                            and raw_path.startswith(pkg['dir'] + '/probes/'),
                            'evidence.probePath',
                            '%s query %r probe path %r is outside its package'
                            % (tag, qid, raw_path))
                    if isinstance(raw_path, str) and exists(raw_path):
                        c.check(probe.get('sha256') == sha(raw_path),
                                'evidence.probeHash',
                                '%s query %r probe source hash drift' % (tag, qid))
                    else:
                        c.fail('evidence.probeMissing',
                               '%s query %r probe source is missing' % (tag, qid))
                    decl = probe.get('declaration') or ''
                    pkg_certified_decls.add(decl)
                    c.check(decl.startswith('PhotoLean.RelationAudit.BoundedAudit.'),
                            'evidence.probeDecl',
                            '%s query %r probe declaration is outside the expected '
                            'namespace' % (tag, qid))
                    c.check(probe_text is not None
                            and re.search(r'\bdef\s+%s\b' % re.escape(short_name(decl)),
                                          probe_text) is not None,
                            'evidence.probeDeclMissing',
                            '%s query %r probe declaration is not in the probe source'
                            % (tag, qid))
                    kind_thm = probe.get('kindCheckTheorem') or ''
                    c.check(probe_text is not None
                            and re.search(r'\b(theorem|lemma)\s+%s\b'
                                          % re.escape(short_name(kind_thm)),
                                          probe_text) is not None,
                            'evidence.probeKindMissing',
                            '%s query %r probe kind-check theorem is missing'
                            % (tag, qid))
                    c.check((probe.get('buildCommand') or '').startswith(
                        'proofs/scripts/lake env lean '), 'evidence.probeBuild',
                        '%s query %r probe build command drift' % (tag, qid))
                    log_rel = probe.get('log') or ''
                    c.check(log_rel == pkg['dir'] + '/probes/compile.log',
                            'evidence.probeLog',
                            '%s query %r probe log path drift' % (tag, qid))
                    if decl and probe_axioms:
                        axioms = probe_axioms.get(decl)
                        c.check(axioms is not None, 'evidence.probeAxiomLog',
                                '%s query %r has no axiom print-out' % (tag, qid))
                        if axioms is not None:
                            c.check(axioms == footprint,
                                    'evidence.probeAxiomMatch',
                                    '%s query %r probe axiom print-out %r does not '
                                    'match the declared footprint %r'
                                    % (tag, qid, sorted(axioms), sorted(footprint)))
                    theorems = evidence.get('underlyingTheorems') or []
                    c.check(len(theorems) >= 1, 'evidence.underlying',
                            '%s query %r probe evidence cites no underlying theorem'
                            % (tag, qid))
                    for thm in theorems:
                        decl2 = thm.get('declaration') or ''
                        rel2 = thm.get('sourceArtifact') or ''
                        line = thm.get('sourceLine')
                        c.nonempty(decl2, 'evidence.underlyingDecl',
                                   '%s query %r underlying theorem has no declaration'
                                   % (tag, qid))
                        c.check(exists(rel2) if rel2 else False,
                                'evidence.underlyingSource',
                                '%s query %r underlying theorem source %r is missing'
                                % (tag, qid, rel2))
                        c.check(isinstance(line, int) and line >= 1,
                                'evidence.underlyingLine',
                                '%s query %r underlying theorem has no positive source '
                                'line' % (tag, qid))
                        if rel2 and exists(rel2) and isinstance(line, int):
                            lines = text(rel2).splitlines()
                            c.check(line <= len(lines), 'evidence.underlyingRange',
                                    '%s query %r underlying theorem line is outside '
                                    'its source' % (tag, qid))
                            if line <= len(lines):
                                c.check(short_name(decl2) in lines[line - 1],
                                        'evidence.underlyingLineMatch',
                                        '%s query %r underlying theorem is not at its '
                                        'declared source line' % (tag, qid))
                elif status in {'unresolved', 'notEstablished'}:
                    c.check((evidence.get('type') or '') == 'scoped-search',
                            'evidence.searchType',
                            '%s query %r status %s requires a scoped-search record'
                            % (tag, qid, status))
                    c.nonempty(evidence.get('searchLogRef'), 'evidence.searchRef',
                               '%s query %r status %s has no search-log reference'
                               % (tag, qid, status))
                    c.nonempty(evidence.get('candidateSummary'),
                               'evidence.candidateSummary',
                               '%s query %r status %s has no candidate summary'
                               % (tag, qid, status))
                    cand = evidence.get('candidateProbe')
                    if isinstance(cand, dict):
                        cdecl = cand.get('declaration') or ''
                        pkg_candidate_decls.add(cdecl)
                        c.check(exists(cand.get('path') or '') if cand.get('path')
                                else False, 'evidence.candidateProbePath',
                                '%s query %r candidate probe path is missing'
                                % (tag, qid))
                        c.check((cand.get('sha256') or '') != ''
                                and exists(cand.get('path') or '')
                                and cand.get('sha256') == sha(cand['path']),
                                'evidence.candidateProbeHash',
                                '%s query %r candidate probe hash drift' % (tag, qid))
                        c.check(set(cand.get('axiomFootprint') or [])
                                <= ALLOWED_AXIOMS, 'evidence.candidateAxioms',
                                '%s query %r candidate probe footprint has '
                                'disallowed axioms' % (tag, qid))
                        if cdecl and probe_axioms:
                            c.check(cdecl in probe_axioms,
                                    'evidence.candidateAxiomLog',
                                    '%s query %r candidate declaration has no axiom '
                                    'print-out' % (tag, qid))
                elif status == 'outOfScope':
                    c.check((evidence.get('type') or '') == 'jurisdiction',
                            'evidence.jurisdictionType',
                            '%s query %r outOfScope requires a jurisdiction record'
                            % (tag, qid))
                    c.nonempty(evidence.get('jurisdictionRationale'),
                               'evidence.jurisdictionRationale',
                               '%s query %r outOfScope has no statement-level rationale'
                               % (tag, qid))
                    c.nonempty(evidence.get('searchLogRef'),
                               'evidence.searchRef',
                               '%s query %r outOfScope has no search-log reference'
                               % (tag, qid))
                elif status == 'refuted':
                    c.check((evidence.get('type') or '') == 'refutation-certificate',
                            'evidence.refutationType',
                            '%s query %r refuted requires a refutation certificate'
                            % (tag, qid))
                    c.check(evidence.get('kind') == 'refutation',
                            'evidence.refutationKind',
                            '%s query %r refuted evidence kind is not refutation'
                            % (tag, qid))
                    c.nonempty(evidence.get('counterexampleWitness'),
                               'evidence.counterexample',
                               '%s query %r refuted has no counterexample witness'
                               % (tag, qid))

        # ---- probe declarations accounted for
        if pkg['probe']:
            package_decls = pkg_certified_decls | pkg_candidate_decls
            if probe_axioms:
                c.check(set(probe_axioms) <= package_decls,
                        'pkg.%s.probeUnaccounted' % tag,
                        '%s probe has axiom blocks for declarations no query cites: %s'
                        % (tag, sorted(set(probe_axioms) - package_decls)))
                cited = {d for d in package_decls
                         if d.startswith('PhotoLean.RelationAudit.BoundedAudit.')}
                c.check(cited <= set(probe_axioms), 'pkg.%s.probeMissingAxioms' % tag,
                        '%s cites probe declarations with no axiom print-out: %s'
                        % (tag, sorted(cited - set(probe_axioms))))

        # ---- search-log links
        entries = search_log.get('entries') or []
        entry_ids = [e.get('searchId') or e.get('id') for e in entries]
        c.check(search_log.get('artifactKind') == 'bounded-search-log',
                'pkg.%s.searchKind' % tag, '%s search-log artifactKind drift' % tag)
        c.check(search_log.get('round') == 'R5', 'pkg.%s.searchRound' % tag,
                '%s search-log round drift' % tag)
        c.check(len(entry_ids) == len(set(entry_ids)), 'pkg.%s.searchDuplicate' % tag,
                '%s search log has duplicate search ids' % tag)
        entry_by_id = {e.get('searchId') or e.get('id'): e for e in entries}
        status_by_qid = {q['queryId']: q['outcome']['status']
                         for pair in screening['pairs'] for q in pair['queries']}
        pair_by_qid = {q['queryId']: pair['pairId']
                       for pair in screening['pairs'] for q in pair['queries']}
        evidence_by_qid = {q['queryId']: (q['outcome'].get('evidence') or {})
                           for pair in screening['pairs'] for q in pair['queries']}
        non_certified = {qid for qid, status in status_by_qid.items()
                         if status != 'certified'}
        c.check(set(e.get('queryId') for e in entries) == non_certified,
                'pkg.%s.searchCoverage' % tag,
                '%s search log does not back exactly the non-certified queries' % tag)
        declared = search_log.get('counts') or {}
        if 'entries' in declared:
            c.check(declared.get('entries') == len(entries),
                    'pkg.%s.searchCounts' % tag,
                    '%s search-log declared entry count drift' % tag)
        for e in entries:
            sid = e.get('searchId') or e.get('id')
            qid = e.get('queryId')
            c.check(qid in status_by_qid, 'pkg.%s.searchQuery' % tag,
                    '%s search entry %r points to unknown query %r' % (tag, sid, qid))
            c.check(e.get('pairId') == pair_by_qid.get(qid),
                    'pkg.%s.searchPair' % tag,
                    '%s search entry %r names the wrong pair' % (tag, sid))
            c.check(e.get('status') == status_by_qid.get(qid),
                    'pkg.%s.searchStatus' % tag,
                    '%s search entry %r status does not match its query' % (tag, sid))
            c.check(evidence_by_qid.get(qid, {}).get('searchLogRef') == sid,
                    'pkg.%s.searchBackref' % tag,
                    '%s query %r does not point back to search entry %r'
                    % (tag, qid, sid))
            c.check(e.get('scope') in (screening.get('scopeLibrary') or {}),
                    'pkg.%s.searchScope' % tag,
                    '%s search entry %r has unknown scope' % (tag, sid))
            c.check(e.get('snapshot') == snap.get('id'),
                    'pkg.%s.searchSnapshot' % tag,
                    '%s search entry %r snapshot drift' % (tag, sid))
            stmts = e.get('searchedStatements')
            c.check(isinstance(stmts, list) and len(stmts) >= 1,
                    'pkg.%s.searchStatements' % tag,
                    '%s search entry %r has no searched statements' % (tag, sid))
            for st in stmts or []:
                c.check(st in inv_by_id, 'pkg.%s.searchStatement' % tag,
                        '%s search entry %r cites unknown statement %r'
                        % (tag, sid, st))
            kinds = e.get('searchedKinds')
            c.check(isinstance(kinds, list) and len(kinds) >= 1,
                    'pkg.%s.searchKinds' % tag,
                    '%s search entry %r has no searched kinds' % (tag, sid))
            c.check(set(kinds or []) <= set(KINDS), 'pkg.%s.searchKindVocab' % tag,
                    '%s search entry %r searches an unknown kind' % (tag, sid))
            ctxs = e.get('contextsConsidered')
            c.check(isinstance(ctxs, list) and len(ctxs) >= 1,
                    'pkg.%s.searchContexts' % tag,
                    '%s search entry %r has no considered context' % (tag, sid))
            deps = e.get('dependenciesConsulted')
            c.check(isinstance(deps, list) and len(deps) >= 1,
                    'pkg.%s.searchDeps' % tag,
                    '%s search entry %r has no consulted dependencies' % (tag, sid))
            for dep in deps or []:
                for key in ['artifact', 'locator', 'finding']:
                    c.nonempty(dep.get(key), 'pkg.%s.searchDep.%s' % (tag, key),
                               '%s search entry %r dependency has no %s'
                               % (tag, sid, key))
                art = dep.get('artifact') or ''
                if art.startswith(('PhotoLean/', 'tools/', 'bounded_audit/',
                                   'audit_boundary/', 'relation_audit/')):
                    c.check(exists(art), 'pkg.%s.searchDepMissing' % tag,
                            '%s search entry %r dependency artifact is missing: %s'
                            % (tag, sid, art))
            cmds = e.get('commands')
            c.check(isinstance(cmds, list) and len(cmds) >= 1,
                    'pkg.%s.searchCommands' % tag,
                    '%s search entry %r has no recorded commands' % (tag, sid))
            for cmd in cmds or []:
                for key in ['command', 'purpose', 'result']:
                    c.nonempty(cmd.get(key), 'pkg.%s.searchCommand.%s' % (tag, key),
                               '%s search entry %r command has no %s'
                               % (tag, sid, key))
            strategies = e.get('strategiesAttempted')
            c.check(isinstance(strategies, list) and len(strategies) >= 1,
                    'pkg.%s.searchStrategies' % tag,
                    '%s search entry %r has no attempted strategies' % (tag, sid))
            for stg in strategies or []:
                for key in ['strategy', 'outcome']:
                    c.nonempty(stg.get(key),
                               'pkg.%s.searchStrategy.%s' % (tag, key),
                               '%s search entry %r strategy has no %s'
                               % (tag, sid, key))
            c.check(bool(e.get('candidateEvidence')), 'pkg.%s.searchCandidates' % tag,
                    '%s search entry %r has no candidate evidence' % (tag, sid))
            c.check(bool(e.get('remainingGap')) or bool(e.get('jurisdictionReason')),
                    'pkg.%s.searchGap' % tag,
                    '%s search entry %r has no remaining gap or jurisdiction reason'
                    % (tag, sid))
            rec = e.get('recomputeCommands')
            c.check(bool(rec), 'pkg.%s.searchRecompute' % tag,
                    '%s search entry %r has no recompute command' % (tag, sid))
            c.nonempty(e.get('rationale'), 'pkg.%s.searchRationale' % tag,
                       '%s search entry %r has no rationale' % (tag, sid))
        for qid, status in status_by_qid.items():
            ev = evidence_by_qid.get(qid, {})
            if status == 'certified':
                c.check((ev.get('searchLogRef') or '') == '',
                        'pkg.%s.certifiedSearchEntry' % tag,
                        '%s certified query %r carries a search-log reference'
                        % (tag, qid))
            else:
                sid = ev.get('searchLogRef')
                c.check(sid in entry_by_id, 'pkg.%s.searchMissing' % tag,
                        '%s query %r status %s has no search-log entry %r'
                        % (tag, qid, status, sid))

        # ---- package declared counts
        counts = screening.get('counts') or {}
        c.check(counts.get('pairs') == pkg['pairs'], 'pkg.%s.countsPairs' % tag,
                '%s declared pair count drift' % tag)
        c.check(counts.get('queries') == pkg['queries'],
                'pkg.%s.countsQueries' % tag,
                '%s declared query count drift' % tag)
        c.check(dict(counts.get('byStatus') or {}) == pkg['byStatus'],
                'pkg.%s.countsByStatus' % tag,
                '%s declared status counts drift' % tag)
        c.check(counts.get('refuted', 0) == 0, 'pkg.%s.refuted' % tag,
                '%s declares a refuted outcome' % tag)

        # ---- actual per-package aggregation
        pkg_status = Counter()
        pkg_queries = 0
        pkg_qids = []
        for qids, by_status, _kinds in pair_map.values():
            pkg_queries += len(qids)
            pkg_qids += qids
            pkg_status.update(by_status)
        per_package_pairs[tag] = set(pair_map)
        per_package_queries[tag] = pkg_queries
        per_package_status[tag] = dict(pkg_status)
        per_package_query_ids[tag] = pkg_qids
        r5_pair_ids += list(pair_map)
        c.check(pkg_queries == pkg['queries'], 'pkg.%s.queryCount' % tag,
                '%s has %d queries, expected %d'
                % (tag, pkg_queries, pkg['queries']))
        c.check(dict(pkg_status) == pkg['byStatus'], 'pkg.%s.actualByStatus' % tag,
                '%s actual status counts drift from the R5 contract' % tag)

        # ---- prior coverage reference (must be the accepted packages, not the ledger)
        prior_paths = set()
        for ref in (screening.get('acceptedCoverageReference') or {},
                    screening.get('coverageReference') or {}):
            if not isinstance(ref, dict):
                continue
            if 'acceptedPairs' in ref:
                c.check(ref.get('acceptedPairs') == PRIOR_ACCEPTED_PAIRS,
                        'pkg.%s.priorCount' % tag,
                        '%s prior accepted-pair count is not 67' % tag)
            if 'acceptedScreenedPairCount' in ref:
                c.check(ref.get('acceptedScreenedPairCount') == PRIOR_ACCEPTED_PAIRS,
                        'pkg.%s.priorCount' % tag,
                        '%s prior accepted-pair count is not 67' % tag)
            for key in ('sources', 'derivedFrom'):
                if isinstance(ref.get(key), list):
                    prior_paths |= set(ref[key])
            if isinstance(ref.get('sourceShas'), dict):
                for rel, value in ref['sourceShas'].items():
                    prior_paths.add(rel)
                    c.check(exists(rel) and sha(rel) == value,
                            'pkg.%s.priorSha' % tag,
                            '%s prior source hash drift for %s' % (tag, rel))
        for key in ('acceptedPriorScreenedPairCount', 'priorAcceptedPairCount'):
            if key in snap:
                c.check(snap.get(key) == PRIOR_ACCEPTED_PAIRS,
                        'pkg.%s.priorCount' % tag,
                        '%s %s is not 67' % (tag, key))
        for row in snap.get('priorPackages') or []:
            rel = row.get('path')
            if rel:
                prior_paths.add(rel)
                c.check(exists(rel) and sha(rel) == row.get('sha256'),
                        'pkg.%s.priorSha' % tag,
                        '%s prior package hash drift for %s' % (tag, rel))
        accepted_pkgs = snap.get('acceptedPackages')
        if isinstance(accepted_pkgs, dict):
            for value in accepted_pkgs.values():
                if isinstance(value, dict) and value.get('path'):
                    prior_paths.add(value['path'])
                    c.check(exists(value['path'])
                            and sha(value['path']) == value.get('sha256'),
                            'pkg.%s.priorSha' % tag,
                            '%s prior package hash drift for %s'
                            % (tag, value['path']))
        for key, value in snap.items():
            if key.endswith('Sha256') and key not in {
                    'inventorySha256', 'pairQueueSha256', 'clusterPlanSha256',
                    'boundarySha256', 'legacyRegistrySha256'}:
                base = key[:-len('Sha256')]
                rel = snap.get(base + 'Package') or snap.get(base)
                if isinstance(rel, str) and 'bounded_audit' in rel:
                    prior_paths.add(rel)
                    c.check(exists(rel) and sha(rel) == value,
                            'pkg.%s.priorSha' % tag,
                            '%s prior package hash drift for %s' % (tag, rel))
        # ---- mutable-ledger abstention / fragment
        c.check('coverageLedgerSha256' not in snap, 'pkg.%s.ledgerPinned' % tag,
                '%s snapshot pins the mutable R5 ledger' % tag)
        c.check(ledger_sha not in screening_text, 'cycle.packagePinsLedger',
                '%s screening records the ledger SHA-256' % tag)
        c.check(ledger_sha not in text(pkg['searchLog']),
                'cycle.searchLogPinsLedger',
                '%s search log records the ledger SHA-256' % tag)
        c.check(fragment.get('artifactKind') == 'bounded-coverage-fragment',
                'fragment.%s.kind' % tag, '%s fragment kind drift' % tag)
        c.check(fragment.get('round') == 'R5', 'fragment.%s.round' % tag,
                '%s fragment round drift' % tag)
        c.check(fragment_state(fragment) == PENDING_STATE,
                'fragment.%s.state' % tag,
                '%s fragment is not an immutable %s submission snapshot'
                % (tag, PENDING_STATE))
        f_pairs, f_queries, f_status = fragment_counts(fragment)
        c.check(f_pairs == pkg['pairs'], 'fragment.%s.pairCount' % tag,
                '%s fragment pair count drift' % tag)
        c.check(f_queries == pkg['queries'], 'fragment.%s.queryCount' % tag,
                '%s fragment query count drift' % tag)
        c.check(f_status == pkg['byStatus'], 'fragment.%s.byStatus' % tag,
                '%s fragment status counts drift' % tag)
        c.check(fragment_screening_sha(fragment) == sha(pkg['screening']),
                'fragment.%s.screeningSha' % tag,
                '%s fragment does not pin its screening JSON' % tag)
        f_map = fragment_pair_map(fragment)
        c.check(set(f_map) == set(pair_map), 'fragment.%s.pairSet' % tag,
                '%s fragment pair set drift' % tag)
        for pid, (_count, f_by, _ids) in f_map.items():
            c.check(f_by == pair_map.get(pid, (None, None, None))[1],
                    'fragment.%s.byStatus.%s' % (tag, pid),
                    '%s fragment per-pair status drift for %r' % (tag, pid))
        c.check('cumulative' not in fragment, 'fragment.%s.cumulative' % tag,
                '%s fragment claims a cumulative ledger count' % tag)
        c.check('screenedPairCount' not in json.dumps(fragment),
                'fragment.%s.cumulativeCount' % tag,
                '%s fragment claims a cumulative screened count' % tag)
        c.check(ledger_sha not in fragment_text, 'cycle.fragmentPinsLedger',
                '%s fragment pins the mutable ledger' % tag)
        universe_frag = fragment.get('universe') or {}
        if universe_frag:
            c.check(universe_frag.get('pairCount') == UNIVERSE_PAIRS,
                    'fragment.%s.universe' % tag,
                    '%s fragment universe count drift' % tag)
            c.check(universe_frag.get('sourceSha256') == sha(QUEUE_REL),
                    'fragment.%s.universeHash' % tag,
                    '%s fragment universe hash drift' % tag)
        overlap_frag = fragment.get('overlapWithAccepted') or {}
        if overlap_frag:
            c.check(overlap_frag.get('intersection') == [],
                    'fragment.%s.overlap' % tag,
                    '%s fragment overlaps an accepted pair' % tag)
            if 'acceptedScreenedPairCount' in overlap_frag:
                c.check(overlap_frag.get('acceptedScreenedPairCount')
                        == PRIOR_ACCEPTED_PAIRS,
                        'fragment.%s.priorCount' % tag,
                        '%s fragment prior accepted count is not 67' % tag)
            for rel in overlap_frag.get('acceptedPackages') or []:
                prior_paths.add(rel)
                c.check(exists(rel), 'fragment.%s.priorPath' % tag,
                        '%s fragment names a missing prior package %s' % (tag, rel))
        if prior_paths:
            expected_prior = {p['path'] for p in PRIOR_PACKAGES}
            c.check(prior_paths == expected_prior, 'pkg.%s.priorPathSet' % tag,
                    '%s prior coverage is not derived from exactly the five accepted '
                    'packages: %s' % (tag, sorted(prior_paths ^ expected_prior)))

    # ------------------------------------------------ cross-package disjointness
    tags = [p['tag'] for p in R5_PACKAGES]
    for i, a in enumerate(tags):
        for b in tags[i + 1:]:
            c.check(not (per_package_pairs[a] & per_package_pairs[b]),
                    'packages.overlap',
                    'packages %s and %s screen the same pair' % (a, b))
    union_pairs = set().union(*per_package_pairs.values())
    c.check(len(r5_pair_ids) == R5_PAIRS
            and len(set(r5_pair_ids)) == R5_PAIRS,
            'packages.union', 'the five R5 packages cover %d unique pairs, expected %d'
            % (len(set(r5_pair_ids)), R5_PAIRS))
    c.check(len(union_pairs) == R5_PAIRS, 'packages.uniquePairs',
            'the R5 pair union is not 69 unique pairs')
    c.check(not (union_pairs & set(accepted_prior_ids)), 'packages.acceptedOverlap',
            'the R5 pair union overlaps the accepted 67 pairs')
    c.check(union_pairs | set(accepted_prior_ids) == universe_set,
            'packages.universe', 'accepted 67 + R5 69 is not the 136-pair universe')
    c.check(len(r5_query_ids) == R5_QUERY_COUNT
            and len(set(r5_query_ids)) == R5_QUERY_COUNT,
            'packages.queryIds', 'R5 has %d unique named queries, expected %d'
            % (len(set(r5_query_ids)), R5_QUERY_COUNT))
    c.check([per_package_queries[t] for t in tags] == [17, 16, 16, 15, 11],
            'packages.querySplit', 'per-package query split is not 17/16/16/15/11')
    c.check([len(per_package_pairs[t]) for t in tags] == [16, 16, 13, 15, 9],
            'packages.pairSplit', 'per-package pair split is not 16/16/13/15/9')
    c.check(dict(zero_filled(r5_status)) == R5_QUERY_OUTCOMES, 'counts.r5Status',
            'actual R5 query outcomes are %r, expected %r'
            % (dict(zero_filled(r5_status)), R5_QUERY_OUTCOMES))
    prior_query_ids = []
    for pkg in PRIOR_PACKAGES:
        for qids, _by, _kinds in prior_maps[pkg['tag']].values():
            prior_query_ids += qids
    c.check(len(prior_query_ids) == 77, 'counts.priorQueries',
            'the accepted R2/R3/R4 packages do not hold 77 named queries')
    c.check(not (set(prior_query_ids) & set(r5_query_ids)), 'counts.queryOverlap',
            'an R5 query id repeats an accepted query id')

    # ------------------------------------------------------------ R5 ledger rows
    r5_rows = ledger.get('r5SubmittedPairs') or []
    r5_by_id = ledger_entries_by_pair(r5_rows)
    c.check(len(r5_rows) == R5_PAIRS, 'r5.count',
            'ledger has %d R5 rows, expected %d' % (len(r5_rows), R5_PAIRS))
    c.check(len(r5_by_id) == len(r5_rows), 'r5.duplicate',
            'the R5 ledger rows contain a duplicate pair')
    states = {e.get('acceptance') for e in r5_rows}
    c.check(states <= R5_ALLOWED_STATES and len(states) <= 1, 'r5.state.uniform',
            'the R5 ledger rows are not uniformly one allowed state: %r'
            % sorted(states))
    r5_state = (list(states)[0] if len(states) == 1
                and list(states)[0] in R5_ALLOWED_STATES else PENDING_STATE)
    r5_accepted = 1 if r5_state == ACCEPTED_R5_STATE else 0
    expected_accepted_pairs = PRIOR_ACCEPTED_PAIRS + (R5_PAIRS if r5_accepted else 0)
    expected_submitted_pairs = 0 if r5_accepted else R5_PAIRS
    c.check(set(r5_by_id) == union_pairs, 'r5.pairSet',
            'the R5 ledger rows are not the union of the five R5 packages')
    c.check(not (set(r5_by_id) & set(accepted_prior_ids)), 'r5.overlapAccepted',
            'an R5 ledger row repeats an accepted R2/R3/R4 pair')
    c.check('P-Kasha-Sabatier' not in r5_by_id, 'r5.kashaSabatier',
            'the R5 ledger repeats the accepted P-Kasha-Sabatier pair')
    pkg_by_path = {p['screening']: p for p in R5_PACKAGES}
    for entry in r5_rows:
        pid = entry.get('pairId')
        c.check(entry.get('round') == 'R5', 'r5.round',
                'R5 ledger row %r is not round R5' % pid)
        c.check(entry.get('acceptance') in R5_ALLOWED_STATES, 'r5.acceptance',
                'R5 ledger row %r has an unknown acceptance state' % pid)
        c.nonempty(entry.get('overlapNote'), 'r5.overlapNote',
                   'R5 ledger row %r has no overlap note' % pid)
        pkg = pkg_by_path.get(entry.get('packagePath'))
        c.check(pkg is not None, 'r5.packagePath',
                'R5 ledger row %r names an unknown package' % pid)
        if pkg is None:
            continue
        pair_map = package_pair_map(load(pkg['screening']))
        if pid in pair_map:
            qids, by_status, _kinds = pair_map[pid]
            c.check(entry.get('workPackage') == pkg['workPackage'],
                    'r5.workPackage', 'R5 ledger row %r names the wrong work package'
                    % pid)
            c.check(entry.get('queryCount') == len(qids), 'r5.queryCount',
                    'R5 ledger row %r query count drift' % pid)
            c.check(entry.get('byStatus') == by_status, 'r5.byStatus',
                    'R5 ledger row %r per-status counts drift' % pid)
            c.check(entry.get('queryIds') == qids, 'r5.queryIds',
                    'R5 ledger row %r query ids drift' % pid)
        else:
            c.fail('r5.packagePair',
                   'R5 ledger row %r is not in its package' % pid)

    # ------------------------------------------------------- R5 work-package block
    r5_wps = ledger.get('r5WorkPackages') or []
    c.check(len(r5_wps) == len(R5_PACKAGES), 'r5wp.count',
            'expected exactly five R5 work packages')
    wp_by_id = {w.get('id'): w for w in r5_wps}
    for pkg in R5_PACKAGES:
        tag = pkg['tag']
        wp = wp_by_id.get(pkg['workPackage'])
        c.check(wp is not None, 'r5wp.%s' % tag,
                'ledger has no R5 work package %r' % pkg['workPackage'])
        if wp is None:
            continue
        c.check(wp.get('round') == 'R5', 'r5wp.%s.round' % tag,
                '%s work package is not round R5' % tag)
        c.check(wp.get('r1WorkPackage') == pkg['r1WorkPackage'],
                'r5wp.%s.r1' % tag, '%s R1 work-package reference drift' % tag)
        c.check(wp.get('acceptance') == r5_state, 'r5wp.%s.state' % tag,
                '%s work package state %r does not match the uniform R5 row state %r'
                % (tag, wp.get('acceptance'), r5_state))
        c.check(wp.get('pairCount') == pkg['pairs'], 'r5wp.%s.pairCount' % tag,
                '%s recorded pair count drift' % tag)
        c.check(wp.get('queryCount') == pkg['queries'], 'r5wp.%s.queryCount' % tag,
                '%s recorded query count drift' % tag)
        for key, rel in [('sha256', pkg['screening']),
                         ('searchLogSha256', pkg['searchLog']),
                         ('fragmentSha256', pkg['fragment']),
                         ('validateSha256', pkg['validate'])]:
            c.check(wp.get(key) == sha(rel), 'r5wp.%s.%s' % (tag, key),
                    '%s recorded %s does not match %s' % (tag, key, rel))
        if pkg['probe']:
            probe_rel = pkg['dir'] + '/' + pkg['probe']
            c.check(wp.get('probePath') == probe_rel, 'r5wp.%s.probePath' % tag,
                    '%s probe path drift' % tag)
            c.check(wp.get('probeSha256') == sha(probe_rel),
                    'r5wp.%s.probeSha' % tag, '%s probe hash drift' % tag)
        else:
            c.check(wp.get('probePath') is None and wp.get('probeSha256') is None,
                    'r5wp.%s.probeNull' % tag,
                    '%s records a probe it does not ship' % tag)

    # ---------------------------------------------------------------- cumulative
    cum = ledger.get('cumulative') or {}
    c.check(cum.get('screenedPairCount') == CUMULATIVE_SCREENED,
            'cumulative.screened',
            'cumulative screened count is %r, expected %d'
            % (cum.get('screenedPairCount'), CUMULATIVE_SCREENED))
    c.check(cum.get('remainingPairCount') == CUMULATIVE_REMAINING,
            'cumulative.remaining',
            'cumulative remaining count is %r, expected %d'
            % (cum.get('remainingPairCount'), CUMULATIVE_REMAINING))
    c.check(cum.get('acceptedPairCount') == expected_accepted_pairs,
            'cumulative.accepted',
            'cumulative accepted count is %r, expected %d for R5 state %r'
            % (cum.get('acceptedPairCount'), expected_accepted_pairs, r5_state))
    c.check(cum.get('submittedPairCount') == expected_submitted_pairs,
            'cumulative.submitted',
            'cumulative submitted count is %r, expected %d for R5 state %r'
            % (cum.get('submittedPairCount'), expected_submitted_pairs, r5_state))
    c.check(cum.get('acceptedBeforeReviewPairCount') == PRIOR_ACCEPTED_PAIRS,
            'cumulative.acceptedBeforeReview',
            'acceptedBeforeReviewPairCount must stay 67')
    c.check(cum.get('byRound') == {'R2': 10, 'R3': 11, 'R4': 46, 'R5': 69},
            'cumulative.byRound', 'cumulative by-round counts drift')
    c.check(dict(cum.get('queryOutcomes') or {}) == CUMULATIVE_QUERY_OUTCOMES,
            'cumulative.queryOutcomes',
            'cumulative query outcomes are %r, expected %r'
            % (cum.get('queryOutcomes'), CUMULATIVE_QUERY_OUTCOMES))
    c.check(cum.get('queryCount') == CUMULATIVE_QUERY_COUNT,
            'cumulative.queryCount',
            'cumulative query count is %r, not %d'
            % (cum.get('queryCount'), CUMULATIVE_QUERY_COUNT))
    c.check(cum.get('surfaceGapReconciliation') == 'P-Marcus-SymmetryFactor',
            'cumulative.surfaceGap',
            'surface-gap reconciliation is not recorded')
    c.check(cum.get('earlyCrossDomainPair') == 'P-Kasha-Sabatier',
            'cumulative.earlyCrossDomain',
            'early cross-domain pair is not recorded')
    c.check(cum.get('acceptedPairCount', -1) + cum.get('submittedPairCount', -1)
            == CUMULATIVE_SCREENED, 'cumulative.sum',
            'accepted + submitted does not equal the cumulative screened count')
    c.check(len(screened) + len(submitted) + len(r5_rows) == CUMULATIVE_SCREENED,
            'cumulative.rows', 'the ledger rows do not sum to 136')
    c.check(expected_accepted_pairs + expected_submitted_pairs
            == CUMULATIVE_SCREENED, 'cumulative.state.partition',
            'accepted + submitted pair counts do not partition the 136 pairs')

    # ---- actual aggregation must reproduce the cumulative numbers
    actual_outcomes = Counter()
    actual_outcomes.update(prior_status)
    actual_outcomes.update(r5_status)
    c.check(dict(zero_filled(actual_outcomes)) == CUMULATIVE_QUERY_OUTCOMES,
            'counts.cumulativeStatus',
            'actual cumulative query outcomes are %r, expected %r'
            % (dict(zero_filled(actual_outcomes)), CUMULATIVE_QUERY_OUTCOMES))
    c.check(len(prior_query_ids) + len(r5_query_ids) == CUMULATIVE_QUERY_COUNT,
            'counts.cumulativeQueries',
            'named queries over the 136 pairs are not 152')

    # ---- remaining pairs
    remaining = ledger.get('remainingPairIds') or []
    c.check(len(remaining) == CUMULATIVE_REMAINING, 'remaining.count',
            'remainingPairIds has %d entries, expected 0' % len(remaining))
    c.check(set(remaining) == set(), 'remaining.set',
            'remainingPairIds is not empty, but 136/136 pairs are covered')
    expected_remaining = [pid for pid in universe
                          if pid not in set(accepted_prior_ids)
                          and pid not in set(r5_by_id)]
    c.check(expected_remaining == [], 'remaining.derived',
            'the universe minus the 136 covered pairs is not empty')

    # ---- round history
    history = ledger.get('roundHistory') or []
    by_round = {row.get('round'): row for row in history}
    c.check(len(history) == 4, 'history.count',
            'roundHistory does not have four round rows')
    for rnd, screened_n, remaining_n, state in [
            ('R2', 10, 126, 'accepted-R2'),
            ('R3', 21, 115, 'accepted-R3'),
            ('R4', 67, 69, 'accepted-R4'),
            ('R5', CUMULATIVE_SCREENED, CUMULATIVE_REMAINING, r5_state)]:
        row = by_round.get(rnd) or {}
        c.check(row.get('screenedPairCount') == screened_n,
                'history.%s.screened' % rnd, '%s screened count drift' % rnd)
        c.check(row.get('remainingPairCount') == remaining_n,
                'history.%s.remaining' % rnd, '%s remaining count drift' % rnd)
        c.check(row.get('acceptance') == state, 'history.%s.acceptance' % rnd,
                '%s acceptance state drift (expected %r)' % (rnd, state))
    c.check(10 + 11 + 46 + R5_PAIRS == CUMULATIVE_SCREENED, 'history.sum',
            'per-round screened counts do not sum to 136')

    # ----------------------------------------------------------- frozen inputs
    c.check(sha(REGISTRY_REL) == EXPECTED_REGISTRY_SHA, 'registry.sha256',
            'legacy registry SHA-256 is not the accepted value')
    c.check(len(inventory.get('statements', [])) > 0, 'inventory.rows',
            'the R1 statement inventory is empty')
    lean_files = sum(1 for _dirpath, _dirs, files in os.walk(
        os.path.join(root, 'PhotoLean')) for name in files if name.endswith('.lean'))
    c.check(lean_files == EXPECTED_LEAN_FILES, 'photoLean.fileCount',
            'delivered Lean tree has %d files, expected %d'
            % (lean_files, EXPECTED_LEAN_FILES))
    frozen = ledger.get('frozenSnapshots') or []
    c.check(any(row.get('path') == R4_SNAPSHOT_REL
                and row.get('sha256') == EXPECTED_R4_SNAPSHOT_SHA
                for row in frozen), 'ledger.frozenSnapshot',
            'the ledger does not record the frozen R4 accepted-ledger snapshot')

    # ------------------------------------------------------------------ non-claims
    non_claims = ledger.get('nonClaims') or []
    c.check(isinstance(non_claims, list) and len(non_claims) >= 3,
            'ledger.nonClaims', 'the ledger has fewer than three non-claims')
    joined = ' '.join(str(x).lower() for x in non_claims)
    c.check('not the same as certified' in joined or 'screened is not' in joined,
            'ledger.nonClaimScreened',
            'no non-claim that screening is not certification')
    c.check('does not self-accept' in joined or 'not an acceptance' in joined
            or 'accepted only if' in joined, 'ledger.nonClaimAcceptance',
            'no non-claim that the submitted state is not an acceptance')
    c.check('submitted coverage' in joined and 'accepted coverage' in joined,
            'ledger.nonClaimSubmittedAccepted',
            'no non-claim distinguishing 136/136 submitted coverage from accepted '
            'coverage')
    c.check(isinstance(ledger.get('knownSeams'), list)
            and len(ledger.get('knownSeams')) >= 1, 'ledger.knownSeams',
            'the ledger does not record its known hash seams')
    c.check(any('cycle' in str(x).lower() for x in ledger.get('knownSeams') or []),
            'ledger.cycleNote', 'the ledger does not document the anti-cycle rule')

    # ------------------------------------------------------ package validator runs
    if not args.skip_package_validators:
        for pkg in R5_PACKAGES:
            try:
                proc = subprocess.run(
                    [sys.executable, os.path.join(root, pkg['validate'])],
                    cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    text=True, timeout=900)
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
        'accepted': expected_accepted_pairs,
        'submitted': expected_submitted_pairs,
        'r5_state': r5_state,
        'r5_rows': len(r5_rows),
        'r5_pairs': len(r5_pair_ids),
        'r5_queries': len(r5_query_ids),
        'r5_status': dict(zero_filled(r5_status)),
        'cumulative': cum.get('screenedPairCount'),
        'remaining': len(remaining),
        'queries': len(prior_query_ids) + len(r5_query_ids),
        'outcomes': dict(zero_filled(actual_outcomes)),
    })
    return 0 if not c.failed else 1


def add_provenance_checks(c, tag, qid, q):
    prov = q.get('provenance') or {}
    c.nonempty(prov.get('kind'), 'provenance.kind',
               '%s query %r has no provenance kind' % (tag, qid))
    c.nonempty(prov.get('locator'), 'provenance.locator',
               '%s query %r has no provenance locator' % (tag, qid))
    status = (q.get('outcome') or {}).get('status')
    if status == 'certified':
        c.nonempty(prov.get('certificateId'), 'provenance.certificateId',
                   '%s query %r has no certificate id' % (tag, qid))
    else:
        c.nonempty(prov.get('legacyDisposition'), 'provenance.legacyDisposition',
                   '%s query %r has no legacy disposition note' % (tag, qid))
        ref = ((q.get('outcome') or {}).get('evidence') or {}).get('searchLogRef')
        if ref:
            c.check(prov.get('locator') == ref, 'provenance.locatorBackref',
                    '%s query %r provenance locator does not match its search-log '
                    'reference' % (tag, qid))


def report(c, root, coverage, summary):
    print('R5 cumulative coverage validation')
    print('  root: %s' % root)
    print('  ledger: %s' % coverage)
    if summary:
        print('  R5 ledger state: %s' % summary['r5_state'])
        print('  R5 pairs: %d (%s)' % (summary['r5_pairs'], summary['r5_rows']))
        print('  R5 named queries: %d' % summary['r5_queries'])
        print('  R5 query outcomes: %s'
              % json.dumps(summary['r5_status'], sort_keys=True))
        print('  accepted pairs: %d' % summary['accepted'])
        print('  submitted pairs: %d' % summary['submitted'])
        print('  cumulative: %s/136 screened, %s remaining'
              % (summary['cumulative'], summary['remaining']))
        print('  named queries over the 136 pairs: %d' % summary['queries'])
        print('  cumulative query outcomes: %s'
              % json.dumps(summary['outcomes'], sort_keys=True))
    print('  checks passed: %d' % c.passed)
    print('  checks failed: %d' % len(c.failed))
    for code, message in c.failed:
        print('FAIL [%s] %s' % (code, message))
    if c.failed:
        print('RESULT: FAIL (%d failed checks)' % len(c.failed))
    else:
        print('RESULT: PASS (all R5 coverage checks passed)')
    if summary and summary['remaining'] == 0 and c.failed == []:
        print('NOTE: 136/136 is *submitted* coverage; accepted coverage is %d/136 '
              'until the R5 rows uniformly flip to %s.'
              % (summary['accepted'], ACCEPTED_R5_STATE))


if __name__ == '__main__':
    sys.exit(main())
