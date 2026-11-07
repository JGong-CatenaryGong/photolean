#!/usr/bin/env python3
"""Deterministic fail-closed validator for the R5 XD1 cross-domain-01 package.

Usage:
    python3 bounded_audit/r5/cross-domain-01/validate.py

Optional overrides (used by the fail-closed mutation tests, which work on copies):
    python3 bounded_audit/r5/cross-domain-01/validate.py --screening /tmp/x.json
    python3 bounded_audit/r5/cross-domain-01/validate.py --search-log /tmp/s.json --fragment /tmp/f.json

The validator re-derives every fact from the frozen R1 inventory, the frozen pair queue,
the accepted legacy registry, the accepted R2/R3/R4 screening packages, the package search
log, the package probe and its compile log. It does not trust the package's own counts or
prose.

It deliberately does **not** read or pin the mutable R5 cumulative coverage ledger
(`bounded_audit/coverage.json`). Prior coverage is derived from the accepted R2/R3/R4
screening packages themselves, so an integration step that writes the R5 ledger cannot break
this package validator.
"""

import argparse
import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
REL = os.path.relpath(HERE, ROOT)

EXPECTED_PAIRS = [
    'P-Marcus-Goldschmidt',
    'P-Hammond-Goldschmidt',
    'P-BEP-Goldschmidt',
    'P-Kasha-Goldschmidt',
    'P-Sabatier-Goldschmidt',
    'P-Sabatier-KashaVavilov',
    'P-Sabatier-SternVolmer',
    'P-Sabatier-QuantumYield',
    'P-Sabatier-FluorPhos',
    'P-Sabatier-EnergyGapLaw',
    'P-Sabatier-StokesShift',
    'P-Sabatier-ICvsISC',
    'P-Sabatier-Forster',
    'P-Sabatier-Einstein',
    'P-Goldschmidt-SymmetryFactor',
]
R1_WP_PAIRS = [
    'P-Marcus-Goldschmidt',
    'P-Hammond-Goldschmidt',
    'P-BEP-Goldschmidt',
    'P-Kasha-Sabatier',
    'P-Kasha-Goldschmidt',
    'P-Sabatier-Goldschmidt',
    'P-Sabatier-KashaVavilov',
    'P-Sabatier-SternVolmer',
    'P-Sabatier-QuantumYield',
    'P-Sabatier-FluorPhos',
    'P-Sabatier-EnergyGapLaw',
    'P-Sabatier-StokesShift',
    'P-Sabatier-ICvsISC',
    'P-Sabatier-Forster',
    'P-Sabatier-Einstein',
    'P-Goldschmidt-SymmetryFactor',
]
EXCLUDED_PAIR = 'P-Kasha-Sabatier'

STATUSES = ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope']
KINDS = ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition',
         'observationalEquivalence', 'distinguishability', 'refutation']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
ENDPOINT_FORMS = {'definition', 'theorem', 'theorem-lhs-predicate',
                  'theorem-rhs-predicate', 'theorem-rhs-term'}
TRANSLATION_IDS = {'identity', 'rfl-pin', 'coordinate-map', 'rat-to-real',
                   'surface-to-barrier', 'descriptor-endpoint', 'energy-window',
                   'observational-setup', 'candidate-not-total', 'none-declared'}
CHANNEL_IDS = {'intensity-ratio', 'lifetime-ratio', 'joint-intensity-lifetime',
               'rate-constant', 'barrier-height', 'quantum-yield',
               'transfer-efficiency', 'emission-energy', 'spectral-intensity',
               'zone-tag'}
PROBE_NAMESPACE = 'PhotoLean.RelationAudit.BoundedAudit.XD1.'

INV_REL = 'audit_boundary/statement-inventory.json'
QUEUE_REL = 'audit_boundary/pair-queue.json'
CLUSTER_REL = 'audit_boundary/cluster-plan.json'
BOUNDARY_REL = 'audit_boundary/BOUNDARY.md'
REGISTRY_REL = 'relation_audit/registry.json'
R2_REL = 'bounded_audit/wp-surface-01/screening.json'
R3_REL = 'bounded_audit/r3/screening.json'
R4_E1_REL = 'bounded_audit/r4/excited-01/screening.json'
R4_E2_REL = 'bounded_audit/r4/excited-02/screening.json'
R4_CI_REL = 'bounded_audit/r4/conical-01/screening.json'
SCREENING_REL = REL + '/screening.json'
SEARCH_REL = REL + '/search-log.json'
FRAGMENT_REL = REL + '/coverage-fragment.json'
PROBE_REL = REL + '/probes/XD1-probe.lean'
PROBE_LOG_REL = REL + '/probes/compile.log'
SCREENING_PATH = 'bounded_audit/r5/cross-domain-01/screening.json'
PROBE_PATH = 'bounded_audit/r5/cross-domain-01/probes/XD1-probe.lean'
PROBE_LOG_PATH = 'bounded_audit/r5/cross-domain-01/probes/compile.log'
BUILD_COMMAND = 'proofs/scripts/lake env lean ' + PROBE_PATH
EXPECTED_REGISTRY_SHA = '25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0'
EXPECTED_LEAN_FILES = 102
EXPECTED_PAIRS_N = 15
EXPECTED_ACCEPTED = 67
EXPECTED_PRIOR = [
    ('R2', R2_REL, 10),
    ('R3', R3_REL, 11),
    ('R4', R4_E1_REL, 16),
    ('R4', R4_E2_REL, 14),
    ('R4', R4_CI_REL, 16),
]


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

    def check(self, cond, code, message):
        if not cond:
            self.failures.append((code, message))

    def nonempty(self, value, code, message):
        self.check(isinstance(value, str) and value.strip() != '', code, message)

    def summary(self):
        print('R5 XD1 cross-domain-01 validation')
        print('  root: %s' % ROOT)
        print('  package: %s' % REL)
        print('  checks failed: %d' % len(self.failures))
        if self.failures:
            for code, message in self.failures:
                print('FAIL [%s] %s' % (code, message))
            print('RESULT: FAIL (%d failed checks)' % len(self.failures))
            return 1
        print('RESULT: PASS (all cross-domain-01 package checks passed)')
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


def line_contains(rel, line, name):
    """True when `name` occurs on 1-based `line` of the repository artifact `rel`."""
    path = os.path.join(ROOT, rel)
    if not os.path.exists(path):
        return False
    text = open(path, encoding='utf-8').read().splitlines()
    if not isinstance(line, int) or line < 1 or line > len(text):
        return False
    return name in text[line - 1]


def _status_counts(queries):
    counts = {}
    for q in queries:
        status = q.get('outcome', {}).get('status')
        counts[status] = counts.get(status, 0) + 1
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--screening', default=SCREENING_REL)
    parser.add_argument('--search-log', default=SEARCH_REL)
    parser.add_argument('--fragment', default=FRAGMENT_REL)
    args = parser.parse_args()

    c = Checker()
    required = [INV_REL, QUEUE_REL, CLUSTER_REL, BOUNDARY_REL, REGISTRY_REL,
                R2_REL, R3_REL, R4_E1_REL, R4_E2_REL, R4_CI_REL,
                args.screening, args.search_log, args.fragment,
                PROBE_REL, PROBE_LOG_REL]
    for rel in required:
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
    r3 = load_rel(R3_REL)
    r4_e1 = load_rel(R4_E1_REL)
    r4_e2 = load_rel(R4_E2_REL)
    r4_ci = load_rel(R4_CI_REL)
    search_log = load_rel(args.search_log)
    fragment = load_rel(args.fragment)
    probe_text = read_rel(PROBE_REL)
    probe_log = read_rel(PROBE_LOG_REL)

    inv_by_id = {row['id']: row for row in inv['statements']}
    dangling_ids = {d['id'] for d in inv.get('legacyDanglingStatements', [])}
    queue_by_id = {row['pairId']: row for row in queue['pairs']}
    all_pairs = [row['pairId'] for row in queue['pairs']]
    probe_axioms = parse_probe_axioms(probe_log)

    # Accepted pair sets come from the accepted packages, not from the mutable R5 ledger.
    prior_packages = [
        ('R2', r2, R2_REL, 10),
        ('R3', r3, R3_REL, 11),
        ('R4', r4_e1, R4_E1_REL, 16),
        ('R4', r4_e2, R4_E2_REL, 14),
        ('R4', r4_ci, R4_CI_REL, 16),
    ]
    prior_sets = []
    for round_name, pkg, rel, expected in prior_packages:
        ids = [p.get('pairId') for p in pkg.get('pairs', [])]
        c.check(len(ids) == expected, 'prior.%s.count' % round_name,
                '%s carries %d pairs, expected %d' % (rel, len(ids), expected))
        c.check(len(ids) == len(set(ids)), 'prior.%s.duplicate' % round_name,
                '%s has a duplicate pair' % rel)
        prior_sets.append(set(ids))
    accepted_pairs = set().union(*prior_sets)
    c.check(len(accepted_pairs) == EXPECTED_ACCEPTED, 'prior.total',
            'accepted R2/R3/R4 pair union is %d, expected %d'
            % (len(accepted_pairs), EXPECTED_ACCEPTED))
    c.check(EXCLUDED_PAIR in accepted_pairs, 'prior.excludedPresent',
            'the accepted package set does not contain the excluded P-Kasha-Sabatier pair')
    c.check(R2_REL in [p[2] for p in prior_packages], 'prior.r2', 'R2 package is not read')

    # ---------------------------------------------------------------- vocabulary
    c.check(screening.get('schemaVersion') == '1.0.0', 'schema.version',
            'unexpected schemaVersion')
    c.check(screening.get('artifactKind') == 'bounded-screening-package',
            'schema.kind', 'unexpected artifactKind')
    c.check(screening.get('round') == 'R5', 'schema.round', 'unexpected round')
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
                     (REGISTRY_REL, 'legacyRegistrySha256')]:
        actual = sha_file(os.path.join(ROOT, rel))
        c.check(snap.get(key) == actual, 'snapshot.%s' % key,
                '%s hash drift: %s != %s' % (rel, snap.get(key), actual))
    c.check(snap.get('legacyRegistrySha256') == EXPECTED_REGISTRY_SHA,
            'snapshot.registryPinned', 'legacy registry hash is not the accepted hash')
    # The mutable R5 ledger must not be pinned by this package.
    c.check('coverageLedgerSha256' not in snap, 'snapshot.coveragePinned',
            'the snapshot pins a mutable coverage ledger')
    cov_ref = screening.get('coverageReference', {})
    c.check(cov_ref.get('pin') in (None, 'not-pinned'), 'coverageReference.pin',
            'the coverage reference must declare itself unpinned')
    c.check('sha256' not in cov_ref or cov_ref.get('pin') == 'not-pinned',
            'coverageReference.sha256',
            'the coverage reference must not carry a mutable ledger hash')

    snap_prior = {p.get('path'): p for p in snap.get('priorPackages', [])}
    c.check(len(snap_prior) == len(EXPECTED_PRIOR), 'snapshot.priorCount',
            'snapshot prior-package count drift')
    for round_name, rel, expected in EXPECTED_PRIOR:
        p = snap_prior.get(rel)
        c.check(p is not None, 'snapshot.priorMissing',
                'snapshot does not list the accepted package %s' % rel)
        if p is not None:
            c.check(p.get('round') == round_name, 'snapshot.priorRound',
                    'snapshot prior-package round drift for %s' % rel)
            c.check(p.get('pairCount') == expected, 'snapshot.priorPairs',
                    'snapshot prior-package pair count drift for %s' % rel)
            c.check(p.get('sha256') == sha_file(os.path.join(ROOT, rel)),
                    'snapshot.priorHash',
                    'snapshot prior-package hash drift for %s' % rel)
    c.check(snap.get('priorAcceptedPairCount') == EXPECTED_ACCEPTED,
            'snapshot.priorAcceptedCount',
            'snapshot prior accepted-pair count drift')
    c.nonempty(snap.get('priorCoverageSource'), 'snapshot.priorSource',
               'snapshot has no prior-coverage provenance')
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
    c.check(search_ref.get('sha256') == sha_file(os.path.join(ROOT, args.search_log)),
            'searchLogReference.sha256', 'search-log hash drift')
    probe_ref = screening.get('probeReference', {})
    c.check(probe_ref.get('sha256') == sha_file(os.path.join(ROOT, PROBE_REL)),
            'probeReference.sha256', 'probe hash drift')
    c.check(probe_ref.get('log') == PROBE_LOG_PATH, 'probeReference.log',
            'probe log path drift')
    c.check(probe_ref.get('role') == 'candidate-evidence', 'probeReference.role',
            'this package probe is candidate evidence, not a certified-outcome probe')
    c.check(probe_ref.get('buildCommand') == BUILD_COMMAND,
            'probeReference.buildCommand', 'probe reference build command drift')

    # ---------------------------------------------------------------- pair coverage
    work = screening.get('workPackage', {})
    c.check(work.get('id') == 'XD1-CROSS-DOMAIN-01', 'workPackage.id',
            'work package id drift')
    c.check(work.get('pairIds') == EXPECTED_PAIRS, 'workPackage.pairIds',
            'work package pair list is not the approved fifteen')
    c.check(work.get('pairCount') == EXPECTED_PAIRS_N, 'workPackage.pairCount',
            'work package pair count drift')
    r1wp = work.get('r1WorkPackage', {})
    c.check(r1wp.get('id') == 'WP-cross-domain-screening-01', 'workPackage.r1Id',
            'R1 work package id drift')
    c.check(r1wp.get('pairIds') == R1_WP_PAIRS, 'workPackage.r1Pairs',
            'R1 work package pair list drift')
    c.check(set(r1wp.get('pairIds', [])) - set(EXPECTED_PAIRS) == {EXCLUDED_PAIR},
            'workPackage.difference',
            'the package is not exactly the R1 work package minus the excluded accepted pair')
    c.check(EXCLUDED_PAIR not in work.get('pairIds', []), 'workPackage.excluded',
            'the package rescreens the accepted P-Kasha-Sabatier pair')
    c.check(not (set(work.get('pairIds', [])) & accepted_pairs),
            'workPackage.acceptedOverlap',
            'the package pair list overlaps the accepted R2/R3/R4 pairs')

    # The R1 cluster plan must still assign these fifteen to the R1 work package.
    plan_wp = {}
    for cl in cluster.get('clusters', []):
        for wp in cl.get('workPackages', []):
            plan_wp[wp.get('id')] = wp
    c.check('WP-cross-domain-screening-01' in plan_wp, 'cluster.wpMissing',
            'the R1 cluster plan has no WP-cross-domain-screening-01')
    if 'WP-cross-domain-screening-01' in plan_wp:
        c.check(plan_wp['WP-cross-domain-screening-01'].get('pairIds') == R1_WP_PAIRS,
                'cluster.wpPairs', 'the R1 cluster-plan pair list drift')
        c.check(set(plan_wp['WP-cross-domain-screening-01'].get('pairIds', [])) -
                set(EXPECTED_PAIRS) == {EXCLUDED_PAIR}, 'cluster.difference',
                'the assigned fifteen are not the R1 work package minus P-Kasha-Sabatier')

    pairs = screening.get('pairs', [])
    pair_ids = [p.get('pairId') for p in pairs]
    c.check(len(pair_ids) == len(set(pair_ids)), 'pairs.duplicate',
            'duplicate pair id in screening package')
    c.check(set(pair_ids) == set(EXPECTED_PAIRS), 'pairs.coverage',
            'screening pair set is not exactly the approved fifteen')
    c.check(len(pair_ids) == EXPECTED_PAIRS_N, 'pairs.count',
            'screening pair count is not fifteen')
    c.check(not (set(pair_ids) & accepted_pairs), 'pairs.acceptedOverlap',
            'screening pairs overlap the accepted R2/R3/R4 pairs')
    c.check(EXCLUDED_PAIR not in pair_ids, 'pairs.excluded',
            'the accepted P-Kasha-Sabatier pair is present')

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
                    'pair.cluster',
                    'pair %r primary cluster does not match the R1 queue' % pid)
            c.check(pair.get('primaryCluster') == 'cross-domain-screening',
                    'pair.clusterName',
                    'pair %r is not in the cross-domain-screening cluster' % pid)
        qids = pair.get('queryIds', [])
        c.check(isinstance(qids, list) and len(qids) >= 1, 'pair.noQuery',
                'pair %r has no named query or outOfScope record' % pid)
        c.check(qids == [q.get('queryId') for q in pair.get('queries', [])],
                'pair.queryIds', 'pair %r queryIds do not match its query rows' % pid)
        c.check(len(qids) == len(set(qids)), 'pair.queryDuplicate',
                'pair %r has duplicate query ids' % pid)
        for q in pair.get('queries', []):
            qid = q.get('queryId')
            all_query_ids.append(qid)
            query_by_id[qid] = q
            c.check(q.get('pairId') == pid, 'query.pairId',
                    'query %r pairId does not match its pair row' % qid)

    c.check(len(all_query_ids) == len(set(all_query_ids)), 'queries.duplicate',
            'duplicate query id in screening package')
    c.check(len(all_query_ids) == EXPECTED_PAIRS_N, 'queries.count',
            'query count is %d, expected %d' % (len(all_query_ids), EXPECTED_PAIRS_N))

    # ---------------------------------------------------------------- per-query checks
    non_certified = []
    certified_decls = {}
    candidate_decls = {}
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
                    c.check(line_contains(row['sourceArtifact'], row['sourceLine'],
                                          short_name(row['declaration'])),
                            'endpoint.sourceLine',
                            'query %r %s declaration is not at its declared source line'
                            % (qid, side))
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
            lib_ctx = screening.get('contextLibrary', {}).get(ctx_id, {})
            c.check(ctx.get('fields') == lib_ctx.get('fields'), 'context.fieldsMatch',
                    'query %r shared-context fields drift from the library' % qid)
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
            c.check(isinstance(pids, list), 'premise.ids',
                    'query %r premiseIds is not a list' % qid)
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
                c.check('True' in (prem.get('predicate') or ''),
                        'premise.emptyPredicate',
                        'query %r has no premise ids but its predicate is not True' % qid)

            # scope and snapshot
            scope = q.get('scope', {})
            sid = scope.get('id')
            c.check(sid in screening.get('scopeLibrary', {}), 'scope.missing',
                    'query %r scope %r is not in the scope library' % (qid, sid))
            lib_scope = screening.get('scopeLibrary', {}).get(sid, {})
            c.check(scope.get('description') == lib_scope.get('description'),
                    'scope.descriptionMatch',
                    'query %r scope description drifts from the library' % qid)
            c.check(scope.get('domain') == lib_scope.get('domain'),
                    'scope.domainMatch',
                    'query %r scope domain drifts from the library' % qid)
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
                c.check(ch.get('id') in CHANNEL_IDS, 'channel.idKnown',
                        'query %r channel id %r is not a known channel'
                        % (qid, ch.get('id')))
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
                c.check(evidence.get('type') == 'xd1-probe-certificate',
                        'evidence.type',
                        'query %r certified evidence has unsupported type %r'
                        % (qid, evidence.get('type')))
                c.check(evidence.get('kind') == kind, 'evidence.kindMatch',
                        'query %r evidence kind %r does not match expectedKind %r'
                        % (qid, evidence.get('kind'), kind))
                footprint = set(evidence.get('axiomFootprint', []))
                c.check(footprint <= ALLOWED_AXIOMS, 'evidence.axioms',
                        'query %r evidence footprint contains disallowed axioms: %s'
                        % (qid, sorted(footprint - ALLOWED_AXIOMS)))
                c.check(set(evidence.get('allowedAxioms', [])) == ALLOWED_AXIOMS,
                        'evidence.allowedAxioms',
                        'query %r evidence allowed-axiom list drift' % qid)
                probe = evidence.get('probe', {})
                c.check(probe.get('path') == PROBE_PATH, 'evidence.probePath',
                        'query %r probe path drift' % qid)
                c.check(probe.get('sha256') == sha_file(os.path.join(ROOT, PROBE_REL)),
                        'evidence.probeHash', 'query %r probe source hash drift' % qid)
                decl = probe.get('declaration', '')
                certified_decls[decl] = qid
                c.check(decl.startswith(PROBE_NAMESPACE), 'evidence.probeDecl',
                        'query %r probe declaration is outside the XD1 namespace' % qid)
                short = short_name(decl)
                c.check(re.search(r'\bdef\s+%s\b|\btheorem\s+%s\b'
                                  % (re.escape(short), re.escape(short)),
                                  probe_text) is not None,
                        'evidence.probeDeclMissing',
                        'query %r probe declaration is not in the probe source' % qid)
                kind_thm = probe.get('kindCheckTheorem', '')
                c.check(re.search(r'\btheorem\s+%s\b' % re.escape(short_name(kind_thm)),
                                  probe_text) is not None,
                        'evidence.probeKindMissing',
                        'query %r probe kind-check theorem is missing' % qid)
                c.check(kind_thm == decl + '_kind', 'evidence.kindCheckName',
                        'query %r kind-check theorem is not <declaration>_kind' % qid)
                c.check(probe.get('buildCommand') == BUILD_COMMAND,
                        'evidence.probeBuild', 'query %r probe build command drift' % qid)
                c.check(probe.get('log') == PROBE_LOG_PATH, 'evidence.probeLog',
                        'query %r probe log path drift' % qid)
                axioms = probe_axioms.get(decl)
                c.check(axioms is not None, 'evidence.probeAxiomLog',
                        'query %r probe declaration has no axiom print-out' % qid)
                if axioms is not None:
                    c.check(axioms == footprint, 'evidence.probeAxiomMatch',
                            'query %r probe axiom print-out %r does not match the '
                            'declared footprint %r'
                            % (qid, sorted(axioms), sorted(footprint)))
                    c.check(axioms <= ALLOWED_AXIOMS, 'evidence.probeAxiomDisallowed',
                            'query %r probe certificate has disallowed axioms: %s'
                            % (qid, sorted(axioms - ALLOWED_AXIOMS)))
                c.nonempty(evidence.get('justification'), 'evidence.justification',
                           'query %r certified evidence has no justification' % qid)
            elif status in {'unresolved', 'notEstablished'}:
                non_certified.append((qid, status, evidence))
                c.check(evidence.get('type') == 'scoped-search',
                        'evidence.searchType',
                        'query %r status %s requires a scoped-search evidence record'
                        % (qid, status))
                c.nonempty(evidence.get('searchLogRef'), 'evidence.searchRef',
                           'query %r status %s has no search-log reference' % (qid, status))
                c.nonempty(evidence.get('candidateSummary'),
                           'evidence.candidateSummary',
                           'query %r status %s has no candidate metadata summary'
                           % (qid, status))
                cp = evidence.get('candidateProbe')
                if cp is not None:
                    c.check(cp.get('path') == PROBE_PATH, 'evidence.candidateProbePath',
                            'query %r candidate probe path drift' % qid)
                    c.check(cp.get('sha256') == sha_file(os.path.join(ROOT, PROBE_REL)),
                            'evidence.candidateProbeHash',
                            'query %r candidate probe hash drift' % qid)
                    decl = cp.get('declaration', '')
                    candidate_decls[decl] = qid
                    c.check(decl.startswith(PROBE_NAMESPACE),
                            'evidence.candidateProbeDecl',
                            'query %r candidate probe declaration is outside XD1' % qid)
                    short = short_name(decl)
                    c.check(re.search(r'\btheorem\s+%s\b' % re.escape(short),
                                      probe_text) is not None,
                            'evidence.candidateProbeMissing',
                            'query %r candidate probe declaration is missing' % qid)
                    c.check(cp.get('buildCommand') == BUILD_COMMAND,
                            'evidence.candidateProbeBuild',
                            'query %r candidate probe build command drift' % qid)
                    c.check(cp.get('log') == PROBE_LOG_PATH,
                            'evidence.candidateProbeLog',
                            'query %r candidate probe log path drift' % qid)
                    axioms = probe_axioms.get(decl)
                    c.check(axioms is not None, 'evidence.candidateProbeAxiomLog',
                            'query %r candidate declaration has no axiom print-out' % qid)
                    if axioms is not None:
                        c.check(axioms == set(cp.get('axiomFootprint', [])),
                                'evidence.candidateProbeAxiomMatch',
                                'query %r candidate axiom print-out %r does not match '
                                'the declared footprint %r'
                                % (qid, sorted(axioms), cp.get('axiomFootprint')))
                        c.check(axioms <= ALLOWED_AXIOMS,
                                'evidence.candidateProbeAxiomDisallowed',
                                'query %r candidate declaration has disallowed axioms: %s'
                                % (qid, sorted(axioms - ALLOWED_AXIOMS)))
            elif status == 'outOfScope':
                non_certified.append((qid, status, evidence))
                c.check(evidence.get('type') == 'jurisdiction',
                        'evidence.jurisdictionType',
                        'query %r outOfScope requires a jurisdiction evidence record' % qid)
                c.nonempty(evidence.get('searchLogRef'), 'evidence.searchRef',
                           'query %r outOfScope has no search-log reference' % qid)
                c.nonempty(evidence.get('jurisdictionRationale'),
                           'evidence.jurisdictionRationale',
                           'query %r outOfScope has no statement-level rationale' % qid)
                c.nonempty(evidence.get('statementLevelReason'),
                           'evidence.jurisdictionStatement',
                           'query %r outOfScope has no statement-level reason' % qid)
            elif status == 'refuted':
                c.check(evidence.get('type') == 'refutation-certificate',
                        'evidence.refutationType',
                        'query %r refuted requires a refutation certificate' % qid)
                c.check(evidence.get('kind') == 'refutation',
                        'evidence.refutationKind',
                        'query %r refuted evidence kind is not refutation' % qid)
                c.nonempty(evidence.get('counterexampleWitness'),
                           'evidence.counterexample',
                           'query %r refuted has no explicit counterexample witness' % qid)

    # ---------------------------------------------------------------- probe gates
    c.check(set(certified_decls) == set(), 'probe.certifiedDeclarations',
            'this package has no certified outcomes but declares certified probe evidence')
    c.check(probe_ref.get('declarationCount') == len(probe_axioms),
            'probe.declarationCount', 'probe reference declaration count drift')
    c.check(set(probe_ref.get('declarations', [])) == set(probe_axioms),
            'probe.declarations', 'probe reference declarations do not match the axiom log')
    c.check(set(candidate_decls) <= set(probe_axioms), 'probe.candidateCoverage',
            'a candidate declaration is not in the probe axiom log')
    c.check(set(candidate_decls) == set(probe_axioms), 'probe.candidateComplete',
            'candidate declarations %r do not cover the probe axiom log %r'
            % (sorted(candidate_decls), sorted(probe_axioms)))
    forbidden = re.compile(r'sorry|admit|^[ \t]*(private[ \t]+|protected[ \t]+)?'
                           r'(axiom|constant)([ \t]|$)', re.M)
    c.check(forbidden.search(probe_text) is None, 'probe.forbiddenToken',
            'probe source contains a forbidden token')
    c.check(probe_log.strip() != '', 'probe.logEmpty', 'probe compile log is empty')
    for decl in probe_axioms:
        c.check(probe_axioms[decl] <= ALLOWED_AXIOMS, 'probe.axioms',
                'probe declaration %r carries disallowed axioms %s'
                % (decl, sorted(probe_axioms[decl] - ALLOWED_AXIOMS)))
    prints = re.findall(r'#print axioms\s+(\S+)', probe_text)
    c.check(len(prints) == len(probe_axioms), 'probe.printCount',
            'probe has %d #print axioms lines but the log has %d blocks'
            % (len(prints), len(probe_axioms)))
    for name in prints:
        c.check(name in probe_axioms, 'probe.printMatch',
                'probe print-out for %r is missing from the compile log' % name)

    # ---------------------------------------------------------------- search log
    entries = search_log.get('entries', [])
    c.check(search_log.get('artifactKind') == 'bounded-search-log', 'search.kind',
            'search-log artifactKind drift')
    c.check(search_log.get('round') == 'R5', 'search.round', 'search-log round drift')
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
                    'search.status',
                    'search entry %r status does not match its query' % sid)
            c.check(q.get('outcome', {}).get('evidence', {}).get('searchLogRef') == sid,
                    'search.backref',
                    'query %r does not point back to search entry %r' % (qid, sid))
        c.check(e.get('scope') in screening.get('scopeLibrary', {}), 'search.scope',
                'search entry %r has unknown scope' % sid)
        c.check(e.get('snapshot') == snap.get('id'), 'search.entrySnapshot',
                'search entry %r snapshot drift' % sid)
        stmts = e.get('searchedStatements')
        c.check(isinstance(stmts, list) and len(stmts) >= 1,
                'search.searchedStatements',
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
                        'search entry %r dependency artifact is missing: %s'
                        % (sid, art))
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
    c.check(search_ref.get('entryCount') == len(entries),
            'searchLogReference.entryCount', 'search-log reference entry count drift')
    c.check(search_log.get('counts', {}).get('entries') == len(entries),
            'counts.searchEntries', 'search-log entry count drift')

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
            'kind counts drift: %r != %r'
            % (declared.get('byExpectedKind'), kind_counts))
    for status in STATUSES:
        c.check(declared.get(status) == status_counts.get(status, 0),
                'counts.%s' % status, 'declared %s count drift' % status)

    # ---------------------------------------------------------------- coverage fragment
    fw = fragment.get('workPackage', {})
    c.check(fragment.get('artifactKind') == 'bounded-coverage-fragment',
            'fragment.kind', 'coverage fragment artifactKind drift')
    c.check(fragment.get('round') == 'R5', 'fragment.round',
            'coverage fragment round drift')
    c.check(fragment.get('packageState') == 'submitted-R5-pending-review',
            'fragment.state', 'coverage fragment package state drift')
    c.check(fw.get('id') == 'XD1-CROSS-DOMAIN-01', 'fragment.id',
            'coverage fragment work-package id drift')
    c.check(fw.get('path') == SCREENING_PATH, 'fragment.path',
            'coverage fragment screening path drift')
    c.check(fw.get('pairCount') == EXPECTED_PAIRS_N, 'fragment.pairCount',
            'coverage fragment pair count drift')
    c.check(fw.get('sha256') == sha_file(os.path.join(ROOT, args.screening)),
            'fragment.sha', 'coverage fragment screening hash drift')
    c.check(fw.get('r1WorkPackage') == 'WP-cross-domain-screening-01',
            'fragment.r1wp', 'coverage fragment R1 work-package id drift')
    c.check(fw.get('excludedAcceptedPair') == EXCLUDED_PAIR,
            'fragment.excluded', 'coverage fragment excluded-pair drift')
    q_by_pair_row = {p['pairId']: p for p in pairs}
    f_pairs = [p.get('pairId') for p in fragment.get('pairs', [])]
    c.check(f_pairs == pair_ids, 'fragment.pairs',
            'coverage fragment pairs do not match the screening pairs')
    for fp in fragment.get('pairs', []):
        src = q_by_pair_row.get(fp.get('pairId'))
        if src is None:
            continue
        qq = [q for p in pairs if p['pairId'] == fp['pairId'] for q in p['queries']]
        c.check(fp.get('queryCount') == len(qq), 'fragment.queryCount',
                'coverage fragment query count for %r drift' % fp.get('pairId'))
        c.check(fp.get('byStatus') == _status_counts(qq), 'fragment.byStatus',
                'coverage fragment status counts for %r drift' % fp.get('pairId'))
        c.check(fp.get('theories') == src['theories'], 'fragment.theories',
                'coverage fragment theories for %r drift' % fp.get('pairId'))
        c.check(fp.get('primaryCluster') == src.get('primaryCluster'),
                'fragment.cluster',
                'coverage fragment cluster for %r drift' % fp.get('pairId'))
    fcounts = fragment.get('counts', {})
    c.check(fcounts.get('pairs') == len(pairs), 'fragment.counts.pairs',
            'coverage fragment pair count drift')
    c.check(fcounts.get('queries') == len(all_query_ids), 'fragment.counts.queries',
            'coverage fragment query count drift')
    c.check(fcounts.get('byStatus') == status_counts, 'fragment.counts.byStatus',
            'coverage fragment status counts drift')
    c.check(fcounts.get('screenedDelta') == EXPECTED_PAIRS_N,
            'fragment.counts.delta', 'coverage fragment screened delta drift')
    ow = fragment.get('overlapWithAccepted', {})
    c.check(ow.get('intersection') == [], 'fragment.overlap',
            'coverage fragment overlaps the accepted pairs')
    c.check(ow.get('acceptedScreenedPairCount') == len(accepted_pairs),
            'fragment.acceptedCount',
            'coverage fragment accepted-pair count drift')
    c.check(fragment.get('universe', {}).get('pairCount') == len(all_pairs),
            'fragment.universe', 'coverage fragment universe pair count drift')
    c.check(fragment.get('universe', {}).get('sourceSha256') ==
            sha_file(os.path.join(ROOT, QUEUE_REL)), 'fragment.universeHash',
            'coverage fragment universe hash drift')

    # ---------------------------------------------------------------- non-claims
    c.check(isinstance(screening.get('nonClaims'), list)
            and len(screening.get('nonClaims')) >= 1, 'nonClaims.missing',
            'screening package has no non-claims statement')
    c.check(isinstance(search_log.get('nonClaims'), list)
            and len(search_log.get('nonClaims')) >= 1, 'search.nonClaims',
            'search log has no non-claims statement')

    return c.summary()


if __name__ == '__main__':
    sys.exit(main())
