#!/usr/bin/env python3
"""Deterministic fail-closed validator for the R5 XD2 cross-domain screening package.

Usage:
    python3 bounded_audit/r5/cross-domain-02/validate.py

Optional overrides (used by the fail-closed mutation tests, which work on copies in /tmp):
    python3 bounded_audit/r5/cross-domain-02/validate.py --screening /tmp/x.json
    python3 bounded_audit/r5/cross-domain-02/validate.py --search-log /tmp/s.json --fragment /tmp/f.json

What this validator re-derives, independently of the package's own counts and prose:

  * the frozen R1 universe (inventory, pair queue, cluster plan, boundary) and the accepted
    legacy registry, by SHA-256;
  * the exact nine assigned pairs and their queue rows;
  * every endpoint field, source line and source hash from the frozen inventory;
  * the semantic completeness of every query (question, rationale, context, translations,
    premises, scope, versions, provenance, falsification condition, channels);
  * that every query carries exactly one of the five outcomes and that the package claims no
    `certified`/`refuted` outcome and therefore ships no Lean certificate;
  * the statement-level jurisdiction facts for every pair: a signature scan over both statement
    authorities, both import closures, and the legacy pair disposition;
  * the one-to-one correspondence between the non-certified outcomes and the scoped search log,
    including the per-entry commands and the remaining gap;
  * the coverage fragment as a pure submission snapshot.

Prior coverage is derived from the five accepted screening packages themselves (R2 wp-surface-01,
R3 r3, R4 excited-01, R4 excited-02, R4 conical-01). This validator deliberately never opens and
never pins the mutable R5 cumulative ledger `bounded_audit/coverage.json`: an integration step
that appends the R5 entries must not be able to break this package validator, and this package
must not be able to pin a ledger that later changes.
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
    'P-Goldschmidt-KashaVavilov',
    'P-Goldschmidt-SternVolmer',
    'P-Goldschmidt-QuantumYield',
    'P-Goldschmidt-FluorPhos',
    'P-Goldschmidt-EnergyGapLaw',
    'P-Goldschmidt-StokesShift',
    'P-Goldschmidt-ICvsISC',
    'P-Goldschmidt-Forster',
    'P-Goldschmidt-Einstein',
]
PARTNERS = {
    'P-Goldschmidt-KashaVavilov': 'KashaVavilov',
    'P-Goldschmidt-SternVolmer': 'SternVolmer',
    'P-Goldschmidt-QuantumYield': 'QuantumYield',
    'P-Goldschmidt-FluorPhos': 'FluorPhos',
    'P-Goldschmidt-EnergyGapLaw': 'EnergyGapLaw',
    'P-Goldschmidt-StokesShift': 'StokesShift',
    'P-Goldschmidt-ICvsISC': 'ICvsISC',
    'P-Goldschmidt-Forster': 'Forster',
    'P-Goldschmidt-Einstein': 'Einstein',
}

STATUSES = ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope']
KINDS = ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition',
         'observationalEquivalence', 'distinguishability', 'refutation']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
ENDPOINT_FORMS = {'definition', 'theorem', 'theorem-lhs-predicate', 'theorem-rhs-predicate',
                  'theorem-rhs-term'}
TRANSLATION_IDS = {'identity', 'rfl-pin', 'coordinate-map', 'rat-to-real', 'surface-to-barrier',
                   'descriptor-endpoint', 'energy-window', 'observational-setup',
                   'candidate-not-total', 'none-declared'}

# Independent copies of the jurisdiction scan vocabulary. They are hard-coded here on purpose:
# a tampered `jurisdictionEvidence` block in screening.json cannot relax the scan.
GOLDSCHMIDT_TOKENS = [
    'tolFac', 'latticeOf', 'idealAO', 'idealA', 'rAMin', 'rAMax', 'InBand',
    'GoldschmidtConforms', 'goldschmidtZone', 'GoldschmidtZone', 'gapA', 'classicLo',
    'classicHi', 'tetragonalHi', 'tauGoldschmidt', 'RadiusMatch', 'chiTol',
    'Substitutable', 'ChargeBalanced', 'isovalent',
]
PARTNER_TOKENS = {
    'KashaVavilov': ['SpecSame', 'fluoYield', 'emitYield', 'upperYield', 'rateData',
                     'specFrac', 'kashaRule', 'vavilovAt', 'VavilovAt', 'VavilovUpTo',
                     'lossless', 'KashaRule', 'radBranch', 'icBranch', 'cascade'],
    'SternVolmer': ['dynDecay', 'svRatioDyn', 'tauRatioDyn', 'svRatioStat', 'tauRatioStat',
                    'KSV', 'svRatioBoth', 'svRatioOf', 'tauRatioOf', 'LifetimeTracks',
                    'svZoneQ', 'SVZone', 'Mech'],
    'QuantumYield': ['totalRate', 'yieldOf', 'tauOf', 'QYData', 'sum_yieldOf_eq_one'],
    'FluorPhos': ['s1Decay', 'phiF', 'iscBranch', 't1BranchP', 'phiP', 'FPZone', 'fpZoneQ',
                  'FPData', 'crossover_isc'],
    'EnergyGapLaw': ['nrBarrier', 'nrRate', 'InvertedGap', 'lnRate', 'eglTangent', 'egZoneQ',
                     'EGZone', 'aromaticSeries', 'secant_slope'],
    'StokesShift': ['s0Surface', 's1Surface', 'absEnergy', 'emEnergy', 'stokesShift',
                    'SSZone', 'ssZoneQ', 'mirror_midpoint', 'emission_window'],
    'ICvsISC': ['fcBarrier', 'icRate', 'iscRate', 'rate_ratio_eq', 'log_rate_ratio',
                'isc_dominates_iff', 'spin_discount', 'FCData', 'hso_zero_isc_absent',
                'barrier_diff'],
    'Forster': ['kappaSq', 'fretRate', 'fretEff6', 'fretEff', 'r0six', 'kappaConvention',
                'fret_blind_spot'],
    'Einstein': ['radFactor', 'aOfB', 'b12OfB21', 'fOfA', 'aOfInt', 'tauR',
                 'detailed_balance', 'degeneracy_roundtrip', 'af_roundtrip'],
}

INV_REL = 'audit_boundary/statement-inventory.json'
QUEUE_REL = 'audit_boundary/pair-queue.json'
CLUSTER_REL = 'audit_boundary/cluster-plan.json'
BOUNDARY_REL = 'audit_boundary/BOUNDARY.md'
REGISTRY_REL = 'relation_audit/registry.json'
LEDGER_REL = 'bounded_audit/coverage.json'
ACCEPTED_PACKAGES = [
    ('R2', 'WP-SURFACE-01', 'bounded_audit/wp-surface-01/screening.json', 10),
    ('R3', 'R3-QUENCH-01', 'bounded_audit/r3/screening.json', 11),
    ('R4', 'R4-E1-EXCITED-01', 'bounded_audit/r4/excited-01/screening.json', 16),
    ('R4', 'WP-excited-state-kinetics-02', 'bounded_audit/r4/excited-02/screening.json', 14),
    ('R4', 'WP-conical-intersection-01', 'bounded_audit/r4/conical-01/screening.json', 16),
]
SCREENING_REL = REL + '/screening.json'
SEARCH_REL = REL + '/search-log.json'
FRAGMENT_REL = REL + '/coverage-fragment.json'
REPORT_REL = REL + '/REPORT.md'
GATES_REL = REL + '/evidence/gates.log'
EXPECTED_REGISTRY_SHA = '25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0'
EXPECTED_LEAN_FILES = 102
EXPECTED_PRIOR = 67
EXPECTED_PAIRS_N = 9
EXPECTED_QUERIES_N = 11
PROBE_NAMESPACE = None  # this package ships no probe

READ_PATHS = []


def sha_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def read_rel(rel):
    """Read a repository artifact, refusing the mutable R5 cumulative ledger."""
    if os.path.abspath(os.path.join(ROOT, rel)) == os.path.abspath(
            os.path.join(ROOT, LEDGER_REL)):
        raise AssertionError('the validator must never open the mutable R5 ledger')
    path = os.path.join(ROOT, rel)
    READ_PATHS.append(os.path.normpath(path))
    with open(path, encoding='utf-8') as fh:
        return fh.read()


def load_rel(rel):
    return json.loads(read_rel(rel))


class Checker:
    def __init__(self):
        self.failures = []

    def check(self, cond, code, message):
        if not cond:
            self.failures.append((code, message))

    def nonempty(self, value, code, message):
        self.check(isinstance(value, str) and value.strip() != '', code, message)

    def summary(self):
        print('R5 WP-cross-domain-screening-02 validation')
        print('  root: %s' % ROOT)
        print('  package: %s' % REL)
        print('  checks failed: %d' % len(self.failures))
        if self.failures:
            for code, message in self.failures:
                print('FAIL [%s] %s' % (code, message))
            print('RESULT: FAIL (%d failed checks)' % len(self.failures))
            return 1
        print('RESULT: PASS (all cross-domain-02 package checks passed)')
        return 0


def short_name(decl):
    return decl.rsplit('.', 1)[-1]


def line_contains(rel, line, name):
    path = os.path.join(ROOT, rel)
    if not os.path.exists(path):
        return False
    text = read_rel(rel).splitlines()
    if not isinstance(line, int) or line < 1 or line > len(text):
        return False
    return name in text[line - 1]


def status_counts(queries):
    counts = {}
    for q in queries:
        status = q.get('outcome', {}).get('status')
        counts[status] = counts.get(status, 0) + 1
    return counts


def theory_signatures(inv, theory):
    return [(row['id'], row['sourceSignature'])
            for row in inv['statements'] if row['theory'] == theory]


def token_hits(tokens, rows):
    found = []
    for token in tokens:
        pattern = re.compile(r'\b' + re.escape(token) + r'\b')
        matched = [rid for rid, sig in rows if pattern.search(sig)]
        if matched:
            found.append(token)
    return found


def import_closure(theory):
    """Non-own modules a theory imports, read from the delivered `^import` lines."""
    modules = set()
    directory = os.path.join(ROOT, 'PhotoLean', theory)
    if not os.path.isdir(directory):
        return modules
    own_prefix = 'PhotoLean.' + theory
    for name in sorted(os.listdir(directory)):
        if not name.endswith('.lean'):
            continue
        text = read_rel('PhotoLean/%s/%s' % (theory, name))
        for line in text.splitlines():
            m = re.match(r'^import\s+(\S+)\s*$', line)
            if not m:
                continue
            module = m.group(1)
            if module == 'Mathlib' or module == own_prefix or \
                    module.startswith(own_prefix + '.'):
                continue
            modules.add(module)
    return modules


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--screening', default=SCREENING_REL)
    parser.add_argument('--search-log', default=SEARCH_REL)
    parser.add_argument('--fragment', default=FRAGMENT_REL)
    args = parser.parse_args()

    c = Checker()
    required = [INV_REL, QUEUE_REL, CLUSTER_REL, BOUNDARY_REL, REGISTRY_REL,
                args.screening, args.search_log, args.fragment, REPORT_REL, GATES_REL]
    required += [rel for _round, _wp, rel, _n in ACCEPTED_PACKAGES]
    for rel in required:
        if not os.path.exists(os.path.join(ROOT, rel)):
            print('FAIL [file.missing] required artifact not found: %s' % rel)
            print('RESULT: FAIL')
            return 1

    screening = json.loads(read_rel(args.screening))
    search_log = json.loads(read_rel(args.search_log))
    fragment = json.loads(read_rel(args.fragment))
    inv = load_rel(INV_REL)
    queue = load_rel(QUEUE_REL)
    cluster = load_rel(CLUSTER_REL)
    registry = load_rel(REGISTRY_REL)
    report = read_rel(REPORT_REL)
    gates = read_rel(GATES_REL)

    inv_by_id = {row['id']: row for row in inv['statements']}
    dangling_ids = {d['id'] for d in inv.get('legacyDanglingStatements', [])}
    queue_by_id = {row['pairId']: row for row in queue['pairs']}
    all_pairs = [row['pairId'] for row in queue['pairs']]

    rec_by_id = {}
    for rec in registry['records']:
        rec_by_id[rec.get('id')] = rec

    # ---------------------------------------------------------------- self-audit
    ledger_abs = os.path.normpath(os.path.join(ROOT, LEDGER_REL))
    c.check(ledger_abs not in READ_PATHS, 'self.ledgerRead',
            'the validator opened the mutable R5 cumulative ledger')
    c.check('coverageLedgerSha256' not in screening.get('snapshot', {}),
            'self.ledgerPinned', 'the snapshot pins the mutable R5 coverage ledger')
    c.check(not os.path.exists(os.path.join(HERE, 'probes')), 'self.probeDir',
            'the package ships a probe directory although it claims no certificate')
    lean_in_package = []
    for dirpath, _dirnames, filenames in os.walk(HERE):
        lean_in_package += [f for f in filenames if f.endswith('.lean')]
    c.check(lean_in_package == [], 'self.packageLean',
            'the package ships Lean files although it claims no certificate: %r'
            % lean_in_package)

    # ---------------------------------------------------------------- vocabulary
    c.check(screening.get('schemaVersion') == '1.0.0', 'schema.version',
            'unexpected schemaVersion')
    c.check(screening.get('artifactKind') == 'bounded-screening-package', 'schema.kind',
            'unexpected artifactKind')
    c.check(screening.get('round') == 'R5', 'schema.round', 'unexpected round')
    c.check(screening.get('statusVocabulary') == STATUSES, 'schema.statusVocabulary',
            'status vocabulary drift')
    c.check(screening.get('kindVocabulary') == KINDS, 'schema.kindVocabulary',
            'kind vocabulary drift')
    c.check(set(screening.get('allowedAxioms', [])) == ALLOWED_AXIOMS, 'schema.allowedAxioms',
            'allowed-axiom list drift')

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
    c.check(snap.get('deliveredLeanFileCount') == EXPECTED_LEAN_FILES,
            'snapshot.leanFileCount', 'declared Lean file count drift')
    lean_files = []
    for dirpath, _dirnames, filenames in os.walk(os.path.join(ROOT, 'PhotoLean')):
        lean_files += [f for f in filenames if f.endswith('.lean')]
    c.check(len(lean_files) == EXPECTED_LEAN_FILES, 'snapshot.leanTree',
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
    cov_ref = screening.get('coverageReference', {})
    c.check(cov_ref.get('pin') == 'not-pinned', 'coverageReference.pin',
            'the coverage reference must declare itself unpinned')
    c.check('sha256' not in cov_ref, 'coverageReference.sha256',
            'the coverage reference must not carry a ledger hash')
    c.check('probeReference' not in screening, 'schema.probeReference',
            'the package declares a probe reference although it claims no certificate')
    cert_ref = screening.get('certificateReference', {})
    c.check(cert_ref.get('declarationCount') == 0, 'certificateReference.count',
            'a package without certified/refuted outcomes must declare zero certificates')
    c.check(cert_ref.get('path') in (None, ''), 'certificateReference.path',
            'a package without certified/refuted outcomes must not point at a probe')

    # ---------------------------------------------------------------- prior coverage
    prior_pairs = []
    for round_tag, wp_id, rel, expected_n in ACCEPTED_PACKAGES:
        pkg = json.loads(read_rel(rel))
        ids = [p.get('pairId') for p in pkg.get('pairs', [])]
        c.check(len(ids) == expected_n, 'prior.count.%s' % wp_id,
                'accepted package %s has %d pairs, expected %d'
                % (rel, len(ids), expected_n))
        c.check(pkg.get('round') == round_tag, 'prior.round.%s' % wp_id,
                'accepted package %s round drift' % rel)
        c.check(pkg.get('workPackage', {}).get('id') == wp_id, 'prior.wp.%s' % wp_id,
                'accepted package %s work-package id drift' % rel)
        for p in pkg.get('pairs', []):
            sts = {q.get('outcome', {}).get('status') for q in p.get('queries', [])}
            c.check(bool(sts), 'prior.queryMissing.%s' % wp_id,
                    'accepted pair %r in %s has no query row' % (p.get('pairId'), rel))
            c.check(sts <= set(STATUSES), 'prior.statusVocabulary.%s' % wp_id,
                    'accepted pair %r in %s carries an unknown status' % (p.get('pairId'), rel))
        prior_pairs.extend(ids)
    c.check(len(prior_pairs) == len(set(prior_pairs)), 'prior.duplicate',
            'the accepted packages double-count a pair')
    c.check(len(set(prior_pairs)) == EXPECTED_PRIOR, 'prior.total',
            'prior coverage derived from the accepted packages is %d, expected %d'
            % (len(set(prior_pairs)), EXPECTED_PRIOR))
    c.check(not (set(prior_pairs) & set(EXPECTED_PAIRS)), 'prior.overlap',
            'the assigned pairs overlap the accepted R2/R3/R4 pairs')
    c.check(len(set(prior_pairs) | set(EXPECTED_PAIRS)) == EXPECTED_PRIOR + EXPECTED_PAIRS_N,
            'prior.union', 'prior plus assigned pairs is not a disjoint union of 76')

    # ---------------------------------------------------------------- pair coverage
    work = screening.get('workPackage', {})
    c.check(work.get('id') == 'WP-cross-domain-screening-02', 'workPackage.id',
            'work package id drift')
    c.check(work.get('pairIds') == EXPECTED_PAIRS, 'workPackage.pairIds',
            'work package pair list is not the approved nine')
    c.check(work.get('pairCount') == EXPECTED_PAIRS_N, 'workPackage.pairCount',
            'work package pair count drift')

    pairs = screening.get('pairs', [])
    pair_ids = [p.get('pairId') for p in pairs]
    c.check(pair_ids == EXPECTED_PAIRS, 'pairs.order',
            'screening pair rows are not exactly the approved nine in plan order')
    c.check(len(pair_ids) == len(set(pair_ids)), 'pairs.duplicate',
            'duplicate pair id in screening package')
    c.check(set(pair_ids) == set(EXPECTED_PAIRS), 'pairs.coverage',
            'screening pair set is not exactly the approved nine')

    all_query_ids = []
    query_by_id = {}
    for pair in pairs:
        pid = pair.get('pairId')
        qrow = queue_by_id.get(pid)
        c.check(qrow is not None, 'pair.queueMissing',
                'pair %r is not in the R1 pair queue' % pid)
        if qrow is not None:
            c.check(pair.get('theories') == qrow['theories'], 'pair.theories',
                    'pair %r theories do not match the R1 queue' % pid)
            c.check(pair.get('primaryCluster') == qrow['screeningCluster'], 'pair.cluster',
                    'pair %r primary cluster does not match the R1 queue' % pid)
        c.check(pair.get('primaryCluster') == 'cross-domain-screening', 'pair.clusterName',
                'pair %r is not in the cross-domain-screening cluster' % pid)
        theories = pair.get('theories', [])
        partner = PARTNERS.get(pid)
        c.check(partner is not None, 'pair.unknown',
                'pair %r is not one of the nine assigned XD2 pairs' % pid)
        c.check(len(theories) == 2 and 'Goldschmidt' in theories, 'pair.goldschmidt',
                'pair %r is not a two-theory pair carrying Goldschmidt' % pid)
        c.check(partner is not None and set(theories) == {'Goldschmidt', partner},
                'pair.partner',
                'pair %r theories are not Goldschmidt plus its assigned partner' % pid)
        qids = pair.get('queryIds', [])
        c.check(isinstance(qids, list) and len(qids) >= 1, 'pair.noQuery',
                'pair %r has no named query or outOfScope record' % pid)
        c.check(qids == [q.get('queryId') for q in pair.get('queries', [])],
                'pair.queryIds', 'pair %r queryIds do not match its query rows' % pid)
        for q in pair.get('queries', []):
            qid = q.get('queryId')
            all_query_ids.append(qid)
            query_by_id[qid] = q
            c.check(q.get('pairId') == pid, 'query.pairId',
                    'query %r pairId does not match its pair row' % qid)

    c.check(len(all_query_ids) == len(set(all_query_ids)), 'queries.duplicate',
            'duplicate query id in screening package')
    c.check(len(all_query_ids) == EXPECTED_QUERIES_N, 'queries.count',
            'query count is %d, expected %d' % (len(all_query_ids), EXPECTED_QUERIES_N))

    # ---------------------------------------------------------------- per-query checks
    non_certified = []
    for pair in pairs:
        pid = pair.get('pairId')
        for q in pair.get('queries', []):
            qid = q.get('queryId')
            c.nonempty(qid, 'query.id', 'query row without queryId')
            for field in ['title', 'chemicalQuestion', 'chemicalRationale',
                          'expectedKindRationale', 'falsificationCondition']:
                c.nonempty(q.get(field), 'query.%s' % field,
                           'query %r missing %s' % (qid, field))
                floor = 40 if field == 'title' else 120
                c.check(isinstance(q.get(field), str) and len(q.get(field, '')) >= floor,
                        'query.%s.length' % field,
                        'query %r has a stub %s' % (qid, field))

            kind = q.get('expectedKind')
            c.check(kind in KINDS, 'query.kind',
                    'query %r expectedKind %r is not a seven-kind value' % (qid, kind))
            c.check(kind != 'refuted', 'query.kindRefuted',
                    'query %r uses the status refuted as an evidence kind' % qid)

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
            c.check(src_theory == 'Goldschmidt', 'endpoint.orientation',
                    'query %r is not oriented Goldschmidt -> partner' % qid)
            c.check(PARTNERS.get(pid) is not None and tgt_theory == PARTNERS[pid],
                    'endpoint.partnerTheory',
                    'query %r target is not the pair partner theory' % qid)

            ctx = q.get('sharedContext', {})
            ctx_id = ctx.get('id')
            c.check(ctx_id in screening.get('contextLibrary', {}), 'context.missing',
                    'query %r shared context %r is not in the context library'
                    % (qid, ctx_id))
            lib_ctx = screening.get('contextLibrary', {}).get(ctx_id, {})
            c.check(ctx.get('fields') == lib_ctx.get('fields'), 'context.fieldsMatch',
                    'query %r shared-context fields drift from the library' % qid)
            c.check(isinstance(ctx.get('fields'), list) and len(ctx.get('fields')) >= 2,
                    'context.fields', 'query %r shared context has fewer than two fields' % qid)
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
                               'query %r %s translation %r has no reason' % (qid, side, tid))
                    c.check(isinstance(tr.get('reason'), str) and len(tr.get('reason')) >= 80,
                            'translation.reasonLength',
                            'query %r %s translation reason is a stub' % (qid, side))
                else:
                    c.nonempty(tr.get('term'), 'translation.term',
                               'query %r %s translation has no term' % (qid, side))
                c.nonempty(tr.get('requirement'), 'translation.requirement',
                           'query %r %s translation has no requirement note' % (qid, side))

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
                c.check('True' in (prem.get('predicate') or ''), 'premise.emptyPredicate',
                        'query %r has no premise ids but its predicate is not True' % qid)

            scope = q.get('scope', {})
            sid = scope.get('id')
            c.check(sid in screening.get('scopeLibrary', {}), 'scope.missing',
                    'query %r scope %r is not in the scope library' % (qid, sid))
            lib_scope = screening.get('scopeLibrary', {}).get(sid, {})
            c.check(scope.get('description') == lib_scope.get('description'),
                    'scope.descriptionMatch',
                    'query %r scope description drifts from the library' % qid)
            c.check(scope.get('domain') == lib_scope.get('domain'),
                    'scope.domainMatch', 'query %r scope domain drifts from the library' % qid)
            c.nonempty(scope.get('description'), 'scope.description',
                       'query %r scope has no description' % qid)
            c.nonempty(scope.get('domain'), 'scope.domain', 'query %r scope has no domain' % qid)
            c.check(scope.get('snapshot') == snap.get('id'), 'scope.snapshot',
                    'query %r scope snapshot does not match the package snapshot' % qid)

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
                c.check(False, 'outcome.certifiedUnsupported',
                        'query %r claims certified but the package ships no probe' % qid)
            elif status == 'refuted':
                c.check(False, 'outcome.refutedUnsupported',
                        'query %r claims refuted but the package ships no countermodel '
                        'certificate' % qid)
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
                non_certified.append((qid, status, evidence))
                c.check(evidence.get('type') == 'jurisdiction', 'evidence.jurisdictionType',
                        'query %r outOfScope requires a jurisdiction evidence record' % qid)
                c.nonempty(evidence.get('searchLogRef'), 'evidence.searchRef',
                           'query %r outOfScope has no search-log reference' % qid)
                c.nonempty(evidence.get('jurisdictionRationale'),
                           'evidence.jurisdictionRationale',
                           'query %r outOfScope has no statement-level rationale' % qid)
                c.nonempty(evidence.get('statementLevelReason'),
                           'evidence.jurisdictionStatement',
                           'query %r outOfScope has no statement-level reason' % qid)
                reason = evidence.get('statementLevelReason') or ''
                c.check(len(reason) >= 200, 'evidence.statementLevelLength',
                        'query %r statement-level reason is a stub' % qid)
                for side in ['source', 'target']:
                    name = short_name(endpoints.get(side, {}).get('declaration', ''))
                    c.check(name and name in reason, 'evidence.statementLevelNames',
                            'query %r statement-level reason does not name the %s endpoint %r'
                            % (qid, side, name))
                c.check(channels == [], 'evidence.jurisdictionChannels',
                        'query %r is outOfScope but declares observation channels' % qid)

            prov = q.get('provenance', {})
            c.nonempty(prov.get('kind'), 'provenance.kind',
                       'query %r has no provenance kind' % qid)
            c.check(prov.get('sourceArtifact') == REL + '/search-log.json',
                    'provenance.artifact', 'query %r provenance artifact drift' % qid)
            c.check(prov.get('locator') == evidence.get('searchLogRef'),
                    'provenance.locator',
                    'query %r provenance locator does not match the search reference' % qid)
            c.nonempty(prov.get('legacyDisposition'), 'provenance.legacy',
                       'query %r has no legacy disposition note' % qid)

    # ---------------------------------------------------------------- no certificates
    claimed_statuses = status_counts([q for p in pairs for q in p['queries']])
    c.check(claimed_statuses.get('certified', 0) == 0, 'outcome.noCertified',
            'the package claims a certified outcome without a probe')
    c.check(claimed_statuses.get('refuted', 0) == 0, 'outcome.noRefuted',
            'the package claims a refuted outcome without a countermodel certificate')

    # ---------------------------------------------------------------- jurisdiction
    jurisdiction = screening.get('jurisdictionEvidence', {})
    c.check(jurisdiction.get('goldschmidtTokens') == GOLDSCHMIDT_TOKENS,
            'jurisdiction.goldschmidtTokens',
            'the declared Goldschmidt scan vocabulary drifts from the validator vocabulary')
    c.check(jurisdiction.get('partnerTokens') == PARTNER_TOKENS,
            'jurisdiction.partnerTokens',
            'the declared partner scan vocabulary drifts from the validator vocabulary')
    jpairs = {row.get('pairId'): row for row in jurisdiction.get('pairs', [])}
    c.check(sorted(jpairs) == sorted(EXPECTED_PAIRS), 'jurisdiction.pairs',
            'the jurisdiction evidence does not cover exactly the nine pairs')
    gs_rows = theory_signatures(inv, 'Goldschmidt')
    for pid in EXPECTED_PAIRS:
        partner = PARTNERS[pid]
        pt_rows = theory_signatures(inv, partner)
        gs_in_pt = token_hits(GOLDSCHMIDT_TOKENS, pt_rows)
        pt_in_gs = token_hits(PARTNER_TOKENS[partner], gs_rows)
        c.check(gs_in_pt == [], 'jurisdiction.goldschmidtInPartner.%s' % pid,
                'pair %r: Goldschmidt identifiers occur in %s signatures: %r'
                % (pid, partner, gs_in_pt))
        c.check(pt_in_gs == [], 'jurisdiction.partnerInGoldschmidt.%s' % pid,
                'pair %r: %s identifiers occur in Goldschmidt signatures: %r'
                % (pid, partner, pt_in_gs))
        gs_imports = import_closure('Goldschmidt')
        pt_imports = import_closure(partner)
        shared = sorted(gs_imports & pt_imports)
        c.check(shared == [], 'jurisdiction.importIntersection.%s' % pid,
                'pair %r: the two authorities share a non-Mathlib import: %r'
                % (pid, shared))
        declared = jpairs.get(pid, {})
        c.check(declared.get('partnerTheory') == partner, 'jurisdiction.partner.%s' % pid,
                'pair %r jurisdiction evidence names the wrong partner' % pid)
        c.check(declared.get('goldschmidtStatementRows') == len(gs_rows),
                'jurisdiction.gsRows.%s' % pid,
                'pair %r Goldschmidt row count drift' % pid)
        c.check(declared.get('partnerStatementRows') == len(pt_rows),
                'jurisdiction.ptRows.%s' % pid,
                'pair %r partner row count drift' % pid)
        c.check(declared.get('goldschmidtTokensInPartnerSignatures') == [],
                'jurisdiction.declaredGsHits.%s' % pid,
                'pair %r declares a nonempty Goldschmidt-hit list' % pid)
        c.check(declared.get('partnerTokensInGoldschmidtSignatures') == [],
                'jurisdiction.declaredPtHits.%s' % pid,
                'pair %r declares a nonempty partner-hit list' % pid)
        c.check(declared.get('importClosureIntersection') == [],
                'jurisdiction.declaredImports.%s' % pid,
                'pair %r declares a nonempty import intersection' % pid)
        rec_id = 'rec-notestablished-%s' % pid
        rec = rec_by_id.get(rec_id)
        c.check(rec is not None, 'jurisdiction.legacyRecord.%s' % pid,
                'pair %r has no legacy notEstablished record' % pid)
        if rec is not None:
            c.check(rec.get('status') == 'notEstablished', 'jurisdiction.legacyStatus.%s' % pid,
                    'pair %r legacy record status drift' % pid)
            c.check(rec.get('relationKind') is None,
                    'jurisdiction.legacyKind.%s' % pid,
                    'pair %r legacy record carries a relation kind' % pid)
            c.check(rec.get('certificate') is None, 'jurisdiction.legacyCertificate.%s' % pid,
                    'pair %r legacy record carries a certificate' % pid)

    # ---------------------------------------------------------------- search log
    entries = search_log.get('entries', [])
    c.check(search_log.get('artifactKind') == 'bounded-search-log', 'search.kind',
            'search-log artifactKind drift')
    c.check(search_log.get('round') == 'R5', 'search.round', 'search-log round drift')
    c.check(search_log.get('workPackage') == 'WP-cross-domain-screening-02', 'search.wp',
            'search-log work-package drift')
    c.check(search_log.get('snapshot') == snap.get('id'), 'search.snapshot',
            'search-log snapshot drift')
    entry_ids = [e.get('searchId') for e in entries]
    c.check(len(entry_ids) == len(set(entry_ids)), 'search.duplicate', 'duplicate search id')
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
            c.check(e.get('status') == q.get('outcome', {}).get('status'), 'search.status',
                    'search entry %r status does not match its query' % sid)
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
        c.check(isinstance(cmds, list) and len(cmds) >= 4, 'search.commands',
                'search entry %r has fewer than four recorded commands' % sid)
        for cmd in cmds or []:
            c.nonempty(cmd.get('command'), 'search.command',
                       'search entry %r command is empty' % sid)
            c.nonempty(cmd.get('purpose'), 'search.commandPurpose',
                       'search entry %r command has no purpose' % sid)
            c.nonempty(cmd.get('result'), 'search.commandResult',
                       'search entry %r command has no result' % sid)
        strategies = e.get('strategiesAttempted')
        c.check(isinstance(strategies, list) and len(strategies) >= 3, 'search.strategies',
                'search entry %r has fewer than three attempted strategies' % sid)
        for st in strategies or []:
            c.nonempty(st.get('strategy'), 'search.strategy',
                       'search entry %r strategy is empty' % sid)
            c.nonempty(st.get('outcome'), 'search.strategyOutcome',
                       'search entry %r strategy has no outcome' % sid)
        candidates = e.get('candidateEvidence')
        c.check(isinstance(candidates, list) and len(candidates) >= 1, 'search.candidates',
                'search entry %r has no candidate evidence' % sid)
        c.nonempty(e.get('remainingGap'), 'search.remainingGap',
                   'search entry %r has no remaining gap' % sid)
        rec = e.get('recomputeCommands')
        c.check(isinstance(rec, list) and len(rec) >= 1, 'search.recompute',
                'search entry %r has no recompute command' % sid)
        c.check(any('validate.py' in x for x in rec or []), 'search.recomputeValidator',
                'search entry %r does not cite the package validator' % sid)
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
            c.check(q.get('outcome', {}).get('status') != 'certified', 'search.certifiedEntry',
                    'certified query %r has a search-log entry' % e.get('queryId'))
    c.check(len(entries) == len(non_certified), 'search.oneToOne',
            'search-log entries %d do not match the non-certified queries %d'
            % (len(entries), len(non_certified)))
    c.check(search_ref.get('entryCount') == len(entries), 'searchLogReference.entryCount',
            'search-log reference entry count drift')
    c.check(search_log.get('counts', {}).get('entries') == len(entries),
            'counts.searchEntries', 'search-log entry count drift')
    c.check(search_log.get('counts', {}).get('byStatus') == status_counts(
        [q for p in pairs for q in p['queries']]), 'counts.searchByStatus',
        'search-log status counts drift')

    # ---------------------------------------------------------------- counts
    kind_counts = {}
    for pair in pairs:
        for q in pair['queries']:
            kind_counts[q['expectedKind']] = kind_counts.get(q['expectedKind'], 0) + 1
    declared = screening.get('counts', {})
    c.check(declared.get('pairs') == len(pairs), 'counts.pairs', 'pair count drift')
    c.check(declared.get('queries') == len(all_query_ids), 'counts.queries',
            'query count drift')
    c.check(declared.get('byStatus') == claimed_statuses, 'counts.byStatus',
            'status counts drift: %r != %r' % (declared.get('byStatus'), claimed_statuses))
    c.check(declared.get('byExpectedKind') == kind_counts, 'counts.byExpectedKind',
            'kind counts drift: %r != %r' % (declared.get('byExpectedKind'), kind_counts))
    for status in STATUSES:
        c.check(declared.get(status) == claimed_statuses.get(status, 0),
                'counts.%s' % status, 'declared %s count drift' % status)
    c.check(declared.get('pairsWithAtLeastOneQuery') == len(pairs),
            'counts.pairsWithQuery', 'pairs-with-a-query count drift')
    c.check(declared.get('pairsWithoutNamedQuery') == 0, 'counts.pairsWithoutQuery',
            'a pair is declared without a named query')

    # ---------------------------------------------------------------- fragment
    fw = fragment.get('workPackage', {})
    c.check(fragment.get('artifactKind') == 'bounded-coverage-fragment', 'fragment.kind',
            'coverage fragment artifactKind drift')
    c.check(fragment.get('round') == 'R5', 'fragment.round', 'coverage fragment round drift')
    c.check(fragment.get('packageState') == 'submitted-R5-pending-review', 'fragment.state',
            'coverage fragment package state drift')
    c.check(fw.get('id') == 'WP-cross-domain-screening-02', 'fragment.id',
            'coverage fragment work-package id drift')
    c.check(fw.get('path') == SCREENING_REL, 'fragment.path',
            'coverage fragment screening path drift')
    c.check(fw.get('pairCount') == EXPECTED_PAIRS_N, 'fragment.pairCount',
            'coverage fragment pair count drift')
    c.check(fw.get('sha256') == sha_file(os.path.join(ROOT, args.screening)), 'fragment.sha',
            'coverage fragment screening hash drift')
    pair_row = {p['pairId']: p for p in pairs}
    f_pairs = [p.get('pairId') for p in fragment.get('pairs', [])]
    c.check(f_pairs == pair_ids, 'fragment.pairs',
            'coverage fragment pairs do not match the screening pairs')
    for fp in fragment.get('pairs', []):
        src = pair_row.get(fp.get('pairId'))
        if src is None:
            continue
        c.check(fp.get('queryCount') == len(src['queries']), 'fragment.queryCount',
                'coverage fragment query count for %r drift' % fp.get('pairId'))
        c.check(fp.get('byStatus') == status_counts(src['queries']), 'fragment.byStatus',
                'coverage fragment status counts for %r drift' % fp.get('pairId'))
        c.check(fp.get('theories') == src['theories'], 'fragment.theories',
                'coverage fragment theories for %r drift' % fp.get('pairId'))
        c.check(fp.get('primaryCluster') == src.get('primaryCluster'), 'fragment.cluster',
                'coverage fragment cluster for %r drift' % fp.get('pairId'))
    fcounts = fragment.get('counts', {})
    c.check(fcounts.get('pairs') == len(pairs), 'fragment.counts.pairs',
            'coverage fragment pair count drift')
    c.check(fcounts.get('queries') == len(all_query_ids), 'fragment.counts.queries',
            'coverage fragment query count drift')
    c.check(fcounts.get('byStatus') == claimed_statuses, 'fragment.counts.byStatus',
            'coverage fragment status counts drift')
    c.check(fcounts.get('screenedDelta') == EXPECTED_PAIRS_N, 'fragment.counts.delta',
            'coverage fragment screened delta drift')
    ow = fragment.get('overlapWithAccepted', {})
    c.check(ow.get('intersection') == [], 'fragment.overlap',
            'coverage fragment overlaps the accepted pairs')
    c.check(ow.get('acceptedScreenedPairCount') == len(set(prior_pairs)),
            'fragment.acceptedCount',
            'coverage fragment accepted-pair count drift')
    c.check('sha256' not in json.dumps(ow), 'fragment.overlapHash',
            'the overlap block must not carry a ledger hash')
    c.check(fragment.get('universe', {}).get('pairCount') == len(all_pairs),
            'fragment.universe', 'coverage fragment universe pair count drift')
    c.check(fragment.get('universe', {}).get('sourceSha256') ==
            sha_file(os.path.join(ROOT, QUEUE_REL)), 'fragment.universeHash',
            'coverage fragment universe hash drift')

    # ---------------------------------------------------------------- non-claims
    c.check(isinstance(screening.get('nonClaims'), list)
            and len(screening.get('nonClaims')) >= 3, 'nonClaims.missing',
            'screening package has fewer than three non-claim statements')
    c.check(isinstance(search_log.get('nonClaims'), list)
            and len(search_log.get('nonClaims')) >= 3, 'search.nonClaims',
            'search log has fewer than three non-claim statements')
    c.check(isinstance(fragment.get('nonClaims'), list)
            and len(fragment.get('nonClaims')) >= 2, 'fragment.nonClaims',
            'coverage fragment has fewer than two non-claim statements')

    # ---------------------------------------------------------------- report
    for needle in ['python3 bounded_audit/r5/cross-domain-02/validate.py',
                   'python3 audit_boundary/validate_boundary.py',
                   'python3 bounded_audit/validate_screening.py',
                   'python3 bounded_audit/r4/validate_r3_content.py',
                   'python3 bounded_audit/r4/validate_coverage.py --coverage '
                   'bounded_audit/r4/coverage-accepted.json',
                   'proofs/scripts/check.sh --strict',
                   'mutation']:
        c.check(needle in report, 'report.gate',
                'REPORT.md does not record the gate %r' % needle)
    c.check('outOfScope' in report, 'report.outcomes',
            'REPORT.md does not report the outcome counts')
    c.check('FAIL-CLOSED' in report, 'report.failClosed',
            'REPORT.md does not record the fail-closed mutation results')
    for needle in ['python3 audit_boundary/validate_boundary.py',
                   'proofs/scripts/check.sh --strict']:
        c.check(needle in gates, 'evidence.gateTranscript',
                'evidence/gates.log does not record the gate %r' % needle)
    c.check('[exit=0]' in gates, 'evidence.gateExit',
            'evidence/gates.log records no successful exit code')

    return c.summary()


if __name__ == '__main__':
    sys.exit(main())
