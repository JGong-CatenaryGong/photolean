#!/usr/bin/env python3
"""Deterministic fail-closed validator for the R5 RAD3 package.

Usage (from the repository root):

    python3 bounded_audit/r5/radiative-03/validate.py

Optional overrides, used by the fail-closed `/tmp` mutation tests on copies:

    python3 bounded_audit/r5/radiative-03/validate.py --screening /tmp/x.json
    python3 bounded_audit/r5/radiative-03/validate.py --search-log /tmp/y.json \\
        --fragment /tmp/z.json

The validator re-derives every fact from the frozen R1 inventory, the frozen pair queue, the
frozen cluster plan, the accepted legacy registry, the four accepted prior screening packages,
the package search log, the package probe and its compile log. It does not trust the package's
own counts or prose.

It deliberately does **not** read or pin the mutable R5 cumulative ledger
(`bounded_audit/coverage.json`). Prior coverage is derived directly from the accepted package
artifacts listed in `PRIOR_PACKAGES`, and the validator fails if the ledger path is ever opened.
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
    'P-FluorPhos-ICvsISC',
    'P-FluorPhos-Forster',
    'P-FluorPhos-Einstein',
    'P-EnergyGapLaw-StokesShift',
    'P-EnergyGapLaw-ICvsISC',
    'P-EnergyGapLaw-Forster',
    'P-EnergyGapLaw-Einstein',
    'P-StokesShift-ICvsISC',
    'P-StokesShift-Forster',
    'P-StokesShift-Einstein',
    'P-ICvsISC-Forster',
    'P-ICvsISC-Einstein',
    'P-Forster-Einstein',
]
WORK_PACKAGE = 'WP-radiative-energy-transfer-03'
PRIOR_PACKAGES = [
    'bounded_audit/wp-surface-01/screening.json',
    'bounded_audit/r3/screening.json',
    'bounded_audit/r4/excited-01/screening.json',
    'bounded_audit/r4/excited-02/screening.json',
    'bounded_audit/r4/conical-01/screening.json',
]
EXPECTED_PRIOR_PAIRS = 67

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
               'rate-constant', 'barrier-height', 'quantum-yield', 'transfer-efficiency',
               'emission-energy', 'spectral-intensity', 'zone-tag'}
PROBE_NAMESPACE = 'PhotoLean.RelationAudit.BoundedAudit.Rad3.'
CHEMISTRY_WORDS = ('rate', 'barrier', 'yield', 'energy', 'efficiency', 'branch',
                   'transfer', 'emission', 'channel', 'reorganization', 'coupling',
                   'spin-orbit', 'stokes', 'oscillator', 'lifetime')

INV_REL = 'audit_boundary/statement-inventory.json'
QUEUE_REL = 'audit_boundary/pair-queue.json'
CLUSTER_REL = 'audit_boundary/cluster-plan.json'
BOUNDARY_REL = 'audit_boundary/BOUNDARY.md'
REGISTRY_REL = 'relation_audit/registry.json'
SCREENING_REL = REL + '/screening.json'
SEARCH_REL = REL + '/search-log.json'
FRAGMENT_REL = REL + '/coverage-fragment.json'
PROBE_REL = REL + '/probes/RAD3-probe.lean'
PROBE_LOG_REL = REL + '/probes/compile.log'
BUILD_COMMAND = 'proofs/scripts/lake env lean ' + PROBE_REL
EXPECTED_REGISTRY_SHA = '25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0'
EXPECTED_LEAN_FILES = 102
EXPECTED_QUERIES = 16
EXPECTED_CHANNEL_QUERIES = 6

OPENED = []


def _record(path):
    OPENED.append(os.path.abspath(path))


def sha_file(path):
    _record(path)
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def sha_rel(rel):
    return sha_file(os.path.join(ROOT, rel))


def load_file(path):
    _record(path)
    with open(path, encoding='utf-8') as fh:
        return json.load(fh)


def read_file(path):
    _record(path)
    with open(path, encoding='utf-8') as fh:
        return fh.read()


def load_rel(rel):
    return load_file(os.path.join(ROOT, rel))


def read_rel(rel):
    return read_file(os.path.join(ROOT, rel))


class Checker:
    def __init__(self):
        self.failures = []

    def check(self, cond, code, message):
        if not cond:
            self.failures.append((code, message))

    def nonempty(self, value, code, message):
        self.check(isinstance(value, str) and value.strip() != '', code, message)

    def summary(self, label):
        print('R5 %s validation' % label)
        print('  root: %s' % ROOT)
        print('  package: %s' % REL)
        print('  checks failed: %d' % len(self.failures))
        if self.failures:
            for code, message in self.failures:
                print('FAIL [%s] %s' % (code, message))
            print('RESULT: FAIL (%d failed checks)' % len(self.failures))
            return 1
        print('RESULT: PASS (all %s package checks passed)' % label)
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


def line_contains(rel_path, line, name):
    path = os.path.join(ROOT, rel_path)
    if not os.path.exists(path):
        return False
    try:
        text = read_file(path).splitlines()
    except OSError:
        return False
    if not isinstance(line, int) or line < 1 or line > len(text):
        return False
    return name in text[line - 1]


def status_counts(queries):
    counts = {}
    for q in queries:
        status = q.get('outcome', {}).get('status')
        counts[status] = counts.get(status, 0) + 1
    return counts


def theorem_block(text, name):
    """Return the declaration block starting at `theorem <name>` (bounded at the next
    declaration keyword), so kind-check theorems can be inspected without a fragile regex."""
    match = re.search(r'\btheorem\s+%s\b' % re.escape(name), text)
    if match is None:
        return None
    rest = text[match.start():]
    nxt = re.search(r'\n(?:theorem|def|example|end|#print)\s', rest[1:])
    return rest[:nxt.start() + 1] if nxt else rest


def parse_premise_witnesses(probe_text):
    out = {}
    for m in re.finditer(r'certificatePremiseIDs\s+(\w+)\s*=\s*(\[[^\]]*\])',
                         probe_text, re.S):
        out[m.group(1)] = json.loads(m.group(2))
    return out


def parse_composition_witnesses(probe_text):
    out = {}
    pattern = (r'\(certificateComposition\?\s+(\w+)\)\.map\s+'
               r'\(fun m => m\.(\w+)\)\s*=\s*some\s*(\[[^\]]*\]|CompositionForm\.\w+)')
    for m in re.finditer(pattern, probe_text, re.S):
        decl, field_name, value = m.group(1), m.group(2), m.group(3)
        if value.startswith('['):
            parsed = json.loads(value)
        else:
            parsed = value.split('.')[-1]
        out.setdefault(decl, {})[field_name] = parsed
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--screening', default=SCREENING_REL)
    parser.add_argument('--search-log', default=SEARCH_REL)
    parser.add_argument('--fragment', default=FRAGMENT_REL)
    args = parser.parse_args()

    def resolve(path):
        return path if os.path.isabs(path) else os.path.join(ROOT, path)

    screening_path = resolve(args.screening)
    search_path = resolve(args.search_log)
    fragment_path = resolve(args.fragment)

    c = Checker()
    required = [INV_REL, QUEUE_REL, CLUSTER_REL, BOUNDARY_REL, REGISTRY_REL,
                screening_path, search_path, fragment_path,
                PROBE_REL, PROBE_LOG_REL] + PRIOR_PACKAGES
    for path in required:
        full = path if os.path.isabs(path) else os.path.join(ROOT, path)
        if not os.path.exists(full):
            print('FAIL [file.missing] required artifact not found: %s' % path)
            print('RESULT: FAIL')
            return 1

    screening = load_file(screening_path)
    inv = load_rel(INV_REL)
    queue = load_rel(QUEUE_REL)
    cluster = load_rel(CLUSTER_REL)
    registry = load_rel(REGISTRY_REL)
    search_log = load_file(search_path)
    fragment = load_file(fragment_path)
    probe_text = read_rel(PROBE_REL)
    probe_log = read_rel(PROBE_LOG_REL)

    inv_by_id = {row['id']: row for row in inv['statements']}
    dangling_ids = {row['id'] for row in inv.get('legacyDanglingStatements', [])}
    queue_by_id = {row['pairId']: row for row in queue['pairs']}
    all_pairs = [row['pairId'] for row in queue['pairs']]
    probe_axioms = parse_probe_axioms(probe_log)
    premise_witness = parse_premise_witnesses(probe_text)
    composition_witness = parse_composition_witnesses(probe_text)

    # ------------------------------------------------------- accepted prior coverage
    prior_pairs = set()
    per_package = {}
    for rel in PRIOR_PACKAGES:
        pkg = load_rel(rel)
        ids = [row.get('pairId') for row in pkg.get('pairs', [])]
        c.check(len(ids) == len(set(ids)), 'prior.duplicate',
                'accepted package %s carries a duplicate pair id' % rel)
        c.check(all(pid in queue_by_id for pid in ids), 'prior.unknownPair',
                'accepted package %s carries an unknown pair id' % rel)
        per_package[rel] = len(ids)
        prior_pairs |= set(ids)
    c.check(len(prior_pairs) == EXPECTED_PRIOR_PAIRS, 'prior.count',
            'prior coverage derived from accepted packages is %d, expected %d'
            % (len(prior_pairs), EXPECTED_PRIOR_PAIRS))

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
        actual = sha_rel(rel)
        c.check(snap.get(key) == actual, 'snapshot.%s' % key,
                '%s hash drift: %s != %s' % (rel, snap.get(key), actual))
    c.check(snap.get('legacyRegistrySha256') == EXPECTED_REGISTRY_SHA,
            'snapshot.registryPinned', 'legacy registry hash is not the accepted hash')
    # The mutable cumulative ledger must not be pinned or hashed by this package.
    c.check('coverageLedgerSha256' not in snap, 'snapshot.coveragePinned',
            'the snapshot pins the mutable R5 coverage ledger')
    cov_ref = screening.get('coverageReference', {})
    c.check(cov_ref.get('pin') == 'not-pinned', 'coverageReference.pin',
            'the coverage reference must declare itself unpinned')
    c.check('sha256' not in cov_ref, 'coverageReference.sha256',
            'the coverage reference must not carry a ledger hash')
    c.check(cov_ref.get('acceptedScreenedPairCount') == EXPECTED_PRIOR_PAIRS,
            'coverageReference.acceptedCount',
            'the coverage reference accepted count is not the derived 67')
    c.check(cov_ref.get('derivedFrom') == PRIOR_PACKAGES, 'coverageReference.derivedFrom',
            'the coverage reference must derive prior coverage from the accepted packages')
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
    c.check(inv_ref.get('sha256') == sha_rel(INV_REL), 'inventoryReference.sha256',
            'inventory reference hash drift')
    c.check(inv_ref.get('statementRows') == len(inv['statements']),
            'inventoryReference.rows', 'inventory row count drift')
    c.check(inv_ref.get('screeningEligibleRows') ==
            sum(1 for s in inv['statements'] if s['screeningEligible']),
            'inventoryReference.eligible', 'eligible row count drift')
    reg_ref = screening.get('legacyRegistryReference', {})
    c.check(reg_ref.get('sha256') == sha_rel(REGISTRY_REL),
            'legacyRegistryReference.sha256', 'registry reference hash drift')
    c.check(reg_ref.get('certificateCount') == len(registry.get('certificates', [])),
            'legacyRegistryReference.certs', 'registry certificate count drift')
    search_ref = screening.get('searchLogReference', {})
    c.check(search_ref.get('sha256') == sha_rel(SEARCH_REL),
            'searchLogReference.sha256', 'search-log reference hash drift')
    probe_ref = screening.get('probeReference', {})
    c.check(probe_ref.get('sha256') == sha_rel(PROBE_REL),
            'probeReference.sha256', 'probe hash drift')
    c.check(probe_ref.get('log') == PROBE_LOG_REL, 'probeReference.log',
            'probe log path drift')

    # ---------------------------------------------------------------- work package
    work = screening.get('workPackage', {})
    c.check(work.get('id') == WORK_PACKAGE, 'workPackage.id', 'work package id drift')
    c.check(work.get('pairIds') == EXPECTED_PAIRS, 'workPackage.pairIds',
            'work package pair list is not the assigned thirteen')
    c.check(work.get('pairCount') == len(EXPECTED_PAIRS), 'workPackage.pairCount',
            'work package pair count drift')
    c.check(not (set(work.get('pairIds', [])) & prior_pairs),
            'workPackage.acceptedOverlap',
            'the package pair list overlaps the accepted prior pairs')
    # The assigned pair set must be exactly the cluster plan's WP-radiative-energy-transfer-03.
    plan_wp = None
    for cluster_row in cluster.get('clusters', []):
        for wp in cluster_row.get('workPackages', []):
            if wp.get('id') == WORK_PACKAGE:
                plan_wp = wp
    c.check(plan_wp is not None, 'workPackage.planMissing',
            'the cluster plan has no %s work package' % WORK_PACKAGE)
    if plan_wp is not None:
        c.check(work.get('pairIds') == plan_wp.get('pairIds'), 'workPackage.planPairs',
                'work package pair list drifts from the frozen cluster plan')
        c.check(plan_wp.get('pairCount') == len(EXPECTED_PAIRS),
                'workPackage.planCount', 'cluster-plan pair count drift')

    # ---------------------------------------------------------------- pairs
    pairs = screening.get('pairs', [])
    pair_ids = [p.get('pairId') for p in pairs]
    c.check(len(pair_ids) == len(set(pair_ids)), 'pairs.duplicate',
            'duplicate pair id in screening package')
    c.check(set(pair_ids) == set(EXPECTED_PAIRS), 'pairs.coverage',
            'screening pair set is not exactly the assigned thirteen')
    c.check(len(pair_ids) == len(EXPECTED_PAIRS), 'pairs.count',
            'screening pair count is not thirteen')
    c.check(not (set(pair_ids) & prior_pairs), 'pairs.acceptedOverlap',
            'screening pairs overlap the accepted prior pairs')

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
            c.check(pair.get('primaryCluster') == 'radiative-energy-transfer',
                    'pair.clusterName',
                    'pair %r is not in the radiative-energy-transfer cluster' % pid)
            c.check(len(pair.get('theories', [])) == 2 and
                    set(pair.get('theories', [])) <= set(queue.get('theoryInventory', [])),
                    'pair.theoriesShape',
                    'pair %r is not a two-theory pair of the frozen universe' % pid)
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
    c.check(len(all_query_ids) == EXPECTED_QUERIES, 'queries.count',
            'query count is %d, expected %d' % (len(all_query_ids), EXPECTED_QUERIES))

    # ---------------------------------------------------------------- per-query
    non_certified = []
    certified_decls = {}
    certified_queries = {}
    channel_queries = 0
    for pair in pairs:
        for q in pair.get('queries', []):
            qid = q.get('queryId')
            c.nonempty(qid, 'query.id', 'query row without queryId')
            for field in ['title', 'chemicalQuestion', 'chemicalRationale',
                          'expectedKindRationale', 'falsificationCondition']:
                c.nonempty(q.get(field), 'query.%s' % field,
                           'query %r missing %s' % (qid, field))
            question = q.get('chemicalQuestion') or ''
            rationale = q.get('chemicalRationale') or ''
            c.check(question.rstrip().endswith('?'), 'query.questionShape',
                    'query %r chemicalQuestion is not a question' % qid)
            c.check(len(rationale) >= 120, 'query.rationaleShort',
                    'query %r chemicalRationale is too short to be a chemical rationale' % qid)
            lowered = rationale.lower()
            c.check(any(word in lowered for word in CHEMISTRY_WORDS), 'query.rationaleChemical',
                    'query %r chemicalRationale names no chemical quantity' % qid)

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
                    c.check(sha_rel(row['sourceArtifact']) == row['sourceArtifactSha256'],
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
            translation_ids = {}
            for side in ['left', 'right']:
                tr = trans.get(side, {})
                tid = tr.get('id')
                translation_ids[side] = tid
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
            if channels:
                channel_queries += 1
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
            c.check(isinstance(status, str) and STATUSES.count(status) == 1,
                    'outcome.exactlyOne',
                    'query %r does not carry exactly one five-status outcome' % qid)

            translations = set(translation_ids.values())
            if status == 'certified':
                c.check(evidence.get('type') == 'r5-rad3-probe-certificate',
                        'evidence.type',
                        'query %r certified evidence has unsupported type %r'
                        % (qid, evidence.get('type')))
                c.check(evidence.get('kind') == kind, 'evidence.kindMatch',
                        'query %r evidence kind %r does not match expectedKind %r'
                        % (qid, evidence.get('kind'), kind))
                c.check(kind in KINDS and kind != 'refutation', 'evidence.kindCertified',
                        'query %r certified with a non-certifying kind %r' % (qid, kind))
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
                c.check(probe.get('sha256') == sha_rel(PROBE_REL),
                        'evidence.probeHash', 'query %r probe source hash drift' % qid)
                decl = probe.get('declaration', '')
                certified_decls[decl] = qid
                certified_queries[qid] = (q, decl)
                c.check(decl.startswith(PROBE_NAMESPACE), 'evidence.probeDecl',
                        'query %r probe declaration is outside the RAD3 namespace' % qid)
                short = short_name(decl)
                c.check(re.search(r'\bdef\s+%s\b' % re.escape(short), probe_text)
                        is not None, 'evidence.probeDeclMissing',
                        'query %r probe declaration is not in the probe source' % qid)
                kind_thm = probe.get('kindCheckTheorem', '')
                c.check(re.search(r'\btheorem\s+%s\b' % re.escape(short_name(kind_thm)),
                                  probe_text) is not None,
                        'evidence.probeKindMissing',
                        'query %r probe kind-check theorem is missing' % qid)
                c.check(kind_thm == decl + '_kind', 'evidence.kindCheckName',
                        'query %r kind-check theorem is not <declaration>_kind' % qid)
                block = theorem_block(probe_text, short_name(kind_thm))
                c.check(block is not None and ':=' in block and 'rfl' in block,
                        'evidence.kindCheckRfl',
                        'query %r kind-check theorem is not a kernel rfl check' % qid)
                kind_pin = None
                if block is not None:
                    km = re.search(r'certificateKind\s+\w+\s*=\s*RelationKind\.(\w+)', block)
                    if km is not None:
                        kind_pin = km.group(1)
                c.check(kind_pin == kind, 'evidence.kindPin',
                        'query %r screening kind %r does not match the probe kind pin %r'
                        % (qid, kind, kind_pin))
                prov = q.get('provenance', {})
                c.check(prov.get('kind') == 'r5-rad3-probe-certificate',
                        'provenance.kind', 'query %r certified provenance kind drift' % qid)
                c.check(prov.get('certificateId') == qid, 'provenance.certificateId',
                        'query %r certified provenance certificateId drift' % qid)
                c.check(prov.get('sourceArtifact') == PROBE_REL, 'provenance.source',
                        'query %r certified provenance source drift' % qid)
                c.check(prov.get('locator') == decl, 'provenance.locator',
                        'query %r certified provenance locator drift' % qid)
                c.nonempty(prov.get('legacyDisposition'), 'provenance.legacy',
                           'query %r certified provenance has no legacy disposition' % qid)
                c.check(probe.get('buildCommand') == BUILD_COMMAND,
                        'evidence.probeBuild', 'query %r probe build command drift' % qid)
                c.check(probe.get('log') == PROBE_LOG_REL, 'evidence.probeLog',
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
                    c.nonempty(thm.get('role'), 'evidence.underlyingRole',
                               'query %r underlying theorem has no role' % qid)
                    path = os.path.join(ROOT, rel)
                    c.check(os.path.exists(path), 'evidence.underlyingSource',
                            'query %r underlying theorem source is missing' % qid)
                    c.check(isinstance(line, int) and line >= 1,
                            'evidence.underlyingLine',
                            'query %r underlying theorem has no positive source line' % qid)
                    if os.path.exists(path) and isinstance(line, int):
                        c.check(line_contains(rel, line, short_name(d)),
                                'evidence.underlyingLineMatch',
                                'query %r underlying theorem is not at its declared '
                                'source line' % qid)
                c.nonempty(evidence.get('justification'), 'evidence.justification',
                           'query %r certified evidence has no justification' % qid)
                # premise list must match the machine-checked probe witness
                witness = premise_witness.get(short)
                c.check(witness is not None, 'evidence.premiseWitness',
                        'query %r certificate has no machine-checked premise witness' % qid)
                if witness is not None:
                    c.check(witness == (pids or []), 'evidence.premiseMatch',
                            'query %r declared premiseIds %r do not match the probe '
                            'witness %r' % (qid, pids, witness))
                if kind == 'conditionalComposition':
                    comp = evidence.get('composition')
                    c.check(isinstance(comp, dict), 'evidence.compositionMissing',
                            'query %r conditional composition has no composition block' % qid)
                    if isinstance(comp, dict):
                        parents = comp.get('parents') or []
                        parent_ids = [p.get('id') for p in parents]
                        c.check(all(p.get('kind') == 'equivalence' for p in parents),
                                'evidence.parentKinds',
                                'query %r composition parents are not equivalences' % qid)
                        witness_ids = composition_witness.get(short, {}).get('parentIDs')
                        c.check(witness_ids == parent_ids, 'evidence.parentWitness',
                                'query %r composition parent ids do not match the probe '
                                'witness' % qid)
                        witness_bridge = composition_witness.get(short, {}).get('bridgeIDs')
                        c.check(witness_bridge == comp.get('bridgeIds'),
                                'evidence.bridgeWitness',
                                'query %r composition bridge ids do not match the probe '
                                'witness' % qid)
                        witness_form = composition_witness.get(short, {}).get('form')
                        c.check(witness_form == comp.get('form'),
                                'evidence.formWitness',
                                'query %r composition form does not match the probe witness'
                                % qid)
                        c.check(comp.get('childPremiseIds') == (pids or []),
                                'evidence.childPremiseMatch',
                                'query %r composition child premises do not match the '
                                'declared premise list' % qid)
            elif status in {'unresolved', 'notEstablished'}:
                non_certified.append((qid, status, evidence))
                c.check(evidence.get('type') == 'scoped-search',
                        'evidence.searchType',
                        'query %r status %s requires a scoped-search evidence record'
                        % (qid, status))
                c.nonempty(evidence.get('searchLogRef'), 'evidence.searchRef',
                           'query %r status %s has no search-log reference'
                           % (qid, status))
                c.nonempty(evidence.get('candidateSummary'),
                           'evidence.candidateSummary',
                           'query %r status %s has no candidate metadata summary'
                           % (qid, status))
                c.check(translations <= {'none-declared', 'candidate-not-total'},
                        'evidence.candidateTranslation',
                        'query %r status %s claims a total translation' % (qid, status))
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
                c.check(translations == {'none-declared'},
                        'evidence.jurisdictionTranslation',
                        'query %r outOfScope declares a translation' % qid)
                c.check(q.get('observationChannels') == [],
                        'evidence.jurisdictionChannels',
                        'query %r outOfScope carries observation channels' % qid)
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

    c.check(channel_queries >= EXPECTED_CHANNEL_QUERIES, 'queries.channelCoverage',
            'only %d queries carry observation channels, expected at least %d'
            % (channel_queries, EXPECTED_CHANNEL_QUERIES))
    c.check('Certificate.refutation' not in probe_text, 'probe.noRefutation',
            'the probe carries a refutation certificate but the package declares none')
    c.check(not any(q.get('outcome', {}).get('status') == 'refuted' for q in
                    [q for p in pairs for q in p.get('queries', [])]),
            'queries.noRefuted',
            'the package declares a refuted outcome without a refutation certificate')

    # ---------------------------------------------------------------- probe gates
    c.check(set(certified_decls) == set(probe_axioms), 'probe.declarationCoverage',
            'probe axiom declarations %r do not match the certified query declarations %r'
            % (sorted(set(probe_axioms)), sorted(certified_decls)))
    c.check(len(certified_queries) == len(certified_decls), 'probe.declarationUnique',
            'two certified queries share one probe declaration')
    c.check(probe_ref.get('declarationCount') == len(probe_axioms),
            'probe.declarationCount', 'probe reference declaration count drift')
    c.check(probe_ref.get('buildCommand') == BUILD_COMMAND,
            'probe.buildCommand', 'probe reference build command drift')
    forbidden = re.compile(r'sorry|admit|^[ \t]*(private[ \t]+|protected[ \t]+)?'
                           r'(axiom|constant)([ \t]|$)', re.M)
    c.check(forbidden.search(probe_text) is None, 'probe.forbiddenToken',
            'probe source contains a forbidden token')
    c.check(probe_log.strip() != '', 'probe.logEmpty', 'probe compile log is empty')
    for decl in probe_axioms:
        c.check(probe_axioms[decl] <= ALLOWED_AXIOMS, 'probe.axioms',
                'probe declaration %r carries disallowed axioms: %s'
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
            c.check(st not in dangling_ids, 'search.danglingStatement',
                    'search entry %r cites a dangling legacy alias %r' % (sid, st))
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
        qrec = query_by_id.get(qid, {})
        prov = qrec.get('provenance', {})
        c.check(prov.get('kind') == evidence.get('type'), 'provenance.kind',
                'query %r non-certified provenance kind drift' % qid)
        c.check(prov.get('sourceArtifact') == SEARCH_REL, 'provenance.source',
                'query %r non-certified provenance source drift' % qid)
        c.check(prov.get('locator') == sid, 'provenance.locator',
                'query %r non-certified provenance locator drift' % qid)
        c.nonempty(prov.get('legacyDisposition'), 'provenance.legacy',
                   'query %r non-certified provenance has no legacy disposition' % qid)
        c.check(sid in entry_by_id, 'search.missing',
                'query %r status %s has no search-log entry %r' % (qid, status, sid))
        if sid in entry_by_id:
            c.check(entry_by_id[sid].get('queryId') == qid, 'search.mismatch',
                    'search entry %r queryId does not match %r' % (sid, qid))
    c.check(len(entry_by_id) == len(non_certified), 'search.bijection',
            'search-log entries are not in one-to-one correspondence with the non-certified '
            'queries')
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
    statuses = {}
    kinds = {}
    for pair in pairs:
        for q in pair.get('queries', []):
            statuses[q['outcome']['status']] = \
                statuses.get(q['outcome']['status'], 0) + 1
            kinds[q['expectedKind']] = kinds.get(q['expectedKind'], 0) + 1
    declared = screening.get('counts', {})
    c.check(declared.get('pairs') == len(pairs), 'counts.pairs', 'pair count drift')
    c.check(declared.get('queries') == len(all_query_ids), 'counts.queries',
            'query count drift')
    c.check(declared.get('byStatus') == statuses, 'counts.byStatus',
            'status counts drift: %r != %r' % (declared.get('byStatus'), statuses))
    c.check(declared.get('byExpectedKind') == kinds, 'counts.byExpectedKind',
            'kind counts drift: %r != %r' % (declared.get('byExpectedKind'), kinds))
    for status in STATUSES:
        c.check(declared.get(status) == statuses.get(status, 0),
                'counts.%s' % status, 'declared %s count drift' % status)

    # ---------------------------------------------------------------- fragment
    fw = fragment.get('workPackage', {})
    c.check(fragment.get('artifactKind') == 'bounded-coverage-fragment',
            'fragment.kind', 'coverage fragment artifactKind drift')
    c.check(fragment.get('round') == 'R5', 'fragment.round',
            'coverage fragment round drift')
    c.check(fragment.get('packageState') == 'submitted-R5-pending-review',
            'fragment.state', 'coverage fragment package state drift')
    c.check(fw.get('id') == WORK_PACKAGE, 'fragment.id',
            'coverage fragment work-package id drift')
    c.check(fw.get('path') == SCREENING_REL, 'fragment.path',
            'coverage fragment screening path drift')
    c.check(fw.get('pairCount') == len(EXPECTED_PAIRS), 'fragment.pairCount',
            'coverage fragment pair count drift')
    c.check(fw.get('sha256') == sha_file(screening_path), 'fragment.sha',
            'coverage fragment screening hash drift')
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
        c.check(fp.get('byStatus') == status_counts(qq), 'fragment.byStatus',
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
    c.check(fcounts.get('byStatus') == statuses, 'fragment.counts.byStatus',
            'coverage fragment status counts drift')
    c.check(fcounts.get('screenedDelta') == len(EXPECTED_PAIRS),
            'fragment.counts.delta', 'coverage fragment screened delta drift')
    ow = fragment.get('overlapWithAccepted', {})
    c.check(ow.get('intersection') == [], 'fragment.overlap',
            'coverage fragment overlaps the accepted pairs')
    c.check(ow.get('acceptedScreenedPairCount') == len(prior_pairs),
            'fragment.acceptedCount',
            'coverage fragment accepted-pair count drift')
    c.check(ow.get('derivedFrom') == PRIOR_PACKAGES, 'fragment.derivedFrom',
            'coverage fragment does not derive prior coverage from the accepted packages')
    c.check(fragment.get('universe', {}).get('pairCount') == len(all_pairs),
            'fragment.universe', 'coverage fragment universe pair count drift')
    c.check(fragment.get('universe', {}).get('sourceSha256') == sha_rel(QUEUE_REL),
            'fragment.universeHash', 'coverage fragment universe hash drift')

    # ---------------------------------------------------------------- non-claims
    c.check(isinstance(screening.get('nonClaims'), list)
            and len(screening.get('nonClaims')) >= 1, 'nonClaims.missing',
            'screening package has no non-claims statement')
    c.check(isinstance(search_log.get('nonClaims'), list)
            and len(search_log.get('nonClaims')) >= 1, 'search.nonClaims',
            'search log has no non-claims statement')

    # ---------------------------------------------------------------- alias resolutions
    aliases = screening.get('aliasResolutions', [])
    c.check(isinstance(aliases, list), 'aliases.list', 'aliasResolutions is not a list')
    for alias in aliases:
        dangling = alias.get('danglingEndpoints') or []
        resolved = alias.get('resolvedStatements') or []
        c.check(all(d in dangling_ids for d in dangling), 'aliases.danglingKnown',
                'alias record cites an unknown dangling endpoint')
        c.check(all(r in inv_by_id for r in resolved), 'aliases.resolvedKnown',
                'alias record cites an unknown resolved statement')
        all_endpoints = {qq.get('endpoints', {}).get(side, {}).get('statementId')
                         for p in pairs for qq in p.get('queries', [])
                         for side in ('source', 'target')}
        for r in resolved:
            c.check(r in all_endpoints, 'aliases.resolvedUsed',
                    'alias resolved statement %r is not an endpoint of any query' % r)
        c.check(any('dangling' in (q.get('provenance', {}).get('legacyDisposition') or '')
                    or 'alias' in (q.get('provenance', {}).get('legacyDisposition') or '')
                    for q in [qq for p in pairs for qq in p.get('queries', [])]),
                'aliases.disclosure', 'no query discloses the alias resolution')

    # ---------------------------------------------------------------- ledger discipline
    ledger = os.path.abspath(os.path.join(ROOT, 'bounded_audit/coverage.json'))
    c.check(not any(os.path.abspath(p) == ledger for p in OPENED), 'ledger.mustNotRead',
            'the validator opened the mutable R5 cumulative ledger')

    return c.summary('WP-radiative-energy-transfer-03')


if __name__ == '__main__':
    sys.exit(main())
