#!/usr/bin/env python3
"""Deterministic fail-closed validator for the R2 WP-SURFACE-01 screening package.

Usage:
    python3 bounded_audit/validate_screening.py [path/to/screening.json]

The validator re-derives its facts from the frozen R1 inventory, the accepted
legacy registry, the delivered Lean sources, and the evidence logs. It does not
trust the package's own counts or its own prose.
"""

import argparse
import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

EXPECTED_PAIRS = [
    'P-Marcus-Hammond',
    'P-Marcus-BEP',
    'P-Marcus-Sabatier',
    'P-Hammond-BEP',
    'P-Hammond-Sabatier',
    'P-Hammond-SymmetryFactor',
    'P-BEP-Sabatier',
    'P-BEP-SymmetryFactor',
    'P-Kasha-Sabatier',
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

INV_REL = 'audit_boundary/statement-inventory.json'
QUEUE_REL = 'audit_boundary/pair-queue.json'
CLUSTER_REL = 'audit_boundary/cluster-plan.json'
BOUNDARY_REL = 'audit_boundary/BOUNDARY.md'
REGISTRY_REL = 'relation_audit/registry.json'
SCREENING_REL = 'bounded_audit/wp-surface-01/screening.json'
SEARCH_REL = 'bounded_audit/wp-surface-01/search-log.json'
PROBE_REL = 'bounded_audit/wp-surface-01/probes/Surface-probe.lean'
LEGACY_LOG_REL = 'bounded_audit/wp-surface-01/evidence/legacy-axioms.log'
PROBE_LOG_REL = 'bounded_audit/wp-surface-01/evidence/surface-probe.log'
EXPECTED_REGISTRY_SHA = '25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0'
EXPECTED_LEAN_FILES = 102


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
        print('R2 bounded screening validation')
        print('  root: %s' % ROOT)
        print('  checks failed: %d' % len(self.failures))
        if self.failures:
            for code, message in self.failures:
                print('FAIL [%s] %s' % (code, message))
            print('RESULT: FAIL (%d failed checks)' % len(self.failures))
            return 1
        print('RESULT: PASS (all bounded-screening checks passed)')
        return 0


def parse_axiom_blocks(text):
    """Parse `#print axioms` output into {declaration: set(axioms)}.

    Handles the line wrapping that Lean's formatter introduces. Blocks are
    separated by lines beginning with `=== `; a block may also have no marker.
    """
    blocks = {}
    current = []
    for line in text.splitlines() + ['=== <end>']:
        if line.startswith('=== '):
            chunk = '\n'.join(current)
            current = []
            m = re.search(r"'([^']+)'\s+depends on axioms:\s*\[(.*?)\]", chunk, re.S)
            if m:
                axioms = {a.strip() for a in m.group(2).replace('\n', ' ').split(',')
                          if a.strip()}
                blocks[m.group(1)] = axioms
        else:
            current.append(line)
    return blocks


def parse_probe_axioms(text):
    """Parse the probe log (four `#print axioms` lines, possibly wrapped)."""
    blocks = {}
    joined = re.sub(r'\s*\n\s*', ' ', text)
    for m in re.finditer(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", joined):
        axioms = {a.strip() for a in m.group(2).split(',') if a.strip()}
        blocks[m.group(1)] = axioms
    return blocks


def short_name(decl):
    return decl.rsplit('.', 1)[-1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('screening', nargs='?', default=SCREENING_REL)
    args = parser.parse_args()

    c = Checker()
    if not os.path.exists(os.path.join(ROOT, args.screening)):
        print('FAIL [file.missing] screening package not found: %s' % args.screening)
        print('RESULT: FAIL')
        return 1

    screening = load_rel(args.screening)
    inv = load_rel(INV_REL)
    queue = load_rel(QUEUE_REL)
    cluster = load_rel(CLUSTER_REL)
    registry = load_rel(REGISTRY_REL)
    search_log = load_rel(SEARCH_REL)
    probe_text = read_rel(PROBE_REL)
    legacy_log = read_rel(LEGACY_LOG_REL)
    probe_log = read_rel(PROBE_LOG_REL)

    inv_by_id = {row['id']: row for row in inv['statements']}
    dangling_ids = {d['id'] for d in inv.get('legacyDanglingStatements', [])}
    queue_by_id = {row['pairId']: row for row in queue['pairs']}
    reg_certs = {x['id']: x for x in registry['certificates']}
    legacy_axioms = parse_axiom_blocks(legacy_log)
    probe_axioms = parse_probe_axioms(probe_log)

    # ---------------------------------------------------------------- vocabulary
    c.check(screening.get('schemaVersion') == '1.0.0', 'schema.version',
            'unexpected schemaVersion')
    c.check(screening.get('artifactKind') == 'bounded-screening-package',
            'schema.kind', 'unexpected artifactKind')
    c.check(screening.get('round') == 'R2', 'schema.round', 'unexpected round')
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
    lean_files = []
    for dirpath, _dirnames, filenames in os.walk(os.path.join(ROOT, 'PhotoLean')):
        for name in filenames:
            if name.endswith('.lean'):
                lean_files.append(os.path.join(dirpath, name))
    c.check(len(lean_files) == EXPECTED_LEAN_FILES, 'snapshot.leanFileCount',
            'delivered Lean tree has %d files, expected %d'
            % (len(lean_files), EXPECTED_LEAN_FILES))

    # ---------------------------------------------------------------- pair coverage
    pair_work = screening.get('workPackage', {})
    c.check(pair_work.get('id') == 'WP-SURFACE-01', 'workPackage.id',
            'work package id drift')
    c.check(pair_work.get('pairIds') == EXPECTED_PAIRS, 'workPackage.pairIds',
            'work package pair list is not the approved ten')
    c.check(pair_work.get('pairCount') == len(EXPECTED_PAIRS), 'workPackage.pairCount',
            'work package pair count drift')
    r1wp = pair_work.get('r1ClusterPlanWorkPackage', {})
    diff = r1wp.get('difference', {})
    c.check(diff.get('addedByR2Plan') == ['P-Kasha-Sabatier'],
            'workPackage.r1DifferenceAdded', 'R1/R2 pair-list difference not recorded')
    c.check(diff.get('removedByR2Plan') == ['P-Marcus-SymmetryFactor'],
            'workPackage.r1DifferenceRemoved', 'R1/R2 pair-list difference not recorded')
    c.nonempty(diff.get('note'), 'workPackage.r1DifferenceNote',
               'missing mismatch note')

    pairs = screening.get('pairs', [])
    pair_ids = [p.get('pairId') for p in pairs]
    c.check(len(pair_ids) == len(set(pair_ids)), 'pairs.duplicate',
            'duplicate pair id in screening package')
    c.check(set(pair_ids) == set(EXPECTED_PAIRS), 'pairs.coverage',
            'screening pair set is not exactly the approved ten')
    c.check(len(pair_ids) == len(EXPECTED_PAIRS), 'pairs.count',
            'screening pair count is not ten')

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
                'pair %r has no named query' % pid)
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
        resolved = a.get('resolvedStatementId')
        c.check(resolved in inv_by_id, 'alias.resolved',
                'alias %r resolvedStatementId is not an inventory statement' % aid)
        if resolved in inv_by_id:
            c.check(a.get('resolvedDeclaration') == inv_by_id[resolved]['declaration'],
                    'alias.resolvedDeclaration',
                    'alias %r resolvedDeclaration drift' % aid)
        c.check(a.get('resolutionKind') in {'theorem-rhs-term', 'theorem-lhs-predicate',
                                            'theorem-rhs-predicate'},
                'alias.resolutionKind', 'alias %r has unknown resolutionKind' % aid)
        c.nonempty(a.get('note'), 'alias.note', 'alias %r has no note' % aid)

    # ---------------------------------------------------------------- per-query checks
    non_certified = []
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
                           'query %r %s translation has no requirement note'
                           % (qid, side))

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
                c.check(etype in {'legacy-certificate', 'r2-probe-certificate'},
                        'evidence.type',
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
                if etype == 'legacy-certificate':
                    cert_id = evidence.get('certificateId')
                    cert = reg_certs.get(cert_id)
                    c.check(cert is not None, 'evidence.certMissing',
                            'query %r certificate %r is not in the legacy registry'
                            % (qid, cert_id))
                    if cert is not None:
                        c.check(cert.get('kind') == evidence.get('kind'),
                                'evidence.certKind', 'query %r certificate kind drift' % qid)
                        lean = evidence.get('lean', {})
                        c.check(lean.get('declaration') == cert.get('lean'),
                                'evidence.certLean',
                                'query %r certificate declaration drift' % qid)
                        c.check(lean.get('module') == cert.get('module'),
                                'evidence.certModule',
                                'query %r certificate module drift' % qid)
                        source = evidence.get('source', {})
                        c.check(source.get('path') == cert.get('sourcePath'),
                                'evidence.certSource',
                                'query %r certificate source path drift' % qid)
                        c.check(source.get('sha256') == cert.get('sourceSha256'),
                                'evidence.certSourceHash',
                                'query %r certificate source hash drift' % qid)
                        c.check(set(cert.get('axiomFootprint', [])) <= ALLOWED_AXIOMS,
                                'evidence.certRegistryAxioms',
                                'query %r registry certificate footprint is disallowed' % qid)
                        path = os.path.join(ROOT, cert.get('sourcePath', ''))
                        c.check(os.path.exists(path), 'evidence.certSourceMissing',
                                'query %r certificate source file is missing' % qid)
                        if os.path.exists(path):
                            c.check(sha_file(path) == cert.get('sourceSha256'),
                                    'evidence.certSourceFileHash',
                                    'query %r certificate source file hash drift' % qid)
                            text = open(path, encoding='utf-8').read()
                            short = short_name(cert.get('lean', ''))
                            c.check(re.search(r'\b(def|theorem)\s+%s\b' % re.escape(short),
                                              text) is not None,
                                    'evidence.certDeclarationMissing',
                                    'query %r certificate declaration is not in its source '
                                    'file' % qid)
                        c.check(lean.get('kindCheck', '').find(cert.get('lean', '')) >= 0,
                                'evidence.certKindCheck',
                                'query %r certificate kind check does not name the '
                                'declaration' % qid)
                        axioms = legacy_axioms.get(cert.get('lean'))
                        c.check(axioms is not None, 'evidence.certAxiomLog',
                                'query %r certificate has no axiom-audit log entry' % qid)
                        if axioms is not None:
                            c.check(axioms <= ALLOWED_AXIOMS, 'evidence.certAxiomDisallowed',
                                    'query %r certificate has disallowed axioms: %s'
                                    % (qid, sorted(axioms - ALLOWED_AXIOMS)))
                elif etype == 'r2-probe-certificate':
                    probe = evidence.get('probe', {})
                    c.check(probe.get('path') == PROBE_REL, 'evidence.probePath',
                            'query %r probe path drift' % qid)
                    c.check(probe.get('sha256') == sha_file(os.path.join(ROOT, PROBE_REL)),
                            'evidence.probeHash', 'query %r probe source hash drift' % qid)
                    decl = probe.get('declaration', '')
                    c.check(decl.startswith(
                        'PhotoLean.RelationAudit.BoundedAudit.Surface.'), 'evidence.probeDecl',
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
                    c.check(probe.get('buildCommand', '').startswith('proofs/scripts/lake '
                                                                     'env lean '),
                            'evidence.probeBuild', 'query %r probe build command drift' % qid)
                    axioms = probe_axioms.get(decl)
                    c.check(axioms is not None, 'evidence.probeAxiomLog',
                            'query %r probe declaration has no axiom print-out' % qid)
                    if axioms is not None:
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

    # ---------------------------------------------------------------- search log
    entries = search_log.get('entries', [])
    c.check(search_log.get('artifactKind') == 'bounded-search-log', 'search.kind',
            'search-log artifactKind drift')
    c.check(search_log.get('round') == 'R2', 'search.round', 'search-log round drift')
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
        c.check(isinstance(e.get('searchedKinds'), list) and len(e.get('searchedKinds')) >= 1,
                'search.searchedKinds', 'search entry %r has no searched kinds' % sid)
        c.check(set(e.get('searchedKinds', [])) <= set(KINDS), 'search.kindVocabulary',
                'search entry %r searches an unknown kind' % sid)
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
            c.nonempty(cmd.get('command'), 'search.command', 'search entry %r command '
                                                              'is empty' % sid)
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

    # ---------------------------------------------------------------- alias use
    used_aliases = set()
    for pair in pairs:
        for q in pair.get('queries', []):
            for side in ['source', 'target']:
                stmt = q.get('endpoints', {}).get(side, {}).get('statementId')
                if stmt in dangling_ids:
                    used_aliases.add(stmt)
            for side in ['source', 'target']:
                ep = q.get('endpoints', {}).get(side, {})
                if ep.get('endpointForm') in {'theorem-lhs-predicate',
                                              'theorem-rhs-predicate',
                                              'theorem-rhs-term'}:
                    c.check(any(a.get('resolvedStatementId') == ep.get('statementId')
                                for a in alias_rows), 'alias.formUnresolved',
                            'query %r uses a derived endpoint form without an alias '
                            'resolution' % q.get('queryId'))
    c.check(not used_aliases, 'alias.citedAsEndpoint',
            'dangling legacy aliases are cited as endpoints: %s' % sorted(used_aliases))

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

    # ---------------------------------------------------------------- forbidden tokens
    forbidden = re.compile(r'sorry|admit|^[ \t]*(private[ \t]+|protected[ \t]+)?'
                           r'(axiom|constant)([ \t]|$)', re.M)
    c.check(forbidden.search(probe_text) is None, 'probe.forbiddenToken',
            'probe source contains a forbidden token')

    # ---------------------------------------------------------------- non-claims
    c.check(isinstance(screening.get('nonClaims'), list)
            and len(screening.get('nonClaims')) >= 1, 'nonClaims.missing',
            'screening package has no non-claims statement')

    return c.summary()


if __name__ == '__main__':
    sys.exit(main())
