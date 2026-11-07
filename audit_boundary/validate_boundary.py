#!/usr/bin/env python3
"""Fail-closed validator for the R1 bounded relation-audit boundary.

Run from the PhotoLean repository root:

    python3 audit_boundary/validate_boundary.py

The validator is deliberately independent of the JSON generator. It re-derives the statement
authority from the Lean sources, re-derives every legacy pair summary from the frozen registry,
and recomputes the cluster assignment from the declared affinity policy. Any missing or duplicate
entry, unresolved reference, hash drift, or extra/missing Lean source is a failure.

Exit codes: 0 = every check passed; 1 = at least one check failed.
"""

from __future__ import annotations

import collections
import glob
import hashlib
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BOUNDARY_DIR = os.path.join(ROOT, 'audit_boundary')
INVENTORY_PATH = os.path.join(BOUNDARY_DIR, 'statement-inventory.json')
QUEUE_PATH = os.path.join(BOUNDARY_DIR, 'pair-queue.json')
CLUSTER_PATH = os.path.join(BOUNDARY_DIR, 'cluster-plan.json')
BOUNDARY_PATH = os.path.join(BOUNDARY_DIR, 'BOUNDARY.md')
REGISTRY_PATH = os.path.join(ROOT, 'relation_audit', 'registry.json')
PAIR_INVENTORY_PATH = os.path.join(ROOT, 'relation_audit', 'generated', 'pair_inventory.json')

THEORIES = ['Marcus', 'Hammond', 'BEP', 'Kasha', 'Sabatier', 'Goldschmidt', 'SymmetryFactor',
            'KashaVavilov', 'SternVolmer', 'QuantumYield', 'FluorPhos', 'EnergyGapLaw',
            'StokesShift', 'ICvsISC', 'Forster', 'Einstein', 'RACI']
THEORY_INDEX = {t: i for i, t in enumerate(THEORIES)}
STATUSES = ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope']
RELATION_KINDS = ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition',
                  'observationalEquivalence', 'distinguishability', 'refutation']
CLUSTER_IDS = ['surface-free-energy', 'excited-state-kinetics', 'quenching-quantum-yield',
               'radiative-energy-transfer', 'conical-intersection', 'cross-domain-screening']
PRIORITY = ['conical-intersection', 'surface-free-energy', 'quenching-quantum-yield',
            'radiative-energy-transfer', 'excited-state-kinetics']
FORCED = {'RACI': 'conical-intersection'}
FALLBACK = 'cross-domain-screening'
EXPECTED_REGISTRY_SHA = '25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0'
EXPECTED_THEORY_COUNT = 17
EXPECTED_PAIR_COUNT = 136
EXPECTED_AUTHORITY_DECLARATIONS = 1153
EXPECTED_TOTAL_STATEMENTS = 1154
EXPECTED_SCREENING_ELIGIBLE = 1134
EXPECTED_CONTEXT_TYPES = 20
EXPECTED_LEGACY_STATEMENTS = 52
EXPECTED_LEGACY_DECLARED_ROWS = 35
EXPECTED_LEGACY_UNIQUE_DECLARATIONS = 34
EXPECTED_LEGACY_TRACEABLE_DECLARATIONS = 30
EXPECTED_LEGACY_DANGLING = 4
EXPECTED_LEGACY_THEORY_ANCHORS = 17
EXPECTED_LEGACY_RECORDS = 151
EXPECTED_LEGACY_QUERIES = 151
EXPECTED_LEGACY_CERTIFICATES = 38
EXPECTED_LEGACY_PAIR_ANCHORS = 125
EXPECTED_LEGACY_NAMED_QUERIES = 26
EXPECTED_LEGACY_CERTIFIED_CROSS = 19
EXPECTED_LEGACY_CERTIFIED_INTRA = 5
EXPECTED_CERTIFIED_CROSS_PAIRS = 9
EXPECTED_WORK_PACKAGES = 10
EXPECTED_LEAN_FILES = 102

FAILURES: list[tuple[str, str]] = []


def check(condition: bool, code: str, message: str) -> None:
    if not condition:
        FAILURES.append((code, message))


def load_json(path: str, code: str):
    if not os.path.exists(path):
        FAILURES.append((code, 'missing file: ' + os.path.relpath(path, ROOT)))
        return None
    try:
        with open(path, encoding='utf-8') as fh:
            return json.load(fh)
    except (OSError, json.JSONDecodeError) as exc:
        FAILURES.append((code, 'cannot parse ' + os.path.relpath(path, ROOT) + ': ' + str(exc)))
        return None


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha_file(path: str) -> str | None:
    try:
        with open(path, 'rb') as fh:
            return sha_bytes(fh.read())
    except OSError:
        return None


def relpath(path: str) -> str:
    return os.path.relpath(path, ROOT).replace(os.sep, '/')


# --------------------------------------------------------------------------- Lean parsing
def strip_comments_keep(src: str) -> str:
    out: list[str] = []
    i = 0
    n = len(src)
    depth = 0
    while i < n:
        c = src[i]
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i)
            if j == -1:
                break
            i = j
            continue
        if src.startswith('/-', i):
            depth += 1
            i += 2
            continue
        if depth > 0 and src.startswith('-/', i):
            depth -= 1
            i += 2
            continue
        if depth > 0:
            out.append('\n' if c == '\n' else ' ')
            i += 1
            continue
        out.append(c)
        i += 1
    return ''.join(out)


def ns_stack_at(src: str, pos: int) -> str:
    stack: list[tuple[str, str]] = []
    for line in src[:pos].splitlines():
        t = line.strip()
        m = re.match(r'namespace\s+([A-Za-z_][\w\'.]*)', t)
        if m:
            stack.append(('ns', m.group(1)))
            continue
        m = re.match(r'section(\s+[A-Za-z_][\w\'.]*)?$', t)
        if m:
            stack.append(('sec', ''))
            continue
        m = re.match(r'end(\s+[A-Za-z_][\w\'.]*)?$', t)
        if m:
            if stack:
                stack.pop()
    return '.'.join(name for kind, name in stack if kind == 'ns')


DECL_RE = re.compile(
    r'^(?:noncomputable\s+)?(theorem|def|inductive|structure)\s+([A-Za-z_][\w\'.]*)(.*?)'
    r'(?=:=\s*by|:=\s*$|:=|\n\n)', re.M | re.S)


def signatures(path: str) -> dict[str, dict]:
    src = strip_comments_keep(open(path, encoding='utf-8').read())
    out: dict[str, dict] = {}
    for m in DECL_RE.finditer(src):
        kind = m.group(1)
        name = m.group(2)
        sig = re.sub(r'\s+', ' ', m.group(3) or '').strip()
        ns = ns_stack_at(src, m.start())
        key = f'{ns}.{name}' if ns else name
        out[key] = {'kind': kind, 'signature': sig, 'position': m.start(),
                    'line': src[:m.start()].count('\n') + 1}
    return out


def theory_dir(t: str) -> str | None:
    for name in (t, t.capitalize(), t.upper(), t.lower()):
        d = os.path.join(ROOT, 'theories', name)
        if os.path.isdir(d):
            return d
    return None


def skeleton_of(t: str) -> str | None:
    d = theory_dir(t)
    if d is None:
        return None
    base = os.path.basename(d)
    for name in (base, base.lower(), base.upper()):
        p = os.path.join(d, 'probes', f'{name}-statement-skeleton.lean')
        if os.path.exists(p):
            return p
    return None


def source_dir(t: str) -> str | None:
    for name in (t, t.capitalize(), t.upper(), t.lower()):
        d = os.path.join(ROOT, 'PhotoLean', name)
        if os.path.isdir(d):
            return d
    return None


def resolve_delivered(skeleton_key: str, skeleton: dict, delivered: dict) -> str | None:
    if skeleton_key in delivered:
        return skeleton_key
    bare = skeleton_key.rsplit('.', 1)[-1]
    candidates = [k for k in skeleton if k.rsplit('.', 1)[-1] == bare]
    if len(candidates) != 1:
        return None
    authority_ns = candidates[0].rsplit('.', 1)[0] if '.' in candidates[0] else ''
    delivered_ns = {k.rsplit('.', 1)[0] if '.' in k else '' for k in delivered}
    if authority_ns in delivered_ns:
        return None
    hits = [k for k in delivered if k.rsplit('.', 1)[-1] == bare]
    return hits[0] if len(hits) == 1 else None


def signature_sha(kind: str, declaration: str, signature: str) -> str:
    return sha_bytes((kind + ' ' + declaration + ' ' + signature).encode('utf-8'))


def pair_id(a: str, b: str) -> str:
    return f'P-{a}-{b}' if THEORY_INDEX[a] <= THEORY_INDEX[b] else f'P-{b}-{a}'


def expected_pairs() -> list[tuple[str, str]]:
    out = []
    for i, a in enumerate(THEORIES):
        for b in THEORIES[i + 1:]:
            out.append((a, b))
    return out


# --------------------------------------------------------------------------- checks
def check_boundary_text() -> None:
    if not os.path.exists(BOUNDARY_PATH):
        FAILURES.append(('boundary.missing', 'missing file: audit_boundary/BOUNDARY.md'))
        return
    text = open(BOUNDARY_PATH, encoding='utf-8').read()
    for status in STATUSES:
        check(re.search(r'\b' + re.escape(status) + r'\b', text) is not None,
              'boundary.status', f'BOUNDARY.md does not define status {status!r}')
    for kind in RELATION_KINDS:
        check(re.search(r'\b' + re.escape(kind) + r'\b', text) is not None,
              'boundary.kind', f'BOUNDARY.md does not define evidence kind {kind!r}')
    for phrase, code in [
        ('named proposition-level query', 'boundary.namedQuery'),
        ('pair-level anchor', 'boundary.pairAnchor'),
        ('No pair may be forced into a relation', 'boundary.forcedEdge'),
        ('non-exhaustiveness', 'boundary.nonExhaustive'),
        ('context', 'boundary.context'),
        ('translation', 'boundary.translation'),
        ('observation channel', 'boundary.channel'),
    ]:
        check(phrase.lower() in text.lower(), code, f'BOUNDARY.md is missing {phrase!r}')
    check('refuted' in text and 'eighth relation kind' in text,
          'boundary.refuted', 'BOUNDARY.md must distinguish refuted status from relation kinds')
    check('adjudication' in text, 'boundary.adjudication',
          'BOUNDARY.md must state that adjudication is not a relation kind')


def check_inventory(inv: dict, registry: dict, registry_sha: str) -> dict:
    check(inv.get('schemaVersion') == '1.0.0', 'inventory.schema', 'inventory schemaVersion')
    check(inv.get('artifactKind') == 'bounded-statement-inventory', 'inventory.kind',
          'inventory artifactKind')
    check(inv.get('theoryInventory') == THEORIES, 'inventory.theories',
          'inventory theoryInventory is not the exact seventeen-theory order')
    check(len(inv.get('theoryInventory', [])) == EXPECTED_THEORY_COUNT, 'inventory.theoryCount',
          'inventory theory count is not 17')

    base = inv.get('registryBaseline', {})
    check(base.get('sha256') == registry_sha, 'inventory.registryHash',
          'inventory registryBaseline.sha256 does not match the frozen registry')
    check(base.get('expectedSha256') == EXPECTED_REGISTRY_SHA, 'inventory.registryExpected',
          'inventory expected legacy hash is wrong')
    check(base.get('statementObjects') == EXPECTED_LEGACY_STATEMENTS, 'inventory.registryStatements',
          'inventory registry statement count')
    check(base.get('declaredStatementRows') == EXPECTED_LEGACY_DECLARED_ROWS,
          'inventory.registryDeclaredRows', 'inventory registry declared row count')
    check(base.get('uniqueDeclaredStatements') == EXPECTED_LEGACY_UNIQUE_DECLARATIONS,
          'inventory.registryUniqueDeclarations', 'inventory registry unique declaration count')
    check(base.get('pairLevelAnchors') == EXPECTED_LEGACY_PAIR_ANCHORS,
          'inventory.pairAnchors', 'inventory pair-level anchor count')
    check(base.get('namedPropositionQueries') == EXPECTED_LEGACY_NAMED_QUERIES,
          'inventory.namedQueries', 'inventory named-query count')
    check(base.get('certifiedCrossTheoryRecords') == EXPECTED_LEGACY_CERTIFIED_CROSS,
          'inventory.certCross', 'inventory certified cross-theory count')
    check(base.get('certifiedIntraTheoryRecords') == EXPECTED_LEGACY_CERTIFIED_INTRA,
          'inventory.certIntra', 'inventory certified intra-theory count')
    check(base.get('certifiedCrossTheoryPairs') == EXPECTED_CERTIFIED_CROSS_PAIRS,
          'inventory.certPairs', 'inventory certified cross-theory pair count')

    rows = inv.get('statements', [])
    check(len(rows) == EXPECTED_TOTAL_STATEMENTS, 'inventory.total',
          f'inventory statement rows {len(rows)} != {EXPECTED_TOTAL_STATEMENTS}')
    ids = [r.get('id') for r in rows]
    check(len(ids) == len(set(ids)), 'inventory.duplicateId', 'duplicate statement id')
    declarations = [r.get('declaration') for r in rows]
    check(len(declarations) == len(set(declarations)), 'inventory.duplicateDeclaration',
          'duplicate statement declaration')

    required = {'id', 'theory', 'declaration', 'declarationKind', 'screeningRole',
                'screeningEligible', 'sourceArtifact', 'sourceLine', 'sourceArtifactSha256',
                'sourceSignature', 'signatureSha256', 'version', 'versionBasis', 'authority',
                'legacyRegistry'}
    legacy_required = {'occurs', 'statementIds', 'queryIds', 'recordIds', 'byStatus', 'byKind',
                       'certifiedRecordIds', 'unresolvedRecordIds'}

    # Re-derive authority signatures and delivered maps.
    authority: dict[str, dict] = {}
    delivered_by_theory: dict[str, dict] = {}
    for t in THEORIES:
        skel = skeleton_of(t)
        check(skel is not None, 'inventory.authorityMissing', f'missing authority for {t}')
        if skel is None:
            continue
        authority[t] = signatures(skel)
        sdir = source_dir(t)
        check(sdir is not None, 'inventory.sourceMissing', f'missing source directory for {t}')
        if sdir is None:
            continue
        delivered: dict[str, dict] = {}
        for f in sorted(glob.glob(os.path.join(sdir, '*.lean'))):
            for k, v in signatures(f).items():
                if k in delivered:
                    FAILURES.append(('inventory.deliveredDuplicate',
                                     f'duplicate delivered declaration {k} in {t}'))
                delivered[k] = {**v, 'file': relpath(f)}
        delivered_by_theory[t] = delivered

    all_delivered = set()
    for delivered in delivered_by_theory.values():
        all_delivered |= set(delivered)
    kernel_sigs_all = signatures(os.path.join(ROOT, 'PhotoLean', 'Kernel.lean'))
    all_delivered |= set(kernel_sigs_all)

    per_theory = collections.Counter()
    eligible_by_theory = collections.Counter()
    kind_counts = collections.Counter()
    eligible = 0
    context_types = 0
    covered_declarations = set()

    for row in rows:
        missing = required - set(row)
        check(not missing, 'inventory.rowShape',
              f'statement {row.get("id")!r} missing fields {sorted(missing)}')
        if missing:
            continue
        theory = row['theory']
        check(theory in THEORIES, 'inventory.rowTheory', f'statement {row["id"]!r} has unknown theory')
        check(isinstance(row['declaration'], str) and row['declaration'].startswith('PhotoLean.'),
              'inventory.rowDeclaration', f'statement {row["id"]!r} declaration is not fully qualified')
        check(row['version'] == '1.0.0', 'inventory.rowVersion', f'statement {row["id"]!r} version')
        check(row['versionBasis'] in ('legacy-registry', 'statement-authority'),
              'inventory.rowVersionBasis', f'statement {row["id"]!r} versionBasis')
        check(row['declarationKind'] in ('theorem', 'def', 'inductive', 'structure'),
              'inventory.rowKind', f'statement {row["id"]!r} declarationKind')
        expected_eligible = row['declarationKind'] in ('theorem', 'def')
        check(row['screeningEligible'] is expected_eligible, 'inventory.rowEligible',
              f'statement {row["id"]!r} screeningEligible inconsistent with declarationKind')
        expected_role = ('claim' if row['declarationKind'] == 'theorem'
                         else 'definition' if row['declarationKind'] == 'def' else 'contextType')
        check(row['screeningRole'] == expected_role, 'inventory.rowRole',
              f'statement {row["id"]!r} screeningRole')
        if row['screeningEligible']:
            eligible += 1
            eligible_by_theory[theory] += 1
        else:
            context_types += 1
        per_theory[theory] += 1
        kind_counts[row['declarationKind']] += 1

        lr = row.get('legacyRegistry', {})
        check(isinstance(lr, dict) and legacy_required <= set(lr), 'inventory.rowLegacyShape',
              f'statement {row["id"]!r} legacyRegistry shape')
        if isinstance(lr, dict):
            check(lr.get('occurs') is bool(lr.get('statementIds')), 'inventory.rowLegacyOccurs',
                  f'statement {row["id"]!r} legacyRegistry.occurs')
            if lr.get('occurs'):
                covered_declarations.add(row['declaration'])

        auth = row.get('authority')
        if row.get('sourceKind') == 'shared-kernel':
            check(auth is None, 'inventory.sharedAuthority',
                  'shared-kernel statement must not claim a theory authority')
            check(row['declaration'] == 'PhotoLean.Kernel.barrier', 'inventory.sharedDecl',
                  'unexpected shared-kernel declaration')
            check(row['theory'] == 'Marcus', 'inventory.sharedTheory',
                  'shared-kernel row must be reported under Marcus for legacy compatibility')
        else:
            check(isinstance(auth, dict), 'inventory.authorityShape',
                  f'statement {row["id"]!r} authority is not an object')
            if not isinstance(auth, dict):
                continue
            t = row['theory']
            check(auth.get('artifact') == relpath(skeleton_of(t) or ''), 'inventory.authorityArtifact',
                  f'statement {row["id"]!r} authority artifact')
            check(auth.get('sha256') == sha_file(skeleton_of(t) or ''), 'inventory.authorityHash',
                  f'statement {row["id"]!r} authority sha256')
            skel_key = auth.get('declaration')
            check(skel_key in authority.get(t, {}), 'inventory.authorityDecl',
                  f'statement {row["id"]!r} authority declaration not in skeleton')

        # Source artifact checks.
        artifact = row.get('sourceArtifact')
        check(isinstance(artifact, str) and os.path.exists(os.path.join(ROOT, artifact)),
              'inventory.sourceArtifact', f'statement {row["id"]!r} source artifact missing')
        if not isinstance(artifact, str) or not os.path.exists(os.path.join(ROOT, artifact)):
            continue
        check(row.get('sourceArtifactSha256') == sha_file(os.path.join(ROOT, artifact)),
              'inventory.sourceHash', f'statement {row["id"]!r} sourceArtifactSha256 drift')
        check(isinstance(row.get('sourceLine'), int) and row['sourceLine'] >= 1,
              'inventory.sourceLine', f'statement {row["id"]!r} sourceLine')

        t = row['theory']
        delivered = delivered_by_theory.get(t, {})
        if row.get('sourceKind') == 'shared-kernel':
            kernel_path = os.path.join(ROOT, 'PhotoLean', 'Kernel.lean')
            kernel_sigs = signatures(kernel_path)
            siginfo = kernel_sigs.get(row['declaration'])
            check(siginfo is not None, 'inventory.sharedMissing',
                  'shared-kernel declaration not found in PhotoLean/Kernel.lean')
        else:
            skel_key = (row.get('authority') or {}).get('declaration')
            resolved = resolve_delivered(skel_key, authority.get(t, {}), delivered) if skel_key else None
            check(resolved == row['declaration'], 'inventory.resolution',
                  f'statement {row["id"]!r} does not resolve to {row["declaration"]!r}')
            siginfo = delivered.get(row['declaration'])
            if siginfo is not None and skel_key in authority.get(t, {}):
                check(authority[t][skel_key]['signature'] == siginfo['signature'],
                      'inventory.authoritySignature',
                      f'statement {row["id"]!r} authority signature differs from delivered signature')
        if siginfo is None:
            continue
        check(siginfo['kind'] == row['declarationKind'], 'inventory.kind',
              f'statement {row["id"]!r} declarationKind drift')
        check(siginfo['line'] == row['sourceLine'], 'inventory.line',
              f'statement {row["id"]!r} sourceLine drift')
        expected_sig = (siginfo['kind'] + ' ' + row['declaration'].rsplit('.', 1)[-1]
                        + ' ' + siginfo['signature']).strip()
        check(row['sourceSignature'] == expected_sig, 'inventory.sourceSignature',
              f'statement {row["id"]!r} sourceSignature drift')
        expected_sig_sha = signature_sha(siginfo['kind'], row['declaration'], siginfo['signature'])
        check(row['signatureSha256'] == expected_sig_sha, 'inventory.signatureHash',
              f'statement {row["id"]!r} signatureSha256 drift')

        # Legacy mapping re-derived from the registry.
        legacy_ids = st_by_decl.get(row['declaration'], [])
        expected_qids = sorted({q for sid in legacy_ids for q in queries_by_stmt.get(sid, [])})
        expected_rids = sorted({r for sid in legacy_ids for r in records_by_stmt.get(sid, [])})
        lr = row.get('legacyRegistry', {})
        check(sorted(lr.get('statementIds', [])) == sorted(legacy_ids), 'inventory.legacyIds',
              f'statement {row["id"]!r} legacy statementIds drift')
        check(sorted(lr.get('queryIds', [])) == expected_qids, 'inventory.legacyQueries',
              f'statement {row["id"]!r} legacy queryIds drift')
        check(sorted(lr.get('recordIds', [])) == expected_rids, 'inventory.legacyRecords',
              f'statement {row["id"]!r} legacy recordIds drift')
        expected_status = dict(sorted(collections.Counter(rec_by_id[x]['status'] for x in expected_rids).items()))
        expected_kind = dict(sorted(collections.Counter(rec_by_id[x].get('relationKind') for x in expected_rids
                                                       if rec_by_id[x].get('relationKind')).items()))
        check(lr.get('byStatus') == expected_status, 'inventory.legacyStatus',
              f'statement {row["id"]!r} legacy byStatus drift')
        check(lr.get('byKind') == expected_kind, 'inventory.legacyKind',
              f'statement {row["id"]!r} legacy byKind drift')
        check(sorted(lr.get('certifiedRecordIds', [])) == sorted(x for x in expected_rids if rec_by_id[x]['status'] == 'certified'),
              'inventory.legacyCertified', f'statement {row["id"]!r} legacy certified ids drift')
        check(sorted(lr.get('unresolvedRecordIds', [])) == sorted(x for x in expected_rids if rec_by_id[x]['status'] == 'unresolved'),
              'inventory.legacyUnresolved', f'statement {row["id"]!r} legacy unresolved ids drift')

    check(per_theory and set(per_theory) == set(THEORIES), 'inventory.theoryCoverage',
          'inventory does not cover all seventeen theories')
    check(len(per_theory) == EXPECTED_THEORY_COUNT, 'inventory.theoryCountRows',
          'inventory theory row count')
    check(sum(per_theory.values()) == EXPECTED_TOTAL_STATEMENTS, 'inventory.sum',
          'inventory per-theory counts do not sum to the total')
    check(eligible == EXPECTED_SCREENING_ELIGIBLE, 'inventory.eligible',
          f'screeningEligible {eligible} != {EXPECTED_SCREENING_ELIGIBLE}')
    check(context_types == EXPECTED_CONTEXT_TYPES, 'inventory.contextTypes',
          f'contextType rows {context_types} != {EXPECTED_CONTEXT_TYPES}')

    # Authority source rows.
    sources = inv.get('authoritySources', [])
    check(len(sources) == EXPECTED_THEORY_COUNT, 'inventory.authorityCount',
          'authoritySources does not have seventeen rows')
    source_theories = [s.get('theory') for s in sources]
    check(sorted(source_theories) == sorted(THEORIES), 'inventory.authorityTheories',
          'authoritySources theory set')
    for s in sources:
        t = s.get('theory')
        skel = skeleton_of(t) if t in THEORIES else None
        check(skel is not None and s.get('artifact') == relpath(skel), 'inventory.authorityPath',
              f'authority source path for {t!r}')
        check(skel is not None and s.get('sha256') == sha_file(skel), 'inventory.authoritySourceHash',
              f'authority source hash for {t!r}')
        check(s.get('declarationCount') == len(authority.get(t, {})), 'inventory.authorityCountRow',
              f'authority declaration count for {t!r}')

    # Source file manifest: exact set and hashes.
    manifest = inv.get('sourceFileManifest', {})
    files = manifest.get('files', {}) if isinstance(manifest, dict) else {}
    actual_files = {relpath(f): sha_file(f) for f in glob.glob(os.path.join(ROOT, 'PhotoLean', '**', '*.lean'),
                                                               recursive=True)}
    check(manifest.get('root') == 'PhotoLean', 'inventory.manifestRoot', 'source manifest root')
    check(manifest.get('fileCount') == len(files), 'inventory.manifestCount',
          'source manifest fileCount')
    check(len(files) == EXPECTED_LEAN_FILES, 'inventory.manifestExpectedCount',
          f'source manifest expects {EXPECTED_LEAN_FILES} Lean files, found {len(files)}')
    check(set(files) == set(actual_files), 'inventory.manifestSet',
          'source manifest file set differs from the delivered Lean tree')
    for f, digest in files.items():
        check(actual_files.get(f) == digest, 'inventory.manifestHash',
              f'source manifest hash drift for {f}')

    # No proof placeholders or custom axioms anywhere in the delivered tree.
    for f in actual_files:
        text = strip_comments_keep(open(os.path.join(ROOT, f), encoding='utf-8').read())
        for token in ('sorry', 'admit', 'axiom'):
            check(re.search(r'\b' + token + r'\b', text) is None, 'inventory.forbiddenToken',
                  f'forbidden token {token!r} in {f}')

    # Legacy traceability: every unique declared registry statement is either in the inventory
    # or explicitly recorded as dangling metadata.
    inv_decls = {r['declaration'] for r in rows}
    dangling = inv.get('legacyDanglingStatements', [])
    check(len(dangling) == EXPECTED_LEGACY_DANGLING, 'inventory.danglingCount',
          f'legacy dangling statement count {len(dangling)} != {EXPECTED_LEGACY_DANGLING}')
    dangling_ids = set()
    dangling_decls = set()
    for d in dangling:
        dangling_ids.add(d.get('id'))
        dangling_decls.add(d.get('declaration'))
        check(d.get('declaration') not in inv_decls, 'inventory.danglingInInventory',
              f'dangling declaration {d.get("declaration")!r} is in the inventory')
        check(d.get('id') in st_by_id, 'inventory.danglingId',
              f'dangling statement id {d.get("id")!r} not in registry')
        check(isinstance(d.get('reason'), str) and 'legacy' in d['reason'].lower(),
              'inventory.danglingReason', f'dangling statement {d.get("id")!r} lacks a reason')
        check(d.get('declaration') not in {k for k in inv_decls}, 'inventory.danglingOverlap',
              'dangling declaration overlaps the inventory')
        check(d.get('declaration') not in all_delivered, 'inventory.danglingExists',
              f'dangling declaration {d.get("declaration")!r} actually exists in the delivered tree')
        artifact = d.get('artifact')
        check(isinstance(artifact, str) and os.path.exists(os.path.join(ROOT, artifact)),
              'inventory.danglingArtifact',
              f'dangling statement {d.get("id")!r} artifact path is missing')
    check(len(dangling_decls) == EXPECTED_LEGACY_DANGLING, 'inventory.danglingUnique',
          'dangling declarations are not unique')
    traceable_decls = {r['declaration'] for r in rows if r['legacyRegistry']['occurs']}
    check({s.get('declaration') for s in registry['statements'] if s.get('declaration')}
          == traceable_decls | dangling_decls, 'inventory.registryDeclarationsCovered',
          'registry declarations are not partitioned into traceable inventory rows and '
          'dangling metadata')
    check(len(covered_declarations) == EXPECTED_LEGACY_TRACEABLE_DECLARATIONS,
          'inventory.coveredDeclarations',
          f'traceable legacy declarations {len(covered_declarations)} != '
          f'{EXPECTED_LEGACY_TRACEABLE_DECLARATIONS}')

    anchors = inv.get('legacyTheoryAnchors', [])
    check(len(anchors) == EXPECTED_LEGACY_THEORY_ANCHORS, 'inventory.theoryAnchors',
          'legacy theory anchor count')
    check({a.get('theory') for a in anchors} == set(THEORIES), 'inventory.anchorTheories',
          'legacy theory anchors do not cover all theories')
    check(len({a.get('id') for a in anchors}) == len(anchors), 'inventory.anchorIds',
          'legacy theory anchor ids are not unique')
    expected_anchor_ids = {s['id'] for s in registry['statements'] if not s.get('declaration')}
    check({a.get('id') for a in anchors} == expected_anchor_ids, 'inventory.anchorSet',
          'legacy theory anchors are not exactly the registry statements without a declaration')

    counts = inv.get('counts', {})
    check(counts.get('authorityDeclarations') == EXPECTED_AUTHORITY_DECLARATIONS,
          'inventory.countAuthority', 'authority declaration count')
    check(counts.get('totalStatements') == EXPECTED_TOTAL_STATEMENTS, 'inventory.countTotal',
          'total statement count')
    check(counts.get('screeningEligible') == EXPECTED_SCREENING_ELIGIBLE, 'inventory.countEligible',
          'screening-eligible count')
    check(counts.get('contextTypeStatements') == EXPECTED_CONTEXT_TYPES, 'inventory.countContext',
          'context-type count')
    check(counts.get('sharedKernelStatements') == 1, 'inventory.countShared',
          'shared-kernel count')
    check(counts.get('legacyCoveredUniqueDeclarations') == EXPECTED_LEGACY_TRACEABLE_DECLARATIONS,
          'inventory.countCovered', 'legacy covered unique declaration count')
    check(counts.get('legacyDanglingStatementObjects') == EXPECTED_LEGACY_DANGLING,
          'inventory.countDangling', 'legacy dangling statement count')
    check(counts.get('registryUniqueDeclarations') == EXPECTED_LEGACY_UNIQUE_DECLARATIONS,
          'inventory.countUnique', 'registry unique declaration count')
    check(counts.get('byTheory') == dict(sorted(per_theory.items())), 'inventory.countByTheory',
          'inventory byTheory counts drift')
    check(counts.get('byScreeningEligibleByTheory') == dict(sorted(eligible_by_theory.items())),
          'inventory.countEligibleByTheory', 'inventory screening-eligible byTheory counts drift')
    check(counts.get('byDeclarationKind') == dict(sorted(kind_counts.items())),
          'inventory.countByKind', 'inventory byDeclarationKind counts drift')
    return {'rows': rows, 'dangling_ids': dangling_ids, 'dangling_record_ids': dangling_record_ids}


def check_queue(queue: dict, registry: dict, inv_info: dict) -> dict:
    check(queue.get('schemaVersion') == '1.0.0', 'queue.schema', 'queue schemaVersion')
    check(queue.get('artifactKind') == 'bounded-pair-queue', 'queue.kind', 'queue artifactKind')
    check(queue.get('theoryInventory') == THEORIES, 'queue.theories',
          'queue theoryInventory is not the exact seventeen-theory order')
    check(queue.get('pairCount') == EXPECTED_PAIR_COUNT, 'queue.pairCount', 'queue pairCount')
    check(queue.get('statuses') == STATUSES, 'queue.statuses', 'queue status vocabulary')
    check(queue.get('relationKinds') == RELATION_KINDS, 'queue.kinds',
          'queue relation-kind vocabulary')
    check(set(queue.get('statuses', [])) == set(STATUSES) and len(queue.get('statuses', [])) == 5,
          'queue.statusesSet', 'queue must define exactly the five statuses')
    check(set(queue.get('relationKinds', [])) == set(RELATION_KINDS)
          and len(queue.get('relationKinds', [])) == 7, 'queue.kindsSet',
          'queue must define exactly the seven evidence kinds')
    check('refuted' not in queue.get('relationKinds', []), 'queue.refutedKind',
          'refuted must not be an evidence kind')
    check('adjudication' not in queue.get('relationKinds', []), 'queue.adjudicationKind',
          'adjudication must not be an evidence kind')

    rules = queue.get('requirementRules', {})
    check(rules.get('requiredOutcome') == 'namedQuery', 'queue.ruleOutcome',
          'queue requirement rule must require a named query')
    check(rules.get('permittedAlternative') == 'outOfScope', 'queue.ruleAlternative',
          'queue requirement rule must permit a justified outOfScope alternative')
    check(rules.get('pairLevelAnchorSatisfiesRequirement') is False, 'queue.ruleAnchor',
          'a pair-level anchor must not satisfy the named-query requirement')
    check(rules.get('noForcedRelation') is True, 'queue.ruleForced',
          'queue must forbid forced relations')
    check(rules.get('outcomeAssignedInThisRound') is False, 'queue.ruleAssigned',
          'queue must not assign outcomes in R1')
    check(isinstance(rules.get('outOfScopePermittedOnlyWith'), list)
          and len(rules['outOfScopePermittedOnlyWith']) >= 3, 'queue.ruleOutOfScope',
          'queue must define the outOfScope justification requirements')
    check(queue.get('adjudication', {}).get('assigned') is False, 'queue.adjudication',
          'queue must not assign adjudication in R1')

    pairs = queue.get('pairs', [])
    check(len(pairs) == EXPECTED_PAIR_COUNT, 'queue.pairRows',
          f'queue pair rows {len(pairs)} != {EXPECTED_PAIR_COUNT}')
    pair_ids = [p.get('pairId') for p in pairs]
    check(len(pair_ids) == len(set(pair_ids)), 'queue.duplicatePair', 'duplicate pair id')
    expected = {pair_id(a, b) for a, b in expected_pairs()}
    check(set(pair_ids) == expected, 'queue.pairSet',
          'queue pair set is not exactly the 136 unordered pairs')
    check(len(expected) == EXPECTED_PAIR_COUNT, 'queue.expectedPairs',
          'internal expected pair count')

    by_pair = {p['pairId']: p for p in pairs}
    check(set(by_pair) == expected, 'queue.pairIndex', 'queue pair index')
    for a, b in expected_pairs():
        pid = pair_id(a, b)
        p = by_pair.get(pid)
        check(p is not None, 'queue.missingPair', f'missing pair {pid}')
        if p is None:
            continue
        check(p.get('theories') == [a, b], 'queue.pairTheories',
              f'pair {pid} theory order')
        check(p.get('screeningCluster') in CLUSTER_IDS, 'queue.pairCluster',
              f'pair {pid} has unknown cluster')
        req = p.get('requirement', {})
        check(req.get('requiredOutcome') in ('namedQuery', 'outOfScope'),
              'queue.requirementKind', f'pair {pid} requiredOutcome')
        check(req.get('permittedAlternative') == 'outOfScope', 'queue.requirementAlternative',
              f'pair {pid} permittedAlternative')
        check(req.get('outcomeAssigned') is None, 'queue.requirementAssigned',
              f'pair {pid} must leave the outcome unassigned')
        check(p.get('candidateQueryIds') == [], 'queue.candidateIds',
              f'pair {pid} candidateQueryIds must be empty in R1')
        check(p.get('adjudicationOutcome') is None, 'queue.adjudicationOutcome',
              f'pair {pid} adjudicationOutcome must be null in R1')
        lc = p.get('legacyCoverage', {})
        check(lc.get('legacyLabelIsNotAnAuditJudgment') is True, 'queue.legacyLabel',
              f'pair {pid} must mark the legacy label as non-audit metadata')
        census = lc.get('census', {})
        expected_census = census_by_pair.get(pid, {}).get('legacy', {})
        for key in ('label', 'subtype', 'registry', 'citation'):
            check(census.get(key) == expected_census.get(key), 'queue.census',
                  f'pair {pid} census {key} drift')
        check(census.get('alsoListedIn') == expected_census.get('alsoListedIn', []),
              'queue.censusAlsoListed', f'pair {pid} census alsoListedIn')
        check(census.get('duplicateRegistryRow') == expected_census.get('duplicateRegistryRow'),
              'queue.censusDuplicate', f'pair {pid} census duplicate flag')

        # Recompute the legacy record summary.
        recs = records_by_pair.get(pid, [])
        summary = summarize_records(recs)
        actual = lc.get('registry', {})
        for key in ('recordCount', 'byStatus', 'byRelationKind', 'pairLevelAnchorCount',
                    'namedPropositionQueryCount', 'pairAnchorQueryIds', 'certifiedRecordIds',
                    'unresolvedRecordIds', 'notEstablishedRecordIds', 'hasCertifiedRelation',
                    'hasNamedPropositionQuery', 'hasUnresolved', 'danglingRecordIds',
                    'hasDanglingEndpoint'):
            check(actual.get(key) == summary[key], 'queue.legacySummary',
                  f'pair {pid} legacy summary {key} drift')
        actual_named = actual.get('namedPropositionQueries', [])
        check(len(actual_named) == len(summary['namedPropositionQueries']), 'queue.namedCount',
              f'pair {pid} named query count drift')
        actual_by_id = {q.get('queryId'): q for q in actual_named}
        for expected_row in summary['namedPropositionQueries']:
            qid = expected_row['queryId']
            check(qid in actual_by_id, 'queue.namedMissing', f'pair {pid} missing named query {qid}')
            if qid in actual_by_id:
                for key in ('recordId', 'status', 'relationKind', 'question', 'source',
                            'target', 'context', 'endpointsTraceable'):
                    check(actual_by_id[qid].get(key) == expected_row[key], 'queue.namedRow',
                          f'pair {pid} named query {qid} field {key} drift')
        check(len(actual_named) == len(actual_by_id), 'queue.namedDuplicate',
              f'pair {pid} duplicate named query ids')

    # Queue-wide legacy summary.
    summary = queue.get('legacySummary', {})
    computed = {
        'pairsWithAnyRecord': sum(1 for p in pairs if p['legacyCoverage']['registry']['recordCount'] > 0),
        'pairsWithCertifiedRelation': sum(1 for p in pairs if p['legacyCoverage']['registry']['hasCertifiedRelation']),
        'pairsWithNamedPropositionQuery': sum(1 for p in pairs if p['legacyCoverage']['registry']['hasNamedPropositionQuery']),
        'pairsWithPairLevelAnchorOnly': sum(1 for p in pairs if p['legacyCoverage']['registry']['pairLevelAnchorCount'] > 0
                                            and p['legacyCoverage']['registry']['namedPropositionQueryCount'] == 0),
        'pairsWithUnresolved': sum(1 for p in pairs if p['legacyCoverage']['registry']['hasUnresolved']),
        'censusLabels': dict(sorted(collections.Counter(p['legacyCoverage']['census']['label'] for p in pairs).items())),
        'certifiedCrossTheoryRecords': len([r for r in registry['records'] if r['status'] == 'certified' and is_cross(r)]),
        'certifiedIntraTheoryRecords': len([r for r in registry['records'] if r['status'] == 'certified' and not is_cross(r)]),
    }
    for key, value in computed.items():
        check(summary.get(key) == value, 'queue.summary', f'queue legacySummary {key} drift')
    check(len(summary.get('intraTheoryRecords', [])) == EXPECTED_LEGACY_CERTIFIED_INTRA,
          'queue.intraCount', 'queue intra-theory record count')
    expected_intra = sorted(r['id'] for r in registry['records'] if r['status'] == 'certified' and not is_cross(r))
    check(sorted(x.get('recordId') for x in summary.get('intraTheoryRecords', [])) == expected_intra,
          'queue.intraIds', 'queue intra-theory record ids drift')
    check(summary.get('danglingStatementIds') == sorted(inv_info['dangling_ids']),
          'queue.danglingStatements', 'queue dangling statement ids')
    check(summary.get('danglingQueryIds') == sorted(dangling_query_ids),
          'queue.danglingQueries', 'queue dangling query ids')
    check(summary.get('danglingRecordIds') == sorted(dangling_record_ids),
          'queue.danglingRecords', 'queue dangling record ids')
    check(summary.get('pairsWithDanglingEndpoint') == 3, 'queue.danglingPairs',
          'queue pairs with dangling endpoint')
    check(computed['pairsWithAnyRecord'] == 136, 'queue.coverage', 'not all 136 pairs have a record')
    return by_pair


def check_clusters(plan: dict, queue_by_pair: dict) -> None:
    check(plan.get('schemaVersion') == '1.0.0', 'cluster.schema', 'cluster schemaVersion')
    check(plan.get('artifactKind') == 'bounded-cluster-plan', 'cluster.kind',
          'cluster artifactKind')
    check(plan.get('theoryInventory') == THEORIES, 'cluster.theories',
          'cluster theoryInventory is not the exact seventeen-theory order')
    check(plan.get('clusterVocabulary') == CLUSTER_IDS, 'cluster.vocabulary',
          'cluster vocabulary is not the six fixed clusters')
    clusters = plan.get('clusters', [])
    check(len(clusters) == len(CLUSTER_IDS), 'cluster.count', 'cluster count')
    ids = [c.get('id') for c in clusters]
    check(len(ids) == len(set(ids)), 'cluster.duplicateId', 'duplicate cluster id')
    check(set(ids) == set(CLUSTER_IDS), 'cluster.ids', 'cluster ids are not the six fixed clusters')

    affinity = plan.get('theoryAffinity', {})
    check(set(affinity) == set(THEORIES), 'cluster.affinity',
          'theory affinity does not cover the seventeen theories')
    for t, themes in affinity.items():
        check(isinstance(themes, list) and set(themes) <= set(CLUSTER_IDS), 'cluster.affinityTheme',
              f'theory {t} has an unknown affinity theme')
    policy = plan.get('assignmentPolicy', {})
    check(policy.get('priority') == PRIORITY, 'cluster.priority', 'cluster priority policy')
    check(policy.get('forcedClusterByTheory') == FORCED, 'cluster.forced', 'cluster forced policy')
    check(policy.get('fallbackCluster') == FALLBACK, 'cluster.fallback', 'cluster fallback policy')
    check(policy.get('workPackageMaxPairs') == 16, 'cluster.maxPairs', 'work package max size')

    def cluster_of(a: str, b: str) -> str:
        if a in FORCED:
            return FORCED[a]
        if b in FORCED:
            return FORCED[b]
        shared = set(affinity[a]) & set(affinity[b])
        for c in policy['priority']:
            if c in shared:
                return c
        return policy['fallbackCluster']

    computed: dict[str, list[str]] = collections.defaultdict(list)
    for a, b in expected_pairs():
        computed[cluster_of(a, b)].append(pair_id(a, b))

    for c in clusters:
        cid = c.get('id')
        pids = c.get('pairIds', [])
        check(c.get('pairCount') == len(pids), 'cluster.pairCount',
              f'cluster {cid} pairCount')
        check(sorted(pids) == sorted(computed.get(cid, [])), 'cluster.assignment',
              f'cluster {cid} pair assignment drift')
        for pid in pids:
            q = queue_by_pair.get(pid)
            check(q is not None and q.get('screeningCluster') == cid, 'cluster.queueMismatch',
                  f'pair {pid} cluster {q.get("screeningCluster") if q else None} != {cid}')
        # Disjoint work packages covering the cluster.
        wps = c.get('workPackages', [])
        check(len(wps) >= 1, 'cluster.wpEmpty', f'cluster {cid} has no work package')
        wp_ids = [w.get('id') for w in wps]
        check(len(wp_ids) == len(set(wp_ids)), 'cluster.wpDuplicateId',
              f'cluster {cid} duplicate work-package id')
        wp_pairs: list[str] = []
        for w in wps:
            wp_pids = w.get('pairIds', [])
            check(w.get('pairCount') == len(wp_pids), 'cluster.wpCount',
                  f'work package {w.get("id")} pairCount')
            check(len(wp_pids) <= 16, 'cluster.wpSize',
                  f'work package {w.get("id")} exceeds 16 pairs')
            wp_pairs.extend(wp_pids)
        check(len(wp_pairs) == len(set(wp_pairs)), 'cluster.wpDisjoint',
              f'cluster {cid} work packages overlap')
        check(sorted(wp_pairs) == sorted(pids), 'cluster.wpCoverage',
              f'cluster {cid} work packages do not cover the cluster')

    all_assigned = [p for c in clusters for p in c.get('pairIds', [])]
    check(len(all_assigned) == EXPECTED_PAIR_COUNT, 'cluster.coverageCount',
          'cluster coverage count')
    check(len(all_assigned) == len(set(all_assigned)), 'cluster.overlap',
          'a pair appears in more than one primary cluster')
    check(set(all_assigned) == {pair_id(a, b) for a, b in expected_pairs()},
          'cluster.coverageSet', 'clusters do not cover the 136 pairs')
    coverage = plan.get('coverage', {})
    check(coverage.get('pairCount') == EXPECTED_PAIR_COUNT, 'cluster.coverageField',
          'cluster coverage pairCount')
    check(coverage.get('assigned') == EXPECTED_PAIR_COUNT, 'cluster.assigned',
          'cluster coverage assigned')
    check(coverage.get('unassignedPairIds') == [], 'cluster.unassigned',
          'cluster coverage unassigned pairs')
    check(coverage.get('duplicatePairIds') == [], 'cluster.duplicates',
          'cluster coverage duplicate pairs')
    check(coverage.get('workPackageCount') == EXPECTED_WORK_PACKAGES, 'cluster.wpTotal',
          'cluster work-package total')


def is_cross(record: dict) -> bool:
    q = q_by_id[record['queryId']]
    return st_by_id[q['source']]['theory'] != st_by_id[q['target']]['theory']


def summarize_records(recs: list[dict]) -> dict:
    statuses = collections.Counter(r['status'] for r in recs)
    kinds = collections.Counter(r.get('relationKind') for r in recs if r.get('relationKind'))
    named = [r for r in recs if not q_by_id[r['queryId']]['id'].startswith('q-pair-')]
    anchors = [r for r in recs if q_by_id[r['queryId']]['id'].startswith('q-pair-')]
    named_rows = []
    for r in sorted(named, key=lambda x: x['id']):
        q = q_by_id[r['queryId']]
        named_rows.append({'queryId': q['id'], 'recordId': r['id'], 'status': r['status'],
                           'relationKind': r.get('relationKind'), 'question': q['question'],
                           'source': q['source'], 'target': q['target'], 'context': q['context'],
                           'endpointsTraceable': not (q['source'] in dangling_ids
                                                      or q['target'] in dangling_ids)})
    return {
        'recordCount': len(recs),
        'byStatus': dict(sorted(statuses.items())),
        'byRelationKind': dict(sorted(kinds.items())),
        'pairLevelAnchorCount': len(anchors),
        'namedPropositionQueryCount': len(named),
        'pairAnchorQueryIds': sorted(q_by_id[r['queryId']]['id'] for r in anchors),
        'namedPropositionQueries': named_rows,
        'certifiedRecordIds': sorted(r['id'] for r in recs if r['status'] == 'certified'),
        'unresolvedRecordIds': sorted(r['id'] for r in recs if r['status'] == 'unresolved'),
        'notEstablishedRecordIds': sorted(r['id'] for r in recs if r['status'] == 'notEstablished'),
        'danglingRecordIds': sorted(r['id'] for r in recs if r['id'] in dangling_record_ids),
        'hasDanglingEndpoint': any(r['id'] in dangling_record_ids for r in recs),
        'hasCertifiedRelation': any(r['status'] == 'certified' for r in recs),
        'hasNamedPropositionQuery': bool(named),
        'hasUnresolved': any(r['status'] == 'unresolved' for r in recs),
    }


def main() -> int:
    boundary = os.path.exists(BOUNDARY_PATH)
    inv = load_json(INVENTORY_PATH, 'inventory.missing')
    queue = load_json(QUEUE_PATH, 'queue.missing')
    plan = load_json(CLUSTER_PATH, 'cluster.missing')
    registry = load_json(REGISTRY_PATH, 'registry.missing')
    pair_inventory = load_json(PAIR_INVENTORY_PATH, 'pairInventory.missing')

    print('Bounded relation-audit boundary validation')
    print('  root: ' + ROOT)
    print('  boundary.md: ' + ('present' if boundary else 'MISSING'))
    print(f'  theories: {EXPECTED_THEORY_COUNT}')
    print(f'  pairs: {EXPECTED_PAIR_COUNT}')

    if registry is None:
        for code, message in FAILURES:
            print(f'FAIL [{code}] {message}')
        print('RESULT: FAIL')
        return 1
    registry_sha = sha_file(REGISTRY_PATH)
    if inv is None or queue is None or plan is None or pair_inventory is None:
        for code, message in FAILURES:
            print(f'FAIL [{code}] {message}')
        print('RESULT: FAIL')
        return 1

    # Registry-shape checks needed by the re-derivations below.
    global st_by_id, q_by_id, rec_by_id, st_by_decl, queries_by_stmt, records_by_stmt
    global records_by_pair, dangling_ids, dangling_query_ids, dangling_record_ids, census_by_pair

    st_by_id = {s['id']: s for s in registry.get('statements', [])}
    q_by_id = {q['id']: q for q in registry.get('queries', [])}
    rec_by_id = {r['id']: r for r in registry.get('records', [])}
    check(len(st_by_id) == len(registry.get('statements', [])), 'registry.statementIds',
          'duplicate registry statement id')
    check(len(q_by_id) == len(registry.get('queries', [])), 'registry.queryIds',
          'duplicate registry query id')
    check(len(rec_by_id) == len(registry.get('records', [])), 'registry.recordIds',
          'duplicate registry record id')
    check(len({c['id'] for c in registry.get('certificates', [])})
          == len(registry.get('certificates', [])), 'registry.certificateIds',
          'duplicate registry certificate id')
    check(registry.get('theoryInventory') == THEORIES, 'registry.theories',
          'registry theoryInventory is not the exact seventeen-theory order')
    check(registry.get('pairCount') == EXPECTED_PAIR_COUNT, 'registry.pairCount',
          'registry pairCount')
    check(len(registry.get('statements', [])) == EXPECTED_LEGACY_STATEMENTS,
          'registry.statementCount', 'registry statement count')
    check(len(registry.get('queries', [])) == EXPECTED_LEGACY_QUERIES, 'registry.queryCount',
          'registry query count')
    check(len(registry.get('records', [])) == EXPECTED_LEGACY_RECORDS, 'registry.recordCount',
          'registry record count')
    check(len(registry.get('certificates', [])) == EXPECTED_LEGACY_CERTIFICATES,
          'registry.certificateCount', 'registry certificate count')

    st_by_decl = collections.defaultdict(list)
    for s in registry.get('statements', []):
        if s.get('declaration'):
            st_by_decl[s['declaration']].append(s['id'])
    queries_by_stmt = collections.defaultdict(list)
    for q in registry.get('queries', []):
        queries_by_stmt[q['source']].append(q['id'])
        queries_by_stmt[q['target']].append(q['id'])
    records_by_stmt = collections.defaultdict(list)
    records_by_pair = collections.defaultdict(list)
    for r in registry.get('records', []):
        q = q_by_id.get(r['queryId'])
        check(q is not None, 'registry.recordQuery', f'record {r["id"]} has unknown query')
        if q is None:
            continue
        records_by_stmt[q['source']].append(r['id'])
        records_by_stmt[q['target']].append(r['id'])
        ta = st_by_id.get(q['source'], {}).get('theory')
        tb = st_by_id.get(q['target'], {}).get('theory')
        check(ta in THEORIES and tb in THEORIES, 'registry.statementTheory',
              f'query {q["id"]} endpoint theory unknown')
        if ta in THEORIES and tb in THEORIES and ta != tb:
            records_by_pair[pair_id(ta, tb)].append(r)

    dangling = inv.get('legacyDanglingStatements', [])
    dangling_ids = {d.get('id') for d in dangling}
    dangling_query_ids = {q['id'] for q in registry.get('queries', [])
                          if q['source'] in dangling_ids or q['target'] in dangling_ids}
    dangling_record_ids = {r['id'] for r in registry.get('records', [])
                           if r['queryId'] in dangling_query_ids}
    census_by_pair = {p['pairId']: p for p in pair_inventory.get('pairs', [])}
    check(len(census_by_pair) == EXPECTED_PAIR_COUNT, 'pairInventory.count',
          'pair inventory count')
    check(set(census_by_pair) == {pair_id(a, b) for a, b in expected_pairs()},
          'pairInventory.ids', 'pair inventory ids are not the 136 canonical pairs')

    check_boundary_text()
    inv_info = check_inventory(inv, registry, registry_sha)
    check_queue(queue, registry, inv_info)
    check_clusters(plan, {p['pairId']: p for p in queue.get('pairs', [])})
    check(registry_sha == EXPECTED_REGISTRY_SHA, 'registry.hash',
          f'legacy registry sha256 {registry_sha} != {EXPECTED_REGISTRY_SHA}')

    # Counts printed only after the checks have actually run.
    rows = inv.get('statements', [])
    print(f'  statement rows: {len(rows)} '
          f'(authority {inv.get("counts", {}).get("authorityDeclarations")}, '
          f'shared {inv.get("counts", {}).get("sharedKernelStatements")}, '
          f'eligible {inv.get("counts", {}).get("screeningEligible")})')
    print(f'  unique pairs: {len({p.get("pairId") for p in queue.get("pairs", [])})}')
    print(f'  clusters: {len(plan.get("clusters", []))}')
    print(f'  legacy registry sha256: {registry_sha}')

    if FAILURES:
        for code, message in FAILURES:
            print(f'FAIL [{code}] {message}')
        print(f'RESULT: FAIL ({len(FAILURES)} failed checks)')
        return 1
    print('RESULT: PASS (all boundary checks passed)')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as exc:  # fail closed on an internal error
        print(f'FAIL [internal] {type(exc).__name__}: {exc}')
        print('RESULT: FAIL')
        sys.exit(1)
