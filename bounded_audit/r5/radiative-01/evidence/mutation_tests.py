#!/usr/bin/env python3
"""Mutation tests for the R5 Package RAD1 validator (fail-closed evidence).

Each test copies the package's three JSON artifacts into a fresh temporary directory, applies
exactly one mutation, repairs the incidental hashes so that only the intended defect remains, and
runs ``validate.py`` against the copy. The validator must exit non-zero and must name the expected
failure code. A positive control runs the unmutated copy and requires exit 0.

Usage:
    python3 bounded_audit/r5/radiative-01/evidence/mutation_tests.py

Exit 0 = every mutation behaved as required. Nothing in the repository is modified.
"""

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.dirname(HERE)
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(PKG)))
SCREENING = os.path.join(PKG, 'screening.json')
SEARCH = os.path.join(PKG, 'search-log.json')
FRAGMENT = os.path.join(PKG, 'coverage-fragment.json')
PROBE = os.path.join(PKG, 'probes', 'RAD1-probe.lean')
PROBE_NAME = 'RAD1-probe.lean'
VALIDATOR = os.path.join(PKG, 'validate.py')


def sha_path(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def load(path):
    with open(path, encoding='utf-8') as fh:
        return json.load(fh)


def dump(path, doc):
    with open(path, 'w', encoding='utf-8') as fh:
        json.dump(doc, fh, indent=2, ensure_ascii=False)
        fh.write('\n')


def find_query(screening, query_id):
    for pair in screening['pairs']:
        for q in pair['queries']:
            if q['queryId'] == query_id:
                return pair, q
    raise SystemExit('query not found: %s' % query_id)


CERTIFIED_QUERY = 'Q-RAD1-MKVV-01'
JURISDICTION_QUERY = 'Q-RAD1-MFO-01'


def repair(work):
    """Re-pin the incidental hashes so only the intended defect survives."""
    screening_path = os.path.join(work, 'screening.json')
    search_path = os.path.join(work, 'search-log.json')
    fragment_path = os.path.join(work, 'coverage-fragment.json')
    screening = load(screening_path)
    if os.path.exists(search_path):
        screening['searchLogReference']['sha256'] = sha_path(search_path)
        dump(screening_path, screening)
    fragment = load(fragment_path)
    fragment['screeningSha256'] = sha_path(screening_path)
    dump(fragment_path, fragment)


def run(work):
    cmd = [sys.executable, VALIDATOR,
           '--screening', os.path.join(work, 'screening.json'),
           '--search-log', os.path.join(work, 'search-log.json'),
           '--fragment', os.path.join(work, 'coverage-fragment.json'),
           '--probe', os.path.join(work, PROBE_NAME)]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    return proc.returncode, proc.stdout + proc.stderr


def mutate_duplicate_pair(work):
    screening = load(os.path.join(work, 'screening.json'))
    screening['pairs'][1]['pairId'] = screening['pairs'][0]['pairId']
    dump(os.path.join(work, 'screening.json'), screening)


def mutate_endpoint_line(work):
    screening = load(os.path.join(work, 'screening.json'))
    _pair, q = find_query(screening, CERTIFIED_QUERY)
    q['endpoints']['source']['sourceLine'] += 1
    dump(os.path.join(work, 'screening.json'), screening)


def mutate_certified_to_unresolved(work):
    screening = load(os.path.join(work, 'screening.json'))
    _pair, q = find_query(screening, CERTIFIED_QUERY)
    q['outcome']['status'] = 'unresolved'
    dump(os.path.join(work, 'screening.json'), screening)


def mutate_jurisdiction_rationale(work):
    screening = load(os.path.join(work, 'screening.json'))
    _pair, q = find_query(screening, JURISDICTION_QUERY)
    q['outcome']['evidence']['jurisdictionRationale'] = ''
    dump(os.path.join(work, 'screening.json'), screening)


def mutate_probe_hash(work):
    screening = load(os.path.join(work, 'screening.json'))
    _pair, q = find_query(screening, CERTIFIED_QUERY)
    q['outcome']['evidence']['probe']['sha256'] = '0' * 64
    dump(os.path.join(work, 'screening.json'), screening)


def mutate_snapshot_hash(work):
    screening = load(os.path.join(work, 'screening.json'))
    screening['snapshot']['inventorySha256'] = '0' * 64
    dump(os.path.join(work, 'screening.json'), screening)


def mutate_kind_mismatch(work):
    screening = load(os.path.join(work, 'screening.json'))
    _pair, q = find_query(screening, CERTIFIED_QUERY)
    q['expectedKind'] = 'equivalence'
    dump(os.path.join(work, 'screening.json'), screening)


def mutate_drop_query(work):
    screening = load(os.path.join(work, 'screening.json'))
    pair = screening['pairs'][0]
    pair['queries'] = pair['queries'][1:]
    pair['queryIds'] = [q['queryId'] for q in pair['queries']]
    dump(os.path.join(work, 'screening.json'), screening)


OLD_MSS_QUESTION = (
    'Is the Stokes emission energy positive — the emission maximum lying above the 0-0 energy — '
    'exactly on the Marcus normal-region side, and negative (inverted emission) exactly in the '
    'Marcus inverted region?')

OLD_MSS_FALSIFICATION = (
    'A pair (lam, e00) at which the emission energy is positive yet the Marcus region predicate '
    'holds (or vice versa) would refute the equivalence.')

OLD_KKV_RATIONALE = (
    'The row is one-way: the exact rule entails spectral invariance; the converse fails in the '
    'lossless corner, where the spectrum is invariant yet the rule fails.')


def mutate_mss_question_direction(work):
    screening = load(os.path.join(work, 'screening.json'))
    _pair, q = find_query(screening, 'Q-RAD1-MSS-01')
    q['chemicalQuestion'] = OLD_MSS_QUESTION
    dump(os.path.join(work, 'screening.json'), screening)


def mutate_mss_falsification(work):
    screening = load(os.path.join(work, 'screening.json'))
    _pair, q = find_query(screening, 'Q-RAD1-MSS-01')
    q['falsificationCondition'] = OLD_MSS_FALSIFICATION
    dump(os.path.join(work, 'screening.json'), screening)


def mutate_kkv_rationale(work):
    screening = load(os.path.join(work, 'screening.json'))
    _pair, q = find_query(screening, 'Q-RAD1-KKV-01')
    q['expectedKindRationale'] = OLD_KKV_RATIONALE
    dump(os.path.join(work, 'screening.json'), screening)


def retie_probe_hash(work):
    """Re-pin every probe hash after a deliberate probe mutation, leaving only that defect."""
    probe_sha = sha_path(os.path.join(work, PROBE_NAME))
    screening = load(os.path.join(work, 'screening.json'))
    screening['probeReference']['sha256'] = probe_sha
    for pair in screening['pairs']:
        for q in pair['queries']:
            evidence = q.get('outcome', {}).get('evidence', {})
            if evidence.get('type') == 'rad1-probe-certificate':
                evidence['probe']['sha256'] = probe_sha
    dump(os.path.join(work, 'screening.json'), screening)


def mutate_mkv_probe_ref(work):
    probe_path = os.path.join(work, PROBE_NAME)
    text = open(probe_path, encoding='utf-8').read()
    old = ('(mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.barrier" "MarcusKvCtx"\n'
           '      "PhotoLean/Marcus/Basic.lean#barrier")')
    new = ('(mkRef "PhotoLean.Marcus" "PhotoLean.Kasha.marcusIC" "MarcusKvCtx"\n'
           '      "PhotoLean/Kernel.lean#barrier")')
    if old not in text:
        raise SystemExit('cannot find the pinned mkvCmp StatementRef in the probe copy')
    with open(probe_path, 'w', encoding='utf-8') as fh:
        fh.write(text.replace(old, new))
    retie_probe_hash(work)


OLD_SS_PROBE_COMMENT = '''/-! ## §4 — Marcus / StokesShift: the emission window closes at the inverted-region boundary

The Stokes emission energy is `e00 - lam`; it turns negative (the emission maximum moves below
the 0-0 energy, the inverted-emission corner) exactly when the 0-0 energy exceeds the
reorganization energy — i.e. exactly in the Marcus inverted region. The delivered row SS-C9 is
re-used here as the certificate's entailment. -/'''


def replace_ss_probe_comment(work, replacement):
    probe_path = os.path.join(work, PROBE_NAME)
    text = open(probe_path, encoding='utf-8').read()
    new_text, count = re.subn(r'/-!\s*##\s*§4\b.*?-/', replacement, text, count=1, flags=re.S)
    if count != 1:
        raise SystemExit('cannot locate the §4 probe comment in the probe copy')
    with open(probe_path, 'w', encoding='utf-8') as fh:
        fh.write(new_text)
    retie_probe_hash(work)


def mutate_ss_probe_comment_reversed(work):
    replace_ss_probe_comment(work, OLD_SS_PROBE_COMMENT)


def mutate_ss_probe_comment_drop_normal(work):
    replacement = '''/-! ## §4 — Marcus / StokesShift: the emission energy is positive exactly in the inverted region

The Stokes emission energy is `emEnergy = e00 - lam`. It is positive exactly in the Marcus
inverted region (`lam < e00`) and zero at `e00 = lam`. The delivered row SS-C9 is re-used here
as the certificate's entailment. -/'''
    replace_ss_probe_comment(work, replacement)


MUTATIONS = [
    ('M1 duplicate pair id', mutate_duplicate_pair, ['pairs.duplicate', 'pairs.coverage']),
    ('M2 endpoint source line', mutate_endpoint_line,
     ['endpoint.sourceLine', 'endpoint.lineMatch']),
    ('M3 certified relabelled unresolved', mutate_certified_to_unresolved,
     ['evidence.searchType', 'search.missing']),
    ('M4 empty jurisdiction rationale', mutate_jurisdiction_rationale,
     ['evidence.jurisdictionRationale']),
    ('M5 tampered probe hash', mutate_probe_hash, ['evidence.probeHash']),
    ('M6 tampered inventory snapshot hash', mutate_snapshot_hash,
     ['snapshot.inventorySha256']),
    ('M7 expected-kind mismatch', mutate_kind_mismatch, ['evidence.kindMatch']),
    ('M8 dropped query row', mutate_drop_query, ['pair.queryIds', 'pair.noQueryRow']),
    ('M9 reversed MSS question', mutate_mss_question_direction,
     ['pin.mss.chemicalQuestion', 'pin.mss.predicateTokens']),
    ('M10 loosened MSS falsification', mutate_mss_falsification,
     ['pin.mss.falsificationCondition', 'pin.mss.exactlyOne']),
    ('M11 Vavilov-leaking KKV rationale', mutate_kkv_rationale,
     ['pin.kkv.expectedKindRationale', 'pin.kkv.independenceLeak']),
    ('M12 stale mkvCmp StatementRef', mutate_mkv_probe_ref,
     ['pin.mkvCmp.statementRef', 'pin.mkvCmp.legacyRef', 'pin.mkvCmp.provenance']),
    ('M13 reversed §4 probe comment', mutate_ss_probe_comment_reversed,
     ['pin.ssProbeComment.text', 'pin.ssProbeComment.reversed', 'pin.ssProbe.reversed',
      'pin.ssProbeComment.inverted', 'pin.ssProbeComment.normal']),
    ('M14 §4 probe comment drops normal region', mutate_ss_probe_comment_drop_normal,
     ['pin.ssProbeComment.text', 'pin.ssProbeComment.normal']),
]


def copy_artifacts(work):
    for src in (SCREENING, SEARCH, FRAGMENT):
        shutil.copy(src, os.path.join(work, os.path.basename(src)))
    shutil.copy(PROBE, os.path.join(work, PROBE_NAME))


def main():
    failures = []
    work = tempfile.mkdtemp(prefix='rad1-mutation-')
    copy_artifacts(work)
    repair(work)
    code, out = run(work)
    control_ok = code == 0 and 'RESULT: PASS' in out
    print('CONTROL unmutated copy: exit=%d %s' % (code, 'PASS' if control_ok else 'FAIL'))
    if not control_ok:
        print(out)
        failures.append('control copy did not pass')
    shutil.rmtree(work, ignore_errors=True)

    for name, mutator, expected_codes in MUTATIONS:
        work = tempfile.mkdtemp(prefix='rad1-mutation-')
        try:
            copy_artifacts(work)
            mutator(work)
            repair(work)
            code, out = run(work)
            hit = [c for c in expected_codes if '[%s]' % c in out]
            ok = code != 0 and bool(hit)
            print('%s: exit=%d expected=%s hit=%s %s'
                  % (name, code, expected_codes, hit, 'PASS' if ok else 'FAIL'))
            if not ok:
                failures.append(name)
                print(out)
        finally:
            shutil.rmtree(work, ignore_errors=True)

    total = len(MUTATIONS) + 1
    if failures:
        print('MUTATION RESULT: FAIL (%d/%d behaved as required; failures: %s)'
              % (total - len(failures), total, failures))
        return 1
    print('MUTATION RESULT: PASS (%d/%d: control passes, every mutation fails closed with the '
          'expected code)' % (total, total))
    return 0


if __name__ == '__main__':
    sys.exit(main())
