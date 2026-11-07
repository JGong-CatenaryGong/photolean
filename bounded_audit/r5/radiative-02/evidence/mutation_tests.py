#!/usr/bin/env python3
"""RAD2 /tmp mutation tests: the package validator must fail closed.

Each mutation copies the real package artifacts into a fresh /tmp directory, edits one
copy, runs the real `validate.py` against it, and asserts:
  * the validator exits 1, and
  * the expected failure code appears in its output.

A control run (unmutated copies) must exit 0. The script exits 0 only when the control
passes and every mutation fails closed.

Usage:
    python3 bounded_audit/r5/radiative-02/evidence/mutation_tests.py
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.dirname(HERE)
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(PKG)))
VALIDATOR = os.path.join(PKG, 'validate.py')
SCREENING = os.path.join(PKG, 'screening.json')
SEARCH = os.path.join(PKG, 'search-log.json')
FRAGMENT = os.path.join(PKG, 'coverage-fragment.json')

CASES = []


def load(path):
    with open(path, encoding='utf-8') as fh:
        return json.load(fh)


def dump(obj, path):
    with open(path, 'w', encoding='utf-8') as fh:
        json.dump(obj, fh, indent=2, ensure_ascii=False)
        fh.write('\n')


def run(args):
    proc = subprocess.run([sys.executable, VALIDATOR] + args,
                          cwd=ROOT, capture_output=True, text=True)
    return proc.returncode, proc.stdout + proc.stderr


def first_certified(screening):
    for pair in screening['pairs']:
        for q in pair['queries']:
            if q['outcome']['status'] == 'certified':
                return q
    raise AssertionError('no certified query in the package')


def mutate_duplicate_pair(screening, _search, _fragment):
    screening['pairs'].append(json.loads(json.dumps(screening['pairs'][0])))
    return screening, None, None, ('pairs.duplicate', 'pairs.count')


def mutate_no_query(screening, _search, _fragment):
    screening['pairs'][0]['queries'] = []
    screening['pairs'][0]['queryIds'] = []
    return screening, None, None, ('pair.noQuery',)


def mutate_probe_hash(screening, _search, _fragment):
    first_certified(screening)['outcome']['evidence']['probe']['sha256'] = '0' * 64
    return screening, None, None, ('evidence.probeHash',)


def mutate_endpoint_signature(screening, _search, _fragment):
    screening['pairs'][0]['queries'][0]['endpoints']['source']['signatureSha256'] = '0' * 64
    return screening, None, None, ('endpoint.signatureSha256',)


def mutate_drop_search_entry(screening, search, _fragment):
    search['entries'] = search['entries'][1:]
    return None, search, None, ('search.missing', 'searchLogReference.sha256')


def mutate_relabel_outofscope(screening, _search, _fragment):
    for pair in screening['pairs']:
        for q in pair['queries']:
            if q['outcome']['status'] == 'outOfScope':
                q['outcome']['status'] = 'certified'
                return screening, None, None, ('evidence.type', 'search.certifiedEntry')
    raise AssertionError('no outOfScope query in the package')


def mutate_fragment_count(screening, _search, fragment):
    fragment['pairCount'] = 15
    return None, None, fragment, ('fragment.pairCount',)


CASES = [
    ('duplicate pair row', mutate_duplicate_pair),
    ('pair with no query row', mutate_no_query),
    ('certified probe hash corrupted', mutate_probe_hash),
    ('endpoint signature hash drift', mutate_endpoint_signature),
    ('missing search-log entry', mutate_drop_search_entry),
    ('outOfScope relabelled certified without evidence', mutate_relabel_outofscope),
    ('coverage fragment pair count drift', mutate_fragment_count),
]


def main():
    tmp = tempfile.mkdtemp(prefix='rad2-mut-', dir='/tmp')
    print('# RAD2 /tmp mutation tests')
    print('# tmp: %s' % tmp)
    failures = 0

    # Control: unmutated copies of all three JSON artifacts must PASS.
    control_dir = os.path.join(tmp, 'control')
    os.makedirs(control_dir)
    for src, name in [(SCREENING, 'screening.json'), (SEARCH, 'search-log.json'),
                      (FRAGMENT, 'coverage-fragment.json')]:
        shutil.copy2(src, os.path.join(control_dir, name))
    rc, out = run(['--screening', os.path.join(control_dir, 'screening.json'),
                   '--search-log', os.path.join(control_dir, 'search-log.json'),
                   '--fragment', os.path.join(control_dir, 'coverage-fragment.json')])
    control_ok = rc == 0 and 'RESULT: PASS' in out
    print('CONTROL unmutated copies: exit=%d %s' % (rc, 'PASS' if control_ok else 'FAIL'))
    if not control_ok:
        failures += 1
        print(out)

    for index, (name, fn) in enumerate(CASES, 1):
        case_dir = os.path.join(tmp, 'case-%02d' % index)
        os.makedirs(case_dir)
        screening = load(SCREENING)
        search = load(SEARCH)
        fragment = load(FRAGMENT)
        screening, search, fragment, expected = fn(screening, search, fragment)
        args = []
        if screening is not None:
            p = os.path.join(case_dir, 'screening.json')
            dump(screening, p)
            args += ['--screening', p]
        if search is not None:
            p = os.path.join(case_dir, 'search-log.json')
            dump(search, p)
            args += ['--search-log', p]
        if fragment is not None:
            p = os.path.join(case_dir, 'coverage-fragment.json')
            dump(fragment, p)
            args += ['--fragment', p]
        rc, out = run(args)
        hit = [code for code in expected if ('FAIL [%s]' % code) in out]
        ok = rc != 0 and len(hit) == len(expected)
        print('MUTATION %02d %-48s exit=%d expected=%s hit=%s %s'
              % (index, name, rc, list(expected), hit, 'PASS' if ok else 'FAIL'))
        if not ok:
            failures += 1
            print(out)

    shutil.rmtree(tmp, ignore_errors=True)
    mutation_failures = failures - (1 if not control_ok else 0)
    print('# summary: control %s; %d/%d mutations failed closed'
          % ('PASS' if control_ok else 'FAIL',
             len(CASES) - mutation_failures, len(CASES)))
    if failures:
        print('RESULT: FAIL (%d mutation/control defects)' % failures)
        return 1
    print('RESULT: PASS (%d/%d mutations fail closed; control passes)'
          % (len(CASES), len(CASES)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
