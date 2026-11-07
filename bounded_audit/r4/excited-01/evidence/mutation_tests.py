#!/usr/bin/env python3
"""Fail-closed mutation tests for the R4 E1 package validator.

Each test copies the package to a temporary directory, applies one mutation, and
runs the real validator with --package. The validator must exit nonzero. The log
is written to evidence/mutation-tests.log.
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.dirname(HERE)
VALIDATOR = os.path.join(PKG, 'validate.py')
FILES = ['screening.json', 'search-log.json', 'coverage-fragment.json', 'validate.py']
PROBE_FILES = ['E1-probe.lean', 'compile.log', 'scan.log']


def fresh(mut):
    for name in FILES:
        shutil.copy2(os.path.join(PKG, name), os.path.join(mut, name))
    for name in PROBE_FILES:
        shutil.copy2(os.path.join(PKG, 'probes', name), os.path.join(mut, 'probes', name))


def edit_json(path, fn):
    with open(path, encoding='utf-8') as fh:
        d = json.load(fh)
    fn(d)
    with open(path, 'w', encoding='utf-8') as fh:
        json.dump(d, fh, indent=2, ensure_ascii=False)
        fh.write('\n')


def duplicate_pair(mut):
    edit_json(os.path.join(mut, 'screening.json'),
              lambda d: d['pairs'].append(json.loads(json.dumps(d['pairs'][0]))))


def drop_query(mut):
    edit_json(os.path.join(mut, 'screening.json'),
              lambda d: (d['pairs'][0].__setitem__('queryIds', []),
                         d['pairs'][0].__setitem__('queries', [])))


def corrupt_probe_hash(mut):
    def fn(d):
        for q in d['pairs'][0]['queries']:
            q['outcome']['evidence']['probe']['sha256'] = '0' * 64
    edit_json(os.path.join(mut, 'screening.json'), fn)


def endpoint_hash_drift(mut):
    edit_json(os.path.join(mut, 'screening.json'),
              lambda d: d['pairs'][0]['queries'][0]['endpoints']['source']
              .__setitem__('signatureSha256', '0' * 64))


def drop_search_entry(mut):
    edit_json(os.path.join(mut, 'search-log.json'),
              lambda d: d.__setitem__('entries', d['entries'][1:]))


def relabel_status(mut):
    edit_json(os.path.join(mut, 'screening.json'),
              lambda d: d['pairs'][0]['queries'][0]['outcome']
              .__setitem__('status', 'unresolved'))


MUTATIONS = [
    ('duplicate pair row', duplicate_pair),
    ('pair with no query row', drop_query),
    ('certified query with a corrupted probe hash', corrupt_probe_hash),
    ('endpoint signature hash drift', endpoint_hash_drift),
    ('missing search-log entry for an unresolved query', drop_search_entry),
    ('certified query relabelled unresolved without evidence', relabel_status),
]


def main():
    lines = ['# R4 E1 package mutation tests',
             '# validator: python3 bounded_audit/r4/excited-01/validate.py --package <mutant>',
             '# each mutation must make the validator exit nonzero', '']
    survived = 0
    for name, fn in MUTATIONS:
        mut = tempfile.mkdtemp(prefix='e1-mut-')
        os.makedirs(os.path.join(mut, 'probes'), exist_ok=True)
        fresh(mut)
        fn(mut)
        proc = subprocess.run([sys.executable, VALIDATOR, '--package', mut],
                              capture_output=True, text=True)
        fails = [ln for ln in proc.stdout.splitlines() if ln.startswith('FAIL')]
        lines.append('## %s' % name)
        lines.append('exit=%d' % proc.returncode)
        lines.extend(fails[:5])
        lines.append('')
        print('%-58s exit=%d fails=%d' % (name, proc.returncode, len(fails)))
        if proc.returncode == 0:
            survived += 1
        shutil.rmtree(mut, ignore_errors=True)
    lines.append('mutations=%d survived=%d' % (len(MUTATIONS), survived))
    with open(os.path.join(HERE, 'mutation-tests.log'), 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(lines) + '\n')
    print('mutations=%d survived=%d' % (len(MUTATIONS), survived))
    return 0 if survived == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
