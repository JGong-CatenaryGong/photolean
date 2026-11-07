#!/usr/bin/env python3
"""Fail-closed mutation harness for the R5 XD2 package validator.

Usage (repository root):
    python3 bounded_audit/r5/cross-domain-02/evidence/mutation_tests.py

Every case copies the three JSON artifacts into a scratch directory under /tmp, applies exactly one
mutation, and runs `bounded_audit/r5/cross-domain-02/validate.py` against the copies through the
documented `--screening/--search-log/--fragment` overrides. The package itself is never modified.

M0 is the unmutated baseline and must pass (exit 0). Every other case must be FAIL-CLOSED: the
validator must exit 1 and name a failure code. A mutation that still passes is a validator defect
and the harness reports it as such.
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


def load(name):
    with open(os.path.join(PKG, name), encoding='utf-8') as fh:
        return json.load(fh)


def dump(path, payload):
    with open(path, 'w', encoding='utf-8') as fh:
        json.dump(payload, fh, indent=1, ensure_ascii=False)
        fh.write('\n')


def first_query(screening, qid):
    for pair in screening['pairs']:
        for q in pair['queries']:
            if q['queryId'] == qid:
                return q
    raise KeyError(qid)


def m_drop_pair(screening, search_log, fragment):
    screening['pairs'] = screening['pairs'][:-1]
    return screening, search_log, fragment


def m_add_accepted_pair(screening, search_log, fragment):
    donor = dict(screening['pairs'][0])
    donor['pairId'] = 'P-Marcus-Hammond'
    donor['theories'] = ['Marcus', 'Hammond']
    donor['primaryCluster'] = 'surface-free-energy'
    screening['pairs'].append(donor)
    return screening, search_log, fragment


def m_duplicate_query_id(screening, search_log, fragment):
    first_query(screening, 'Q-XD2-EG-02')['queryId'] = 'Q-XD2-EG-01'
    return screening, search_log, fragment


def m_forge_certified(screening, search_log, fragment):
    q = first_query(screening, 'Q-XD2-KV-01')
    q['outcome'] = {
        'status': 'certified',
        'rationale': 'forged for the mutation test',
        'evidence': {'type': 'r5-xd2-probe-certificate', 'kind': q['expectedKind'],
                     'axiomFootprint': ['propext']},
    }
    return screening, search_log, fragment


def m_tamper_endpoint_hash(screening, search_log, fragment):
    q = first_query(screening, 'Q-XD2-SS-01')
    q['endpoints']['source']['signatureSha256'] = '0' * 64
    return screening, search_log, fragment


def m_mislabel_kind(screening, search_log, fragment):
    q = first_query(screening, 'Q-XD2-EG-01')
    q['expectedKind'] = 'equivalence'
    return screening, search_log, fragment


def m_strip_translation_reason(screening, search_log, fragment):
    q = first_query(screening, 'Q-XD2-EI-01')
    q['translations']['left']['reason'] = ''
    return screening, search_log, fragment


def m_delete_search_entry(screening, search_log, fragment):
    search_log['entries'] = [e for e in search_log['entries']
                             if e['searchId'] != 'SL-XD2-FR-02']
    return screening, search_log, fragment


def m_pin_ledger(screening, search_log, fragment):
    screening['snapshot']['coverageLedgerSha256'] = 'f' * 64
    return screening, search_log, fragment


def m_drift_fragment(screening, search_log, fragment):
    fragment['counts']['screenedDelta'] = 10
    return screening, search_log, fragment


def m_theory_name_reason(screening, search_log, fragment):
    q = first_query(screening, 'Q-XD2-IC-01')
    q['outcome']['evidence']['statementLevelReason'] = (
        'Goldschmidt is lattice geometry and ICvsISC is photophysics, so the theories differ.')
    return screening, search_log, fragment


CASES = [
    ('M0', 'baseline (unmutated copies) - must PASS', None, 0),
    ('M1', 'drop one assigned pair', m_drop_pair, 1),
    ('M2', 'add an accepted R2 pair', m_add_accepted_pair, 1),
    ('M3', 'duplicate a query id', m_duplicate_query_id, 1),
    ('M4', 'forge a certified outcome', m_forge_certified, 1),
    ('M5', 'tamper an endpoint signature hash', m_tamper_endpoint_hash, 1),
    ('M6', 'mislabel an expected kind', m_mislabel_kind, 1),
    ('M7', 'strip an outOfScope translation reason', m_strip_translation_reason, 1),
    ('M8', 'delete a search-log entry', m_delete_search_entry, 1),
    ('M9', 'pin the mutable R5 ledger in the snapshot', m_pin_ledger, 1),
    ('M10', 'drift the coverage fragment', m_drift_fragment, 1),
    ('M11', 'replace a statement-level reason with a theory-name contrast',
     m_theory_name_reason, 1),
]


def main():
    base = tempfile.mkdtemp(prefix='xd2-mut-')
    summary = []
    print('scratch directory: %s' % base)
    print('validator: %s' % VALIDATOR)
    print('')
    for case_id, description, mutator, expected in CASES:
        work = os.path.join(base, case_id)
        os.makedirs(work, exist_ok=True)
        screening, search_log, fragment = load('screening.json'), load('search-log.json'), \
            load('coverage-fragment.json')
        if mutator is not None:
            screening, search_log, fragment = mutator(screening, search_log, fragment)
            # keep the fragment honest about the screening hash so the case tests its own target
            import hashlib
            blob = json.dumps(screening, indent=1, ensure_ascii=False) + '\n'
            fragment['workPackage']['sha256'] = hashlib.sha256(blob.encode()).hexdigest()
        sp = os.path.join(work, 'screening.json')
        lp = os.path.join(work, 'search-log.json')
        fp = os.path.join(work, 'coverage-fragment.json')
        dump(sp, screening)
        dump(lp, search_log)
        dump(fp, fragment)
        if mutator is not None:
            # pin the search-log hash so M8 is caught as a missing entry, not only as hash drift
            blob = json.dumps(search_log, indent=1, ensure_ascii=False) + '\n'
            screening['searchLogReference']['sha256'] = \
                __import__('hashlib').sha256(blob.encode()).hexdigest()
            dump(sp, screening)
        cmd = [sys.executable, VALIDATOR, '--screening', sp, '--search-log', lp,
               '--fragment', fp]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        codes = sorted({line.split(']')[0].replace('FAIL [', '').strip()
                        for line in proc.stdout.splitlines() if line.startswith('FAIL [')})
        ok = (proc.returncode == expected)
        summary.append((case_id, description, proc.returncode, codes, ok))
        print('### %s %s' % (case_id, description))
        print('$ %s' % ' '.join(cmd))
        print('exit=%d (expected %d)' % (proc.returncode, expected))
        if codes:
            print('failure codes: %s' % ', '.join(codes))
        print('verdict: %s' % ('OK' if ok else 'HARNESS-FAIL'))
        print('')
    print('SUMMARY')
    print('%-5s %-52s %-6s %s' % ('case', 'mutation', 'exit', 'verdict'))
    for case_id, description, code, codes, ok in summary:
        print('%-5s %-52s %-6d %s' % (case_id, description[:52], code,
                                      'PASS' if case_id == 'M0' and ok else
                                      ('FAIL-CLOSED' if ok else 'HARNESS-FAIL')))
    bad = [row for row in summary if not row[4]]
    print('')
    print('harness verdict: %s' % ('PASS' if not bad else 'FAIL (%d cases)' % len(bad)))
    shutil.rmtree(base, ignore_errors=True)
    return 0 if not bad else 1


if __name__ == '__main__':
    sys.exit(main())
