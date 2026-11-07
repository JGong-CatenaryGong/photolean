#!/usr/bin/env python3
"""Fail-closed mutation suite for the R5 RAD3 package validator.

Run from the repository root:

    python3 bounded_audit/r5/radiative-03/evidence/mutation_tests.py

The script copies the three JSON artifacts to /tmp, mutates copies, and invokes the package
validator through its --screening/--search-log/--fragment overrides. M0 must pass; every other
mutation must exit non-zero. The delivered artifacts are never modified.
"""

import json
import os
import shutil
import subprocess
import sys

ROOT = os.getcwd()
PKG = os.path.join(ROOT, 'bounded_audit/r5/radiative-03')
OUT = '/tmp/rad3-mutations'
shutil.rmtree(OUT, ignore_errors=True)
os.makedirs(OUT)
base = {k: json.load(open(os.path.join(PKG, f))) for k, f in
        [('screening', 'screening.json'), ('search', 'search-log.json'),
         ('fragment', 'coverage-fragment.json')]}


def write(name, obj):
    path = os.path.join(OUT, name)
    json.dump(obj, open(path, 'w'), ensure_ascii=False, indent=2)
    return path


def deep(o):
    return json.loads(json.dumps(o))


def run(screening, search, fragment, label):
    cmd = [sys.executable, os.path.join(PKG, 'validate.py'),
           '--screening', screening, '--search-log', search, '--fragment', fragment]
    proc = subprocess.run(cmd, cwd=ROOT, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True)
    first = next((line for line in proc.stdout.splitlines()
                  if line.startswith('FAIL [')), None)
    print('%-4s exit=%d  %s' % (label, proc.returncode, first or '(no failure line)'))


s0 = os.path.join(OUT, 's0.json')
l0 = os.path.join(OUT, 'l0.json')
f0 = os.path.join(OUT, 'f0.json')
for src, dst in [('screening.json', s0), ('search-log.json', l0),
                 ('coverage-fragment.json', f0)]:
    shutil.copyfile(os.path.join(PKG, src), dst)
run(s0, l0, f0, 'M0')

m = deep(base['screening'])
m['pairs'] = [p for p in m['pairs'] if p['pairId'] != 'P-Forster-Einstein']
run(write('s1.json', m), l0, f0, 'M1')

m = deep(base['screening'])
for p in m['pairs']:
    for q in p['queries']:
        if q['queryId'] == 'Q-RAD3-FI-01':
            q['queryId'] = 'Q-RAD3-FF-01'
            p['queryIds'] = ['Q-RAD3-FF-01']
run(write('s2.json', m), l0, f0, 'M2')

m = deep(base['screening'])
prior = json.load(open('bounded_audit/wp-surface-01/screening.json'))['pairs'][0]
m['pairs'].append({'pairId': prior['pairId'], 'theories': prior['theories'],
                   'primaryCluster': prior['primaryCluster'], 'queryIds': ['QX'],
                   'queries': []})
run(write('s3.json', m), l0, f0, 'M3')

m = deep(base['screening'])
for p in m['pairs']:
    for q in p['queries']:
        if q['queryId'] == 'Q-RAD3-FI-01':
            q['outcome']['evidence']['probe']['declaration'] = (
                'PhotoLean.RelationAudit.BoundedAudit.Rad3.notACertificate')
            q['provenance']['locator'] = (
                'PhotoLean.RelationAudit.BoundedAudit.Rad3.notACertificate')
run(write('s4.json', m), l0, f0, 'M4')

m = deep(base['screening'])
m['pairs'][0]['queries'][0]['endpoints']['source']['signatureSha256'] = '0' * 64
run(write('s5.json', m), l0, f0, 'M5')

m = deep(base['screening'])
for p in m['pairs']:
    for q in p['queries']:
        if q['queryId'] == 'Q-RAD3-FF-01':
            q['expectedKind'] = 'equivalence'
            q['outcome']['evidence']['kind'] = 'equivalence'
run(write('s6.json', m), l0, f0, 'M6')

m = deep(base['screening'])
for p in m['pairs']:
    for q in p['queries']:
        if q['queryId'] == 'Q-RAD3-EF-01':
            q['translations']['left']['reason'] = ''
run(write('s7.json', m), l0, f0, 'M7')

m = deep(base['screening'])
for p in m['pairs']:
    for q in p['queries']:
        if q['queryId'] == 'Q-RAD3-FI-01':
            q['outcome']['evidence']['probe']['declaration'] = (
                'PhotoLean.RelationAudit.BoundedAudit.Rad3.fpEinsBridge')
            q['outcome']['evidence']['probe']['kindCheckTheorem'] = (
                'PhotoLean.RelationAudit.BoundedAudit.Rad3.fpEinsBridge_kind')
            q['provenance']['locator'] = (
                'PhotoLean.RelationAudit.BoundedAudit.Rad3.fpEinsBridge')
run(write('s8.json', m), l0, f0, 'M8')

l = deep(base['search'])
l['entries'] = [e for e in l['entries'] if e['searchId'] != 'SL-RAD3-EF-01']
run(s0, write('l9.json', l), f0, 'M9')

m = deep(base['screening'])
m['snapshot']['coverageLedgerSha256'] = '0' * 64
run(write('s10.json', m), l0, f0, 'M10')

f = deep(base['fragment'])
f['counts']['screenedDelta'] = 12
run(s0, l0, write('f11.json', f), 'M11')

m = deep(base['screening'])
for p in m['pairs']:
    for q in p['queries']:
        if q['queryId'] == 'Q-RAD3-FF-01':
            q['premises']['premiseIds'] = ['RAD3-FF-tauD-nonzero-X', 'RAD3-FF-R-nonzero']
            for d in q['premises']['definitions']:
                if d['id'] == 'RAD3-FF-tauD-nonzero':
                    d['id'] = 'RAD3-FF-tauD-nonzero-X'
run(write('s12.json', m), l0, f0, 'M12')

m = deep(base['screening'])
for p in m['pairs']:
    for q in p['queries']:
        if q['queryId'] == 'Q-RAD3-EI-02':
            q['outcome']['evidence']['composition']['parents'][0]['id'] = 'RAD3-EI-wrong-parent'
run(write('s13.json', m), l0, f0, 'M13')

m = deep(base['screening'])
m['snapshot']['inventorySha256'] = '0' * 64
run(write('s14.json', m), l0, f0, 'M14')

m = deep(base['screening'])
for p in m['pairs']:
    for q in p['queries']:
        if q['queryId'] == 'Q-RAD3-FI-02':
            q['premises']['premiseIds'] = ['RAD3-FIES-kP-nonzero']
run(write('s15.json', m), l0, f0, 'M15')
