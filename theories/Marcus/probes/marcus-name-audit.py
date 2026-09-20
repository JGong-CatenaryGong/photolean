#!/usr/bin/env python3
"""Structural audit for the Marcus theory: for every definition, count how many times it is
referenced by theorem/definition bodies elsewhere.  A definition constrained by no theorem is a
structural smell (it could be changed silently).

Scope: PhotoLean/Marcus/*.lean.  Namespace/comment aware: comments are stripped first so that
English prose starting with a keyword is never mistaken for a declaration.

Run:  python3 theories/Marcus/probes/marcus-name-audit.py
"""
import re, glob, os


def strip_comments(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
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
            i += 1
            continue
        out.append(src[i])
        i += 1
    return ''.join(out)


root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
files = sorted(glob.glob(os.path.join(root, 'PhotoLean/Marcus/*.lean')))
code = {os.path.basename(f): strip_comments(open(f, encoding='utf-8').read()) for f in files}

# every def / inductive carries its own definition line, which must not count as a reference
decls = {}
for f, src in code.items():
    for m in re.finditer(r'^(?:noncomputable\s+)?(def|inductive)\s+([A-Za-z_][\w\']*)', src, re.M):
        decls[m.group(2)] = f

print(f"{'definition':<22}{'declared in':<18}{'references'}")
print('-' * 56)
unconstrained = []
for name in sorted(decls):
    uses = 0
    for f, src in code.items():
        for line in src.split('\n'):
            if re.match(r'^(?:noncomputable\s+)?(def|inductive|theorem)\s+' + re.escape(name) + r'\b', line.strip()):
                continue          # the declaration itself
            if re.search(r'\b' + re.escape(name) + r'\b', line):
                uses += 1
    if uses == 0:
        unconstrained.append(name)
    print(f"{name:<22}{decls[name]:<18}{uses}")
print()
print(f"definitions/inductives audited: {len(decls)}")
print("unconstrained: " + (", ".join(unconstrained) if unconstrained else "none"))
