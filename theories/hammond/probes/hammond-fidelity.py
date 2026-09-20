#!/usr/bin/env python3
"""Per-theory statement fidelity checker for the Hammond milestone (lead-owned).

Usage: python3 theories/hammond/probes/hammond-fidelity.py [--verbose]
Exit code: 0 = every delivered signature matches the skeleton word for word;
           1 = a difference exists (details printed) — a missing declaration is NOT a
               difference yet (the milestone is delivered in stages), but it is listed.
"""
import re, sys, glob, os


def _repo_root():
    """Walk up to the repository root (the directory holding proofs/ENGINE.yml) so the
    script keeps working if the theory directory moves."""
    d = os.path.dirname(os.path.abspath(__file__))
    while d != os.path.dirname(d):
        if os.path.exists(os.path.join(d, 'proofs', 'ENGINE.yml')):
            return d
        d = os.path.dirname(d)
    return os.getcwd()


ROOT = _repo_root()
SKEL = os.path.join(ROOT, 'theories/hammond/probes/hammond-statement-skeleton.lean')
DELIVERED = sorted(glob.glob(os.path.join(ROOT, 'PhotoLean/Hammond/*.lean')))


def strip_comments(src):
    """Remove Lean comments (nested block comments and line comments) so that prose in doc
    comments (e.g. lines starting with the word "theorem") is not mistaken for a declaration."""
    out = []
    i, n, depth = 0, len(src), 0
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


def signatures(path):
    """name -> normalized signature (comments stripped, whitespace collapsed, up to the first :=)."""
    src = strip_comments(open(path).read())
    out = {}
    for m in re.finditer(
            r'^(?:noncomputable\s+)?(?:theorem|def|inductive)\s+([A-Za-z_][\w\']*)(.*?)(?=:=\s*by|:=\s*$|:=|\n\n)',
            src, re.M | re.S):
        name = m.group(1)
        sig = re.sub(r'\s+', ' ', (m.group(2) or '')).strip()
        out[name] = sig
    return out


skel = signatures(SKEL)
diff, same, extra, met = [], 0, [], set()

for f in DELIVERED:
    got = signatures(f)
    for name, sig in got.items():
        if name not in skel:
            extra.append(f"{os.path.basename(f)}::{name}")
            continue
        met.add(name)
        a = re.sub(r'\s+', ' ', skel[name]).strip()
        if a == sig:
            same += 1
        else:
            diff.append((os.path.basename(f), name, a, sig))

missing = sorted(set(skel) - met)

print(f"skeleton declarations      : {len(skel)}")
print(f"delivered, word-for-word   : {same}")
print(f"delivered, not in authority: {len(extra)} (auxiliary declarations, not a difference)")
print(f"not delivered yet          : {len(missing)}")
print(f"signature differences      : {len(diff)}")
if diff:
    for f, n, a, b in diff:
        print(f"\n✗ {f}::{n}\n  skeleton : {a[:200]}\n  delivered: {b[:200]}")
if '--verbose' in sys.argv:
    for e in extra:
        print("  (extra)", e)
    for m_ in missing:
        print("  (missing)", m_)
sys.exit(1 if diff else 0)
