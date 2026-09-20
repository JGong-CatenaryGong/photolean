#!/usr/bin/env python3
"""Per-theory statement fidelity checker for the BEP milestone (lead-owned).

Usage: python3 theories/BEP/probes/bep-fidelity.py [--verbose] [--theory <name>]
Exit code: 0 = every delivered signature matches the skeleton word for word;
           1 = a difference exists (details printed) — a missing declaration is NOT a
               difference yet (the milestone is delivered in stages), but it is listed.

The script is a port of `theories/hammond/probes/hammond-fidelity.py`; the theory name
selects the skeleton and the delivered source directory, so one checker serves every
theory of the repository.
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


def _arg(flag, default):
    if flag in sys.argv:
        i = sys.argv.index(flag)
        if i + 1 < len(sys.argv):
            return sys.argv[i + 1]
    return default


ROOT = _repo_root()
THEORY = _arg('--theory', 'BEP')


def _first_existing(paths):
    for p in paths:
        if os.path.exists(p):
            return p
    return paths[0]


# Theory directory (`theories/hammond` is lowercase while `theories/Marcus` is not) and
# source directory (`PhotoLean/Hammond`) follow the repository's historical spelling, so
# resolve both by existence rather than by a naming rule.
_tdir = _first_existing([os.path.join(ROOT, 'theories', n) for n in
                         (THEORY, THEORY.lower(), THEORY.capitalize(), THEORY.upper())])
_sdir = _first_existing([os.path.join(ROOT, 'PhotoLean', n) for n in
                         (THEORY, THEORY.capitalize(), THEORY.upper(), THEORY.lower())])
_skel_candidates = [os.path.join(_tdir, 'probes', f'{n}-statement-skeleton.lean')
                    for n in (os.path.basename(_tdir), os.path.basename(_tdir).lower(),
                              os.path.basename(_tdir).upper())]
SKEL = _first_existing(_skel_candidates)
DELIVERED = sorted(glob.glob(os.path.join(_sdir, '*.lean')))


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
    """name -> normalized signature (comments stripped, whitespace collapsed, up to the
    first `:=`), including `noncomputable def`, plain `def`, `inductive`, `structure` and
    `theorem`.

    `structure` was added when the kasha theory introduced `RateData` (a Prop-valued bundle
    holding the standing physical premises): before that the checker silently skipped every
    `structure` declaration, i.e. it covered 143 of that theory's 144 declarations. Coverage of
    a checker has to be verified, not assumed — the same lesson as the directory sweep of
    `check.sh`. The other theories declare no top-level `structure`, so their reports are
    unchanged (re-run 2026-09-20: Marcus / hammond / BEP identical, kasha 144/144)."""
    src = strip_comments(open(path).read())
    out = {}
    for m in re.finditer(
            r'^(?:noncomputable\s+)?(?:theorem|def|inductive|structure)\s+([A-Za-z_][\w\']*)(.*?)(?=:=\s*by|:=\s*$|:=|\n\n)',
            src, re.M | re.S):
        name = m.group(1)
        sig = re.sub(r'\s+', ' ', (m.group(2) or '')).strip()
        out[name] = sig
    return out


if not os.path.exists(SKEL):
    print(f"!! statement authority missing: {SKEL}")
    print("   (no statement has been calibrated for this theory yet — nothing to check)")
    sys.exit(2)

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

print(f"theory                     : {THEORY}")
print(f"statement authority        : {os.path.relpath(SKEL, ROOT)}")
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
