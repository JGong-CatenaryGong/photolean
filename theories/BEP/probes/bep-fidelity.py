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


def _ns_stack_at(src, pos):
    """Namespace path enclosing `pos`, tracked line by line.

    Added 2026-09-22 (photobatch): the checker used to key signatures by BARE declaration name,
    so a nested `namespace Rat` shadowed same-named outer rows — the photobatch authorities
    declare e.g. `aOfB` twice (once over ℝ, once over ℚ) and the report showed five FALSE
    signature differences on verbatim copies (found by prover_d on `--theory Einstein`;
    measured: Einstein and StokesShift each reported 5). Keying by the namespace path fixes it
    and is behaviour-preserving for the seven earlier theories (they have no same-named rows in
    a nested namespace — re-run evidence in the experience bank entry of 2026-09-22). `section`
    is tracked so that a bare `end` of a section does not pop a namespace.
    """
    stack = []
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
            continue
    return '.'.join(name for kind, name in stack if kind == 'ns')


def signatures(path):
    """qualified name -> normalized signature (comments stripped, whitespace collapsed, up to
    the first `:=`), including `noncomputable def`, plain `def`, `inductive`, `structure` and
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
        ns = _ns_stack_at(src, m.start())
        out[f"{ns}.{name}" if ns else name] = sig
    return out


if not os.path.exists(SKEL):
    print(f"!! statement authority missing: {SKEL}")
    print("   (no statement has been calibrated for this theory yet — nothing to check)")
    sys.exit(2)

skel_all = signatures(SKEL)
skel = skel_all

# Milestone scoping (`--milestone <name>`, e.g. `--milestone K1`) — added 2026-09-20 after an
# independent verifier found that the milestone acceptance criterion "44/44 word-for-word" was not
# expressible: the unscoped checker counts every delivered milestone at once, so the number grows
# while a milestone's own batch is being verified. The scope is the set of declarations the
# authority declares inside the `/-! ## <name> ...` section. Section titles are matched by prefix,
# so `--milestone K5b` selects the K5b block (and, if present, its `### K5b ...` sub-block, which
# also starts with the milestone token).
MS = _arg('--milestone', None)
if MS:
    src = strip_comments(open(SKEL).read())
    names, cur, stack = set(), None, []
    # declarations of a section carry their own `theorem`/`def` line; headers are `/-! ## <token>`.
    # Names are collected namespace-qualified (same tracking as `signatures`, added 2026-09-22).
    for line in open(SKEL).read().splitlines():
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
            continue
        m = re.match(r'\s*/-! #*\s*(\S+)', line)
        if m:
            cur = m.group(1).rstrip('.')
            continue
        m = re.match(r'^(?:noncomputable\s+)?(?:theorem|def|inductive|structure)\s+([A-Za-z_][\w\']*)', line)
        if m and cur and (cur == MS or cur.startswith(MS)):
            ns = '.'.join(name for kind, name in stack if kind == 'ns')
            names.add(f"{ns}.{m.group(1)}" if ns else m.group(1))
    if not names:
        print(f"!! no declarations found for milestone '{MS}' — check the section title in the authority")
        sys.exit(2)
    skel = {n: s for n, s in skel_all.items() if n in names}

diff, same, extra, met = [], 0, [], set()

def _resolve(name, skel):
    """Resolve a delivered (possibly namespace-qualified) name to an authority key.

    Exact qualified match first; otherwise fall back to a BARE-name match **only when exactly
    one authority key carries that bare name**. The fallback preserves the behaviour of the
    seven earlier theories, whose authorities declare at top level while the delivered modules
    sit in `namespace PhotoLean.<Theory>` (measured 2026-09-22: Marcus 51/51 both before and
    after this change). The exact branch fixes the photobatch's nested-`Rat` shadowing, where
    the same bare name appears twice in the authority (once over ℝ, once over ℚ)."""
    if name in skel:
        return name
    bare = name.rsplit('.', 1)[-1]
    cands = [k for k in skel if k.rsplit('.', 1)[-1] == bare]
    if len(cands) == 1:
        return cands[0]
    return None


for f in DELIVERED:
    got = signatures(f)
    for name, sig in got.items():
        key = _resolve(name, skel)
        if key is None:
            # outside the milestone scope: not a difference, not an extra (report separately)
            if MS and _resolve(name, skel_all) is not None:
                continue
            extra.append(f"{os.path.basename(f)}::{name}")
            continue
        met.add(key)
        a = re.sub(r'\s+', ' ', skel[key]).strip()
        if a == sig:
            same += 1
        else:
            diff.append((os.path.basename(f), key, a, sig))

missing = sorted(set(skel) - met)

print(f"theory                     : {THEORY}")
print(f"statement authority        : {os.path.relpath(SKEL, ROOT)}")
print(f"milestone scope            : {MS if MS else '(whole theory)'}")
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
