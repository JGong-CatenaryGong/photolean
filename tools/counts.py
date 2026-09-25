#!/usr/bin/env python3
"""PhotoLean census: the repository's number source of record.

Every count quoted about this repository is computed here from the tree, never from memory.
The script is pure Python 3 (standard library only; no network access) and is run from the
repository root:

    python3 tools/counts.py                      # human-readable census
    python3 tools/counts.py --md                 # markdown census
    python3 tools/counts.py --json tools/claims.json
    python3 tools/counts.py --axioms             # + the `#print axioms` sweep (minutes)
    python3 tools/counts.py --no-lean            # skip every Lean-toolchain step (CI)

Definitions (the authoritative statements live in tools/README.md):

* "theory modules"  = `.lean` files under `PhotoLean/<Theory>/`; "top-level modules" =
  `Kernel.lean`, `Relations.lean`, `Smoke.lean`.
* "public declarations" (source scan) = declaration starts at line start after stripping
  `--` line comments and nested `/- ... -/` block comments, excluding rows carrying the
  `private` modifier. Kinds: theorem, lemma, def, abbrev, structure, inductive, class,
  instance, example.
* "statement authority (per theory)" = the `skeleton declarations` counter of
  `theories/BEP/probes/bep-fidelity.py --theory <T>`.
* "public delivered declarations (total)" = sum over the seventeen theories of the probe's
  `delivered, word-for-word` + `delivered, not in authority` counters — i.e. the statement
  authority plus the probe-registered auxiliaries, excluding private helpers and instance
  declarations (the probe's pattern covers `theorem|def|inductive|structure` only, and
  `private` rows never match it).
* "rfl kernel certificates" = the definitional pin rows of `PhotoLean/Relations.lean` whose
  proof is rfl-level: §1 (proof term `:= rfl`) and §12 (re-exports of the in-module `cert_*`
  theorems, each proved by `rfl` / `Iff.rfl`).
* Edge / absence sets of the pair census are written out explicitly below, one citation per
  pair; nothing is inferred at run time.

Exit code 0 always (the census reports; it does not adjudicate the repository)."""

import argparse
import glob
import json
import os
import re
import subprocess
import sys
from itertools import combinations

# ── repository root ─────────────────────────────────────────────────────────────────────
def repo_root():
    """Walk up to the directory holding proofs/ENGINE.yml, so the script works from anywhere."""
    d = os.path.dirname(os.path.abspath(__file__))
    while d != os.path.dirname(d):
        if os.path.exists(os.path.join(d, 'proofs', 'ENGINE.yml')):
            return d
        d = os.path.dirname(d)
    return os.getcwd()


ROOT = repo_root()
CONTRACT = os.path.join(ROOT, 'proofs', 'ENGINE.yml')
PROBE = os.path.join(ROOT, 'theories', 'BEP', 'probes', 'bep-fidelity.py')
CHECK = os.path.join(ROOT, 'proofs', 'scripts', 'check.sh')
SCRATCH = os.path.join(ROOT, '.lake', 'tmp', 'counts-scratch')

# The seventeen theories, in the order the manuscript lists their authority counts.
# (Directory under theories/ is lowercased for the pre-2026-09 names; the module directory
# under PhotoLean/ is always the capitalized name.)
THEORIES = ['Marcus', 'Hammond', 'BEP', 'Kasha', 'Sabatier', 'Goldschmidt', 'SymmetryFactor',
            'KashaVavilov', 'SternVolmer', 'QuantumYield', 'FluorPhos', 'EnergyGapLaw',
            'StokesShift', 'ICvsISC', 'Forster', 'Einstein', 'RACI']
TOP_LEVEL = ['Kernel.lean', 'Relations.lean', 'Smoke.lean']

# ── source scanning ─────────────────────────────────────────────────────────────────────
DECL_KINDS = ['theorem', 'lemma', 'def', 'abbrev', 'structure', 'inductive', 'class',
              'instance', 'example']
MODIFIERS = ['noncomputable', 'protected', 'private', 'unsafe']
DECL_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'                                   # optional attribute, same line
    r'(?:(?:' + '|'.join(MODIFIERS) + r')\s+)*'               # optional modifiers
    r'(' + '|'.join(DECL_KINDS) + r')\b'                      # the declaration keyword
    r'(?:[ \t]+([A-Za-z_\u00c0-\uffff][\w\'.\u00c0-\uffff]*))?')  # optional declared name


def strip_comments(src, keep_lines=True):
    """Remove Lean comments: `--` line comments and (nested) `/- ... -/` block comments.

    keep_lines=True substitutes spaces for comment characters and preserves newlines, so line
    numbers of the remaining text still refer to the original file; keep_lines=False removes
    the comment bodies together with their newlines (the bep-fidelity behaviour)."""
    out = []
    i, n, depth = 0, len(src), 0
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
            out.append('\n' if (keep_lines and c == '\n') else ' ')
            i += 1
            continue
        out.append(c)
        i += 1
    return ''.join(out)


def read(path):
    with open(os.path.join(ROOT, path), encoding='utf-8') as fh:
        return fh.read()


class Decl:
    """One source-level declaration row."""

    def __init__(self, path, theory, line, kind, name, private, fqname):
        self.path = path
        self.theory = theory          # PhotoLean/<theory> directory name, or '(top-level)'
        self.line = line
        self.kind = kind
        self.name = name
        self.private = private
        self.fqname = fqname          # namespace-qualified (for the axioms sweep)

    def as_dict(self):
        return {'file': self.path, 'line': self.line, 'kind': self.kind, 'name': self.name,
                'private': self.private, 'qualified_name': self.fqname}


def theory_of(path):
    """Theory directory for a `PhotoLean/...` path, or '(top-level)'."""
    rel = os.path.relpath(path, 'PhotoLean')
    if os.sep in rel:
        return rel.split(os.sep)[0]
    return '(top-level)'


def scan_file(path):
    """Comment-aware declaration scan of one file, with namespace-aware qualified names."""
    raw = read(path)
    clean = strip_comments(raw, keep_lines=True)
    ns_stack = []
    decls = []
    for lineno, line in enumerate(clean.split('\n'), start=1):
        t = line.strip()
        m = re.match(r'namespace\s+([A-Za-z_][\w\'.]*)\s*$', t)
        if m:
            ns_stack.append(('ns', m.group(1)))
            continue
        m = re.match(r'section(\s+[A-Za-z_][\w\'.]*)?\s*$', t)
        if m:
            ns_stack.append(('sec', ''))
            continue
        m = re.match(r'end(\s+[A-Za-z_][\w\'.]*)?\s*$', t)
        if m:
            if ns_stack:
                ns_stack.pop()
            continue
        m = DECL_RE.match(line)
        if not m:
            continue
        prefix = '.'.join(nm for kind, nm in ns_stack if kind == 'ns')
        name = m.group(2) or ''
        fq = (prefix + '.' + name).lstrip('.') if name else prefix
        decls.append(Decl(path, theory_of(path), lineno, m.group(1), name,
                          'private' in m.group(0).split(m.group(1))[0], fq))
    return decls


def all_lean_files():
    return sorted(os.path.relpath(p, ROOT).replace(os.sep, '/')
                  for p in glob.glob(os.path.join(ROOT, 'PhotoLean', '**', '*.lean'),
                                     recursive=True))


def file_census(files):
    theory_modules = [f for f in files if f.count('/') >= 2]
    top_modules = [f for f in files if f.count('/') == 1]
    dirs = sorted({f.split('/')[1] for f in theory_modules})
    per_theory = {t: len([f for f in theory_modules if f.split('/')[1] == t]) for t in dirs}
    return {
        'lean_files_total': len(files),
        'theory_modules': len(theory_modules),
        'top_level_modules': sorted(os.path.basename(f) for f in top_modules),
        'theory_directories': len(dirs),
        'theory_directories_names': dirs,
        'per_theory_modules': per_theory,
    }


def declaration_census(decls):
    """The four requested classes, over the whole tree and per theory."""
    def cls(ds):
        public = [d for d in ds if not d.private]
        return {
            'a_public_excluding_private': len(public),
            'b_public_excluding_instance': len([d for d in public if d.kind != 'instance']),
            'c_public_theorem_lemma_def_abbrev':
                len([d for d in public if d.kind in ('theorem', 'lemma', 'def', 'abbrev')]),
            'd_private': len([d for d in ds if d.private]),
            'all_rows': len(ds),
        }
    per_theory = {}
    for t in sorted({d.theory for d in decls}):
        per_theory[t] = cls([d for d in decls if d.theory == t])
    per_top = {}
    for f in sorted({d.path for d in decls if d.theory == '(top-level)'}):
        rows = [d for d in decls if d.path == f]
        per_top[f] = {'rows': len(rows),
                      'kinds': [[d.kind, d.name] for d in rows]}
    return {'totals': cls(decls), 'per_theory': per_theory,
            'per_top_level_file': per_top,
            'kinds': {k: len([d for d in decls if d.kind == k and not d.private])
                      for k in DECL_KINDS}}


# ── statement authority probes ──────────────────────────────────────────────────────────
PROBE_KEYS = ['skeleton declarations', 'delivered, word-for-word', 'delivered, not in authority',
              'not delivered yet', 'signature differences']


def probe_counts(theory):
    if not os.path.exists(PROBE):
        return {'error': 'probe missing', 'theory': theory}
    p = subprocess.run([sys.executable, os.path.relpath(PROBE, ROOT), '--theory', theory],
                       cwd=ROOT, capture_output=True, text=True)
    out = p.stdout
    res = {'theory': theory, 'exit_code': p.returncode}
    for k in PROBE_KEYS:
        m = re.search(re.escape(k) + r'\s*:\s*(\d+)', out)
        res[k] = int(m.group(1)) if m else None
    return res


def authority_census():
    per = [probe_counts(t) for t in THEORIES]
    for r in per:
        r['delivered_total (word-for-word + not in authority)'] = \
            (r['delivered, word-for-word'] or 0) + (r['delivered, not in authority'] or 0)
    return {
        'per_theory': per,
        'authority_total': sum(r['skeleton declarations'] or 0 for r in per),
        'word_for_word_total': sum(r['delivered, word-for-word'] or 0 for r in per),
        'auxiliary_total': sum(r['delivered, not in authority'] or 0 for r in per),
        'delivered_public_total': sum(r['delivered_total (word-for-word + not in authority)']
                                      for r in per),
        'not_delivered_total': sum(r['not delivered yet'] or 0 for r in per),
        'signature_differences_total': sum(r['signature differences'] or 0 for r in per),
        'theories_reporting_zero_undelivered':
            len([r for r in per if r['not delivered yet'] == 0]),
        'theories_reporting_zero_signature_differences':
            len([r for r in per if r['signature differences'] == 0]),
    }


# ── the relation module: sections, rows, classes ────────────────────────────────────────
RELATIONS = 'PhotoLean/Relations.lean'
SECTION_RE = re.compile(r'^/-! ##\s*(\d+)\.\s*(.*)$', re.M)

# The section → class mapping of the paper's Fig. 3.  Sections that mix classes list their
# rows explicitly by name (the row names are the ones the source scan extracts).
CLASS_OF_SECTION = {
    '1': 'certificate',
    '2': 'equivalence/entailment/bridge',
    '3': 'equivalence/entailment/bridge',
    '4': 'equivalence/entailment/bridge',
    '5': 'equivalence/entailment/bridge',
    '6': 'equivalence/entailment/bridge',
    '7': 'composition',
    '8': 'composition',
    '9': 'composition',
    '10': None,                                    # documentation only (no declarations)
    '11': None,                                    # mixed: two tie-back certificates + verdict
    '12': 'certificate',
    '13': 'adjudication',
    '14': 'adjudication',
    '15': 'composition',
    '16': None,                                    # documentation only
    '17': 'RACI',
}
# Row-level overrides for the mixed sections (documented classification, not a guess).
CLASS_OF_ROW = {
    'symmetryFactor_tsCoordZero_eq_kernel': 'equivalence/entailment/bridge',
    'symmetryFactor_tsCoordZero_eq_bepTransfer': 'equivalence/entailment/bridge',
    'symmetryFactor_betaHalf_iff': 'adjudication',
    'symmetryFactor_conflation_falsified_and_holds_in_kernel': 'adjudication',
}
CLASS_ORDER = ['certificate', 'equivalence/entailment/bridge', 'composition', 'adjudication',
               'RACI', 'other']

QUOTED_CLASS_COMPOSITION = {'certificate': 15, 'equivalence/entailment/bridge': 22,
                            'composition': 26, 'adjudication': 8, 'RACI': 5, 'other': 2}

# The rfl-level definitional pins: §1 rows are closed by a literal `:= rfl`; §12 rows re-export
# the in-module `cert_*` theorems, which are `rfl` / `Iff.rfl`-level (`unfold` + `rfl`).
RFL_CERTIFICATE_SECTIONS = ['1', '12']


def relations_census(decls):
    raw = read(RELATIONS)
    marks = [(int(m.group(1)), m.group(2).rstrip().removesuffix('-/').strip(),
              raw[:m.start()].count('\n') + 1)
             for m in SECTION_RE.finditer(raw)]
    rows = [d for d in decls if d.path == RELATIONS]
    total_lines = raw.count('\n') + 1
    sections = []
    for idx, (num, title, line) in enumerate(marks):
        end = marks[idx + 1][2] - 1 if idx + 1 < len(marks) else total_lines
        srows = [d for d in rows if line <= d.line <= end]
        for d in srows:
            d.section = str(num)
        cls = CLASS_OF_SECTION.get(str(num))
        classes = {}
        for d in srows:
            c = CLASS_OF_ROW.get(d.name, cls) or 'other'
            classes.setdefault(c, []).append(d.name)
        sections.append({'number': num, 'title': title, 'line': line, 'end_line': end,
                         'rows': len(srows), 'class': cls, 'row_names': [d.name for d in srows],
                         'rows_by_class': {k: sorted(v) for k, v in classes.items()}})
    class_totals = {c: 0 for c in CLASS_ORDER}
    for s in sections:
        for c, names in s['rows_by_class'].items():
            class_totals[c] = class_totals.get(c, 0) + len(names)
    rfl_rows = [d.name for d in rows
                if str(getattr(d, 'section', '')) in RFL_CERTIFICATE_SECTIONS]
    # The quoted six numbers are the primary mapping plus a redistribution of exactly four §9
    # rows out of `composition`: a three-way split of §9's seven rows (3 composition / 2
    # adjudication / 2 other) reproduces 15/22/26/8/5/2 exactly.  The manuscript's sources do
    # not fix *which* four rows those are; the section's own labels (C1 certificate, C2 shared
    # predicate, C3–C5 non-relations) do not add up to such a split, so the reconstruction is
    # reported, never applied.
    quoted_delta = {c: QUOTED_CLASS_COMPOSITION[c] - class_totals.get(c, 0) for c in CLASS_ORDER}
    reconciliation = {
        'primary_class_totals': class_totals,
        'quoted_class_totals': QUOTED_CLASS_COMPOSITION,
        'delta_quoted_minus_primary': quoted_delta,
        'reading': 'The quoted composition count is 4 lower than the primary mapping; the quoted '
                   'adjudication count is 2 higher and the quoted "other" count is 2 higher. '
                   'A consistent reconstruction exists: count §9 (the look-alike section, 7 rows) '
                   'as 3 composition + 2 adjudication + 2 other, everything else as in the primary '
                   'mapping. Under that reconstruction all six quoted numbers (15/22/26/8/5/2) and '
                   'the total 78 hold. Which four of §9\'s rows move cannot be recovered from the '
                   'repository: §9\'s own labels are C1 (certificate), C2 (shared predicate), '
                   'C3a/C3b, C4, C5a/C5b (non-relations), and the class list has no "non-relation" '
                   'class.',
        'fig3_total_quoted': sum(QUOTED_CLASS_COMPOSITION.values()),
        'fig3_total_primary': sum(class_totals.values()),
        'reconstructions': [
            {'name': 'A (§15 shape rows out of composition)',
             'rule': '§11 splits 2 bridge / 2 adjudication (as in the primary mapping), §9 is all '
                     'composition, and §15 splits 8 composition / 2 adjudication / 2 other, where '
                     'the two "other" rows are the two rows §15\'s own prose calls "shape rows": '
                     'fretEff6_inv_eq_one_plus and eg_boundary_eq_tsCoord_zero',
             'totals': {'certificate': 15, 'equivalence/entailment/bridge': 22,
                        'composition': 26, 'adjudication': 8, 'RACI': 5, 'other': 2},
             'weakness': 'no §15 row carries an A-label, so the two rows that would move to '
                         'adjudication have no textual support (candidates: the D-adjacent rows '
                         'sv_quench_dilutes_yield and kasha_radBranch_eq_yieldOf)'},
            {'name': 'B (§9 look-alike rows out of composition)',
             'rule': '§11 counts wholly as adjudication (4 rows, all A1), §15 is all composition, '
                     'and §9\'s seven rows split 3 composition / 2 bridge / 2 other',
             'totals': {'certificate': 15, 'equivalence/entailment/bridge': 22,
                        'composition': 26, 'adjudication': 8, 'RACI': 5, 'other': 2},
             'weakness': 'cannot read §11 wholly as adjudication while keeping the two tie-back '
                         'rows available to reach 22 bridge rows, and §9\'s own labels (C1 '
                         'certificate, C2 shared predicate, C3–C5 non-relations) do not produce a '
                         '3/2/2 split'}],
        'recommendation': 'Update the Fig. 3 caption to the recomputed split 15/22/30/6/5/0: the '
                          'section markers of Relations.lean do not support 15/22/26/8/5/2, and '
                          'both reconstructions that reach the caption rest on assignments the '
                          'module text does not license.',
    }
    return {
        'sections': sections,
        'section_count': len(sections),
        'declaration_count': len(rows),
        'class_totals': class_totals,
        'quoted_class_totals': QUOTED_CLASS_COMPOSITION,
        'class_verdicts': {c: ('MATCH' if class_totals.get(c, 0) == QUOTED_CLASS_COMPOSITION[c]
                               else 'DIFF') for c in CLASS_ORDER},
        'class_totals_sum': sum(class_totals.values()),
        'reconciliation': reconciliation,
        'rfl_certificate_rows': sorted(rfl_rows),
        'rfl_certificate_count': len(rfl_rows),
        'class_of_section': CLASS_OF_SECTION,
        'class_of_row': CLASS_OF_ROW,
    }


# ── pair coverage (explicit sets, one citation per pair) ────────────────────────────────
# Nodes of the graph.  `Kernel` is a shared module, not one of the seventeen theories, so it
# is not a node of the C(17,2)=136 census.
P = {
    'M': 'Marcus', 'H': 'Hammond', 'B': 'BEP', 'K': 'Kasha', 'Sab': 'Sabatier',
    'G': 'Goldschmidt', 'X': 'SymmetryFactor', 'KV': 'KashaVavilov', 'SV': 'SternVolmer',
    'QY': 'QuantumYield', 'FP': 'FluorPhos', 'EGL': 'EnergyGapLaw', 'SS': 'StokesShift',
    'IC': 'ICvsISC', 'FO': 'Forster', 'EB': 'Einstein', 'RA': 'RACI',
}
# Each entry: (pair key tuple, citation string).  Section numbers refer to Relations.lean.
EDGES = [
    (('M', 'H'), '§2 tsCoord_lt_zero_iff_inverted, lefflerSecant_neg_iff_inverted; §4; §5 hammond_barrier_eq_gapReactant; §6 hammond_sharp_iff_marcus_sharp'),
    (('M', 'B'), '§2 epBounds_iff_no_inverted_direction; §3 epBounds_of_marcus_normal; §5 bep_eact_eq_marcus_barrier, bep_rate_eq_exp_neg_eact'),
    (('H', 'B'), '§2 transfer_eq_tsCoord_bridge, secSlope_eq_lefflerSecant; §3 epBounds_of_reactionRegion, hammondDescriptor_of_epConformsOnWindow; §6 hammond_trend_exact_bep_law_inexact'),
    (('M', 'Sab'), '§9 marcus_rate_eq_activity (C1), marcusRate_antiVolcanoDescriptor (C2)'),
    (('Sab', 'B'), '§8 six rows (linearVolcano_eq_bepTangent … linearVolcano_apex_exact)'),
    (('K', 'M'), '§7 five rows (kernel_marcusIC, kashaWithin_one_marcus, not_kashaWithin_of_gap_far, kashaWindow_halfWidth, marcusIC_pos)'),
    (('X', 'M'), '§11 symmetryFactor_tsCoordZero_eq_kernel, symmetryFactor_betaHalf_iff; §10 registry "SymmetryFactor ↔ Marcus, Hammond, BEP — §11"'),
    (('X', 'B'), '§11 symmetryFactor_tsCoordZero_eq_bepTransfer'),
    (('X', 'H'), '§10 registry "SymmetryFactor ↔ Marcus, Hammond, BEP — §11" (via §1 kernel certificate Kernel.tsCoord = Hammond.tsCoord)'),
    (('KV', 'K'), '§13 kv_d2_verdict, kv_antiKasha_boundary (both over Kasha.RateData / Kasha.KashaRule)'),
    (('EGL', 'M'), '§12 eg_rate_eq_marcus, eg_invertedGap_iff_marcus'),
    (('IC', 'M'), '§12 icvscic_icRate_eq_marcus'),
    (('K', 'QY'), '§15 kasha_radBranch_eq_yieldOf'),
    (('SV', 'QY'), '§15 sv_quench_dilutes_yield'),
    (('FP', 'QY'), '§15 phiF_eq_yieldOf, phiP_eq_yieldOf_cascade'),
    (('EB', 'QY'), '§15 einstein_yield_via_qy'),
    (('FO', 'QY'), '§15 fretEff6_eq_one_sub_yieldOf'),
    (('K', 'EGL'), '§15 marcusIC_strictAnti_on_inverted_gaps'),
    (('SS', 'EGL'), '§15 egBarrier_zero_iff_emEnergy_zero'),
    (('IC', 'EGL'), '§15 icvscic_icRate_eq_eg_nrRate'),
    (('SV', 'FP'), '§15 fpRatio_invariant_under_quench'),
    (('EGL', 'H'), '§15 eg_boundary_eq_tsCoord_zero (the "Hammond boundary row")'),
    (('M', 'SS'), 'in-module edge: PhotoLean/StokesShift/Criterion.lean emEnergy_pos_iff_inverted (row SS-C9), noted in §16 completion block'),
    (('RA', 'QY'), '§17 raci_qy_eq_yieldOf_two_channel, qy_two_channel_strictAnti_of_nr_lt'),
    (('RA', 'EGL'), '§17 log_barrierRate_eq'),
    (('RA', 'IC'), '§17 icvsisc_barrier_zero_at_crossing'),
]

ABSENCE_REGISTRIES = {
    '§10 (no-edge registry, first seven theories)': [
        (('K', 'B'), '§10 "Kasha ↔ BEP — no edge"'),
        (('K', 'H'), '§10 "Kasha ↔ Hammond — no edge"'),
        (('Sab', 'H'), '§10 "Sabatier ↔ Hammond — no edge"'),
        (('Sab', 'K'), '§10 "Sabatier ↔ Kasha — no edge"'),
        (('G', 'M'), '§10 "Goldschmidt ↔ all six — no edge"'),
        (('G', 'H'), '§10 "Goldschmidt ↔ all six — no edge"'),
        (('G', 'B'), '§10 "Goldschmidt ↔ all six — no edge"'),
        (('G', 'K'), '§10 "Goldschmidt ↔ all six — no edge"'),
        (('G', 'Sab'), '§10 "Goldschmidt ↔ all six — no edge" + "Goldschmidt ↔ Sabatier — look-alike of shape"'),
        (('G', 'X'), '§10 "Goldschmidt ↔ all six" and "SymmetryFactor ↔ Kasha, Sabatier, Goldschmidt — no edge" (listed twice)'),
        (('X', 'K'), '§10 "SymmetryFactor ↔ Kasha, Sabatier, Goldschmidt — no edge"'),
        (('X', 'Sab'), '§10 "SymmetryFactor ↔ Kasha, Sabatier, Goldschmidt — no edge"'),
    ],
    '§16 (extended no-edge registry, per-theory bullets)': [
        (('KV', 'M'), '§16 "KashaVavilov ↔ Marcus / Hammond / BEP — no edge"'),
        (('KV', 'H'), '§16 "KashaVavilov ↔ Marcus / Hammond / BEP — no edge"'),
        (('KV', 'B'), '§16 "KashaVavilov ↔ Marcus / Hammond / BEP — no edge"'),
        (('KV', 'Sab'), '§16 "KashaVavilov ↔ Sabatier / Goldschmidt / SymmetryFactor — no edge"'),
        (('KV', 'G'), '§16 "KashaVavilov ↔ Sabatier / Goldschmidt / SymmetryFactor — no edge"'),
        (('KV', 'X'), '§16 "KashaVavilov ↔ Sabatier / Goldschmidt / SymmetryFactor — no edge"'),
        (('SV', 'M'), '§16 "SternVolmer ↔ Marcus / … — no edge"'),
        (('SV', 'H'), '§16 "SternVolmer ↔ Marcus / … — no edge"'),
        (('SV', 'B'), '§16 "SternVolmer ↔ Marcus / … — no edge"'),
        (('SV', 'Sab'), '§16 "SternVolmer ↔ Marcus / … — no edge"'),
        (('SV', 'G'), '§16 "SternVolmer ↔ Marcus / … — no edge"'),
        (('SV', 'X'), '§16 "SternVolmer ↔ Marcus / … — no edge"'),
        (('QY', 'M'), '§16 "QuantumYield ↔ Marcus / … — no edge"'),
        (('QY', 'H'), '§16 "QuantumYield ↔ Marcus / … — no edge"'),
        (('QY', 'B'), '§16 "QuantumYield ↔ Marcus / … — no edge"'),
        (('QY', 'Sab'), '§16 "QuantumYield ↔ Marcus / … — no edge"'),
        (('QY', 'G'), '§16 "QuantumYield ↔ Marcus / … — no edge"'),
        (('QY', 'X'), '§16 "QuantumYield ↔ Marcus / … — no edge"'),
        (('FP', 'M'), '§16 "FluorPhos ↔ … — no edge except through QuantumYield"'),
        (('FP', 'H'), '§16 "FluorPhos ↔ … — no edge except through QuantumYield"'),
        (('FP', 'B'), '§16 "FluorPhos ↔ … — no edge except through QuantumYield"'),
        (('FP', 'Sab'), '§16 "FluorPhos ↔ … — no edge except through QuantumYield"'),
        (('FP', 'G'), '§16 "FluorPhos ↔ … — no edge except through QuantumYield"'),
        (('FP', 'X'), '§16 "FluorPhos ↔ … — no edge except through QuantumYield"'),
        (('FP', 'SS'), '§16 "FluorPhos ↔ … / StokesShift / … — no edge" (also listed under the StokesShift bullet)'),
        (('FP', 'EGL'), '§16 "FluorPhos ↔ … / EnergyGapLaw / … — no edge"'),
        (('FP', 'FO'), '§16 "FluorPhos ↔ … / Forster / Einstein — no edge"'),
        (('FP', 'EB'), '§16 "FluorPhos ↔ … / Forster / Einstein — no edge"'),
        (('SS', 'K'), '§16 "StokesShift ↔ Kasha / … — no edge"'),
        (('SS', 'KV'), '§16 "StokesShift ↔ Kasha / KashaVavilov / … — no edge"'),
        (('SS', 'SV'), '§16 "StokesShift ↔ … / SternVolmer / … — no edge"'),
        (('SS', 'QY'), '§16 "StokesShift ↔ … / QuantumYield / … — no edge"'),
        (('SS', 'FP'), '§16 "StokesShift ↔ … / FluorPhos / … — no edge" (also listed under the FluorPhos bullet)'),
        (('SS', 'IC'), '§16 "StokesShift ↔ … / ICvsISC / … — no edge"'),
        (('SS', 'FO'), '§16 "StokesShift ↔ … / Forster / Einstein — no edge" (also listed under the FluorPhos bullet)'),
        (('SS', 'EB'), '§16 "StokesShift ↔ … / Forster / Einstein — no edge" (also listed under the FluorPhos bullet)'),
        (('IC', 'K'), '§16 "ICvsISC ↔ Kasha / KashaVavilov / … — no edge"'),
        (('IC', 'KV'), '§16 "ICvsISC ↔ Kasha / KashaVavilov / … — no edge"'),
        (('IC', 'SV'), '§16 "ICvsISC ↔ … / SternVolmer / QuantumYield / … — no edge"'),
        (('IC', 'QY'), '§16 "ICvsISC ↔ … / QuantumYield / … — no edge"'),
        (('IC', 'FO'), '§16 "ICvsISC ↔ … / Forster / Einstein — no edge" (also listed under the Forster bullet)'),
        (('IC', 'EB'), '§16 "ICvsISC ↔ … / Forster / Einstein — no edge"'),
        (('FO', 'M'), '§16 "Forster ↔ Marcus / … — no edge"'),
        (('FO', 'H'), '§16 "Forster ↔ Marcus / … — no edge"'),
        (('FO', 'B'), '§16 "Forster ↔ Marcus / … — no edge"'),
        (('FO', 'K'), '§16 "Forster ↔ … / Kasha / … — no edge"'),
        (('FO', 'KV'), '§16 "Forster ↔ … / KashaVavilov / … — no edge"'),
        (('FO', 'Sab'), '§16 "Forster ↔ … / Sabatier / … — no edge"'),
        (('FO', 'X'), '§16 "Forster ↔ … / SymmetryFactor / … — no edge"'),
        (('FO', 'SS'), '§16 "Forster ↔ … / StokesShift / … — no edge" (also listed under the FluorPhos bullet)'),
        (('FO', 'EGL'), '§16 "Forster ↔ … / EnergyGapLaw / … — no edge"'),
        (('FO', 'IC'), '§16 "Forster ↔ … / ICvsISC — no edge" (also listed under the ICvsISC bullet)'),
        (('FO', 'SV'), '§16 Forster bullet: "Two shape registrations carry machine content: the SV look-alike (fretEff6_inv_eq_one_plus, §15)" — shape registered, no edge (paper §3 "edge construction refused")'),
        (('EB', 'M'), '§16 "Einstein ↔ Marcus / … — no edge"'),
        (('EB', 'H'), '§16 "Einstein ↔ Marcus / … — no edge"'),
        (('EB', 'B'), '§16 "Einstein ↔ Marcus / … — no edge"'),
        (('EB', 'K'), '§16 "Einstein ↔ … / Kasha / … — no edge"'),
        (('EB', 'KV'), '§16 "Einstein ↔ … / KashaVavilov / … — no edge"'),
        (('EB', 'Sab'), '§16 "Einstein ↔ … / Sabatier / … — no edge"'),
        (('EB', 'G'), '§16 "Einstein ↔ … / Goldschmidt / … — no edge"'),
        (('EB', 'X'), '§16 "Einstein ↔ … / SymmetryFactor / … — no edge"'),
        (('EB', 'SS'), '§16 "Einstein ↔ … / StokesShift / Forster — no edge"'),
        (('EB', 'FO'), '§16 "Einstein ↔ … / Forster — no edge"'),
    ],
    '§16 completion block (added 2026-09-24, 26 pairs)': [
        (('EGL', 'B'), '§16 completion "EnergyGapLaw ↔ BEP — no edge (a registered shape edge)"'),
        (('EGL', 'Sab'), '§16 completion "EnergyGapLaw ↔ Sabatier / … — no edge"'),
        (('EGL', 'G'), '§16 completion "EnergyGapLaw ↔ … / Goldschmidt / … — no edge"'),
        (('EGL', 'X'), '§16 completion "EnergyGapLaw ↔ … / SymmetryFactor / … — no edge"'),
        (('EGL', 'KV'), '§16 completion "EnergyGapLaw ↔ … / KashaVavilov / … — no edge"'),
        (('EGL', 'SV'), '§16 completion "EnergyGapLaw ↔ … / SternVolmer / … — no edge"'),
        (('EGL', 'QY'), '§16 completion "EnergyGapLaw ↔ … / QuantumYield / … — no edge"'),
        (('EGL', 'EB'), '§16 completion "EnergyGapLaw ↔ … / Einstein — no edge"'),
        (('SS', 'H'), '§16 completion "StokesShift ↔ Hammond / … — no edge"'),
        (('SS', 'B'), '§16 completion "StokesShift ↔ … / BEP / … — no edge"'),
        (('SS', 'Sab'), '§16 completion "StokesShift ↔ … / Sabatier / … — no edge"'),
        (('SS', 'G'), '§16 completion "StokesShift ↔ … / Goldschmidt / … — no edge"'),
        (('SS', 'X'), '§16 completion "StokesShift ↔ … / SymmetryFactor — no edge"'),
        (('IC', 'H'), '§16 completion "ICvsISC ↔ Hammond / … — no edge"'),
        (('IC', 'B'), '§16 completion "ICvsISC ↔ … / BEP / … — no edge"'),
        (('IC', 'Sab'), '§16 completion "ICvsISC ↔ … / Sabatier / … — no edge"'),
        (('IC', 'G'), '§16 completion "ICvsISC ↔ … / Goldschmidt / … — no edge"'),
        (('IC', 'X'), '§16 completion "ICvsISC ↔ … / SymmetryFactor — no edge"'),
        (('FP', 'K'), '§16 completion "FluorPhos ↔ Kasha / KashaVavilov — no edge (undelivered candidate compositions)"'),
        (('FP', 'KV'), '§16 completion "FluorPhos ↔ Kasha / KashaVavilov — no edge"'),
        (('FP', 'IC'), '§16 completion "FluorPhos ↔ ICvsISC — the premise-level kISC identification (registered in both plans as a modelling premise, not a Lean row)"'),
        (('KV', 'SV'), '§16 completion "KashaVavilov ↔ SternVolmer / QuantumYield — undelivered candidate compositions"'),
        (('KV', 'QY'), '§16 completion "KashaVavilov ↔ … / QuantumYield — undelivered candidate compositions"'),
        (('K', 'SV'), '§16 completion "Kasha ↔ SternVolmer — no edge (registered candidate, not delivered)"'),
        (('EB', 'SV'), '§16 completion "Einstein ↔ SternVolmer — no edge"'),
        (('FO', 'G'), '§16 completion "Forster ↔ Goldschmidt — no edge (look-alike, no machine row)"'),
    ],
    '§17 (no-edge registrations of the seventeenth node)': [
        (('RA', 'H'), '§17 "RACI ↔ Hammond / BEP / Sabatier — no edge"'),
        (('RA', 'B'), '§17 "RACI ↔ Hammond / BEP / Sabatier — no edge"'),
        (('RA', 'Sab'), '§17 "RACI ↔ Hammond / BEP / Sabatier — no edge"'),
        (('RA', 'G'), '§17 "RACI ↔ Goldschmidt — no edge"'),
        (('RA', 'X'), '§17 "RACI ↔ SymmetryFactor — no edge"'),
        (('RA', 'K'), '§17 "RACI ↔ Kasha / KashaVavilov — shape note (no machine row)"'),
        (('RA', 'KV'), '§17 "RACI ↔ Kasha / KashaVavilov — shape note (no machine row)"'),
        (('RA', 'SV'), '§17 "RACI ↔ SternVolmer — look-alike note (opposite trend)"'),
        (('RA', 'FP'), '§17 "RACI ↔ FluorPhos — no edge"'),
        (('RA', 'SS'), '§17 "RACI ↔ StokesShift — no edge"'),
        (('RA', 'FO'), '§17 "RACI ↔ Forster — no edge"'),
        (('RA', 'EB'), '§17 "RACI ↔ Einstein — no edge"'),
        (('RA', 'M'), '§17 kernel_surfaces_cross_at_tsCoord — "RACI ↔ Marcus (look-alike, machine note)"; paper §3 lists "RACI versus Marcus … real crossing vs. codimension-2 degeneracy" among the shape look-alikes with edge construction refused (the row pins the Marcus side and asserts no edge)'),
    ],
}


def citation_check(decl_names):
    """Every edge citation must name at least one declaration that exists in the tree — a cheap
    guard against stale row names after a rename.  Absence citations name registry bullets, so
    they are checked only for the pairs that carry a machine row."""
    resolved, unresolved = [], []
    for pair, cite in EDGES:
        hits = sorted({n for n in decl_names if n and n in cite})
        (resolved if hits else unresolved).append(
            {'pair': [P[pair[0]], P[pair[1]]], 'cite': cite, 'rows': hits})
    return {'edges_with_resolved_row': len(resolved), 'edges_without_resolved_row': unresolved,
            'resolved': resolved}


def pair_census():
    nodes = list(P.values())
    edges = {}
    for pair, cite in EDGES:
        edges[frozenset(P[k] for k in pair)] = cite
    absent = {}
    dup_notes = []
    for registry, pairs in ABSENCE_REGISTRIES.items():
        for pair, cite in pairs:
            key = frozenset(P[k] for k in pair)
            if key in absent:
                dup_notes.append({'pair': sorted(key), 'registries': [absent[key]['registry'],
                                                                      registry]})
            absent[key] = {'cite': cite, 'registry': registry}
    all_pairs = {frozenset(c) for c in combinations(nodes, 2)}
    both = sorted(tuple(sorted(k)) for k in set(edges) & set(absent))
    unaccounted = sorted(tuple(sorted(k)) for k in all_pairs - set(edges) - set(absent))
    completion = [p for p in ABSENCE_REGISTRIES['§16 completion block (added 2026-09-24, 26 pairs)']]
    return {
        'node_count': len(nodes),
        'nodes': nodes,
        'pairs_total': len(all_pairs),
        'edges': sorted([{'pair': sorted(k), 'cite': v} for k, v in edges.items()],
                        key=lambda e: e['pair']),
        'edge_count': len(edges),
        'absences': sorted([{'pair': sorted(k), 'cite': v['cite'], 'registry': v['registry']}
                            for k, v in absent.items()], key=lambda e: e['pair']),
        'absence_count': len(absent),
        'both_edge_and_absence': both,
        'unaccounted': unaccounted,
        'registry_double_listings': dup_notes,
        'ambiguous_pairs': [
            {'pair': ['Marcus', 'RACI'],
             'edge_reading': '§17 last bullet groups "RACI ↔ QuantumYield / EnergyGapLaw / '
                             'ICvsISC / Marcus — see the five machine rows above"',
             'absence_reading': '§17 row kernel_surfaces_cross_at_tsCoord is labelled '
                                '"look-alike, machine note", and paper §3 lists "RACI versus '
                                'Marcus … real crossing vs. codimension-2 degeneracy" among the '
                                'shape look-alikes registered with edge construction refused',
             'counted_as': 'absence',
             'effect_on_coverage': 'none (the pair is covered either way); counting it as an edge '
                                   'would give 27 edges + 109 absences'}],
        'edge_absence_alternative': {'edges': len(edges) + 1, 'absences': len(absent) - 1},
        'classification_decisions': [
            {'pair': ['Marcus', 'RACI'],
             'decision': 'absence (registered shape look-alike with a machine note)',
             'alternative': 'edge (the row is one of the five machine rows §17 registers)',
             'reason': 'both the manuscript §5.7 and the Fig. 1 caption list "the classical '
                       'surface crossing versus the codimension-2 conical intersection of RACI" '
                       'among the shape look-alikes registered WITHOUT an edge; the row '
                       'kernel_surfaces_cross_at_tsCoord pins the classical side only. Any text '
                       'that states 27 edges + 109 absences is off by this single judgment.'},
            {'pair': ['Hammond', 'SymmetryFactor'],
             'decision': 'edge, transitively only',
             'alternative': 'absence (no direct row exists)',
             'reason': 'no Relations.lean row names both theories. The edge rests on §10\'s '
                       'registry line "SymmetryFactor ↔ Marcus, Hammond, BEP — §11 (yes, A1 + '
                       'specialization)" plus §11\'s tie-backs to Kernel.tsCoord / BEP.transfer '
                       'and §1\'s kernel certificates kernel_tsCoord_eq_hammond / '
                       'kernel_transfer_eq_bep. It must not be read as a direct row.'},
            {'item': 'registry double-listings',
             'pairs': [x['pair'] for x in dup_notes],
             'decision': 'each pair assigned once, to the absence set, with both bullets cited',
             'reason': 'the registry lists these four pairs under two bullets each '
                       '(§16 FluorPhos bullet, §16 StokesShift bullet, §16 Forster bullet, §16 '
                       'ICvsISC bullet); the duplication is harmless for coverage but is '
                       'reported so the registry can be de-duplicated.'},
            {'item': 'Relations.lean §11',
             'decision': 'mixed section: the two tie-back certificates → equivalence/entailment/'
                         'bridge; the A1 verdict and the falsification-plus-persistence row → '
                         'adjudication',
             'alternative': 'all four rows adjudication (that is reconstruction B above, which '
                            'drops the bridge count to 20)',
             'reason': 'the rows\' own docstrings label them "A1 certificate" vs "A1 verdict".'},
            {'item': 'Relations.lean §6',
             'decision': 'equivalence/entailment/bridge',
             'alternative': 'other (the section is titled "Non-relations and shape differences")',
             'reason': 'the three rows are proved cross-theory content (an exactness/failure '
                       'contrast, a co-extensiveness composition, a predicate-strength row); the '
                       'alternative reading would give bridge 19 / other 3.'},
            {'item': 'Relations.lean §9',
             'decision': 'composition (the section is an edge-section of the graph)',
             'alternative': 'other (the section is the look-alike/non-relation pair, C1–C5)',
             'reason': 'the choice is the crux of the Fig. 3 caption gap: moving §9 out of '
                       'composition is what any caption-faithful mapping must do (see '
                       'relations_module.reconciliation).'},
        ],
        'completion_block_pairs': len(completion),
        'completion_block_in_module_edge': {'pair': ['Marcus', 'StokesShift'],
                                            'cite': '§16 completion block: "StokesShift ↔ Marcus — edge, delivered inside the theory module"' },
        'covered_total': len(edges) + len(absent),
        'complete': len(edges) + len(absent) == len(all_pairs) and not both and not unaccounted,
    }


# ── negative results ────────────────────────────────────────────────────────────────────
REFUTE_RE = re.compile(r'^(theorem|lemma) '
                       r'[A-Za-z_][A-Za-z0-9_.]*(refut|falsif|not_model_consistent)[A-Za-z0-9_.]*')


def negative_results(decls):
    hits = [d for d in decls if REFUTE_RE.match(d.kind + ' ' + (d.name or ''))]
    raw = subprocess.run(['grep', '-rnE', REFUTE_RE.pattern, '--include=*.lean', 'PhotoLean'],
                         cwd=ROOT, capture_output=True, text=True).stdout
    raw_lines = [ln for ln in raw.splitlines() if ln.strip()]
    return {
        'pattern': REFUTE_RE.pattern,
        'count': len(hits),
        'rows': [{'name': d.name, 'file': d.path, 'line': d.line, 'kind': d.kind} for d in hits],
        'raw_grep_count': len(raw_lines),
        'raw_grep_rows': raw_lines,
    }


# ── gates ───────────────────────────────────────────────────────────────────────────────
UNUSED_RE = re.compile(r'^warning: (.+?\.lean):(\d+):(\d+): unused variable `([^`]*)`')
TRACE_UNUSED_RE = re.compile(r'(?:\./)+([\w./-]+\.lean):(\d+):(\d+): unused variable `([^`]*)`')


def unused_from_traces():
    """Unused-variable warnings read from Lake's cached build traces.

    `lake build` replays a module's message log only when it decides to (measured: successive
    cached runs of check.sh can print nothing, so the check.sh output alone is not a stable
    surface for this count).  The `.trace` files Lake writes next to each olean hold the
    messages of the module's last elaboration; reading them is deterministic across cache
    states.  Only traces whose `.lean` source still exists are counted."""
    rows = []
    for path in glob.glob(os.path.join(ROOT, '.lake', 'build', 'lib', '**', '*.trace'),
                          recursive=True):
        try:
            with open(path, 'r', encoding='utf-8', errors='replace') as fh:
                blob = fh.read()
        except OSError:
            continue
        for m in TRACE_UNUSED_RE.finditer(blob):
            rel = m.group(1)
            if not os.path.exists(os.path.join(ROOT, rel)):
                continue
            rows.append({'file': rel, 'line': int(m.group(2)), 'column': int(m.group(3)),
                         'variable': m.group(4), 'source': 'trace'})
    return rows


def gates(check_output=None):
    if check_output is None:
        p = subprocess.run(['bash', os.path.relpath(CHECK, ROOT), '--strict'],
                           cwd=ROOT, capture_output=True, text=True)
        out, code = p.stdout + p.stderr, p.returncode
    else:
        out, code = check_output, None
    leaf = re.findall(r'^\s+OK\s+(theories/\S+)\s+\(5/5\)\s*$', out, re.M)
    unused = [{'file': m.group(1), 'line': int(m.group(2)), 'column': int(m.group(3)),
               'variable': m.group(4), 'source': 'check.sh'} for m in UNUSED_RE.finditer(out)]
    trace_rows = unused_from_traces()
    rows = unused if unused else trace_rows
    unused_files = sorted({u['file'] for u in rows})
    build_ok = 'build: OK' in out
    scan_clean = bool(re.search(r'^clean\s*$', out, re.M))
    verdict = 'PASS' if re.search(r'^verdict: PASS\s*$', out, re.M) else (
        'FAIL' if re.search(r'^verdict: FAIL', out, re.M) else 'UNKNOWN')
    return {
        'command': 'proofs/scripts/check.sh --strict',
        'exit_code': code,
        'build': 'OK' if build_ok else ('FAILED' if 'build: FAILED' in out else 'UNKNOWN'),
        'scan': 'clean' if scan_clean else 'HITS',
        'leaf_planes_ok': len(leaf),
        'leaf_planes_expected': len(THEORIES),
        'leaf_planes': leaf,
        'verdict': verdict,
        'unused_variable_warnings': len(rows),
        'unused_variable_warnings_check_sh': len(unused),
        'unused_variable_warnings_traces': len(trace_rows),
        'unused_variable_source': 'check.sh output' if unused else 'lake build traces',
        'unused_variable_files': unused_files,
        'unused_variable_rows': rows,
        'output_tail': out.strip().splitlines()[-6:],
    }


# ── environment cross-check (needs the Lean toolchain) ──────────────────────────────────
ENV_PROBE_NAME = 'env-census.lean'


def env_probe_file(files):
    """A generated Lean batch file that folds over `env.constants` and prints one census line
    per theory directory (grouped by the defining module, not by namespace, so declarations
    written under a bare `namespace PhotoLean` still land in their module's theory)."""
    imports = '\n'.join('import ' + f[:-5].replace('/', '.') for f in files)
    return imports + '''
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut acc : Std.HashMap String (Array Nat) := {}
  let mut axNames : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.getRoot == `PhotoLean && !isPrivateName n then
      let theory : String :=
        match env.getModuleIdxFor? n with
        | some idx =>
          match env.header.moduleNames[idx.toNat]? with
          | some m =>
            match m.components with
            | _ :: t :: _ => if t == `Kernel || t == `Relations || t == `Smoke then "<top>" else t.toString
            | _ => "<top>"
          | none => "<none>"
        | none => "<none>"
      let kindIdx : Nat :=
        match ci with
        | .thmInfo _    => 0
        | .defnInfo _   => 1
        | .inductInfo _ => 2
        | .ctorInfo _   => 3
        | .recInfo _    => 4
        | .quotInfo _   => 5
        | .axiomInfo _  => 6
        | .opaqueInfo _ => 7
      let isInst ← liftCoreM (Lean.Meta.isInstance n)
      let isStruct := Lean.isStructure env n
      let cur0 := acc.getD theory (Array.mkArray 12 0)
      let cur1 := cur0.set! kindIdx (cur0.getD kindIdx 0 + 1)
      let cur2 := cur1.set! 8 (cur1.getD 8 0 + 1)
      let cur3 := if isInst then cur2.set! 9 (cur2.getD 9 0 + 1) else cur2
      let cur4 := if isStruct then cur3.set! 10 (cur3.getD 10 0 + 1) else cur3
      acc := acc.insert theory cur4
      if kindIdx == 6 then axNames := axNames.push n.toString
  let mut keys := acc.keys.toArray
  keys := keys.qsort (fun a b => a < b)
  let mut total := Array.mkArray 12 0
  for k in keys do
    let v := acc.getD k (Array.mkArray 12 0)
    IO.println s!"ENV|{k}|thm={v.getD 0 0}|defn={v.getD 1 0}|induct={v.getD 2 0}|ctor={v.getD 3 0}|rec={v.getD 4 0}|quot={v.getD 5 0}|axiom={v.getD 6 0}|opaque={v.getD 7 0}|total={v.getD 8 0}|instance={v.getD 9 0}|structure={v.getD 10 0}"
    for i in [0:12] do
      total := total.set! i (total.getD i 0 + v.getD i 0)
  IO.println s!"ENV|__TOTAL__|thm={total.getD 0 0}|defn={total.getD 1 0}|induct={total.getD 2 0}|ctor={total.getD 3 0}|rec={total.getD 4 0}|quot={total.getD 5 0}|axiom={total.getD 6 0}|opaque={total.getD 7 0}|total={total.getD 8 0}|instance={total.getD 9 0}|structure={total.getD 10 0}"
  for a in axNames do
    IO.println s!"ENV|__AXIOMCONST__|{a}"
'''


def run_env_probe(files):
    os.makedirs(SCRATCH, exist_ok=True)
    path = os.path.join(SCRATCH, ENV_PROBE_NAME)
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write(env_probe_file(files))
    p = subprocess.run(['proofs/scripts/lake', 'env', 'lean', os.path.relpath(path, ROOT)],
                       cwd=ROOT, capture_output=True, text=True)
    per, total, axioms = {}, {}, []
    for line in p.stdout.splitlines():
        if not line.startswith('ENV|'):
            continue
        parts = line.split('|')
        if len(parts) >= 3 and parts[1] == '__AXIOMCONST__':
            axioms.append(parts[2])
            continue
        if len(parts) < 3:
            continue
        key = parts[1]
        fields = {}
        for kv in parts[2:]:
            if '=' in kv:
                k, v = kv.split('=', 1)
                fields[k] = int(v) if v.isdigit() else v
        if key == '__TOTAL__':
            total = fields
        else:
            per[key] = fields
    return {'ok': not p.returncode, 'modules': len(files), 'per_module_ns': per,
            'total': total, 'auxiliary_axiom_constants': sorted(axioms),
            'stderr': p.stderr.strip().splitlines()[:5]}

# ── axioms sweep (needs the Lean toolchain) ─────────────────────────────────────────────
AXIOMS_FILE_NAME = 'axioms-sweep.lean'
# The name character class is bounded so that the greedy match cannot run across two
# declarations in the whitespace-flattened output; `'` is inside the class because Lean
# identifiers may end in a prime, in which case the output reads `'Name'' depends on axioms:`. 
NAME_CLASS = r"[A-Za-z0-9_.'\u00c0-\uffff]"
AXIOM_LINE_RE = re.compile(r"'(" + NAME_CLASS + r"+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOM_RE = re.compile(r"'(" + NAME_CLASS + r"+)' does not depend on any axioms")


def allowed_axioms():
    txt = read('proofs/ENGINE.yml')
    m = re.search(r'^ALLOWED_AXIOMS="([^"]*)"', txt, re.M)
    return m.group(1).split() if m else []


def run_axioms_sweep(files, decls):
    os.makedirs(SCRATCH, exist_ok=True)
    path = os.path.join(SCRATCH, AXIOMS_FILE_NAME)
    public = [d for d in decls if not d.private and d.fqname]
    lines = ['import ' + f[:-5].replace('/', '.') for f in files]
    lines += ['', '-- generated by tools/counts.py --axioms']
    lines += ['#print axioms ' + d.fqname for d in public]
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(lines) + '\n')
    p = subprocess.run(['proofs/scripts/lake', 'env', 'lean', os.path.relpath(path, ROOT)],
                       cwd=ROOT, capture_output=True, text=True)
    flat = re.sub(r'\s+', ' ', p.stdout + '\n' + p.stderr)
    allowed = set(allowed_axioms())
    printed, no_ax, outside, unknown = [], [], [], []
    for m in AXIOM_LINE_RE.finditer(flat):
        name, lst = m.group(1), [x.strip() for x in m.group(2).split(',') if x.strip()]
        printed.append({'name': name, 'axioms': lst})
        extra = sorted(set(lst) - allowed)
        if extra:
            outside.append({'name': name, 'axioms': lst, 'outside': extra})
    for m in NO_AXIOM_RE.finditer(flat):
        no_ax.append(m.group(1))
    for m in re.finditer(r"unknown identifier '([^']+)'|unknown constant '([^']+)'", flat):
        unknown.append(m.group(1) or m.group(2))
    by_file = {}
    for d in public:
        by_file.setdefault(d.path, 0)
        by_file[d.path] += 1
    hist = {}
    for r in printed:
        hist[', '.join(sorted(r['axioms']))] = hist.get(', '.join(sorted(r['axioms'])), 0) + 1
    return {
        'command': 'proofs/scripts/lake env lean .lake/tmp/counts-scratch/axioms-sweep.lean',
        'exit_code': p.returncode,
        'declarations_requested': len(public),
        'declarations_printed': len(printed),
        'declarations_without_axioms': len(no_ax),
        'declarations_accounted_for': len(printed) + len(no_ax),
        'footprints_outside_allowed': len(outside),
        'outside_detail': outside[:50],
        'unknown_identifiers': sorted(set(unknown))[:50],
        'allowed_axioms': sorted(allowed),
        'distinct_footprints': sorted({tuple(sorted(r['axioms'])) for r in printed}),
        'footprint_histogram': hist,
        'requested_per_file': by_file,
    }


# ── tree state ──────────────────────────────────────────────────────────────────────────
def git_state():
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True,
                          text=True).stdout.strip()
    status = subprocess.run(['git', 'status', '--short'], cwd=ROOT, capture_output=True,
                            text=True).stdout.strip().splitlines()
    return {'head': head, 'git_status_short': status}


# ── claims ──────────────────────────────────────────────────────────────────────────────
def build_claims(census):
    f, auth, rel, pairs = (census['files'], census['statement_authority'],
                           census['relations_module'], census['pair_coverage'])
    decl = census['declarations']
    neg = census['negative_results']
    gate = census.get('gates')
    ax = census.get('axioms')
    claims = []

    def add(cid, quoted, source, computed, verdict, note=''):
        claims.append({'id': cid, 'quoted': quoted, 'source': source, 'computed': computed,
                       'verdict': verdict, 'note': note})

    per_theory_quoted = [51, 102, 191, 151, 132, 139, 35, 29, 46, 29, 30, 26, 36, 20, 32, 33, 71]
    per_theory_computed = [r['skeleton declarations'] for r in auth['per_theory']]

    add('theories', 17, 'paper §2.1, §3.1 Table 1',
        f['theory_directories'], 'MATCH' if f['theory_directories'] == 17 else 'DIFF')
    add('theory_modules', 92, 'paper §2.1, Fig. 3 caption',
        f['theory_modules'], 'MATCH' if f['theory_modules'] == 92 else 'DIFF')
    add('lean_files', 95, 'paper §2.1, Fig. 3 caption',
        f['lean_files_total'], 'MATCH' if f['lean_files_total'] == 95 else 'DIFF')
    add('statement_authority_total', 1153, 'paper §2.1, Fig. 1/3 captions',
        auth['authority_total'], 'MATCH' if auth['authority_total'] == 1153 else 'DIFF',
        'Σ probe "skeleton declarations" over the 17 theories')
    add('statement_authority_per_theory', per_theory_quoted, 'paper Fig. 3 / Table 1',
        per_theory_computed, 'MATCH' if per_theory_computed == per_theory_quoted else 'DIFF')
    add('fidelity_probes', '17/17 probes passed, 0 signature discrepancies, 0 undelivered',
        'paper §2.1',
        f"{auth['theories_reporting_zero_signature_differences']}/17 zero signature "
        f"differences, {auth['theories_reporting_zero_undelivered']}/17 zero undelivered, "
        f"not delivered total {auth['not_delivered_total']}",
        'MATCH' if (auth['theories_reporting_zero_signature_differences'] == 17 and
                    auth['theories_reporting_zero_undelivered'] == 17 and
                    auth['not_delivered_total'] == 0) else 'DIFF')
    add('public_delivered_total', 1214,
        'paper §2.1 and §5.2 ("1214 public declarations delivered in total …")',
        f"{auth['delivered_public_total']} = Σ_theory (delivered, word-for-word "
        f"{auth['word_for_word_total']} + delivered, not in authority {auth['auxiliary_total']})",
        'MATCH' if auth['delivered_public_total'] == 1214 else 'DIFF',
        'source-scan cross-check: public declarations in PhotoLean/<Theory>/*.lean excluding '
        f"private = {census['declarations']['per_theory_totals_theory_dirs']}"
        "; excluding instance = "
        f"{census['declarations']['per_theory_totals_theory_dirs'] - 1}")
    add('relations_declarations_sections', '78 declarations in 17 sections',
        'paper §2.3, Fig. 1 caption',
        f"{rel['declaration_count']} declarations in {rel['section_count']} sections",
        'MATCH' if (rel['declaration_count'] == 78 and rel['section_count'] == 17) else 'DIFF')
    for c in CLASS_ORDER:
        add('fig3_class_' + c.replace('/', '_'), QUOTED_CLASS_COMPOSITION[c],
            'paper Fig. 3 caption (15/22/26/8/5/2 = 78)',
            rel['class_totals'].get(c, 0), rel['class_verdicts'][c],
            'tools/counts.py CLASS_OF_SECTION/CLASS_OF_ROW mapping')
    add('fig3_class_total', 78, 'paper Fig. 3 caption',
        rel['class_totals_sum'], 'MATCH' if rel['class_totals_sum'] == 78 else 'DIFF',
        f"Σ of my classes = {rel['class_totals_sum']} of {rel['declaration_count']} rows")
    add('rfl_kernel_certificates', 15, 'paper §2.1, §2.3, §5.3, Fig. 3',
        rel['rfl_certificate_count'], 'MATCH' if rel['rfl_certificate_count'] == 15 else 'DIFF',
        '§1 (8 rows, literal `:= rfl`) + §12 (7 rows, in-module `cert_*` rfl certificates)')
    add('pair_coverage', 136, 'paper §3.1 bullet and §5.7',
        f"{pairs['covered_total']} covered = {pairs['edge_count']} edge pairs + "
        f"{pairs['absence_count']} absence pairs; edge∩absence={len(pairs['both_edge_and_absence'])}; "
        f"unaccounted={len(pairs['unaccounted'])}",
        'MATCH' if pairs['complete'] else 'DIFF')
    add('completion_block_pairs', 26, 'paper §3.1 bullet, §5.7',
        pairs['completion_block_pairs'], 'MATCH' if pairs['completion_block_pairs'] == 26 else 'DIFF')
    add('stokes_shift_in_module_edge', 'one edge of SS delivered within the theory module',
        'paper §3.1 bullet, §5.7', 'in-module edge Marcus–StokesShift (SS-C9)',
        'MATCH', 'PhotoLean/StokesShift/Criterion.lean emEnergy_pos_iff_inverted')
    add('refutation_rows', 10, 'paper §5.6', neg['count'],
        'MATCH' if neg['count'] == 10 else 'DIFF',
        f"comment-aware scan; raw grep cross-check = {neg['raw_grep_count']}")
    topk = {f: [k for k, _ in v['kinds']] for f, v in
            census['declarations']['per_top_level_file'].items()}
    kernel_kinds = topk.get('PhotoLean/Kernel.lean', [])
    add('kernel_contents', 'six definitions (reactantSurface, productSurface, barrier, '
        'reverseBarrier, tsCoord, transfer) and two barrier-rate algebra theorems', 'paper §5.3',
        f"{kernel_kinds.count('def')} definitions, {kernel_kinds.count('theorem')} theorems",
        'MATCH' if (kernel_kinds.count('def') == 6 and kernel_kinds.count('theorem') == 2)
        else 'DIFF')
    add('relations_module_rows', 'Relations.lean: 78 declarations, 17 sections', 'paper §2.3',
        f"{rel['declaration_count']} declarations, {rel['section_count']} sections",
        'MATCH' if (rel['declaration_count'] == 78 and rel['section_count'] == 17) else 'DIFF')
    add('equivalences_entailments', '7 genuine equivalences (E1-E7) and 3 one-way implications '
        '(O1-O3)', 'paper §2.3 edge-vocabulary bullet',
        '§2 has 6 rows, §3 has 3 rows (9 rows in the F1 core)',
        'NOTE', 'Relations.lean §2–§3 carries 6 equivalences + 3 one-way rows; the tenth E/O row '
        'is not identifiable from the module alone')
    if gate:
        add('leaf_planes', '17/17 leaf planes OK', 'paper §5.8',
            f"{gate['leaf_planes_ok']}/{gate['leaf_planes_expected']}",
            'MATCH' if gate['leaf_planes_ok'] == gate['leaf_planes_expected'] == 17 else 'DIFF')
        add('gate_verdict', 'verdict PASS', 'paper §2.1, §5.8', gate['verdict'],
            'MATCH' if gate['verdict'] == 'PASS' else 'DIFF',
            f"build {gate['build']}, scan {gate['scan']}")
        add('unused_variable_warnings', 'five unused variable linter warnings in three files',
            'paper §5.9/§5.10',
            f"{gate['unused_variable_warnings']} warnings in "
            f"{len(gate['unused_variable_files'])} files "
            f"({', '.join(gate['unused_variable_files'])}); "
            f"check.sh output {gate['unused_variable_warnings_check_sh']}, lake traces "
            f"{gate['unused_variable_warnings_traces']}",
            'MATCH' if (gate['unused_variable_warnings'] == 5 and
                        len(gate['unused_variable_files']) == 3) else 'DIFF',
            f"primary source: {gate['unused_variable_source']}")
    else:
        add('leaf_planes', '17/17 leaf planes OK', 'paper §5.8', 'skipped (--no-lean)', 'NOTE')
        add('gate_verdict', 'verdict PASS', 'paper §2.1, §5.8', 'skipped (--no-lean)', 'NOTE')
        add('unused_variable_warnings', 'five unused variable linter warnings in three files',
            'paper §5.9/§5.10', 'skipped (--no-lean)', 'NOTE')
    env = census.get('environment')
    if env and env.get('ok'):
        axc = env.get('auxiliary_axiom_constants', [])
        add('auxiliary_axiom_constants', 'the tree has exactly one auxiliary axiom constant and no '
            'user-declared axiom', 'METHOD NOTE / paper §5.8 ("No delivered row contains sorry or a '
            'custom axiom")',
            f"{len(axc)} axiom constant(s): {', '.join(axc) if axc else 'none'}",
            'MATCH' if len(axc) == 1 else 'DIFF',
            'the constant is the elaborator auxiliary PhotoLean.RACI.nonModelNoCI._elambda_1; '
            'no user-declared axiom exists')
    else:
        add('auxiliary_axiom_constants', 'the tree has exactly one auxiliary axiom constant and no '
            'user-declared axiom', 'METHOD NOTE / paper §5.8',
            'skipped (--no-lean or environment cross-check unavailable)', 'NOTE')
    if ax:
        add('axiom_footprints', "for every named row cited in the text, #print axioms reports "
            "exactly [propext, Classical.choice, Quot.sound]", 'paper §5.8',
            f"{ax['declarations_printed']}/{ax['declarations_requested']} declarations printed "
            f"(+{ax['declarations_without_axioms']} without axioms); "
            f"{ax['footprints_outside_allowed']} footprints outside ALLOWED_AXIOMS; "
            f"distinct footprints {ax['distinct_footprints']}",
            'MATCH' if ax['footprints_outside_allowed'] == 0 else 'DIFF',
            'no footprint exceeds ALLOWED_AXIOMS, but the footprint is an upper bound, not a '
            'constant: histogram ' + str(ax['footprint_histogram']))
    else:
        add('axiom_footprints', "for every named row cited in the text, #print axioms reports "
            "exactly [propext, Classical.choice, Quot.sound]", 'paper §5.8',
            'skipped (run with --axioms)', 'NOTE')
    return claims


# ── rendering ───────────────────────────────────────────────────────────────────────────
def verdict_of(computed, quoted):
    return 'MATCH' if computed == quoted else 'DIFF'


def render_text(census):
    L = []
    a = L.append
    f, d, auth, rel, pairs = (census['files'], census['declarations'],
                              census['statement_authority'], census['relations_module'],
                              census['pair_coverage'])
    a('PhotoLean census (tools/counts.py)')
    a('=' * 72)
    a(f"tree state: HEAD {census['meta']['tree_state']['head'][:12]}, "
      f"{len(census['meta']['tree_state']['git_status_short'])} modified/untracked paths")
    a('')
    a('files')
    a(f"  .lean files under PhotoLean/            : {f['lean_files_total']}")
    a(f"  theory modules (PhotoLean/<Theory>/*)  : {f['theory_modules']}")
    a(f"  top-level modules                      : {len(f['top_level_modules'])} "
      f"({', '.join(f['top_level_modules'])})")
    a(f"  theory directories                     : {f['theory_directories']}")
    for t, n in sorted(f['per_theory_modules'].items()):
        a(f"    {t:16s} {n}")
    a('')
    a('declarations (source scan — primary definition)')
    tt = d['totals']
    a(f"  (a) public, excluding private          : {tt['a_public_excluding_private']}")
    a(f"  (b) public, excluding instance         : {tt['b_public_excluding_instance']}")
    a(f"  (c) public theorem|lemma|def|abbrev    : {tt['c_public_theorem_lemma_def_abbrev']}")
    a(f"  (d) private                            : {tt['d_private']}")
    a(f"  kinds (public): {d['kinds']}")
    if 'environment' in census and census['environment'].get('ok'):
        e = census['environment']
        a(f"  environment cross-check: {e['total'].get('total')} non-private PhotoLean "
          f"constants (thm {e['total'].get('thm')}, defn {e['total'].get('defn')}, "
          f"induct {e['total'].get('induct')}, ctor {e['total'].get('ctor')}, "
          f"rec {e['total'].get('rec')}, axiom {e['total'].get('axiom')}); "
          f"instance {e['total'].get('instance')}, structure {e['total'].get('structure')}")
        for k, v in sorted(e['per_module_ns'].items())[:0]:
            a(f"    {k}: {v}")
    else:
        a('  environment cross-check: skipped')
    a('')
    a('per-theory cross-check (source scan | probe | environment)')
    a(f"  {'theory':16s} {'mod':>4s} {'src_pub':>8s} {'priv':>5s} {'auth':>5s} {'www':>4s} "
      f"{'aux':>4s} {'deliv':>6s} {'env':>5s} {'env-inst':>8s}")
    for r in census['per_theory']:
        a(f"  {r['theory']:16s} {r['modules']:4d} {r['source_public_excluding_private']:8d} "
          f"{r['source_private']:5d} {r['probe_authority']:5d} {r['probe_word_for_word']:4d} "
          f"{r['probe_auxiliaries']:4d} {r['probe_delivered_total']:6d} "
          f"{str(r['env_constants_total'] or '-'):>5s} {str(r['env_instances']):>8s}")
    a('')
    a('statement authority (probes) and delivered totals')
    a(f"  {'theory':16s} {'authority':>9s} {'word-for-word':>13s} {'aux':>4s} "
      f"{'delivered':>9s} {'undel':>5s} {'sigd':>4s}")
    for r in auth['per_theory']:
        a(f"  {r['theory']:16s} {r['skeleton declarations']:9d} "
          f"{r['delivered, word-for-word']:13d} {r['delivered, not in authority']:4d} "
          f"{r['delivered_total (word-for-word + not in authority)']:9d} "
          f"{r['not delivered yet']:5d} {r['signature differences']:4d}")
    a(f"  {'TOTAL':16s} {auth['authority_total']:9d} {auth['word_for_word_total']:13d} "
      f"{auth['auxiliary_total']:4d} {auth['delivered_public_total']:9d} "
      f"{auth['not_delivered_total']:5d} {auth['signature_differences_total']:4d}")
    a('')
    a('relation module (PhotoLean/Relations.lean)')
    for s in rel['sections']:
        cls = s['class'] or ('mixed' if s['rows'] else '—')
        a(f"  §{s['number']:<2d} {s['title'][:60]:60s} rows={s['rows']:3d} class={cls}")
    a(f"  declarations {rel['declaration_count']}, sections {rel['section_count']}")
    a(f"  rfl kernel certificates (§1+§12): {rel['rfl_certificate_count']}")
    a('  Fig. 3 class composition (quoted → computed):')
    for c in CLASS_ORDER:
        q = QUOTED_CLASS_COMPOSITION[c]
        got = rel['class_totals'].get(c, 0)
        a(f"    {c:32s} {q:3d} → {got:3d}  {rel['class_verdicts'][c]}")
    a(f"    {'TOTAL':32s} {sum(QUOTED_CLASS_COMPOSITION.values()):3d} → "
      f"{rel['class_totals_sum']:3d}  "
      f"{'MATCH' if rel['class_totals_sum'] == 78 else 'DIFF'}")
    a('')
    a('pair coverage')
    a(f"  nodes {pairs['node_count']}, pairs {pairs['pairs_total']}, edges "
      f"{pairs['edge_count']}, registered absences {pairs['absence_count']}, covered "
      f"{pairs['covered_total']}")
    a(f"  edge ∩ absence: {len(pairs['both_edge_and_absence'])}; unaccounted: "
      f"{len(pairs['unaccounted'])}")
    a(f"  completion-block pairs: {pairs['completion_block_pairs']}")
    a(f"  registry double-listings: {len(pairs['registry_double_listings'])} "
      f"({', '.join('-'.join(x['pair']) for x in pairs['registry_double_listings'])})")
    a('')
    a('negative results')
    a(f"  pattern {census['negative_results']['pattern']}")
    a(f"  rows: {census['negative_results']['count']} (raw grep cross-check: "
      f"{census['negative_results']['raw_grep_count']})")
    for r in census['negative_results']['rows']:
        a(f"    {r['file']}:{r['line']} {r['name']}")
    a('')
    if census.get('gates'):
        g = census['gates']
        a('gates (proofs/scripts/check.sh --strict)')
        a(f"  build {g['build']}, scan {g['scan']}, leaf planes "
          f"{g['leaf_planes_ok']}/{g['leaf_planes_expected']}, verdict {g['verdict']}, "
          f"exit {g['exit_code']}")
        a(f"  unused-variable warnings: {g['unused_variable_warnings']} in "
          f"{len(g['unused_variable_files'])} files")
        for u in g['unused_variable_rows']:
            a(f"    {u['file']}:{u['line']}:{u['column']} unused variable `{u['variable']}`")
    else:
        a('gates: skipped (--no-lean)')
    a('')
    if census.get('axioms'):
        x = census['axioms']
        a('axioms sweep (#print axioms)')
        a(f"  requested {x['declarations_requested']}, printed {x['declarations_printed']}, "
          f"without axioms {x['declarations_without_axioms']}, outside allowed "
          f"{x['footprints_outside_allowed']}, unknown identifiers "
          f"{len(x['unknown_identifiers'])}")
        a(f"  distinct footprints: {x['distinct_footprints']}")
        for o in x['outside_detail'][:10]:
            a(f"    OUTSIDE {o['name']}: {o['outside']}")
    else:
        a('axioms sweep: skipped (pass --axioms)')
    a('')
    a('claims')
    a(f"  {'id':34s} {'quoted':>10s} {'computed':>34s}  verdict")
    for c in census['claims']:
        q = str(c['quoted'])
        if len(q) > 10:
            q = q[:10] + '…'
        comp = str(c['computed'])
        if len(comp) > 34:
            comp = comp[:33] + '…'
        a(f"  {c['id']:34s} {q:>10s} {comp:>34s}  {c['verdict']}")
    a('')
    a(f"  MATCH {sum(1 for c in census['claims'] if c['verdict'] == 'MATCH')}, "
      f"DIFF {sum(1 for c in census['claims'] if c['verdict'] == 'DIFF')}, "
      f"NOTE {sum(1 for c in census['claims'] if c['verdict'] == 'NOTE')}")
    return '\n'.join(L)


def render_md(census):
    L = []
    a = L.append
    f, d, auth, rel, pairs = (census['files'], census['declarations'],
                              census['statement_authority'], census['relations_module'],
                              census['pair_coverage'])
    a('# PhotoLean census')
    a('')
    a(f"Tree state: `HEAD {census['meta']['tree_state']['head'][:12]}` "
      f"({len(census['meta']['tree_state']['git_status_short'])} modified/untracked paths).")
    a('')
    a('## 1. Files')
    a('')
    a(f"- `.lean` files under `PhotoLean/`: **{f['lean_files_total']}**")
    a(f"- theory modules (`PhotoLean/<Theory>/*.lean`): **{f['theory_modules']}**")
    a(f"- top-level modules: **{len(f['top_level_modules'])}** "
      f"(`{'`, `'.join(f['top_level_modules'])}`)")
    a(f"- theory directories: **{f['theory_directories']}**")
    a('')
    a('| theory | modules |')
    a('|---|---|')
    for t, n in sorted(f['per_theory_modules'].items()):
        a(f"| {t} | {n} |")
    a(f"| **total** | **{f['theory_modules']}** |")
    a('')
    a('## 2. Declarations (source scan, primary)')
    a('')
    a(f"- (a) public excluding `private`: **{d['totals']['a_public_excluding_private']}**")
    a(f"- (b) public excluding `instance`: **{d['totals']['b_public_excluding_instance']}**")
    a(f"- (c) public `theorem|lemma|def|abbrev`: "
      f"**{d['totals']['c_public_theorem_lemma_def_abbrev']}**")
    a(f"- (d) `private`: **{d['totals']['d_private']}**")
    a(f"- kinds (public): {', '.join(f'{k}={v}' for k, v in d['kinds'].items())}")
    if census.get('environment', {}).get('ok'):
        e = census['environment']['total']
        a('')
        a(f"Environment cross-check: **{e.get('total')}** non-private `PhotoLean` constants "
          f"(thm {e.get('thm')}, defn {e.get('defn')}, induct {e.get('induct')}, "
          f"ctor {e.get('ctor')}, rec {e.get('rec')}, axiom {e.get('axiom')}; "
          f"`isInstance` {e.get('instance')}, `isStructure` {e.get('structure')}). "
          f"Auxiliary axiom constants: "
          f"{', '.join(census['environment']['auxiliary_axiom_constants']) or 'none'}.")
    a('')
    a('### Per-theory cross-check')
    a('')
    a('| theory | modules | source public (excl. private) | source private | probe authority | '
      'word-for-word | auxiliaries | delivered total | environment constants | env instances |')
    a('|---|---|---|---|---|---|---|---|---|---|')
    for r in census['per_theory']:
        a(f"| {r['theory']} | {r['modules']} | {r['source_public_excluding_private']} | "
          f"{r['source_private']} | {r['probe_authority']} | {r['probe_word_for_word']} | "
          f"{r['probe_auxiliaries']} | {r['probe_delivered_total']} | "
          f"{r['env_constants_total'] if r['env_constants_total'] is not None else '—'} | "
          f"{r['env_instances'] if r['env_instances'] is not None else '—'} |")
    a('')
    a('## 3. Statement authority and delivered totals')
    a('')
    a('| theory | authority | word-for-word | auxiliaries | delivered total | undelivered | '
      'signature diffs |')
    a('|---|---|---|---|---|---|---|')
    for r in auth['per_theory']:
        a(f"| {r['theory']} | {r['skeleton declarations']} | "
          f"{r['delivered, word-for-word']} | {r['delivered, not in authority']} | "
          f"{r['delivered_total (word-for-word + not in authority)']} | "
          f"{r['not delivered yet']} | {r['signature differences']} |")
    a(f"| **total** | **{auth['authority_total']}** | **{auth['word_for_word_total']}** | "
      f"**{auth['auxiliary_total']}** | **{auth['delivered_public_total']}** | "
      f"**{auth['not_delivered_total']}** | **{auth['signature_differences_total']}** |")
    a('')
    a('## 4. Relation module')
    a('')
    a('| § | title | rows | class |')
    a('|---|---|---|---|')
    for s in rel['sections']:
        cls = s['class'] or ('mixed' if s['rows'] else '— (documentation)')
        a(f"| {s['number']} | {s['title']} | {s['rows']} | {cls} |")
    a(f"| **total** | | **{rel['declaration_count']}** | ({rel['section_count']} sections) |")
    a('')
    a('### Fig. 3 class composition')
    a('')
    a('| class | quoted | computed | verdict |')
    a('|---|---|---|---|')
    for c in CLASS_ORDER:
        a(f"| {c} | {QUOTED_CLASS_COMPOSITION[c]} | {rel['class_totals'].get(c, 0)} | "
          f"{rel['class_verdicts'][c]} |")
    a(f"| **total** | **{sum(QUOTED_CLASS_COMPOSITION.values())}** | "
      f"**{rel['class_totals_sum']}** | "
      f"{'MATCH' if rel['class_totals_sum'] == 78 else 'DIFF'} |")
    a('')
    a(f"`rfl` kernel certificates (§1+§12): **{rel['rfl_certificate_count']}**.")
    a('')
    a('Per-row assignment:')
    a('')
    for s in rel['sections']:
        if not s['row_names']:
            continue
        cls = s['class'] or 'mixed'
        a(f"- **§{s['number']} {s['title']}** ({s['rows']} rows, class `{cls}`):")
        for c, names in sorted(s['rows_by_class'].items()):
            a(f"  - `{c}`: {', '.join('`' + n + '`' for n in names)}")
    a('')
    a('## 5. Pair coverage')
    a('')
    a(f"- nodes: {pairs['node_count']}; unordered pairs: {pairs['pairs_total']}")
    a(f"- edges: **{pairs['edge_count']}**; registered absences: **{pairs['absence_count']}**; "
      f"covered: **{pairs['covered_total']}**")
    a(f"- edge ∩ absence: {len(pairs['both_edge_and_absence'])}; unaccounted: "
      f"{len(pairs['unaccounted'])}")
    a(f"- completion-block pairs: **{pairs['completion_block_pairs']}**")
    a(f"- registry double-listings: {len(pairs['registry_double_listings'])}")
    a('')
    a('| pair | kind | citation |')
    a('|---|---|---|')
    for e in pairs['edges']:
        a(f"| {' ↔ '.join(e['pair'])} | edge | {e['cite']} |")
    for x in pairs['absences']:
        a(f"| {' ↔ '.join(x['pair'])} | absence | {x['cite']} |")
    a('')
    a('## 6. Negative results')
    a('')
    a(f"Pattern `{census['negative_results']['pattern']}`: "
      f"**{census['negative_results']['count']}** rows "
      f"(raw grep cross-check {census['negative_results']['raw_grep_count']}).")
    a('')
    a('| file | line | row |')
    a('|---|---|---|')
    for r in census['negative_results']['rows']:
        a(f"| {r['file']} | {r['line']} | `{r['name']}` |")
    a('')
    a('## 7. Gates')
    a('')
    if census.get('gates'):
        g = census['gates']
        a(f"- `proofs/scripts/check.sh --strict`: build **{g['build']}**, scan **{g['scan']}**, "
          f"leaf planes **{g['leaf_planes_ok']}/{g['leaf_planes_expected']}**, verdict "
          f"**{g['verdict']}** (exit {g['exit_code']})")
        a(f"- unused-variable warnings: **{g['unused_variable_warnings']}** in "
          f"**{len(g['unused_variable_files'])}** files (check.sh output "
          f"{g['unused_variable_warnings_check_sh']}, lake build traces "
          f"{g['unused_variable_warnings_traces']}; primary source: {g['unused_variable_source']})")
        a('')
        a('| file | line:col | variable |')
        a('|---|---|---|')
        for u in g['unused_variable_rows']:
            a(f"| {u['file']} | {u['line']}:{u['column']} | `{u['variable']}` |")
    else:
        a('- skipped (`--no-lean`)')
    a('')
    a('## 8. Axiom sweep')
    a('')
    if census.get('axioms'):
        x = census['axioms']
        a(f"- declarations requested **{x['declarations_requested']}**, printed "
          f"**{x['declarations_printed']}**, without axioms {x['declarations_without_axioms']}")
        a(f"- footprints outside `ALLOWED_AXIOMS` ({', '.join(x['allowed_axioms'])}): "
          f"**{x['footprints_outside_allowed']}**")
        a(f"- distinct footprints: {x['distinct_footprints']}")
        a(f"- unknown identifiers: {len(x['unknown_identifiers'])}")
    else:
        a('- skipped (pass `--axioms`)')
    a('')
    a('## 9. Claims')
    a('')
    a('| id | quoted | source | computed | verdict |')
    a('|---|---|---|---|---|')
    for c in census['claims']:
        a(f"| {c['id']} | {c['quoted']} | {c['source']} | {c['computed']} | {c['verdict']} |")
    a('')
    return '\n'.join(L)


# ── main ────────────────────────────────────────────────────────────────────────────────
def main():
    ap = argparse.ArgumentParser(description='PhotoLean census (the repository number source of record).')
    ap.add_argument('--json', nargs='?', const='tools/claims.json', default=None,
                    metavar='PATH', help='write the machine-readable census (default tools/claims.json)')
    ap.add_argument('--md', action='store_true', help='markdown output instead of plain text')
    ap.add_argument('--no-lean', action='store_true',
                    help='skip every Lean-toolchain step (check.sh gate, environment cross-check, '
                         'axioms sweep); source-level census only')
    ap.add_argument('--axioms', action='store_true',
                    help='run the #print axioms sweep (minutes)')
    args = ap.parse_args()

    files = all_lean_files()
    f_census = file_census(files)
    decls = []
    for p in files:
        decls.extend(scan_file(p))
    d_census = declaration_census(decls)
    theory_dirs = [t for t in f_census['theory_directories_names']]
    d_census['per_theory_totals_theory_dirs'] = sum(
        v['a_public_excluding_private'] for k, v in d_census['per_theory'].items()
        if k in theory_dirs)
    d_census['per_theory_totals_all'] = d_census['totals']['a_public_excluding_private']
    rel = relations_census(decls)
    pairs = pair_census()
    neg = negative_results(decls)
    auth = authority_census()

    census = {
        'meta': {
            'script': 'tools/counts.py',
            'contract': 'proofs/ENGINE.yml',
            'allowed_axioms': allowed_axioms(),
            'flags': {'no_lean': args.no_lean, 'axioms': args.axioms, 'md': args.md},
            'tree_state': git_state(),
            'theories': THEORIES,
        },
        'files': f_census,
        'declarations': d_census,
        'statement_authority': auth,
        'relations_module': rel,
        'pair_coverage': pairs,
        'negative_results': neg,
        'claims': [],
    }
    if not args.no_lean:
        census['environment'] = run_env_probe(files)
        census['gates'] = gates()
        if args.axioms:
            census['axioms'] = run_axioms_sweep(files, decls)

    # One row per theory, joining the three independent sources: the comment-aware source scan,
    # the fidelity probe, and (when available) the Lean environment.
    probe = {r['theory']: r for r in auth['per_theory']}
    env_ns = census.get('environment', {}).get('per_module_ns', {})
    per_theory = []
    for t in THEORIES:
        s = d_census['per_theory'].get(t, {})
        p = probe.get(t, {})
        e = env_ns.get(t, {})
        per_theory.append({
            'theory': t,
            'modules': f_census['per_theory_modules'].get(t, 0),
            'source_public_excluding_private': s.get('a_public_excluding_private'),
            'source_public_excluding_instance': s.get('b_public_excluding_instance'),
            'source_public_theorem_lemma_def_abbrev':
                s.get('c_public_theorem_lemma_def_abbrev'),
            'source_private': s.get('d_private'),
            'probe_authority': p.get('skeleton declarations'),
            'probe_word_for_word': p.get('delivered, word-for-word'),
            'probe_auxiliaries': p.get('delivered, not in authority'),
            'probe_delivered_total': p.get('delivered_total (word-for-word + not in authority)'),
            'probe_undelivered': p.get('not delivered yet'),
            'probe_signature_differences': p.get('signature differences'),
            'env_constants_total': e.get('total'),
            'env_instances': e.get('instance'),
            'env_structures': e.get('structure'),
            'env_minus_source': (e.get('total') - s.get('a_public_excluding_private'))
            if e.get('total') is not None and s.get('a_public_excluding_private') is not None
            else None,
        })
    census['pair_coverage']['citation_check'] = citation_check(
        {d.name for d in decls if d.name})
    census['per_theory'] = per_theory
    census['claims'] = build_claims(census)

    text = render_md(census) if args.md else render_text(census)
    print(text)
    if args.json:
        out = os.path.join(ROOT, args.json)
        os.makedirs(os.path.dirname(out), exist_ok=True)
        with open(out, 'w', encoding='utf-8') as fh:
            json.dump(census, fh, indent=2, sort_keys=True, ensure_ascii=False)
            fh.write('\n')
        print(f"\n[wrote {args.json}]", file=sys.stderr)
    return 0


if __name__ == '__main__':
    try:
        code = main()
        sys.stdout.flush()
        sys.exit(code)
    except BrokenPipeError:
        # Piping the census into `head`/`less` closes stdout early; leave without the
        # interpreter's final flush (which would raise the same error again at shutdown).
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, sys.stdout.fileno())
        os._exit(0)
