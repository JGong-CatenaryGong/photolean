#!/usr/bin/env python3
"""BEP instance-layer cross-check — the **non-Lean, independent** recomputation.

This is the non-Lean independent check of the numbers that the instance layer
`PhotoLean/BEP/Instances.lean` (plan §8.2, rows I1–I12) is going to assert. It is an
*evidence chain that does not go through the delivered Lean theorems*, and it is written to
be read by the verifier next to them. **It does not replace the kernel**: nothing here is a
proof, and a green run of this script is not an acceptance gate for any Lean declaration —
only `lake build` + `check.sh --strict` + `#print axioms` are.

What it recomputes, in exact rational arithmetic, from the family data printed in
`theories/BEP/LITERATURE.md` §R1.10 (Python standard library only — `fractions`, `os`, `re`,
`sys`; no third-party imports):

  0. before anything else it **re-reads its own transcription** of §R1.10 out of the record
     file, cell by cell (section [1b]): each `(driving force, barrier, kJ/mol, λ̂)` cell of
     F1/F2/F5, the aggregate rows of F3/F4, the prose rows of F3 and the prose family
     aggregates are compared with the values hard-coded below, so a stale transcription (or
     a changed record) fails loudly instead of silently invalidating the cross-check;
  1. per family: the observable two-point BEP slope `alphaObs = (ea₁ - ea₂)/(x₂ - x₁)`, the
     two-point reorganization-energy solver
     `lamOfPair = (x₂² - x₁²)/(2*(x₂ - x₁) - 4*(ea₁ - ea₂))`, and the second divided
     difference `sdd = ((e₃-e₂)/(x₃-x₂) - (e₂-e₁)/(x₂-x₁))/(x₃-x₁)` of the three points the
     Lean instances use (each point is a printed `(driving force x = -ΔG°, barrier)` pair);
  2. the model-side identities **as checks**: `sdd * 4 * lam = 1` and `sdd > 0` iff `lam > 0`
     when the three points are model data (`qEact lam x = (lam-x)²/(4λ)`), plus the negative
     controls that show why the premises `lam ≠ 0` and `x₁ ≠ x₃` are needed;
  3. the six-branch verdict of the `epQVerdict` cascade of
     `theories/BEP/probes/bep-statement-skeleton.lean` (branch order copied verbatim from
     lines 601–608) for every family point, together with the exhaustiveness of that order;
  4. the model-constructed families I1–I10 of plan §8.2 (λ, x, expected verdict, and the
     tolerance threshold pair λ = 2, w = 1, tol ∈ {1/8, 1/16});
  5. a final machine-readable table (`family | alphaObs | lamOfPair | sdd-sign | verdict |
     provenance flag`) for `theories/BEP/RESULTS.md`, and an explicit `UNSUPPORTED` line for
     every family in §R1.10 whose data are aggregate-only (no per-point pairs). No number is
     invented for an unsupported family.

Units. Every number is printed with the unit (or with the statement that it is
dimensionless), and the unit used is the source's own **kcal/mol** column of §R1.10 (the
record prints kcal/mol first and its own kJ/mol arithmetic second, with
`1 kcal/mol = 4.184 kJ/mol` stated in §R1.10.1); the script never silently converts, and it
audits each printed kJ/mol cell against 4.184 × kcal/mol. Dimensional bookkeeping:
`x`, `Ea`, `λ̂`, the barriers and the family λ̂ are `kcal/mol`; `alphaObs` is dimensionless
(barrier ÷ driving force); the second divided difference — the curvature witness — is
`1/(kcal/mol)`, and the model identity `sdd · 4 · λ = 1` is dimensionless as it must be.
The model-constructed rows I1–I10 carry no physical unit: they are the plan's rational
model inputs, and the same rationals hold in any unit system.

Exit status
-----------
0 — every number the Lean side asserts (plan §8.2 and the B5b block of
    `theories/BEP/probes/bep-statement-skeleton.lean`) agrees with the recomputation, and
    prints `CROSS-CHECK: OK`;
1 — at least one such value disagrees, **or** the transcription of §R1.10 could not be
    confirmed against the record file; each disagreement is printed as a diff
    (`recomputed … / Lean-side …`), so the failure names the number, the recomputed value
    and the asserted value.

Soft findings about `LITERATURE.md` itself (a printed aggregate that cannot be recomputed
from the printed rows, a printed per-row value that is not a root of the model quadratic,
a kJ/mol cell that does not follow from the kcal/mol cell) are reported in the `AUDIT`
section with `AUDIT-FAIL`. They are findings **about the literature record**, not about the
Lean layer, so they do not change the exit status; the exit code answers exactly one
question — "do the Lean-side values follow from §R1.10 as read back from the record?".
"""
from fractions import Fraction as F
import os
import re
import sys

# ────────────────────────────────────────────────────────────────────────────────────────
# [1] Lean `ℚ` semantics as used by `PhotoLean/BEP/RatModel.lean` (plan §8.1).
#     Lean's `x / 0 = 0` is *totalised* division, not an error: the mirror below must have
#     the same behaviour, otherwise I8 (λ = 0) cannot be recomputed at all.
# ────────────────────────────────────────────────────────────────────────────────────────


def qdiv(a, b):
    """Lean's `(a : ℚ) / b`: totalised, `a / 0 = 0`.

    Both arguments are coerced to `Fraction` first: `1/2` on two Python ints is *float*
    division, and a single float leaking into a `qTransfer` call silently destroys the
    exactness of every downstream comparison (measured: `qTransfer 3 2` came back as
    `0.16666666666666669` until the coercion was added).
    """
    a, b = F(a), F(b)
    return F(0) if b == 0 else a / b


def qEact(lam, x):
    """plan §8.1 `qEact lam x = (lam - x)^2 / (4 * lam)`."""
    return qdiv((lam - x) ** 2, 4 * lam)


def qBepLine(lam, x):
    """plan §8.1 `qBepLine lam x = lam / 4 - x / 2`."""
    return lam / 4 - x / 2


def qBepDefect(lam, x):
    """plan §8.1 `qBepDefect lam x = qEact lam x - qBepLine lam x`."""
    return qEact(lam, x) - qBepLine(lam, x)


def qTransfer(lam, x):
    """plan §8.1 `qTransfer lam x = 1 / 2 - x / (2 * lam)` (linear-response body)."""
    return qdiv(1, 2) - qdiv(x, 2 * lam)


def qReverseTransfer(lam, x):
    """plan §8.1 `qReverseTransfer lam x = 1 / 2 + x / (2 * lam)`."""
    return qdiv(1, 2) + qdiv(x, 2 * lam)


def qSecSlope(lam, x, h):
    """plan §8.1 `qSecSlope lam x h = (qEact lam x - qEact lam (x + h)) / h`."""
    return qdiv(qEact(lam, x) - qEact(lam, x + h), h)


def qAlphaObs(x1, ea1, x2, ea2):
    """plan §8.1 `qAlphaObs` — the observable two-point BEP slope."""
    return qdiv(ea1 - ea2, x2 - x1)


def qLamOfPair(x1, ea1, x2, ea2):
    """plan §8.1 `qLamOfPair` — the two-point solver (numerator `x₂² - x₁²`, corrected form)."""
    return qdiv(x2 ** 2 - x1 ** 2, 2 * (x2 - x1) - 4 * (ea1 - ea2))


def qConformsWindow(lam, tol, w):
    """plan §8.1 `qConformsWindow lam tol w = 0 < lam ∧ 0 < tol ∧ w^2 ≤ 4*lam*tol`."""
    return 0 < lam and 0 < tol and w ** 2 <= 4 * lam * tol


def qSecondDividedDiff(x1, e1, x2, e2, x3, e3):
    """plan §8.1 `qSecondDividedDiff` — the model's curvature witness."""
    return qdiv(qdiv(e3 - e2, x3 - x2) - qdiv(e2 - e1, x2 - x1), x3 - x1)


def qModelConsistent3(lam, x1, x2, x3, e1, e2, e3):
    """plan §8.1 `qModelConsistent3`: the three points are model data at this λ > 0."""
    return (0 < lam and e1 == qEact(lam, x1) and e2 == qEact(lam, x2)
            and e3 == qEact(lam, x3))


# `EPQVerdict` constructors, spelled as in the skeleton.
DEGENERATE = "degenerate"
UNPHYSICAL = "unphysical"
CONFORMING = "conforming"
BOUNDARY = "boundary"
SUPERLINEAR = "superLinear"
SUBLINEAR = "subLinear"


def epQVerdict(lam, x):
    """The `epQVerdict` cascade — branch order copied verbatim from
    `theories/BEP/probes/bep-statement-skeleton.lean` lines 601–608:

        if lam = 0        then .degenerate
        else if lam < 0   then .unphysical
        else if x = lam   then .boundary
        else if x = -lam  then .boundary
        else if 0 < qTransfer lam x ∧ qTransfer lam x < 1 then .conforming
        else if 1 < qTransfer lam x then .superLinear
        else .subLinear

    The guard order matters (see `check_cascade_branch_order`): `degenerate`/`unphysical`
    are tested before any use of `x`, and both `boundary` arms are consumed before the
    `qTransfer` comparisons.
    """
    if lam == 0:
        return DEGENERATE
    if lam < 0:
        return UNPHYSICAL
    if x == lam:
        return BOUNDARY
    if x == -lam:
        return BOUNDARY
    a = qTransfer(lam, x)
    if 0 < a and a < 1:
        return CONFORMING
    if 1 < a:
        return SUPERLINEAR
    return SUBLINEAR


# ────────────────────────────────────────────────────────────────────────────────────────
# [2] §R1.10 family data, read from `theories/BEP/LITERATURE.md`, verbatim in kcal/mol.
#     `dG0` is the source's printed ΔG° (F5: classical ΔE); the model's driving force is
#     x = -dG0. A row with `ea = None` prints no barrier and cannot enter the family.
# ────────────────────────────────────────────────────────────────────────────────────────

KG = F(4184, 1000)          # 1 kcal/mol = 4.184 kJ/mol, exact (thermochemical calorie)
UNIT = "kcal/mol"
SDD_UNIT = "1/(kcal/mol)"   # the second divided difference is a curvature, 1/(4λ)


class Family:
    """A §R1.10 family: printed rows, provenance, and the record's own aggregates."""

    def __init__(self, fid, label, row_kind, source, locus, status,
                 rows, aggregates=None, notes=(),
    short=None):
        self.fid = fid
        self.label = label
        self.short = short or label
        self.row_kind = row_kind        # "ΔG°" (Gibbs) or "ΔE" (classical energy)
        self.source = source
        self.locus = locus
        self.status = status            # provenance flag of the family
        self.rows = rows                # (name, dG0|dE, barrier|None, kJ_dG0, kJ_barrier)
        self.aggregates = aggregates or {}
        self.notes = list(notes)

    def points(self):
        """The printed rows that carry a barrier, as (name, x, ea) with x = -dG0."""
        return [(n, -d, e) for n, d, e, _kjd, _kje in self.rows if e is not None]

    def dropped(self):
        return [(n, d) for n, d, e, _kjd, _kje in self.rows if e is None]


# F1 — Antioxidants 15(7) 840–860 (2026), DOI 10.3390/antiox15070868, Table 1 "Water" columns.
F1 = Family(
    "F1", "f-HAT phenolic O–H → •OOH, water", "ΔG°",
    "Antioxidants 15(7) 840–860 (2026), DOI 10.3390/antiox15070868 (OA, PMC13405240)",
    "Table 1, 'Water' columns, 298.15 K", "first-hand",
    [
        ("16(2)", F("-0.3"), F("15.6"), F("-1.3"), F("65.3")),
        ("16(1)", F("-0.9"), F("15.7"), F("-3.8"), F("65.7")),
        ("19(2)", F("1.9"), F("17.3"), F("7.9"), F("72.4")),
        ("14(1)", F("-2.3"), F("15.7"), F("-9.6"), F("65.7")),
        ("12", F("-4.9"), F("13.9"), F("-20.5"), F("58.2")),
        ("2", F("-6.7"), F("12.4"), F("-28.0"), F("51.9")),
        ("7", F("-11.6"), F("8.2"), F("-48.5"), F("34.3")),
        ("8", F("-12.9"), F("8.8"), F("-54.0"), F("36.8")),
        ("10†", F("-19.1"), None, F("-79.9"), None),
    ],
    aggregates=dict(n=31, mean=F("61.5"), sd=F("4.5"), range=(F("53.5"), F("67.3")),
                    curvature=F("-0.0160"), lam_from_curvature=F("-15.7"),
                    fit="Ea = 16.6 - 0.613x", r2=F("0.934")),
    notes=("9 printed rows of 31 pairs; row 10† prints no water barrier.",),
    short="f-HAT water/\u2022OOH",
)

# F2 — same paper, Table 1 "PE" (pentyl ethanoate) columns.
F2 = Family(
    "F2", "same reaction, solvent pentyl ethanoate (PE)", "ΔG°",
    "Antioxidants 15(7) 840–860 (2026), DOI 10.3390/antiox15070868 (OA, PMC13405240)",
    "Table 1, 'PE' columns", "first-hand",
    [
        ("16(2)", F("1.0"), F("14.0"), F("4.2"), F("58.6")),
        ("13", F("-2.2"), F("13.3"), F("-9.2"), F("55.6")),
        ("19(2)", F("3.1"), F("14.6"), F("13.0"), F("61.1")),
        ("2", F("-4.6"), F("10.0"), F("-19.2"), F("41.8")),
        ("1", F("-6.3"), F("9.1"), F("-26.4"), F("38.1")),
        ("8", F("-9.2"), F("8.5"), F("-38.5"), F("35.6")),
        ("10", F("-14.3"), F("5.1"), F("-59.8"), F("21.3")),
    ],
    aggregates=dict(n=34, mean=F("50.3"), sd=F("3.7"), range=(F("44.4"), F("57.5")),
                    curvature=F("-0.0253"), lam_from_curvature=F("-9.9"),
                    fit="Ea = 14.5 - 0.498x", r2=F("0.548")),
    notes=("7 printed rows of 34 pairs.",),
    short="f-HAT PE/\u2022OOH",
)

# F3 — same paper, Table 2 "Water" columns (•OOCH₃ as the abstracting radical).
F3 = Family(
    "F3", "same substrates with •OOCH₃, water", "ΔG°",
    "Antioxidants 15(7) 840–860 (2026), DOI 10.3390/antiox15070868 (OA, PMC13405240)",
    "Table 2, 'Water' columns", "first-hand",
    [
        ("16(1)", F("0.8"), F("15.6"), None, None),
        ("19(2)", F("3.6"), F("17.7"), None, None),
        ("1", F("-7.1"), F("11.0"), None, None),
        ("7", F("-9.9"), F("7.3"), None, None),
        ("10", F("-17.3"), None, None, None),
    ],
    aggregates=dict(n=31, mean=F("59.4"), sd=None, range=(F("46.9"), F("68.2")),
                    curvature=F("-0.0074"), lam_from_curvature=F("-33.6"),
                    fit="Ea = 15.5 - 0.651x", r2=F("0.934")),
    notes=("5 representative water rows printed; row 10 prints no water barrier; the "
           "kJ/mol columns are not printed for this table.",),
    short="\u2022OOCH\u2083 water",
)

# F4 — same paper, Table 2 "PE" columns: AGGREGATES ONLY, no per-row pairs.
F4 = Family(
    "F4", "same substrates with •OOCH₃, PE", "ΔG°",
    "Antioxidants 15(7) 840–860 (2026), DOI 10.3390/antiox15070868 (OA, PMC13405240)",
    "Table 2, 'PE' columns", "first-hand",
    [],
    aggregates=dict(n=34, mean=F("53.4"), sd=None, range=(F("43.8"), F("57.9")),
                    curvature=F("-0.0046"), lam_from_curvature=F("-54.8"),
                    fit="Ea = 13.7 - 0.585x", r2=F("0.952")),
    notes=("aggregate-only: mean λ̂, λ̂ range, curvature, linear fit and R² are printed, but "
           "no per-row (x, Ea) pair -> no statement of the instance block can be built on it.",),
    short="\u2022OOCH\u2083 PE",
)

# F5 — Chem. Sci. 6(10) 5866–5881 (2015), Table 1, CCSD(T)-F12a/jun-cc-pVTZ row.
F5 = Family(
    "F5", "site-resolved C–H abstraction from 2-butanol by •OOH (classical CCSD(T))", "ΔE",
    "Chem. Sci. 6(10) 5866–5881 (2015), DOI 10.1039/c5sc01848j (OA, PMC5950756)",
    "Table 1, row CCSD(T)-F12a/jun-cc-pVTZ", "first-hand",
    [
        ("R2", F("7.62"), F("12.38"), F("31.9"), F("51.8")),
        ("R3", F("13.14"), F("17.57"), F("55.0"), F("73.5")),
        ("R4", F("14.56"), F("17.47"), F("60.9"), F("73.1")),
        ("R1", F("15.80"), F("20.32"), F("66.1"), F("85.0")),
        ("R5", F("19.82"), F("21.72"), F("82.9"), F("90.9")),
    ],
    aggregates=dict(n=5, mean=F("37.4507"), sd=None,
                    range=(F("32.493019"), F("44.007305")),
                    curvature=F("-0.0203"), lam_from_curvature=F("-12.3"),
                    fit=None, r2=None),
    notes=("all 5 rows printed (the only §R1.10 family whose aggregates are recomputable "
           "from the printed rows); the printed quantity is a classical ΔE, not a ΔG°.",
           ),
    short="2-butanol CCSD(T)",
)

FAMILIES = [F1, F2, F3, F4, F5]

# §R1.10.7 — families deliberately left unfilled: no pair data at all, nothing to recompute.
UNFILLED = [
    ("Miller–Calcaterra–Closs 1984 series (dispatch option (b))",
     "the sibling record's λ = 1.20 eV and x ∈ {0.05, 1.23, 2.40} eV are our own fit-derived "
     "x values, not printed (ΔG°, Ea) pairs; primary series paywalled — not-accessed"),
    ("reaction-centre numbers (Nobel 1992 p. 88)",
     "quoted modelling numbers inside a lecture (~-prefixed), not a (ΔG°, Ea) table — "
     "not-accessed"),
    ("Evans–Polanyi 1938 halogen/H₂ exchange data (§R1.3)",
     "body not-accessed (RSC 403); no numbers invented"),
    ("combustion-model H-abstraction barriers (J. Phys. Chem. A 119, 7652 (2015), Table 6)",
     "barriers printed as fitted E/R, the corresponding ΔrH not-accessed — no pair can be formed"),
    ("Denisov 2012 (ΔH, Ee) (Russ. Chem. Rev. 81, 1117, Table 6)",
     "barriers computed by that paper's own intersecting-parabola model — usable as a "
     "self-consistency check, never as evidence"),
    ("HER BEP form (npj Comput. Mater. 10, 98 (2024))",
     "the 14 metal points exist only in a figure; the printed ΔG‡₀ = 0.7 eV, α = 0.5 are "
     "fitted parameters, not point data"),
]

# ────────────────────────────────────────────────────────────────────────────────────────
# [3] The Lean-side values to be checked, and where they are asserted.
#     `PLAN` = theories/BEP/plan.md §8.2; `SKEL` = theories/BEP/probes/bep-statement-skeleton.lean.
# ────────────────────────────────────────────────────────────────────────────────────────

PLAN = "plan §8.2"
SKEL = "skeleton B5b"

# I1–I10, model-constructed: id, λ, x, expected verdict, expected α = qTransfer λ x,
# expected window checks (tol, w), and the assertion loci.
MODEL_INSTANCES = [
    ("I1", "thermoneutral family", F(2), F(0), CONFORMING, F(1, 2), [(F(1, 4), F(0), True)],
     "plan §8.2 I1; skeleton 749/752/755"),
    ("I2", "mildly exergonic", F(2), F(1, 2), CONFORMING, F(3, 8), [(F(1, 4), F(1, 2), True)],
     "plan §8.2 I2; skeleton 759/762/765"),
    ("I3", "mildly endergonic", F(2), F(-1, 2), CONFORMING, F(5, 8), [(F(1, 4), F(1, 2), True)],
     "plan §8.2 I3; skeleton 769/772/775"),
    ("I4", "forward barrierless limit", F(2), F(2), BOUNDARY, F(0), [],
     "plan §8.2 I4; skeleton 779/782/787"),
    ("I5", "reverse barrierless limit", F(2), F(-2), BOUNDARY, F(1), [],
     "plan §8.2 I5; skeleton 792/795/798"),
    ("I6", "forward inverted region", F(2), F(3), SUBLINEAR, F(-1, 4), [],
     "plan §8.2 I6; skeleton 804/807/810"),
    ("I7", "reverse inverted region", F(2), F(-3), SUPERLINEAR, F(5, 4), [],
     "plan §8.2 I7; skeleton 816/819/822"),
    ("I8", "degenerate family", F(0), F(1), DEGENERATE, F(1, 2), [],
     "plan §8.2 I8 (corrected row); skeleton 830/833/836"),
    ("I9", "unphysical curvature", F(-2), F(1), UNPHYSICAL, F(3, 4), [],
     "plan §8.2 I9 + numeric-audit note; skeleton 841/844/847/850"),
    ("I10", "tolerance threshold", F(2), None, None, None,
     [(F(1, 8), F(1), True), (F(1, 16), F(1), False)],
     "plan §8.2 I10; skeleton 856/859"),
]

# I11/I12, literature: fid -> the three printed rows the instance block uses, and the
# Lean-side expected values (verbatim from the skeleton).
LIT_INSTANCES = {
    "F1": dict(
        alpha_pair=("16(2)", "8"),
        lam_pair=("16(2)", "16(1)"),
        triple=("16(1)", "14(1)", "12"),
        alpha=F(34, 63), lam_hat=F(9, 20), sdd=F(-9, 52),
        loci="skeleton 876/880/883/888; plan §8.2 I11",
    ),
    "F2": dict(
        alpha_pair=("16(2)", "10"),
        lam_pair=("16(2)", "13"),
        triple=("16(2)", "13", "2"),
        alpha=F(89, 153), lam_hat=F(16, 15), sdd=F(-185, 896),
        loci="skeleton 895/899/902/908; plan §8.2 I11",
    ),
    "F3": dict(
        alpha_pair=("16(1)", "7"),
        lam_pair=("16(1)", "19(2)"),
        triple=("16(1)", "1", "7"),
        alpha=F(83, 107), lam_hat=F(22, 5), sdd=F(-8175, 118342),
        loci="skeleton 916/920/923/928; plan §8.2 I11",
    ),
    "F5": dict(
        alpha_pair=("R2", "R5"),
        lam_pair=("R2", "R3"),
        triple=("R4", "R1", "R5"),
        alpha=F(467, 610), lam_hat=F(7958, 675), sdd=F(-1215125, 3277506),
        loci="skeleton 939/943/947/953; plan §8.2 I11",
    ),
}

# The plan §8.2 tolerance pair (λ = 2, w = 1) — the exact threshold is tol* = w²/(4λ) = 1/8.
I10_LAM, I10_W = F(2), F(1)
I10_TOL_TRUE, I10_TOL_FALSE = F(1, 8), F(1, 16)

# The model sampling the script itself uses for the model-constructed rows (documented,
# not hidden): three abscissae x, x + h, x + 2h with h = 1/2.
MODEL_H = F(1, 2)


# ────────────────────────────────────────────────────────────────────────────────────────
# [4] Output helpers.
# ────────────────────────────────────────────────────────────────────────────────────────

FAILURES = []      # (id, source, recomputed, asserted)  -> exit 1
AUDITS = []        # (severity, text)                    -> exit 0, findings about LITERATURE.md
CHECKS = [0]


def fmt(v):
    """`n/d` plus a decimal rendering, so both the kernel form and the human form are visible."""
    if isinstance(v, F):
        if v.denominator == 1:
            return "%d" % v.numerator
        return "%s (%.6f)" % (v, float(v))
    return str(v)


def near(v, nd=6):
    """Compact decimal display for values produced by bisection (whose exact fractions are
    astronomically large but whose decimal rendering is what a reader needs)."""
    return ("%%.%df" % nd) % float(v)


def printed(v):
    """Render a Fraction the way the source prints it (a decimal, no trailing zeros).

    Used only to *search* the record's prose for a value: `str(F(4, 5))` is `4/5`, which
    never occurs in the source, so a naive `str()` silently makes a token check vacuous."""
    return ("%.4f" % float(v)).rstrip("0").rstrip(".")


def check(cid, source, got, want):
    CHECKS[0] += 1
    if got != want:
        FAILURES.append((cid, source, got, want))


def audit(ok, text):
    AUDITS.append((("AUDIT-OK" if ok else "AUDIT-FAIL"), text))


def row_named(fam, name):
    for n, dG0, ea, kjd, kje in fam.rows:
        if n == name:
            return (-dG0, ea)
    raise KeyError("%s has no printed row %r" % (fam.fid, name))


def line(char="-", n=96):
    print(char * n)

def section(title):
    print()
    line("=")
    print(title)
    line("=")


# ────────────────────────────────────────────────────────────────────────────────────────
# [5] §R1.10 data as read (units printed per number).
# ────────────────────────────────────────────────────────────────────────────────────────

def dump_data():
    section("[1] §R1.10 family data as read from theories/BEP/LITERATURE.md "
            "(source unit: %s)" % UNIT)
    for fam in FAMILIES:
        print()
        print("%s — %s" % (fam.fid, fam.label))
        print("    source : %s" % fam.source)
        print("    locus  : %s" % fam.locus)
        print("    status : %s   unit: printed %s columns (the record's kJ/mol columns are "
              "its own arithmetic)" % (fam.status, UNIT))
        if fam.rows:
            print("    rows   : %-7s %14s %14s %14s"
                  % ("row", ("%s/%s" % (fam.row_kind, UNIT)),
                     ("barrier/%s" % UNIT), "x = -%s" % fam.row_kind))
            for n, dG0, ea, _kjd, _kje in fam.rows:
                print("             %-7s %14s %14s %14s"
                      % (n, fmt(dG0), ("(none printed)" if ea is None else fmt(ea)),
                         fmt(-dG0)))
        else:
            print("    rows   : NONE — aggregate-only family (%s)" % "; ".join(fam.notes))
        for note in fam.notes:
            print("    note   : %s" % note)


# ────────────────────────────────────────────────────────────────────────────────────────
# [5b] Read-back: re-read the numbers above from §R1.10 of LITERATURE.md and compare them
#      cell by cell. A stale transcription would invalidate the whole cross-check, so a
#      read-back mismatch is a hard failure (exit 1), not a soft audit note.
# ────────────────────────────────────────────────────────────────────────────────────────

LIT_PATH = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                         os.pardir, "LITERATURE.md"))
NONE_TOKENS = {"(none)", "\u2014", "\u2013", "-", ""}
EM_DASH = "\u2014"
EN_DASH = "\u2013"
MINUS = "\u2212"


def norm_cell(s):
    """Normalise a markdown table cell: unicode minus -> ASCII, drop markdown emphasis."""
    s = s.replace(MINUS, "-").replace("**", "").replace("*", "").replace("`", "")
    return " ".join(s.split()).strip()


def cell_value(cell):
    """Fraction value of a table cell, or None for the record's '(none)'/dash cells."""
    c = norm_cell(cell)
    if c in NONE_TOKENS:
        return None
    return F(c)


def split_range(cell):
    """`46.9–68.2` (en dash) -> (F(46.9), F(68.2))."""
    parts = [p.strip() for p in re.split("[" + EN_DASH + EM_DASH + "]", norm_cell(cell))
             if p.strip()]
    return tuple(F(p) for p in parts)


def lit_section(path):
    """(first_line, last_line, {subsection key: text}) for the §R1.10 span of the record."""
    with open(path, encoding="utf-8") as fh:
        lines = fh.read().splitlines()
    start = end = None
    for i, ln in enumerate(lines):
        if ln.startswith("# §R1.10"):
            start = i
        elif start is not None and ln.startswith("# §R1.11"):
            end = i
            break
    if start is None:
        return None, None, None
    if end is None:
        end = len(lines)
    secs = {}
    cur = None
    for ln in lines[start:end]:
        if ln.startswith("## "):
            cur = ln[3:].strip()
            secs[cur] = []
        elif cur is not None:
            secs[cur].append(ln)
    return start + 1, end, {k: "\n".join(v) for k, v in secs.items()}


def table_rows(text):
    """Markdown table body rows of a section, as lists of normalised cells."""
    out = []
    for ln in text.splitlines():
        s = ln.strip()
        if not s.startswith("|"):
            continue
        cells = [norm_cell(c) for c in s.strip("|").split("|")]
        if all(set(c) <= set("-: ") for c in cells):
            continue                                   # separator row
        if cells and cells[0] in ("substrate", "site", "solvent"):
            continue                                   # header row
        out.append(cells)
    return out


def find_section(secs, key):
    for k, v in secs.items():
        if k.startswith(key):
            return v
    return None


def readback_literature():
    section("[1b] read-back of §R1.10 — the transcription above is re-read from the record")
    if not os.path.exists(LIT_PATH):
        print("  record not found at %s" % LIT_PATH)
        check("DATA read-back: LITERATURE.md exists", "script input", False, True)
        return
    first, last, secs = lit_section(LIT_PATH)
    print("  file: %s   §R1.10 span: lines %s–%s   subsections: %d"
          % (LIT_PATH, first, last, len(secs) if secs else 0))
    if not secs:
        check("DATA read-back: §R1.10 section found", "script input", False, True)
        return
    table_fams = {"F1": "R1.10.2", "F2": "R1.10.3", "F3": "R1.10.4", "F4": "R1.10.4",
                  "F5": "R1.10.5"}
    ok_cells = 0
    for fam in FAMILIES:
        text = find_section(secs, table_fams[fam.fid])
        if text is None:
            check("DATA read-back: subsection %s present" % table_fams[fam.fid],
                  "LITERATURE.md", False, True)
            continue
        rows = {r[0]: r for r in table_rows(text)}
        print("  %s: subsection %s, %d markdown table row(s) read"
              % (fam.fid, table_fams[fam.fid], len(rows)))
        if fam.fid in ("F1", "F2", "F5"):
            for n, dG0, ea, kjd, kje in fam.rows:
                if n not in rows:
                    check("DATA read-back %s row %s present" % (fam.fid, n), "LITERATURE.md",
                          False, True)
                    continue
                r = rows[n]
                want = [dG0, ea, kjd, kje]
                for j, (label, w) in enumerate(zip(("ΔG° (kcal/mol)", "barrier (kcal/mol)",
                                                    "ΔG° (kJ/mol)", "barrier (kJ/mol)"), want)):
                    got = cell_value(r[j + 1]) if j + 1 < len(r) else None
                    check("DATA read-back %s row %s %s" % (fam.fid, n, label), "LITERATURE.md",
                          got, w)
                    ok_cells += 1
                if len(r) > 5 and n in fam.aggregates.get("printed_lam_hat", {}):
                    check("DATA read-back %s row %s printed λ̂" % (fam.fid, n), "LITERATURE.md",
                          cell_value(r[5]), fam.aggregates["printed_lam_hat"][n])
                    ok_cells += 1
            # family aggregates of F1/F2/F5, printed as prose under the table
            norm = norm_cell(text)
            m = re.search(r"mean ([\d.]+), sd ([\d.]+), range\s+([\d.]+)" + EN_DASH
                          + r"([\d.]+)", norm)
            if m:
                check("DATA read-back %s family mean λ̂" % fam.fid, "LITERATURE.md",
                      F(m.group(1)), fam.aggregates["mean"])
                check("DATA read-back %s family sd" % fam.fid, "LITERATURE.md",
                      F(m.group(2)), fam.aggregates["sd"])
                check("DATA read-back %s family λ̂ range" % fam.fid, "LITERATURE.md",
                      (F(m.group(3)), F(m.group(4))), fam.aggregates["range"])
                ok_cells += 3
            else:
                m = re.search(r"mean ([\d.]+), range ([\d.]+)" + EN_DASH + r"([\d.]+)", norm)
                if m:
                    check("DATA read-back %s family mean λ̂" % fam.fid, "LITERATURE.md",
                          F(m.group(1)), fam.aggregates["mean"])
                    check("DATA read-back %s family λ̂ range" % fam.fid, "LITERATURE.md",
                          (F(m.group(2)), F(m.group(3))), fam.aggregates["range"])
                    ok_cells += 2
        if fam.fid in ("F3", "F4"):
            row = rows.get("water" if fam.fid == "F3" else "PE")
            if row is None:
                check("DATA read-back %s aggregate row present" % fam.fid, "LITERATURE.md",
                      False, True)
                continue
            check("DATA read-back %s n" % fam.fid, "LITERATURE.md", F(row[1]),
                  F(fam.aggregates["n"]))
            check("DATA read-back %s mean λ̂" % fam.fid, "LITERATURE.md",
                  F(re.search(r"[\d.]+", row[2]).group(0)), fam.aggregates["mean"])
            check("DATA read-back %s λ̂ range" % fam.fid, "LITERATURE.md",
                  split_range(row[3]), fam.aggregates["range"])
            nums = [F(x) for x in re.findall(r"[-+]?\d+(?:\.\d+)?", row[4])]
            check("DATA read-back %s curvature" % fam.fid, "LITERATURE.md", nums[0],
                  fam.aggregates["curvature"])
            check("DATA read-back %s λ from curvature" % fam.fid, "LITERATURE.md", nums[1],
                  fam.aggregates["lam_from_curvature"])
            if fam.aggregates.get("fit") is not None:
                check("DATA read-back %s linear fit" % fam.fid, "LITERATURE.md",
                      re.sub(r"\s+", "", row[6]), re.sub(r"\s+", "", fam.aggregates["fit"]))
            if fam.aggregates.get("r2") is not None:
                check("DATA read-back %s R²" % fam.fid, "LITERATURE.md", F(row[7]),
                      fam.aggregates["r2"])
            ok_cells += 6
    # F3's per-row data are printed as prose, not as a table: token-level read-back.
    f3text = norm_cell(find_section(secs, "R1.10.4") or "")
    for n, dG0, ea, _kjd, _kje in F3.rows:
        for label, tok in (("ΔG°", ("+" if dG0 > 0 else "-") + printed(abs(dG0))),
                           ("barrier", None if ea is None else printed(ea))):
            if tok is None:
                continue
            check("DATA read-back F3 row %s %s token" % (n, label), "LITERATURE.md",
                  tok in f3text, True)
            ok_cells += 1
    print("  read-back: %d cell(s)/token(s) compared against the record." % ok_cells)


# ────────────────────────────────────────────────────────────────────────────────────────
# [6] Model-constructed families I1–I10 (recomputation + the Lean-side comparison).
# ────────────────────────────────────────────────────────────────────────────────────────

def check_model_instances():
    section("[2] model-constructed families I1–I10 (plan §8.2) — recomputed in ℚ")
    print("The script samples each model family at x, x+1/2, x+1 (its own documented choice):")
    print("`alphaObs` is the observable slope between the first two samples, `lamOfPair` the")
    print("solver on the same two samples, `sdd` the second divided difference of all three.")
    print()
    print("  %-4s %-26s %-8s %-8s %-16s %-16s %-16s %-16s  %-11s"
          % ("id", "family", "lam", "x", "qEact", "qBepDefect", "alphaObs", "qTransfer",
             "verdict"))
    line("-", 140)
    for (iid, label, lam, x, verdict, alpha, windows, loci) in MODEL_INSTANCES:
        if x is None:       # I10 has no single point: threshold pair only
            continue
        pts = [(xx, qEact(lam, xx)) for xx in (x, x + MODEL_H, x + 2 * MODEL_H)]
        obs = qAlphaObs(pts[0][0], pts[0][1], pts[1][0], pts[1][1])
        lam_hat = qLamOfPair(pts[0][0], pts[0][1], pts[1][0], pts[1][1])
        sdd = qSecondDividedDiff(pts[0][0], pts[0][1], pts[1][0], pts[1][1],
                                 pts[2][0], pts[2][1])
        got_verdict = epQVerdict(lam, x)
        got_alpha = qTransfer(lam, x)
        print("  %-4s %-26s %-8s %-8s %-16s %-16s %-16s %-16s  %-11s"
              % (iid, label, fmt(lam), fmt(x), fmt(qEact(lam, x)), fmt(qBepDefect(lam, x)),
                 fmt(obs), fmt(got_alpha), got_verdict))
        check("%s verdict (skeleton B5b)" % iid, loci, got_verdict, verdict)
        check("%s transfer (skeleton B5b)" % iid, loci, got_alpha, alpha)
        if lam != 0:
            check("%s secant = coefficient at the midpoint (skeleton qSecSlope_eq_qTransfer_mid)"
                  % iid, "plan §8.1; skeleton 640",
                  obs, qTransfer(lam, x + MODEL_H / 2))
        if lam != 0:
            check("%s two-point solver recovers lam (skeleton qLamOfPair_reconstructs)" % iid,
                  "plan §8.1; skeleton 653", lam_hat, lam)
        check("%s sdd sign is the model sign for lam %s 0 (skeleton "
              "qModelConsistent3_curvature_pos)" % (iid, ">" if lam > 0 else ("<" if lam < 0
                                                                               else "=")),
              "plan §8.1; skeleton 706",
              (sdd > 0) if lam > 0 else ((sdd < 0) if lam < 0 else (sdd == 0)), True)
        if lam != 0:
            check("%s sdd * 4 * lam = 1 (model identity)" % iid, "plan §8.1; skeleton 699",
                  sdd * 4 * lam, F(1))
        for (tol, w, want) in windows:
            check("%s qConformsWindow lam %s w %s (skeleton B5b)" % (iid, fmt(tol), fmt(w)),
                  loci, qConformsWindow(lam, tol, w), want)
    # I8, the degenerate family: the two premises that the negative controls below need.
    check("I8 qEact 0 1 = 0 (totalised division, plan §8.2 I8)", "skeleton 833",
          qEact(F(0), F(1)), F(0))
    check("I8 qTransfer 0 1 = 1/2 (linear-response body, corrected row)", "plan §8.2 I8; "
          "skeleton 836", qTransfer(F(0), F(1)), F(1, 2))
    check("negative control I8: at lam = 0 the secant/midpoint identity fails "
          "(0 ≠ 1/2) — which is why the skeleton carries `hlam : lam ≠ 0`",
          "plan §8.1; skeleton 640",
          qSecSlope(F(0), F(1), MODEL_H) != qTransfer(F(0), F(1) + MODEL_H / 2), True)
    check("I8 two-point solver does NOT recover lam = 0 (the `lam ≠ 0` premise is necessary)",
          "plan §8.1; skeleton 650-655",
          qLamOfPair(F(0), qEact(F(0), F(0)), F(1, 2), qEact(F(0), F(1, 2))), F(1, 4))
    # I4/I5 boundary arms: the *open* band 0 < α < 1 really fails there.
    check("I4 not (0 < α < 1) at the boundary arm", "skeleton 787",
          (0 < qTransfer(F(2), F(2)) and qTransfer(F(2), F(2)) < 1), False)
    check("I5 not (0 < α < 1) at the boundary arm", "skeleton 798",
          (0 < qTransfer(F(2), F(-2)) and qTransfer(F(2), F(-2)) < 1), False)
    check("I6 not (0 ≤ α ≤ 1)", "skeleton 810",
          (0 <= qTransfer(F(2), F(3)) <= 1), False)
    check("I7 not (0 ≤ α ≤ 1)", "skeleton 822",
          (0 <= qTransfer(F(2), F(-3)) <= 1), False)
    check("I9 defect = -1/8", "skeleton 847", qBepDefect(F(-2), F(1)), F(-1, 8))
    check("I9 bounds are blind: 0 ≤ α ≤ 1 still holds", "skeleton 850",
          (0 <= qTransfer(F(-2), F(1)) <= 1), True)
    # I10: the tolerance threshold pair, and the exact threshold tol* = w^2/(4*lam).
    print()
    print("  I10 tolerance threshold  lam = %s, w = %s (%s): threshold tol* = w^2/(4*lam) = %s"
          % (fmt(I10_LAM), fmt(I10_W), "model rationals", fmt(I10_W ** 2 / (4 * I10_LAM))))
    check("I10 conforms at tol = 1/8 (w^2 = 4*lam*tol exactly)", "skeleton 856",
          qConformsWindow(I10_LAM, I10_TOL_TRUE, I10_W), True)
    check("I10 fails at tol = 1/16", "skeleton 859",
          qConformsWindow(I10_LAM, I10_TOL_FALSE, I10_W), False)
    check("I10 threshold is exact: tol* = 1/8", "plan §8.2 I10",
          I10_W ** 2 / (4 * I10_LAM), I10_TOL_TRUE)
    check("I10 halving below the threshold still fails (tol = 1/32, w = 1)", "plan §8.2 I10",
          qConformsWindow(I10_LAM, F(1, 32), I10_W), False)


# ────────────────────────────────────────────────────────────────────────────────────────
# [7] Model-side identities as checks, with the negative controls that motivate the
#     premises (this is the part that must *not* be assumed: it is recomputed here).
# ────────────────────────────────────────────────────────────────────────────────────────

def check_model_identities():
    section("[3] model-side identities (checks) and premise negative controls")
    print("Model barrier: qEact lam x = (lam - x)^2/(4*lam) (totalised division). Three model")
    print("points at x, x+1/2, x+1 must give sdd = 1/(4*lam). No unit is claimed here: these")
    print("are the plan's rational model inputs.")
    print()
    print("  %-8s %-12s %-12s %-14s" % ("lam", "sdd", "4*lam*sdd", "identity"))
    line()
    for lam in (F(1), F(2), F(-2), F(1, 2), F(-1, 2), F(3), F(9, 4), F(-7, 3)):
        pts = [(xx, qEact(lam, xx)) for xx in (F(0), F(1, 2), F(1))]
        sdd = qSecondDividedDiff(pts[0][0], pts[0][1], pts[1][0], pts[1][1],
                                 pts[2][0], pts[2][1])
        print("  %-8s %-12s %-12s %-14s"
              % (fmt(lam), fmt(sdd), fmt(4 * lam * sdd), "OK" if 4 * lam * sdd == 1 else "BROKEN"))
        check("model identity sdd*4*lam = 1 at lam = %s" % fmt(lam),
              "plan §8.1 qSecondDividedDiff_model", sdd * 4 * lam, F(1))
        check("model forces sign(sdd) = sign(lam) for lam = %s" % fmt(lam),
              "plan §8.1 qModelConsistent3_curvature_pos",
              (sdd > 0, sdd < 0, sdd == 0),
              (lam > 0, lam < 0, lam == 0))
    print()
    print("  negative control 1 — lam = 0 (premise `lam ≠ 0`): points (0,0), (1/2,0), (1,0):")
    sdd0 = qSecondDividedDiff(F(0), qEact(F(0), F(0)), F(1, 2), qEact(F(0), F(1, 2)),
                              F(1), qEact(F(0), F(1)))
    print("      sdd = %s, 4*lam*sdd = %s ≠ 1  → the identity genuinely needs `lam ≠ 0`."
          % (fmt(sdd0), fmt(4 * F(0) * sdd0)))
    check("negative control: lam = 0 breaks sdd*4*lam = 1 (the premise is necessary)",
          "plan §8.1; skeleton 650", sdd0 * 4 * F(0) != F(1), True)
    print()
    print("  negative control 2 — x₁ = x₃ (premise `x₁ ≠ x₃`): points (0,1/4), (1,0), (0,1/4)")
    print("      at lam = 1: the outer denominator is 0 and totalised division gives 0, so")
    sdd_same = qSecondDividedDiff(F(0), qEact(F(1), F(0)), F(1), qEact(F(1), F(1)),
                                  F(0), qEact(F(1), F(0)))
    print("      sdd = %s ≠ 1/4 %s — the third pairwise-distinctness premise is not decorative."
          % (fmt(sdd_same), SDD_UNIT))
    check("negative control: x₁ = x₃ breaks sdd = 1/(4λ) (the premise is necessary)",
          "plan §8.1; skeleton 695-698", sdd_same != F(1, 4), True)
    # Secant/midpoint identity and the two-point-data→structure identity.
    print()
    for lam, x, h in ((F(2), F(0), F(1, 2)), (F(5), F(-2), F(1, 4)), (F(3), F(1), F(2))):
        check("secSlope(%s,%s,%s) = qTransfer at the midpoint" % (fmt(lam), fmt(x), fmt(h)),
              "plan §8.1 qSecSlope_eq_qTransfer_mid",
              qSecSlope(lam, x, h), qTransfer(lam, x + h / 2))
        check("two model points -> alphaObs = coefficient at the data midpoint (%s,%s)"
              % (fmt(lam), fmt(x)), "plan §8.1 qAlphaObs_eq_qTransfer_mid",
              qAlphaObs(x, qEact(lam, x), x + h, qEact(lam, x + h)),
              qTransfer(lam, (x + (x + h)) / 2))
        check("two-point solver recovers lam (%s,%s)" % (fmt(lam), fmt(x)),
              "plan §8.1 qLamOfPair_reconstructs",
              qLamOfPair(x, qEact(lam, x), x + h, qEact(lam, x + h)), lam)
    # Cascade branch order: exhaustiveness of the six arms and guard-level priority.
    print()
    print("  cascade branch order (skeleton 601–608): guard priority and exhaustiveness.")
    print("  %-16s %-10s %-14s %-14s" % ("(lam,x)", "verdict", "alpha", "alpha-class"))
    line()
    grid = [(F(2), F(0)), (F(2), F(1)), (F(2), F(-1)), (F(2), F(2)), (F(2), F(-2)),
            (F(2), F(3)), (F(2), F(-3)), (F(0), F(0)), (F(0), F(5)), (F(-2), F(-2)),
            (F(-2), F(0)), (F(1), F(-1)), (F(1, 2), F(1, 4))]
    for lam, x in grid:
        v = epQVerdict(lam, x)
        if lam <= 0:
            cls = "not a model point (lam ≤ 0)"
        else:
            a = qTransfer(lam, x)
            if x == lam or x == -lam:
                cls = "boundary arm (alpha = 0 or 1)"
            elif 0 < a < 1:
                cls = "0 < alpha < 1"
            elif 1 < a:
                cls = "1 < alpha"
            else:
                cls = "alpha < 0"
        print("  %-16s %-10s %-14s %-14s"
              % ("(%s,%s)" % (fmt(lam), fmt(x)), v, fmt(qTransfer(lam, x)) if lam != 0 else "-",
                 cls))
    check("cascade guard order: degenerate wins over every x-arm", "skeleton 601-608",
          epQVerdict(F(0), F(0)), DEGENERATE)
    check("cascade guard order: unphysical wins over the boundary arms", "skeleton 601-608",
          epQVerdict(F(-2), F(-2)), UNPHYSICAL)
    check("cascade guard order: x = +lam is boundary, alpha = 0", "skeleton 604",
          (epQVerdict(F(2), F(2)), qTransfer(F(2), F(2))), (BOUNDARY, F(0)))
    check("cascade guard order: x = -lam is boundary, alpha = 1", "skeleton 605",
          (epQVerdict(F(2), F(-2)), qTransfer(F(2), F(-2))), (BOUNDARY, F(1)))
    for lam, x in grid:
        if lam <= 0:
            continue
        a = qTransfer(lam, x)
        want = (BOUNDARY if (x == lam or x == -lam)
                else CONFORMING if 0 < a < 1
                else SUPERLINEAR if 1 < a else SUBLINEAR)
        check("cascade agrees with the alpha-classification at (lam,x)=(%s,%s)"
              % (fmt(lam), fmt(x)), "plan §8.2 (branch order); skeleton 601-608",
              epQVerdict(lam, x), want)
    check("alpha = 0 iff x = +lam (the boundary arms consume both ends of the band)",
          "plan §8.2", [x for x in (F(-3), F(-1), F(0), F(1), F(2), F(3))
                        if qTransfer(F(2), x) == 0], [F(2)])
    check("alpha = 1 iff x = -lam", "plan §8.2",
          [x for x in (F(-3), F(-2), F(-1), F(0), F(1)) if qTransfer(F(2), x) == 1], [F(-2)])


# ────────────────────────────────────────────────────────────────────────────────────────
# [8] Literature families: per-family recomputation of alphaObs, lamOfPair, sdd, verdicts.
# ────────────────────────────────────────────────────────────────────────────────────────

def family_recompute(fam):
    """Return the recomputed quantities for one §R1.10 family (exact ℚ, kcal/mol)."""
    spec = LIT_INSTANCES[fam.fid]
    ap1, ap2 = spec["alpha_pair"]
    lp1, lp2 = spec["lam_pair"]
    t1, t2, t3 = spec["triple"]
    (x1, e1), (x2, e2) = row_named(fam, ap1), row_named(fam, ap2)
    (u1, f1), (u2, f2) = row_named(fam, lp1), row_named(fam, lp2)
    a3 = row_named(fam, t1)
    b3 = row_named(fam, t2)
    c3 = row_named(fam, t3)
    obs = qAlphaObs(x1, e1, x2, e2)
    lam_hat = qLamOfPair(u1, f1, u2, f2)
    sdd = qSecondDividedDiff(a3[0], a3[1], b3[0], b3[1], c3[0], c3[1])
    # The three pairwise solvers on the designated triple: if those three points were model
    # data at one λ ≠ 0, each of them would have to return that λ.
    pair_solvers = [
        (("%s/%s" % (t1, t2)), qLamOfPair(a3[0], a3[1], b3[0], b3[1]),
         (2 * (b3[0] - a3[0]) - 4 * (a3[1] - b3[1]))),
        (("%s/%s" % (t2, t3)), qLamOfPair(b3[0], b3[1], c3[0], c3[1]),
         (2 * (c3[0] - b3[0]) - 4 * (b3[1] - c3[1]))),
        (("%s/%s" % (t1, t3)), qLamOfPair(a3[0], a3[1], c3[0], c3[1]),
         (2 * (c3[0] - a3[0]) - 4 * (a3[1] - c3[1]))),
    ]
    fam_lam = fam.aggregates.get("mean")
    v_pair_all = [epQVerdict(lam_hat, x) if lam_hat != 0 else "-"
                  for _n, x, _e in fam.points()]
    v_fam_all = ([epQVerdict(fam_lam, x) for _n, x, _e in fam.points()]
                 if fam_lam not in (None, F(0)) else [])
    return dict(spec=spec, obs=obs, lam_hat=lam_hat, sdd=sdd, pair_solvers=pair_solvers,
                alpha_pair=(ap1, ap2, x1, e1, x2, e2), lam_pair=(lp1, lp2, u1, f1, u2, f2),
                triple=(t1, t2, t3, a3, b3, c3), fam_lam=fam_lam,
                v_pair_all=v_pair_all, v_fam_all=v_fam_all)


def check_literature_families():
    section("[4] literature families of §R1.10 — per-family recomputation (unit: %s)" % UNIT)
    for fam in FAMILIES:
        if fam.fid == "F4":
            continue
        r = family_recompute(fam)
        spec = r["spec"]
        print()
        line("-")
        print("%s — %s   [%s; locus %s; provenance flag %s]"
              % (fam.fid, fam.label, r["spec"]["loci"], fam.locus, fam.status))
        print("  unit: all numbers below are the source's printed %s values." % UNIT)
        ap1, ap2, x1, e1, x2, e2 = r["alpha_pair"]
        print("  alphaObs over the family's leading documented pair (%s → %s)   [dimensionless: "
              "%s ÷ %s]:" % (ap1, ap2, UNIT, UNIT))
        print("      (ea₁ - ea₂)/(x₂ - x₁) = (%s - %s)/(%s - %s) = %s"
              % (fmt(e1), fmt(e2), fmt(x2), fmt(x1), fmt(r["obs"])))
        lp1, lp2, u1, f1, u2, f2 = r["lam_pair"]
        print("  lamOfPair over the designated adjacent pair (%s → %s)   [%s]:"
              % (lp1, lp2, UNIT))
        print("      (x₂² - x₁²)/(2(x₂-x₁) - 4(ea₁-ea₂)) = %s %s"
              % (fmt(r["lam_hat"]), UNIT))
        t1, t2, t3, a3, b3, c3 = r["triple"]
        print("  second divided difference of the three designated rows   [%s]:"
              % SDD_UNIT)
        for nm, (xx, ee) in ((t1, a3), (t2, b3), (t3, c3)):
            print("      %-7s x = %-18s %s   e = %-18s %s"
                  % (nm, fmt(xx), UNIT, fmt(ee), UNIT))
        print("      sdd = %s %s   (sign %s)"
              % (fmt(r["sdd"]), SDD_UNIT,
                 "+" if r["sdd"] > 0 else ("-" if r["sdd"] < 0 else "0")))
        print("      in the model this must equal 1/(4λ) > 0 for every λ > 0 (%s): the"
              % SDD_UNIT)
        print("      measured sign is '%s', so no positive λ reproduces these three rows."
              % ("+" if r["sdd"] > 0 else "-"))
        print("  pair solvers on the same three rows (model data at one λ would give one value):")
        vals = []
        for name, val, den in r["pair_solvers"]:
            vals.append(val)
            print("      %-14s lamOfPair = %-24s %s   (denominator %s)"
                  % (name, fmt(val) if den != 0 else "n/a (denominator 0)",
                     UNIT, fmt(den)))
        print("      pairwise consistency: %s" % ("AGREE" if len(set(vals)) == 1
                                                 else "DISAGREE -> no λ ≠ 0 reproduces all three"))
        # Per-point cascade verdicts, at both λ readings available for these data.
        fam_lam = r["fam_lam"]
        print("  per-point cascade verdicts (x = model driving force, %s):" % UNIT)
        print("      %-7s %20s %20s %-30s %-30s"
              % ("row", "x", "barrier", "verdict at λ̂(pair)=%s" % fmt(r["lam_hat"]),
                 "verdict at λ̂(family)=%s" % fmt(fam_lam)))
        for name, x, e in fam.points():
            if r["lam_hat"] != 0:
                v_pair = "%s (α=%s)" % (epQVerdict(r["lam_hat"], x),
                                        fmt(qTransfer(r["lam_hat"], x)))
            else:
                v_pair = "-"
            if fam_lam not in (None, F(0)):
                v_fam = "%s (α=%s)" % (epQVerdict(fam_lam, x), fmt(qTransfer(fam_lam, x)))
            else:
                v_fam = "-"
            print("      %-7s %20s %20s %-30s %-30s"
                  % (name, fmt(x), fmt(e), v_pair, v_fam))
        check("%s alphaObs" % fam.fid, spec["loci"], r["obs"], spec["alpha"])
        check("%s lamOfPair" % fam.fid, spec["loci"], r["lam_hat"], spec["lam_hat"])
        check("%s second divided difference" % fam.fid, spec["loci"], r["sdd"], spec["sdd"])
        check("%s sdd < 0 (model with λ > 0 forces sdd = 1/(4λ) > 0)" % fam.fid,
              "plan §8.2 I11/I12; LITERATURE.md §R1.10.6", r["sdd"] < 0, True)
        check("%s 0 < alphaObs < 1 (the affine/BEP side conforms)" % fam.fid,
              "plan §8.2 I12; skeleton 964-976", (0 < r["obs"] < 1), True)
        check("%s no λ ∈ ℚ is model-consistent with the three rows (pairwise solver "
              "disagreement, and sdd < 0 for λ > 0)" % fam.fid,
              "plan §8.2 I11/I12; skeleton 888/908/928/953",
              (len(set(vals)) > 1) and r["sdd"] < 0, True)
        check("%s no printed barrier is zero, so λ = 0 is excluded as well (at λ = 0 the "
              "model forces every qEact 0 x = 0)" % fam.fid, "plan §8.2 I11; skeleton 833",
              all(e != 0 for _n, _x, e in fam.points()), True)
        for name, val, den in r["pair_solvers"]:
            if den != 0 and val <= 0:
                check("%s pair %s admits no λ > 0 (weaker per-pair test)" % (fam.fid, name),
                      "LITERATURE.md §R1.10.6", val <= 0, True)


# ────────────────────────────────────────────────────────────────────────────────────────
# [9] Soft audit of the literature record itself.
# ────────────────────────────────────────────────────────────────────────────────────────

def round1(v):
    """Round a Fraction to one decimal, half away from zero (the record's printed format)."""
    n = v * 10
    if n >= 0:
        q = (2 * n.numerator + n.denominator) // (2 * n.denominator)
    else:
        m = -n
        q = -((2 * m.numerator + m.denominator) // (2 * m.denominator))
    return F(q, 10)


def larger_root(x, ea):
    """The larger root of the model quadratic `λ² - (2x + 4Ea)λ + x² = 0` (the record's λ̂),
    bracketed by bisection in exact rational arithmetic; `None` if the pair admits no real λ.
    The roots are `(x + 2Ea) ± 2√(Ea(Ea + x))`, so the vertex of the upward parabola sits
    exactly at their midpoint `x + 2Ea`."""
    vertex = x + 2 * ea

    def f(lam):
        return lam * lam - (2 * x + 4 * ea) * lam + x * x

    if f(vertex) > 0:
        return None                      # no real root: the pair admits no λ at all
    lo, hi = vertex, vertex + 1
    while f(hi) <= 0 and hi - vertex < 10 ** 6:
        hi = vertex + 2 * (hi - vertex)
    if f(hi) <= 0:
        return None
    for _ in range(120):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2


def audit_literature():
    section("[5] AUDIT of LITERATURE.md §R1.10 itself (soft: findings about the record, "
            "not about the Lean layer)")
    # (a) kJ/mol cells = 4.184 × kcal/mol, rounded to 1 decimal.
    bad_kj = []
    for fam in FAMILIES:
        for n, dG0, ea, kjd, kje in fam.rows:
            if kjd is not None and round1(dG0 * KG) != kjd:
                bad_kj.append("%s %s ΔG°: 4.184 × %s = %s ≠ printed %s"
                              % (fam.fid, n, fmt(dG0), fmt(round1(dG0 * KG)), fmt(kjd)))
            if ea is not None and kje is not None and round1(ea * KG) != kje:
                bad_kj.append("%s %s barrier: 4.184 × %s = %s ≠ printed %s"
                              % (fam.fid, n, fmt(ea), fmt(round1(ea * KG)), fmt(kje)))
    audit(not bad_kj, "unit arithmetic: every printed kJ/mol cell equals 4.184 × the printed "
                      "%s cell rounded to 1 decimal (%s)"
          % (UNIT, "OK" if not bad_kj else "; ".join(bad_kj)))
    # (b) printed per-row λ̂ must be the larger root of λ² - (2x + 4Ea)λ + x² = 0 within the
    #     printed precision (one decimal).
    bad_lam = []
    for fam in FAMILIES:
        printed = fam.aggregates.get("printed_lam_hat", {})
        for name, printed_lam in printed.items():
            x, ea = row_named(fam, name)
            root = larger_root(x, ea)
            if root is None:
                bad_lam.append("%s %s: the printed pair admits no real λ at all" % (fam.fid, name))
            elif abs(printed_lam - root) > F(1, 20):
                bad_lam.append("%s %s: printed λ̂ = %s is not the larger root of "
                               "λ² - (2x + 4Ea)λ + x² = 0 — recomputed root ≈ %s %s "
                               "(difference %s, beyond the ±0.05 of a one-decimal cell)"
                               % (fam.fid, name, fmt(printed_lam), near(root), UNIT,
                                  near(abs(printed_lam - root), 3)))
    audit(not bad_lam, "printed per-row λ̂ cells are the larger root of the model quadratic "
                       "λ² - (2x + 4Ea)λ + x² = 0 to one decimal%s"
          % (" (all printed rows of F1, F2, F5)" if not bad_lam else ": " + "; ".join(bad_lam)))
    # (c) aggregates that are recomputable from the printed rows (F5 prints all rows).
    for fam in FAMILIES:
        agg = fam.aggregates
        if not agg or not fam.rows or fam.fid != "F5":
            continue
        roots = []
        for n, dG0, ea, _kjd, _kje in fam.rows:
            if ea is None:
                continue
            root = larger_root(-dG0, ea)
            if root is not None:
                roots.append(root)
        mean = sum(roots) / len(roots)
        rng = (min(roots), max(roots))
        audit(abs(mean - agg["mean"]) < F(1, 20),
              "F5 family mean λ̂: recomputed ≈%s vs printed %s (%s)"
              % (near(mean), fmt(agg["mean"]), "OK" if abs(mean - agg["mean"]) < F(1, 20)
                 else "MISMATCH"))
        audit(all(abs(a - b) < F(1, 20) for a, b in zip(rng, agg["range"])),
              "F5 λ̂ range: recomputed ≈%s–%s vs printed %s–%s"
              % (near(rng[0], 3), near(rng[1], 3), fmt(agg["range"][0]), fmt(agg["range"][1])))
    # (d) the curvature -> λ conversion, and the factor-2 label question.
    for fam in FAMILIES:
        agg = fam.aggregates
        if not agg or agg.get("curvature") is None:
            continue
        c = agg["curvature"]
        lam_quad = 1 / (4 * c)           # curvature read as the quadratic coefficient (1/(4λ))
        lam_2nd = 1 / (2 * c)            # curvature read as the literal second derivative (1/(2λ))
        printed = agg["lam_from_curvature"]
        rel = abs(lam_quad - printed) / abs(printed)
        audit(rel <= F(2, 100),
              "%s curvature → λ: the printed λ = %s is reproduced by the quadratic-coefficient "
              "convention λ = 1/(4·curvature) = %s (relative difference %.3f%%, within the two "
              "significant digits of the printed curvature); the literal second-derivative "
              "reading λ = 1/(2·curvature) = %s is off by a factor 2 — §R1.10.1's prose writes "
              "d²Ea/dx² = 1/(2λ), while the record's own λ arithmetic (and the Lean "
              "`qSecondDividedDiff = 1/(4λ)`) uses the quadratic-coefficient convention. The "
              "verdict (negative curvature ⇒ no positive λ) is insensitive to the factor."
              % (fam.fid, fmt(printed), near(lam_quad, 3), float(rel) * 100, near(lam_2nd, 3)))
    # (e) subset coverage: which family aggregates are recomputable from the printed rows.
    for fam in FAMILIES:
        if not fam.aggregates:
            continue
        n_printed = len(fam.points())
        n_family = fam.aggregates.get("n")
        if n_printed != n_family:
            audit(True, "%s aggregates (mean %s, sd %s, curvature %s, fit %s, R² %s) are over "
                        "n = %s pairs, but only %d rows are printed -> the aggregate cells are "
                        "NOT recomputable from this record's printed data (declared UNSUPPORTED "
                        "below, not guessed)"
                  % (fam.fid, fmt(fam.aggregates.get("mean")),
                     fmt(fam.aggregates.get("sd")), fmt(fam.aggregates.get("curvature")),
                     fam.aggregates.get("fit"), fmt(fam.aggregates.get("r2")),
                     n_family, n_printed))
    # (f) pair-solver stability on the printed subset (why `lamHat` is a pair, not a family).
    for fam in FAMILIES:
        if fam.fid == "F4":
            continue
        pts = fam.points()
        vals = []
        for (n1, x1, e1), (n2, x2, e2) in zip(pts, pts[1:]):
            vals.append((("%s/%s" % (n1, n2)), qLamOfPair(x1, e1, x2, e2)))
        spread = ", ".join("%s: %s" % (k, fmt(v)) for k, v in vals)
        audit(True, "%s adjacent-pair solvers on the printed subset (unit %s) — %s ; the value "
                    "is a property of the pair, not of the family, so a Lean `_lamHat` row must "
                    "not be read as a measured reorganization energy"
              % (fam.fid, UNIT, spread))
    print()
    for sev, text in AUDITS:
        print("  %-10s %s" % (sev, text))
    bad = [t for s, t in AUDITS if s == "AUDIT-FAIL"]
    print()
    if bad:
        print("  %d AUDIT-FAIL finding(s) about LITERATURE.md — reported to the lead; they do "
              "not change the exit code." % len(bad))
    else:
        print("  no AUDIT-FAIL finding: the printed §R1.10 cells audited here are internally "
              "consistent.")


# The record's printed per-row λ̂ columns (F1, F2, F5 print them; F3/F4 print aggregates only).
F1.aggregates["printed_lam_hat"] = {
    "16(2)": F("63.0"), "16(1)": F("64.6"), "19(2)": F("65.3"), "14(1)": F("67.3"),
    "12": F("65.0"), "2": F("62.3"), "7": F("53.5"), "8": F("58.1"),
}
F2.aggregates["printed_lam_hat"] = {
    "16(2)": F("54.0"), "13": F("57.5"), "19(2)": F("52.0"), "2": F("48.8"),
    "1": F("48.2"), "8": F("50.7"), "10": F("44.4"),
}
F5.aggregates["printed_lam_hat"] = {
    # round 1j: R4 and R5 were AUDIT-FAILed by this script (the record had the wrong sign
    # orientation for those two rows) and are superseded by the recomputed roots; all five
    # entries below are the record's current cells, checked against the exact roots (±0.05).
    "R2": F("32.493"), "R3": F("39.645"), "R4": F("34.640"), "R1": F("44.007"),
    "R5": F("36.468"),
}


# ────────────────────────────────────────────────────────────────────────────────────────
# [10] UNSUPPORTED families and the final machine-readable table.
# ────────────────────────────────────────────────────────────────────────────────────────

def unsupported():
    section("[6] UNSUPPORTED — families for which no number may be asserted by "
            "Instances.lean")
    print("Printed only to keep the instance layer honest: this script refuses to invent a")
    print("per-point row for these families, so no statement of the B5b block can be built on")
    print("them. Reasons are quoted from LITERATURE.md §R1.10.3/§R1.10.4/§R1.10.7.")
    print()
    agg = F4
    print("UNSUPPORTED  %s — %s" % (agg.fid, agg.label))
    print("             locus : %s ; status %s ; unit %s" % (agg.locus, agg.status, UNIT))
    print("             data  : aggregate-only — %s"
          % "; ".join("%s = %s" % (k, fmt(v)) for k, v in sorted(agg.aggregates.items())
                      if k != "printed_lam_hat"))
    print("             reason: %s" % " ".join(agg.notes))
    print("             -> no per-point (x, Ea) pair exists in §R1.10 for this family; "
          "alphaObs / lamOfPair / sdd are NOT computed.")
    for name, reason in UNFILLED:
        print()
        print("UNSUPPORTED  %s" % name)
        print("             reason: %s" % reason)
    print()
    print("UNSUPPORTED  family aggregates of F1/F2/F3 — mean λ̂, sd, λ̂ range, fitted")
    print("             curvature, linear fit and R² are quoted over n = 31/34/31 pairs while")
    print("             only 8/7/4 of them carry a printed barrier; not recomputable from the")
    print("             printed data (F1 prints 9 rows, of which 8 have a water barrier; F3")
    print("             prints 5, of which 4 have one).")
    print("             (F5 is the exception: all n = 5 rows are printed, and its mean and range")
    print("             are recomputed and audited in section [5].)")


def table():
    section("[7] machine-readable table (paste into theories/BEP/RESULTS.md)")

    def compact(v):
        """Exact form only (`n/d`), so the table stays narrow and paste-able."""
        if isinstance(v, F):
            return "%d" % v.numerator if v.denominator == 1 else "%s" % v
        return str(v)

    print("# unit: %s for every literature number; I* rows are unitless rational model inputs" % UNIT)
    print("# provenance flags: model-constructed (plan §8.2) | literature (LITERATURE.md "
          "§R1.10, status flag in the last column)")
    print("# 'sdd-sign' is the sign of the second divided difference of the three printed rows")
    print("# (model-constructed rows use x, x+1/2, x+1); the model with λ > 0 forces '+'.")
    print("# literature 'verdict' = cascade verdict of every printed point at the family λ̂ of")
    print("# §R1.10; model 'verdict' = cascade verdict at (λ, x).")
    hdr = ("family", "alphaObs", "lamOfPair", "sdd-sign", "verdict", "provenance flag")
    rows = []
    for (iid, label, lam, x, verdict, alpha, windows, loci) in MODEL_INSTANCES:
        if x is None:
            rows.append(("%s %s (lam=%s, w=%s; tol %s ok / %s fails)"
                         % (iid, label, compact(lam), compact(I10_W),
                            compact(I10_TOL_TRUE), compact(I10_TOL_FALSE)),
                         "-", "-", "-",
                         "conforms@%s, fails@%s" % (compact(I10_TOL_TRUE),
                                                    compact(I10_TOL_FALSE)),
                         "model-constructed (plan §8.2)"))
            continue
        pts = [(xx, qEact(lam, xx)) for xx in (x, x + MODEL_H, x + 2 * MODEL_H)]
        obs = qAlphaObs(pts[0][0], pts[0][1], pts[1][0], pts[1][1])
        lam_hat = qLamOfPair(pts[0][0], pts[0][1], pts[1][0], pts[1][1])
        sdd = qSecondDividedDiff(pts[0][0], pts[0][1], pts[1][0], pts[1][1],
                                 pts[2][0], pts[2][1])
        rows.append(("%s %s (lam=%s, x=%s)" % (iid, label, compact(lam), compact(x)),
                     compact(obs),
                     compact(lam_hat) + (" (= lam)" if lam_hat == lam else " (!= lam)"),
                     "+" if sdd > 0 else ("-" if sdd < 0 else "0"),
                     verdict, "model-constructed (plan §8.2)"))
    for fam in FAMILIES:
        if fam.fid == "F4":
            rows.append(("%s %s — AGGREGATE-ONLY" % (fam.fid, fam.short), "UNSUPPORTED",
                         "UNSUPPORTED", "UNSUPPORTED", "UNSUPPORTED",
                         "UNSUPPORTED (literature, %s, no per-point pairs)" % fam.status))
            continue
        r = family_recompute(fam)
        sig = "+" if r["sdd"] > 0 else ("-" if r["sdd"] < 0 else "0")
        per = {}
        for v in r["v_fam_all"]:
            per[v] = per.get(v, 0) + 1
        verdict = "@lamFam %s: %s" % (compact(r["fam_lam"]),
                                      ", ".join("%s x%d" % (k, v)
                                                for k, v in sorted(per.items())))
        rows.append(("%s %s (%d printed rows)" % (fam.fid, fam.short, len(fam.points())),
                     compact(r["obs"]), compact(r["lam_hat"]), sig, verdict,
                     "literature (LITERATURE.md %s, status %s)"
                     % (fam.locus.split(",")[0], fam.status)))
    w = [max(len(str(r[i])) for r in rows + [hdr]) for i in range(6)]
    print(" | ".join(h.ljust(w[i]) for i, h in enumerate(hdr)))
    print("-+-".join("-" * w[i] for i in range(6)))
    for r in rows:
        print(" | ".join(str(r[i]).ljust(w[i]) for i in range(6)))
    print()
    print("# reading of the literature rows: 'alphaObs' (dimensionless) is the observable two-point")
    print("# slope over the family's leading documented pair as named in that family's heading (NOT the")
    print("# abscissa-widest pair); 'lamOfPair' is the designated adjacent-pair solver (kcal/mol); the")
    print("# 'verdict' column classifies every printed point at the family λ̂ of §R1.10 (the")
    print("# κ = 1/(4λ) reading), and 'sdd-sign' '-' is the λ-independent refutation: the model")
    print("# with λ > 0 forces '+'.  F1–F3 and F5 pass the affine test and fail the curvature")
    print("# test, which is the I12 statement; F4 has no per-point data and stays UNSUPPORTED.")


# ────────────────────────────────────────────────────────────────────────────────────────
# main
# ────────────────────────────────────────────────────────────────────────────────────────

def main():
    print("BEP instance cross-check — non-Lean, independent recomputation "
          "(exact rational arithmetic)")
    print("sources: theories/BEP/LITERATURE.md §R1.10 (data, unit %s); " % UNIT)
    print("         theories/BEP/plan.md §8.1/§8.2 (model + instance table);")
    print("         theories/BEP/probes/bep-statement-skeleton.lean (B5a/B5b block, "
          "branch order copied verbatim)")
    print("this script does NOT replace the kernel: it is an independent evidence chain, "
          "the gate is build + strict scan + #print axioms")
    dump_data()
    readback_literature()
    check_model_instances()
    check_model_identities()
    check_literature_families()
    audit_literature()
    unsupported()
    table()

    section("[8] comparison with the Lean-side values (plan §8.2 + skeleton B5b)")
    print("checked %d Lean-side values against the recomputation." % CHECKS[0])
    if FAILURES:
        print()
        print("DISAGREEMENTS (%d) — recomputed vs Lean-side:" % len(FAILURES))
        for cid, source, got, want in FAILURES:
            line("!")
            print("FAIL  %s" % cid)
            print("      recomputed (from LITERATURE.md §R1.10 / the plan's rationals): %s"
                  % fmt(got))
            print("      Lean-side  (%s): %s" % (source, fmt(want)))
    else:
        print("no disagreement: every checked value follows from the recomputation.")
    print()
    bad_audits = [(s, t) for s, t in AUDITS if s == "AUDIT-FAIL"]
    print("AUDIT summary (details in section [5]; soft, they do not change the exit code):")
    print("  %d audit check(s), %d AUDIT-FAIL finding(s) about LITERATURE.md."
          % (len(AUDITS), len(bad_audits)))
    for _s, text in bad_audits:
        print("    AUDIT-FAIL %s" % text)
    print()
    if FAILURES:
        print("CROSS-CHECK: FAILED — %d disagreement(s) with the Lean side." % len(FAILURES))
        return 1
    print("CROSS-CHECK: OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
