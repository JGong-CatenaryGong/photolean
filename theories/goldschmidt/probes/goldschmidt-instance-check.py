#!/usr/bin/env python3
"""Kernel-independent exact-rational cross-check of the Goldschmidt instance rows (lead-owned).

Usage: python3 theories/goldschmidt/probes/goldschmidt-instance-check.py [--theory goldschmidt]
Exit code: 0 = every asserted number reproduced with exact rational arithmetic;
           1 = a mismatch (the offending row is printed).

Why this exists: the instance layer's verdicts are `norm_num` facts written by hand from printed
radii. A mis-scaled decimal (1.44 typed as 144/100 instead of 36/25, a band edge inverted, a radius
rule read against the wrong reference radius) types a *wrong verdict* that still compiles. This
script recomputes every asserted verdict in `fractions.Fraction` -- no floats anywhere on the
decision path, no `Real.sqrt` -- so a label or direction invert is caught BEFORE the kernel meets
the row. The theory is `√2`-free by construction: since the tolerance factor is nonnegative,
`t <= hi` is exactly `t^2 <= hi^2`, and `t^2 = (rA + rO)^2 / (2 * (rB + rO)^2)` is rational.

This is the goldschmidt analogue of `theories/BEP/probes/bep-instance-check.py`.
"""
import sys
from fractions import Fraction as F

# ── printed radii (Shannon 1976; provenance in theories/goldschmidt/LITERATURE.md) ──────────────
rO = F(7, 5)          # 1.40 Å
rA_Sr = F(36, 25)     # 1.44 Å, Sr2+ XII
rA_Ca = F(67, 50)     # 1.34 Å, Ca2+ XII
rA_Ba = F(161, 100)   # 1.61 Å, Ba2+ XII
rA_Cs = F(47, 25)     # 1.88 Å, Cs+ XII
rA_La = F(34, 25)     # 1.36 Å, La3+ XII
rA_Na = F(139, 100)   # 1.39 Å, Na+ XII
rB_Ti = F(121, 200)   # 0.605 Å, Ti4+ VI
rB_Mn = F(129, 200)   # 0.645 Å, Mn3+ VI high spin
rB_Nb = F(16, 25)     # 0.64 Å, Nb5+ VI
rB_Ni = F(12, 25)     # 0.48 Å, Ni4+ VI

# ── band conventions (parameters of the theory, never hard-coded in a definition) ───────────────
classicLo, classicHi = F(4, 5), F(1)
tetragonalHi = F(11, 10)
symmetricLo, symmetricHi = F(49, 50), F(51, 50)
tau = F(3, 20)        # the printed "15 %" figure

fail = []


def t2(rA, rB):
    """Exact square of the tolerance factor."""
    return (rA + rO) ** 2 / (2 * (rB + rO) ** 2)


def in_band(lo, hi, rA, rB):
    """Exact band verdict: t in [lo, hi] with 0 <= lo <= hi (squared comparison, both sides >= 0)."""
    assert lo >= 0 and hi >= 0, "squared comparison needs nonnegative band edges"
    s = t2(rA, rB)
    return lo ** 2 <= s <= hi ** 2


def radius_match(r, rp):
    """Goldschmidt's radius rule with reference radius r: |r - r'| <= tau * r."""
    return abs(r - rp) <= tau * r


def radius_window(r, rp):
    """The rational form of the radius window: 17 r <= 20 r' <= 23 r."""
    return 17 * r <= 20 * rp and 20 * rp <= 23 * r


def check(row, got, want):
    ok = got == want
    print(f"  [{'ok ' if ok else 'FAIL'}] {row}: got {got}, want {want}")
    if not ok:
        fail.append(row)


def sqrt_approx(x):
    """Information only (never on a decision path): a float sqrt for the printed t value."""
    return x ** F(1, 2).__float__() if x >= 0 else float('nan')


print("== exact rational cross-check of the Goldschmidt instance rows ==")
print(f"  rO = {rO}, tau = {tau}")
print("\n-- I2/I3/I4: band verdicts (Shannon radii) --")
rows = [
    ("SrTiO3", rA_Sr, rB_Ti),
    ("CaTiO3", rA_Ca, rB_Ti),
    ("BaTiO3", rA_Ba, rB_Ti),
    ("LaMnO3", rA_La, rB_Mn),
    ("NaNbO3", rA_Na, rB_Nb),
    ("BaNiO3", rA_Ba, rB_Ni),
]
for name, rA, rB in rows:
    s = t2(rA, rB)
    t = sqrt_approx(s)
    print(f"  {name}: rA+rO = {rA + rO}, rB+rO = {rB + rO}, t^2 = {s} (t ~ {t:.6f}), "
          f"t vs 1: {'>' if s > 1 else ('=' if s == 1 else '<')}")

print("\n-- asserted verdicts --")
check("inst_SrTiO3_tooLarge_classic (not in [4/5,1])", in_band(classicLo, classicHi, rA_Sr, rB_Ti), False)
check("inst_SrTiO3_conforms_symmetric (in [49/50,51/50])", in_band(symmetricLo, symmetricHi, rA_Sr, rB_Ti), True)
check("inst_CaTiO3_classic", in_band(classicLo, classicHi, rA_Ca, rB_Ti), True)
check("inst_BaTiO3_not_classic", in_band(classicLo, classicHi, rA_Ba, rB_Ti), False)
check("inst_BaTiO3_conforms_tetragonal (in [1,11/10])", in_band(classicHi, tetragonalHi, rA_Ba, rB_Ti), True)
check("inst_LaMnO3_classic", in_band(classicLo, classicHi, rA_La, rB_Mn), True)
check("inst_NaNbO3_classic", in_band(classicLo, classicHi, rA_Na, rB_Nb), True)
check("inst_BaNiO3_not_tetragonal", in_band(classicHi, tetragonalHi, rA_Ba, rB_Ni), False)
check("inst_radius_ok_but_band_lost (Ca radius-close to Sr)",
      radius_match(rA_Ca, rA_Sr), True)
check("inst_radius_ok_but_band_lost (Sr still not classic)",
      in_band(classicLo, classicHi, rA_Sr, rB_Ti), False)

print("\n-- I5: radius rule (tau = 3/20), window form must agree with the abs form --")
check("inst_radius_Sr_Ca", radius_match(rA_Sr, rA_Ca), True)
check("inst_radius_Sr_Ba", radius_match(rA_Sr, rA_Ba), True)
check("inst_radius_Ca_Ba_fails", radius_match(rA_Ca, rA_Ba), False)
check("inst_radius_convention_Ba_Cs (Cs as reference: allowed)", radius_match(rA_Cs, rA_Ba), True)
check("inst_radius_convention_Ba_Cs (Ba as reference: refused)", radius_match(rA_Ba, rA_Cs), False)
for name, r, rp in [("Sr<-Ca", rA_Sr, rA_Ca), ("Sr<-Ba", rA_Sr, rA_Ba), ("Ca<-Ba", rA_Ca, rA_Ba),
                    ("Cs<-Ba", rA_Cs, rA_Ba), ("Ba<-Cs", rA_Ba, rA_Cs)]:
    check(f"window form agrees with the abs form ({name})",
          radius_window(r, rp), radius_match(r, rp))
check("ratchet: (1+tau)^2 - 1 = 129/400", (1 + tau) ** 2 - 1, F(129, 400))

print("\n-- I6: charge rule (integer increments; (+1, -1) is the coupled pair) --")
check("inst_charge_coupled sum", 1 + (-1), 0)
check("inst_charge_single_fails (a lone +1 is NOT balanced)", (1 == 0), False)
check("a non-compensated pair (+1,+1) is refused", (1 + 1 == 0), False)
check("the coupled pair (+1,-1) is balanced", (1 + (-1) == 0), True)

print("\n-- I7: chemical rule (chiTol = 3/20 - (1/10)|dchi|, reference radius rA_Ca, rA' = 1.53) --")
rAi = F(153, 100)
chi0 = tau - F(1, 10) * abs(F(0) - F(0))
chi1 = tau - F(1, 10) * abs(F(3, 2) - F(0))
print(f"  chiTol(same chi) = {chi0}, chiTol(|dchi| = 3/2) = {chi1}")
check("inst_chi_load_bearing (close chi: allowed)", abs(rA_Ca - rAi) <= chi0 * rA_Ca, True)
check("inst_chi_load_bearing (far chi: refused)", abs(rA_Ca - rAi) <= chi1 * rA_Ca, False)

print("\n-- model rows --")
check("inst_rA_eq_rB_tolFac (t = 1/sqrt 2 at rA = rB = rO = 1)", t2(F(1), F(1)) * 2, 1)
check("inst_ideal_row_classic (t = 1 lies in [4/5,1])", F(4, 5) ** 2 <= 1 <= 1 ** 2, True)
# the three concrete witnesses of G4 use rB = rO = 1, so t^2 = (rA + 1)^2 / 8
def t2_unit(rA):
    return (rA + 1) ** 2 / 8
check("witness_tooSmall (t = 0 at rA = -1, rB = rO = 1)", t2_unit(F(-1)), 0)
check("witness_tooLarge (t = sqrt 2 at rA = 3, rB = rO = 1)", t2_unit(F(3)), 2)
check("witness_inverted_band (t = sqrt(1/8) at rA = 0, rB = rO = 1)", t2_unit(F(0)), F(1, 8))
# witness_ideal_packing is an ℝ row (its A radius is irrational) and is cross-checked by the
# identity t = 1 <=> rA + rO = sqrt 2 * (rB + rO) instead of by a rational row.

print("\n== summary ==")
if fail:
    print(f"  MISMATCHES: {len(fail)}")
    for f in fail:
        print(f"    - {f}")
    sys.exit(1)
print("  every asserted number reproduced exactly (0 mismatches)")
sys.exit(0)
