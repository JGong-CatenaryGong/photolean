#!/usr/bin/env python3
"""Non-Lean cross-check of the Kasha theory's mathematics (lead-owned, plan 8.2/11).

Purpose: recompute, in exact rational arithmetic and by a *different* implementation than the Lean
one, every number the Kasha theory states. This is a second, independent evidence path: it cannot
replace the kernel (`proofs/scripts/check.sh --strict` + `axioms.sh`), but it catches statement-level
errors before they reach the kernel, and it makes the instance rows reproducible without Lean.

Usage:  python3 theories/kasha/probes/kasha-instance-check.py [--verbose]
Exit:   0 = every checked equality/verdict holds; 1 = a mismatch (printed).

Model (theories/kasha/plan.md 1.2): level 0 is the lowest excited state; rad n = radiative rate,
ic n = nonradiative rate (internal conversion n -> n-1 for n >= 1, loss to the ground state for
n = 0); decay n = rad n + ic n; radBranch = rad/decay; icBranch = ic/decay;
cascade i N = prod_{j=i+1..N} icBranch j; emitYield i N = radBranch i * cascade i N;
fluoYield N = sum_{i=0..N} emitYield i N; upperYield N = sum_{i=1..N} emitYield i N.
Division is totalised exactly as in Lean (x / 0 = 0).
"""
from fractions import Fraction as F
import math
import random
import sys

VERBOSE = "--verbose" in sys.argv
fails = []


def sdiv(a, b):
    """Totalised division, mirroring Lean's `a / 0 = 0`."""
    return F(0) if b == 0 else a / b


class Ladder:
    """Rate data of a finite ladder; a level outside the list has rate 0."""

    def __init__(self, rad_list, ic_list):
        self.rad = {n: F(r) for n, r in enumerate(rad_list)}
        self.ic = {n: F(i) for n, i in enumerate(ic_list)}

    def r(self, n):
        return self.rad.get(n, F(0))

    def i(self, n):
        return self.ic.get(n, F(0))

    def d(self, n):
        return self.r(n) + self.i(n)

    def rb(self, n):
        return sdiv(self.r(n), self.d(n))

    def ib(self, n):
        return sdiv(self.i(n), self.d(n))

    def cascade(self, i, N):
        p = F(1)
        for j in range(i + 1, N + 1):
            p *= self.ib(j)
        return p

    def emit(self, i, N):
        return self.rb(i) * self.cascade(i, N)

    def fluo(self, N):
        return sum((self.emit(i, N) for i in range(0, N + 1)), F(0))

    def upper(self, N):
        return sum((self.emit(i, N) for i in range(1, N + 1)), F(0))

    def within(self, tol, N):
        return self.upper(N) <= tol * self.fluo(N)

    def funnel_ratio(self):
        return sdiv(self.r(0) * self.i(1), self.r(1) * self.d(0))

    def ladder_ratio(self, N):
        return sdiv(self.r(0) * self.cascade(0, N), self.upper(N) * self.d(0))

    def rate_data(self, N):
        return all(self.d(n) > 0 for n in range(N + 1)) and \
            all(v >= 0 for v in self.rad.values()) and all(v >= 0 for v in self.ic.values())

    def effective(self, N):
        """The effective two-level data of plan 7.1."""
        return Ladder([self.r(0), self.upper(N)], [self.i(0), self.cascade(0, N)])


def check(label, got, want):
    ok = (got == want)
    if not ok:
        fails.append(f"{label}: got {got}, want {want}")
    if VERBOSE or not ok:
        print(f"  [{'ok ' if ok else 'FAIL'}] {label}: {got}" + ("" if ok else f"  (want {want})"))
    return ok


print("== 1. instance rows of the statement authority (K5b, plan 8.2) ==")
L1 = Ladder([1, 1], [0, 100])
L2 = Ladder([1, 1], [0, 10])
L3 = Ladder([1, 1], [0, 99])
L3b = Ladder([1, 1], [0, F(9899, 100)])
Leq = Ladder([1, 1, 1], [1, 1, 1])
L8 = Ladder([1, 1, 1], [0, 0, 0])  # constant rad = 1, ic = 0 (skeleton I8)
check("I1  conforming control   KashaWithin (1/100) 1", L1.within(F(1, 100), 1), True)
check("I2  anti-Kasha control   KashaWithin (1/100) 1", L2.within(F(1, 100), 1), False)
check("I3  threshold boundary   KashaWithin (1/100) 1", L3.within(F(1, 100), 1), True)
check("I3b one unit below       KashaWithin (1/100) 1", L3b.within(F(1, 100), 1), False)
check("I4  fluoYield 1 (L1)", L1.fluo(1), F(1))
check("I5  upperYield 1 (L1)", L1.upper(1), F(1, 101))
check("I6  fluoYield 2 (equal-rates with ic0 = 1)", Leq.fluo(2), F(7, 8))
check("I7  upperYield 2 (equal-rates with ic0 = 1)", Leq.upper(2), F(3, 4))
check("I7b equal-rates violates at tol = 1/2", Leq.within(F(1, 2), 2), False)
check("I8  no-loss ladder: fluoYield 2 = fluoYield 1", L8.fluo(2) == L8.fluo(1), True)
check("I8b no-loss ladder fails KashaRule 1", L8.upper(1) == 0, False)

print("== 2. the sharp thresholds (K3 #1-#3, #10; K4 #9) ==")
for tol in [F(1, 100), F(1, 10), F(1, 2), F(3, 4)]:
    rate_form = L1.r(1) * L1.d(0) * (1 - tol) <= tol * (L1.r(0) * L1.i(1))
    check(f"tol={tol}: two-level criterion == rate form (L1)", L1.within(tol, 1), rate_form)
    check(f"tol={tol}: two-level criterion == ratio form (L1)",
          L1.within(tol, 1), (1 - tol) / tol <= L1.funnel_ratio())
    check(f"tol={tol}: N=2 criterion == ladderRatio form (equal-rates)",
          Leq.within(tol, 2), (1 - tol) / tol <= Leq.ladder_ratio(2))
for tol in [F(1, 100), F(1, 8)]:
    Lw = Ladder([1, tol], [0, 1 - tol])
    check(f"tol={tol}: attainment ladder funnelRatio == (1-tol)/tol",
          Lw.funnel_ratio(), (1 - tol) / tol)
    check(f"tol={tol}: attainment ladder satisfies KashaWithin tol", Lw.within(tol, 1), True)
    check(f"tol={tol}: attainment ladder fails below tol", Lw.within(tol / 2, 1), False)

print("== 3. probability conservation (K2 #6) and the recursions (K2 #4/#5) ==")
random.seed(20260920)
checked_cons = 0
for _ in range(200):
    N = random.randint(0, 4)
    L = Ladder([F(random.randint(0, 6), random.randint(1, 4)) for _ in range(N + 1)],
               [F(random.randint(0, 6), random.randint(1, 4)) for _ in range(N + 1)])
    if not L.rate_data(N):
        continue
    checked_cons += 1
    if L.cascade(0, N) + L.upper(N) != 1:
        fails.append(f"conservation failed at N={N}: {L.cascade(0, N) + L.upper(N)}")
    if L.fluo(N) != 1 - L.ib(0) * L.cascade(0, N):
        fails.append(f"yield = 1 - loss failed at N={N}")
    if L.fluo(N) != L.emit(0, N) + L.upper(N):
        fails.append(f"low + upper failed at N={N}")
    if L.upper(N) > L.fluo(N):
        fails.append(f"leak > total failed at N={N}")
    if L.fluo(N) > 1:
        fails.append(f"yield > 1 failed at N={N}")
    if N >= 1:
        if L.fluo(N) != L.rb(N) + L.ib(N) * L.fluo(N - 1):
            fails.append(f"fluoYield recursion failed at N={N}")
        if L.upper(N) != L.rb(N) + L.ib(N) * L.upper(N - 1):
            fails.append(f"upperYield recursion failed at N={N}")
print(f"  conservation / recursion / bounds: {checked_cons} random ladders, "
      f"{'all ok' if not fails else 'see failures'}")

print("== 4. the effective two-level reduction (K4 #8/#9/#10) ==")
checked_eff = 0
bad_eff = 0
for _ in range(300):
    N = random.randint(1, 4)
    L = Ladder([F(random.randint(0, 6), random.randint(1, 3)) for _ in range(N + 1)],
               [F(random.randint(0, 6), random.randint(1, 3)) for _ in range(N + 1)])
    if not L.rate_data(N):
        continue
    eff = L.effective(N)
    if L.upper(N) + L.cascade(0, N) == 0:
        continue
    for tol in [F(1, 100), F(1, 2), F(1)]:
        checked_eff += 1
        if L.within(tol, N) != eff.within(tol, 1):
            bad_eff += 1
            fails.append(f"effective reduction mismatch: N={N} tol={tol} "
                         f"rad={sorted(L.rad.items())} ic={sorted(L.ic.items())}")
    if eff.funnel_ratio() != L.ladder_ratio(N):
        fails.append(f"ladderRatio != effective funnelRatio at N={N}")
print(f"  effective reduction: {checked_eff} (ladder, tol) pairs checked, {bad_eff} mismatches")

print("== 5. the levelwise-criterion counterexample (K3 #13) ==")
levelwise = all(Leq.r(i) * Leq.d(i - 1) <= Leq.i(i) * Leq.d(i) for i in (1, 2))
check("equal-rates ladder satisfies the levelwise ic >= rad test", levelwise, True)
check("equal-rates ladder nevertheless violates KashaWithin (1/2) 2",
      Leq.within(F(1, 2), 2), False)
check("equal-rates ladder leak fraction (should be 6/7)",
      sdiv(Leq.upper(2), Leq.fluo(2)), F(6, 7))

print("== 6. the Marcus gap bridge (K4 #12/#13/#14) ==")
checked_mar = 0
skipped_mar = 0
for _ in range(400):
    A = F(random.randint(1, 100))
    lam = F(random.randint(1, 20), 2)
    kT = F(random.randint(1, 20), 4)
    x = F(random.randint(-20, 40), 2)
    d0 = F(1)
    tol = F(random.randint(1, 9), 10)
    b = float((lam - x) ** 2 / (4 * lam))
    kTf = float(kT)
    K = float(A * tol / (d0 * (1 - tol)))
    # the algebraic chain: exp(-b/kT) >= 1/K  <=>  -b/kT >= log(1/K) = -log K  <=>  b <= kT log K
    if abs(b - kTf * math.log(K)) < 1e-9:
        skipped_mar += 1
        continue
    checked_mar += 1
    exp_form = (-b / kTf) >= math.log(1 / K)
    log_form = b <= kTf * math.log(K)
    sq_form = float((lam - x) ** 2) <= 4 * float(lam) * kTf * math.log(K)
    if exp_form != log_form:
        fails.append(f"marcus exp/log mismatch: b={b} K={K}")
    if log_form != sq_form:
        fails.append(f"marcus squared-form mismatch: b={b} K={K}")
print(f"  Marcus bridge: {checked_mar} parameter sets checked "
      f"({skipped_mar} boundary cases skipped), exp / log / squared forms agree")

print()
if fails:
    print(f"FAILURES ({len(fails)}):")
    for f in fails[:20]:
        print("  -", f)
    sys.exit(1)
print("all checks passed (this is a cross-check, not the acceptance gate)")
