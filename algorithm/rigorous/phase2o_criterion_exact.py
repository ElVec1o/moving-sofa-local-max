"""Quartic criterion at HIGH PRECISION using the analytic Green oracle.

The Shapely float oracle could not resolve C4 (signature ~1e-6 vs floor 2e-7).
The analytic oracle is exact to ~25 digits, so Q=g''(0), C3=g'''(0), C4=g''''(0)
are clean.  We evaluate them via mpmath finite differences (the oracle's
precision makes small h safe) and test  C3^2 <= 3|Q||C4|.

This decides whether the two-regime picture (C4 sign-change with width) is real,
and whether the criterion margin is genuinely positive -- i.e. whether the
proof target holds, free of the float floor.
"""
from __future__ import annotations
import sys, os
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gerver_constants import solve_gerver_constants
from analytic_oracle import make_traj, area

DPS = 30
HALF = None


def coeffs(p, b, w, comp, h=None):
    """Q, C3, C4 = g''(0), g'''(0), g''''(0) via 7-point central stencils."""
    b = mp.mpf(b); w = mp.mpf(w)
    if h is None:
        h = min(mp.mpf('2e-3'), w / 6)   # keep the step small vs bump width
    vals = {}
    # evaluate k=0 first (exact Gerver seed), then walk outward warm-starting
    _, bk = area(make_traj(p, mp.mpf(0), b, w, comp), p, dps=DPS)
    vals[0] = area(make_traj(p, mp.mpf(0), b, w, comp), p, dps=DPS, b0=list(bk))[0]
    for sign in (1, -1):
        b0 = list(bk)
        for j in range(1, 4):
            eps = sign * j * h
            A, bkj = area(make_traj(p, eps, b, w, comp), p, dps=DPS, b0=b0)
            b0 = list(bkj)
            vals[sign * j] = A
    f = vals
    # central differences (exact-arithmetic function, truncation O(h^2..))
    g2 = (f[1] - 2*f[0] + f[-1]) / h**2
    g3 = (f[2] - 2*f[1] + 2*f[-1] - f[-2]) / (2*h**3)
    g4 = (f[2] - 4*f[1] + 6*f[0] - 4*f[-1] + f[-2]) / h**4
    return g2, g3, g4


def main():
    p, _ = solve_gerver_constants(working_dps=DPS, verbose=False)
    mp.mp.dps = DPS
    TR = p['theta']
    print("=" * 84)
    print("QUARTIC CRITERION AT HIGH PRECISION (analytic oracle)   b2 breakpoint")
    print("=" * 84)
    print(f"  {'comp':>4} {'w':>7} {'Q':>13} {'C3':>12} {'C4':>13} "
          f"{'C3^2':>11} {'3|Q||C4|':>11} {'margin%':>8}")
    for comp in ("x", "y"):
        for w in ('0.02', '0.015', '0.012', '0.009', '0.006'):
            Q, C3, C4 = coeffs(p, TR, w, comp)
            Qf, C3f, C4f = float(Q), float(C3), float(C4)
            if C4f < 0:
                lhs = C3f*C3f; rhs = 3*abs(Qf)*abs(C4f)
                m = 100*(rhs-lhs)/rhs
                tag = f"{m:>8.2f}"
            else:
                lhs = C3f*C3f; rhs = float('nan'); tag = "  C4>=0"
            print(f"  {comp:>4} {w:>7} {Qf:>13.6f} {C3f:>12.4f} {C4f:>13.3f} "
                  f"{lhs:>11.4f} {rhs:>11.4f} {tag}")
        print()
    print("Clean (float-floor-free) C4 sign and criterion margin.")


if __name__ == "__main__":
    main()
