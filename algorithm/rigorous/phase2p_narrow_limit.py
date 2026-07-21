"""Does the quartic-criterion margin stabilize as w->0?

The clean oracle shows C3 -> const, Q ~ w, C4 grows, so the criterion
C3^2 <= 3|Q||C4| tends to a finite jet-determined condition as w->0.  The
x-component margin was DECREASING (42%,36%,27% at w=0.012,0.009,0.006); we push
to narrower w to see whether it stabilizes positive (criterion holds in the
limit) or crosses zero (marginal/failing).

Also reports the scalings Q/w, C3, C4*w to expose the w->0 limits, which are the
quantities a closed-form proof must pin down.
"""
from __future__ import annotations
import sys, os
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gerver_constants import solve_gerver_constants
from analytic_oracle import make_traj, area

DPS = 34


def coeffs(p, b, w, comp):
    b = mp.mpf(b); w = mp.mpf(w)
    h = w / 8
    _, bk = area(make_traj(p, mp.mpf(0), b, w, comp), p, dps=DPS)
    f = {0: area(make_traj(p, mp.mpf(0), b, w, comp), p, dps=DPS, b0=list(bk))[0]}
    for sign in (1, -1):
        b0 = list(bk)
        for j in range(1, 4):
            A, bkj = area(make_traj(p, sign*j*h, b, w, comp), p, dps=DPS, b0=b0)
            b0 = list(bkj); f[sign*j] = A
    g2 = (f[1] - 2*f[0] + f[-1]) / h**2
    g3 = (f[2] - 2*f[1] + 2*f[-1] - f[-2]) / (2*h**3)
    g4 = (f[2] - 4*f[1] + 6*f[0] - 4*f[-1] + f[-2]) / h**4
    return float(g2), float(g3), float(g4)


def main():
    p, _ = solve_gerver_constants(working_dps=DPS, verbose=False)
    mp.mp.dps = DPS
    TR = p['theta']
    print("=" * 90)
    print("NARROW-LIMIT criterion margin at b2   (does it stabilize as w->0?)")
    print("=" * 90)
    for comp in ("x", "y"):
        print(f"\n--- component {comp} ---")
        print(f"  {'w':>7} {'Q':>12} {'C3':>10} {'C4':>12} "
              f"{'Q/w':>9} {'C4*w':>9} {'margin%':>9}")
        for w in ('0.010', '0.007', '0.005', '0.0035', '0.0025'):
            Q, C3, C4 = coeffs(p, TR, w, comp)
            wf = float(w)
            if C4 < 0:
                m = 100*(3*abs(Q)*abs(C4) - C3*C3)/(3*abs(Q)*abs(C4))
                mt = f"{m:>9.2f}"
            else:
                mt = "  C4>=0"
            print(f"  {w:>7} {Q:>12.6f} {C3:>10.4f} {C4:>12.3f} "
                  f"{Q/wf:>9.3f} {C4*wf:>9.4f} {mt}")
    print("\n  margin -> positive constant  => criterion holds in the w->0 limit (provable target)")
    print("  margin -> 0 or negative       => criterion is marginal/fails; proof must handle it")


if __name__ == "__main__":
    main()
