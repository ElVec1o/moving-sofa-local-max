"""Is the quartic criterion  C3^2 <= 3|Q||C4|  robust across directions?

The criterion is SCALE-INVARIANT (Q,C3,C4 ~ lambda^2,3,4 under eta->lambda eta,
so both sides ~ lambda^6), so moderate-width bumps with MEASURABLE area changes
decide it -- no float-limit issue.

For each direction (breakpoint x component x width) we sample
g(eps)=F(c_G+eps*eta)-F0 on a fine eps grid, fit a degree-6 polynomial,
extract Q=2c2, C3=6c3, C4=24c4, and evaluate the criterion and its margin.

If the margin stays bounded away from 0 across directions -> the criterion is
robust and a uniform proof is plausible.  If it approaches 0 (or flips) for
some direction -> that is where a proof must concentrate (or fails).
"""
from __future__ import annotations
import math, os, sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase2d_qsmooth import tabulate_gerver, build_sofa

HALF = math.pi / 2
PHI = 0.039177364790083641
TR = 0.681301509382724894
BREAKS = [("b1", PHI), ("b2", TR), ("b3", HALF - TR), ("b4", HALF - PHI)]


def coeffs(th, cx, cy, F0, t0, w, comp):
    tt = (th - t0) / w
    e = w * tt * np.exp(-tt * tt)          # odd bump, eta'(b)=1
    epsg = np.linspace(-0.035, 0.035, 21)

    def F(a):
        if comp == "x":
            return build_sofa(th, cx + a * e, cy).area
        return build_sofa(th, cx, cy + a * e).area
    g = np.array([F(x) for x in epsg]) - F0
    # fit c0..c6; g(0)=g'(0)=0 expected -> c0,c1 ~ 0
    P = np.polyfit(epsg, g, 6)              # highest power first
    c = P[::-1]                             # c[k] = coeff of eps^k
    Q = 2 * c[2]; C3 = 6 * c[3]; C4 = 24 * c[4]
    return Q, C3, C4, c[0], c[1]


def main():
    n_theta = int(sys.argv[1]) if len(sys.argv) > 1 else 3001
    th, cx, cy = tabulate_gerver(n_theta)
    F0 = build_sofa(th, cx, cy).area
    print("=" * 82)
    print("QUARTIC CRITERION SWEEP   C3^2 <= 3|Q||C4|   (scale-invariant)")
    print("=" * 82)
    print(f"  n_theta={n_theta}  F0={F0:.7f}\n")
    print(f"  {'bkpt':>5} {'comp':>5} {'w':>6} {'Q':>10} {'C3':>9} {'C4':>10} "
          f"{'C3^2':>9} {'3|Q||C4|':>10} {'margin%':>8} {'ok':>4}")
    worst = 1e9
    for name, t0 in BREAKS[:2]:            # b1, b2 (b3,b4 are mirror images)
        for comp in ("x", "y"):
            for w in (0.05, 0.03, 0.02):
                Q, C3, C4, c0, c1 = coeffs(th, cx, cy, F0, t0, w, comp)
                if C4 >= 0:
                    verdict = "C4>=0"
                    lhs = rhs = float("nan"); marg = float("nan")
                else:
                    lhs = C3 * C3; rhs = 3 * abs(Q) * abs(C4)
                    marg = 100 * (rhs - lhs) / rhs if rhs else float("nan")
                    verdict = "yes" if lhs <= rhs else "NO"
                    worst = min(worst, marg)
                print(f"  {name:>5} {comp:>5} {w:>6.3f} {Q:>10.4f} {C3:>9.3f} "
                      f"{C4:>10.1f} {lhs:>9.3f} {rhs:>10.3f} {marg:>8.1f} {verdict:>4}")
        print()
    print(f"  worst margin over all probed directions: {worst:+.1f}%")
    print("  >0 everywhere -> criterion robust; a uniform proof is plausible.")
    print("  approaching 0 or negative -> the delicate/failing directions to target.")


if __name__ == "__main__":
    main()
