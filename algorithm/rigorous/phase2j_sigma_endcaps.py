"""Does Sigma's principal symbol stay non-degenerate at the end caps?

phase2i found:
  * phase 2 (beta < theta < pi/2-beta, most of the domain): D_tot ~ 4*I,
    trace exactly 8.000, isotropic -- lambda_min ~ 4, four times Gerver's.
  * phases 1 and 3 (the end caps): ONE direction collapses to 0.30-0.43,
    and the integer-count fit failed there (rms 1.5, trace not constant).

The Garding constant for Sigma is delta = inf_theta lambda_min(D_tot), so it
is decided entirely by the end caps.  Two outcomes:

    delta > 0 bounded away from 0  -> the Gerver chain transfers to Sigma
                                      and Romik's Open Problem 1 lands on the
                                      same conditional footing as Gerver.
    delta -> 0 as theta -> 0       -> no uniform Garding constant; Sigma is
                                      genuinely harder than Gerver and the
                                      chain does NOT transfer.

METHOD
------
Odd (slope) bumps, whose H^1 norm decays like w, so |Q|/||eta||^2_{H^1}
converges to the directional symbol <e, D_tot e>.  CRITICAL: the bump must
FIT inside [0, pi/2] or the jet normalisation is destroyed (this contaminated
theta=0.12 in phase2i, and b1 in the Gerver run).  We enforce 3w <= theta.
"""
from __future__ import annotations
import math, os, sys, time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from romik_hessian import ambi_area_from_arrays, tabulate_romik

HALF = math.pi / 2
BETA = 0.2897


def quotient(th, cx, cy, F0, t0, w, comp, eps=1e-4):
    t = (th - t0) / w
    e = w * t * np.exp(-t * t)
    if comp == "x":
        Fp = ambi_area_from_arrays(th, cx + eps * e, cy)
        Fm = ambi_area_from_arrays(th, cx - eps * e, cy)
    else:
        Fp = ambi_area_from_arrays(th, cx, cy + eps * e)
        Fm = ambi_area_from_arrays(th, cx, cy - eps * e)
    Q = (Fp - 2 * F0 + Fm) / (eps * eps)
    d = np.gradient(e, th)
    return -Q / np.trapezoid(e * e + d * d, th)


def main():
    n_theta = int(sys.argv[1]) if len(sys.argv) > 1 else 3001
    th, cx, cy = tabulate_romik(n_theta)
    F0 = ambi_area_from_arrays(th, cx, cy)
    print("=" * 72)
    print("SIGMA end-cap degeneracy:  does lambda_min stay away from 0?")
    print("=" * 72)
    print(f"  F_ambi = {F0:.9f}   n_theta={n_theta}   beta={BETA:.4f}\n")
    print(f"  {'theta':>7} {'w':>7} {'3w<=th?':>8} {'<ex,Dex>':>10} "
          f"{'<ey,Dey>':>10} {'min':>8}")
    rows = []
    for t0 in (0.06, 0.09, 0.13, 0.18, 0.24, 0.29,
               HALF - 0.29, HALF - 0.18, HALF - 0.09, HALF - 0.06):
        w = min(0.03, t0 / 3.2, (HALF - t0) / 3.2)
        fits = "yes" if 3 * w <= min(t0, HALF - t0) else "NO"
        qx = quotient(th, cx, cy, F0, t0, w, "x")
        qy = quotient(th, cx, cy, F0, t0, w, "y")
        rows.append((t0, min(qx, qy)))
        print(f"  {t0:>7.3f} {w:>7.4f} {fits:>8} {qx:>10.4f} {qy:>10.4f} "
              f"{min(qx,qy):>8.4f}")
    print()
    lm = [v for _, v in rows]
    print(f"  smallest directional quotient over end caps: {min(lm):.4f}")
    print("  (this upper-bounds lambda_min(D_tot) there)\n")
    inner = [v for t, v in rows if 0.08 < t < HALF - 0.08]
    print(f"  trend toward theta=0: " +
          ", ".join(f"{t:.2f}:{v:.3f}" for t, v in rows[:5]))
    if min(lm) > 0.15:
        print("\n  => bounded away from 0 on the probed range: a uniform Garding")
        print("     constant for Sigma is plausible; chain transfers with a")
        print("     smaller delta than Gerver's 1.")
    else:
        print("\n  => collapsing toward 0: NO uniform Garding constant for Sigma.")
        print("     Sigma is genuinely harder than Gerver; chain does NOT transfer.")


if __name__ == "__main__":
    main()
