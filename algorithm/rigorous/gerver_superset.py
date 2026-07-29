"""gerver_superset.py — ITEM B4: does the repaired A_corr dominate A_true?

A_rec's superset property FAILS: A_rec - A_true = -(l/2) L eps + O(eps^2), so
one sign of any eta with L(eta) != 0 sends A_rec below A_true at first order.
The additive repair

    A_corr(c) := A_rec(c) + (l/2)(c_x'(0) + c_x'(pi/2))

cancels exactly that first-order term, so

    A_corr - A_true  =  O(eps^2),

and whether A_corr >= A_true near c_G is decided at SECOND order.  That is a
finite, measurable question, and this script answers it.

Measure  Delta(eps) := [A_corr - A_true](eps) - [A_corr - A_true](0).  The
subtraction removes the Rust oracle's constant t-discretisation offset (~1.2e-4
in absolute area), which is independent of eps.  Then:

  * Delta > 0 for both signs of eps, with Delta ~ eps^2  ->  A_corr >= A_true
    locally, B4 holds, and the repair is a genuine superset bound.
  * Delta < 0 for either sign  ->  B4 FAILS and the repair does not restore
    the superset property; Part II then needs the ker L restriction instead.

Usage: python3 gerver_superset.py [n_theta]
"""
from __future__ import annotations
import os, sys, math, subprocess
import numpy as np
import mpmath as mp

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from analytic_oracle import _xt_full
from gerver_constants import solve_gerver_constants
from gerver_proof import area_corr


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 6001
    mp.mp.dps = 30
    p, _ = solve_gerver_constants(working_dps=30, verbose=False)
    th = np.linspace(0.0, math.pi/2, n)

    def rust(trajs):
        inp = [f"{n} {len(trajs)}", " ".join(f"{t:.17g}" for t in th)]
        for a, b in trajs:
            inp.append(" ".join(f"{u:.17g} {v:.17g}" for u, v in zip(a, b)))
        r = subprocess.run([os.path.join(THIS, "sigma_area")],
                           input="\n".join(inp), capture_output=True,
                           text=True, env=dict(os.environ, GERVER="1"))
        return [float(x) for x in r.stdout.split()]

    cx = np.empty(n); cy = np.empty(n)
    for i, t in enumerate(th):
        x, _, _ = _xt_full(mp.mpf(t), p)
        cx[i] = float(x[0]); cy[i] = float(x[1])

    def mk(eps, k, comp):
        def traj(t):
            x, xp, xpp = _xt_full(t, p)
            s = mp.sin(2*k*t); sp = 2*k*mp.cos(2*k*t)
            spp = -(2*k)**2*mp.sin(2*k*t)
            if comp == "x":
                return ((x[0]+eps*s, x[1]), (xp[0]+eps*sp, xp[1]),
                        (xpp[0]+eps*spp, xpp[1]))
            return ((x[0], x[1]+eps*s), (xp[0], xp[1]+eps*syp0(sp)),
                    (xpp[0], xpp[1]+eps*spp))
        return traj

    def syp0(v):
        return v

    G0 = float(area_corr(mk(mp.mpf(0), 1, "x"), p, repair=True))
    T0 = rust([(cx, cy)])[0]
    base = G0 - T0
    print(f"ITEM B4 — is A_corr >= A_true near c_G?   (n_theta={n})")
    print(f"  A_corr(c_G) = {G0:.10f}   A_true(c_G) = {T0:.10f}")
    print(f"  constant oracle offset = {base:+.3e}  (subtracted below)\n")
    print(f"{'mode':>10} {'eps':>9} {'Delta':>14} {'Delta/eps^2':>13}  sign")
    verdict = True
    for (k, comp) in ((2, "x"), (4, "x"), (2, "y")):
        g = np.sin(2*k*th)
        for e in (0.02, -0.02, 0.01, -0.01, 0.005, -0.005):
            if comp == "x":
                tr = (cx + e*g, cy)
            else:
                tr = (cx, cy + e*g)
            Tt = rust([tr])[0]
            Gt = float(area_corr(mk(mp.mpf(e), k, comp), p, repair=True))
            d = (Gt - Tt) - base
            print(f"  {comp} sin{2*k:2d}t {e:9.3f} {d:14.3e} "
                  f"{d/e**2:13.3f}  {'+' if d > 0 else '-'}")
            if d <= 0:
                verdict = False
        print()
    print("VERDICT:", "Delta > 0 on every probe -> A_corr >= A_true locally, "
          "B4 HOLDS" if verdict else
          "Delta <= 0 somewhere -> B4 FAILS; the repair does not restore the "
          "superset property")


if __name__ == "__main__":
    main()
