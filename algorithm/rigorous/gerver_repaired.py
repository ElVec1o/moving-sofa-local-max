"""gerver_repaired.py — THE REPAIR: a chord-free, constraint-only reconstruction.

The root cause of the Part II defect is that Lemma `lem:superset` is applied to a
curve containing straight CHORDS, while its proof (and the Lean formalisation
`superset_principle`, which is sound but proves only the constraint-dropping
statement) covers only CONSTRAINT boundaries.  A chord can cut into S(c), and at
c_G's perturbations it does, at first order.

The fix is not to correct the functional but to rebuild the curve so that every
piece is a constraint boundary.  Measured facts that make this possible
(all under a perturbation with eta(0) = eta(pi/2) = 0, so c(0) and c(pi/2) and
hence every constraint line of H_0 and H_{pi/2} are FIXED):

    A(phi)     lies on  x = c_x(0) + 1        to 1.4e-11
    C(pi/2-phi) lies on x = c_x(pi/2) - 1     to 1.4e-11
    B(pi/2)    lies on  y = c_y(0)
    D(0)       lies on  y = c_y(pi/2)
    A(pi/2), C(0) lie on y = c_y(0) + 1, and do not move

So the closed curve

    X[bx1->bx2] . D[bD->0]
      . {y = c_y(pi/2)} . {x = c_x(pi/2)-1}          (left closure)
      . C[pi/2-phi -> 0]
      . {y = c_y(0)+1}                                (top)
      . A[pi/2 -> phi]
      . {x = c_x(0)+1} . {y = c_y(0)}                 (right closure)
      . B[pi/2 -> bB]

uses ONLY envelope arcs, the corner path, and wall lines -- exactly the objects
Lemma `lem:superset` legitimately covers, and exactly the hypotheses of the Lean
`superset_principle`.  Hence R(Gamma) contains S(c) for EVERY c, so
A_rep >= A_true unconditionally.  At c_G the two closure corners degenerate
(A(phi) = (1,0), C(pi/2-phi) = (x_C,0)), so Gamma = dS exactly and A_rep = A*.

Those two facts together force stationarity: A_rep - A_true >= 0 with equality
at c_G, so its derivative vanishes there.  This script checks all three
numerically -- A_rep(c_G) = A*, dA_rep = 0, and A_rep >= A_true -- and compares
against the old chorded A_rec.

Area by shoelace on the assembled closed polygon (not term-by-term Green), so
no boundary-term bookkeeping can go wrong.

Usage: python3 gerver_repaired.py [n_per_arc]
"""
from __future__ import annotations
import os, sys, math, subprocess
import numpy as np
import mpmath as mp

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from analytic_oracle import contact_wd, _xt_full, _solve_junction
from gerver_constants import solve_gerver_constants


def curve(traj, p, n=4000, chorded=False):
    """assemble the closed reconstruction polygon; returns (pts, area)"""
    pi2 = mp.pi/2
    phi = p['phi']
    b0 = [p['theta'], pi2 - p['phi'], p['phi'], pi2 - p['theta']]
    bD, bx2 = _solve_junction(traj, "D", b0[0], b0[1], 30)
    bx1, bB = _solve_junction(traj, "B", b0[3], b0[2], 30)[::-1]

    def arc(w, a, b, m):
        ts = [a + (b - a)*mp.mpf(i)/m for i in range(m+1)]
        return [tuple(float(z) for z in contact_wd(traj, t, w)[0]) for t in ts]

    def corner(a, b, m):
        ts = [a + (b - a)*mp.mpf(i)/m for i in range(m+1)]
        return [tuple(float(z) for z in traj(t)[0]) for t in ts]

    c0 = traj(mp.mpf(0))[0]
    c1 = traj(pi2)[0]
    xr = float(c0[0]) + 1.0        # x = c_x(0)+1        (right closure vertical)
    yr = float(c0[1])              # y = c_y(0)          (right closure floor)
    xl = float(c1[0]) - 1.0        # x = c_x(pi/2)-1     (left closure vertical)
    yl = float(c1[1])              # y = c_y(pi/2)       (left closure floor)

    a_lo = mp.mpf(0) if chorded else phi
    c_hi = pi2 if chorded else pi2 - phi

    pts = []
    pts += corner(bx1, bx2, n//3)
    pts += arc("D", bD, mp.mpf(0), n//3)
    if not chorded:
        pts += [(xl, yl)]                    # along y = c_y(pi/2)
    pts += arc("C", c_hi, mp.mpf(0), n)      # C(c_hi) is on x = xl
    pts += arc("A", pi2, a_lo, n)            # via the top wall line
    if not chorded:
        pts += [(xr, yr)]                    # down x = c_x(0)+1, then y = c_y(0)
    pts += arc("B", pi2, bB, n//3)
    P = np.array(pts)
    x, y = P[:, 0], P[:, 1]
    area = 0.5*abs(np.dot(x, np.roll(y, -1)) - np.dot(np.roll(x, -1), y))
    return P, area


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
    mp.mp.dps = 30
    p, _ = solve_gerver_constants(working_dps=30, verbose=False)
    ASTAR = 2.2195316688

    def mk(eps, k, comp):
        def traj(t):
            x, xp, xpp = _xt_full(t, p)
            s = mp.sin(2*k*t); sp = 2*k*mp.cos(2*k*t)
            spp = -(2*k)**2*mp.sin(2*k*t)
            if comp == "x":
                return ((x[0]+eps*s, x[1]), (xp[0]+eps*sp, xp[1]),
                        (xpp[0]+eps*spp, xpp[1]))
            return ((x[0], x[1]+eps*s), (xp[0], xp[1]+eps*sp),
                    (xpp[0], xpp[1]+eps*spp))
        return traj

    _, A0 = curve(mk(mp.mpf(0), 1, "x"), p, n)
    print(f"CHORD-FREE, CONSTRAINT-ONLY RECONSTRUCTION   (n={n} per arc)")
    print(f"  A_rep(c_G) = {A0:.10f}    A* = {ASTAR:.10f}    "
          f"diff {A0-ASTAR:+.2e}")
    print(f"  (residual is the polygonal sampling of the arcs, O(1/n^2))\n")

    # true area, exact Rust oracle
    nt = 4801
    th = np.linspace(0.0, math.pi/2, nt)
    cx = np.empty(nt); cy = np.empty(nt)
    for i, t in enumerate(th):
        x, _, _ = _xt_full(mp.mpf(t), p)
        cx[i] = float(x[0]); cy[i] = float(x[1])

    def rust(gx, gy):
        inp = [f"{nt} 1", " ".join(f"{t:.17g}" for t in th),
               " ".join(f"{u:.17g} {v:.17g}" for u, v in zip(gx, gy))]
        r = subprocess.run([os.path.join(THIS, "sigma_area")],
                           input="\n".join(inp), capture_output=True,
                           text=True, env=dict(os.environ, GERVER="1"))
        return float(r.stdout.split()[0])

    print(f"{'mode':>10} {'eps':>8} {'A_rep':>14} {'A_rep-A_rep(0)':>16} "
          f"{'A_rep-A_true':>14}  dom?")
    ok_dom = True
    for (k, comp) in ((2, "x"), (4, "x"), (2, "y")):
        g = np.sin(2*k*th)
        for e in (0.01, -0.01, 0.002, -0.002):
            _, Ar = curve(mk(mp.mpf(e), k, comp), p, n)
            gx, gy = (cx + e*g, cy) if comp == "x" else (cx, cy + e*g)
            At = rust(gx, gy)
            dom = Ar - At
            if dom < -2e-4:          # oracle discretisation floor
                ok_dom = False
            print(f"  {comp} sin{2*k:2d}t {e:8.3f} {Ar:14.8f} {Ar-A0:+16.3e} "
                  f"{dom:+14.3e}  {'yes' if dom > -2e-4 else '*** NO ***'}")
        print()

    # first variation
    print("first variation (central difference, eps = 1e-6):")
    for (k, comp) in ((2, "x"), (4, "x"), (6, "x"), (2, "y")):
        e = mp.mpf('1e-6')
        _, Ap = curve(mk(e, k, comp), p, n)
        _, Am = curve(mk(-e, k, comp), p, n)
        d = (Ap - Am)/(2*float(e))
        old = -0.403440807358*(2*k + 2*k*(-1)**k) if comp == "x" else 0.0
        print(f"  {comp} sin{2*k:2d}t   dA_rep/deps = {d:+12.6f}   "
              f"(old chorded law: {old:+.6f})")
    print(f"\nVERDICT: domination {'HOLDS on every probe' if ok_dom else 'FAILS'}")


if __name__ == "__main__":
    main()
