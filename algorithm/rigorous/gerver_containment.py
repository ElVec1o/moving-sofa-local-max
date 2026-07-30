"""gerver_containment.py — ITEM D5: does the chord-free Gamma CONTAIN the sofa?

Comparing areas cannot settle this: the Rust oracle's own error is C/n and grows
with perturbation curvature, which is the same size as the effect.  Containment
is the sharper and more direct test -- check every boundary point of S against
R(Gamma) -- and it is what Lemma `lem:superset` actually needs.

The test is CONSERVATIVE in the right direction.  S is built from a FINITE
hallway family, and dropping constraints only enlarges an intersection, so

    S_finite  ⊇  S_true.

Hence  S_finite ⊆ R(Gamma)  implies  S_true ⊆ R(Gamma).  A pass is meaningful;
a fail needs the margin compared against the sampling resolution.

Reported: the signed distance from each dS point to R(Gamma) (positive = inside),
its minimum, and where the minimum sits.  Run at c_G and under perturbations,
including the eps = 0.01 x-modes where the area comparison went negative.

Usage: python3 gerver_containment.py [n_hall] [n_arc]
"""
from __future__ import annotations
import os, sys, math
import numpy as np
import mpmath as mp
from shapely.geometry import Polygon, Point
from shapely.ops import unary_union

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from gerver_repaired import curve
from analytic_oracle import _xt_full
from gerver_constants import solve_gerver_constants

BIG = 40.0


def hallway(cx, cy, t):
    """H_t = C_t \\ Q_t as a shapely polygon (clipped to a large box)"""
    ct, st = math.cos(t), math.sin(t)
    mux, muy = ct, st
    nux, nuy = -st, ct
    # C_t : <p-c,mu> <= 1 and <p-c,nu> <= 1  -> intersection of two half-planes
    box = Polygon([(-BIG, -BIG), (BIG, -BIG), (BIG, BIG), (-BIG, BIG)])
    for (ax, ay) in ((mux, muy), (nux, nuy)):
        # ax*(x-cx)+ay*(y-cy) <= 1 : half-plane, build as a big rectangle
        # rotated so its interior is the correct side
        px, py = cx + ax*1.0, cy + ay*1.0      # point on the line
        tx, ty = -ay, ax                        # direction along the line
        q = Polygon([(px - tx*BIG, py - ty*BIG),
                     (px + tx*BIG, py + ty*BIG),
                     (px + tx*BIG - ax*2*BIG, py + ty*BIG - ay*2*BIG),
                     (px - tx*BIG - ax*2*BIG, py - ty*BIG - ay*2*BIG)])
        box = box.intersection(q)
    # Q_t : <p-c,mu> < 0 and <p-c,nu> < 0  -> the removed wedge
    w = Polygon([(cx, cy),
                 (cx - mux*BIG, cy - muy*BIG),
                 (cx - mux*BIG - nux*BIG, cy - muy*BIG - nuy*BIG),
                 (cx - nux*BIG, cy - nuy*BIG)])
    return box.difference(w)


def main():
    nh = int(sys.argv[1]) if len(sys.argv) > 1 else 900
    na = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    mp.mp.dps = 25
    p, _ = solve_gerver_constants(working_dps=25, verbose=False)
    th = np.linspace(0.0, math.pi/2, nh)

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

    print(f"CONTAINMENT TEST   S_finite (n_hall={nh}) vs R(Gamma) "
          f"(n_arc={na})")
    print("  S_finite superset S_true, so a PASS proves S_true subset "
          "R(Gamma).\n")
    print(f"{'case':>18} {'|S_fin|':>11} {'|R|':>11} {'min signed dist':>16}"
          f"  verdict")
    for (label, eps, k, comp) in (("c_G", 0.0, 1, "x"),
                                  ("x sin4t  +0.002", 0.002, 2, "x"),
                                  ("x sin4t  -0.002", -0.002, 2, "x"),
                                  ("x sin4t  +0.01", 0.01, 2, "x"),
                                  ("x sin4t  -0.01", -0.01, 2, "x"),
                                  ("x sin16t -0.01", -0.01, 8, "x"),
                                  ("y sin4t  +0.01", 0.01, 2, "y")):
        tr = mk(mp.mpf(eps), k, comp)
        cx = np.empty(nh); cy = np.empty(nh)
        for i, t in enumerate(th):
            x, _, _ = tr(mp.mpf(t))
            cx[i] = float(x[0]); cy[i] = float(x[1])
        S = hallway(cx[0], cy[0], th[0])
        for i in range(1, nh):
            S = S.intersection(hallway(cx[i], cy[i], th[i]))
            if S.is_empty:
                break
        P, _ = curve(tr, p, na)
        R = Polygon(P)
        if not R.is_valid:
            R = R.buffer(0)
        bx, by = S.exterior.xy
        pts = np.column_stack([np.array(bx), np.array(by)])
        # signed distance: + inside R, - outside
        d = np.array([(R.exterior.distance(Point(q)) if R.contains(Point(q))
                       else -R.exterior.distance(Point(q))) for q in pts])
        i = int(d.argmin())
        ok = d[i] > -1e-9
        print(f"{label:>18} {S.area:11.7f} {R.area:11.7f} {d[i]:16.3e}"
              f"  {'CONTAINED' if ok else '*** VIOLATED at (%.4f,%.4f)'
                  % (pts[i,0], pts[i,1])}")


if __name__ == "__main__":
    main()
