"""gerver_corner.py — G8: the corner-path step of the containment proof.

The chord-free Gamma has three kinds of piece.  Two are rigorous already:

  * wall-line segments: each lies on the boundary of a half-plane containing S,
    so it excludes only points already excluded;
  * envelope arcs: the envelope of a family of wall lines bounds the intersection
    of their half-planes, which contains S.

The remaining piece is the CORNER PATH c(t), which enters the reconstruction with
a MINUS sign -- the region it bounds is SUBTRACTED.  For S subset R(Gamma) we need

    (region bounded by the corner path)  subset  union_t Q_t,

so that subtracting it removes only points already excluded from S.  (Subtracting
LESS than union Q_t is harmless: R only gets bigger.)

REDUCTION.  Write points of the plane as complex numbers.  With
mu_t = (cos t, sin t) and nu_t = (-sin t, cos t),

    <q - c(t), mu_t> + i <q - c(t), nu_t>  =  e^{-i t} ( q - c(t) ),

because <c', mu> + i <c', nu> = e^{-it} (c'_x + i c'_y) by the same computation.
Since Q_t is exactly the open third quadrant in the (mu_t, nu_t) frame at c(t),

    q in Q_t   <=>   e^{-i t} ( q - c(t) )  in the open third quadrant
               <=>   arg( q - c(t) ) - t   in ( pi, 3pi/2 )   (mod 2 pi).

So membership in union_t Q_t is a ONE-DIMENSIONAL root-existence question in t:
does the continuous function

    theta(t) := arg( q - c(t) ) - t      (unwrapped)

enter the open interval (pi, 3pi/2) for some t in [0, pi/2]?

This script tests that criterion on a dense sample of the corner region, and
reports the margin -- how far into the interval theta gets at its best t.  A
uniformly positive margin is the certificate that the corner step holds; the
margin's location tells us which t does the covering, which is what a proof would
have to exhibit.

Usage: python3 gerver_corner.py [n_grid] [n_t]
"""
from __future__ import annotations
import os, sys, math
import numpy as np
import mpmath as mp
from shapely.geometry import Polygon, Point

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from analytic_oracle import _xt_full, _solve_junction
from gerver_constants import solve_gerver_constants


def main():
    ng = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    nt = int(sys.argv[2]) if len(sys.argv) > 2 else 4001
    mp.mp.dps = 25
    p, _ = solve_gerver_constants(working_dps=25, verbose=False)
    pi2 = mp.pi/2

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

    print("G8 -- corner-path containment criterion")
    print("  q in Q_t  <=>  arg(q - c(t)) - t  in (pi, 3pi/2)   (mod 2pi)")
    print("  test: every q in the corner region must satisfy it for some t.\n")
    print(f"{'case':>18} {'#pts':>7} {'min margin':>12} {'worst q':>22}"
          f"  verdict")

    for (label, eps, k, comp) in (("c_G", 0.0, 1, "x"),
                                  ("x sin4t +0.01", 0.01, 2, "x"),
                                  ("x sin4t -0.01", -0.01, 2, "x"),
                                  ("y sin4t +0.01", 0.01, 2, "y")):
        tr = mk(mp.mpf(eps), k, comp)
        b0 = [p['theta'], pi2 - p['phi'], p['phi'], pi2 - p['theta']]
        bD, bx2 = _solve_junction(tr, "D", b0[0], b0[1], 25)
        bx1, bB = _solve_junction(tr, "B", b0[3], b0[2], 25)[::-1]

        # the corner region: bounded by c(t) for t in [bx1,bx2] and the chord
        # closing it.  Sample it, then test the criterion with t over ALL of
        # [0,pi/2] (the union is over the whole family, not just the arc range).
        ts = [bx1 + (bx2-bx1)*mp.mpf(i)/400 for i in range(401)]
        cpath = np.array([[float(z) for z in tr(t)[0]] for t in ts])
        reg = Polygon(np.vstack([cpath, cpath[0]]))
        if not reg.is_valid:
            reg = reg.buffer(0)
        minx, miny, maxx, maxy = reg.bounds
        gx = np.linspace(minx, maxx, ng)
        gy = np.linspace(miny, maxy, ng)
        pts = [(a, b) for a in gx for b in gy
               if reg.contains(Point(a, b))]
        if not pts:
            print(f"{label:>18} {'0':>7}  (corner region empty at this "
                  f"resolution)")
            continue
        P = np.array(pts)

        s = np.linspace(0.0, float(pi2), nt)
        cx = np.empty(nt); cy = np.empty(nt)
        for i, t in enumerate(s):
            x, _, _ = tr(mp.mpf(t))
            cx[i] = float(x[0]); cy[i] = float(x[1])
        # margin(q) = max over t of min( -f_mu, -f_nu ) ; > 0 means q in Q_t
        mux, muy = np.cos(s), np.sin(s)
        nux, nuy = -np.sin(s), np.cos(s)
        best = np.full(len(P), -1e30)
        CH = 400
        for a in range(0, nt, CH):
            b = min(a+CH, nt)
            dx = P[:, 0:1] - cx[None, a:b]
            dy = P[:, 1:2] - cy[None, a:b]
            fm = dx*mux[None, a:b] + dy*muy[None, a:b]
            fn = dx*nux[None, a:b] + dy*nuy[None, a:b]
            best = np.maximum(best, np.minimum(-fm, -fn).max(axis=1))
        i = int(best.argmin())
        ok = best[i] > 0
        print(f"{label:>18} {len(P):>7} {best[i]:12.3e} "
              f"({P[i,0]:+8.5f},{P[i,1]:+8.5f})  "
              f"{'COVERED' if ok else '*** NOT COVERED ***'}")

    print("\nA uniformly positive margin certifies the corner step: every point")
    print("the reconstruction subtracts is already excluded from S by some")
    print("wedge, so subtracting it cannot break S subset R(Gamma).")


if __name__ == "__main__":
    main()
