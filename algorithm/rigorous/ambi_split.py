"""ambi_split.py — P3c: find a DISJOINT family of Mamikon sweeps that fills the niche.

ambi_mamikon.py established (n_hall = 721, n_sweep = 2001):

    N = W_1 u W_2   to 1.0e-4,   |W_i| = (1/2) int alpha_i^2  to 6 digits,
    |W_1| = |W_2| = 0.162399,    |N| = 0.184089,   overlap = 0.140606,

with alpha_1 = -<c',mu_t> > 0 exactly on [beta, pi/2] and alpha_2 = <c',nu_t> > 0
exactly on [0, pi/2 - beta].  So each sweep individually is a VALID convex-quadratic
lower bound for |N| -- and on the range where its own arm is positive, Baek's
injectivity condition holds, which is the whole point: the "failure on the outer
phases" was an artefact of demanding BOTH arms at once.

But a single sweep leaves 0.0217 of the niche uncovered, and the two together
double-count 0.1406, so their SUM (0.3248) is not a lower bound.  A lower bound needs
sweeps that are pairwise DISJOINT.  This script measures which splittings are disjoint.

  (1) where is N \\ W_2, and how big?
  (2) the MONOTONE-SWEEP prediction.  The normal velocity of the face-i line at
      distance s from the corner is
          face 2 (dir -mu_t):  alpha_2 - s       (advancing for s < alpha_2)
          face 1 (dir -nu_t):  s - alpha_1       (advancing for s > alpha_1)
      so if the sweep is monotone the niche is created by the INNER part of face 2 and
      the OUTER part of face 1, and
          N = W_2  disjoint-union  W_1out,     W_1out = sweep of [B(t), exit of K].
      Then |N| = (1/2) int alpha_2^2 + (1/2) int (S_1 - alpha_1)^2 exactly, and only
      the second factor is not convex-linear.  TESTED here.
  (3) the time-split family: W_2 on [0,tau] together with W_1 on [tau,pi/2].  Reports
      sum of integrals, union, overlap, so the best DISJOINT member is visible.

Usage: python3 ambi_split.py [n_hall] [n_sweep]
"""
from __future__ import annotations
import os, sys, math
import numpy as np
from shapely.geometry import Polygon, Point, LineString
from shapely.ops import unary_union
from shapely.affinity import rotate as srot, translate as strans, scale as sscale

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sofa_romik2017_reference import HALLWAY, x_path, BETA
from ambi_mamikon import build, arms, sweep, LHORIZ, PI2, BIG


def sweep_range(tw, cs, lens, along, i0, i1, inner=None):
    """sweep restricted to index range [i0,i1]; if inner is given, the segment runs
    from c - inner*dir to c - lens*dir instead of from c."""
    quads = []
    for i in range(i0, min(i1, len(tw) - 1)):
        t0, t1 = float(tw[i]), float(tw[i + 1])
        d0 = ((-math.sin(t0), math.cos(t0)) if along == 'nu' else
              (math.cos(t0), math.sin(t0)))
        d1 = ((-math.sin(t1), math.cos(t1)) if along == 'nu' else
              (math.cos(t1), math.sin(t1)))
        L0, L1 = max(lens[i], 0.0), max(lens[i + 1], 0.0)
        s0 = 0.0 if inner is None else max(inner[i], 0.0)
        s1 = 0.0 if inner is None else max(inner[i + 1], 0.0)
        if L0 <= s0 and L1 <= s1:
            continue
        p0 = (cs[i][0] - s0*d0[0], cs[i][1] - s0*d0[1])
        p1 = (cs[i+1][0] - s1*d1[0], cs[i+1][1] - s1*d1[1])
        q0 = (cs[i][0] - L0*d0[0], cs[i][1] - L0*d0[1])
        q1 = (cs[i+1][0] - L1*d1[0], cs[i+1][1] - L1*d1[1])
        poly = Polygon([p0, q0, q1, p1])
        if not poly.is_valid:
            poly = poly.buffer(0)
        if poly.area > 0:
            quads.append(poly)
    return unary_union(quads) if quads else Polygon()


def exit_len(c, d, K, hi=6.0):
    """distance from c along direction -d until leaving the convex body K"""
    lo = 0.0
    if not K.contains(Point(c[0] - 1e-9*d[0], c[1] - 1e-9*d[1])):
        return 0.0
    for _ in range(60):
        mid = 0.5*(lo + hi)
        p = Point(c[0] - mid*d[0], c[1] - mid*d[1])
        if K.contains(p):
            lo = mid
        else:
            hi = mid
    return lo


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 721
    nsw = int(sys.argv[2]) if len(sys.argv) > 2 else 2001
    ts, C1, S = build(n)
    rho = lambda G: sscale(G, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
    C2 = C1.intersection(rho(C1))
    N = C1.difference(S).intersection(C2)
    tw = np.linspace(0.0, PI2, nsw)
    cs, al1, al2 = arms(tw)
    W1 = sweep(tw, cs, al1, 'nu')
    W2 = sweep(tw, cs, al2, 'mu')
    print(f"|N| = {N.area:.9f}   |W1| = {W1.area:.9f}   |W2| = {W2.area:.9f}")
    print(f"beta = {BETA:.9f}   pi/2-beta = {PI2-BETA:.9f}\n")

    # (1) the uncovered part
    for nm, Wx in (("N \\ W2", N.difference(W2)), ("N \\ W1", N.difference(W1))):
        pieces = 1 if Wx.geom_type == 'Polygon' else len(Wx.geoms)
        print(f"(1) {nm}: area {Wx.area:.9f}  pieces {pieces}  "
              f"bbox {tuple(round(v,4) for v in Wx.bounds)}")
    print()

    # (2) monotone-sweep prediction:  N = W2  u  W1out
    S1 = np.array([exit_len(cs[i], (-math.sin(tw[i]), math.cos(tw[i])), C1)
                   for i in range(len(tw))])
    W1out = sweep_range(tw, cs, S1, 'nu', 0, len(tw) - 1, inner=al1)
    I2 = 0.5*np.trapezoid(np.maximum(al2, 0.0)**2, tw)
    Iout = 0.5*np.trapezoid(np.maximum(S1 - np.maximum(al1, 0.0), 0.0)**2, tw)
    print("(2) MONOTONE-SWEEP PREDICTION  N = W2 (+) W1out")
    print(f"    |W1out| measured = {W1out.area:.9f}   (1/2)int(S1-alpha1)^2 = "
          f"{Iout:.9f}")
    print(f"    |W2| + |W1out| = {W2.area + W1out.area:.9f}   vs |N| = {N.area:.9f}")
    print(f"    overlap W2 ^ W1out = {W2.intersection(W1out).area:.9f}")
    print(f"    N \\ (W2 u W1out)   = {N.difference(unary_union([W2,W1out])).area:.9f}")
    print(f"    (W2 u W1out) \\ N   = {unary_union([W2,W1out]).difference(N).area:.9f}")
    print(f"    integral form (1/2)int a2^2 + (1/2)int(S1-a1)^2 = {I2+Iout:.9f}")
    print()

    # (3) the time-split family
    print("(3) TIME-SPLIT FAMILY   W2 on [0,tau]  +  W1 on [tau,pi/2]")
    print(f"    {'tau':>9} {'int-sum':>11} {'union':>11} {'overlap':>11} "
          f"{'union/|N|':>10}")
    for tau in (0.0, BETA, 0.5, 0.7, math.pi/4, 0.9, 1.1, PI2-BETA, PI2):
        k = int(round(tau/PI2*(nsw-1)))
        A = sweep_range(tw, cs, al2, 'mu', 0, k)
        B = sweep_range(tw, cs, al1, 'nu', k, len(tw)-1)
        isum = (0.5*np.trapezoid(np.maximum(al2[:k+1], 0)**2, tw[:k+1]) if k > 0 else 0) \
             + (0.5*np.trapezoid(np.maximum(al1[k:], 0)**2, tw[k:]) if k < nsw-1 else 0)
        un = unary_union([A, B])
        ov = A.intersection(B).area
        print(f"    {tau:9.6f} {isum:11.7f} {un.area:11.7f} {ov:11.7f} "
              f"{un.area/N.area:10.6f}")
    print()
    print(f"    |N| = {N.area:.7f};  a member is a VALID lower bound only if its")
    print(f"    overlap is 0, and TIGHT only if union/|N| = 1 as well.")


if __name__ == "__main__":
    main()
