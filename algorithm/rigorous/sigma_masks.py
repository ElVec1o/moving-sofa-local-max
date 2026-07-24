"""sigma_masks.py — the full contact-activity diagram (mask table) for Sigma.

For each rotation angle theta, determine which boundary elements of the
direct-family hallway H_b(theta) = R(theta) H + c_R(theta), and of the
reflected-family hallway rho(H_b(theta)), are ACTIVE on the boundary of
Sigma = S ∩ rho(S).

Elements per hallway (hallway frame, inner corner at origin):
    corner : the reflex corner point (0,0)          -> corner path (notch tip)
    iy     : inner wall y=0, x in [-K,0]            -> notch side (horizontal leg)
    ix     : inner wall x=0, y in [-K,0]            -> notch side (vertical leg)
    oy     : outer wall y=1, x in [-K,1]            -> convex boundary support
    ox     : outer wall x=1, y in [-K,1]            -> convex boundary support

Output: per-theta activity flags (distance < tol) + raw distances, and the
condensed interval report = the MASK TABLE for the weighted Garding proof
(PROGRAM.md item S5).  This is a diagnostic (float) computation.
"""
from __future__ import annotations
import os, sys, math, time
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS)
sys.path.insert(0, os.path.dirname(THIS))

from shapely.geometry import Polygon as SPoly, Point, LineString
from shapely.affinity import rotate as srot, translate as strans, scale as sscale

from romik_hessian import tabulate_romik, HALLWAY, LHORIZ, K_BIG
from sofa_romik2017_reference import BETA


def build_sigma(n_theta=1201):
    thetas, cx, cy = tabulate_romik(n_theta=n_theta)
    S = LHORIZ
    for th, x, y in zip(thetas, cx, cy):
        Hb = srot(HALLWAY, math.degrees(th), origin=(0, 0))
        Hb = strans(Hb, xoff=float(x), yoff=float(y))
        S = S.intersection(Hb)
    rhoS = sscale(S, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
    return thetas, cx, cy, S, S.intersection(rhoS)


def elements(th, x, y, reflected=False):
    """The 5 boundary elements of H_b(theta) (or its rho-image)."""
    c, s = math.cos(th), math.sin(th)
    R = lambda p: (c*p[0]-s*p[1]+x, s*p[0]+c*p[1]+y)
    els = {
        "corner": Point(R((0.0, 0.0))),
        "iy": LineString([R((-K_BIG, 0.0)), R((0.0, 0.0))]),
        "ix": LineString([R((0.0, 0.0)), R((0.0, -K_BIG))]),
        "oy": LineString([R((-K_BIG, 1.0)), R((1.0, 1.0))]),
        "ox": LineString([R((1.0, 1.0)), R((1.0, -K_BIG))]),
    }
    if reflected:
        els = {k: sscale(g, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
               for k, g in els.items()}
    return els


def main():
    n_theta = int(sys.argv[1]) if len(sys.argv) > 1 else 1201
    n_probe = int(sys.argv[2]) if len(sys.argv) > 2 else 181
    tol = 2e-4          # activity threshold (discretization ~ (pi/2/n_theta)^2)

    t0 = time.time()
    print(f"building Sigma at n_theta={n_theta} ...", flush=True)
    thetas, cx, cy, S, Sigma = build_sigma(n_theta)
    print(f"  area(Sigma) = {Sigma.area:.7f}  ({time.time()-t0:.1f}s)", flush=True)
    bnd = Sigma.boundary

    # probe grid + interpolated trajectory
    tp = np.linspace(0.0, math.pi/2, n_probe)
    xp = np.interp(tp, thetas, cx); yp = np.interp(tp, thetas, cy)

    keys = ["corner", "iy", "ix", "oy", "ox"]
    fams = [("dir", False), ("ref", True)]
    act = {(f, k): np.zeros(n_probe, bool) for f, _ in fams for k in keys}
    dist = {(f, k): np.zeros(n_probe) for f, _ in fams for k in keys}

    for i, (th, x, y) in enumerate(zip(tp, xp, yp)):
        for fname, refl in fams:
            els = elements(th, x, y, reflected=refl)
            for k, g in els.items():
                d = bnd.distance(g)
                dist[(fname, k)][i] = d
                act[(fname, k)][i] = d < tol
        if (i+1) % 45 == 0:
            print(f"  probe {i+1}/{n_probe}  {time.time()-t0:.1f}s", flush=True)

    # condensed interval report
    print("\nMASK TABLE (activity intervals, theta in units of pi/2):")
    print(f"  beta = {BETA:.6f} rad = {BETA/(math.pi/2):.4f} * pi/2")
    for fname, _ in fams:
        for k in keys:
            a = act[(fname, k)]
            runs = []
            j = 0
            while j < n_probe:
                if a[j]:
                    j0 = j
                    while j < n_probe and a[j]:
                        j += 1
                    runs.append((tp[j0]/(math.pi/2), tp[j-1]/(math.pi/2)))
                else:
                    j += 1
            rs = ", ".join(f"[{u:.3f},{v:.3f}]" for u, v in runs) or "NONE"
            print(f"  {fname}.{k:6s}: {rs}")

    np.savez(os.path.join(THIS, "sigma_masks.npz"),
             tp=tp, **{f"{f}_{k}_d": dist[(f, k)] for f, _ in fams for k in keys})
    print("\nsaved sigma_masks.npz (raw distances)")


if __name__ == "__main__":
    main()
