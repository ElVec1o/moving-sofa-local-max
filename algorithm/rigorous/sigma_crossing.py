"""sigma_crossing.py — S6 candidate 1: does the matched Sigma curve SELF-INTERSECT?

The matched junction response closes all six interior chord gaps, yet the
reconstruction still fails to dominate the true area on the eps<0 branch, at
-1.8 to -5.2 times eps^2 (sigma_matched.py).  Something else makes the
reconstruction UNDERestimate, i.e. its curve cuts inside the true sofa.

Cheapest candidate, and the one whose signature matches: if two arcs CROSS under
perturbation, the shoelace sum subtracts the enclosed lens instead of adding it.
A crossing of depth O(eps) encloses a lens of area O(eps^2), one-signed -- exactly
the observed order and sign.

Test: assemble the matched curve exactly as `sigma_envelope.area_rec` does
(each arc sampled over its SHIFTED range and oriented a0 -> a1, closures being
the straight segments between consecutive ends), then ask shapely whether the
ring is simple.  Where it is not, report the intersection points and which arc
pair produced them.

Usage: python3 sigma_crossing.py [K] [n_per_arc]
"""
from __future__ import annotations
import os, sys, math
import numpy as np
from shapely.geometry import LinearRing, LineString, Polygon

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
import sigma_envelope as SE
from sigma_matched import solve_matched


def pieces(amps, delta, modes, n=800):
    """the per-arc point arrays, in traversal order, exactly as area_rec builds
    them (shifted ranges, oriented a0 -> a1)"""
    shifts = {}
    for d, (pi_, which) in zip(delta, SE.FREE):
        shifts[(pi_, which)] = d
    out = []
    for i, (lab, t0, t1, slot) in enumerate(SE.TAB):
        a0 = t0 + shifts.get((i, 't0'), 0.0)
        a1 = t1 + shifts.get((i, 't1'), 0.0)
        lo, hi = (a0, a1) if a0 < a1 else (a1, a0)
        if hi - lo < 1e-14:
            P = np.array([SE.arc_point(lab, slot, a0, amps, modes)])
        else:
            ts = np.linspace(lo, hi, n)
            P = np.array([SE.arc_point(lab, slot, float(t), amps, modes)
                          for t in ts])
            if a1 < a0:
                P = P[::-1]
        out.append((lab, P))
    return out


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 800
    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    d0, _ = solve_matched([0.0]*len(modes), modes)
    rng = np.random.default_rng(2024)

    print(f"SELF-INTERSECTION TEST on the MATCHED Sigma curve  "
          f"(K={K}, n={n}/arc)\n")
    print(f"{'case':>22} {'simple?':>9} {'#cross':>7}  detail")
    for (label, eps, seed) in (("c_R", 0.0, None),
                               ("dir1  eps=+0.004", 0.004, 1),
                               ("dir1  eps=-0.004", -0.004, 1),
                               ("dir2  eps=+0.004", 0.004, 2),
                               ("dir2  eps=-0.004", -0.004, 2),
                               ("dir2  eps=-0.002", -0.002, 2)):
        if seed is None:
            v = np.zeros(len(modes))
        else:
            r2 = np.random.default_rng(2024)
            for _ in range(seed):
                v = r2.standard_normal(len(modes))
            v = v/np.linalg.norm(v)
        amps = list(eps*v)
        dm, res = solve_matched(amps, modes, d0) if eps != 0 else (d0, 0.0)
        pc = pieces(amps, dm, modes, n)
        allp = np.vstack([P for _, P in pc])
        ring = LinearRing(allp)
        simple = ring.is_simple
        # locate crossings pairwise between non-adjacent arcs
        segs = [(lab, LineString(P)) for lab, P in pc if len(P) > 1]
        cross = []
        for a in range(len(segs)):
            for b in range(a+1, len(segs)):
                if b == a+1 or (a == 0 and b == len(segs)-1):
                    continue          # adjacent arcs share an endpoint
                it = segs[a][1].intersection(segs[b][1])
                if not it.is_empty:
                    cross.append((segs[a][0], segs[b][0], it))
        det = ", ".join(f"{u}x{v}" for u, v, _ in cross[:4]) or "-"
        print(f"{label:>22} {str(simple):>9} {len(cross):>7}  {det}")
        if cross:
            u, v, it = cross[0]
            try:
                pt = it if it.geom_type == "Point" else list(it.geoms)[0]
                print(f"{'':>22} first crossing {u} x {v} at "
                      f"({pt.x:.5f}, {pt.y:.5f})")
            except Exception:
                pass
    print("\nReading: a crossing between NON-adjacent arcs means the shoelace")
    print("  subtracts a lens, so the reconstruction underestimates -- the")
    print("  signature of the observed eps^2, one-signed deficit.")


if __name__ == "__main__":
    main()
