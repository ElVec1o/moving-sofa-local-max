"""sigma_resolved.py — S6 SOLVED, and the repair: use the REGION, not the signed area.

Chain of findings:

  * Sigma's reconstruction fails to dominate the true area at second order
    (sigma_matched.py), and closing the six interior chord gaps via the matched
    junction response does NOT fix it: the eps<0 branch stays at -1.8 to -5.2
    times eps^2.
  * The matched curve SELF-INTERSECTS under perturbation.  Measured lens area
    (resolved area minus |shoelace|): +8.312e-05, +3.125e-05, +7.612e-06,
    +1.878e-06 -- and this quantitatively accounts for the deficit (-8.270e-05,
    -3.016e-05, -7.066e-06) to between 0.5% and 8%.
  * The lens is exactly QUADRATIC in eps: over the three amplitudes
    eps = -0.004, -0.002, -0.001 the lens is 3.125e-5, 7.612e-6, 1.878e-6,
    giving local exponents 2.04 and 2.02.
  * At c_R the lens is 5.45e-13, i.e. the curve is simple there.

THE POINT.  Lemma `lem:superset` is a statement about the enclosed REGION
R(Gamma): S(c) is contained in R(Gamma), hence |S| <= |R(Gamma)|.  But every
reconstruction in this project evaluates a SIGNED area -- a Green/shoelace sum --
and

    signed area  =  |R(Gamma)|   only when Gamma is SIMPLE.

When Gamma self-intersects, the shoelace subtracts the lens instead of adding it,
so the computed number falls BELOW |R(Gamma)| and can fall below |S| even though
the region still contains the sofa.  The lemma was never wrong here; the
evaluation was.

REPAIR: evaluate the enclosed region's area, resolving self-intersections
(shapely `buffer(0)` computes exactly the outer region).  This script checks that
the repaired functional dominates the true area, and reports the improvement.

Usage: python3 sigma_resolved.py [K] [n_dir] [n_arc]
"""
from __future__ import annotations
import os, sys, math, subprocess
import numpy as np
from shapely.geometry import Polygon

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
import sigma_envelope as SE
from sigma_matched import solve_matched
from sigma_crossing import pieces
from romik_hessian import tabulate_romik


def shoelace(P):
    x, y = P[:, 0], P[:, 1]
    return 0.5*(np.dot(x, np.roll(y, -1)) - np.dot(np.roll(x, -1), y))


def areas(amps, delta, modes, n=600):
    """(signed |shoelace|, resolved region area) of the reconstruction curve"""
    pc = pieces(amps, delta, modes, n)
    P = np.vstack([Q for _, Q in pc])
    keep = np.r_[True, (np.abs(np.diff(P, axis=0)).sum(axis=1) > 1e-14)]
    P = P[keep]
    return abs(shoelace(P)), Polygon(P).buffer(0).area


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    nd = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    na = int(sys.argv[3]) if len(sys.argv) > 3 else 600
    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    d0, _ = solve_matched([0.0]*len(modes), modes)
    nt = 4801
    th, cx, cy = tabulate_romik(nt)

    def rust(gx, gy):
        inp = [f"{nt} 1", " ".join(f"{t:.17g}" for t in th),
               " ".join(f"{u:.17g} {v:.17g}" for u, v in zip(gx, gy))]
        r = subprocess.run([os.path.join(THIS, "sigma_area")],
                           input="\n".join(inp), capture_output=True, text=True)
        return float(r.stdout.split()[0])

    sl0, rs0 = areas([0.0]*len(modes), d0, modes, na)
    T0 = rust(cx, cy)
    print(f"SIGNED vs REGION area for the matched Sigma reconstruction  "
          f"(K={K}, n={na}/arc)")
    print(f"  at c_R:  |shoelace| = {sl0:.9f}   region = {rs0:.9f}   "
          f"lens = {rs0-sl0:.2e}")
    print(f"  A_true(c_R) = {T0:.9f};  offsets subtracted below\n")
    b_sl = sl0 - T0
    b_rs = rs0 - T0

    B = {m: np.sin(2*m[1]*th) for m in modes}
    rng = np.random.default_rng(2024)
    print(f"{'dir':>4} {'eps':>8} {'lens':>12} {'D signed':>12} "
          f"{'D region':>12} {'Dr/eps^2':>10}  dom?")
    negs = negr = tot = 0
    for t_ in range(nd):
        v = rng.standard_normal(len(modes)); v /= np.linalg.norm(v)
        gx = sum(v[i]*B[m] for i, m in enumerate(modes) if m[0] == 0)
        gy = sum(v[i]*B[m] for i, m in enumerate(modes) if m[0] == 1)
        for e in (0.004, -0.004, 0.002, -0.002):
            amps = list(e*v)
            dm, res = solve_matched(amps, modes, d0)
            if res > 1e-8:
                print(f"{t_+1:>4} {e:8.4f}   (Newton residual {res:.1e} -- "
                      f"NOT converged, skipped)")
                continue
            sl, rs = areas(amps, dm, modes, na)
            At = rust(cx + e*gx, cy + e*gy)
            ds = (sl - At) - b_sl
            dr = (rs - At) - b_rs
            tot += 1
            if ds < 0:
                negs += 1
            if dr < 0:
                negr += 1
            print(f"{t_+1:>4} {e:8.4f} {rs-sl:12.3e} {ds:12.3e} {dr:12.3e} "
                  f"{dr/e**2:10.4f}  {'yes' if dr > 0 else 'NO'}")
        print()
    print(f"signed shoelace : {negs}/{tot} probes with Delta < 0")
    print(f"region area     : {negr}/{tot} probes with Delta < 0")
    print("\nVERDICT:", "REGION area dominates -- the defect was the SIGNED "
          "evaluation, not the lemma." if negr == 0 else
          f"region area still fails on {negr} probe(s) -- a further mechanism "
          "remains.")


if __name__ == "__main__":
    main()
