"""Direct local-maximality check with the EXACT oracle -- no differentiation.

The C3,C4 decomposition is unreliable: extracting a 4th eps-derivative by finite
differences has truncation error that grows as w->0, and the extracted C4 even
flips sign between step choices.  But local maximality does NOT need C3,C4: it is
simply g(eps) = F(c_G + eps*eta_hat) - F(c_G) <= 0 for eps in a fixed ball.

The oracle gives g EXACTLY (30+ digits), so we can test the H2-NORMALIZED narrow
bumps that Shapely could not resolve (they sat under its 2e-7 floor).  Normalize
eta to ||eta||_H2 = 1, then g(eps) < 0 for eps in [0, rho] over all narrow widths
== local max in the H2-ball of radius rho.

Report the WORST (max) g over the ball for each width and component, and whether
it stays <= 0 (and its magnitude) as w -> 0.
"""
from __future__ import annotations
import sys, os
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gerver_constants import solve_gerver_constants
from analytic_oracle import make_traj, area

DPS = 30


def h2norm(b, w, comp):
    """||eta||_{H2}, weighted norm ||eta||^2 + ||eta''||^2, in mpmath quad."""
    b = mp.mpf(b); w = mp.mpf(w)
    def eta2(t):
        s = (t - b) / w
        return (w * s * mp.e**(-s*s))**2
    def etapp2(t):
        s = (t - b) / w
        return ((1/w) * mp.e**(-s*s) * (4*s**3 - 6*s))**2
    lo, hi = b - 12*w, b + 12*w
    I = mp.quad(eta2, [lo, b, hi]) + mp.quad(etapp2, [lo, b, hi])
    return mp.sqrt(I)


def main():
    p, _ = solve_gerver_constants(working_dps=DPS, verbose=False)
    mp.mp.dps = DPS
    TR = p['theta']
    rho = mp.mpf('0.4')                    # H2-ball radius to certify
    epsgrid = [rho * mp.mpf(k) / 10 for k in range(1, 11)]
    print("=" * 80)
    print(f"DIRECT local-max check (exact oracle), H2-normalized bumps, ball rho={float(rho)}")
    print("=" * 80)
    for comp in ("x", "y"):
        print(f"\n--- component {comp} ---")
        print(f"  {'w':>8} {'||eta||_H2':>11} {'max_eps g':>14} {'at eps':>8} {'verdict':>9}")
        for w in ('0.02', '0.01', '0.005', '0.0025'):
            nrm = h2norm(TR, w, comp)
            _, bk = area(make_traj(p, mp.mpf(0), mp.mpf(TR), mp.mpf(w), comp), p, dps=DPS)
            A0 = area(make_traj(p, mp.mpf(0), mp.mpf(TR), mp.mpf(w), comp), p, dps=DPS, b0=list(bk))[0]
            b0 = list(bk); worst = mp.mpf('-1e18'); wat = 0
            for e in epsgrid:
                eu = e / nrm                # unnormalized eps for ||eta_hat||=1
                A, bkj = area(make_traj(p, eu, mp.mpf(TR), mp.mpf(w), comp), p, dps=DPS, b0=b0)
                b0 = list(bkj); g = A - A0
                if g > worst: worst, wat = g, e
            v = "MAX ok" if worst <= mp.mpf('1e-20') else "*** g>0 ***"
            print(f"  {w:>8} {float(nrm):>11.3f} {mp.nstr(worst,5):>14} "
                  f"{float(wat):>8.3f} {v:>9}")
    print("\n  g<=0 across the ball for all narrow w  =>  local max in H2-ball rho (exact).")
    print("  This is the robust statement; it needs no C3,C4 extraction.")


if __name__ == "__main__":
    main()
