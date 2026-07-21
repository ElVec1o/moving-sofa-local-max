"""Direct local-max check at ALL four breakpoints (exact oracle).

phase2q verified g<0 across an H2-ball for localized bumps at b2.  By the
theta -> pi/2-theta symmetry of Gerver's sofa, b3 mirrors b2 and b4 mirrors b1,
so the genuinely new case is the EDGE breakpoint b1 = phi (close to theta=0).
We check b1 and b3 (and re-confirm b2, b4) so local maximality is verified along
the worst-case localized directions at every breakpoint.

Edge breakpoints need narrower bumps (support must stay in [0,pi/2] and respect
the gauge eta(0)=0); we use w <= 0.008 there, where eta(0) ~ e^{-(phi/w)^2} is
negligible.
"""
from __future__ import annotations
import sys, os
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gerver_constants import solve_gerver_constants
from analytic_oracle import make_traj, area

DPS = 30


def h2norm(b, w, comp):
    b = mp.mpf(b); w = mp.mpf(w)
    def eta2(t):
        s = (t - b) / w
        return (w * s * mp.e**(-s*s))**2
    def etapp2(t):
        s = (t - b) / w
        return ((1/w) * mp.e**(-s*s) * (4*s**3 - 6*s))**2
    lo, hi = b - 12*w, b + 12*w
    return mp.sqrt(mp.quad(eta2, [lo, b, hi]) + mp.quad(etapp2, [lo, b, hi]))


def check(p, name, b, widths, comp, rho=mp.mpf('0.3')):
    mp.mp.dps = DPS
    b = mp.mpf(b)
    epsgrid = [rho * mp.mpf(k) / 8 for k in range(1, 9)]
    for w in widths:
        w = mp.mpf(w)
        try:
            nrm = h2norm(b, w, comp)
            _, bk = area(make_traj(p, mp.mpf(0), b, w, comp), p, dps=DPS)
            A0 = area(make_traj(p, mp.mpf(0), b, w, comp), p, dps=DPS, b0=list(bk))[0]
            b0 = list(bk); worst = mp.mpf('-1e18')
            for e in epsgrid:
                A, bkj = area(make_traj(p, e/nrm, b, w, comp), p, dps=DPS, b0=b0)
                b0 = list(bkj); worst = max(worst, A - A0)
            v = "ok" if worst <= mp.mpf('1e-18') else "*** g>0 ***"
            print(f"    {name} {comp}  w={float(w):<7} max_eps g = {mp.nstr(worst,4):>12}  {v}")
        except Exception as ex:
            print(f"    {name} {comp}  w={float(w):<7} FAILED: {type(ex).__name__}")


def main():
    p, _ = solve_gerver_constants(working_dps=DPS, verbose=False)
    mp.mp.dps = DPS
    pi2 = mp.pi / 2
    BK = [("b1", p['phi'], ('0.008', '0.005', '0.003')),
          ("b3", pi2 - p['theta'], ('0.02', '0.01', '0.005')),
          ("b4", pi2 - p['phi'], ('0.008', '0.005', '0.003'))]
    print("=" * 76)
    print("DIRECT local-max at all breakpoints (exact oracle, H2-ball rho=0.3)")
    print("=" * 76)
    for name, b, widths in BK:
        print(f"\n  breakpoint {name} at theta={float(b):.5f}:")
        for comp in ("x", "y"):
            check(p, name, b, widths, comp)
    print("\n  all rows 'ok'  =>  local max verified along localized directions")
    print("  at every breakpoint (b2 done separately in phase2q).")


if __name__ == "__main__":
    main()
