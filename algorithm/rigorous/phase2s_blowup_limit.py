"""The blow-up limit: does g(eps*eta_hat)/w^2 converge to a w-independent
profile G(eps), and is G(eps) < 0 on a ball?

Why this is the right object.  A Taylor proof fails: the cubic model
g ~ 1/2 Q eps^2 + 1/6 C3 eps^3 predicts g>0 for narrow bumps beyond
eps* ~ 5 sqrt(w), but the exact oracle finds g<0 far past that -- the
non-smooth 4th-order remainder rescues it.  So the smoothness-based route
stalls.

But the DIRECT data has clean structure: for the H2-normalized bump, max g
scales EXACTLY like w^2.  If  G(eps) := lim_{w->0} g(eps*eta_hat)/w^2
exists (w-independent) and G(eps) < 0 for eps in [0, rho], then g < 0 for all
small w uniformly -- the local-max statement in the narrow limit, with no
Taylor expansion.  G is a boundary-layer (blow-up) profile: the rescaled area
response at the breakpoint.

This script computes g(eps*eta_hat)/w^2 over an eps-grid at several w and checks
(i) convergence to a common profile G(eps), (ii) G(eps) < 0 throughout.
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


def profile(p, b, w, comp, epsgrid):
    b = mp.mpf(b); w = mp.mpf(w)
    nrm = h2norm(b, w, comp)
    _, bk = area(make_traj(p, mp.mpf(0), b, w, comp), p, dps=DPS)
    A0 = area(make_traj(p, mp.mpf(0), b, w, comp), p, dps=DPS, b0=list(bk))[0]
    out = []; b0 = list(bk)
    for e in epsgrid:
        A, bkj = area(make_traj(p, e/nrm, b, w, comp), p, dps=DPS, b0=b0)
        b0 = list(bkj)
        out.append((A - A0) / (w*w))
    return out


def main():
    p, _ = solve_gerver_constants(working_dps=DPS, verbose=False)
    mp.mp.dps = DPS
    TR = p['theta']
    comp = sys.argv[1] if len(sys.argv) > 1 else "x"
    epsgrid = [mp.mpf(k)/20 for k in range(1, 13)]     # eps = 0.05 .. 0.60
    ws = ['0.01', '0.005', '0.0025']
    print("=" * 78)
    print(f"BLOW-UP LIMIT  G(eps)=lim g(eps*eta_hat)/w^2   at b2, component {comp}")
    print("=" * 78)
    cols = {w: profile(p, TR, w, comp, epsgrid) for w in ws}
    print(f"  {'eps':>6} " + "".join(f"{'w='+w:>14}" for w in ws) + f"{'converged?':>12}")
    allneg = True
    for i, e in enumerate(epsgrid):
        vals = [cols[w][i] for w in ws]
        spread = abs(float(vals[-1]) - float(vals[-2]))
        conv = "yes" if spread < abs(float(vals[-1]))*mp.mpf('0.02') + mp.mpf('1e-12') else "no"
        if float(vals[-1]) > 1e-18:
            allneg = False
        print(f"  {float(e):>6.2f} " +
              "".join(f"{mp.nstr(v,6):>14}" for v in vals) + f"{conv:>12}")
    print()
    print(f"  G(eps) < 0 throughout the sampled ball?  {allneg}")
    print("  columns agree across w  =>  blow-up limit G(eps) exists (w-independent)")
    print("  If G<0 on [0,rho] and convergence is uniform, c_G is a local max in the")
    print("  narrow limit at this breakpoint -- the uniform-in-w statement Taylor missed.")


if __name__ == "__main__":
    main()
