"""High-precision analytic area oracle for perturbed Gerver trajectories.

Replaces the floating-point Shapely polygon oracle with the EXACT Green's-
theorem boundary integral over Romik's contact paths, in mpmath at arbitrary
precision.  This removes the ~2e-7 float floor that made C4 (hence the quartic
criterion C3^2 <= 3|Q||C4|) unmeasurable, and is the interval-ready form that
closes caveat (i).

Built by generalizing gerver_area(): a trajectory provider gives
(x, x', x'') = (c_G + eps*eta, c_G' + eps*eta', c_G'' + eps*eta'') using the
analytic phase data _xt_full for c_G and closed-form derivatives of the bump.
Contact paths and their theta-derivatives are analytic (no kink-straddling),
so the area is correct to the working precision.  Moving breakpoints
(bD,bx2,bx1,bB) solve the junctions D(bD)=x(bx2), x(bx1)=B(bB).
"""
from __future__ import annotations
import sys, os
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gerver_constants import solve_gerver_constants, _xt_full


def bump_jet(t, b, w):
    """eta, eta', eta'' for the localized odd bump eta=w*s*exp(-s^2), s=(t-b)/w.
    eta(b)=0, eta'(b)=1, eta''(b)=0."""
    s = (t - b) / w
    e = mp.e ** (-s * s)
    eta = w * s * e
    etap = e * (1 - 2 * s * s)
    etapp = (1 / w) * e * (4 * s**3 - 6 * s)
    return eta, etap, etapp


def make_traj(p, eps, b, w, comp):
    """traj(t) -> (x, xp, xpp) for c_G + eps*eta in component comp ('x'/'y')."""
    def traj(t):
        x, xp, xpp = _xt_full(t, p)
        eta, etap, etapp = bump_jet(t, b, w)
        if comp == "x":
            return ((x[0] + eps*eta, x[1]), (xp[0] + eps*etap, xp[1]),
                    (xpp[0] + eps*etapp, xpp[1]))
        else:
            return ((x[0], x[1] + eps*eta), (xp[0], xp[1] + eps*etap),
                    (xpp[0], xpp[1] + eps*etapp))
    return traj


def contact_wd(traj, t, which):
    """Analytic value and theta-derivative of contact path A/B/C/D."""
    x, xp, xpp = traj(t)
    c, s = mp.cos(t), mp.sin(t)
    mu = (c, s); mup = (-s, c); nu = (-s, c); nup = (-c, -s)
    if which in ("A", "B"):
        d = xp[0]*mu[0] + xp[1]*mu[1]
        dp = xpp[0]*mu[0] + xpp[1]*mu[1] + xp[0]*mup[0] + xp[1]*mup[1]
        base = (x[0] + d*nu[0], x[1] + d*nu[1])
        dbase = (xp[0] + dp*nu[0] + d*nup[0], xp[1] + dp*nu[1] + d*nup[1])
        if which == "A":
            return (base[0]+mu[0], base[1]+mu[1]), (dbase[0]+mup[0], dbase[1]+mup[1])
        return base, dbase
    else:  # C, D
        d = xp[0]*nu[0] + xp[1]*nu[1]
        dp = xpp[0]*nu[0] + xpp[1]*nu[1] + xp[0]*nup[0] + xp[1]*nup[1]
        base = (x[0] - d*mu[0], x[1] - d*mu[1])
        dbase = (xp[0] - dp*mu[0] - d*mup[0], xp[1] - dp*mu[1] - d*mup[1])
        if which == "C":
            return (base[0]+nu[0], base[1]+nu[1]), (dbase[0]+nup[0], dbase[1]+nup[1])
        return base, dbase


def area(traj, p, dps=30, b0=None):
    pi2 = mp.pi / 2
    half = mp.mpf('0.5')

    def val(t, which):
        return contact_wd(traj, t, which)[0]

    if b0 is None:
        b0 = [p['theta'], pi2 - p['phi'], p['phi'], pi2 - p['theta']]

    def junc(bD, bx2, bx1, bB):
        D = val(bD, "D"); x2 = traj(bx2)[0]; x1 = traj(bx1)[0]; B = val(bB, "B")
        return [D[0]-x2[0], D[1]-x2[1], x1[0]-B[0], x1[1]-B[1]]
    sol = mp.findroot(lambda a, b, c, d: junc(a, b, c, d),
                      [mp.mpf(v) for v in b0], tol=mp.mpf(10)**(-(dps-4)))
    bD, bx2, bx1, bB = [sol[i] for i in range(4)]

    def integ(which):
        def f(t):
            v, dv = contact_wd(traj, t, which)
            return v[0]*dv[1] - v[1]*dv[0]
        return f

    def x_integ(t):
        x, xp, _ = traj(t)
        return x[0]*xp[1] - x[1]*xp[0]

    # c_G'' jumps at the four phase boundaries; the contact-path derivative
    # (hence the Green integrand) is kinked there, so mp.quad needs them as
    # interior nodes.  Clip the fixed kink set to each arc's range.
    kinks = [p['phi'], p['theta'], pi2-p['theta'], pi2-p['phi']]

    def nds(lo, hi):
        return [lo] + [k for k in kinks if lo < k < hi] + [hi]

    IA = mp.quad(integ("A"), nds(mp.mpf(0), pi2))
    IC = mp.quad(integ("C"), nds(mp.mpf(0), pi2))
    ID = mp.quad(integ("D"), nds(mp.mpf(0), bD))
    Ix = mp.quad(x_integ, nds(bx1, bx2))
    IB = mp.quad(integ("B"), nds(bB, pi2))
    S = half * (IA + IC + ID - Ix + IB)
    Ae = val(pi2, "A"); C0 = val(mp.mpf(0), "C"); Ce = val(pi2, "C")
    D0 = val(mp.mpf(0), "D"); Be = val(pi2, "B"); A0 = val(mp.mpf(0), "A")
    def seg(u, v): return half*(u[0]*v[1] - v[0]*u[1])
    return S + seg(Ae, C0) + seg(Ce, D0) + seg(Be, A0), (bD, bx2, bx1, bB)


def g_of_eps(p, eps, b, w, comp, dps=30):
    """F(c_G + eps*eta) - F(c_G) at high precision."""
    tr = make_traj(p, mp.mpf(eps), b, w, comp)
    A, _ = area(tr, p, dps=dps)
    return A


if __name__ == "__main__":
    dps = 30
    p, _ = solve_gerver_constants(working_dps=dps, verbose=False)
    mp.mp.dps = dps
    tr0 = make_traj(p, mp.mpf(0), mp.mpf('0.6813'), mp.mpf('0.05'), "x")
    A0, bk = area(tr0, p, dps=dps)
    print("analytic area at c_G (eps=0):", mp.nstr(A0, 18))
    print("true A* =                     2.219531668871967889")
    print("difference:", mp.nstr(A0 - mp.mpf('2.219531668871967889'), 4))
