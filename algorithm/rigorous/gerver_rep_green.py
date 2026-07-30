"""gerver_rep_green.py — the chord-free reconstruction in GREEN form (fast).

gerver_repaired.curve() assembles the corrected closed curve as a polygon and
shoelaces it.  That is safe (no boundary-term bookkeeping) but costs thousands
of mpmath contact evaluations per area, far too slow for a Hessian.

Here the same curve is integrated term by term with mp.quad, which is both
exact-ish and ~100x faster.  The two must agree; `--check` verifies that.

The curve (see gerver_repaired for the measured facts licensing it):

    A over [phi, pi/2]          (drop the constant piece)
    C over [0, pi/2 - phi]      (drop the constant piece)
    D over [0, bD],  corner over [bx1, bx2] (subtracted),  B over [bB, pi/2]
    top closure     : A(pi/2) -> C(0)                 on y = c_y(0)+1
    left closure    : C(pi/2-phi) -> (xl,yl) -> D(0)   on x = c_x(pi/2)-1 then
                                                          y = c_y(pi/2)
    right closure   : B(pi/2) -> (xr,yr) -> A(phi)     on y = c_y(0) then
                                                          x = c_x(0)+1

Every piece is an envelope arc, the corner path, or a wall line.  No chords.

Usage: python3 gerver_rep_green.py [--check]
"""
from __future__ import annotations
import os, sys, math
import mpmath as mp

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from analytic_oracle import contact_wd, _xt_full, _solve_junction
from gerver_constants import solve_gerver_constants


def area_rep(traj, p, dps=30, chorded=False):
    """chord-free A_rep (chorded=False) or the original A_rec (chorded=True)"""
    pi2 = mp.pi/2
    half = mp.mpf('0.5')
    phi = p['phi']

    def val(t, w):
        return contact_wd(traj, t, w)[0]
    b0 = [p['theta'], pi2 - p['phi'], p['phi'], pi2 - p['theta']]
    bD, bx2 = _solve_junction(traj, "D", b0[0], b0[1], dps)
    bx1, bB = _solve_junction(traj, "B", b0[3], b0[2], dps)[::-1]

    def integ(w):
        def f(t):
            v, dv = contact_wd(traj, t, w)
            return v[0]*dv[1] - v[1]*dv[0]
        return f

    def x_integ(t):
        x, xp, _ = traj(t)
        return x[0]*xp[1] - x[1]*xp[0]
    kinks = [p['phi'], p['theta'], pi2-p['theta'], pi2-p['phi']]

    def nds(lo, hi):
        return [lo] + [k for k in kinks if lo < k < hi] + [hi]

    a_lo = mp.mpf(0) if chorded else phi
    c_hi = pi2 if chorded else pi2 - phi

    S = half*(mp.quad(integ("A"), nds(a_lo, pi2))
              + mp.quad(integ("C"), nds(mp.mpf(0), c_hi))
              + mp.quad(integ("D"), nds(mp.mpf(0), bD))
              - mp.quad(x_integ, nds(bx1, bx2))
              + mp.quad(integ("B"), nds(bB, pi2)))

    def seg(u, v):
        return half*(u[0]*v[1] - v[0]*u[1])

    c0 = traj(mp.mpf(0))[0]
    c1 = traj(pi2)[0]
    out = S + seg(val(pi2, "A"), val(mp.mpf(0), "C"))          # top
    if chorded:
        out += seg(val(pi2, "C"), val(mp.mpf(0), "D"))
        out += seg(val(pi2, "B"), val(mp.mpf(0), "A"))
    else:
        corner_l = (c1[0] - 1, c1[1])
        corner_r = (c0[0] + 1, c0[1])
        out += seg(val(c_hi, "C"), corner_l) + seg(corner_l, val(mp.mpf(0), "D"))
        out += seg(val(pi2, "B"), corner_r) + seg(corner_r, val(a_lo, "A"))
    return out


def main():
    mp.mp.dps = 30
    p, _ = solve_gerver_constants(working_dps=30, verbose=False)
    ASTAR = mp.mpf('2.2195316688')

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

    A0 = area_rep(mk(mp.mpf(0), 1, "x"), p)
    print("CHORD-FREE RECONSTRUCTION, GREEN FORM")
    print(f"  A_rep(c_G) = {mp.nstr(A0, 12)}    A* = {mp.nstr(ASTAR, 11)}"
          f"    diff {mp.nstr(A0-ASTAR, 3)}")
    if "--check" in sys.argv:
        from gerver_repaired import curve
        _, Ap = curve(mk(mp.mpf(0), 1, "x"), p, 4000)
        print(f"  polygon form (n=4000)      = {Ap:.10f}   "
              f"agree to {abs(float(A0)-Ap):.2e}")
    e = mp.mpf('1e-8')
    print("\n  first variation (should be 0 on every mode):")
    for (k, comp) in ((2, "x"), (4, "x"), (6, "x"), (8, "x"), (2, "y"),
                      (5, "y")):
        d = (area_rep(mk(e, k, comp), p) - area_rep(mk(-e, k, comp), p))/(2*e)
        old = (-mp.mpf('0.403440807358')*(2*k + 2*k*(-1)**k)
               if comp == "x" else mp.mpf(0))
        print(f"    {comp} sin{2*k:2d}t   dA_rep = {mp.nstr(d, 6):>14}   "
              f"(chorded law {mp.nstr(old, 6)})")


if __name__ == "__main__":
    main()
