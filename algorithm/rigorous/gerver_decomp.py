"""gerver_decomp.py — first variation of A_rec, TERM BY TERM.

Six hypotheses for the Part II defect have been killed by measurement (basin
jump, swallowtail, wrong arc list, wrong arc ranges, wrong chord endpoints,
chord-vs-wall-segment).  The arc table is now verified correct at c_G in every
respect, yet dA_rec/deps != 0 while dA_true/deps = 0.

So localize it: A_rec = (1/2)(IA + IC + ID - Ix + IB) + s1 + s2 + s3.
Compute d/deps of EACH term at c_G under a sin(2kt) perturbation and see which
one carries the discrepancy.  Everything else has been ruled out, so exactly
one of these eight numbers must be responsible.

Usage: python3 gerver_decomp.py [k] [comp]
"""
from __future__ import annotations
import os, sys, math
import mpmath as mp

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from analytic_oracle import contact_wd, _xt_full, _solve_junction
from gerver_constants import solve_gerver_constants


def terms(traj, p, dps=30):
    """the eight Green terms of A_rec, separately"""
    pi2 = mp.pi/2
    half = mp.mpf('0.5')

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

    IA = mp.quad(integ("A"), nds(mp.mpf(0), pi2))
    IC = mp.quad(integ("C"), nds(mp.mpf(0), pi2))
    ID = mp.quad(integ("D"), nds(mp.mpf(0), bD))
    Ix = mp.quad(x_integ, nds(bx1, bx2))
    IB = mp.quad(integ("B"), nds(bB, pi2))

    def seg(u, v):
        return half*(u[0]*v[1] - v[0]*u[1])
    s1 = seg(val(pi2, "A"), val(mp.mpf(0), "C"))
    s2 = seg(val(pi2, "C"), val(mp.mpf(0), "D"))
    s3 = seg(val(pi2, "B"), val(mp.mpf(0), "A"))
    names = ["IA/2", "IC/2", "ID/2", "-Ix/2", "IB/2", "seg(Ae,C0)",
             "seg(Ce,D0)", "seg(Be,A0)"]
    vals = [half*IA, half*IC, half*ID, -half*Ix, half*IB, s1, s2, s3]
    return names, vals, (bD, bx2, bx1, bB)


def main():
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    comp = sys.argv[2] if len(sys.argv) > 2 else "y"
    mp.mp.dps = 30
    p, _ = solve_gerver_constants(working_dps=30, verbose=False)

    def mk(eps):
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

    e = mp.mpf('1e-10')
    n0, v0, b0 = terms(mk(mp.mpf(0)), p)
    _, vp, bp = terms(mk(e), p)
    _, vm, bm = terms(mk(-e), p)

    print(f"first variation of A_rec, term by term   "
          f"(mode sin {2*k}t, component {comp})")
    print(f"  A_rec(c_G) = {mp.nstr(sum(v0), 12)}\n")
    print(f"{'term':>12} {'value at c_G':>18} {'d/deps':>16}")
    tot = mp.mpf(0)
    for nm, a, b, c in zip(n0, v0, vp, vm):
        d = (b - c)/(2*e)
        tot += d
        print(f"{nm:>12} {mp.nstr(a, 12):>18} {mp.nstr(d, 8):>16}")
    print(f"{'TOTAL':>12} {'':>18} {mp.nstr(tot, 8):>16}")
    print(f"\njunction motion d/deps: "
          + " ".join(f"{nm}={mp.nstr((x-y)/(2*e), 6)}"
                     for nm, x, y in zip(("bD", "bx2", "bx1", "bB"), bp, bm)))


if __name__ == "__main__":
    main()
