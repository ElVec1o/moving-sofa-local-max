"""gerver_fixed.py — THE REPAIR of Part II's reconstruction.

DIAGNOSIS (measured, this session).  A_rec closes the sofa boundary with three
chords and solves FOUR moving junctions (bD, bx2, bx1, bB).  But it pins arc A
to start at t=0 and arc C to end at t=pi/2.  At c_G that is correct: A(0) and
C(pi/2) sit exactly on the wall line y=0.  Under an x-perturbation they do not:

    d/deps A(0)_y     = eta'(0),
    d/deps C(pi/2)_y  = eta'(pi/2),

measured to 6 digits.  So the two bottom chords stop lying along y=0 and pick
up a first-order area sliver

    d/deps [ seg(C(pi/2),D(0)) + seg(B(pi/2),A(0)) ]
        = -(1/2) x_D eta'(pi/2) + (1/2) x_B eta'(0),

which with x_D = -1.42064, x_B = 0.19312 reproduces the observed defect
exactly.  Net:  dA_rec/deps = -0.4034408 (eta'(0) + eta'(pi/2)),  while
dA_true/deps = 0.  Hence A_rec is NOT stationary at c_G and the superset
property fails at first order in half the x-modes.

THE FIX.  Treat the two wall contacts as junctions too: solve

    a0  near 0     with  A(a0)_y = 0,
    c1  near pi/2  with  C(c1)_y = 0,

integrate arc A over [a0, pi/2] and arc C over [0, c1], and close with the
chords at the MOVED endpoints (which then lie on y=0, so both bottom chords
contribute 0 identically).  Six junctions, not four.

This script builds the repaired A_fix and checks (i) A_fix(c_G) = A* and
(ii) dA_fix/deps = 0 on the modes where A_rec failed.

Usage: python3 gerver_fixed.py [kmax]
"""
from __future__ import annotations
import os, sys, math
import mpmath as mp

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from analytic_oracle import contact_wd, _xt_full, _solve_junction
from gerver_constants import solve_gerver_constants


def wall_junction(traj, which, t0, dps=30):
    """solve  arc_which(t)_y = 0  by Newton, started at t0"""
    t = mp.mpf(t0)
    for _ in range(60):
        v, dv = contact_wd(traj, t, which)
        if dv[1] == 0:
            break
        step = v[1]/dv[1]
        t = t - step
        if abs(step) < mp.mpf(10)**(-dps+4):
            break
    return t


def area_fixed(traj, p, dps=30, fix=True):
    """A_fix (fix=True) or the original A_rec (fix=False)"""
    pi2 = mp.pi/2
    half = mp.mpf('0.5')

    def val(t, w):
        return contact_wd(traj, t, w)[0]

    b0 = [p['theta'], pi2 - p['phi'], p['phi'], pi2 - p['theta']]
    bD, bx2 = _solve_junction(traj, "D", b0[0], b0[1], dps)
    bx1, bB = _solve_junction(traj, "B", b0[3], b0[2], dps)[::-1]
    if fix:
        a0 = wall_junction(traj, "A", mp.mpf(0), dps)
        c1 = wall_junction(traj, "C", pi2, dps)
    else:
        a0, c1 = mp.mpf(0), pi2

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

    IA = mp.quad(integ("A"), nds(a0, pi2))
    IC = mp.quad(integ("C"), nds(mp.mpf(0), c1))
    ID = mp.quad(integ("D"), nds(mp.mpf(0), bD))
    Ix = mp.quad(x_integ, nds(bx1, bx2))
    IB = mp.quad(integ("B"), nds(bB, pi2))
    S = half*(IA + IC + ID - Ix + IB)

    def seg(u, v):
        return half*(u[0]*v[1] - v[0]*u[1])
    return (S + seg(val(pi2, "A"), val(mp.mpf(0), "C"))
              + seg(val(c1, "C"), val(mp.mpf(0), "D"))
              + seg(val(pi2, "B"), val(a0, "A"))), (a0, c1)


def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    mp.mp.dps = 30
    p, _ = solve_gerver_constants(working_dps=30, verbose=False)
    pi2 = mp.pi/2

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

    A0, (a0, c1) = area_fixed(mk(mp.mpf(0), 1, "x"), p)
    ASTAR = mp.mpf('2.2195316688')
    print("REPAIRED RECONSTRUCTION  (six junctions, not four)")
    print(f"  A_fix(c_G)  = {mp.nstr(A0, 12)}")
    print(f"  A*          = {mp.nstr(ASTAR, 11)}     "
          f"difference {mp.nstr(A0-ASTAR, 3)}")
    print(f"  wall junctions at c_G: a0 = {mp.nstr(a0, 6)}  "
          f"c1 = {mp.nstr(c1, 8)}  (pi/2 = {mp.nstr(pi2, 8)})\n")

    e = mp.mpf('1e-10')
    print(f"{'mode':>10} {'dA_rec/deps':>15} {'dA_fix/deps':>15}   verdict")
    ok = True
    for comp in ("x", "y"):
        for k in range(1, kmax+1):
            rp, _ = area_fixed(mk(e, k, comp), p, fix=False)
            rm, _ = area_fixed(mk(-e, k, comp), p, fix=False)
            fp, _ = area_fixed(mk(e, k, comp), p, fix=True)
            fm, _ = area_fixed(mk(-e, k, comp), p, fix=True)
            dr = (rp-rm)/(2*e); df = (fp-fm)/(2*e)
            good = abs(df) < mp.mpf('1e-6')
            ok = ok and good
            print(f"  {comp} sin{2*k:2d}t {mp.nstr(dr, 8):>15} "
                  f"{mp.nstr(df, 8):>15}   {'OK' if good else '*** FAILS ***'}")
    print(f"\nVERDICT: the repaired reconstruction is "
          f"{'STATIONARY at c_G on every mode tested' if ok else 'STILL DEFECTIVE'}")


if __name__ == "__main__":
    main()
