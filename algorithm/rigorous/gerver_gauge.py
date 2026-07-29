"""gerver_gauge.py — the Part II defect is a BROKEN GAUGE SYMMETRY.

The sofa  S(c) = intersection_t H_{t,c(t)}  depends only on the SET of
hallways, not on how the rotation is parametrised.  So the true area is
invariant under reparametrisation

    c(t)  -->  c(t + eps s(t)),      s(0) = s(pi/2) = 0,

i.e. dA_true = 0 along every gauge direction  eta = s c'.  This is an exact,
infinite-dimensional symmetry of the functional.

The reconstruction A_rec is NOT invariant: it integrates Green's form along
CONTACT ARCS parametrised by t, and near t = 0 and t = pi/2 the hallway touches
the sofa along a SEGMENT rather than a point (arc A is identically the wall
y = 0 on [0,phi], arc C on [pi/2-phi,pi/2]).  There the "contact point" is a
spurious selection, and reparametrising slides it along the segment, changing
A_rec at first order.

PREDICTION.  The measured defect is  dA_rec = a (eta_x'(0) + eta_x'(pi/2)),
a = -0.4034408.  If the mechanism is gauge-breaking, then for a gauge direction
eta = s c' this must equal

    a ( s'(0) c_x'(0) + s'(pi/2) c_x'(pi/2) ).

This script tests that on gauge directions never used to fit a, and checks the
true area is flat along them.

Usage: python3 gerver_gauge.py
"""
from __future__ import annotations
import os, sys, math, subprocess
import numpy as np
import mpmath as mp

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from analytic_oracle import contact_wd, _xt_full, _solve_junction
from gerver_constants import solve_gerver_constants

A_FIT = mp.mpf('-0.4034408')


def area_rec(traj, p, dps=30):
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
    S = half*(mp.quad(integ("A"), nds(mp.mpf(0), pi2))
              + mp.quad(integ("C"), nds(mp.mpf(0), pi2))
              + mp.quad(integ("D"), nds(mp.mpf(0), bD))
              - mp.quad(x_integ, nds(bx1, bx2))
              + mp.quad(integ("B"), nds(bB, pi2)))

    def seg(u, v):
        return half*(u[0]*v[1] - v[0]*u[1])
    return (S + seg(val(pi2, "A"), val(mp.mpf(0), "C"))
              + seg(val(pi2, "C"), val(mp.mpf(0), "D"))
              + seg(val(pi2, "B"), val(mp.mpf(0), "A")))


def main():
    mp.mp.dps = 30
    p, _ = solve_gerver_constants(working_dps=30, verbose=False)
    pi2 = mp.pi/2

    # gauge directions: c(t + eps s(t)) with s vanishing at both ends
    GAUGE = [("sin 2t", lambda t: mp.sin(2*t), lambda t: 2*mp.cos(2*t),
              lambda t: -4*mp.sin(2*t)),
             ("sin 4t", lambda t: mp.sin(4*t), lambda t: 4*mp.cos(4*t),
              lambda t: -16*mp.sin(4*t)),
             ("t(pi/2-t)", lambda t: t*(pi2-t), lambda t: pi2 - 2*t,
              lambda t: mp.mpf(-2)),
             ("sin^2 2t", lambda t: mp.sin(2*t)**2,
              lambda t: 2*mp.sin(4*t), lambda t: 8*mp.cos(4*t))]

    def mk(eps, s, sp, spp):
        """traj for c(t + eps s(t)); chain rule to SECOND order (the eps*s''
        term in c'' is first-order and must not be dropped)"""
        def traj(t):
            u = t + eps*s(t)
            x, xp, xpp = _xt_full(u, p)
            du = 1 + eps*sp(t); d2u = eps*spp(t)
            return (x, (xp[0]*du, xp[1]*du),
                    (xpp[0]*du*du + xp[0]*d2u, xpp[1]*du*du + xp[1]*d2u))
        return traj

    cp0 = _xt_full(mp.mpf(0), p)[1]
    cp1 = _xt_full(pi2, p)[1]
    print("GAUGE TEST — is the Part II defect the broken reparametrisation "
          "symmetry?\n")
    print(f"  c'(0)     = ({mp.nstr(cp0[0], 8)}, {mp.nstr(cp0[1], 8)})")
    print(f"  c'(pi/2)  = ({mp.nstr(cp1[0], 8)}, {mp.nstr(cp1[1], 8)})")
    print(f"  fitted a  = {mp.nstr(A_FIT, 8)}   (from the sin-mode family "
          f"ONLY)\n")
    e = mp.mpf('1e-10')
    print(f"{'gauge s(t)':>12} {'predicted a*L':>16} {'measured dA_rec':>17}"
          f" {'rel err':>10}")
    for nm, s, sp, spp in GAUGE:
        L = sp(mp.mpf(0))*cp0[0] + sp(pi2)*cp1[0]
        pred = A_FIT*L
        d = (area_rec(mk(e, s, sp, spp), p)
             - area_rec(mk(-e, s, sp, spp), p))/(2*e)
        rel = abs((d - pred)/pred) if pred != 0 else abs(d)
        print(f"{nm:>12} {mp.nstr(pred, 8):>16} {mp.nstr(d, 8):>17} "
              f"{mp.nstr(rel, 3):>10}")

    # true area along the same gauge directions, exact Rust oracle
    print("\n  and the TRUE area along the same directions "
          "(exact Rust oracle):")
    n = 4801
    th = np.linspace(0, math.pi/2, n)
    cx = np.empty(n); cy = np.empty(n)
    for i, t in enumerate(th):
        x, _, _ = _xt_full(mp.mpf(t), p)
        cx[i] = float(x[0]); cy[i] = float(x[1])

    def areas(trajs):
        inp = [f"{n} {len(trajs)}", " ".join(f"{t:.17g}" for t in th)]
        for a, b in trajs:
            inp.append(" ".join(f"{u:.17g} {v:.17g}" for u, v in zip(a, b)))
        r = subprocess.run([os.path.join(THIS, "sigma_area")],
                           input="\n".join(inp), capture_output=True,
                           text=True, env=dict(os.environ, GERVER="1"))
        return [float(x) for x in r.stdout.split()]
    E = 1e-5
    for nm, s, sp, spp in GAUGE:
        sv = np.array([float(s(mp.mpf(t))) for t in th])
        out = []
        for sg in (+1, -1):
            u = th + sg*E*sv
            u = np.clip(u, 0.0, math.pi/2)
            gx = np.empty(n); gy = np.empty(n)
            for i, t in enumerate(u):
                x, _, _ = _xt_full(mp.mpf(t), p)
                gx[i] = float(x[0]); gy[i] = float(x[1])
            out.append((gx, gy))
        Ap, Am = areas(out)
        print(f"{nm:>12}   dA_true/deps = {(Ap-Am)/(2*E):+.5f}")


if __name__ == "__main__":
    main()
