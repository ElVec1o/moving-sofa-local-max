"""gerver_rankone.py — the Part II defect is exactly RANK ONE.

Measured claim:  for every perturbation eta vanishing at t = 0 and pi/2,

    dA_rec/deps |_{c_G}  =  a * L(eta),     L(eta) = eta_x'(0) + eta_x'(pi/2),
    a = -(x_B - x_D)/4 = -0.4034408,

while dA_true/deps = 0.  a was fitted from the pure sin-mode family alone.
This script tests the law on RANDOM mixed directions it was never fitted to:
if the law holds there, the defect is a single linear functional, i.e. the
reconstruction fails in exactly ONE direction of the tangent space and is
stationary on the codimension-1 subspace ker L.

Usage: python3 gerver_rankone.py [n_trials] [K]
"""
from __future__ import annotations
import os, sys, math
import numpy as np
import mpmath as mp

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from gerver_gauge import area_rec
from analytic_oracle import _xt_full
from gerver_constants import solve_gerver_constants

A_FIT = mp.mpf('-0.40344081')


def main():
    nt = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    mp.mp.dps = 30
    p, _ = solve_gerver_constants(working_dps=30, verbose=False)
    rng = np.random.default_rng(20260729)

    def mk(eps, ax, ay):
        def traj(t):
            x, xp, xpp = _xt_full(t, p)
            sx = sxp = sxpp = mp.mpf(0)
            sy = syp = sypp = mp.mpf(0)
            for k in range(1, K+1):
                s = mp.sin(2*k*t); c = mp.cos(2*k*t)
                sx += ax[k-1]*s;  sxp += ax[k-1]*2*k*c
                sxpp -= ax[k-1]*(2*k)**2*s
                sy += ay[k-1]*s;  syp += ay[k-1]*2*k*c
                sypp -= ay[k-1]*(2*k)**2*s
            return ((x[0]+eps*sx, x[1]+eps*sy),
                    (xp[0]+eps*sxp, xp[1]+eps*syp),
                    (xpp[0]+eps*sxpp, xpp[1]+eps*sypp))
        return traj

    e = mp.mpf('1e-10')
    print(f"RANK-ONE TEST of the Part II defect   (K={K}, random mixed "
          f"directions)")
    print(f"  law:  dA_rec/deps = a*L,   L = eta_x'(0)+eta_x'(pi/2),  "
          f"a = {mp.nstr(A_FIT, 9)}")
    print(f"  a was fitted from the PURE sin-mode family only.\n")
    print(f"{'trial':>6} {'L(eta)':>14} {'predicted':>15} {'measured':>15}"
          f" {'rel err':>11}")
    worst = mp.mpf(0)
    for i in range(nt):
        ax = [mp.mpf(float(v)) for v in rng.standard_normal(K)]
        ay = [mp.mpf(float(v)) for v in rng.standard_normal(K)]
        L = sum(ax[k-1]*(2*k + 2*k*(-1)**k) for k in range(1, K+1))
        pred = A_FIT*L
        d = (area_rec(mk(e, ax, ay), p) - area_rec(mk(-e, ax, ay), p))/(2*e)
        rel = abs((d - pred)/pred) if pred != 0 else abs(d)
        worst = max(worst, rel)
        print(f"{i:>6} {mp.nstr(L, 8):>14} {mp.nstr(pred, 8):>15} "
              f"{mp.nstr(d, 8):>15} {mp.nstr(rel, 3):>11}")
    print(f"\nworst relative error over {nt} random directions: "
          f"{mp.nstr(worst, 3)}")
    print("VERDICT:", "RANK-ONE LAW CONFIRMED — the defect is the single "
          "functional L." if worst < mp.mpf('1e-3') else
          "law does not hold on general directions")


if __name__ == "__main__":
    main()
