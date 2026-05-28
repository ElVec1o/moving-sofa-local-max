"""
Motion-simulation verification for the CORRECTED ambidextrous formulation.

If this passes, we have a genuine ambidextrous sofa with area > 1.645,
exceeding Romik's conjectured optimum by ~9%.

Critical sanity:
  1. Re-derive the optimal trajectory under v2 formulation.
  2. Compute the body-frame sofa S at dense n_theta.
  3. Simulate R(theta) S + c(theta) for theta in [0, pi/2] -- must lie in H_L.
  4. Simulate R(-theta) S + (c_x, 1 - c_y)(theta) -- must lie in H_R = mirror_{y=1/2}(H_L).

Both 3 and 4 must pass at every sampled angle.
"""

from __future__ import annotations

import math, time
import numpy as np
from shapely.affinity import rotate as srot, translate as strans, scale as sscale

from sofa_bvp import HALLWAY, make_trajectory
from sofa_ambidextrous_v2 import (
    HALLWAY_L, HALLWAY_R_CORRECT,
    sofa_ambidextrous_corrected,
    neg_area_corrected,
)


def reoptimize_v2(target_modes=12):
    from scipy.optimize import minimize
    import cma

    n_modes = 4
    x0 = np.zeros(2 + 2*n_modes)
    x0[0] = 2.0/math.pi
    x0[1] = 0.5

    for nm in [4, 8, target_modes]:
        if nm > 4:
            p_new = np.zeros(2 + 2*nm)
            p_new[0] = x0[0]; p_new[1] = x0[1]
            old_nm = (len(x0) - 2) // 2
            ncp = min(old_nm, nm)
            p_new[2:2+ncp] = x0[2:2+ncp]
            p_new[2+nm:2+nm+ncp] = x0[2+old_nm:2+old_nm+ncp]
            x0 = p_new
        res = minimize(neg_area_corrected, x0, args=(nm, 121),
                       method="Nelder-Mead",
                       options=dict(xatol=1e-5, fatol=1e-5, maxiter=2000, disp=False))
        x0 = res.x
        es = cma.CMAEvolutionStrategy(list(x0), 0.1,
            {'maxiter': 60, 'verbose': -9, 'seed': 42 + nm,
             'tolfun': 1e-7, 'popsize': 20})
        while not es.stop():
            sols = es.ask()
            fits = [neg_area_corrected(s, nm, 121) for s in sols]
            es.tell(sols, fits)
        if -es.result.fbest > -res.fun:
            x0 = es.result.xbest
        print(f"  v2 reopt n_modes={nm}  area={-min(res.fun, es.result.fbest):.5f}")
    return x0, target_modes


def check_motion_v2(S, c_x, c_y, n_theta: int, mirror: bool):
    thetas = np.linspace(0, math.pi/2, n_theta)
    H = HALLWAY_R_CORRECT if mirror else HALLWAY_L
    n_fail = 0
    worst_excess = 0.0
    failures = []
    for th in thetas:
        if not mirror:
            ang_deg = math.degrees(th)
            shift = (c_x(th), c_y(th))
        else:
            ang_deg = -math.degrees(th)
            shift = (c_x(th), 1.0 - c_y(th))  # mirror trajectory across y=0.5
        Sw = srot(S, ang_deg, origin=(0, 0))
        Sw = strans(Sw, xoff=shift[0], yoff=shift[1])
        outside = Sw.difference(H)
        excess = outside.area
        if excess > 1e-8:
            n_fail += 1
            if excess > worst_excess:
                worst_excess = excess
            if len(failures) < 5:
                failures.append((th, excess))
    return n_fail, worst_excess, failures


def main():
    print("="*72)
    print("CORRECTED ambidextrous: motion-simulation verification")
    print("="*72)

    print("\n[1] Re-optimising v2 trajectory...")
    t0 = time.time()
    params, n_modes = reoptimize_v2(target_modes=12)
    fx, fy = make_trajectory(params, n_modes=n_modes)
    print(f"  ({time.time()-t0:.1f}s)")

    print("\n[2] Body-frame sofa at n_theta=2001...")
    S, A = sofa_ambidextrous_corrected(fx, fy, n_theta=2001)
    print(f"  area = {A:.6f}")

    print("\n[3] Motion through H_L (right-turn, n_theta=2001)...")
    n_fL, exc_L, fL = check_motion_v2(S, fx, fy, n_theta=2001, mirror=False)
    if n_fL == 0:
        print("  PASS — 0/2001 failures, worst excess <= 1e-8")
    else:
        print(f"  FAIL — {n_fL}/2001 failures, worst excess = {exc_L:.6f}")
        for th, e in fL: print(f"    theta={math.degrees(th):6.2f}deg  excess={e:.5f}")

    print("\n[4] Motion through H_R = mirror_{y=1/2}(H_L) (n_theta=2001)...")
    n_fR, exc_R, fR = check_motion_v2(S, fx, fy, n_theta=2001, mirror=True)
    if n_fR == 0:
        print("  PASS — 0/2001 failures, worst excess <= 1e-8")
    else:
        print(f"  FAIL — {n_fR}/2001 failures, worst excess = {exc_R:.6f}")
        for th, e in fR: print(f"    theta={math.degrees(th):6.2f}deg  excess={e:.5f}")

    print("\n" + "="*72)
    print("VERDICT")
    print("="*72)
    print(f"  Sofa area     = {A:.6f}")
    print(f"  Romik 2018    = 1.64495   (conjectured optimum)")
    print(f"  Delta         = {A - 1.64495:+.5f}")
    if n_fL == 0 and n_fR == 0:
        print()
        print("  >>> Body-frame sofa navigates BOTH hallways via")
        print("      c(theta) and mirror_{y=1/2}(c)(theta).")
        print("      Formulation = Romik 2018 ambidextrous.")
        if A > 1.645 + 1e-3:
            print("      AREA EXCEEDS ROMIK by > 1e-3.")
            print("      This is a genuine exceedance candidate.")
    else:
        print("  >>> Motion verification FAILED.  Number is artifact.")


if __name__ == "__main__":
    main()
