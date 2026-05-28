"""
sofa_ambidextrous_v2.py
=======================

CORRECTED Romik-formulation ambidextrous moving sofa.

Bug found in v1:  I used y-mirror across y=0, producing two hallways
with disjoint horizontal corridors.  Romik uses y-mirror across
y = 1/2 (the corridor centerline), so both hallways share the same
horizontal corridor.

This is the geometrically correct formulation.  Expected: optimum
near Romik's 1.64495.  Anything above that with motion verification
would be a genuine exceedance.
"""

from __future__ import annotations

import math, time
import numpy as np
from shapely.geometry import Polygon as SPoly
from shapely.affinity import rotate as srot, translate as strans, scale as sscale

from sofa_bvp import HALLWAY, make_trajectory


# Corrected: mirror across y = 1/2, NOT y = 0
HALLWAY_L = HALLWAY
HALLWAY_R_CORRECT = sscale(HALLWAY, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))


def sofa_ambidextrous_corrected(c_x, c_y, n_theta: int = 181):
    """
    S = ∩_θ R(-θ)(H_L - c_L(θ))  ∩  ∩_θ R(+θ)(H_R - c_R(θ))

    with H_R = mirror_{y=1/2}(H_L) and the mirror trajectory
    c_R(θ) = (c_x(θ), 1 - c_y(θ))   (i.e. y-reflected across y=1/2).
    """
    thetas = np.linspace(0.0, math.pi / 2, n_theta)
    S = None
    for th in thetas:
        cx, cy = c_x(th), c_y(th)
        # Left family
        Hb_L = strans(HALLWAY_L, xoff=-cx, yoff=-cy)
        Hb_L = srot(Hb_L, -math.degrees(th), origin=(0, 0))
        # Right family — mirror trajectory: y -> 1 - y
        cy_mirror = 1.0 - cy
        Hb_R = strans(HALLWAY_R_CORRECT, xoff=-cx, yoff=-cy_mirror)
        Hb_R = srot(Hb_R, +math.degrees(th), origin=(0, 0))
        slab = Hb_L.intersection(Hb_R)
        S = slab if S is None else S.intersection(slab)
        if S.is_empty or S.area < 1e-10:
            return S, 0.0
    return S, S.area


def neg_area_corrected(params, n_modes, n_theta):
    try:
        x_of, y_of = make_trajectory(params, n_modes=n_modes)
        _, A = sofa_ambidextrous_corrected(x_of, y_of, n_theta=n_theta)
        return -A
    except Exception:
        return 0.0


def main():
    print("=" * 72)
    print("Corrected ambidextrous moving sofa (Romik formulation)")
    print("=" * 72)
    print("  Target: Romik 2018 candidate area 1.64495")
    print()

    # Sanity: zero trajectory
    print("[sanity] trajectory pinned at (0, 0):")
    _, A0 = sofa_ambidextrous_corrected(lambda t: 0.0, lambda t: 0.0, n_theta=181)
    print(f"  area = {A0:.5f}")

    print("[sanity] trajectory pinned at corridor centerline (0, 0.5):")
    _, A0b = sofa_ambidextrous_corrected(lambda t: 0.0, lambda t: 0.5, n_theta=181)
    print(f"  area = {A0b:.5f}")

    # Staged optimisation
    from scipy.optimize import minimize
    import cma

    def staged():
        n_modes = 4
        x0 = np.zeros(2 + 2 * n_modes)
        x0[0] = 2.0 / math.pi
        x0[1] = 0.5   # centered on corridor centerline by symmetry expectation

        for nm in [4, 8, 12, 16]:
            print(f"\n[opt] n_modes = {nm}")
            t0 = time.time()
            if nm > 4:
                p_new = np.zeros(2 + 2 * nm)
                p_new[0] = x0[0]; p_new[1] = x0[1]
                old_nm = (len(x0) - 2) // 2
                ncp = min(old_nm, nm)
                p_new[2:2 + ncp] = x0[2:2 + ncp]
                p_new[2 + nm:2 + nm + ncp] = x0[2 + old_nm:2 + old_nm + ncp]
                x0 = p_new
            res = minimize(
                neg_area_corrected, x0, args=(nm, 121),
                method="Nelder-Mead",
                options=dict(xatol=1e-5, fatol=1e-5, maxiter=2000, disp=False),
            )
            x0 = res.x
            A_coarse = -res.fun
            print(f"  NM coarse area = {A_coarse:.5f}  ({time.time()-t0:.1f}s)")

            t0 = time.time()
            es = cma.CMAEvolutionStrategy(
                list(x0), 0.1,
                {'maxiter': 80, 'verbose': -9, 'seed': 42 + nm,
                 'tolfun': 1e-7, 'popsize': 20},
            )
            while not es.stop():
                sols = es.ask()
                fits = [neg_area_corrected(s, nm, 121) for s in sols]
                es.tell(sols, fits)
            if -es.result.fbest > A_coarse:
                x0 = es.result.xbest
                A_coarse = -es.result.fbest
            print(f"  CMA polish area = {A_coarse:.5f}  ({time.time()-t0:.1f}s)")

        return x0, nm

    x_final, n_modes = staged()
    x_of, y_of = make_trajectory(x_final, n_modes=n_modes)
    print("\nDense verification:")
    for n_dense in [181, 361, 721, 1441, 2001]:
        _, A_d = sofa_ambidextrous_corrected(x_of, y_of, n_theta=n_dense)
        print(f"  n_theta={n_dense:4d}  area = {A_d:.6f}")
    A_final = A_d

    print("\n" + "=" * 72)
    print("Honest summary (CORRECTED formulation)")
    print("=" * 72)
    ROMIK = 1.64495
    print(f"  Romik 2018 candidate:   {ROMIK:.5f}")
    print(f"  Our dense area:         {A_final:.5f}")
    print(f"  delta vs Romik:         {A_final - ROMIK:+.5f}")
    if A_final > ROMIK + 1e-3:
        print("  >>> EXCEEDS Romik by > 1e-3.  Needs motion verification.")
    elif abs(A_final - ROMIK) < 1e-3:
        print("  >>> Matches Romik to ~1e-3.  Pipeline reproduces his number.")
    else:
        print("  >>> Below Romik.  Likely local optimum;  retry with more restarts.")


if __name__ == "__main__":
    main()
