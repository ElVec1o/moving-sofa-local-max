"""
sofa_bvp.py
===========

Intersection-of-rotated-hallways formulation of the moving sofa
(Romik 2018).  Given a corner-trajectory c(theta) = (x(theta), y(theta))
for theta in [0, pi/2], the body-frame sofa is

    S = intersection over theta of  R(-theta) ( H - c(theta) )

where H is the L-hallway.  Maximising area(S) over admissible c(theta)
is the moving-sofa problem in trajectory-space.

This file:
  1. Builds the polygon-intersection evaluator (Shapely).
  2. Verifies on Hammersley's trajectory (known area pi/2 + 2/pi).
  3. Parameterises c(theta) with a Fourier series and runs scipy.
  4. Reports the actual area achieved.  No cheating: the number is
     whatever it is.
"""

from __future__ import annotations

import math
import time
from typing import Callable, Tuple

import numpy as np
from shapely.geometry import Polygon as SPoly
from shapely.affinity import rotate as srot, translate as strans
from shapely.ops import unary_union


# ---------------------------------------------------------------------
#  L-hallway as a (bounded) Shapely polygon
# ---------------------------------------------------------------------
#  H = ([-K, 1] x [0, 1])  U  ([0, 1] x [-K, 1])
#  i.e. unit-width horizontal corridor extending to x = -K joined to
#  a unit-width vertical corridor extending to y = -K, sharing the
#  inner unit square [0,1]^2.
#
#  This is the *standard* sofa-problem L (with the inner corner
#  region; not the tight L used in moving_sofa_tools.py).

K_BIG = 8.0  # extent of each corridor away from the corner

def _hallway_poly(K: float = K_BIG) -> SPoly:
    horiz = SPoly([(-K, 0), (1, 0), (1, 1), (-K, 1)])
    vert  = SPoly([(0, -K), (1, -K), (1, 1), (0, 1)])
    return unary_union([horiz, vert])


HALLWAY = _hallway_poly()


# ---------------------------------------------------------------------
#  Sofa area given a corner trajectory
# ---------------------------------------------------------------------

def sofa_from_trajectory(
    x_of_theta: Callable[[float], float],
    y_of_theta: Callable[[float], float],
    n_theta: int = 181,
) -> Tuple[SPoly, float]:
    """Compute S = ∩_theta R(-theta)(H - c(theta)).

    Returns (polygon, area).  Empty polygon -> area 0.
    """
    thetas = np.linspace(0.0, math.pi / 2, n_theta)
    S = None
    for th in thetas:
        cx = x_of_theta(th)
        cy = y_of_theta(th)
        # Body-frame hallway at angle theta:
        # 1. translate world hallway by -c(theta) (corner -> origin)
        # 2. rotate by -theta around origin (de-rotate)
        Hb = strans(HALLWAY, xoff=-cx, yoff=-cy)
        Hb = srot(Hb, -math.degrees(th), origin=(0, 0))
        S = Hb if S is None else S.intersection(Hb)
        if S.is_empty or S.area < 1e-10:
            return S, 0.0
    return S, S.area


# ---------------------------------------------------------------------
#  Reference trajectory:  Hammersley
# ---------------------------------------------------------------------
#  Hammersley's sofa corresponds to the corner travelling along a
#  half-circle of radius 2/pi.  Specifically the (world-frame) corner
#  trajectory is
#       c(theta) = ((2/pi) sin(theta), (2/pi)(1 - cos(theta)))   ??
#  This is one common parameterisation; we check the resulting area
#  and compare to pi/2 + 2/pi = 2.20741... .

def hammersley_trajectory():
    R = 2.0 / math.pi
    # The corner moves along a circular arc of radius R from
    # theta = 0 to theta = pi/2, centred at (0, R).
    # World corner pose: c(theta) = R (sin theta, 1 - cos theta).
    return (lambda th: R * math.sin(th),
            lambda th: R * (1 - math.cos(th)))


# Gerver's trajectory is piecewise from an ODE system; we don't
# attempt to reproduce it here. We instead parameterise generically
# and let the optimiser search.


# ---------------------------------------------------------------------
#  Generic Fourier-series trajectory  (for optimisation)
# ---------------------------------------------------------------------
#  c(theta) = c0 + linear-in-theta drift + sum of sin(2k theta) terms
#  on each component.  Boundary conditions: c(0) and c(pi/2) determine
#  the start/end pose.  We fix c(0) = (0, 0) and let the rest float.

def make_trajectory(params: np.ndarray, n_modes: int = 4):
    """params layout (length 2 + 2*n_modes):
       [ ax_end, ay_end, sx_1..sx_n, sy_1..sy_n ]
       linear drift + sine modes vanishing at theta=0.
    """
    ax_end = params[0]
    ay_end = params[1]
    sx = params[2 : 2 + n_modes]
    sy = params[2 + n_modes : 2 + 2 * n_modes]
    half_pi = math.pi / 2

    def x(th):
        s = ax_end * (th / half_pi)
        for k, a in enumerate(sx, start=1):
            s += a * math.sin(2 * k * th)
        return s

    def y(th):
        s = ay_end * (th / half_pi)
        for k, a in enumerate(sy, start=1):
            s += a * math.sin(2 * k * th)
        return s

    return x, y


# ---------------------------------------------------------------------
#  Optimisation
# ---------------------------------------------------------------------

def neg_area(params, n_modes=4, n_theta=121):
    x, y = make_trajectory(params, n_modes=n_modes)
    try:
        _, A = sofa_from_trajectory(x, y, n_theta=n_theta)
    except Exception:
        return 0.0
    return -A


def optimize_trajectory(n_modes=4, n_theta=121,
                        warm_start=None, seed=0,
                        maxiter=200):
    from scipy.optimize import minimize
    rng = np.random.default_rng(seed)
    n_params = 2 + 2 * n_modes
    if warm_start is None:
        # Initial guess: a Hammersley-like linear-only motion
        x0 = np.zeros(n_params)
        x0[0] = 2.0 / math.pi    # ax_end
        x0[1] = 2.0 / math.pi    # ay_end
    else:
        x0 = warm_start
    print(f"  optimising {n_params} params (n_modes={n_modes}, "
          f"n_theta={n_theta}) ...")
    res = minimize(
        neg_area, x0, args=(n_modes, n_theta),
        method="Nelder-Mead",
        options=dict(xatol=1e-4, fatol=1e-4, maxiter=maxiter, disp=True),
    )
    return res


# ---------------------------------------------------------------------
#  Main
# ---------------------------------------------------------------------

def main():
    print("=" * 70)
    print("Moving sofa via intersection-of-rotated-hallways (Romik form)")
    print("=" * 70)

    # --- Sanity check 1: a stationary corner -> sofa is just the L corner ---
    print("\n[1] Sanity: trivial trajectory c(theta) = (0, 0).")
    print("    Body-frame sofa = intersection of rotated L-shapes pivoting")
    print("    around the corner; should be small.")
    t0 = time.time()
    _, A = sofa_from_trajectory(lambda t: 0.0, lambda t: 0.0, n_theta=91)
    print(f"    area = {A:.5f}  (time {time.time()-t0:.2f}s)")

    # --- Sanity check 2: Hammersley trajectory ---
    print("\n[2] Hammersley trajectory  c(theta)=R(sin t, 1-cos t),"
          " R=2/pi.")
    print(f"    Hammersley's reported area: pi/2 + 2/pi = "
          f"{math.pi/2 + 2/math.pi:.5f}")
    fx, fy = hammersley_trajectory()
    t0 = time.time()
    _, A_h = sofa_from_trajectory(fx, fy, n_theta=181)
    print(f"    computed area = {A_h:.5f}  (time {time.time()-t0:.2f}s)")

    # --- Run optimiser ---
    print("\n[3] Optimising a 4-mode Fourier trajectory  (Nelder-Mead).")
    t0 = time.time()
    res = optimize_trajectory(n_modes=4, n_theta=91, maxiter=400)
    A_opt = -res.fun
    print(f"\n    optimiser final area = {A_opt:.5f}   "
          f"(time {time.time()-t0:.1f}s)")
    print(f"    params: {np.round(res.x, 4)}")

    # --- Push to more modes if it looks promising ---
    print("\n[4] Refining with 8-mode trajectory, warm-started.")
    n_modes2 = 8
    p0 = np.zeros(2 + 2 * n_modes2)
    # copy lower modes
    p0[0] = res.x[0]; p0[1] = res.x[1]
    p0[2:2+4] = res.x[2:6]
    p0[2+n_modes2:2+n_modes2+4] = res.x[6:10]
    t0 = time.time()
    res2 = optimize_trajectory(n_modes=n_modes2, n_theta=121,
                                warm_start=p0, maxiter=4000)
    A_opt2 = -res2.fun
    print(f"\n    refined area = {A_opt2:.5f}   "
          f"(time {time.time()-t0:.1f}s)")

    # --- Push further: 12 modes, longer run ---
    print("\n[5] Final push: 12-mode trajectory, long run.")
    n_modes3 = 12
    p0b = np.zeros(2 + 2 * n_modes3)
    p0b[0] = res2.x[0]; p0b[1] = res2.x[1]
    p0b[2:2+n_modes2] = res2.x[2:2+n_modes2]
    p0b[2+n_modes3:2+n_modes3+n_modes2] = res2.x[2+n_modes2:2+2*n_modes2]
    t0 = time.time()
    res3 = optimize_trajectory(n_modes=n_modes3, n_theta=181,
                                warm_start=p0b, maxiter=8000)
    A_opt3 = -res3.fun
    print(f"\n    12-mode refined area = {A_opt3:.5f}   "
          f"(time {time.time()-t0:.1f}s)")

    print("\n" + "=" * 70)
    print("Honest summary")
    print("=" * 70)
    print(f"  Hammersley reference  : 2.20741")
    print(f"  Hammersley (our eval) : {A_h:.5f}")
    print(f"  4-mode optimum        : {A_opt:.5f}")
    print(f"  8-mode optimum        : {A_opt2:.5f}")
    print(f"  12-mode optimum       : {A_opt3:.5f}")
    print(f"  Gerver constant       : 2.21953")
    print(f"  Upper bound (Baek)    : 2.37")


if __name__ == "__main__":
    main()
