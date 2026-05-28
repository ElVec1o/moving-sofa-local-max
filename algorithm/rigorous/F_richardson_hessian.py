"""
F_richardson_hessian.py
=======================

Use Richardson-extrapolated F[c] (p=1 convergence, validated against
Gerver's A* to 8+ digits) to compute Hessian entries with rigorous
precision.  This is Phase 4 closure attempt #3 — Path B.

Strategy:
  1. F_inf(c) = Richardson extrapolation of F(c, N=128, 256, ..., 8192)
     at p=1.  Target precision: ~10⁻¹¹ after 6 levels.
  2. For Hessian Q[k,k], compute F at c_G, c_G + ε·η_k, c_G - ε·η_k.
     η_k = sin(2(k+1)θ)·ê_x  (the Phase 2 basis).
  3. Q[k,k] = (F(+ε) - 2 F(0) + F(-ε)) / ε².
  4. Compare against Phase 2/4's Shapely Hessian values.

If Q[0,0] computed this way matches Phase 2/4's Q[0,0] ≈ -5.86 within
expected precision, the Phase 2/4 spectrum is empirically validated and
Phase 4 closure is within reach.
"""

from __future__ import annotations
import math, time, sys, os
import numpy as np
import mpmath as mp
from shapely.affinity import rotate as srot, translate as strans

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from sofa_bvp import HALLWAY
from gerver_constants import solve_gerver_constants, _xt_xtp

PUBLISHED_A_STAR = mp.mpf("2.219531668871967889")

mp.mp.dps = 30


# ---------------------------------------------------------------------
# F at a grid (R(+θ)(H) + c convention — validated against A*)
# ---------------------------------------------------------------------

def F_grid(cx, cy, n_theta):
    """body-frame H(θ) = R(+θ)·H_world + c(θ)"""
    thetas = np.linspace(0.0, math.pi/2, n_theta)
    S = None
    for th in thetas:
        Hb = srot(HALLWAY, +math.degrees(th), origin=(0, 0))
        Hb = strans(Hb, xoff=cx(th), yoff=cy(th))
        S = Hb if S is None else S.intersection(Hb)
        if S.is_empty:
            return 0.0
    return S.area


# ---------------------------------------------------------------------
# Richardson extrapolation at p=1
# ---------------------------------------------------------------------

def richardson_p1(values):
    """p=1 Richardson: T_{k+1}[i] = (2^k T_k[i+1] - T_k[i]) / (2^k - 1)
    Returns triangular table; final entry is the best extrapolant."""
    T = [list(values)]
    for k in range(1, len(values)):
        prev = T[-1]
        scale = 2 ** k
        denom = scale - 1
        new = [(scale * prev[i+1] - prev[i]) / denom
               for i in range(len(prev) - 1)]
        T.append(new)
    return T


def F_richardson(cx, cy, base_N=128, levels=6):
    """Compute F at N=base_N, 2*base_N, ..., 2^levels * base_N then extrapolate."""
    Ns = [base_N * 2**k for k in range(levels + 1)]
    Fs = []
    for N in Ns:
        t0 = time.time()
        Fv = F_grid(cx, cy, N)
        Fs.append(Fv)
        print(f"    N={N:6d}  F={Fv:.13f}  ({time.time()-t0:.1f}s)")
    T = richardson_p1(Fs)
    return T[-1][0], Fs, T


# ---------------------------------------------------------------------
# Trajectories
# ---------------------------------------------------------------------

def gerver_callable(p):
    """Return cx, cy callables for the Gerver trajectory."""
    def cx(th):
        x, _ = _xt_xtp(mp.mpf(th), p)
        return float(x[0])
    def cy(th):
        x, _ = _xt_xtp(mp.mpf(th), p)
        return float(x[1])
    return cx, cy


def perturbed_callable(p, eps, k_mode, component):
    """c_G + eps * sin(2(k+1)θ) on (x or y) component.  component in {'x', 'y'}."""
    n = 2 * (k_mode + 1)
    cx0, cy0 = gerver_callable(p)
    if component == "x":
        def cx(th): return cx0(th) + eps * math.sin(n * th)
        cy = cy0
    elif component == "y":
        cx = cx0
        def cy(th): return cy0(th) + eps * math.sin(n * th)
    else:
        raise ValueError(component)
    return cx, cy


# ---------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------

def main():
    print("=" * 76)
    print("F_richardson_hessian: Path B Hessian validation")
    print("=" * 76)
    print()
    print("[1] Solving Gerver constants ...")
    t0 = time.time()
    p, resid = solve_gerver_constants(working_dps=30)
    print(f"    done ({time.time()-t0:.1f}s), residual = {mp.nstr(resid, 3)}")

    cx_G, cy_G = gerver_callable(p)
    A_target = float(PUBLISHED_A_STAR)

    # Validate the Richardson framework on c_G with deep extrapolation
    print("\n[2] Validating F_richardson on c_G (levels=6, N up to 8192):")
    F_inf_0, Fs_0, T_0 = F_richardson(cx_G, cy_G, base_N=128, levels=6)
    print(f"\n    Richardson F_∞ = {F_inf_0:.12f}")
    print(f"    Published A*   = {A_target:.12f}")
    delta_0 = F_inf_0 - A_target
    print(f"    delta          = {delta_0:+.3e}")
    if abs(delta_0) > 1e-7:
        print("  WARNING: F_∞ delta exceeds 1e-7.  Hessian precision may suffer.")

    # Hessian Q[0,0] — k=0 → sin(2θ) perturbation on x-component
    print("\n[3] Computing Hessian Q[0,0] via Richardson-extrapolated F:")
    eps = 1e-3  # step size; small relative to trajectory scale
    print(f"    perturbation: η_0(θ) = sin(2θ)·ê_x,  ε = {eps}")

    print("\n    F at c_G + ε·η_0:")
    cx_p, cy_p = perturbed_callable(p, +eps, 0, "x")
    F_inf_p, _, _ = F_richardson(cx_p, cy_p, base_N=128, levels=5)

    print("\n    F at c_G - ε·η_0:")
    cx_m, cy_m = perturbed_callable(p, -eps, 0, "x")
    F_inf_m, _, _ = F_richardson(cx_m, cy_m, base_N=128, levels=5)

    # Central-difference Hessian diagonal
    Q00 = (F_inf_p - 2*F_inf_0 + F_inf_m) / (eps * eps)
    print(f"\n[4] Hessian diagonal Q[0,0]:")
    print(f"    F_inf(c_G + ε)  = {F_inf_p:.11f}")
    print(f"    F_inf(c_G)      = {F_inf_0:.11f}")
    print(f"    F_inf(c_G - ε)  = {F_inf_m:.11f}")
    print(f"    F(+ε) - 2 F(0) + F(-ε)  = {F_inf_p - 2*F_inf_0 + F_inf_m:.3e}")
    print(f"    Q[0,0]  = {Q00:.6f}")

    # Phase 2/4 reference
    print(f"\n    Phase 2 Q[0,0] (Shapely) ≈ -5.86")
    print(f"    Phase 4 Q[0,0] (Shapely) ≈ -5.86")
    print(f"    Our Q[0,0]               = {Q00:.4f}")

    if abs(Q00 - (-5.86)) < 0.5:
        print("\n  >>> AGREEMENT with Phase 2/4 within 0.5.  Path B validates the spectrum.")
    elif abs(Q00 - (-5.86)) < 2.0:
        print("\n  >>> Approximate agreement; precision-limited.  Need more Richardson levels.")
    else:
        print("\n  >>> DISAGREEMENT.  Either Phase 2/4 was wrong, or Path B has its own issue.")


if __name__ == "__main__":
    main()
