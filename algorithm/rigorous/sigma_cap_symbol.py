"""sigma_cap_symbol.py — direct measurement of the TRUE cap symbol of Q_Sigma
on the self-similar family: eta = e_x * g((theta - t0)/delta), g a fixed
C^1 bump, amplitude normalized, scales delta -> 0 anchored INSIDE the cap.

For each delta: Q(eta_delta) via 3-point second difference of the ambi area,
at two stencil sizes (linearity check), plus the weighted/unweighted energy
integrals. Output: the scaling law Q ~ delta^p (p = 1 + 2s for symbol
theta^{2s} at self-similar scaling... report raw table; exponent from fit).

Also probes ONE-SIDEDNESS: forward-only and backward-only second responses
F(+e)-F(0) and F(-e)-F(0) separately (a kinked (one-sided) response shows
asymmetric halves).
"""
import os, sys, math, time
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from romik_hessian import tabulate_romik, ambi_area_from_arrays

trapz = np.trapezoid
B = 0.289653820817320941


def bump(u):
    """C^2 bump on [0,1], peak 1 at 1/2."""
    v = np.zeros_like(u)
    m = (u > 0) & (u < 1)
    v[m] = np.sin(np.pi*u[m])**2
    return v


def main():
    n_theta = 1201
    th, cx, cy = tabulate_romik(n_theta)
    F0 = ambi_area_from_arrays(th, cx, cy)
    print(f"F0 = {F0:.7f}", flush=True)
    sb2 = math.sin(B)**2

    print(f"{'delta':>8} {'t0':>6} {'eps':>8} {'Q':>12} {'Q2(e/2)':>12} "
          f"{'E_w':>10} {'L2':>10} {'Q/E_w':>9} {'fwd/bwd':>9}")
    for frac in (0.9, 0.6, 0.4, 0.25, 0.15):
        delta = frac*B
        t0 = 0.05*B          # anchor: bump on [t0, t0+delta], inside the cap
        g = bump((th - t0)/delta)
        gp = np.gradient(g, th)
        L2 = trapz(g*g, th)
        wmu = np.minimum(1.0, np.minimum(np.sin(th)**2, np.cos(th)**2)/sb2)
        mu0, mu1 = np.cos(th), np.sin(th)
        nu0, nu1 = -np.sin(th), np.cos(th)
        Ew = trapz(wmu*(gp*mu0)**2 + (gp*nu0)**2, th)  # e_x polarization
        amp = 1.0/math.sqrt(L2)                        # L2-normalize
        for eps0 in (2e-4,):
            eps = eps0
            def area(a):
                return ambi_area_from_arrays(th, cx + a*amp*g, cy)
            Fp = area(+eps); Fm = area(-eps)
            Q = (Fp - 2*F0 + Fm)/eps**2
            Fp2 = area(+eps/2); Fm2 = area(-eps/2)
            Q2 = (Fp2 - 2*F0 + Fm2)/(eps/2)**2
            fwd = (Fp - F0)/eps**2
            bwd = (Fm - F0)/eps**2
            ratio = fwd/bwd if bwd != 0 else float('nan')
            print(f"{delta:8.4f} {t0:6.3f} {eps:8.1e} {Q:12.5f} {Q2:12.5f} "
                  f"{Ew*amp*amp:10.3f} {1.0:10.3f} {Q/(Ew*amp*amp):9.4f} "
                  f"{ratio:9.4f}", flush=True)


if __name__ == "__main__":
    main()
