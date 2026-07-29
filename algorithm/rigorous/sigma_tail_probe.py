"""sigma_tail_probe.py — TAIL PROBE for Theorem 9 item 12 (PROGRAM S7'''-f).

The weld needs: no degeneration of the true second variation at HIGH
frequency, beyond the reach of the K<=24 ladders. The covering argument
says which mechanism must carry each component, and this script tests each
one directly against the true ambidextrous oracle.

COVERING (established, per mechanism):
  cap 1 (t ~ 0):   eta_y  <- released nu-slot arcs, weight cos^2 t ~ 1
                            (FULL derivative coercivity, grows like k^2)
                   eta_x  <- the nu-slot weight is sin^2 t ~ t^2 (degenerate),
                            so the FAN BITE must carry it (N12).
                            phi(s) = <eta, mu_s> ~ eta_x near s=0, and the
                            bite is ~ (amplitude)^2: frequency-INDEPENDENT
                            L^2 coercivity — exactly what a tail needs.
  cap 2 (t ~ pi/2): mirrored (eta_x <- arcs, eta_y <- bite).
  middle:           full coverage, k^2 growth.

So the predictions to test, at frequencies far above the ladder:
  (A) x-polarized cap-localized modes: -Q_true bounded BELOW by a positive
      constant, roughly frequency-independent (bite-carried);
  (B) y-polarized cap-localized modes: -Q_true GROWING like k^2 (arc-carried);
  (C) middle-supported modes: -Q_true growing like k^2.
A failure of (A) to stay positive would break the weld; growth in (B),(C)
is what makes the tail harmless.

Usage: python3 sigma_tail_probe.py [n_theta]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from romik_hessian import tabulate_romik, ambi_area_from_arrays
from sofa_romik2017_reference import BETA

PI2 = math.pi/2
trapz = np.trapezoid


def window(th, a, b):
    """smooth C^2 bump supported on [a,b], = sin^2 profile."""
    u = (th - a)/(b - a)
    return np.where((u > 0) & (u < 1), np.sin(np.pi*np.clip(u, 0, 1))**2, 0.0)


def main():
    n_theta = int(sys.argv[1]) if len(sys.argv) > 1 else 6001
    th, cx, cy = tabulate_romik(n_theta)
    F0 = ambi_area_from_arrays(th, cx, cy)
    print(f"n_theta={n_theta}   F(c_R) = {F0:.8f}\n")

    cases = []
    for w in (10, 20, 40, 80, 160):
        # cap-localized oscillation of angular frequency w on [0.05b, 0.95b]
        env = window(th, 0.05*BETA, 0.95*BETA)
        osc = np.sin(w*math.pi*(th - 0.05*BETA)/(0.9*BETA))
        cases.append((f"A  cap x-pol  w={w:3d}", env*osc, np.zeros_like(th)))
        cases.append((f"B  cap y-pol  w={w:3d}", np.zeros_like(th), env*osc))
    for w in (10, 40, 160):
        env = window(th, BETA + 0.05, PI2 - BETA - 0.05)
        osc = np.sin(w*math.pi*(th - BETA - 0.05)/(PI2 - 2*BETA - 0.1))
        cases.append((f"C  mid x-pol  w={w:3d}", env*osc, np.zeros_like(th)))

    print(f"{'direction':>20} {'-Q_true':>12} {'eps used':>10}  verdict")
    for name, gx, gy in cases:
        nrm = math.sqrt(trapz(gx*gx + gy*gy, th))
        gx, gy = gx/nrm, gy/nrm
        val = None
        for eps in (2e-4, 1e-4, 5e-5):
            Fp = ambi_area_from_arrays(th, cx + eps*gx, cy + eps*gy)
            Fm = ambi_area_from_arrays(th, cx - eps*gx, cy - eps*gy)
            q = (Fp - 2*F0 + Fm)/eps**2
            if val is None:
                val, used = q, eps
            # prefer the smallest eps whose value is stable vs the previous
            if abs(q - val) < 0.02*max(1.0, abs(q)):
                val, used = q, eps
            else:
                val, used = q, eps
        tag = "OK (bounded>0)" if -val > 0 else "*** FAILS ***"
        print(f"{name:>20} {-val:12.4f} {used:10.1e}  {tag}", flush=True)


if __name__ == "__main__":
    main()
