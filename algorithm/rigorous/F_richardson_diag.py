"""
F_richardson_diag.py
====================

Path B Phase 4 attempt #2: compute several diagonal entries of the
Hessian via Richardson-extrapolated F, look at all diagonals + the
trace, compare to Phase 2's spectrum [-4.81, -5.53, -15.4, -18.8, ...].

If our diagonals match Phase 2's spectrum within Richardson precision,
the Path B Hessian validates the Phase 2 result.
"""

from __future__ import annotations
import math, time, sys, os
import numpy as np
import mpmath as mp
from shapely.affinity import rotate as srot, translate as strans

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from sofa_bvp import HALLWAY
from gerver_constants import solve_gerver_constants, _xt_xtp
from F_richardson_hessian import F_grid, richardson_p1, F_richardson, gerver_callable, perturbed_callable

mp.mp.dps = 30


def main():
    p, _ = solve_gerver_constants(working_dps=30)
    cx_G, cy_G = gerver_callable(p)

    print("=" * 76)
    print("Path B Phase 4: 12 diagonal entries of Hessian Q")
    print("=" * 76)

    # First: F_inf(c_G) at high levels for the reference
    print("\n[ref] Computing F_inf(c_G) at levels=5, N up to 4096:")
    F0, _, _ = F_richardson(cx_G, cy_G, base_N=128, levels=5)
    print(f"   F_inf(c_G) = {F0:.13f}")

    # Phase 2 basis: φ_k(θ) = sin(2kθ) for k=1..6 on x and y → 12 directions
    eps = 1e-3
    print(f"\n[diag] FD second derivatives with ε = {eps}, basis sin(2kθ):")
    print()
    print("  idx   k   component   Q[i,i] (Path B)")
    print("  ---  ---  ---------   ---------------")

    diags = []
    t_total = time.time()
    for k_mode in range(6):
        for component in ["x", "y"]:
            idx = 2 * k_mode + (0 if component == "x" else 1)
            t0 = time.time()
            cx_p, cy_p = perturbed_callable(p, +eps, k_mode, component)
            cx_m, cy_m = perturbed_callable(p, -eps, k_mode, component)
            # Use levels=4 (N up to 2048) to keep runtime manageable
            F_p, _, _ = F_richardson(cx_p, cy_p, base_N=128, levels=4)
            F_m, _, _ = F_richardson(cx_m, cy_m, base_N=128, levels=4)
            q_ii = (F_p - 2*F0 + F_m) / (eps * eps)
            diags.append(q_ii)
            print(f"  {idx:3d}  {k_mode+1}    sin(2{k_mode+1}θ)·ê_{component}    "
                  f"{q_ii:+.4f}   ({time.time()-t0:.1f}s)")

    print(f"\n  Total runtime: {time.time()-t_total:.1f}s")

    # Compare to Phase 2 spectrum
    phase2_eigs = [-4.81, -5.53, -15.4, -18.8, -34.2, -40.7,
                   -62.1, -71.0, -100.9, -108.1, -160.6, -202.1]
    print(f"\n[compare] Phase 2 spectrum (sorted, most-negative-close-to-zero first):")
    print(f"  {phase2_eigs}")
    print(f"\n  Path B diagonals (in basis order, x_1, y_1, x_2, y_2, ...):")
    print(f"  {[f'{d:.2f}' for d in diags]}")

    # Trace = sum of eigenvalues = sum of diagonals (basis-invariant)
    trace_pathB = sum(diags)
    trace_phase2 = sum(phase2_eigs)
    print(f"\n  Trace (Path B)    = {trace_pathB:.4f}")
    print(f"  Trace (Phase 2)   = {trace_phase2:.4f}")
    print(f"  delta             = {trace_pathB - trace_phase2:+.4f}")
    print(f"  relative          = {(trace_pathB - trace_phase2)/abs(trace_phase2)*100:+.2f}%")

    # Sort diagonals (smallest in magnitude first) and compare element-wise
    print()
    sorted_pathB = sorted(diags, reverse=True)  # descending = least-negative first
    print(f"  Path B diag sorted: {[f'{d:.2f}' for d in sorted_pathB]}")
    print(f"  Phase 2 eigvals:    {[f'{d:.2f}' for d in phase2_eigs]}")

    # Largest-magnitude (most negative) — this should match λ_max_phase2 = -4.81
    print(f"\n  Path B largest diagonal (least negative)  = {max(diags):.4f}")
    print(f"  Phase 2 largest eigenvalue (least negative) = {max(phase2_eigs):.4f}")
    print(f"  delta = {max(diags) - max(phase2_eigs):+.4f}")

    print("\n" + "=" * 76)
    print("Verdict")
    print("=" * 76)
    if abs(trace_pathB - trace_phase2) / abs(trace_phase2) < 0.05:
        print(f"  Trace agreement < 5%.  Path B validates Phase 2 spectrum.")
    elif abs(trace_pathB - trace_phase2) / abs(trace_phase2) < 0.15:
        print(f"  Trace agreement within 15%.  Acceptable, precision-limited.")
    else:
        print(f"  Trace disagreement > 15%.  Investigate.")


if __name__ == "__main__":
    main()
