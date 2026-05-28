"""
hypV_sweep.py
=============

Verify Hypothesis V (|Q[k,k]| ≤ 8π k²) across k ∈ {1, ..., 16} ∪ {20, 24, 32}
to test whether the empirical asymptotic slope matches the analytic k² bound.
"""
from __future__ import annotations
import math, os, sys, time, json
import numpy as np
import matplotlib.pyplot as plt
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gerver_constants import solve_gerver_constants
from F_richardson_hessian import F_richardson, gerver_callable, perturbed_callable

mp.mp.dps = 30

def main():
    print("Solving Gerver constants ...")
    p, _ = solve_gerver_constants(working_dps=30)
    cx_G, cy_G = gerver_callable(p)

    print("Computing F_inf(c_G) at base_N=128 levels=4 ...")
    F0, _, _ = F_richardson(cx_G, cy_G, base_N=128, levels=4)
    print(f"  F0 = {F0:.10f}")
    print()

    EPS = 1e-3
    ks = [1, 2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 20, 24, 32]
    rows = []

    print(f"  k    Qx        Qy        8πk²       max-ratio")
    for k in ks:
        t0 = time.time()
        try:
            cx_p, cy_p = perturbed_callable(p, +EPS, k - 1, "x")
            cx_m, cy_m = perturbed_callable(p, -EPS, k - 1, "x")
            Fxp, _, _ = F_richardson(cx_p, cy_p, base_N=128, levels=4)
            Fxm, _, _ = F_richardson(cx_m, cy_m, base_N=128, levels=4)
            Qx = (Fxp - 2*F0 + Fxm) / EPS**2

            cy_p2, cyy_p = perturbed_callable(p, +EPS, k - 1, "y")
            cy_m2, cyy_m = perturbed_callable(p, -EPS, k - 1, "y")
            Fyp, _, _ = F_richardson(cy_p2, cyy_p, base_N=128, levels=4)
            Fym, _, _ = F_richardson(cy_m2, cyy_m, base_N=128, levels=4)
            Qy = (Fyp - 2*F0 + Fym) / EPS**2

            # Paper's tight bound from Theorem (eigenvalue-growth):
            #   |Q[k,k]| ≤ (3π/2) k² + (6π+12) k
            bound = (3 * math.pi / 2) * k**2 + (6 * math.pi + 12) * k
            r = max(abs(Qx), abs(Qy)) / bound
            rows.append({"k": k, "Qx": Qx, "Qy": Qy,
                         "bound": bound, "ratio": r})
            print(f"  {k:3d}  {Qx:8.2f}  {Qy:8.2f}  {bound:8.1f}   {r:.3f}  ({time.time()-t0:.0f}s)")
        except Exception as e:
            print(f"  k={k} failed: {e}")

    # Fit slope
    ks_arr = np.array([r["k"] for r in rows])
    Qs_max = np.array([max(abs(r["Qx"]), abs(r["Qy"])) for r in rows])
    log_k = np.log(ks_arr)
    log_Q = np.log(Qs_max)
    slope_all, intercept = np.polyfit(log_k, log_Q, 1)
    high = ks_arr >= 6
    if high.sum() >= 3:
        slope_high, _ = np.polyfit(log_k[high], log_Q[high], 1)
    else:
        slope_high = None
    max_ratio = max(r["ratio"] for r in rows)
    margin = 1.0 / max_ratio

    print()
    print(f"  Empirical slope all k:  {slope_all:.3f}")
    print(f"  Empirical slope k>=6:   {slope_high}")
    print(f"  Max ratio |Q|/(8πk²):  {max_ratio:.4f}")
    print(f"  Min multiplicative margin: {margin:.2f}x")

    out = {
        "rows": rows,
        "slope_all": slope_all,
        "slope_high": slope_high,
        "max_ratio": max_ratio,
        "min_margin": margin,
        "bound_holds": max_ratio < 1.0,
    }
    with open(os.path.join(os.path.dirname(__file__), "hypV_sweep.json"), "w") as f:
        json.dump(out, f, indent=2, default=float)

    # Plot
    fig, ax = plt.subplots(figsize=(7, 5))
    ax.loglog(ks_arr, np.abs([r["Qx"] for r in rows]), "o-", label="|Q[k,k]_x|", color='steelblue')
    ax.loglog(ks_arr, np.abs([r["Qy"] for r in rows]), "s-", label="|Q[k,k]_y|", color='darkorange')
    k_smooth = np.linspace(1, ks_arr.max(), 100)
    paper_bound = (3 * math.pi / 2) * k_smooth**2 + (6 * math.pi + 12) * k_smooth
    ax.loglog(k_smooth, paper_bound, "--", color="red",
              label=r"$(3\pi/2)k^2 + (6\pi+12)k$ (paper bound)")
    ax.loglog(k_smooth, np.exp(intercept) * k_smooth**slope_all, ":", color="gray",
              label=f"fit: $\\sim k^{{{slope_all:.2f}}}$")
    ax.set_xlabel("mode index k")
    ax.set_ylabel(r"|$Q[k,k]$|")
    ax.set_title(f"Hypothesis V: |Q[k,k]| vs 8π k², empirical slope {slope_all:.2f}")
    ax.legend()
    ax.grid(True, which="both", alpha=0.3)
    plt.tight_layout()
    plt.savefig(os.path.join(os.path.dirname(__file__), "hypV_sweep.pdf"), dpi=120)
    print(f"\nSaved plot to hypV_sweep.pdf")

if __name__ == "__main__":
    main()
