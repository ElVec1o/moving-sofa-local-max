"""gerver_domination.py — systematic Part II sign test.

Question: does the structure-following form (true_hessian `probe`) dominate the
TRUE one-hallway area, i.e. is F_struct >= F_true near c_G?  A spot check on
three modes said no.  The decisive refinement is the ORDER of the discrepancy:

    D(eps) := [F_struct(eps) - F_struct(0)] - [F_true(eps) - F_true(0)]

* D ~ eps^2  ->  the two SECOND VARIATIONS differ.  Then negative definiteness
  of the structure-following ladder does NOT give one-sided local maximality,
  and Part II's step past K=32 is defective.
* D ~ eps^3  ->  the second variations AGREE; the discrepancy is third order
  and is dominated by the eps^2 term for small eps.  Then Q_struct < 0 does
  give F(+-eps) < F(0) one-sidedly, and the flag dissolves.

Exact true area from `sigma_area` in GERVER mode (single hallway family);
exact structure-following area from `true_hessian probe`.

Usage: python3 gerver_domination.py [n_theta]
"""
from __future__ import annotations
import os, sys, math, re, subprocess
import numpy as np
import mpmath as mp

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from gerver_constants import solve_gerver_constants, _xt_full


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1201
    p, _ = solve_gerver_constants(working_dps=25, verbose=False)
    th = np.linspace(0.0, math.pi/2, n)
    cx = np.empty(n); cy = np.empty(n)
    for i, t in enumerate(th):
        x, _, _ = _xt_full(mp.mpf(t), p)
        cx[i] = float(x[0]); cy[i] = float(x[1])

    def true_areas(trajs):
        inp = [f"{n} {len(trajs)}", " ".join(f"{t:.17g}" for t in th)]
        for a, b in trajs:
            inp.append(" ".join(f"{u:.17g} {v:.17g}" for u, v in zip(a, b)))
        r = subprocess.run([os.path.join(THIS, "sigma_area")],
                           input="\n".join(inp), capture_output=True, text=True,
                           env=dict(os.environ, GERVER="1"))
        return [float(x) for x in r.stdout.split()]

    def struct_area(eps, comp, k):
        open("/tmp/gd.txt", "w").write(f"{comp} {k} 1.0\n")
        o = subprocess.run([os.path.join(THIS, "true_hessian"), "probe",
                            repr(eps), "/tmp/gd.txt"],
                           capture_output=True, text=True).stdout
        m = re.search(r"area\s*=\s*([-\d.eE+]+)", o)
        return float(m.group(1)) if m else float("nan")

    F0t = true_areas([(cx, cy)])[0]
    F0s = struct_area(0.0, 0, 1)
    print(f"n_theta={n}   F_true(c_G)={F0t:.10f}   F_struct(c_G)={F0s:.10f}")
    print(f"(the {F0t-F0s:+.2e} offset is the t-discretization of the true "
          f"oracle; it cancels in dF)\n")

    eps_list = [2e-3, 4e-3, 8e-3]
    modes = [(0, k) for k in (1, 2, 3, 5, 8)] + [(1, k) for k in (1, 2, 4, 6)]
    print(f"{'mode':>12} {'D(2e-3)':>12} {'D(4e-3)':>12} {'D(8e-3)':>12} "
          f"{'order':>7}  reading")
    orders = []
    for (comp, k) in modes:
        g = np.sin(2*k*th); z = np.zeros_like(th)
        gx, gy = (g, z) if comp == 0 else (z, g)
        trajs = [(cx + e*gx, cy + e*gy) for e in eps_list]
        At = true_areas(trajs)
        D = []
        for e, ta in zip(eps_list, At):
            dt = ta - F0t
            ds = struct_area(e, comp, k) - F0s
            D.append(ds - dt)
        # local exponent from the last doubling
        with np.errstate(all="ignore"):
            o1 = math.log(abs(D[1]/D[0]))/math.log(2) if D[0] and D[1] else float("nan")
            o2 = math.log(abs(D[2]/D[1]))/math.log(2) if D[1] and D[2] else float("nan")
        orders.append(o2)
        tag = ("2nd-order defect" if o2 < 2.5 else
               "3rd order -> Hessians agree")
        print(f"  e_{'xy'[comp]} sin{2*k:2d}t {D[0]:12.3e} {D[1]:12.3e} "
              f"{D[2]:12.3e} {o2:7.2f}  {tag}")
    good = [o for o in orders if not math.isnan(o)]
    print(f"\nexponents: min {min(good):.2f}  median {np.median(good):.2f}  "
          f"max {max(good):.2f}")
    print("VERDICT:", "second variations AGREE (discrepancy is O(eps^3)) — "
          "Part II flag dissolves" if min(good) > 2.5 else
          "at least one mode shows an O(eps^2) discrepancy — defect confirmed")


if __name__ == "__main__":
    main()
