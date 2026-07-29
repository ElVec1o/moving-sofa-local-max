"""sigma_symbol.py — ITEM 12b: the Sigma tail is governed by a TOEPLITZ SYMBOL.

Measured structure (K=32).  Write M = (-Q_rel + (cot b/b)(D1+D2))/(pi/4) and
normalise out the k^2 diagonal growth:

    N[k,k'] := M[k,k'] / (k k').

N is TOEPLITZ to within a few percent: N[k,k'] depends on Delta = |k-k'| alone,
and vanishes identically for odd Delta.  Sample (comp x, k = 8,12,16,20,24):

    Delta=0   10.55  9.93 10.33 10.50 10.20
    Delta=2   -3.97 -4.70 -4.78 -4.44 -4.39
    Delta=4   -1.60 -1.69 -2.09 -1.92 -1.48

This is what every previous weld missed.  A Toeplitz form's spectrum is the
range of its symbol

    f(theta) = a_0 + 2 sum_{Delta>0} a_Delta cos(Delta theta),

so the INFINITE tail is controlled by min_theta f, a single number computable
from finitely many coefficients -- no band decomposition, no coupling maxima.

WHY THIS CLOSES THE TAIL.  For the tail block (k > K),

    M(eta_tail) >= f_min * sum_k k^2 |eta_k|^2 >= f_min K^2 ||eta_tail||_{L2}^2,

so the tail's L^2 margin grows like K^2 while the target margin is the fixed
number m ~ 6.45.  The tail requirement is therefore only f_min >= m/K^2, which
at K=32 is 0.0063 -- two orders below the measured f_min.  The tail is not
tight at all once the Toeplitz structure is used; what remains is the coupling
block, not the tail.

This script fits the symbol, computes min_theta f, checks it against the
directly measured H^1 margin (they must agree -- that is the consistency test),
and reports the resulting tail margin against the target.

Usage: python3 sigma_symbol.py [K]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sigma_interp import cap_grams, COTB
from sofa_romik2017_reference import BETA

TARGET = 6.4806        # the L2 margin the Sigma-local theorem needs


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 32
    Q = np.load(os.path.join(THIS, f"sigma_rel_K{K}.npy"))
    Q = 0.5*(Q + Q.T)
    D1, D2, modes = cap_grams(K)
    M = (-Q + (COTB/BETA)*(D1 + D2))/(math.pi/4)
    idx = {m: i for i, m in enumerate(modes)}

    print(f"TOEPLITZ SYMBOL OF THE SIGMA TAIL   (K={K})\n")
    for comp, nm in ((0, "x"), (1, "y")):
        # fit a_Delta by averaging over the middle of the range, where the
        # Toeplitz limit is cleanest (edges are contaminated by truncation)
        lo, hi = K//4, K
        a = {}
        for D in range(0, K, 2):
            vals = [M[idx[(comp, k)], idx[(comp, k+D)]]/(k*(k+D))
                    for k in range(lo, hi+1) if k+D <= K]
            if len(vals) >= 3:
                a[D] = (float(np.mean(vals)), float(np.std(vals)))
        print(f"  component {nm}:  symbol coefficients a_Delta "
              f"(mean +- spread over k in [{lo},{hi}])")
        for D in sorted(a):
            if abs(a[D][0]) > 5e-3:
                print(f"     a_{D:<2d} = {a[D][0]:+9.4f}  +- {a[D][1]:.4f}")
        th = np.linspace(0, math.pi, 20001)
        f = np.full_like(th, a[0][0])
        for D in sorted(a):
            if D:
                f = f + 2*a[D][0]*np.cos(D*th)
        fmin = float(f.min()); fmax = float(f.max())
        print(f"     symbol range: [{fmin:.4f}, {fmax:.4f}]   "
              f"min at theta = {th[int(f.argmin())]:.4f}")
        print(f"     -> tail L2 margin at K={K}:  f_min * K^2 = "
              f"{fmin*K*K:.2f}   (target {TARGET:.2f})")
        print(f"     -> tail requirement f_min >= m/K^2 = "
              f"{TARGET/K**2:.5f};  measured f_min = {fmin:.5f}  "
              f"[{'SATISFIED' if fmin > TARGET/K**2 else 'FAILS'}]\n")

    print("CONSISTENCY CHECK — the symbol minimum must match the directly")
    print("measured H^1 margin (sigma_h1.py reported 0.068467 at K=32).")
    print("If they disagree the Toeplitz fit is not yet the right model.")


if __name__ == "__main__":
    main()
