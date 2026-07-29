"""sigma_graded.py — GRADED (multi-band) WELD for item 12b.

The 2x2 weld failed because in L^2 the form M is unbounded (Wirtinger terms
~ k^2), so the tail block's minimum and the coupling maximum are attained on
different directions and their product is meaningless.

Graded fix: split the modes into dyadic bands B_0, B_1, ... and use, for each
pair, the sharp splitting

    |2<A_ij x_j, x_i>| <= ||A_ij|| ( t ||x_i||^2 + ||x_j||^2 / t ),
    t = sqrt(w_j / w_i),

so that with band minima lam_i = lam_min(A_ii) and couplings N_ij = ||A_ij||,

    M(x) >= min_i [ lam_i - sum_{j != i} N_ij sqrt(w_j/w_i) ] * ||x||^2.

The weights w are then optimized.  The point of grading is that each band's
coupling is matched against ITS OWN lam_i rather than against the global
minimum, so a band whose lam grows like k^2 can absorb a coupling that also
grows, provided the RATIO behaves.

The script reports the band data (lam_i, N_ij), the optimized bound, and --
the part that decides item 12b -- how lam_i and N_ij scale with the band
index, since closing the tail needs the infinite sum to converge.

Usage: python3 sigma_graded.py [K] [K0]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sigma_interp import cap_grams, COTB
from sofa_romik2017_reference import BETA


def bands(K, K0):
    """dyadic bands of mode index k"""
    out = []
    lo = 0
    hi = K0
    while lo < K:
        out.append((lo, min(hi, K)))
        lo, hi = hi, 2*hi
    return out


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    K0 = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    Q = np.load(os.path.join(THIS, f"sigma_rel_K{K}.npy"))
    Q = 0.5*(Q + Q.T)
    n = 2*K
    D1, D2, modes = cap_grams(K)
    gl = math.pi/4
    A = (-Q + (COTB/BETA)*(D1 + D2))/gl

    # translation projected out
    w = np.zeros(n)
    for i, (c, k) in enumerate(modes):
        if c == 0:
            w[i] = (1.0/k) if (k % 2 == 1) else 0.0
    wn = w/np.linalg.norm(w)
    U, sv, _ = np.linalg.svd(np.eye(n) - np.outer(wn, wn))
    P = U[:, sv > 1e-10]
    full = float(np.linalg.eigvalsh(P.T @ A @ P).min())

    bs = bands(K, K0)
    idx = [[i for i, (c, k) in enumerate(modes) if lo < k <= hi]
           for (lo, hi) in bs]
    # project translation out of the first band only
    B = len(bs)
    lam = np.zeros(B)
    for i in range(B):
        Ai = A[np.ix_(idx[i], idx[i])]
        if i == 0:
            wl = w[idx[0]]; wl = wl/np.linalg.norm(wl)
            Ul, svl, _ = np.linalg.svd(np.eye(len(idx[0])) - np.outer(wl, wl))
            Pl = Ul[:, svl > 1e-10]
            Ai = Pl.T @ Ai @ Pl
        lam[i] = float(np.linalg.eigvalsh(Ai).min())
    N = np.zeros((B, B))
    for i in range(B):
        for j in range(i+1, B):
            N[i, j] = N[j, i] = float(
                np.linalg.svd(A[np.ix_(idx[i], idx[j])], compute_uv=False).max())

    print(f"K={K}  K0={K0}  full-form margin m(M) = {full:.4f}")
    print(f"\nbands (k-range), lam_min, and couplings:")
    for i, (lo, hi) in enumerate(bs):
        print(f"  B{i} k in ({lo},{hi}]  dim={len(idx[i]):3d}  "
              f"lam={lam[i]:12.3f}   N[{i},j] = "
              + " ".join(f"{N[i,j]:9.2f}" for j in range(B)))

    # optimize weights: maximize min_i [ lam_i - sum_j N_ij sqrt(w_j/w_i) ]
    def score(u):
        wt = np.exp(u)
        vals = []
        for i in range(B):
            pen = sum(N[i, j]*math.sqrt(wt[j]/wt[i]) for j in range(B) if j != i)
            vals.append(lam[i] - pen)
        return min(vals)

    rng = np.random.default_rng(11)
    best_u = np.zeros(B); best = score(best_u)
    step = 1.5
    for it in range(4000):
        cand = best_u + step*rng.standard_normal(B)
        v = score(cand)
        if v > best:
            best, best_u = v, cand
        if it % 800 == 799:
            step *= 0.6
    print(f"\noptimized graded bound: m >= {best:.4f}"
          f"   (weights exp(u), u = {np.round(best_u-best_u[0],2)})")
    print(f"  vs true full-form margin {full:.4f}")

    print(f"\nSCALING (what decides the infinite tail):")
    for i in range(1, B):
        r_lam = lam[i]/lam[i-1] if lam[i-1] > 0 else float('nan')
        r_N = N[i-1, i]/N[max(i-2,0), i-1] if i > 1 and N[max(i-2,0), i-1] > 0 else float('nan')
        print(f"  B{i-1}->B{i}: lam ratio {r_lam:8.2f}   "
              f"nearest-neighbour coupling {N[i-1,i]:10.2f}"
              + (f"   (coupling ratio {r_N:.2f})" if i > 1 else ""))


if __name__ == "__main__":
    main()
