"""sigma_matrix_symbol.py — ITEM 12b: the tail's 2x2 MATRIX symbol.

Three fits have now been tried and the first two failed their own consistency
test (symbol minimum vs directly measured H^1 margin):

  1. scalar Toeplitz on the xx block          min f = -0.613  vs  H1 = +0.068
  2. scalar Toeplitz on the graded g-blocks   min f = +3.139  vs  H1 = +0.068

Fit 1 failed because the xx block is not an invariant block.  Fit 2 failed
because the graded block alternates component with k: its fitted a_0 came out
12.95 +- 2.78, and 12.95 = (10.3 + 15.8)/2 while 2.78 = (15.8 - 10.3)/2 -- the
"spread" is not noise, it is a period-2 structure.

So M is not scalar Toeplitz in any basis.  It is BLOCK Toeplitz with 2x2
blocks: at each k there are two components, and after normalising out the k^2
growth,

    N[(c,k),(c',k')]  =  A_{c c'}(k - k'),

a matrix-valued sequence.  The selection rule (proved from Sigma's ambidextrous
symmetry U) says

    A_xx(D) = A_yy(D) = 0 for D odd,      A_xy(D) = 0 for D even.

The spectrum of a block-Toeplitz operator is the union over theta of the
eigenvalues of its MATRIX symbol

    F(theta) = sum_D A(D) e^{i D theta},        F(theta) Hermitian,

so the tail margin is  min over theta of lam_min F(theta).  That single number
controls the whole infinite tail.

ACCEPTANCE TEST (unchanged, and the point of the exercise): min_theta lam_min F
must agree with the directly measured H^1 margin.  Only then is the symbol the
right model and the tail bound legitimate.

Usage: python3 sigma_matrix_symbol.py [K]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sigma_interp import cap_grams, COTB
from sofa_romik2017_reference import BETA

TARGET = 6.4806


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 32
    Q = np.load(os.path.join(THIS, f"sigma_rel_K{K}.npy"))
    Q = 0.5*(Q + Q.T)
    D1, D2, modes = cap_grams(K)
    M = (-Q + (COTB/BETA)*(D1 + D2))/(math.pi/4)
    idx = {m: i for i, m in enumerate(modes)}

    def N(c, k, cp, kp):
        return M[idx[(c, k)], idx[(cp, kp)]]/(k*kp)

    # fit A_{cc'}(D) by averaging over the middle of the range
    lo, hi = K//4, K
    A = {}
    spread = {}
    for c in (0, 1):
        for cp in (0, 1):
            for D in range(-(K-1), K):
                vals = [N(c, k, cp, k+D) for k in range(lo, hi+1)
                        if 1 <= k+D <= K]
                if len(vals) >= 3:
                    A[(c, cp, D)] = float(np.mean(vals))
                    spread[(c, cp, D)] = float(np.std(vals))

    print(f"2x2 MATRIX SYMBOL OF THE SIGMA TAIL   (K={K})\n")
    print("  leading blocks A(D)  (rows x,y; cols x,y), mean +- spread:")
    for D in (0, 1, 2, 3, 4):
        rows = []
        for c in (0, 1):
            rows.append(" ".join(
                f"{A.get((c,cp,D),0.0):+8.3f}({spread.get((c,cp,D),0.0):.2f})"
                for cp in (0, 1)))
        print(f"    D={D}:  [{rows[0]}]")
        print(f"           [{rows[1]}]")

    th = np.linspace(0, 2*math.pi, 4001)
    lam = np.empty((len(th), 2))
    for i, t in enumerate(th):
        F = np.zeros((2, 2), dtype=complex)
        for (c, cp, D), v in A.items():
            F[c, cp] += v*np.exp(1j*D*t)
        F = 0.5*(F + F.conj().T)
        lam[i] = np.linalg.eigvalsh(F)
    fmin = float(lam.min())
    imin = int(np.unravel_index(lam.argmin(), lam.shape)[0])
    print(f"\n  symbol eigenvalue range: [{lam.min():.6f}, {lam.max():.4f}]")
    print(f"  min at theta = {th[imin]:.5f}")

    # directly measured H1 margin, translation projected out
    kk = np.array([k for (c, k) in modes], dtype=float)
    S = np.diag(1.0/kk)
    H = S @ M @ S
    w = np.array([(1.0/k if (c == 0 and k % 2 == 1) else 0.0)
                  for (c, k) in modes])*kk
    w = w/np.linalg.norm(w)
    U, sv, _ = np.linalg.svd(np.eye(len(w)) - np.outer(w, w))
    P = U[:, sv > 1e-10]
    h1 = float(np.linalg.eigvalsh(P.T @ H @ P).min())
    h1raw = float(np.linalg.eigvalsh(H).min())
    print(f"\n  measured H1 margin: {h1:.6f}  (raw, no projection: "
          f"{h1raw:.6f})")
    ok = min(abs(fmin-h1), abs(fmin-h1raw)) < 0.05
    print(f"  |symbol min - H1| = {abs(fmin-h1):.4f} (projected), "
          f"{abs(fmin-h1raw):.4f} (raw)   "
          f"[{'CONSISTENT' if ok else 'INCONSISTENT'}]")
    print(f"\n  tail requirement f_min >= m/K^2 = {TARGET/K**2:.5f};  "
          f"f_min = {fmin:.5f}  "
          f"[{'SATISFIED' if fmin > TARGET/K**2 else 'FAILS'}]")
    if not ok:
        print("\n  NOT ACCEPTED. The symbol is still not the right model at "
              "this K.\n  Do not quote f_min as a tail bound.")


if __name__ == "__main__":
    main()
