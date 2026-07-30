"""sigma_h1.py — ITEM 12b: close the Sigma tail in the H^1 norm.

Every previous weld (2x2 block, dyadic graded) failed for the same reason: they
tried to bound M below in L^2, where M is UNBOUNDED.  Measured structure of
M = (-Q_rel + (cot beta/beta)(D1+D2))/(pi/4) at K=32:

    diagonal   M[x,k] / k^2 -> 10.14,   M[y,k] / k^2 -> 15.80    (k=1..32)
    coupling   M[k,k'] = 0 exactly whenever |k-k'| is ODD

So M grows like k^2 on the diagonal: it is coercive in an H^1-type norm, never
in L^2.  The right statement of the Sigma-local theorem is therefore

    -Q_true(eta)  >=  m * ||eta||_{H}^2,        ||eta||_H^2 := sum_k k^2 |eta_k|^2,

and the tail closes iff  lam_min( D^{-1/2} M D^{-1/2} ),  D = diag(k^2),  is
bounded below UNIFORMLY in K.  That is what this script measures, on the
ladder K = 10, 16, 24, 32.

The parity selection rule additionally splits M into even-k and odd-k blocks,
which are reported separately: a uniform bound on each gives a uniform bound
overall, and halves the size of anything that later needs certifying in arb.

The translation mode (eta_x = sum_{k odd} sin(2kt)/k, which is the k-expansion
of a constant shift) is projected out, as in the earlier ladders.

Usage: python3 sigma_h1.py
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sigma_interp import cap_grams, COTB
from sofa_romik2017_reference import BETA


def build(K):
    Q = np.load(os.path.join(THIS, f"sigma_rel_K{K}.npy"))
    Q = 0.5*(Q + Q.T)
    D1, D2, modes = cap_grams(K)
    M = (-Q + (COTB/BETA)*(D1 + D2))/(math.pi/4)
    return M, modes


def proj_out(A, w):
    """A restricted to the orthogonal complement of w"""
    w = w/np.linalg.norm(w)
    U, sv, _ = np.linalg.svd(np.eye(len(w)) - np.outer(w, w))
    P = U[:, sv > 1e-10]
    return P.T @ A @ P


def main():
    print("ITEM 12b — the Sigma tail in the H^1 norm")
    print("  M is coercive in H^1, never in L^2 (diagonal ~ k^2).")
    print("  Test: is lam_min(D^{-1/2} M D^{-1/2}), D = diag(k^2), uniform "
          "in K?\n")
    print(f"{'K':>4} {'L2 margin':>12} {'H1 margin':>12} {'H1 even-k':>12} "
          f"{'H1 odd-k':>12}")
    rows = []
    for K in (10, 16, 24, 32, 48):
        f = os.path.join(THIS, f"sigma_rel_K{K}.npy")
        if not os.path.exists(f):
            continue
        M, modes = build(K)
        n = len(modes)
        kk = np.array([k for (c, k) in modes], dtype=float)
        # translation direction, in these coordinates
        w = np.array([(1.0/k if (c == 0 and k % 2 == 1) else 0.0)
                      for (c, k) in modes])
        l2 = float(np.linalg.eigvalsh(proj_out(M, w)).min())
        # H^1 rescaling
        S = np.diag(1.0/kk)
        H = S @ M @ S
        wH = w*kk            # the same direction expressed in H-coordinates
        h1 = float(np.linalg.eigvalsh(proj_out(H, wH)).min())
        # parity blocks
        par = []
        for r in (0, 1):
            idx = [i for i, (c, k) in enumerate(modes) if k % 2 == r]
            Hb = H[np.ix_(idx, idx)]
            wb = wH[idx]
            if np.linalg.norm(wb) > 1e-12:
                Hb = proj_out(Hb, wb)
            par.append(float(np.linalg.eigvalsh(Hb).min()))
        print(f"{K:>4} {l2:12.4f} {h1:12.6f} {par[0]:12.6f} {par[1]:12.6f}")
        rows.append((K, l2, h1))

    if len(rows) >= 3:
        print("\nCONVERGENCE (what decides item 12b):")
        for a, b in zip(rows, rows[1:]):
            print(f"  K {a[0]:>2} -> {b[0]:>2}:  L2 margin "
                  f"{a[1]:9.4f} -> {b[1]:9.4f}  (change {b[1]-a[1]:+8.4f})"
                  f"   H1 margin {a[2]:.6f} -> {b[2]:.6f}  "
                  f"(change {b[2]-a[2]:+.6f})")
        d = [abs(b[2]-a[2]) for a, b in zip(rows, rows[1:])]
        print(f"\n  H1 margin changes: {['%.2e' % x for x in d]}")
        stable = d[-1] < 1e-3 and rows[-1][2] > 0
        print("\nVERDICT:", "H1 MARGIN IS STABLE AND POSITIVE — the tail is "
              f"closable in H^1, m_H ~ {rows[-1][2]:.4f}." if stable else
              "H1 margin is NOT yet stable — more K needed, or the norm is "
              "still wrong.")


if __name__ == "__main__":
    main()
