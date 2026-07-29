"""sigma_graded_symbol.py — ITEM 12b in the RIGHT basis.

The selection rule on M is not "odd Delta vanishes".  Measured exhaustively at
K=32 (ratios 1e-10 / 1e-11 / 1.1e9):

    same component (xx, yy):  M[(c,k),(c,k')] = 0  unless k+k' is EVEN
    cross component  (xy)  :  M[(0,k),(1,k')] = 0  unless k+k' is ODD

Both are the single statement that M is block-diagonal for the Z2 grading

    g(c,k) := (k + c) mod 2,        c = 0 for x, 1 for y,
    M[u,v] = 0  unless  g(u) = g(v).

That is the +-1 eigenspace splitting of

    U(eta)(t) := ( eta_x(pi/2 - t),  -eta_y(pi/2 - t) )

-- reverse t and flip y -- which is Sigma's AMBIDEXTROUS symmetry (the
rho-conjugation of SIGMA_LOCAL.md sec.1 composed with time reversal).  Indeed
U(x,k) = (-1)^{k+1}(x,k) and U(y,k) = (-1)^k (y,k), so U = +1 exactly on
{x odd k} u {y even k} = the g=1 block and U = -1 on the g=0 block.  A
U-invariant form cannot couple the two.  PROOF of the selection rule.

CONSEQUENCE, and why the earlier symbol fit failed its own consistency test:
the xx block is NOT an invariant block, so fitting a Toeplitz symbol to it was
fitting a symbol to a non-invariant slice.  The natural blocks INTERLEAVE the
components:

    g=1 block:  m_k = (x,k) for k odd, (y,k) for k even
    g=0 block:  m_k = (y,k) for k odd, (x,k) for k even

each a single sequence indexed by k = 1,2,3,...  This script fits the Toeplitz
symbol of each graded block, in the k-normalised variables N[k,k'] =
B[k,k']/(k k'), and checks min f against the block's directly measured H^1
margin -- the same acceptance test as before, which the xx fit failed.

Usage: python3 sigma_graded_symbol.py [K]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sigma_interp import cap_grams, COTB
from sofa_romik2017_reference import BETA

TARGET = 6.4806


def blocks(K):
    Q = np.load(os.path.join(THIS, f"sigma_rel_K{K}.npy"))
    Q = 0.5*(Q + Q.T)
    D1, D2, modes = cap_grams(K)
    M = (-Q + (COTB/BETA)*(D1 + D2))/(math.pi/4)
    idx = {m: i for i, m in enumerate(modes)}
    out = {}
    for g in (0, 1):
        # m_k has component c with (k + c) mod 2 == g
        seq = [(k, (g - k) % 2) for k in range(1, K+1)]
        ii = [idx[(c, k)] for (k, c) in seq]
        out[g] = (M[np.ix_(ii, ii)], [k for (k, c) in seq],
                  [c for (k, c) in seq])
    return out


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 32
    bl = blocks(K)
    print(f"GRADED TOEPLITZ SYMBOLS   (K={K})\n")
    for g in (0, 1):
        B, ks, cs = bl[g]
        kk = np.array(ks, dtype=float)
        S = np.diag(1.0/kk)
        H = S @ B @ S
        # the translation mode lives in the x-odd-k set, i.e. g = 1
        if g == 1:
            w = np.array([(1.0/k if c == 0 and k % 2 == 1 else 0.0)
                          for k, c in zip(ks, cs)])*kk
            w = w/np.linalg.norm(w)
            U, sv, _ = np.linalg.svd(np.eye(len(w)) - np.outer(w, w))
            P = U[:, sv > 1e-10]
            h1 = float(np.linalg.eigvalsh(P.T @ H @ P).min())
            l2b = float(np.linalg.eigvalsh(
                (P.T @ np.diag(kk)) @ H @ (np.diag(kk) @ P)).min()) \
                if False else float(np.linalg.eigvalsh(P.T @ (S @ B @ S) @ P).min())
        else:
            h1 = float(np.linalg.eigvalsh(H).min())
        l2 = float(np.linalg.eigvalsh(B).min())
        lo, hi = K//4, K
        a = {}
        for D in range(0, K, 1):
            vals = [B[i, i+D]/(ks[i]*ks[i+D])
                    for i in range(lo-1, K-D) if i+D < K]
            if len(vals) >= 3:
                a[D] = (float(np.mean(vals)), float(np.std(vals)))
        th = np.linspace(0, math.pi, 20001)
        f = np.full_like(th, a[0][0])
        for D in sorted(a):
            if D:
                f = f + 2*a[D][0]*np.cos(D*th)
        fmin = float(f.min())
        print(f"  g={g} block  (dim {len(ks)}; components "
              f"{'x odd-k / y even-k' if g==1 else 'y odd-k / x even-k'})")
        print(f"     L2 margin {l2:10.4f}   H1 margin {h1:10.6f}")
        print(f"     symbol a_0 = {a[0][0]:+8.4f} +- {a[0][1]:.4f}   "
              f"a_1 = {a[1][0]:+8.4f} +- {a[1][1]:.4f}   "
              f"a_2 = {a[2][0]:+8.4f} +- {a[2][1]:.4f}")
        print(f"     min symbol {fmin:10.6f}   vs H1 margin {h1:10.6f}   "
              f"|diff| {abs(fmin-h1):.4f}  "
              f"[{'CONSISTENT' if abs(fmin-h1) < 0.05 else 'INCONSISTENT'}]")
        print(f"     tail requirement f_min >= m/K^2 = {TARGET/K**2:.5f}  "
              f"[{'SATISFIED' if fmin > TARGET/K**2 else 'FAILS'}]\n")


if __name__ == "__main__":
    main()
