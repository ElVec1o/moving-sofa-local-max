"""sigma_weld.py — THE WELD (Theorem 9, item 12b).

M := -Q_rel + (cot b / b)(D1 + D2)  is a genuine quadratic form with
-Q_true >= M (interpolation estimate, sigma_interp.py).  Coercivity of M on
ALL of L^2 is therefore an ordinary 2x2 block problem: split eta = eta_N +
eta_T at a cutoff K0,

    M(eta) >= m_N ||eta_N||^2 - 2 tau ||eta_N|| ||eta_T|| + c_T ||eta_T||^2

which is positive definite iff  tau^2 < m_N c_T, with margin

    m = 1/2 [ (m_N + c_T) - sqrt( (m_N - c_T)^2 + 4 tau^2 ) ].

This script performs that weld INSIDE the computed range (cutoff K0 within
K), which exhibits the mechanism and its constants.  The extension to all of
L^2 additionally needs c_T for every mode above the computed range; that is
supplied structurally by the per-arc Wirtinger forms (each active arc
contributes ~ +2k^2 x mask to -Q_rel, so the middle-supported tail grows like
k^2) together with the bite for cap-supported directions (frequency-
independent, measured to saturate at ~3600) -- see PROGRAM.md.

Usage: python3 sigma_weld.py [K] [K0]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sigma_interp import cap_grams, COTB
from sofa_romik2017_reference import BETA


def weld_margin(mN, cT, tau):
    if mN <= 0 or cT <= 0:
        return float('nan')
    return 0.5*((mN + cT) - math.sqrt((mN - cT)**2 + 4*tau*tau))


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    K0 = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    Q = np.load(os.path.join(THIS, f"sigma_rel_K{K}.npy"))
    Q = 0.5*(Q + Q.T)
    n = 2*K
    D1, D2, modes = cap_grams(K)
    gl = math.pi/4
    A = (-Q + (COTB/BETA)*(D1 + D2))/gl          # M in L^2-normalized coords

    # translation direction, projected out
    w = np.zeros(n)
    for i, (c, k) in enumerate(modes):
        if c == 0:
            w[i] = (1.0/k) if (k % 2 == 1) else 0.0
    wn = w/np.linalg.norm(w)
    U, sv, _ = np.linalg.svd(np.eye(n) - np.outer(wn, wn))
    P = U[:, sv > 1e-10]
    Aq = P.T @ A @ P
    print(f"K={K}  cutoff K0={K0}")
    print(f"  full-block margin m(M) = {np.linalg.eigvalsh(Aq).min():.4f}")

    # block split in the ORIGINAL mode basis (low = k<=K0 in both components)
    lowidx = [i for i, (c, k) in enumerate(modes) if k <= K0]
    hiidx = [i for i, (c, k) in enumerate(modes) if k > K0]
    # project out translation within the low block only (it lives there)
    wl = w[lowidx]
    wl = wl/np.linalg.norm(wl)
    Ul, svl, _ = np.linalg.svd(np.eye(len(lowidx)) - np.outer(wl, wl))
    Pl = Ul[:, svl > 1e-10]
    ANN = Pl.T @ A[np.ix_(lowidx, lowidx)] @ Pl
    ANT = Pl.T @ A[np.ix_(lowidx, hiidx)]
    ATT = A[np.ix_(hiidx, hiidx)]

    mN = float(np.linalg.eigvalsh(ANN).min())
    cT = float(np.linalg.eigvalsh(ATT).min())
    tau = float(np.linalg.svd(ANT, compute_uv=False).max())
    m = weld_margin(mN, cT, tau)
    print(f"  m_N (low block, k<=K0)     = {mN:10.4f}")
    print(f"  c_T (tail block, k>K0)     = {cT:10.4f}")
    print(f"  tau (coupling, spec. norm) = {tau:10.4f}")
    print(f"  weld condition tau^2 < m_N c_T : {tau*tau:.4f} < {mN*cT:.4f}  "
          f"{'SATISFIED' if tau*tau < mN*cT else 'FAILS'}")
    print(f"  => welded margin m = {m:.4f}")


if __name__ == "__main__":
    main()
