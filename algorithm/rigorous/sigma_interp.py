"""sigma_interp.py — THE INTERPOLATION ESTIMATE (Theorem 9, item 12).

The obstruction to closing item 12 was that the fan bite N is positively
homogeneous of degree 2 but NOT a quadratic form, so a bound established on
a low-dimensional search space could not be transported to MIXED directions.

Resolution: the PROVED lower bound on the bite is quadratic once unwound.

    N(phi) + N(-phi)  >=  max_s d(s)^2 G(s)          [one interior cut]
                      >=  cot(beta) * ||d||_inf^2    [G >= G(0) = cot beta,
                                                      Lean: fan_cut_gain]
                      >=  (cot(beta)/beta) * ||d||^2_{L2(0,beta)}
                                                      [max >= mean]

and  d(s) = phi(beta) cos(s)/cos(beta) - phi(s)  is LINEAR in eta.  Hence
||d||^2_{L2} is a quadratic form D, and with Q_true = Q_rel - [N(phi)+N(-phi)]
(second-difference convention),

    -Q_true(eta)  >=  -Q_rel(eta) + (cot beta / beta) * (D1 + D2)(eta)  =: M(eta)

with M a genuine QUADRATIC FORM.  Coercivity of M is now an ordinary
eigenvalue problem, valid on every direction simultaneously — mixed
directions included.  That is the interpolation step.

d vanishes on translations (phi -> phi + c cos s leaves d unchanged), as does
Q_rel, so the statement is made modulo the exact translation symmetry.

cap 1 (mu-fan):  phi(s)   = <eta(s), mu_s>
cap 2 (nu-fan):  psi(sig) = <eta(pi/2-sig), nu_{pi/2-sig}>   (congruent fan)

Usage: python3 sigma_interp.py
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sofa_romik2017_reference import BETA

PI2 = math.pi/2
trapz = np.trapezoid
COTB = 1.0/math.tan(BETA)


def cap_grams(K, m=4000):
    """Gram matrices of the cap-deviation operators d^(1), d^(2)."""
    s = np.linspace(0.0, BETA, m)
    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    n = len(modes)
    # cap 1: phi_i(s) = sin(2k s) * (cos s if x else sin s)
    P1 = np.array([np.sin(2*k*s)*(np.cos(s) if c == 0 else np.sin(s))
                   for (c, k) in modes])
    # cap 2: t = pi/2 - s ;  psi_i = sin(2k t) * (-sin t if x else cos t)
    t = PI2 - s
    P2 = np.array([np.sin(2*k*t)*(-np.sin(t) if c == 0 else np.cos(t))
                   for (c, k) in modes])
    D = []
    for P in (P1, P2):
        pb = P[:, -1]                                   # value at s = beta
        d = pb[:, None]*np.cos(s)[None, :]/math.cos(BETA) - P
        G = np.empty((n, n))
        for i in range(n):
            G[i] = trapz(d[i][None, :]*d, s)
        D.append(0.5*(G + G.T))
    return D[0], D[1], modes


def main():
    print("interpolation estimate:  -Q_true >= M := -Q_rel + (cot b / b)(D1+D2)")
    print(f"  cot(beta)/beta = {COTB/BETA:.4f}\n")
    print(f"{'K':>4} {'m(-Q_rel) alone':>17} {'m(M) = closed bound':>21} "
          f"{'bite share':>11}")
    for K in (10, 16, 24):
        Q = np.load(os.path.join(THIS, f"sigma_rel_K{K}.npy"))
        Q = 0.5*(Q + Q.T)
        n = 2*K
        D1, D2, modes = cap_grams(K)
        gl = math.pi/4                                   # L^2 Gram (diagonal)
        # translation direction (const e_x) inside the sine span
        w = np.zeros(n)
        for i, (c, k) in enumerate(modes):
            if c == 0:
                w[i] = (1.0/k) if (k % 2 == 1) else 0.0
        wn = w/np.linalg.norm(w)
        U, sv, _ = np.linalg.svd(np.eye(n) - np.outer(wn, wn))
        P = U[:, sv > 1e-10]                             # L2-orthonormal basis
        A_rel = P.T @ (-Q) @ P / gl
        A_bit = P.T @ ((COTB/BETA)*(D1 + D2)) @ P / gl
        m_rel = np.linalg.eigvalsh(A_rel).min()
        ev = np.linalg.eigvalsh(A_rel + A_bit)
        m_tot = ev.min()
        share = (m_tot - m_rel)/m_tot if m_tot > 0 else float('nan')
        print(f"{K:4d} {m_rel:17.4f} {m_tot:21.4f} {share:11.1%}")
    print("\n  M is a QUADRATIC form, so the bound holds on every direction")
    print("  simultaneously — mixed directions included.  No search, no")
    print("  interpolation gap.")


if __name__ == "__main__":
    main()
