"""ambi_functional.py — P3c: the niche functional in convex-linear data, exactly.

RESULT ESTABLISHED BY ambi_mamikon / ambi_split / ambi_outerarm, assembled here.

Write  F(t) = h_K(mu_t),  G(t) = h_K(nu_t).  Pushing both outer walls of the hallway
in until they touch puts the inner corner at

    c(t) = (F(t) - 1) mu_t + (G(t) - 1) nu_t,                                    (C)

an AFFINE-LINEAR function of the support function, hence convex-linear on Baek's
domain (Thm 7.1.2).  Define three convex-linear scalars:

    alpha_1(t) = -<c'(t), mu_t> = G(t) - 1 - F'(t)          (face-1 arm)
    alpha_2(t) =  <c'(t), nu_t> = F(t) - 1 + G'(t)          (face-2 arm)
    sigma(t)   =  c_y(t) / cos t = (F(t)-1) tan t + G(t) - 1 (face-1 reach to the floor)

The normal velocity of the face-i line at distance s from the corner is alpha_2 - s on
face 2 and s - alpha_1 on face 1.  So the niche is created by the INNER part of face 2
and the OUTER part of face 1, giving the disjoint decomposition (measured exact)

    N  =  W_2  (+)  W_1out,

    |N| = int_0^{pi/2} [ (1/2)(alpha_2^+)^2  +  (1/2)(sigma-alpha_1)^2
                                             -  (1/2)(alpha_1^-)^2 ] dt.       (V)

Every ingredient is convex-linear.  The first two terms are CONVEX quadratics -- what
Baek's Mamikon theorem 7.4.2 buys.  The third is subtracted, so it contributes a
CONVEX term to Q = |C2| - 2V and is the one obstruction left to concavity; it is
supported exactly on [0,beta), the degenerate phase, where alpha_1 < 0.

This script computes (V) from EXACT derivatives of SOL1/SOL5/SOL6 (no finite
differences) and studies convergence, so that "V = |N|" is tested at a level finer than
the discretisation of either side.  In complex form (J <-> i):

    SOL1  z(t) = a1 e^{2it}      - (1 + i/2) e^{it} + (1 - a1 + i/2)
    SOL6  z(t) = (f1 - i f2) e^{3it/2} - (1 + i) e^{it} + (1 - (4/3)a1 + i/2)
    SOL5  z(t) = a1 e^{2it}      - (1/2 + i) e^{it} + (1 - (5/3)a1 + i/2)

(the exponents 3/2 and 1/2 in SOL6 are the characteristic exponents of ODE6).

Usage: python3 ambi_functional.py
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sofa_romik2017_reference import (BETA, A1_const, F1_const, F2_const, x_path)

PI2 = math.pi/2
A1, F1, F2 = A1_const, F1_const, F2_const
K1 = complex(1 - A1, 0.5)
K6 = complex(1 - (4.0/3.0)*A1, 0.5)
K5 = complex(1 - (5.0/3.0)*A1, 0.5)
A_R = 1.6449552184254408


def z_and_dz(t):
    """exact z(t), z'(t) for Sigma's rotation path"""
    if t < BETA:
        e2, e1 = np.exp(2j*t), np.exp(1j*t)
        return A1*e2 - (1+0.5j)*e1 + K1, 2j*A1*e2 - 1j*(1+0.5j)*e1
    if t <= PI2 - BETA:
        e32, e1 = np.exp(1.5j*t), np.exp(1j*t)
        c = complex(F1, -F2)
        return c*e32 - (1+1j)*e1 + K6, 1.5j*c*e32 - 1j*(1+1j)*e1
    e2, e1 = np.exp(2j*t), np.exp(1j*t)
    return A1*e2 - (0.5+1j)*e1 + K5, 2j*A1*e2 - 1j*(0.5+1j)*e1


def data(ts):
    """alpha_1, alpha_2, sigma at the given t's, from exact derivatives"""
    a1 = np.zeros(len(ts)); a2 = np.zeros(len(ts)); sg = np.zeros(len(ts))
    for i, t in enumerate(ts):
        t = float(t)
        z, dz = z_and_dz(t)
        e = np.exp(-1j*t)                       # <v,mu> + i<v,nu> = e^{-it} v
        w = e*dz
        a1[i] = -w.real
        a2[i] = w.imag
        ct = math.cos(t)
        # sigma = c_y / cos t, with the removable singularity at t = pi/2
        if ct > 1e-9:
            sg[i] = z.imag/ct
        else:
            _, dz2 = z_and_dz(t - 1e-6)
            sg[i] = -dz2.imag/math.sin(t)       # l'Hopital: c_y'/(-cos t)' = -c_y'/sin t
    return a1, a2, sg


def V_of(nt):
    """the functional (V) by Gauss-Legendre on each phase separately, so the two
    kinks at beta and pi/2-beta are never straddled by a quadrature interval"""
    tot = 0.0; parts = []
    for lo, hi in ((0.0, BETA), (BETA, PI2 - BETA), (PI2 - BETA, PI2)):
        xg, wg = np.polynomial.legendre.leggauss(nt)
        tsub = 0.5*(hi - lo)*xg + 0.5*(hi + lo)
        wsub = 0.5*(hi - lo)*wg
        a1, a2, sg = data(tsub)
        integ = (0.5*np.maximum(a2, 0.0)**2
                 + 0.5*(sg - a1)**2
                 - 0.5*np.maximum(-a1, 0.0)**2)
        p = float(wsub @ integ)
        parts.append(p); tot += p
    return tot, parts


def main():
    print("P3c: THE NICHE FUNCTIONAL IN CONVEX-LINEAR DATA\n")
    # sanity: exact closed forms agree with the reference piecewise path
    err = max(abs(complex(*x_path(t)) - z_and_dz(t)[0])
              for t in np.linspace(1e-9, PI2 - 1e-9, 3001))
    print(f"exact complex forms vs reference x_path:  max err {err:.3e}\n")

    print(f"{'n_gauss':>8} {'V':>15} {'[0,beta)':>13} {'middle':>13} "
          f"{'(pi/2-b,pi/2]':>14}")
    prev = None
    for nt in (20, 40, 80, 160, 320):
        V, parts = V_of(nt)
        print(f"{nt:8d} {V:15.12f} {parts[0]:13.10f} {parts[1]:13.10f} "
              f"{parts[2]:14.10f}"
              + (f"   d={V-prev:+.2e}" if prev is not None else ""))
        prev = V
    V, parts = V_of(320)

    # the concave (obstruction) term, and its closed form on [0,beta)
    xg, wg = np.polynomial.legendre.leggauss(320)
    tsub = 0.5*BETA*xg + 0.5*BETA
    wsub = 0.5*BETA*wg
    a1, a2, sg = data(tsub)
    C_obs = float(wsub @ (0.5*np.maximum(-a1, 0.0)**2))
    # closed form: alpha_1 = 2 a1 sin t - 1/2 on [0,beta), so
    #   (1/2) int_0^beta (1/2 - 2a1 sin t)^2 dt
    #     = (1/8)beta - a1(1 - cos beta) + a1^2(beta - sin(2beta)/2)
    cf = (0.125*BETA - A1*(1 - math.cos(BETA))
          + A1*A1*(BETA - 0.5*math.sin(2*BETA)))
    print(f"\nthe obstruction term  (1/2) int (alpha_1^-)^2 dt")
    print(f"    quadrature   = {C_obs:.12f}")
    print(f"    closed form  = {cf:.12f}   (= beta/8 - a1(1-cos b) "
          f"+ a1^2(b - sin2b/2))")
    print(f"    err          = {abs(C_obs-cf):.3e}")
    print(f"    as a fraction of V: {100*C_obs/V:.3f}%")

    # arm supports, and what Baek's condition needs where
    print(f"\nbeta = {BETA:.12f}   pi/2 - beta = {PI2-BETA:.12f}")
    tsc = np.linspace(1e-9, PI2-1e-9, 20001)
    a1, a2, sg = data(tsc)
    print(f"    alpha_1 > 0 on [{tsc[a1>0].min():.6f}, {tsc[a1>0].max():.6f}]"
          f"   (= [beta, pi/2])")
    print(f"    alpha_2 > 0 on [{tsc[a2>0].min():.6f}, {tsc[a2>0].max():.6f}]"
          f"   (= [0, pi/2-beta])")
    print(f"    sigma - alpha_1 >= 0 everywhere? "
          f"{'yes' if (sg-a1).min() >= -1e-12 else 'NO'}   "
          f"min {(sg-a1).min():.3e}")
    print(f"    sigma >= 0 everywhere?  "
          f"{'yes' if sg.min() >= -1e-12 else 'NO'}   min {sg.min():.3e}")

    print(f"\nV = {V:.12f}")
    print(f"|C2| implied by V and A_R*:  A_R* + 2V = {A_R + 2*V:.9f}")
    print(f"(measured |C2| = 2.013345504 at n=721, 2.013342045 at n=481,")
    print(f" so the cap discretisation is still O(1e-5) and this is consistent)")


if __name__ == "__main__":
    main()
