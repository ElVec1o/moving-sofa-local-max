"""ambi_domination.py — the decisive test:  is  V(H) <= |N(H)|  for COMPETITORS?

WHY THIS IS THE WHOLE QUESTION.  For any ambidextrous sofa T with cap data H,

    |T| <= |C2| - 2|N| ,        equality for the maximal one T = C2 \\ (U u rho U),

so  Q := |C2| - 2V  is an upper bound for |T| if and only if  V <= |N|.  If instead
V > |N| then Q < |C2| - 2|N| = |T_max|, and Q is NOT an upper bound: it is BELOW the
area of the very sofa it is supposed to bound.

A STRUCTURAL WARNING FIRST.  V is the exact flux of the advancing wedge boundary:

    V = int [ (1/2)(a2^+)^2 + int_{a1^+}^{sigma}(s-a1) ds ] dt .

Reynolds' transport says the area gained by the sweeping region is AT MOST the flux --
advance into already-swept territory is counted by the flux but gains no area.  Hence

    V >= |N|      ALWAYS,     with equality iff nothing is re-swept.

That is the wrong direction.  Baek's construction avoids it by building the niche
UNDERestimate from a core and two tails on which injectivity is proved, so that the flux
integral equals the area of a genuine SUBSET.  Our V is the exact flux, tight at Sigma
precisely because nothing is re-swept there.

So the question this script settles is quantitative: for competitors, how big is
V - |N|?  If it is second order in the perturbation and Sigma is the unique zero, then
Q touches the true bound only at Sigma and falls below it on both sides, and Q cannot
certify anything.  If V - |N| vanishes identically on the domain, the architecture goes
through.

METHOD.  Perturb H = H_Sigma + eps*eta with eta a smooth bump supported where
H + H'' >= 1/2 (so convexity survives), rebuild the corner path from
c(t) = (F-1) mu_t + (G-1) nu_t, measure |N| with the polygon oracle, and compare with V
evaluated from the same H by Gauss-Legendre.  Both signs of eps are tried, since a
one-sided test cannot distinguish a genuine inequality from a critical point.

Usage: python3 ambi_domination.py [n_hall]
"""
from __future__ import annotations
import os, sys, math
import numpy as np
from shapely.geometry import Polygon
from shapely.affinity import scale as sscale

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from ambi_hessian import H_and_dH, gl_split, PI, PI2
from ambi_mamikon import halfplane, LHORIZ
from sofa_romik2017_reference import BETA

BIG = 8.0


def bump(th, c0, w):
    """smooth compactly supported bump centred at c0 of half-width w, and its
    derivative; zero (with all derivatives) outside"""
    z = (np.asarray(th, dtype=float) - c0)/w
    out = np.zeros_like(z); dout = np.zeros_like(z)
    m = np.abs(z) < 1.0
    zm = z[m]
    e = np.exp(-1.0/(1.0 - zm*zm))
    out[m] = e
    dout[m] = e * (-2.0*zm/(1.0 - zm*zm)**2) / w
    return out, dout


def H_pert(th, eps, c0, w):
    H, dH = H_and_dH(np.atleast_1d(th))
    b, db = bump(th, c0, w)
    return H + eps*b, dH + eps*db


def corner(t, eps, c0, w):
    """c(t) = (F-1) mu_t + (G-1) nu_t with F = H(t), G = H(t+pi/2)"""
    F, _ = H_pert([t], eps, c0, w)
    G, _ = H_pert([t + PI2], eps, c0, w)
    mu = np.array([math.cos(t), math.sin(t)])
    nu = np.array([-math.sin(t), math.cos(t)])
    return (F[0] - 1.0)*mu + (G[0] - 1.0)*nu, F[0], G[0]


def measure_N(eps, c0, w, n):
    """|N| = |U ^ C2| for the perturbed body, by the polygon oracle"""
    ts = np.linspace(0.0, PI2, n)
    C = LHORIZ
    wedges = []
    for t in ts:
        t = float(t)
        c, F, G = corner(t, eps, c0, w)
        mu = (math.cos(t), math.sin(t)); nu = (-math.sin(t), math.cos(t))
        C = C.intersection(halfplane(mu, F))
        C = C.intersection(halfplane(nu, G))
        wedges.append((c, mu, nu))
    rho = lambda G_: sscale(G_, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
    C2 = C.intersection(rho(C))
    S = C
    for c, mu, nu in wedges:
        # remove Q_t = {<p-c,mu> < 0} ^ {<p-c,nu> < 0}  from S
        q = halfplane(mu, float(np.dot(c, mu))).intersection(
            halfplane(nu, float(np.dot(c, nu))))
        S = S.difference(q)
    return C.difference(S).intersection(C2).area, C2.area


def V_of(eps, c0, w, ng=200):
    tot = 0.0
    for lo, hi in ((0.0, BETA), (BETA, PI2 - BETA), (PI2 - BETA, PI2)):
        x, wq = np.polynomial.legendre.leggauss(ng)
        T = 0.5*(hi - lo)*x + 0.5*(hi + lo); W = 0.5*(hi - lo)*wq
        F, dF = H_pert(T, eps, c0, w)
        G, dG = H_pert(T + PI2, eps, c0, w)
        a1 = G - 1.0 - dF
        a2 = F - 1.0 + dG
        sg = (F - 1.0)*np.tan(T) + G - 1.0
        tot += float(W @ (0.5*np.maximum(a2, 0.0)**2 + 0.5*(sg - a1)**2
                          - 0.5*np.maximum(-a1, 0.0)**2))
    return tot


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 601
    c0, w = 1.0, 0.45          # bump inside [beta, pi/2-beta], H+H'' >= 0.5 there
    print("IS  V <= |N|  FOR COMPETITORS?   (bump at theta = %.2f, half-width %.2f)\n"
          % (c0, w))
    print("  Reynolds says V >= |N| always.  Domination needs V <= |N|.")
    print("  So the architecture works only if V = |N| identically.\n")
    N0, C20 = measure_N(0.0, c0, w, n)
    V0 = V_of(0.0, c0, w)
    print(f"  {'eps':>8} {'|N| (oracle)':>14} {'V (exact)':>14} {'V - |N|':>12} "
          f"{'|C2|':>12}")
    print(f"  {0.0:8.4f} {N0:14.9f} {V0:14.9f} {V0-N0:12.2e} {C20:12.9f}"
          f"   <- Sigma")
    rows = []
    for eps in (-0.20, -0.10, -0.05, 0.05, 0.10, 0.20):
        N, C2 = measure_N(eps, c0, w, n)
        V = V_of(eps, c0, w)
        rows.append((eps, N, V, V - N))
        print(f"  {eps:8.4f} {N:14.9f} {V:14.9f} {V-N:12.2e} {C2:12.9f}")
    print(f"\n  oracle bias at Sigma (known): V0 - N0 = {V0-N0:.2e}; the oracle")
    print(f"  under-measures |N| by O(1/n), so subtract that baseline:")
    print(f"  {'eps':>8} {'(V-|N|) - baseline':>20} {'/eps^2':>12}")
    for eps, N, V, d in rows:
        print(f"  {eps:8.4f} {d-(V0-N0):20.3e} {(d-(V0-N0))/eps**2:12.4f}")
    print(f"\n  READING.  If the excess grows like eps^2 with a positive coefficient,")
    print(f"  Sigma is an isolated zero of V - |N| and Q falls BELOW the true bound on")
    print(f"  both sides, so Q certifies nothing.  If the excess stays at the oracle")
    print(f"  noise level, V = |N| identically and the architecture goes through.")


if __name__ == "__main__":
    main()
