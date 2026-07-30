"""ambi_mamikon.py — P3c: is the niche of Sigma a sum of MAMIKON regions?

Baek's upper bound needs a functional  Q(K) = |K| - 2 V(K)  with V CONVEX quadratic
and  V(K) <= |N(K)|  for every K in the convex domain, with EQUALITY at the candidate.
Then Q is concave quadratic, Q >= |sofa|, and a first-order condition finishes.

This script reconstructs the convex-linear data from scratch and measures the identity.

SETUP (this repo's hallway convention: L = {y<=1, x<=1} \\ {x<0, y<0}, corner (0,0)).
Placing the hallway at angle t with its corner at c(t) and pushing both outer walls in
until they touch the cap K gives

    h_K(mu_t) = <c(t), mu_t> + 1,      h_K(nu_t) = <c(t), nu_t> + 1,           (1)

so, writing  F(t) := h_K(mu_t),  G(t) := h_K(nu_t),

    c(t) = (F(t) - 1) mu_t + (G(t) - 1) nu_t                                   (2)

is an AFFINE-LINEAR function of the support function, hence convex-linear on Baek's
domain (his Thm 7.1.2).  The removed wedge is

    Q_t = { <p, mu_t> < F(t) - 1 } ^ { <p, nu_t> < G(t) - 1 },   N = (union_t Q_t) ^ K.

Differentiating (2),  <c', mu_t> = F' - G + 1 - 1 = F' - (G - 1) - ... ; done cleanly
below in code.  The two wedge faces are the rays c - s nu_t and c - s mu_t and the arm
lengths are

    alpha_1(t) = -<c'(t), mu_t> = f(t) - 1,     alpha_2(t) = <c'(t), nu_t> = g(t) - 1,

both AFFINE-LINEAR in (F, G) hence convex-linear in K.  Baek's injectivity condition
Def 6.1.2(3) is exactly alpha_1, alpha_2 > 0, i.e. f, g > 1: the contact points B and D
lie on the faces themselves and not on their opposite extensions.

THE MAMIKON CANDIDATE.  Sweep the segment [c(t), c(t) - alpha_i mu-or-nu].  The
Jacobians are computed in the header of each block below and give

    |W_1| = (1/2) int alpha_1^2 dt        (sweep along -nu_t)
    |W_2| = (1/2) int alpha_2^2 dt + int alpha_2 dt   [see note]  (sweep along -mu_t)

Each is a CONVEX quadratic plus a linear term in K, which is what Baek Thm 7.4.2 buys.

WHAT IS MEASURED HERE
  (a) the closed form of the outer phase, including f(t) = 1/2 + 2 a1 sin t and hence
      T3 (4 a1 sin beta = 1) <=> f(beta) = 1 <=> T2;
  (b) |Sigma| = |C2| - 2|N|;
  (c) |W_1 u W_2| against the two Mamikon integrals -- does the area formula hold, i.e.
      is the sweep injective?
  (d) the DEFICIT |N| - |W_1 u W_2|, phase by phase.  This is the whole obstruction:
      if it is zero the construction is tight and P3c closes; if not, its size and
      location say what is missing.

Usage: python3 ambi_mamikon.py [n_hall] [n_sweep]
"""
from __future__ import annotations
import os, sys, math
import numpy as np
from shapely.geometry import Polygon
from shapely.ops import unary_union
from shapely.affinity import rotate as srot, translate as strans, scale as sscale

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sofa_romik2017_reference import (HALLWAY, x_path, BETA, A1_const, F1_const,
                                      F2_const, KAPPA6_1)

BIG = 8.0
PI2 = math.pi / 2
LHORIZ = Polygon([(-BIG, 0), (1, 0), (1, 1), (-BIG, 1)])


# ------------------------------------------------------------------ #
#  (a)  the outer phase in closed form                               #
# ------------------------------------------------------------------ #

def outer_phase_check():
    """On [0,beta) Sigma follows SOL1 with a2 = 0, so in complex form

        z(t) = a1 e^{2it} - (1 + i/2) e^{it} + (1 - a1 + i/2),

    the arm length is f(t) = 1/2 + 2 a1 sin t, and the outer contact A(t) is the
    CONSTANT rho-fixed point (1, 1/2).  Consequently the cap's support function in the
    directions nu_t, t in [0,beta), is that of a disc of radius 1/2 centred at
    (1 - 2a1, 1/2), and f(beta) = 1 is exactly 4 a1 sin beta = 1 (T3), which is exactly
    x'(beta).mu_beta = 0 (T2).  All checked numerically here."""
    a1 = A1_const
    print("(a) OUTER PHASE [0, beta) IN CLOSED FORM")
    print(f"    beta = {BETA:.15f}   a1 = {a1:.15f}")
    err_z = err_f = err_A = err_h = 0.0
    for t in np.linspace(0.0, BETA, 4001)[:-1]:
        c = x_path(t)
        z = a1*np.exp(2j*t) - (1 + 0.5j)*np.exp(1j*t) + (1 - a1 + 0.5j)
        err_z = max(err_z, abs(complex(c[0], c[1]) - z))
        # arm length f = 1 - <x', mu_t>, by centred difference
        hh = 1e-7
        cp = (x_path(t + hh) - x_path(max(t - hh, 0.0))) / (t + hh - max(t - hh, 0.0))
        mu = np.array([math.cos(t), math.sin(t)])
        nu = np.array([-math.sin(t), math.cos(t)])
        f = 1.0 - float(cp @ mu)
        err_f = max(err_f, abs(f - (0.5 + 2*a1*math.sin(t))))
        # A(t) = x + <x',mu> nu + mu  should be the constant (1, 1/2)
        A = c + float(cp @ mu)*nu + mu
        err_A = max(err_A, abs(A[0] - 1.0) + abs(A[1] - 0.5))
        # h_K(nu_t) = <c,nu_t> + 1  should be <(1-2a1,1/2), nu_t> + 1/2
        h = float(c @ nu) + 1.0
        pred = float(np.array([1 - 2*a1, 0.5]) @ nu) + 0.5
        err_h = max(err_h, abs(h - pred))
    print(f"    max |x(t) - a1 e^2it + (1+i/2) e^it - (1-a1+i/2)|  = {err_z:.3e}")
    print(f"    max |f(t) - (1/2 + 2 a1 sin t)|                    = {err_f:.3e}")
    print(f"    max |A(t) - (1, 1/2)|                              = {err_A:.3e}")
    print(f"    max |h_K(nu_t) - [<(1-2a1,1/2),nu_t> + 1/2]|       = {err_h:.3e}")
    print(f"    4 a1 sin beta - 1                                  = "
          f"{4*a1*math.sin(BETA) - 1:.3e}   (T3 = T2 = 'f(beta)=1')")
    print()


# ------------------------------------------------------------------ #
#  cap, sofa, niche                                                  #
# ------------------------------------------------------------------ #

def halfplane(nrm, off):
    """{ p : <p, nrm> <= off } as a big polygon"""
    nx, ny = nrm
    px, py = nx*off, ny*off
    tx, ty = -ny, nx
    return Polygon([(px + BIG*3*tx, py + BIG*3*ty),
                    (px - BIG*3*tx, py - BIG*3*ty),
                    (px - BIG*3*tx - BIG*3*nx, py - BIG*3*ty - BIG*3*ny),
                    (px + BIG*3*tx - BIG*3*nx, py + BIG*3*ty - BIG*3*ny)])


def build(n):
    ts = np.linspace(0.0, PI2, n)
    C1 = LHORIZ
    S = LHORIZ
    for t in ts:
        c = x_path(float(t))
        mu = (math.cos(t), math.sin(t))
        nu = (-math.sin(t), math.cos(t))
        C1 = C1.intersection(halfplane(mu, c @ np.array(mu) + 1.0))
        C1 = C1.intersection(halfplane(nu, c @ np.array(nu) + 1.0))
        H = srot(HALLWAY, math.degrees(t), origin=(0, 0))
        H = strans(H, xoff=float(c[0]), yoff=float(c[1]))
        S = S.intersection(H)
    return ts, C1, S


def arms(ts):
    """alpha_1 = -<c',mu_t>, alpha_2 = <c',nu_t>, plus c itself"""
    cs = np.array([x_path(float(t)) for t in ts])
    a1 = np.zeros(len(ts)); a2 = np.zeros(len(ts))
    hh = 1e-7
    for i, t in enumerate(ts):
        lo, hi = max(float(t) - hh, 0.0), min(float(t) + hh, PI2)
        cp = (x_path(hi) - x_path(lo)) / (hi - lo)
        mu = np.array([math.cos(t), math.sin(t)])
        nu = np.array([-math.sin(t), math.cos(t)])
        a1[i] = -float(cp @ mu)
        a2[i] = float(cp @ nu)
    return cs, a1, a2


def sweep(ts, cs, lens, along):
    """union of the quads swept by [c(t), c(t) - lens(t) * dir(t)]; along = 'nu'|'mu'"""
    quads = []
    for i in range(len(ts) - 1):
        for j in (i, i + 1):
            pass
        t0, t1 = float(ts[i]), float(ts[i + 1])
        d0 = ((-math.sin(t0), math.cos(t0)) if along == 'nu'
              else (math.cos(t0), math.sin(t0)))
        d1 = ((-math.sin(t1), math.cos(t1)) if along == 'nu'
              else (math.cos(t1), math.sin(t1)))
        L0, L1 = max(lens[i], 0.0), max(lens[i + 1], 0.0)
        if L0 <= 0 and L1 <= 0:
            continue
        p0 = cs[i]; p1 = cs[i + 1]
        q0 = (p0[0] - L0*d0[0], p0[1] - L0*d0[1])
        q1 = (p1[0] - L1*d1[0], p1[1] - L1*d1[1])
        poly = Polygon([tuple(p0), q0, q1, tuple(p1)])
        if poly.is_valid and poly.area > 0:
            quads.append(poly)
        else:
            poly = Polygon([tuple(p0), q0, q1, tuple(p1)]).buffer(0)
            if poly.area > 0:
                quads.append(poly)
    return unary_union(quads)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1441
    nsw = int(sys.argv[2]) if len(sys.argv) > 2 else 4001
    outer_phase_check()

    ts, C1, S = build(n)
    rho = lambda G: sscale(G, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
    Sig = S.intersection(rho(S))
    C2 = C1.intersection(rho(C1))
    U = C1.difference(S)
    N = U.intersection(C2)
    A_R = 1.6449552184254408

    print("(b) THE CAP-MINUS-ONE-NICHE IDENTITY   (n_hall = %d)" % n)
    print(f"    |C1| = {C1.area:.9f}    |C2| = {C2.area:.9f}")
    print(f"    |S|  = {S.area:.9f}    |Sigma| = {Sig.area:.9f}   A_R* = {A_R:.9f}")
    print(f"    |U|  = {U.area:.9f}    |N| = |U ^ C2| = {N.area:.9f}")
    print(f"    |C2| - 2|N| = {C2.area - 2*N.area:.9f}   "
          f"vs |Sigma| = {Sig.area:.9f}   err {abs(C2.area-2*N.area-Sig.area):.3e}")
    print()

    tw = np.linspace(0.0, PI2, nsw)
    cs, al1, al2 = arms(tw)
    W1 = sweep(tw, cs, al1, 'nu')
    W2 = sweep(tw, cs, al2, 'mu')
    W = unary_union([W1, W2])
    p1 = np.maximum(al1, 0.0); p2 = np.maximum(al2, 0.0)
    I1 = 0.5*np.trapezoid(p1**2, tw)
    I2 = 0.5*np.trapezoid(p2**2, tw)
    L2 = np.trapezoid(p2, tw)

    print("(c) THE TWO MAMIKON SWEEPS   (n_sweep = %d)" % nsw)
    print(f"    arm 1 (along -nu, contact B): positive on t in "
          f"[{tw[p1>0].min() if (p1>0).any() else float('nan'):.6f}, "
          f"{tw[p1>0].max() if (p1>0).any() else float('nan'):.6f}]")
    print(f"    arm 2 (along -mu, contact D): positive on t in "
          f"[{tw[p2>0].min() if (p2>0).any() else float('nan'):.6f}, "
          f"{tw[p2>0].max() if (p2>0).any() else float('nan'):.6f}]")
    print(f"    beta = {BETA:.9f}   pi/2 - beta = {PI2-BETA:.9f}")
    print(f"    |W1| measured = {W1.area:.9f}    (1/2)int alpha_1^2 = {I1:.9f}"
          f"    ratio {W1.area/I1 if I1 else float('nan'):.6f}")
    print(f"    |W2| measured = {W2.area:.9f}    (1/2)int alpha_2^2 = {I2:.9f}"
          f"    +int alpha_2 = {I2+L2:.9f}")
    print(f"    |W1 u W2| = {W.area:.9f}    |W1|+|W2| = {W1.area+W2.area:.9f}"
          f"    overlap = {W1.area+W2.area-W.area:.9f}")
    print()

    WN = W.intersection(C2)
    print("(d) THE DEFICIT")
    print(f"    |W ^ C2| = {WN.area:.9f}   |N| = {N.area:.9f}")
    print(f"    W ^ C2 inside N? leak = {WN.difference(N).area:.3e}")
    print(f"    DEFICIT |N| - |W ^ C2| = {N.area - WN.area:.9f}"
          f"   ({100*(N.area-WN.area)/N.area:.2f}% of the niche)")
    Def = N.difference(W)
    print(f"    deficit region: area {Def.area:.9f}, "
          f"{1 if Def.geom_type=='Polygon' else len(Def.geoms)} piece(s), "
          f"bbox {tuple(round(v,4) for v in Def.bounds)}")
    print(f"    upper bound it gives: |C2| - 2|W ^ C2| = "
          f"{C2.area - 2*WN.area:.9f}   (need >= {A_R:.9f}, "
          f"slack {C2.area - 2*WN.area - A_R:.9f})")


if __name__ == "__main__":
    main()
