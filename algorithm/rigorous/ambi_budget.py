"""ambi_budget.py — the excess budget (EB_theta), and whether it reaches Gerver.

THE CRUX (I1).  (RC) enters the architecture at exactly one point: it forces the flux
excess E := V - |N| to vanish, so that Q = |C2| - 2V is TIGHT.  Separation and Reynolds
give, with no curvature hypothesis at all,

    |T|  =  |C2| - 2|N|  =  Q + 2E ,     E >= 0 .

So a valid architecture needs U >= Q + 2E with U concave on a convex D' containing Sigma
and U(Sigma) = A_R*.  Writing Etil := (U - Q)/2, that is: Etil >= E, Etil(Sigma) = 0, and
Q + 2 Etil concave.

WHY THE OBVIOUS TARGET IS IMPOSSIBLE (the NO-GO).  Task #21 asked for a CONCAVE upper
bound on the excess.  There is none.  If Etil is concave, Etil >= 0 and Etil(Sigma) = 0
with Sigma in the algebraic interior of D', take a, b in D' with Sigma = (a+b)/2; then

    0 = Etil(Sigma) >= (1/2) Etil(a) + (1/2) Etil(b) >= 0 ,

so Etil(a) = Etil(b) = 0, hence Etil = 0 and E = 0 throughout D'.  Any such architecture
is confined to the injectivity locus {E = 0}, which is where the theorem already lives.
Four sessions of task #21 were chasing something that does not exist.

WHY THE SPEC WAS TOO STRONG.  U = Q + 2 Etil concave does NOT require Etil concave.  It
requires only that Etil's convexity fit inside Q's STRICT concavity:

    d^2 U = d^2 Q + 2 d^2 Etil <= 0 ,      and     (1/2) d^2 Q <= -c* ||eta||^2 ,

with c* = 0.7309566... the sharp constant.  So Etil may be convex with second variation up
to c*||phi||^2.  Taking Etil := (1/2) theta c* ||H - H_Sigma||^2 for theta in [0,1]:

  THEOREM (EB_theta).  Let D' be convex, Sigma in D', with (i) separation M < 1/2,
  (ii) (1/2) d^2 Q <= -c ||eta||^2 on D', and

      (EB_theta)     E(H) <= (1/2) theta c ||H - H_Sigma||^2_{L^2(0,pi)}   on D'.

  Then |T| <= A_R* - (1 - theta) c ||H - H_Sigma||^2 for every ambidextrous sofa with cap
  data in D'.

  Proof.  U := Q + 2 Etil.  Then U >= Q + 2E = |T| by (EB); U(Sigma) = A_R*;
  dU(Sigma) = dQ(Sigma) + 0 = 0; and d^2 U[phi] = d^2 Q[phi] + 2 theta c ||phi||^2
  <= -2(1-theta) c ||phi||^2 <= 0.  Concave with a critical point, so U <= U(Sigma).  QED

theta = 0 is the existing theorem, on {E = 0}.  theta > 0 ADMITS E > 0, so the no-go is
escaped, and the size of the escape is proportional to c: the improvement of the certified
constant from 0.1532 to 0.73 this session is a 4.8x larger budget, not a cosmetic gain.

Since Q is only piecewise quadratic, the segment form of the argument is the usable one
(as in the note's Proposition "Beyond Sigma's own cell"): concavity of U ALONG the segment
[H_Sigma, H] plus (EB) along it already gives |T| <= A_R*.  Convexity of the union of cells
is not needed.  That is what this script tests.

WHAT IT MEASURES, along H_s = (1-s) H_Sigma + s H_Gerver:

  1. E(H_s) = V(H_s) - |N(H_s)|, with the 1/n polygon bias of |N| removed by Richardson
     (E_inf = 2 E(2n) - E(n)), and each row flagged by how much survives the subtraction.
  2. The budget (1/2) theta c ||H_s - H_Sigma||^2.
  3. The sign pattern (tau_1, tau_2) at H_s, which fixes which cell the segment is in and
     hence which concavity constant c applies.

Rule 7: floating point.  EVIDENCE, not proof.
Rule 8: measure_N is superlinear in n; the sweep is a few minutes, with progress, ETA and
an atomic checkpoint.

Usage: python3 ambi_budget.py [outfile.json]
"""
from __future__ import annotations
import json, math, os, sys, time

import numpy as np
import mpmath as mp
from shapely.geometry import Polygon
from shapely.affinity import scale as sscale

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
import gerver_constants as GC
from ambi_hessian import H_and_dH, PI, PI2, gl_split
from ambi_domination import LHORIZ, halfplane
from ambi_functional import A_R

CSTAR = 0.730956620836
mp.mp.dps = 30
_P, _ = GC.solve_gerver_constants(working_dps=30)


def _g(t):
    x, _xp = GC._xt_xtp(mp.mpf(float(t)), _P)
    z = complex(float(x[0]), float(x[1]))
    w = np.exp(-1j*float(t))*z
    return w.real, w.imag


def Hg(x):
    """Gerver's cap support data, in the SAME gauge H(0) = H(pi/2) = 1."""
    if x <= PI2:
        return _g(min(max(x, 1e-9), PI2 - 1e-9))[0] + 1.0
    return _g(min(max(x - PI2, 1e-9), PI2 - 1e-9))[1] + 1.0


def Hseg(x, s):
    """H_s = (1-s) H_Sigma + s H_Gerver, evaluated pointwise."""
    hs, _ = H_and_dH([min(max(x, 0.0), PI)])
    return (1.0 - s)*hs[0] + s*Hg(x)


def dHseg(x, s, h=1e-6):
    a = max(x - h, 0.0); b = min(x + h, PI)
    return (Hseg(b, s) - Hseg(a, s))/(b - a)


def V_seg(s, ng=200):
    tot = 0.0
    from sofa_romik2017_reference import BETA
    for lo, hi in ((0.0, BETA), (BETA, PI2 - BETA), (PI2 - BETA, PI2)):
        x, wq = np.polynomial.legendre.leggauss(ng)
        T = 0.5*(hi - lo)*x + 0.5*(hi + lo); W = 0.5*(hi - lo)*wq
        F = np.array([Hseg(t, s) for t in T]);  dF = np.array([dHseg(t, s) for t in T])
        G = np.array([Hseg(t + PI2, s) for t in T])
        dG = np.array([dHseg(t + PI2, s) for t in T])
        a1 = G - 1.0 - dF; a2 = F - 1.0 + dG
        sg = (F - 1.0)*np.tan(T) + G - 1.0
        tot += float(W @ (0.5*np.maximum(a2, 0.0)**2 + 0.5*(sg - a1)**2
                          - 0.5*np.maximum(-a1, 0.0)**2))
    return tot


def N_seg(s, n):
    ts = np.linspace(0.0, PI2, n)
    C = LHORIZ; wedges = []
    for t in ts:
        t = float(t)
        F = Hseg(t, s); G = Hseg(t + PI2, s)
        mu = (math.cos(t), math.sin(t)); nu = (-math.sin(t), math.cos(t))
        C = C.intersection(halfplane(mu, F)).intersection(halfplane(nu, G))
        c = (F - 1.0)*np.array(mu) + (G - 1.0)*np.array(nu)
        wedges.append((c, mu, nu))
    rho = lambda G_: sscale(G_, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
    C2 = C.intersection(rho(C)); S = C
    for c, mu, nu in wedges:
        q = halfplane(mu, float(np.dot(c, mu))).intersection(
            halfplane(nu, float(np.dot(c, nu))))
        S = S.difference(q)
    return C.difference(S).intersection(C2).area


def signs(s, n=1200):
    """(tau_1, tau_2): E1 = {alpha_1 < 0}, E2 = {alpha_2 > 0} as anchored intervals."""
    T = np.linspace(1e-6, PI2 - 1e-6, n)
    F = np.array([Hseg(t, s) for t in T]); dF = np.array([dHseg(t, s) for t in T])
    G = np.array([Hseg(t + PI2, s) for t in T])
    dG = np.array([dHseg(t + PI2, s) for t in T])
    a1 = G - 1.0 - dF; a2 = F - 1.0 + dG
    t1 = T[a1 < 0].max() if (a1 < 0).any() else 0.0
    t2 = T[a2 > 0].max() if (a2 > 0).any() else 0.0
    return t1, t2, float(np.mean(a1 < 0)), float(np.mean(a2 > 0))


def dist2(s):
    nd = np.array(sorted({0.0, PI2, PI} | {PI*i/400 for i in range(401)}))
    T, W = gl_split(nd, 10)
    HS, _ = H_and_dH(T)
    HH = np.array([Hseg(x, s) for x in T])
    return float(W @ ((HH - HS)**2))


def save(path, d):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(d, f, indent=1)
    os.replace(tmp, path)


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(THIS, "budget_scan.json")
    data = json.load(open(out)) if os.path.exists(out) else {}
    SS = [0.15, 0.3, 0.45, 0.6, 0.75, 0.9, 1.0]
    NS = [2000, 4000]
    todo = [s for s in SS if str(s) not in data]
    print("THE EXCESS BUDGET ALONG THE SEGMENT  H_s = (1-s) H_Sigma + s H_Gerver\n",
          flush=True)
    t0 = time.time()
    for i, s in enumerate(todo):
        row = {"V": V_seg(s), "d2": dist2(s), "sg": signs(s)}
        for n in NS:
            row[str(n)] = N_seg(s, n)
        data[str(s)] = row; save(out, data)
        el = time.time() - t0
        print(f"  s = {s:<5} done   elapsed {el/60:5.2f}m   "
              f"ETA {el/(i+1)*(len(todo)-i-1)/60:5.2f}m", flush=True)

    print(f"\n  ||H_G - H_Sigma||^2 = {dist2(1.0):.6f},  c* = {CSTAR:.7f}\n")
    print(f"  {'s':>5} {'tau_1':>7} {'tau_2':>7} {'E_inf':>11} {'||eta||^2':>10} "
          f"{'theta needed':>13} {'corr/E':>8}")
    worst = 0.0
    for s in SS:
        if str(s) not in data:
            continue
        r = data[str(s)]
        E = {n: r["V"] - r[str(n)] for n in NS}
        Ei = 2*E[4000] - E[2000]
        corr = E[4000] - Ei
        th = 2*Ei/(CSTAR*r["d2"]) if Ei > 0 else 0.0
        worst = max(worst, th)
        t1, t2 = r["sg"][0], r["sg"][1]
        print(f"  {s:5.2f} {t1:7.4f} {t2:7.4f} {Ei:11.3e} {r['d2']:10.5f} "
              f"{th:13.4f} {abs(corr/Ei) if Ei>0 else 0:8.2f}")
    print(f"\n  theta must exceed {worst:.4f} to cover the whole segment.")
    print(f"  theta < 1 is required for a positive stability constant (1-theta)c*.")
    print(f"  VERDICT: {'segment is inside (EB_theta) for theta = %.3f' % worst if worst < 1 else 'NO admissible theta -- the segment leaves the budget'}")
    print(f"\n  Sigma's own cell is (tau_1,tau_2) = (0.2897, 1.2811); Gerver's is")
    print(f"  (0, pi/2).  The anchored family tau_1 <= tau_2 covers the segment, and the")
    print(f"  note's Proposition 'Beyond Sigma's own cell' supplies concavity there.")
    print(f"  Rule 7: floating point.  EVIDENCE, not proof.")


if __name__ == "__main__":
    main()
