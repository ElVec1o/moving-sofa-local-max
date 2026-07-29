"""sigma_onesided.py — (2) falsify, then (1) minimize: the ONE-SIDED condition.

Adversarial review found that M bounds the SYMMETRIC second difference, while
local maximality needs each one-sided branch:

    F(+-eps) - F0 = -(eps^2/2) [ -Q_rel + 2 N(+-phi) ] + O(eps^3).

Since -Q_rel is even and phi_{-eta} = -phi_eta, the minus branch at eta is the
plus branch at -eta, so minimising

    G(eta) := -Q_rel(eta) + 2 [ N1(phi_eta) + N2(psi_eta) ]

over the whole unit sphere covers BOTH branches at once.

STEP 2 (falsify): hunt for eta with G(eta) <= 0.  Uses the PROVED single-cut
lower bound for N (so a positive result is conservative and meaningful; a
negative result must then be re-checked against the exact bite before any
FALSE label is assigned).

STEP 1 (Lemma O): minimise -Q_rel restricted to the zero-bite cone
{d1 <= 0, d2 <= 0}, by penalty + projected gradient rather than random
sampling.

All linear algebra, no oracle calls.
Usage: python3 sigma_onesided.py [K] [restarts]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sofa_romik2017_reference import BETA

PI2 = math.pi/2
COTB = 1.0/math.tan(BETA)


def setup(K, m=400):
    Q = np.load(os.path.join(THIS, f"sigma_rel_K{K}.npy"))
    Q = 0.5*(Q + Q.T)
    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    n = len(modes)
    s = np.linspace(0.0, BETA, m)
    P1 = np.array([np.sin(2*k*s)*(np.cos(s) if c == 0 else np.sin(s))
                   for (c, k) in modes])
    t = PI2 - s
    P2 = np.array([np.sin(2*k*t)*(-np.sin(t) if c == 0 else np.cos(t))
                   for (c, k) in modes])
    # d = phi(beta) cos s / cos beta - phi   (linear in v):  D = R - P
    D1 = np.outer(P1[:, -1], np.cos(s))/math.cos(BETA) - P1
    D2 = np.outer(P2[:, -1], np.cos(s))/math.cos(BETA) - P2
    inner = (s > 1e-9) & (s < BETA - 1e-9)
    Gs = np.where(inner, math.sin(2*BETA) /
                  (2*np.sin(BETA - s)*np.sin(BETA + s) + 1e-300), 0.0)
    gl = math.pi/4
    return (-Q)/gl, D1, D2, Gs, inner, n, gl


def bite_lb(v, D, Gs, inner):
    """proved single-cut lower bound for N(phi_v), plus its argmax index"""
    d = v @ D
    val = np.where(inner, np.maximum(d, 0.0)**2*Gs, 0.0)
    i = int(val.argmax())
    return float(val[i]), i, d


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    nr = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    A, D1, D2, Gs, inner, n, gl = setup(K)
    rng = np.random.default_rng(20260729)

    def G(v):
        nv = v @ v
        r = float(v @ A @ v)/nv
        b1, i1, _ = bite_lb(v/math.sqrt(nv), D1, Gs, inner)
        b2, i2, _ = bite_lb(v/math.sqrt(nv), D2, Gs, inner)
        return r + 2*(b1 + b2), r, 2*(b1+b2), i1, i2

    def gradG(v):
        nv = v @ v
        u = v/math.sqrt(nv)
        r = float(u @ A @ u)
        g = 2*(A @ u - r*u)                      # sphere gradient of Rayleigh
        for D in (D1, D2):
            b, i, d = bite_lb(u, D, Gs, inner)
            if b > 0:
                col = D[:, i]
                gb = 2*2*max(d[i], 0.0)*Gs[i]*col
                g = g + (gb - float(gb @ u)*u)
        return g

    # ---------------- STEP 2: falsification ----------------
    best = None
    for t_ in range(nr):
        v = rng.standard_normal(n)
        if t_ < 40:                              # seed near the danger zone
            w, V = np.linalg.eigh(A)
            v = V[:, t_ % 8] + 0.3*rng.standard_normal(n)
        v = v/np.linalg.norm(v)
        step = 0.25
        for it in range(600):
            g = gradG(v)
            cand = v - step*g/ (np.linalg.norm(g) + 1e-15)
            cand = cand/np.linalg.norm(cand)
            if G(cand)[0] < G(v)[0]:
                v = cand
            else:
                step *= 0.7
                if step < 1e-9:
                    break
        val = G(v)
        if best is None or val[0] < best[0][0]:
            best = (val, v.copy())
    (gv, rv, bv, i1, i2), vb = best
    print(f"STEP 2 — falsification of the ONE-SIDED condition, K={K}")
    print(f"  min over the sphere of  G = -Q_rel + 2(N1+N2)_lowerbound")
    print(f"    G      = {gv:12.4f}")
    print(f"    -Q_rel = {rv:12.4f}   2*bite(lb) = {bv:10.4f}")
    print(f"  verdict: {'NO COUNTEREXAMPLE (G > 0)' if gv > 0 else '*** G <= 0: candidate counterexample ***'}")

    # ---------------- STEP 1: Lemma O on the zero-bite cone ----------------
    print(f"\nSTEP 1 — Lemma O: min -Q_rel on the zero-bite cone "
          f"{{d1<=0, d2<=0}}")
    C = np.concatenate([D1[:, inner], D2[:, inner]], axis=1)   # n x 2m'

    def pen(v, mu):
        u = v/np.linalg.norm(v)
        viol = np.maximum(u @ C, 0.0)
        return float(u @ A @ u) + mu*float(viol @ viol), float(u @ A @ u), \
            float(viol.max() if viol.size else 0.0)

    bestO = None
    for mu in (1e2, 1e4, 1e6, 1e8):
        for t_ in range(60):
            v = rng.standard_normal(n)
            v = v/np.linalg.norm(v)
            step = 0.3
            for it in range(800):
                u = v/np.linalg.norm(v)
                viol = np.maximum(u @ C, 0.0)
                g = 2*(A @ u) + 2*mu*(C @ viol)
                g = g - float(g @ u)*u
                cand = u - step*g/(np.linalg.norm(g) + 1e-15)
                cand = cand/np.linalg.norm(cand)
                if pen(cand, mu)[0] < pen(v, mu)[0]:
                    v = cand
                else:
                    step *= 0.7
                    if step < 1e-10:
                        break
            _, q, mx = pen(v, mu)
            if mx < 1e-9 and (bestO is None or q < bestO[0]):
                bestO = (q, mx)
    if bestO:
        print(f"    min -Q_rel on the cone = {bestO[0]:.4f}   "
              f"(max constraint violation {bestO[1]:.2e})")
        print(f"  Lemma O would need this > 0: "
              f"{'HOLDS numerically' if bestO[0] > 0 else '*** FAILS ***'}")
    else:
        print("    no feasible point found within tolerance")


if __name__ == "__main__":
    main()
