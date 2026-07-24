"""Assemble the FROZEN FORM Q_frz directly from the proved per-arc identities.

No area oracle, no junction solve, no finite differences: Q_frz is exactly
quadratic, and its bilinear form is a sum of explicit 1D integrals (per-arc
Wirtinger forms) plus finite chord-jet terms:

  arcs A,B:  dP = p mu + p' nu,  dP' = (p+p'') nu   ->  wedge = p_u (p_v+p_v'')
  arcs C,D:  dP = -q' mu + q nu, dP' = -(q+q'') mu  ->  wedge = q_u (q_v+q_v'')
  corner x:  dP = eta                                ->  wedge = u ^ v'
  chords:    d2(1/2 P0^P1) -> (1/2)(dP0[u]^dP1[v] + dP0[v]^dP1[u])

with p = <eta,mu_t>, q = <eta,nu_t>.  Orientations as in gerver_area:
A, C, D, B with +, corner path with -, chords +.

Basis: eta = e_comp * sin(2kt), comp in {x,y}, k = 1..K  (H^2-gauged sine
family; the two t-linear modes are flagged for later augmentation).

(F1): H^1-generalized eigenvalues of the K-block.
(F2): cross-block k<=K<l<=L entries + Hilbert-Schmidt tail bound.
"""
from __future__ import annotations
import sys, os
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gerver_constants import solve_gerver_constants, _xt_full

DPS = 25


def mode_pq(comp, k):
    """Return callables p(t), p'(t), p''(t), q, q', q'' for eta = e sin(2kt)."""
    k = mp.mpf(k)
    if comp == "x":
        f, fp, fpp = mp.cos, lambda t: -mp.sin(t), lambda t: -mp.cos(t)     # <e,mu>
        g, gp, gpp = (lambda t: -mp.sin(t)), (lambda t: -mp.cos(t)), mp.sin  # <e,nu>
    else:
        f, fp, fpp = mp.sin, mp.cos, lambda t: -mp.sin(t)
        g, gp, gpp = mp.cos, (lambda t: -mp.sin(t)), (lambda t: -mp.cos(t))
    s = lambda t: mp.sin(2*k*t)
    sp = lambda t: 2*k*mp.cos(2*k*t)
    spp = lambda t: -4*k*k*mp.sin(2*k*t)
    def P(t):  return f(t)*s(t)
    def Pp(t): return fp(t)*s(t) + f(t)*sp(t)
    def Ppp(t): return fpp(t)*s(t) + 2*fp(t)*sp(t) + f(t)*spp(t)
    def Q(t):  return g(t)*s(t)
    def Qp(t): return gp(t)*s(t) + g(t)*sp(t)
    def Qpp(t): return gpp(t)*s(t) + 2*gp(t)*sp(t) + g(t)*spp(t)
    return P, Pp, Ppp, Q, Qp, Qpp


def eta_of(comp, k):
    k = mp.mpf(k)
    if comp == "x":
        return (lambda t: (mp.sin(2*k*t), mp.mpf(0)),
                lambda t: (2*k*mp.cos(2*k*t), mp.mpf(0)))
    return (lambda t: (mp.mpf(0), mp.sin(2*k*t)),
            lambda t: (mp.mpf(0), 2*k*mp.cos(2*k*t)))


def assemble(K, L=None, verbose=True):
    p, _ = solve_gerver_constants(working_dps=DPS, verbose=False)
    mp.mp.dps = DPS
    PHI = p['phi']; TR = p['theta']; PI2 = mp.pi/2
    kinks = [PHI, TR, PI2-TR, PI2-PHI]

    modes = [(c, k) for c in ("x", "y") for k in range(1, K+1)]
    if L:
        tails = [(c, l) for c in ("x", "y") for l in range(K+1, L+1)]
    jets = {m: mode_pq(*m) for m in modes + (tails if L else [])}
    etas = {m: eta_of(*m) for m in modes + (tails if L else [])}

    def nds(lo, hi):
        return [lo] + [x for x in kinks if lo < x < hi] + [hi]

    ARCS = [("A", mp.mpf(0), PI2, +1, "p"), ("C", mp.mpf(0), PI2, +1, "q"),
            ("D", mp.mpf(0), TR, +1, "q"), ("B", PI2-TR, PI2, +1, "p"),
            ("x", PHI, PI2-PHI, -1, "eta")]

    def bil(u, v):
        Pu, Ppu, Pppu, Qu, Qpu, Qppu = jets[u]
        Pv, Ppv, Pppv, Qv, Qpv, Qppv = jets[v]
        eu, epu = etas[u]; ev, epv = etas[v]
        tot = mp.mpf(0)
        for name, lo, hi, sgn, kind in ARCS:
            if kind == "p":
                f = lambda t: mp.mpf('0.5')*(Pu(t)*(Pv(t)+Pppv(t))
                                             + Pv(t)*(Pu(t)+Pppu(t)))
            elif kind == "q":
                f = lambda t: mp.mpf('0.5')*(Qu(t)*(Qv(t)+Qppv(t))
                                             + Qv(t)*(Qu(t)+Qppu(t)))
            else:
                def f(t):
                    a = eu(t); bp = epv(t); b = ev(t); ap = epu(t)
                    return mp.mpf('0.5')*((a[0]*bp[1]-a[1]*bp[0])
                                          + (b[0]*ap[1]-b[1]*ap[0]))
            tot += sgn * mp.quad(f, nds(lo, hi))

        # chord-jet terms.  delta-endpoint formulas in the moving frame:
        #   dA(t) = p mu + p' nu ;  dB = same ;  dC = dD = -q' mu + q nu ;
        #   dx = eta.
        def dpt(m, t, which):
            Pm, Ppm, _, Qm, Qpm, _ = jets[m]
            c, s = mp.cos(t), mp.sin(t)
            mu = (c, s); nu = (-s, c)
            if which in ("A", "B"):
                a, b = Pm(t), Ppm(t)
                return (a*mu[0]+b*nu[0], a*mu[1]+b*nu[1])
            if which in ("C", "D"):
                a, b = -Qpm(t), Qm(t)
                return (a*mu[0]+b*nu[0], a*mu[1]+b*nu[1])
            return etas[m][0](t)
        # Wall-anchored closure: the three outer segments are FIXED wall lines
        # (for the sine basis eta vanishes at t=0,pi/2, so the endpoint walls
        # do not move); each outer bridge chord has one fixed endpoint, so its
        # bilinear term vanishes identically.  Only the two junction-gap
        # chords (both endpoints varied) contribute.
        CHORDS = [(("D", TR), ("x", PI2-PHI)),
                  (("x", PHI), ("B", PI2-TR))]
        for (w0, t0), (w1, t1) in CHORDS:
            a0u = dpt(u, t0, w0); a1v = dpt(v, t1, w1)
            a0v = dpt(v, t0, w0); a1u = dpt(u, t1, w1)
            tot += mp.mpf('0.5')*((a0u[0]*a1v[1]-a0u[1]*a1v[0])
                                  + (a0v[0]*a1u[1]-a0v[1]*a1u[0]))
        return tot

    import numpy as np
    n = len(modes)
    Q = np.zeros((n, n))
    for i in range(n):
        for j in range(i, n):
            Q[i, j] = Q[j, i] = float(bil(modes[i], modes[j]))
        if verbose:
            print(f"  block row {i+1}/{n}", flush=True)
    # H1 Gram (diagonal in this basis)
    import math
    G = np.diag([math.pi/4*(1+4*k*k) for (_, k) in modes])
    return Q, G, modes, (bil if L else None), (tails if L else None)


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    import numpy as np
    Q, G, modes, _, _ = assemble(K)
    S = np.diag(1/np.sqrt(np.diag(G)))
    M = S @ Q @ S
    ev = np.linalg.eigvalsh(M)
    print("\n(F1)  frozen-form low-frequency block, H1-normalized:")
    print(f"  K={K}  eigenvalues: max={ev.max():+.5f}  min={ev.min():+.5f}")
    if ev.max() < 0:
        print(f"  => NEGATIVE DEFINITE with m_1 = {-ev.max():.5f}")
    else:
        print(f"  => NOT negative definite ({(ev>=0).sum()} nonneg)")
    np.savez(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          f"qfrz_block_K{K}.npz"), Q=Q, G=G)
    print(f"  saved qfrz_block_K{K}.npz")


if __name__ == "__main__":
    main()
