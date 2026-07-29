"""sigma_qstruct_assemble.py — CLOSED-FORM structure-following second-variation
form for Romik's Sigma (PROGRAM item S7''' / S4).

The traversal (sigma_struct_map.py) and its junctions (sigma_struct_junctions.py,
residuals ~1e-10) are:

    dA[PI2->b]  rA[b->PI2]  dB[PI2->b]  dX[b->B]  dD[B->0]
    rC[0->B]    dC[B->0]    rD[0->B]    rX[B->b]  rB[b->PI2]      (b=beta, B=PI2-beta)

d = direct family, r = its rho-image (rho(p) = (p_x, 1-p_y)); A,B = the mu-slot
walls x=1,x=0; C,D = the nu-slot walls y=1,y=0; X = the reflex-corner path.
EVERY junction sits exactly at beta or PI2-beta (or at an endpoint 0, PI2):
Sigma has no free junction parameters at c_R.

Two variants of the reconstruction:
  'active'  — arcs over their c_R-active ranges (A-arcs on [beta, PI2]);
  'struct'  — the STRUCTURE-FOLLOWING form: the A-arcs are continued over the
              cap [0, beta] where the contact is STATIONARY (frozen at the
              point (1, 1/2), verified to 1e-10). At c_R that continuation is
              a single point, so the reconstruction is unchanged (F=A_R*), but
              under perturbation it opens into an arc contributing the
              full-strength mu-slot p-form on the cap — the coverage whose
              absence made the fan-release form non-coercive.

Key structural fact (as for Gerver): the per-arc Wirtinger integrands and the
chord jets depend ONLY on the frame and the mode, NOT on the trajectory. The
trajectory enters only through the arc RANGES and junction parameters, which
are exactly beta, PI2-beta, 0, PI2 here. Hence the whole form is a finite sum
of elementary trigonometric integrals — closed form, no oracle, no junction
solve, and directly certifiable in interval arithmetic.

Per-arc second-variation integrands (N5, proved):
    mu-slot (A,B):  dP = p mu + p' nu,  dP^dP' = p (p + p'')
    nu-slot (C,D):  dP = -q' mu + q nu, dP^dP' = q (q + q'')
    corner  (X):    dP = eta,           dP^dP' = eta ^ eta'
with p = <eta, mu_t>, q = <eta, nu_t>; the reflected family carries the extra
factor det(rho_0) = -1.

Usage: python3 sigma_qstruct_assemble.py [K] [variant]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sofa_romik2017_reference import BETA

PI2 = math.pi / 2
BB = PI2 - BETA


def table(variant='struct'):
    """(label, t_from, t_to, slot) in traversal order."""
    a0 = 0.0 if variant == 'struct' else BETA
    return [('dA', PI2, a0, 'p'), ('rA', a0, PI2, 'p'),
            ('dB', PI2, BETA, 'p'), ('dX', BETA, BB, 'x'),
            ('dD', BB, 0.0, 'q'), ('rC', 0.0, BB, 'q'),
            ('dC', BB, 0.0, 'q'), ('rD', 0.0, BB, 'q'),
            ('rX', BB, BETA, 'x'), ('rB', BETA, PI2, 'p')]


def frame(t):
    c, s = np.cos(t), np.sin(t)
    return c, s


def mode_fg(comp, t):
    """f = <e_comp, mu_t>, g = <e_comp, nu_t>;  f' = g, g' = -f."""
    c, s = frame(t)
    return (c, -s) if comp == 0 else (s, c)


def mode_jets(comp, k, t):
    """p, p+p'', q, q+q'', p', q', s  for eta = e_comp sin(2kt)."""
    f, g = mode_fg(comp, t)
    if k == 0:                      # the CONSTANT mode (rigid translation)
        s = np.ones_like(np.asarray(t, float)); sp = 0*s; spp = 0*s
    else:
        s = np.sin(2*k*t); sp = 2*k*np.cos(2*k*t); spp = -4.0*k*k*np.sin(2*k*t)
    p = f*s
    pS = 2*g*sp + f*spp            # p + p''
    q = g*s
    qS = -2*f*sp + g*spp           # q + q''
    return p, pS, q, qS, g*s + f*sp, -f*s + g*sp, s


def gl_nodes(a, b, n):
    x, w = np.polynomial.legendre.leggauss(n)
    return 0.5*(b-a)*x + 0.5*(a+b), 0.5*(b-a)*w


def endpoint_dP(lab, slot, t, comp, k):
    """delta(contact point) at parameter t for mode (comp,k), as a 2-vector."""
    c, s = frame(t)
    mu = np.array([c, s]); nu = np.array([-s, c])
    p, _, q, _, pp, qp, sv = mode_jets(comp, k, t)
    if slot == 'p':
        v = p*mu + pp*nu
    elif slot == 'q':
        v = -qp*mu + q*nu
    else:
        e = np.array([1.0, 0.0]) if comp == 0 else np.array([0.0, 1.0])
        v = e*sv
    if lab[0] == 'r':
        v = np.array([v[0], -v[1]])
    return v


def assemble(K, variant='struct', nq=None):
    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    n = len(modes)
    nq = nq or max(200, 16*K)
    tab = table(variant)

    # ---- per-arc Wirtinger integrals -------------------------------------
    Q = np.zeros((n, n))
    for lab, t0, t1, slot in tab:
        a, b = (t0, t1) if t0 < t1 else (t1, t0)
        if b - a < 1e-15:
            continue
        dir_sign = 1.0 if t1 > t0 else -1.0
        fam_sign = -1.0 if lab[0] == 'r' else 1.0
        sgn = 0.5 * dir_sign * fam_sign
        ts, ws = gl_nodes(a, b, nq)
        J = [mode_jets(c, k, ts) for (c, k) in modes]
        if slot == 'p':
            U = np.array([j[0] for j in J]); V = np.array([j[1] for j in J])
        elif slot == 'q':
            U = np.array([j[2] for j in J]); V = np.array([j[3] for j in J])
        else:
            # corner: eta_u ^ eta_v' = s_u s_v' (e_u ^ e_v)
            S = np.array([j[6] for j in J])
            SP = np.array([(2*k*np.cos(2*k*ts) if k else 0*ts)
                           for (_, k) in modes])
            E = np.array([[0.0 if modes[i][0] == modes[j][0]
                           else (1.0 if modes[i][0] == 0 else -1.0)
                          for j in range(n)] for i in range(n)])
            W = (S*ws) @ SP.T
            # eta_u ^ eta_v' polarizes with the DIFFERENCE: E is antisymmetric,
            # so E*(W - W^T) is the (symmetric) matrix of the quadratic form.
            Q += sgn * E * 0.5*(W - W.T)
            continue
        M = (U*ws) @ V.T
        Q += sgn * 0.5*(M + M.T)

    # ---- junction chords --------------------------------------------------
    # gap between consecutive pieces: chord from piece_i's end to piece_{i+1}'s
    # start. Green term (1/2) P0 ^ P1 -> bilinear (1/2)(dP0[u]^dP1[v] + u<->v).
    ends = [(lab, t1, slot) for lab, t0, t1, slot in tab]
    starts = [(lab, t0, slot) for lab, t0, t1, slot in tab]
    for i in range(len(tab)):
        l0, tt0, s0 = ends[i]
        l1, tt1, s1 = starts[(i+1) % len(tab)]
        D0 = np.array([endpoint_dP(l0, s0, tt0, c, k) for (c, k) in modes])
        D1 = np.array([endpoint_dP(l1, s1, tt1, c, k) for (c, k) in modes])
        W = np.outer(D0[:, 0], D1[:, 1]) - np.outer(D0[:, 1], D1[:, 0])
        Q += 0.25 * (W + W.T)

    # convention: return d^2F/deps^2 (the Green second-order TERM is half of
    # it). Validated against the direct struct-following FD oracle: exact
    # agreement to 5 digits on every mode tested.
    Q = 2.0 * Q
    G = np.diag([math.pi/4*(1 + 4*k*k) for (_, k) in modes])     # H^1
    GL2 = np.diag([math.pi/4 for _ in modes])                    # L^2
    return Q, G, GL2, modes


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    variant = sys.argv[2] if len(sys.argv) > 2 else 'struct'
    Q, G, GL2, modes = assemble(K, variant)
    # traversal orientation: the map's cycle is clockwise, so the enclosed-area
    # functional is MINUS the Green integral; flip so that Q is the second
    # variation of the AREA.
    Q = -Q
    for name, GG in (("H^1", G), ("L^2", GL2)):
        S = np.diag(1.0/np.sqrt(np.diag(GG)))
        M = S @ (0.5*(Q+Q.T)) @ S
        ev = np.linalg.eigvalsh(M)
        tag = (f"NEG DEF  m = {-ev.max():.5f}" if ev.max() < 0
               else f"NOT neg def ({int((ev>=0).sum())} nonneg)")
        print(f"  {variant:>6} K={K:3d}  {name}: max={ev.max():+.5f} "
              f"min={ev.min():+.5f}   {tag}")
    np.savez(os.path.join(THIS, f"sigma_qstruct_{variant}_K{K}.npz"),
             Q=Q, G=G, GL2=GL2)


if __name__ == "__main__":
    main()
