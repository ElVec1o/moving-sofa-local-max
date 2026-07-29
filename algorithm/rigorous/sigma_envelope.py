"""sigma_envelope.py — the ENVELOPE IDENTITY (N3) applied to Sigma (PROGRAM S7'''-b).

The frozen structure-following form Q_frz (sigma_qstruct_assemble.py) loses its
cap coercivity at large K because, with junctions FROZEN, the junction chords
contribute O(k^2) terms — the same defect Gerver's frozen form shows at K=32
while its junction-solved form stays at m ~ 0.78.

Fix (proved, N3): let the junction parameters respond affinely, b(eps) = b0 +
eps*beta. Every such reconstruction is superset-valid, so its second-order
coefficient Q_beta bounds the true second variation from above for EVERY beta,
and the envelope over beta is attained at the implicit-function response:

    Q_true(eta) = min_beta Q_beta(eta)
                = eta^T ( Q_frz - C^T H_bb^{-1} C ) eta      (Schur complement)

with the joint Hessian of the reconstruction area

    [ Q_frz   C^T ]        Q_frz = d2 G / d eps^2  |_{beta=0}
    [ C      H_bb ]        C     = d2 G / d beta d eps ,  H_bb = d2 G/d beta^2.

Sigma has 5 interior junctions (at beta and pi/2-beta), each shared by two
arcs => 10 free junction parameters (the arc ends at t=0 and t=pi/2 are
anchored by the problem, not free). Consistency check built in: dG/d beta = 0
at the base point — the zero-chord derivative identity that makes the envelope
work at all.

Usage: python3 sigma_envelope.py [K] [h_eps] [h_delta]
"""
from __future__ import annotations
import os, sys, math, time
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sigma_struct_map import cjet
import sigma_qstruct_assemble as A

PI2 = A.PI2
BETA = A.BETA
BB = A.BB
TAB = A.table('struct')          # 10 pieces, traversal order

# free junction slots: (piece index, which end) for every arc end at an
# INTERIOR junction (beta or pi/2-beta). Ends at 0 / pi/2 are anchored.
FREE = []
for i, (lab, t0, t1, slot) in enumerate(TAB):
    for which, tv in (('t0', t0), ('t1', t1)):
        if abs(tv - BETA) < 1e-12 or abs(tv - BB) < 1e-12:
            FREE.append((i, which))
NJ = len(FREE)


def arc_point(lab, slot, t, amps, modes):
    """Contact point of arc `lab` at parameter t for trajectory c_R + sum a_u eta_u."""
    t = min(max(float(t), 0.0), PI2)
    c, cp = cjet(t)
    c = c.copy(); cp = cp.copy()
    for a, (comp, k) in zip(amps, modes):
        if a == 0.0:
            continue
        s = math.sin(2*k*t); sp = 2*k*math.cos(2*k*t)
        c[comp] += a*s
        cp[comp] += a*sp
    ct, st = math.cos(t), math.sin(t)
    mu = np.array([ct, st]); nu = np.array([-st, ct])
    dmu = float(cp @ mu); dnu = float(cp @ nu)
    kind = lab[1]
    if kind == 'A':
        P = c + dmu*nu + mu
    elif kind == 'B':
        P = c + dmu*nu
    elif kind == 'C':
        P = c - dnu*mu + nu
    elif kind == 'D':
        P = c - dnu*mu
    else:
        P = c
    return np.array([P[0], 1.0 - P[1]]) if lab[0] == 'r' else P


def area_rec(amps, delta, modes, n=1400):
    """Reconstruction area with trajectory amplitudes `amps` and junction
    shifts `delta` (one per FREE slot)."""
    shifts = {}
    for d, (pi_, which) in zip(delta, FREE):
        shifts[(pi_, which)] = d
    tot = 0.0
    ends = []
    for i, (lab, t0, t1, slot) in enumerate(TAB):
        a0 = t0 + shifts.get((i, 't0'), 0.0)
        a1 = t1 + shifts.get((i, 't1'), 0.0)
        lo, hi = (a0, a1) if a0 < a1 else (a1, a0)
        if hi - lo < 1e-14:
            P = arc_point(lab, slot, a0, amps, modes)
            ends.append((P, P)); continue
        ts = np.linspace(lo, hi, n)
        P = np.array([arc_point(lab, slot, float(t), amps, modes) for t in ts])
        if a1 < a0:
            P = P[::-1]
        tot += 0.5*np.sum(P[:-1, 0]*P[1:, 1] - P[1:, 0]*P[:-1, 1])
        ends.append((P[0], P[-1]))
    for i in range(len(ends)):
        e = ends[i][1]; s0 = ends[(i+1) % len(ends)][0]
        tot += 0.5*(e[0]*s0[1] - s0[0]*e[1])
    return -tot          # CW traversal -> area = -Green


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    he = float(sys.argv[2]) if len(sys.argv) > 2 else 2e-5
    hd = float(sys.argv[3]) if len(sys.argv) > 3 else 2e-4
    n = int(sys.argv[4]) if len(sys.argv) > 4 else 1400
    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    nm = len(modes)
    z = np.zeros(nm); zd = np.zeros(NJ)

    print(f"Sigma envelope identity: K={K}, {nm} modes, {NJ} free junctions "
          f"({[ (TAB[i][0], w) for i, w in FREE ]})", flush=True)
    t0 = time.time()
    F0 = area_rec(z, zd, modes, n)
    dt = time.time() - t0
    print(f"F_rec(c_R) = {F0:.9f}   (A_R* = 1.644955218)   "
          f"[{dt:.2f}s/call]", flush=True)

    # --- consistency: the zero-chord derivative identity dG/d beta = 0 ------
    g1 = []
    for j in range(NJ):
        d = zd.copy(); d[j] = hd
        fp = area_rec(z, d, modes, n)
        d[j] = -hd
        fm = area_rec(z, d, modes, n)
        g1.append((fp - fm)/(2*hd))
    print(f"  max |dG/dbeta| at base = {max(abs(np.array(g1))):.3e}   "
          f"(envelope identity requires 0)", flush=True)

    ck = os.path.join(THIS, f"sigma_env_K{K}.npz")
    # --- H_bb --------------------------------------------------------------
    Hbb = np.zeros((NJ, NJ))
    for j in range(NJ):
        d = zd.copy(); d[j] = hd; fp = area_rec(z, d, modes, n)
        d[j] = -hd; fm = area_rec(z, d, modes, n)
        Hbb[j, j] = (fp - 2*F0 + fm)/hd**2
    for j in range(NJ):
        for l in range(j+1, NJ):
            d = zd.copy(); d[j] = hd; d[l] = hd; pp = area_rec(z, d, modes, n)
            d[j] = -hd; d[l] = -hd; mm = area_rec(z, d, modes, n)
            d[j] = hd; d[l] = -hd; pm = area_rec(z, d, modes, n)
            d[j] = -hd; d[l] = hd; mp = area_rec(z, d, modes, n)
            Hbb[j, l] = Hbb[l, j] = (pp + mm - pm - mp)/(4*hd**2)
        print(f"  H_bb row {j+1}/{NJ}  [{(time.time()-t0)/60:.1f}m]", flush=True)

    # --- C (coupling) ------------------------------------------------------
    C = np.zeros((NJ, nm))
    for j in range(NJ):
        for u in range(nm):
            d = zd.copy(); a = z.copy()
            d[j] = hd; a[u] = he; pp = area_rec(a, d, modes, n)
            d[j] = -hd; a[u] = -he; mm = area_rec(a, d, modes, n)
            d[j] = hd; a[u] = -he; pm = area_rec(a, d, modes, n)
            d[j] = -hd; a[u] = he; mp = area_rec(a, d, modes, n)
            C[j, u] = (pp + mm - pm - mp)/(4*hd*he)
        np.savez(ck, Hbb=Hbb, C=C)
        print(f"  C row {j+1}/{NJ}  [{(time.time()-t0)/60:.1f}m]", flush=True)

    # --- Schur complement --------------------------------------------------
    Qfrz = A.assemble(K, 'struct')[0]
    Qfrz = -0.5*(Qfrz + Qfrz.T)     # assemble returns the Green side; area = -Green

    w, V = np.linalg.eigh(Hbb)
    keep = w > 1e-8*max(1.0, abs(w).max())
    Hinv = (V[:, keep] / w[keep]) @ V[:, keep].T
    Qtrue = Qfrz - C.T @ Hinv @ C
    Qtrue = 0.5*(Qtrue + Qtrue.T)

    print(f"\n  H_bb eigenvalues: min={w.min():+.4e} max={w.max():+.4e}  "
          f"rank kept {int(keep.sum())}/{NJ}")
    GL2 = np.diag([math.pi/4 for _ in modes])
    G1 = np.diag([math.pi/4*(1+4*k*k) for (_, k) in modes])
    for name, GG, Qx in (("frozen H^1", G1, Qfrz), ("frozen L^2", GL2, Qfrz),
                         ("ENVELOPE H^1", G1, Qtrue), ("ENVELOPE L^2", GL2, Qtrue)):
        S = np.diag(1.0/np.sqrt(np.diag(GG)))
        ev = np.linalg.eigvalsh(S @ Qx @ S)
        tag = (f"NEG DEF m={-ev.max():.5f}" if ev.max() < 0
               else f"NOT neg def ({int((ev>=0).sum())} nonneg)")
        print(f"  {name:>14}: max={ev.max():+.6f} min={ev.min():+.4f}  {tag}")
    np.savez(ck, Hbb=Hbb, C=C, Qfrz=Qfrz, Qtrue=Qtrue)
    print(f"saved {os.path.basename(ck)}")


if __name__ == "__main__":
    main()
