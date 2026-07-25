"""sigma_hessian_released.py — the FAN-RELEASE ladder for Sigma (S7'').

The cap degeneracy of Q_Sigma is a stationary WALL FAN: for t in the cap
interior, the outer mu-wall (first cap: ox; last cap: oy, by the x5 SOL1
form) passes through one frozen point P_A. Releasing those interior-fan
constraints (superset principle N1: fewer constraints => larger body =>
F_rel >= F pointwise) leaves the two EXTREME walls, which already cut the
same wedge at c_R — so F_rel(c_R) = F(c_R) exactly, while F_rel is C^2
near c_R (transversal corners respond smoothly; the fan kink is gone).

Therefore Q_rel >= Q in the one-sided sense along every ray, and

    Q_rel <= -m ||eta||_{L2}^2  (ladder, K-stable)   =>
    Sigma is a strict local maximum with L2 modulus m.

Implementation: the hallway polygon for cap-interior angles has the
released wall pushed out to K_BIG. First cap (0, beta): release ox
(outer vertical, x=1). Last cap (pi/2-beta, pi/2): release oy (outer
horizontal, y=1). Extreme angles {0, beta, pi/2-beta, pi/2} and the whole
middle phase keep the full hallway. The reflected family inherits the
release through rho(S_rel).

Checks: (1) F_rel(c_R) = F0 to grid precision; (2) central-difference
validity (the released functional is C^2) via two stencil sizes on a cap
direction; (3) the ladder in the pure L2 metric.

Usage: python3 sigma_hessian_released.py K [eps]
Checkpoints: sigma_rel_K{K}.npy
"""
from __future__ import annotations
import os, sys, math, time
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))

from shapely.geometry import Polygon as SPoly
from shapely.affinity import rotate as srot, translate as strans, scale as sscale
from shapely.ops import unary_union

from romik_hessian import tabulate_romik, LHORIZ, K_BIG
from sofa_romik2017_reference import BETA, _TARGET_AREA

trapz = np.trapezoid


def hallway(release: str | None) -> SPoly:
    """Full hallway, or with one outer wall released to K_BIG."""
    if release == 'ox':      # outer vertical wall x=1 -> x=K_BIG
        horiz = SPoly([(-K_BIG, 0), (1, 0), (1, 1), (-K_BIG, 1)])
        vert = SPoly([(0, -K_BIG), (K_BIG, -K_BIG), (K_BIG, 1), (0, 1)])
    elif release == 'oy':    # outer horizontal wall y=1 -> y=K_BIG
        horiz = SPoly([(-K_BIG, 0), (1, 0), (1, K_BIG), (-K_BIG, K_BIG)])
        vert = SPoly([(0, -K_BIG), (1, -K_BIG), (1, 1), (0, 1)])
    else:
        horiz = SPoly([(-K_BIG, 0), (1, 0), (1, 1), (-K_BIG, 1)])
        vert = SPoly([(0, -K_BIG), (1, -K_BIG), (1, 1), (0, 1)])
    return unary_union([horiz, vert])


H_FULL = hallway(None)
H_RELX = hallway('ox')
H_RELY = hallway('oy')
EDGE = 1e-9


def released_area(thetas, cx, cy) -> float:
    """F_rel: cap-interior angles use the released hallways."""
    S = LHORIZ
    pi2 = math.pi/2
    for th, x, y in zip(thetas, cx, cy):
        if EDGE < th < BETA - EDGE:
            H = H_RELX
        elif pi2 - BETA + EDGE < th < pi2 - EDGE:
            H = H_RELY
        else:
            H = H_FULL
        Hb = strans(srot(H, math.degrees(th), origin=(0, 0)),
                    xoff=float(x), yoff=float(y))
        S = S.intersection(Hb)
        if S.is_empty or S.area < 1e-12:
            return 0.0
    rhoS = sscale(S, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
    Sig = S.intersection(rhoS)
    return 0.0 if Sig.is_empty else float(Sig.area)


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    eps = float(sys.argv[2]) if len(sys.argv) > 2 else 1e-4
    n_theta = 1201
    th, cx, cy = tabulate_romik(n_theta)

    from romik_hessian import ambi_area_from_arrays
    F0_full = ambi_area_from_arrays(th, cx, cy)
    t0 = time.time()
    F0 = released_area(th, cx, cy)
    print(f"F0_full = {F0_full:.8f}   F0_rel = {F0:.8f}   "
          f"delta = {F0-F0_full:+.2e}   ({time.time()-t0:.1f}s)", flush=True)

    # C^2 sanity on a cap direction: two stencil sizes must agree
    g = np.where(th < BETA, np.sin(np.pi*np.clip(th/BETA, 0, 1))**2, 0.0)
    nrm = math.sqrt(trapz(g*g, th)); g /= nrm
    for e in (2e-4, 1e-4):
        Fp = released_area(th, cx + e*g, cy)
        Fm = released_area(th, cx - e*g, cy)
        print(f"  cap-dir stencil e={e:.0e}: Q = {(Fp-2*F0+Fm)/e**2:+.4f}  "
              f"fwd/bwd = {((Fp-F0)/e**2)/((Fm-F0)/e**2):.4f}", flush=True)

    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    n = len(modes)
    ck = os.path.join(THIS, f"sigma_rel_K{K}.npy")
    Q = np.load(ck) if os.path.exists(ck) else np.full((n, n), np.nan)
    basis = {m: np.sin(2*m[1]*th) for m in modes}

    def area(pert):
        cx2, cy2 = cx.copy(), cy.copy()
        for (c, k), a in pert:
            if c == 0:
                cx2 = cx2 + a*basis[(c, k)]
            else:
                cy2 = cy2 + a*basis[(c, k)]
        return released_area(th, cx2, cy2)

    t0 = time.time(); total = n*(n+1)//2
    done = int(np.isfinite(np.triu(Q)).sum())
    for i in range(n):
        if np.isfinite(Q[i, i:]).all():
            continue
        for j in range(i, n):
            if np.isfinite(Q[i, j]):
                continue
            if i == j:
                gp = area([(modes[i], eps)]) - F0
                gm = area([(modes[i], -eps)]) - F0
                Q[i, i] = (gp + gm)/eps**2
            else:
                gpp = area([(modes[i], eps), (modes[j], eps)]) - F0
                gmm = area([(modes[i], -eps), (modes[j], -eps)]) - F0
                gpm = area([(modes[i], eps), (modes[j], -eps)]) - F0
                gmp = area([(modes[i], -eps), (modes[j], eps)]) - F0
                Q[i, j] = (gpp + gmm - gpm - gmp)/(4*eps**2)
            Q[j, i] = Q[i, j]
            done += 1
        np.save(ck, Q)
        el = (time.time()-t0)/60
        print(f"row {i+1}/{n}  {100*done//total}%  elapsed {el:.1f}m", flush=True)

    Qs = 0.5*(Q + Q.T)
    # pure L2 metric
    G = np.zeros((n, n))
    for i, (ci, ki) in enumerate(modes):
        for j, (cj, kj) in enumerate(modes):
            if ci == cj:
                G[i, j] = trapz(np.sin(2*ki*th)*np.sin(2*kj*th), th)
    L = np.linalg.cholesky(G)
    Mi = np.linalg.inv(L)
    M = 0.5*((Mi@Qs@Mi.T) + (Mi@Qs@Mi.T).T)
    ev = np.linalg.eigvalsh(M)
    print(f"\nRELEASED ladder, Sigma, K={K}: L2-metric max={ev.max():+.5f} "
          f"min={ev.min():+.5f}")
    if ev.max() < 0:
        print(f"NEG DEF: m_rel_L2 = {-ev.max():.5f}  "
              f"=> Sigma strict local max modulus (pending certification)")
    else:
        print(f"NOT negative definite: {int((ev >= 0).sum())} nonneg")


if __name__ == "__main__":
    main()
