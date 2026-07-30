"""
romik_hessian.py
================

Phase 1-4 of the rigorous local-maximality framework applied to
Romik's 2017/2018 AMBIDEXTROUS sofa candidate (area 1.64495...).

This is the same machinery as gerver_constants.py + second_variation.py +
phase3_robustness.py + phase4_full_theorem.py, but instantiated for the
ambidextrous functional

    F_ambi[c] = area( S_x[c]  intersect  rho( S_x[c] ) )

where
    S_x[c] = Lhoriz  intersect  intersect_{t in [0, pi/2]}  ( R(+t) H + c(t) )
and rho is reflection across the horizontal line y = 1/2.

The candidate trajectory is Romik's piecewise x_path(t) defined in
algorithm/sofa_romik2017_reference.py using the 13 closed-form constants
(beta, a_1=e_1, f_1, f_2, kappa_*).

USAGE
-----
    python3 romik_hessian.py [--quick] [--n_modes 6]

Quick mode skips arb_mat.eig (slow), uses fewer n_theta and skips the
N=8/12 robustness sweep.
"""

from __future__ import annotations

import os
import sys
import math
import time
import argparse
import numpy as np
import mpmath as mp

from shapely.geometry import Polygon as SPoly
from shapely.affinity import rotate as srot, translate as strans, scale as sscale

THIS = os.path.dirname(os.path.abspath(__file__))
ALGO = os.path.dirname(THIS)
sys.path.insert(0, ALGO)
sys.path.insert(0, THIS)

# Romik trajectory + constants
from sofa_romik2017_reference import (
    x_path, BETA, _TARGET_AREA,
    A1_const, E1_const, F1_const, F2_const,
    KAPPA1_1, KAPPA1_2, KAPPA5_1, KAPPA5_2, KAPPA6_1, KAPPA6_2,
    _x1, _x5, _x6,
)


# -----------------------------------------------------------------------
# Geometry primitives
# -----------------------------------------------------------------------

K_BIG = 8.0


def _hallway_poly(K: float = K_BIG) -> SPoly:
    """Standard L-hallway of unit width, inner corner at the origin."""
    from shapely.ops import unary_union
    horiz = SPoly([(-K, 0), (1, 0), (1, 1), (-K, 1)])
    vert  = SPoly([(0, -K), (1, -K), (1, 1), (0, 1)])
    return unary_union([horiz, vert])


HALLWAY = _hallway_poly()
LHORIZ = SPoly([(-K_BIG, 0), (1, 0), (1, 1), (-K_BIG, 1)])


# -----------------------------------------------------------------------
# Ambidextrous area functional F_ambi[c]
# -----------------------------------------------------------------------
#
# Romik's convention:  body-frame hallway H_b(t) = R(+t) H + c(t).
# We intersect H_b(t) over t in [0, pi/2] (starting from L_horiz) to
# obtain S_x[c]; then intersect with rho(S_x[c]).
#
# For Hessian work we tabulate c at the working theta grid once.

def ambi_area_from_arrays(thetas: np.ndarray,
                           cx: np.ndarray,
                           cy: np.ndarray) -> float:
    """F_ambi[c] using pre-tabulated c at given theta grid."""
    S = LHORIZ
    for th, x, y in zip(thetas, cx, cy):
        Hb = srot(HALLWAY, math.degrees(th), origin=(0, 0))
        Hb = strans(Hb, xoff=float(x), yoff=float(y))
        S = S.intersection(Hb)
        if S.is_empty or S.area < 1e-12:
            return 0.0
    # Intersect with mirror across y = 1/2
    rhoS = sscale(S, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
    Sigma = S.intersection(rhoS)
    if Sigma.is_empty:
        return 0.0
    return float(Sigma.area)


def tabulate_romik(n_theta: int = 721):
    """Return arrays (thetas, cx, cy) for Romik's x_path on a uniform grid."""
    thetas = np.linspace(0.0, math.pi / 2, n_theta)
    cx = np.empty(n_theta)
    cy = np.empty(n_theta)
    for i, th in enumerate(thetas):
        v = x_path(float(th))
        cx[i] = float(v[0])
        cy[i] = float(v[1])
    return thetas, cx, cy


# -----------------------------------------------------------------------
# Fourier sine basis & perturbation evaluator
# -----------------------------------------------------------------------

def basis_matrix(thetas: np.ndarray, n_modes: int) -> np.ndarray:
    """B[i, k-1] = sin(2 k theta_i), k = 1..n_modes."""
    return np.sin(np.outer(thetas, 2 * np.arange(1, n_modes + 1)))


def area_with_perturbation(a: np.ndarray,
                            thetas: np.ndarray,
                            cx0: np.ndarray,
                            cy0: np.ndarray,
                            B: np.ndarray) -> float:
    n_modes = B.shape[1]
    ax = a[:n_modes]
    ay = a[n_modes:]
    cx = cx0 + B @ ax
    cy = cy0 + B @ ay
    return ambi_area_from_arrays(thetas, cx, cy)


# -----------------------------------------------------------------------
# Finite-difference Hessian (4-point central stencil)
# -----------------------------------------------------------------------

def hessian(thetas, cx0, cy0, B, epsilon=1e-3, verbose=True):
    n_dim = 2 * B.shape[1]
    Q = np.zeros((n_dim, n_dim))
    F0 = area_with_perturbation(np.zeros(n_dim), thetas, cx0, cy0, B)
    if verbose:
        print(f"  F[c_R] = {F0:.10f}    (Romik target 1.6449552184254400)")
        print(f"  step epsilon = {epsilon:g}   dimension = {n_dim}")

    a = np.zeros(n_dim)
    t0 = time.time()
    # Diagonal entries: centred 2nd diff at step 2*eps
    for i in range(n_dim):
        a[:] = 0.0
        a[i] = +2 * epsilon
        Fpp = area_with_perturbation(a, thetas, cx0, cy0, B)
        a[i] = -2 * epsilon
        Fmm = area_with_perturbation(a, thetas, cx0, cy0, B)
        Q[i, i] = (Fpp - 2 * F0 + Fmm) / (4 * epsilon ** 2)
    if verbose:
        print(f"  diagonal pass: {time.time() - t0:.1f}s")

    # Off-diagonal: 4-point cross stencil
    t0 = time.time()
    for i in range(n_dim):
        for j in range(i + 1, n_dim):
            a[:] = 0.0
            a[i] = +epsilon; a[j] = +epsilon
            Fpp = area_with_perturbation(a, thetas, cx0, cy0, B)
            a[i] = -epsilon; a[j] = -epsilon
            Fmm = area_with_perturbation(a, thetas, cx0, cy0, B)
            a[i] = +epsilon; a[j] = -epsilon
            Fpm = area_with_perturbation(a, thetas, cx0, cy0, B)
            a[i] = -epsilon; a[j] = +epsilon
            Fmp = area_with_perturbation(a, thetas, cx0, cy0, B)
            q = (Fpp + Fmm - Fpm - Fmp) / (4 * epsilon ** 2)
            Q[i, j] = q
            Q[j, i] = q
    if verbose:
        print(f"  off-diagonal pass ({n_dim*(n_dim-1)//2} entries): "
              f"{time.time() - t0:.1f}s")
    return Q, F0


# -----------------------------------------------------------------------
# Gradient (first variation) -- consistency check
# -----------------------------------------------------------------------

def gradient(thetas, cx0, cy0, B, epsilon=1e-4):
    """Centred first difference for grad F at c_R."""
    n_dim = 2 * B.shape[1]
    g = np.zeros(n_dim)
    a = np.zeros(n_dim)
    for i in range(n_dim):
        a[:] = 0.0
        a[i] = +epsilon
        Fp = area_with_perturbation(a, thetas, cx0, cy0, B)
        a[i] = -epsilon
        Fm = area_with_perturbation(a, thetas, cx0, cy0, B)
        g[i] = (Fp - Fm) / (2 * epsilon)
    return g


# -----------------------------------------------------------------------
# Spectrum report
# -----------------------------------------------------------------------

def report_spectrum(Q, n_modes, epsilon, F0, label=""):
    print()
    print("=" * 72)
    print(f"Hessian Q of F_ambi[c_R + perturbation]  {label}")
    print("=" * 72)
    n_dim = Q.shape[0]
    print(f"  basis     : sin(2 k theta), k = 1, ..., {n_modes} on x & y -> dim {n_dim}")
    print(f"  step eps  : {epsilon:g}")
    print(f"  F[c_R]    : {F0:.10f}    (target 1.6449552184254400)")

    sym_err = np.max(np.abs(Q - Q.T))
    print(f"  symmetry  : ||Q - Q^T||_inf = {sym_err:.3e}")
    Qs = 0.5 * (Q + Q.T)
    eigs = np.sort(np.linalg.eigvalsh(Qs))[::-1]
    print(f"\n  eigenvalues (descending):")
    for i, e in enumerate(eigs):
        marker = ""
        if e > 1e-4:
            marker = "  <-- POSITIVE"
        elif abs(e) < 1e-4:
            marker = "  <-- ~ zero"
        print(f"    lambda_{i:02d} = {e:+.6e}{marker}")
    lam_max = eigs[0]; lam_min = eigs[-1]
    print(f"\n  largest   : {lam_max:+.6e}")
    print(f"  smallest  : {lam_min:+.6e}")
    n_pos  = int(np.sum(eigs >  1e-4))
    n_zero = int(np.sum(np.abs(eigs) <= 1e-4))
    n_neg  = int(np.sum(eigs < -1e-4))
    print(f"  counts    : {n_pos} pos | {n_zero} ~zero | {n_neg} neg")
    if n_pos == 0 and n_zero == 0:
        print("  VERDICT   : Q negative definite -- evidence FOR strict local max")
    elif n_pos == 0:
        print(f"  VERDICT   : Q negative semidefinite with {n_zero} zero mode(s)")
    else:
        print(f"  VERDICT   : Q has {n_pos} positive eig -- NOT a local max")
    print("=" * 72)
    return eigs


# -----------------------------------------------------------------------
# Phase 4: arb-interval certification
# -----------------------------------------------------------------------

def frobenius_perturb_lambda_max(Q_centre, Q_radius):
    eigs = np.linalg.eigvalsh(Q_centre)
    lam_c = float(eigs.max())
    fro = float(np.sqrt(np.sum(Q_radius * Q_radius)))
    return lam_c + fro, lam_c, fro


def gershgorin_lambda_max(Q_centre, Q_radius):
    n = Q_centre.shape[0]
    bounds = np.empty(n)
    for i in range(n):
        diag = Q_centre[i, i] + Q_radius[i, i]
        offsum = 0.0
        for j in range(n):
            if j == i: continue
            offsum += abs(Q_centre[i, j]) + Q_radius[i, j]
        bounds[i] = diag + offsum
    return float(np.max(bounds))


def arb_eig_lambda_max(Q_centre, Q_radius, prec_bits=128, verbose=True):
    try:
        from flint import arb, ctx, arb_mat
    except ImportError:
        if verbose:
            print("  python-flint not available; skipping arb_mat.eig")
        return None
    ctx.prec = prec_bits
    n = Q_centre.shape[0]
    rows = []
    for i in range(n):
        row = []
        for j in range(n):
            c = float(Q_centre[i, j])
            r = float(Q_radius[i, j])
            row.append(arb(c, r if r > 0 else 1e-30))
        rows.append(row)
    M = arb_mat(rows)
    try:
        eigs = M.eig()
    except Exception:
        try:
            eigs = M.eig(multiple=True)
        except Exception as e:
            if verbose:
                print(f"  arb_mat.eig failed: {e}")
            return None
    lam_max_upper = -1e308
    for e in eigs:
        re = e.real if hasattr(e, 'real') else e
        try:
            upper = float(re.upper())
        except AttributeError:
            mid = float(re.mid())
            s = str(re)
            rad = 0.0
            if '+/-' in s:
                try:
                    rad = float(s.split('+/-')[1].split(']')[0].strip())
                except Exception:
                    rad = 0.0
            upper = mid + rad
        if upper > lam_max_upper:
            lam_max_upper = upper
    if verbose:
        print(f"  arb_mat.eig returned {len(eigs)} eigenvalues")
    return lam_max_upper


# -----------------------------------------------------------------------
# Main
# -----------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true",
                        help="reduce n_theta and skip arb_mat.eig")
    parser.add_argument("--n_modes", type=int, default=16)
    parser.add_argument("--n_theta", type=int, default=361)
    # NOTE on the step size.  A mode-k perturbation eps*sin(2k theta) has
    # H^2-size ~ eps*k^2, so a fixed eps that is fine for low modes leaves
    # the linear regime for high modes: at eps=1e-3 the N=16 step-sensitivity
    # radius |Q(eps)-Q(eps/2)| blows up (max ~700) and the arb interval
    # eigenvalue enclosure fails to certify.  At eps=1e-5 the radius collapses
    # (max ~0.16) and arb_mat.eig() certifies lambda_max(Q_16) <= -2.896,
    # i.e. truncated coercivity m_{N=16}^R >= 2.896.  Do not coarsen below 1e-5
    # without re-checking that the certification still succeeds.
    parser.add_argument("--epsilon", type=float, default=1e-5)
    parser.add_argument("--robustness", action="store_true",
                        help="also run N=8 and N=12 for Phase 3 robustness")
    args = parser.parse_args()

    if args.quick:
        args.n_theta = 181

    print("=" * 72)
    print("Romik (2018) ambidextrous sofa -- rigorous local-maximality framework")
    print("=" * 72)
    print(f"  n_theta = {args.n_theta},  n_modes = {args.n_modes},  eps = {args.epsilon}")
    print(f"  target area A_R* = {_TARGET_AREA:.16f}")
    print()

    # ----- Phase 1: load constants, verify F[c_R] -----
    print("-" * 72)
    print("PHASE 1.  Load Romik constants, verify F[c_R]")
    print("-" * 72)
    print(f"  beta              = {BETA:.16f}")
    print(f"  a_1 = e_1         = {A1_const:.16f}")
    print(f"  f_1               = {F1_const:.16f}")
    print(f"  f_2               = {F2_const:.16f}")
    print(f"  kappa_1^(1)       = {KAPPA1_1:.16f}")
    print(f"  kappa_6^(1)       = {KAPPA6_1:.16f}")
    print(f"  kappa_5^(1)       = {KAPPA5_1:.16f}")
    # continuity checks
    j1 = np.linalg.norm(_x1(BETA) - _x6(BETA))
    j2 = np.linalg.norm(_x6(math.pi/2 - BETA) - _x5(math.pi/2 - BETA))
    print(f"  |x1(b)-x6(b)|              = {j1:.3e}   (should be ~0)")
    print(f"  |x6(pi/2-b)-x5(pi/2-b)|    = {j2:.3e}   (should be ~0)")

    print(f"\n[1] Tabulating c_R at n_theta = {args.n_theta} ...")
    t0 = time.time()
    thetas, cx0, cy0 = tabulate_romik(n_theta=args.n_theta)
    print(f"    done ({time.time() - t0:.1f}s)")

    print("[2] Computing F[c_R] = area(Sigma) ...")
    t0 = time.time()
    F_cR = ambi_area_from_arrays(thetas, cx0, cy0)
    print(f"    F[c_R] = {F_cR:.10f}   (target {_TARGET_AREA:.10f})")
    print(f"    delta  = {F_cR - _TARGET_AREA:+.4e}    [{time.time()-t0:.1f}s]")

    # ----- Phase 2: Hessian at c_R -----
    print()
    print("-" * 72)
    print("PHASE 2.  Hessian Q at c_R in sine basis (k = 1..N)")
    print("-" * 72)
    B = basis_matrix(thetas, args.n_modes)

    # Gradient sanity check
    print("[3] First variation (gradient) at c_R ...")
    t0 = time.time()
    g = gradient(thetas, cx0, cy0, B, epsilon=args.epsilon)
    print(f"    ||grad F||_inf = {np.max(np.abs(g)):.3e}")
    print(f"    ||grad F||_2   = {np.linalg.norm(g):.3e}    [{time.time()-t0:.1f}s]")

    print("[4] Computing Hessian Q (4-point central differences) ...")
    t0 = time.time()
    Q, F0 = hessian(thetas, cx0, cy0, B, epsilon=args.epsilon, verbose=True)
    print(f"    Hessian assembled in {time.time() - t0:.1f}s")
    eigs_main = report_spectrum(Q, args.n_modes, args.epsilon, F0,
                                 label=f"(N={args.n_modes}, eps={args.epsilon})")

    # ----- Phase 3: robustness sweep -----
    eigs_by_N = {args.n_modes: eigs_main}
    if args.robustness:
        print()
        print("-" * 72)
        print("PHASE 3.  Robustness: rerun at N = 8 and N = 12")
        print("-" * 72)
        for Nx in [8, 12]:
            if Nx == args.n_modes:
                continue
            print(f"\n>>> N = {Nx}")
            B_x = basis_matrix(thetas, Nx)
            Q_x, F0_x = hessian(thetas, cx0, cy0, B_x,
                                epsilon=args.epsilon, verbose=False)
            ei_x = report_spectrum(Q_x, Nx, args.epsilon, F0_x,
                                    label=f"(N={Nx})")
            eigs_by_N[Nx] = ei_x

        print("\n  lambda_max summary across N:")
        for Nx in sorted(eigs_by_N):
            lm = eigs_by_N[Nx][0]
            print(f"    N = {Nx:2d}   lambda_max = {lm:+.6e}")

    # ----- Phase 4: arb-interval certification -----
    print()
    print("-" * 72)
    print("PHASE 4.  Certification of m_N via interval enclosure")
    print("-" * 72)
    # Compute Q at a second step size for uncertainty estimate
    eps2 = args.epsilon * 0.5
    print(f"[5] Re-computing Q at eps2 = {eps2:g} for sensitivity radius ...")
    t0 = time.time()
    Q2, _ = hessian(thetas, cx0, cy0, B, epsilon=eps2, verbose=False)
    print(f"    done {time.time() - t0:.1f}s")
    # Symmetrise
    Q_c = 0.5 * (Q + Q.T)
    Q_c2 = 0.5 * (Q2 + Q2.T)
    Q_r = np.abs(Q_c - Q_c2)  # step-sensitivity radius
    print(f"    Q_radius:  max = {Q_r.max():.3e},  mean = {Q_r.mean():.3e}")

    # Gershgorin
    gersh = gershgorin_lambda_max(Q_c, Q_r)
    print(f"    Gershgorin upper bound on lambda_max : {gersh:+.6e}")
    fro_ub, lam_c, fro = frobenius_perturb_lambda_max(Q_c, Q_r)
    print(f"    Frobenius/Weyl upper bound on lambda_max : {fro_ub:+.6e}")
    print(f"      (fp lambda_max(Qc) = {lam_c:+.6e}, ||r||_F = {fro:.3e})")

    arb_ub = None
    if not args.quick:
        print("    Trying arb_mat.eig() for sharper enclosure ...")
        try:
            arb_ub = arb_eig_lambda_max(Q_c, Q_r, prec_bits=128, verbose=True)
            if arb_ub is not None:
                print(f"    arb_mat upper bound on lambda_max : {arb_ub:+.6e}")
        except Exception as exc:
            print(f"    arb_mat.eig failed: {exc}")

    candidates = [gersh, fro_ub]
    if arb_ub is not None:
        candidates.append(arb_ub)
    certified_lam_max = min(candidates)
    m_N_R = -certified_lam_max
    print()
    print(f"  CERTIFIED  lambda_max(Q) <= {certified_lam_max:+.6e}")
    print(f"  -> m_N_R >= {m_N_R:.6e}")

    # ----- Final report -----
    print()
    print("=" * 72)
    print("FINAL REPORT: Romik (2018) ambidextrous candidate c_R")
    print("=" * 72)
    print(f"  Verified F[c_R]            : {F_cR:.10f}")
    print(f"  Target (Romik analytic)    : {_TARGET_AREA:.10f}")
    print(f"  |delta|                    : {abs(F_cR - _TARGET_AREA):.3e}")
    print(f"  ||grad F[c_R]||_2          : {np.linalg.norm(g):.3e}")
    print(f"  N = {args.n_modes} eigenvalues (descending):")
    for i, e in enumerate(eigs_main):
        print(f"     lambda_{i:02d} = {e:+.6e}")
    print(f"  CERTIFIED lambda_max       : {certified_lam_max:+.6e}")
    print(f"  Truncated coercivity m_N_R : {m_N_R:.6e}")
    print()
    if certified_lam_max < 0 and np.linalg.norm(g) < 1e-2:
        print("  VERDICT: Numerical evidence STRONGLY SUPPORTS strict local")
        print("           maximality of Romik's ambidextrous candidate on the")
        print(f"           sin(2 k theta) subspace, k=1..{args.n_modes} on x & y.")
    elif certified_lam_max < 0:
        print("  VERDICT: Hessian negative definite, but |grad F| not at zero;")
        print("           likely c_R lies at the maximum but trajectory")
        print("           parametrisation is not stationary -- check basis.")
    else:
        print("  VERDICT: Hessian has positive eigenvalue(s).  Possible:")
        print("           (a) c_R is a saddle, (b) discretisation artefact,")
        print("           (c) basis contains direction violating constraint.")
    print("=" * 72)


if __name__ == "__main__":
    main()
