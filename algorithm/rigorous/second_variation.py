"""
second_variation.py
===================

Phase 2 of the rigorous local-maximality of Gerver project.

GOAL
----
Numerically construct the Hessian operator

    Q[k,l] = d^2 / (de_k de_l)  F[c_G + e_k phi_k + e_l phi_l]  at  e = 0

of the moving-sofa area functional

    F[c] = area( intersection_{t in [0, pi/2]}  ( R(t) H + c(t) ) )

evaluated at Gerver's analytic trajectory c_G (whose pieces are the
certified solutions of Phase 1, gerver_constants.py).  Here R(t) is
counter-clockwise rotation by angle t and H is the standard L-hallway
of width 1 with its inner corner at the origin.

The implementation uses Shapely to compute F[c] as the area of a
polygon intersection over a fine theta grid (n_theta = 721 here).
Finite-difference stencils evaluate the bilinear form
delta^2 F[c_G](phi_k, phi_l) for a truncated Fourier basis of
perturbations.

BASIS
-----
We use sine modes that vanish at both endpoints of [0, pi/2]:

    phi_k(theta) = sin( 2 k theta ),   k = 1, ..., N_modes

applied independently to the x- and y-components of c.  This gives
a 2 * N_modes - dimensional perturbation space which is a clean
subspace of the full admissible perturbation space H^2 (it omits
the global-translation rigid-motion mode by construction, so the
rigid-motion zero eigenvalues of the full Hessian do NOT appear
here -- their absence is the consistency check, not a problem).

VERDICT FRAMEWORK
-----------------
For c_G to be a strict local maximum (restricted to this subspace),
Q must be NEGATIVE DEFINITE.  We report:

  - eigenvalues of Q to 6 digits
  - largest eigenvalue (most positive)
  - smallest eigenvalue (most negative)
  - condition / spectral gap
  - verdict

This is honest numerical evidence, not a proof.  Discretization
bias (Shapely's piecewise-linear intersection at n_theta samples)
limits absolute accuracy to ~1e-3 in F, but it largely cancels in
finite differences (the *change* in bias under smooth perturbation
is much smaller than the bias itself).  We probe sensitivity to
the step size epsilon and report the converged spectrum.

Run:
    python3 second_variation.py
"""

from __future__ import annotations

import math
import time
from typing import Callable, Tuple

import numpy as np
import mpmath as mp
from shapely.geometry import Polygon as SPoly
from shapely.affinity import rotate as srot, translate as strans
from shapely.ops import unary_union

from gerver_constants import solve_gerver_constants, _xt_xtp


# ---------------------------------------------------------------------
#  Geometry primitives
# ---------------------------------------------------------------------

K_BIG = 8.0


def _hallway_poly(K: float = K_BIG) -> SPoly:
    """Standard L-hallway of width 1, inner corner at origin.

    H = ([-K, 1] x [0, 1])  union  ([0, 1] x [-K, 1]).
    """
    horiz = SPoly([(-K, 0), (1, 0), (1, 1), (-K, 1)])
    vert  = SPoly([(0, -K), (1, -K), (1, 1), (0, 1)])
    return unary_union([horiz, vert])


HALLWAY = _hallway_poly()


def sofa_area(c_x: Callable[[float], float],
              c_y: Callable[[float], float],
              n_theta: int = 721) -> float:
    """F[c] = area( intersection over theta of  R(theta) H + c(theta) ).

    Body-frame convention used here:
        H(theta) = R(+theta) * H_world  +  c(theta).
    This is the convention that recovers Gerver's area 2.21953 from
    his analytic trajectory.
    """
    thetas = np.linspace(0.0, math.pi / 2, n_theta)
    S = None
    for th in thetas:
        Hb = srot(HALLWAY, math.degrees(th), origin=(0, 0))
        Hb = strans(Hb, xoff=c_x(th), yoff=c_y(th))
        S = Hb if S is None else S.intersection(Hb)
        if S.is_empty:
            return 0.0
    return S.area


# ---------------------------------------------------------------------
#  Gerver's analytic trajectory  c_G  (interpolated for speed)
# ---------------------------------------------------------------------
#
# Direct mpmath evaluation of _xt_xtp on every (theta, perturbation)
# tuple is too slow for ~10^4 area evaluations.  Instead we tabulate
# c_G at the working theta grid once at high precision and cache
# float64 arrays of (cx, cy) values that the area routine reads.
#

def tabulate_gerver(n_theta: int = 721, dps: int = 30):
    """Return arrays (thetas, cx, cy) for c_G evaluated at the grid."""
    p, _ = solve_gerver_constants(working_dps=dps, verbose=False)
    thetas = np.linspace(0.0, math.pi / 2, n_theta)
    cx = np.empty(n_theta)
    cy = np.empty(n_theta)
    for i, th in enumerate(thetas):
        x, _ = _xt_xtp(mp.mpf(th), p)
        cx[i] = float(x[0])
        cy[i] = float(x[1])
    return thetas, cx, cy


def sofa_area_from_arrays(thetas: np.ndarray,
                          cx: np.ndarray,
                          cy: np.ndarray) -> float:
    """Area of the body-frame intersection using pre-tabulated c values
    at the *same* theta grid used inside.
    """
    S = None
    for th, x, y in zip(thetas, cx, cy):
        Hb = srot(HALLWAY, math.degrees(th), origin=(0, 0))
        Hb = strans(Hb, xoff=float(x), yoff=float(y))
        S = Hb if S is None else S.intersection(Hb)
        if S.is_empty:
            return 0.0
    return S.area


# ---------------------------------------------------------------------
#  Fourier sine basis  phi_k(theta) = sin(2 k theta)
# ---------------------------------------------------------------------

def basis_matrix(thetas: np.ndarray, n_modes: int) -> np.ndarray:
    """Return B of shape (n_theta, n_modes) where B[i, k-1] = sin(2 k theta_i)."""
    return np.sin(np.outer(thetas, 2 * np.arange(1, n_modes + 1)))


# ---------------------------------------------------------------------
#  Perturbation -> area
# ---------------------------------------------------------------------
#
# A perturbation lives in R^{2 * n_modes}:
#     coefficients a = (ax_1, ..., ax_N, ay_1, ..., ay_N).
# Then  eta(theta) = ( sum a_k^x phi_k(theta),  sum a_k^y phi_k(theta) ).
# We evaluate  F[c_G + eta]  given the basis matrix B = [phi_k(theta_i)].
#

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
    return sofa_area_from_arrays(thetas, cx, cy)


# ---------------------------------------------------------------------
#  Finite-difference Hessian
# ---------------------------------------------------------------------

def hessian(thetas: np.ndarray,
            cx0: np.ndarray,
            cy0: np.ndarray,
            B: np.ndarray,
            epsilon: float = 1e-4,
            verbose: bool = True) -> np.ndarray:
    """Compute the Hessian Q of F[c_G + sum a_k phi_k] in the basis at a=0.

    Uses the standard 4-point cross stencil:
      Q[i,j] = ( F(+e_i + e_j) - F(+e_i - e_j) - F(-e_i + e_j) + F(-e_i - e_j) )
               / (4 epsilon^2)
    where e_k = epsilon * unit_k.  For diagonal entries (i = j) this
    reduces to the 3-point second difference:
      Q[i,i] = ( F(+2e_i) - 2 F(0) + F(-2e_i) ) / (4 epsilon^2)
             = ( F(+epsilon u_i) - 2 F(0) + F(-epsilon u_i) ) / epsilon^2
             after rescaling -- we use the 4-point formula uniformly,
             which for i = j returns
                 ( F(2 epsilon) - F(0) - F(0) + F(-2 epsilon) ) / (4 eps^2)
             = ( F(2eps) + F(-2eps) - 2 F(0) ) / (4 eps^2).
             This is the standard centred second-derivative formula
             with step 2 epsilon.
    """
    n_dim = 2 * B.shape[1]
    Q = np.zeros((n_dim, n_dim))
    F0 = area_with_perturbation(np.zeros(n_dim), thetas, cx0, cy0, B)
    if verbose:
        print(f"  F[c_G] = {F0:.10f}    (Gerver constant 2.2195317)")
        print(f"  step epsilon = {epsilon:g}  ; dimension = {n_dim}")

    # Cache one-sided evaluations  F(+/- eps * e_i)
    F_plus = np.empty(n_dim)
    F_minus = np.empty(n_dim)
    a = np.zeros(n_dim)
    t0 = time.time()
    for i in range(n_dim):
        a[:] = 0.0
        a[i] = +epsilon
        F_plus[i] = area_with_perturbation(a, thetas, cx0, cy0, B)
        a[i] = -epsilon
        F_minus[i] = area_with_perturbation(a, thetas, cx0, cy0, B)
    if verbose:
        print(f"  on-axis F+- pass: {time.time() - t0:.1f}s")

    # Diagonal entries (centred second difference at step 2 eps -> match
    # 4-point formula with i = j):
    for i in range(n_dim):
        a[:] = 0.0
        a[i] = +2 * epsilon
        Fpp = area_with_perturbation(a, thetas, cx0, cy0, B)
        a[i] = -2 * epsilon
        Fmm = area_with_perturbation(a, thetas, cx0, cy0, B)
        Q[i, i] = (Fpp - 2 * F0 + Fmm) / (4 * epsilon ** 2)

    # Off-diagonal entries: use the standard
    #   Q[i,j] = ( F(eps e_i + eps e_j) + F(-eps e_i - eps e_j)
    #           - F(eps e_i - eps e_j) - F(-eps e_i + eps e_j) ) / (4 eps^2)
    # Equivalent to the cross-stencil; numerically stable.
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
        print(f"  off-diagonal pass: {time.time() - t0:.1f}s")
    return Q, F0


# ---------------------------------------------------------------------
#  Report
# ---------------------------------------------------------------------

def report_spectrum(Q: np.ndarray,
                    n_modes: int,
                    epsilon: float,
                    F0: float) -> None:
    print()
    print("=" * 72)
    print("Hessian Q of F[c_G + perturbation]  (truncated Fourier sine basis)")
    print("=" * 72)
    n_dim = Q.shape[0]
    print(f"  basis     : sin(2 k theta), k = 1, ..., {n_modes}, on x & y -> dim {n_dim}")
    print(f"  step eps  : {epsilon:g}")
    print(f"  F[c_G]    : {F0:.10f}    (Gerver 2.21953166887...)")
    print()

    sym_err = np.max(np.abs(Q - Q.T))
    print(f"  symmetry  : ||Q - Q^T||_inf = {sym_err:.3e}")
    # symmetrise
    Qs = 0.5 * (Q + Q.T)

    eigs = np.linalg.eigvalsh(Qs)
    eigs = np.sort(eigs)[::-1]  # descending
    print()
    print(f"  eigenvalues (descending):")
    for i, e in enumerate(eigs):
        marker = ""
        if e > 1e-4:
            marker = "  <-- POSITIVE (instability direction)"
        elif abs(e) < 1e-4:
            marker = "  <-- ~ zero"
        print(f"    lambda_{i:02d} = {e:+.6e}{marker}")

    lam_max = eigs[0]
    lam_min = eigs[-1]
    print()
    print(f"  largest   : {lam_max:+.6e}")
    print(f"  smallest  : {lam_min:+.6e}")
    print(f"  range     : {lam_max - lam_min:.6e}")

    # Pos/near-zero counts (heuristic threshold 1e-4 absolute)
    eps_zero = 1e-4
    n_pos  = int(np.sum(eigs >  eps_zero))
    n_zero = int(np.sum(np.abs(eigs) <= eps_zero))
    n_neg  = int(np.sum(eigs < -eps_zero))
    print(f"  counts    : {n_pos} pos | {n_zero} ~zero | {n_neg} neg "
          f"(threshold {eps_zero:g})")

    print()
    print("-" * 72)
    if n_pos == 0 and n_zero == 0:
        verdict = ("Q is NEGATIVE DEFINITE on the sine-basis subspace.\n"
                   "Numerical evidence FOR strict local maximality of c_G\n"
                   "(in this subspace; rigid-motion zero modes are excluded\n"
                   "by construction, so 0 zero modes is the expected count).")
    elif n_pos == 0 and n_zero > 0:
        verdict = (f"Q is negative SEMIdefinite with {n_zero} zero mode(s).\n"
                   "Consistent with local maximality plus residual symmetry\n"
                   "directions; need to identify the zero eigenvector(s).")
    else:
        verdict = (f"Q has {n_pos} POSITIVE eigenvalue(s).  This is numerical\n"
                   "evidence that c_G is NOT a local maximum on this\n"
                   "subspace.  Possible explanations: (i) Gerver is\n"
                   "actually a saddle, (ii) discretization or step-size\n"
                   "artefact (try larger n_theta, different epsilon), or\n"
                   "(iii) the basis does not respect a contact constraint.")
    print("VERDICT:")
    for line in verdict.splitlines():
        print(f"  {line}")
    print("=" * 72)


# ---------------------------------------------------------------------
#  Main
# ---------------------------------------------------------------------

def main():
    print("Phase 2: Hessian of the moving-sofa area functional at c = c_G.")
    print()

    n_theta = 721
    n_modes = 6
    epsilon = 1e-4

    print(f"[1] Tabulating c_G at n_theta = {n_theta} ...")
    t0 = time.time()
    thetas, cx0, cy0 = tabulate_gerver(n_theta=n_theta, dps=30)
    print(f"    done ({time.time() - t0:.1f}s)")

    print(f"[2] Building sine basis with {n_modes} modes per component ...")
    B = basis_matrix(thetas, n_modes)
    print(f"    basis matrix shape = {B.shape}")

    # Calibration: area at c_G
    A0 = sofa_area_from_arrays(thetas, cx0, cy0)
    print(f"    F[c_G] at this grid = {A0:.7f}  (Gerver 2.2195317)")
    print(f"    discretisation bias  = {A0 - 2.21953166887:+.4e}")

    print(f"[3] Computing Hessian via 4-point central differences ...")
    t0 = time.time()
    Q, F0 = hessian(thetas, cx0, cy0, B, epsilon=epsilon, verbose=True)
    print(f"    Hessian assembled in {time.time() - t0:.1f}s")

    report_spectrum(Q, n_modes, epsilon, F0)

    # Optional: epsilon-sensitivity (one extra step size to confirm)
    print()
    print(">>> Re-running with epsilon = 5e-5 to check step-size sensitivity")
    Q2, F0b = hessian(thetas, cx0, cy0, B, epsilon=5e-5, verbose=False)
    eigs2 = np.sort(np.linalg.eigvalsh(0.5 * (Q2 + Q2.T)))[::-1]
    print("    eigenvalues at eps=5e-5:")
    for i, e in enumerate(eigs2):
        print(f"      lambda_{i:02d} = {e:+.6e}")


if __name__ == "__main__":
    main()
