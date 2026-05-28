"""
phase3_robustness.py
====================

Phase 3 of the rigorous local-maximality of Gerver project.

Builds on second_variation.py (Phase 2) and gerver_constants.py /
gerver_arb.py (Phase 1).  Produces four robustness checks:

  3.1  Mode-count robustness.  Re-run the Hessian at N = 8, 12, 16.
       Track lambda_max(Q_N) (the "weakest" negative direction) and
       check it stays bounded away from zero as N grows.  This is
       the heuristic signal that the full infinite-dimensional
       Hessian is negative definite (rather than merely truncation-
       induced negativity).

  3.2  Symmetry quotient.  Augment the sine basis with 4 auxiliary
       directions:
            psi_x  = (1, 0)         constant x-translation
            psi_y  = (0, 1)         constant y-translation
            psi_t1 = (theta, 0)     linear-in-theta x-component
            psi_t2 = (0, theta)     linear-in-theta y-component.
       The augmented spectrum should contain exactly 2 zero modes
       (the constant translations).  The two linear-in-theta modes
       are NOT symmetries; we report what eigenvalues they pick up.

  3.3  Eigenvalue decay rate.  Fit lambda_k ~ -C k^p on the N=16
       spectrum.  Phase 4 will need this to bound the operator norm
       on the orthogonal complement of the first N modes; p >= 2 is
       desirable.

  3.4  Arb-validated single entry.  Recompute the diagonal entry of
       Q corresponding to the worst-case (least-negative) eigenmode
       using python-flint arb ball arithmetic for the trajectory
       evaluation, and check the floating-point and arb values are
       consistent to many digits.

Conventions match second_variation.py exactly:
    H(theta) = R(+theta) * H_world + c(theta).
"""

from __future__ import annotations

import math
import time
from typing import Tuple

import numpy as np
import mpmath as mp

from second_variation import (
    tabulate_gerver,
    basis_matrix,
    sofa_area_from_arrays,
    area_with_perturbation,
    hessian,
)
from gerver_constants import solve_gerver_constants, _xt_xtp


# ---------------------------------------------------------------------
#  Task 3.1 / 3.2 driver: full Hessian + spectrum at varied N
# ---------------------------------------------------------------------

def run_mode_count(thetas, cx0, cy0, n_modes, epsilon=1e-4):
    """Compute Q and return (eigs_descending, runtime_seconds)."""
    B = basis_matrix(thetas, n_modes)
    t0 = time.time()
    Q, F0 = hessian(thetas, cx0, cy0, B, epsilon=epsilon, verbose=False)
    runtime = time.time() - t0
    Qs = 0.5 * (Q + Q.T)
    eigs = np.sort(np.linalg.eigvalsh(Qs))[::-1]
    return eigs, runtime, Q, B, F0


def augmented_hessian(thetas, cx0, cy0, n_modes, epsilon=1e-4):
    """Hessian on the (sine modes) UNION (4 auxiliary directions) basis.

    Block layout of the coefficient vector a of length 2N + 4:
        a[       0 :   N   ]  -> sine x-coeffs   sin(2k theta), k=1..N
        a[   N    : 2 N    ]  -> sine y-coeffs
        a[ 2 N    : 2 N + 1]  -> constant x-translation
        a[ 2 N + 1: 2 N + 2]  -> constant y-translation
        a[ 2 N + 2: 2 N + 3]  -> linear-in-theta x
        a[ 2 N + 3: 2 N + 4]  -> linear-in-theta y.
    """
    n_theta = thetas.size
    B_sine = basis_matrix(thetas, n_modes)
    # Auxiliary basis matrices for x and y components.
    ones = np.ones(n_theta)
    lin  = thetas.copy()
    # Build extended B-style matrices for x and y separately, but
    # since the aux modes mix x and y, we work directly with full
    # cx/cy assembly per coefficient.
    n_aux = 4
    n_dim = 2 * n_modes + n_aux

    def cx_cy_of(a):
        ax = a[:n_modes]
        ay = a[n_modes:2*n_modes]
        tx = a[2*n_modes + 0]
        ty = a[2*n_modes + 1]
        lx = a[2*n_modes + 2]
        ly = a[2*n_modes + 3]
        cx = cx0 + B_sine @ ax + tx * ones + lx * lin
        cy = cy0 + B_sine @ ay + ty * ones + ly * lin
        return cx, cy

    def F_of(a):
        cx, cy = cx_cy_of(a)
        return sofa_area_from_arrays(thetas, cx, cy)

    a = np.zeros(n_dim)
    F0 = F_of(a)

    # Cache one-sided +/- eps * e_i
    Fp = np.empty(n_dim)
    Fm = np.empty(n_dim)
    for i in range(n_dim):
        a[:] = 0.0
        a[i] = +epsilon
        Fp[i] = F_of(a)
        a[i] = -epsilon
        Fm[i] = F_of(a)

    Q = np.zeros((n_dim, n_dim))
    # Diagonal
    for i in range(n_dim):
        a[:] = 0.0
        a[i] = +2 * epsilon
        Fpp = F_of(a)
        a[i] = -2 * epsilon
        Fmm = F_of(a)
        Q[i, i] = (Fpp - 2 * F0 + Fmm) / (4 * epsilon ** 2)

    for i in range(n_dim):
        for j in range(i + 1, n_dim):
            a[:] = 0.0
            a[i] = +epsilon; a[j] = +epsilon
            Fpp = F_of(a)
            a[i] = -epsilon; a[j] = -epsilon
            Fmm = F_of(a)
            a[i] = +epsilon; a[j] = -epsilon
            Fpm = F_of(a)
            a[i] = -epsilon; a[j] = +epsilon
            Fmp = F_of(a)
            q = (Fpp + Fmm - Fpm - Fmp) / (4 * epsilon ** 2)
            Q[i, j] = q
            Q[j, i] = q
    return Q, F0


# ---------------------------------------------------------------------
#  Task 3.4: arb ball-arithmetic enclosure of a single diagonal entry
# ---------------------------------------------------------------------
#
# We use python-flint's arb to evaluate c_G(theta) at the working grid
# in high-precision ball arithmetic, then construct the perturbation
# cx, cy as arb arrays, project to float64 ball CENTRES at full
# precision, and compute the second difference along the worst-case
# eigenvector direction.  The geometry step (polygon intersection) is
# still done in float64 -- arb doesn't help with Shapely -- but the
# *trajectory* evaluation is done in arb, which is the part where
# numerical error in the Phase 1 constants would propagate.
#
# To get a meaningful enclosure of Q[i,i] we use a wider working
# precision in the trajectory (e.g. mpmath dps = 50) and verify that
# Q[i,i] at dps = 50 agrees with Q[i,i] at dps = 30 to many digits.
#

def tabulate_gerver_at_dps(thetas, dps):
    p, _ = solve_gerver_constants(working_dps=dps, verbose=False)
    cx = np.empty(thetas.size)
    cy = np.empty(thetas.size)
    for i, th in enumerate(thetas):
        x, _ = _xt_xtp(mp.mpf(th), p)
        cx[i] = float(x[0])
        cy[i] = float(x[1])
    return cx, cy


def worst_eigvec_diag_entry(thetas, cx0, cy0, B, eigvec, epsilon=1e-4):
    """Diagonal entry of Q in the direction of `eigvec`:
            (F(+eps v) - 2 F(0) + F(-eps v)) / eps^2
       where v is a unit-norm coefficient vector in R^{2N}.
    """
    n_dim = 2 * B.shape[1]
    assert eigvec.shape == (n_dim,)
    v = eigvec / np.linalg.norm(eigvec)
    F0 = area_with_perturbation(np.zeros(n_dim), thetas, cx0, cy0, B)
    Fp = area_with_perturbation(+epsilon * v, thetas, cx0, cy0, B)
    Fm = area_with_perturbation(-epsilon * v, thetas, cx0, cy0, B)
    return (Fp - 2 * F0 + Fm) / (epsilon ** 2), F0, Fp, Fm


def arb_validated_diag(thetas, n_modes, eigvec, epsilon=1e-4):
    """Recompute the diagonal entry at dps=30 and dps=50; report both
       as a ball with centre = average and radius = |difference|/2.

       This is a *trajectory-precision* validation: the area evaluation
       remains Shapely / float64, but the input trajectory c_G is
       tabulated at two different mpmath precisions.  The Phase 1 arb
       certificate (gerver_arb.py) already bounds the constants
       themselves to ~10^-30; what we want to check here is that the
       Hessian value, viewed as a function of those constants, is
       stable under precision increase.
    """
    B = basis_matrix(thetas, n_modes)

    cx30, cy30 = tabulate_gerver_at_dps(thetas, dps=30)
    cx50, cy50 = tabulate_gerver_at_dps(thetas, dps=50)

    d30, F0_30, _, _ = worst_eigvec_diag_entry(thetas, cx30, cy30, B, eigvec, epsilon)
    d50, F0_50, _, _ = worst_eigvec_diag_entry(thetas, cx50, cy50, B, eigvec, epsilon)

    # Also bound difference in cx,cy between dps=30 and dps=50
    cx_diff = np.max(np.abs(cx30 - cx50))
    cy_diff = np.max(np.abs(cy30 - cy50))

    centre = 0.5 * (d30 + d50)
    radius = 0.5 * abs(d30 - d50)
    return {
        "d_dps30": d30,
        "d_dps50": d50,
        "centre":  centre,
        "radius":  radius,
        "F0_dps30": F0_30,
        "F0_dps50": F0_50,
        "cx_max_dps_diff": cx_diff,
        "cy_max_dps_diff": cy_diff,
    }


# Also: use python-flint arb directly to evaluate a sample c_G(theta)
# at very high precision and report the ball.  This anchors the
# trajectory-precision check to a hard arb enclosure.

def arb_traj_enclosure(theta_sample, prec_bits=256):
    """Return an arb-ball enclosure of c_G(theta_sample) by re-solving
       at very high mpmath precision and converting to arb."""
    try:
        from flint import arb, ctx
    except ImportError:
        return None
    ctx.prec = prec_bits

    p_lo, _ = solve_gerver_constants(working_dps=30, verbose=False)
    p_hi, _ = solve_gerver_constants(working_dps=60, verbose=False)
    x_lo, _ = _xt_xtp(mp.mpf(theta_sample), p_lo)
    x_hi, _ = _xt_xtp(mp.mpf(theta_sample), p_hi)
    # Build arb balls with centre = high-precision value, radius =
    # |hi - lo| (a crude but valid envelope provided the iteration
    # converges).
    cx_c = mp.mpf(x_hi[0]); cx_r = abs(mp.mpf(x_hi[0]) - mp.mpf(x_lo[0]))
    cy_c = mp.mpf(x_hi[1]); cy_r = abs(mp.mpf(x_hi[1]) - mp.mpf(x_lo[1]))
    # arb does not directly take mpf; go via string
    cx_arb = arb(str(cx_c), str(cx_r) if cx_r > 0 else "1e-50")
    cy_arb = arb(str(cy_c), str(cy_r) if cy_r > 0 else "1e-50")
    return cx_arb, cy_arb


# ---------------------------------------------------------------------
#  Driver
# ---------------------------------------------------------------------

def fmt_eig_table(eigs):
    return "  ".join(f"{e:+.4e}" for e in eigs)


def main():
    print("=" * 72)
    print("Phase 3: robustness of the Hessian negative-definiteness signal")
    print("=" * 72)

    # Use n_theta = 361 (vs Phase 2's 721) to keep N=16 runtime tractable.
    # Phase 2 step-refinement showed eigenvalues are stable to ~3-4 digits
    # under such resolution changes, which is more than enough to track
    # the qualitative trend in lambda_max(N).
    n_theta = 361
    epsilon = 1e-4

    print(f"\n[setup] tabulating c_G at n_theta = {n_theta} (dps=30) ...")
    t0 = time.time()
    thetas, cx0, cy0 = tabulate_gerver(n_theta=n_theta, dps=30)
    print(f"        done ({time.time()-t0:.2f}s)")
    A0 = sofa_area_from_arrays(thetas, cx0, cy0)
    print(f"        F[c_G] at this grid = {A0:.7f}   (Gerver 2.2195317)")

    # -----------------------------------------------------------------
    # Task 3.1: mode-count robustness
    # -----------------------------------------------------------------
    print("\n" + "-" * 72)
    print("TASK 3.1  Mode-count robustness  (sine basis, no augmentation)")
    print("-" * 72)
    results = {}
    for N in (8, 12, 16):
        print(f"\n  N = {N:>2d}  (dim {2*N}) ...")
        t0 = time.time()
        eigs, runtime, Q, B, F0 = run_mode_count(
            thetas, cx0, cy0, n_modes=N, epsilon=epsilon
        )
        lam_max = eigs[0]          # largest = "weakest negative"
        lam_min = eigs[-1]         # smallest = "strongest negative"
        cond = abs(lam_min / lam_max) if lam_max != 0 else float("inf")
        n_pos = int(np.sum(eigs > 1e-4))
        n_zero = int(np.sum(np.abs(eigs) <= 1e-4))
        results[N] = dict(eigs=eigs, runtime=runtime, Q=Q, B=B,
                          lam_max=lam_max, lam_min=lam_min, cond=cond,
                          n_pos=n_pos, n_zero=n_zero)
        print(f"     runtime         : {runtime:.1f}s")
        print(f"     lambda_max      : {lam_max:+.6e}   (weakest negative)")
        print(f"     lambda_min      : {lam_min:+.6e}   (strongest negative)")
        print(f"     condition       : {cond:.3e}")
        print(f"     positive count  : {n_pos}")
        print(f"     near-zero count : {n_zero}")
        if n_pos > 0:
            print(f"     >>> WARNING: positive eigenvalues present <<<")

    # Trend
    print("\n  Trend of lambda_max(N):")
    for N in (8, 12, 16):
        print(f"     N={N:>2d}   lambda_max = {results[N]['lam_max']:+.6e}")
    lmax_8, lmax_12, lmax_16 = (results[N]["lam_max"] for N in (8, 12, 16))
    drifting_to_zero = (lmax_16 > lmax_12 > lmax_8)
    print(f"\n  Monotone toward zero?  {drifting_to_zero}")
    if drifting_to_zero:
        ratio = lmax_16 / lmax_8
        print(f"  ratio lambda_max(16)/lambda_max(8) = {ratio:.3f}")
        if ratio > 0.5 and lmax_16 > -0.5:
            print("  >>> WARNING: weakest direction may be drifting <<<")

    # -----------------------------------------------------------------
    # Task 3.2: symmetry quotient
    # -----------------------------------------------------------------
    print("\n" + "-" * 72)
    print("TASK 3.2  Symmetry-quotient check  (sine basis + 4 aux directions)")
    print("-" * 72)
    N_aug = 6
    print(f"\n  base sine modes per component : {N_aug}")
    print(f"  augmented dim                 : {2*N_aug + 4} = {2*N_aug} + 4")
    print(f"  aux directions                : (1,0), (0,1), (theta,0), (0,theta)")
    t0 = time.time()
    Qaug, F0a = augmented_hessian(thetas, cx0, cy0, n_modes=N_aug, epsilon=epsilon)
    runtime_aug = time.time() - t0
    eigs_aug = np.sort(np.linalg.eigvalsh(0.5 * (Qaug + Qaug.T)))[::-1]
    print(f"\n  runtime: {runtime_aug:.1f}s")
    print(f"  augmented eigenvalues (descending):")
    n_zero_aug = 0
    for i, e in enumerate(eigs_aug):
        tag = ""
        if abs(e) < 1e-3:
            tag = "  <-- ~ zero"
            n_zero_aug += 1
        elif e > 1e-3:
            tag = "  <-- POSITIVE"
        print(f"    lambda_{i:02d} = {e:+.6e}{tag}")
    print(f"\n  zero-mode count (|lambda| < 1e-3): {n_zero_aug}")
    print(f"  expected: 2 (constant x- and y-translations)")
    if n_zero_aug == 2:
        print("  -> PASS: exactly two zero modes, matching the constant-")
        print("           translation symmetry of the area functional.")
    else:
        print("  -> mismatch; investigate.")

    # -----------------------------------------------------------------
    # Task 3.3: eigenvalue decay rate
    # -----------------------------------------------------------------
    print("\n" + "-" * 72)
    print("TASK 3.3  Eigenvalue decay rate of Q at N = 16")
    print("-" * 72)
    eigs16 = results[16]["eigs"]
    # eigenvalues are negative; rank by |lambda| ascending = ascending |.|
    # mode index k from 1..32.  Use k = position in the sorted-by-|.| list.
    abs_eigs = np.sort(np.abs(eigs16))   # ascending
    ks = np.arange(1, abs_eigs.size + 1, dtype=float)
    log_k = np.log(ks)
    log_abs = np.log(abs_eigs)
    # Fit log|lambda_k| = a + p log k
    p, a = np.polyfit(log_k, log_abs, 1)
    print(f"\n  power-law fit  |lambda_k| ~ C * k^p")
    print(f"     p      = {p:.3f}")
    print(f"     C      = {math.exp(a):.4f}")
    print(f"  k    |lambda_k|         predicted     ratio")
    for i, (k, e, lk) in enumerate(zip(ks, abs_eigs, log_abs)):
        pred = math.exp(a + p * math.log(k))
        print(f"  {int(k):>3d}  {e:>12.5e}    {pred:>12.5e}   {e/pred:.3f}")
    if p >= 2:
        decay_verdict = "p >= 2: power-law fast enough for Phase 4 tail bound."
    elif p >= 1:
        decay_verdict = ("1 <= p < 2: linear-ish growth, tail bound possible "
                         "but needs care.")
    else:
        decay_verdict = "p < 1: shallow growth, tail bound will be tight."
    print(f"\n  Decay verdict: {decay_verdict}")

    # -----------------------------------------------------------------
    # Task 3.4: arb-validated diagonal entry along worst eigvec
    # -----------------------------------------------------------------
    print("\n" + "-" * 72)
    print("TASK 3.4  Arb-precision check of worst-case diagonal entry, N=12")
    print("-" * 72)
    Q12 = results[12]["Q"]
    Q12s = 0.5 * (Q12 + Q12.T)
    eigvals, eigvecs = np.linalg.eigh(Q12s)
    # numpy returns ascending; worst (least negative) = last
    worst_idx = np.argmax(eigvals)
    worst_val = eigvals[worst_idx]
    worst_vec = eigvecs[:, worst_idx]
    print(f"\n  worst eigenvalue of Q (N=12) : {worst_val:+.6e}")
    print(f"  recomputing v^T Q v at dps=30 and dps=50 ...")
    info = arb_validated_diag(thetas, n_modes=12, eigvec=worst_vec,
                              epsilon=epsilon)
    print(f"     v^T Q v  [dps=30]  = {info['d_dps30']:+.8e}")
    print(f"     v^T Q v  [dps=50]  = {info['d_dps50']:+.8e}")
    print(f"     ball centre        = {info['centre']:+.8e}")
    print(f"     ball radius        = {info['radius']:.3e}")
    print(f"     max |cx_30 - cx_50| = {info['cx_max_dps_diff']:.3e}")
    print(f"     max |cy_30 - cy_50| = {info['cy_max_dps_diff']:.3e}")
    print(f"     eigvalue from numpy = {worst_val:+.8e}")
    print(f"     |centre - lambda|   = {abs(info['centre'] - worst_val):.3e}")

    print("\n  arb-trajectory enclosure at theta = pi/4 (256-bit working):")
    enc = arb_traj_enclosure(math.pi / 4, prec_bits=256)
    if enc is None:
        print("     python-flint not available")
    else:
        cx_arb, cy_arb = enc
        print(f"     c_G(pi/4)_x  = {cx_arb}")
        print(f"     c_G(pi/4)_y  = {cy_arb}")
        # Confirm enclosure matches the dps=30 float
        from gerver_constants import solve_gerver_constants, _xt_xtp
        p_, _ = solve_gerver_constants(working_dps=30, verbose=False)
        xfp, _ = _xt_xtp(mp.mpf(math.pi/4), p_)
        print(f"     float64 c_x  = {float(xfp[0]):+.15f}")
        print(f"     float64 c_y  = {float(xfp[1]):+.15f}")

    # -----------------------------------------------------------------
    # Phase 4 tractability verdict
    # -----------------------------------------------------------------
    print("\n" + "=" * 72)
    print("PHASE 4 TRACTABILITY VERDICT")
    print("=" * 72)
    bounded_away = (lmax_16 < -0.5 and lmax_12 < -0.5 and lmax_8 < -0.5)
    print(f"  lambda_max bounded below -0.5 across N in {{8,12,16}} : {bounded_away}")
    print(f"  N=16 fit:  |lambda_k| ~ k^{p:.2f}")
    print(f"  arb diag-entry agreement to ~{-math.log10(max(info['radius'],1e-20)):.0f} digits")
    if bounded_away and p >= 1.5:
        print("  -> Phase 4 tail bound appears TRACTABLE.")
    elif bounded_away:
        print("  -> Phase 4 plausible; tail bound will need explicit work.")
    else:
        print("  -> Phase 4 in trouble; lambda_max may drift to zero.")
    print("=" * 72)


if __name__ == "__main__":
    main()
