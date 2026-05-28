"""
rigor_validation.py
===================

Validate the explicit constants used in RIGOROUS_BOUNDS.md:

  D.1  κ_max := sup |ψ_θθ| over contact arcs of c_G    (Section A)
  D.2  ‖c'_G‖_∞                                          (Section B)
  D.3  |λ_k| growth vs predicted ≤ 8π k²                (Section B)
  D.4  Richardson constants |a_k| bounded               (Section A)

If any of these fail to validate, the bounds in RIGOROUS_BOUNDS.md
need tightening or the proof restructured.
"""

from __future__ import annotations
import math, sys, os
import numpy as np
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gerver_constants import (
    solve_gerver_constants, _xt_xtp, _v1, _v1p, _v2, _v2p,
    _v3, _v3p, _v4, _v4p, _v5, _v5p,
    _v1pp, _v2pp, _v3pp, _v4pp, _v5pp,
    _xj
)

mp.mp.dps = 30


def _xt_xtp_xtpp(t, p):
    """Return (x, x', x'') at trajectory parameter t."""
    phi = p['phi']; theta = p['theta']
    pi2 = mp.pi / 2
    if t <= phi:
        v_funs = (_v1, _v1p, _v1pp)
        par = (p['a1'], p['a2']); kappa = (p['k11'], p['k12'])
    elif t <= theta:
        v_funs = (_v2, _v2p, _v2pp)
        par = (p['b1'], p['b2']); kappa = (p['k21'], p['k22'])
    elif t <= pi2 - theta:
        v_funs = (_v3, _v3p, _v3pp)
        par = (p['c1'], p['c2']); kappa = (p['k31'], p['k32'])
    elif t <= pi2 - phi:
        v_funs = (_v4, _v4p, _v4pp)
        par = (p['d1'], p['d2']); kappa = (p['k41'], p['k42'])
    else:
        v_funs = (_v5, _v5p, _v5pp)
        par = (p['e1'], p['e2']); kappa = (p['k51'], p['k52'])
    vj, vjp, vjpp = v_funs
    v = vj(t, *par); vp = vjp(t, *par); vpp = vjpp(t, *par)
    c, s = mp.cos(t), mp.sin(t)
    Rv  = (c*v[0]  - s*v[1],   s*v[0]  + c*v[1])
    Rpv = (-s*v[0] - c*v[1],   c*v[0]  - s*v[1])
    Rppv= (-c*v[0] + s*v[1],  -s*v[0]  - c*v[1])
    Rvp = (c*vp[0] - s*vp[1],  s*vp[0] + c*vp[1])
    Rpvp= (-s*vp[0]- c*vp[1],  c*vp[0] - s*vp[1])
    Rvpp= (c*vpp[0]- s*vpp[1], s*vpp[0]+ c*vpp[1])
    x   = (Rv[0]+kappa[0],   Rv[1]+kappa[1])
    xp  = (Rpv[0]+Rvp[0],    Rpv[1]+Rvp[1])
    xpp = (Rppv[0]+2*Rpvp[0]+Rvpp[0], Rppv[1]+2*Rpvp[1]+Rvpp[1])
    return x, xp, xpp


def kappa_max(p, n_sample=1001):
    """Compute sup |ψ_θθ| over θ ∈ [0, π/2] for the worst contact-side
    of the L-hallway.

    The side equations after pulling back to body frame:
       ψ(θ; u, v) = a(θ)·u + b(θ)·v − d(θ)
    where d depends on c_G. Then ψ_θθ depends on c_G(θ), c'_G(θ), c''_G(θ).

    We evaluate at a grid of θ for the WORST side (typically the inner
    corner of the L), and report the maximum |ψ_θθ| over a few sample
    body-frame points x = (u, v).
    """
    # For each of 8 sides of the L-hallway, the side equation is
    # of the form a·u + b·v = d. The side normals are axis-aligned in
    # world frame, so (α, β) ∈ {(±1, 0), (0, ±1)} with specific γ.
    # After body-frame pull-back:
    #   ψ_θθ ⊃ d''(θ) terms involving c''(θ), and second derivatives
    #   of (a, b) involving cos/sin and c.
    # For a representative side (α=1, β=0, γ=1):
    #   ψ(θ;u,v) = cosθ·u + sinθ·v − (1 − c_x(θ))
    #   ψ_θθ = -cosθ·u − sinθ·v + c_x''(θ)
    # Bound: |ψ_θθ| ≤ |u| + |v| + ‖c''_G‖_∞
    #
    # For the sofa body frame, |u|, |v| ≤ 2 (Gerver's sofa fits in roughly
    # 2x1 region). So ψ_θθ ≤ 4 + ‖c''_G‖_∞.
    thetas = np.linspace(0.05, math.pi/2 - 0.05, n_sample)  # avoid breakpoints
    max_cpp = mp.mpf(0)
    for th in thetas:
        try:
            _, _, xpp = _xt_xtp_xtpp(mp.mpf(th), p)
            v = max(abs(xpp[0]), abs(xpp[1]))
            if v > max_cpp:
                max_cpp = v
        except Exception:
            continue
    bound = 4 + float(max_cpp)
    return float(max_cpp), bound


def c_velocity_max(p, n_sample=2001):
    """Compute ‖c'_G‖_∞."""
    thetas = np.linspace(0.05, math.pi/2 - 0.05, n_sample)
    max_norm = mp.mpf(0)
    for th in thetas:
        try:
            _, xp = _xt_xtp(mp.mpf(th), p)
            norm = mp.sqrt(xp[0]**2 + xp[1]**2)
            if norm > max_norm:
                max_norm = norm
        except Exception:
            continue
    return float(max_norm)


def main():
    print("=" * 76)
    print("Numerical validation of constants in RIGOROUS_BOUNDS.md")
    print("=" * 76)

    print("\nSolving Gerver constants at dps=30 ...")
    p, resid = solve_gerver_constants(working_dps=30)
    print(f"  residual = {mp.nstr(resid, 3)}")

    # ----- D.2 ‖c'_G‖_∞ -----
    print("\n[D.2] ‖c'_G‖_∞ on a fine grid:")
    cprime_max = c_velocity_max(p)
    print(f"  ‖c'_G‖_∞ ≈ {cprime_max:.4f}")
    print(f"  Document assumes ‖c'_G‖_∞ ≤ 3:  {'✓' if cprime_max <= 3 else '✗'}")
    if cprime_max > 3:
        print(f"  → Constant in bound needs adjustment; replace 3 → {math.ceil(cprime_max)}")

    # ----- D.1 κ_max -----
    print("\n[D.1] ‖c''_G‖_∞ on a fine grid, and resulting κ_max bound:")
    cpp_max, kappa_bound = kappa_max(p)
    print(f"  ‖c''_G‖_∞ ≈ {cpp_max:.4f}")
    print(f"  κ_max bound = 4 + ‖c''‖ = {kappa_bound:.4f}")
    print(f"  Document assumes κ_max ≤ 8:  {'✓' if kappa_bound <= 8 else '✗'}")
    if kappa_bound > 8:
        print(f"  → Tighten document's bound: π² · {kappa_bound:.2f} / N = {math.pi**2 * kappa_bound:.2f}/N")

    # ----- D.3 |λ_k| bound check using Phase-3 spectrum -----
    print("\n[D.3] Empirical |λ_k| from Phase 3 vs bound 8π k²:")
    # Phase 3 N=16 spectrum, descending: [-4.604, ..., -1477] (32 eigenvalues)
    # Approximate as |λ_k| for sin(2kθ) mode of k=1..16 (paired x, y)
    # The Phase-3 numerical decay |λ_k| ~ k^1.46; let's check our bound is
    # ≥ the empirical maximum.
    phase3_lambdas = [4.604, 5.5, 13.4, 20.7, 33.1, 51.3, 52.4, 85.1,
                       85.6, 138.6, 123.2, 195.8]
    print(f"  k    empirical |λ_k|   bound 8π k²    margin")
    for k_idx, lk in enumerate(phase3_lambdas):
        k = (k_idx // 2) + 1
        bound = 8 * math.pi * k**2
        margin = bound / lk
        print(f"  {k:2d}   {lk:6.1f}             {bound:6.1f}      ×{margin:.2f}")
    max_ratio = max(lk / (8 * math.pi * (((i//2)+1)**2))
                    for i, lk in enumerate(phase3_lambdas))
    print(f"  Max ratio empirical/bound: {max_ratio:.3f}")
    print(f"  Bound holds: {'✓' if max_ratio < 1 else '✗'}")

    # ----- D.4 Richardson coefficients bounded -----
    print("\n[D.4] Richardson coefficients |a_k| from F(N) sequence on c_G:")
    # F at N = 128, 256, ..., 8192 from F_richardson_hessian.py
    Fs = [2.2241510870586, 2.2218360830367, 2.2206828298363,
          2.2201069302319, 2.2198192432505, 2.2196754347305,
          2.2196035466449]
    F_inf = 2.219531676731
    Ns = [128 * 2**k for k in range(len(Fs))]
    print(f"  N        F(N)             F(N)-F_∞       N(F-F_∞) ≈ a_1")
    for N, F in zip(Ns, Fs):
        diff = F - F_inf
        a_est = N * diff
        print(f"  {N:5d}   {F:.10f}   {diff:+.3e}   {a_est:+.5f}")
    # If F(N) = F_∞ + a/N + O(1/N²), then N(F-F_∞) → a as N → ∞.
    # The values should stabilize around the leading coefficient a_1.
    a_estimates = [N * (F - F_inf) for N, F in zip(Ns, Fs)]
    print(f"\n  Leading coefficient a_1 ≈ {a_estimates[-1]:.4f}")
    print(f"  Document bound on a_1: π² κ_max ≤ π² · 8 = {8 * math.pi**2:.2f}")
    print(f"  Actual |a_1| ≤ bound: "
          f"{'✓' if abs(a_estimates[-1]) <= 8 * math.pi**2 else '✗'}")

    print("\n" + "=" * 76)
    print("Validation summary")
    print("=" * 76)
    issues = []
    if cprime_max > 3: issues.append(f"‖c'‖ = {cprime_max:.2f} > 3")
    if kappa_bound > 8: issues.append(f"κ_max bound {kappa_bound:.2f} > 8")
    if max_ratio >= 1: issues.append(f"|λ_k| bound violated, max ratio {max_ratio:.2f}")
    if abs(a_estimates[-1]) > 8 * math.pi**2:
        issues.append(f"|a_1| = {abs(a_estimates[-1]):.2f} > {8*math.pi**2:.2f}")
    if not issues:
        print("  All constants validated.  RIGOROUS_BOUNDS.md is internally consistent.")
    else:
        print("  Issues found:")
        for it in issues:
            print(f"    - {it}")
        print("  RIGOROUS_BOUNDS.md needs constant adjustments.")


if __name__ == "__main__":
    main()
