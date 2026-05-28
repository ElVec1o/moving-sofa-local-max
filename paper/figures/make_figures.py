"""Generate three figures for the manuscript.

Outputs:
    fig_gerver_sofa.pdf
    fig_spectrum.pdf
    fig_richardson.pdf
"""
from __future__ import annotations

import os
import sys
import math

import numpy as np
import matplotlib.pyplot as plt
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, ROOT)

from algorithm.rigorous.gerver_constants import (  # noqa: E402
    solve_gerver_constants, _At, _Bt, _Ct, _Dt, _xt_xtp,
)

OUT = HERE

# ---------------------------------------------------------------------
# Figure 1: Gerver's sofa
# ---------------------------------------------------------------------
def fig1():
    mp.mp.dps = 30
    p, _ = solve_gerver_constants(working_dps=30, verbose=False)
    phi = float(p['phi']); theta = float(p['theta'])
    pi2 = math.pi / 2

    def sample(func, t0, t1, n):
        ts = np.linspace(float(t0), float(t1), n)
        xs = np.empty(n); ys = np.empty(n)
        for i, t in enumerate(ts):
            tm = mp.mpf(t)
            pt = func(tm, p)
            xs[i] = float(pt[0]); ys[i] = float(pt[1])
        return xs, ys

    # CCW boundary
    Ax, Ay = sample(_At, 0, pi2, 200)
    Cx, Cy = sample(_Ct, 0, pi2, 200)
    Dx, Dy = sample(_Dt, 0, theta, 120)
    # Inner corner trajectory x(t) (reversed for boundary, but we want full curve for visual)
    def x_only(t, pp):
        x, _ = _xt_xtp(t, pp)
        return x
    XTx, XTy = sample(x_only, phi, pi2 - phi, 200)
    Bx, By = sample(_Bt, pi2 - theta, pi2, 120)

    # Build closed boundary (CCW):
    # A(0->pi/2) ; top straight to C(0); C(0->pi/2); bottom-left to D(0);
    # D(0->theta); x reverse from pi/2-phi to phi; B(pi/2-theta->pi/2);
    # straight from B(pi/2) to A(0).
    bx = list(Ax) + [Cx[0]] + list(Cx) + [Dx[0]] + list(Dx) \
        + list(XTx[::-1]) + list(Bx) + [Ax[0]]
    by = list(Ay) + [Cy[0]] + list(Cy) + [Dy[0]] + list(Dy) \
        + list(XTy[::-1]) + list(By) + [Ay[0]]

    fig, ax = plt.subplots(figsize=(5, 4.2))
    ax.fill(bx, by, color="#cfe2f3", alpha=0.85, zorder=1)
    ax.plot(bx, by, color="#1f3a93", lw=1.6, zorder=2)

    # Corner trajectory x_G(t)
    ax.plot(XTx, XTy, ':', color="#c0392b", lw=1.5, label=r"corner trajectory $x_G(\theta)$", zorder=3)

    # Breakpoints at phi, theta, pi/2-theta, pi/2-phi
    bps = [phi, theta, pi2 - theta, pi2 - phi]
    bp_x = []; bp_y = []
    for t in bps:
        pt = x_only(mp.mpf(t), p)
        bp_x.append(float(pt[0])); bp_y.append(float(pt[1]))
    ax.scatter(bp_x, bp_y, s=30, color="#c0392b", zorder=4,
               edgecolors="black", linewidths=0.5,
               label="breakpoints")
    # Also mark t=0 and t=pi/2 endpoints of trajectory
    p0 = x_only(mp.mpf(phi), p)
    p1 = x_only(mp.mpf(pi2 - phi), p)
    ax.scatter([float(p0[0]), float(p1[0])],
               [float(p0[1]), float(p1[1])],
               s=20, color="#c0392b", zorder=4, marker='s')

    ax.set_aspect("equal")
    ax.grid(True, alpha=0.25)
    ax.set_title(r"Gerver's sofa,  $A^{*} = 2.21953\ldots$")
    ax.legend(loc="upper right", fontsize=8, framealpha=0.9)
    ax.set_xlabel("x"); ax.set_ylabel("y")
    fig.tight_layout()
    out = os.path.join(OUT, "fig_gerver_sofa.pdf")
    fig.savefig(out)
    plt.close(fig)
    print("wrote", out)


# ---------------------------------------------------------------------
# Figure 2: Hessian spectrum
# ---------------------------------------------------------------------
def fig2():
    # N=12 eigenvalues (absolute values, in order k=1..12)
    abs_lam = np.array([4.81, 5.53, 15.4, 18.8, 34.2, 40.7,
                        62.1, 71.0, 100.9, 108.1, 160.6, 202.1])
    k = np.arange(1, len(abs_lam) + 1)
    bound = 8 * math.pi * k**2

    fig, ax = plt.subplots(figsize=(6, 4))
    ax.semilogy(k, abs_lam, 'o', color="#1f3a93", markersize=7,
                label=r"empirical $|\lambda_k|$ (N=12)")
    ax.semilogy(k, bound, '--', color="#c0392b", lw=1.6,
                label=r"bound $8\pi k^{2}$")
    ax.axhline(4.60, color="#1e8449", lw=1.3, linestyle=':',
               label=r"$m_N = 4.60$ (coercivity gap)")
    ax.set_xlabel("mode index $k$")
    ax.set_ylabel(r"$|\lambda_k|$  (log scale)")
    ax.set_title(r"Hessian spectrum vs analytic bound $|\lambda_k| \leq 8\pi k^{2}$")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(loc="upper left", fontsize=9)
    fig.tight_layout()
    out = os.path.join(OUT, "fig_spectrum.pdf")
    fig.savefig(out)
    plt.close(fig)
    print("wrote", out)


# ---------------------------------------------------------------------
# Figure 3: Richardson convergence
# ---------------------------------------------------------------------
def fig3():
    Nt = np.array([128, 256, 512, 1024, 2048, 4096, 8192], dtype=float)
    F = np.array([
        2.2241510870586, 2.2218360830367, 2.2206828298363,
        2.2201069302319, 2.2198192432505, 2.2196754347305,
        2.2196035466449,
    ])
    A_star = 2.219531668871967889
    err = np.abs(F - A_star)

    # O(1/N) reference line through the first point.
    ref = err[0] * (Nt[0] / Nt)

    fig, ax = plt.subplots(figsize=(6, 4.2))
    ax.loglog(Nt, err, 's', color="#c0392b", markersize=7,
              label=r"$|F(N_\theta) - A^{*}|$  (raw, level 0)")
    ax.loglog(Nt, ref, '--', color="#7f8c8d", lw=1.4,
              label=r"$\mathcal{O}(1/N_\theta)$ reference")

    # Richardson-extrapolated converged value
    rich_err = 8e-9
    ax.axhline(rich_err, color="#1e8449", lw=1.2, linestyle=':',
               label=r"Richardson level 6 error $\approx 8\times 10^{-9}$")
    # Arrow showing cancellation gain
    ax.annotate(
        "Richardson cancellation\n(p=1, 6 levels)",
        xy=(Nt[-1], rich_err), xytext=(Nt[1], err[-2] * 0.3),
        fontsize=9, color="#1e8449",
        arrowprops=dict(arrowstyle="->", color="#1e8449", lw=1.2),
    )

    ax.set_xlabel(r"$N_\theta$")
    ax.set_ylabel("error")
    ax.set_title("Polygon-intersection convergence ($p{=}1$) and Richardson cancellation")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(loc="lower left", fontsize=9)
    fig.tight_layout()
    out = os.path.join(OUT, "fig_richardson.pdf")
    fig.savefig(out)
    plt.close(fig)
    print("wrote", out)


if __name__ == "__main__":
    fig1()
    fig2()
    fig3()
