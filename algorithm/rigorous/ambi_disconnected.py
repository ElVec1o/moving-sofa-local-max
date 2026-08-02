"""ambi_disconnected.py — do DISCONNECTED competitors matter for the ambidextrous supremum?

THE QUESTION.  rem:gerverout excludes Gerver's cap data by CONNECTEDNESS: when
M := max_t c_y(t) exceeds 1/2 the two niches overlap, thm:ceiling says the body omits a
vertical strip of width 2M - 1, and a connected body lies entirely on one side of it and so
cannot meet both arms.  That argument is the only place connectedness is used, and it is
load-bearing: with overlapping niches inclusion-exclusion gives

    |S| = |C2| - |U u rho U| = |C2| - 2|N| + |U ^ rho U|  >  Q(H) ,

so overlap INCREASES the area and cannot be assumed away on extremal grounds.  If
disconnected bodies were admissible, the M >= 1/2 regime would reopen and the local
theorem would say nothing there.

WHY IT IS NOT A GAP.  A moving sofa is connected by definition -- it is a rigid body moved
through the corridor -- so the hypothesis is part of the problem, not an extra assumption.
But "it is excluded by definition" is a weak answer if the excluded competitors would win.
This file measures what they would score.

THE METHOD.  Rasterise the intersection directly rather than trusting the cap/niche
bookkeeping, which is exactly what is in question when the niches overlap:

    S = intersect_t [ Hall(t) ^ rho Hall(t) ] ,
    Hall(t) = {<w,mu_th> <= H(th) for all th} minus the wedge at the corner z(t),
    z(t) = (F-1) mu_t + (G-1) nu_t ,   F = H(t), G = H(t+pi/2), rho(x,y) = (x,1-y).

The wedge orientation {a<0, b<0} was CALIBRATED against the known answer, not derived here:
of the four quadrant choices only this one reproduces Sigma, and it is the one
ambi_connected.py describes as opening down-left.  Recorded as calibration, not as proof.

I11 REGRESSION, run every time: Sigma must come back at A_R* = 1.6449552.  Caps are drawn
by the curvature-radius construction of ambi_sigma_ball.py, so (RC) holds by construction
and the forced boundary data hold exactly; the atom at pi/2 is swept, since it is what
moves M.

Rule 7: rasterised areas on a finite grid.  The Sigma value calibrates the grid bias and
every comparison is made against it, but nothing here is a proof.

Usage: python3 ambi_disconnected.py [nsamples]
"""
from __future__ import annotations
import sys
import numpy as np

P2 = np.pi / 2
AR = 1.6449552184254408


def Hfun(r, x, atom):
    dx = x[1] - x[0]
    rs, rc = r * np.sin(x), r * np.cos(x)
    cs = np.concatenate([[0.], np.cumsum(rs[1:] + rs[:-1]) * dx / 2])
    cc = np.concatenate([[0.], np.cumsum(rc[1:] + rc[:-1]) * dx / 2])
    H = np.cos(x) + 0.5 * np.sin(x) + (np.sin(x) * cc - np.cos(x) * cs)
    return H + np.where(x >= P2, atom * np.sin(x - P2), 0.)


def rasterise(H, x, NT=260, NG=620):
    th = np.linspace(0, np.pi, NT)
    Hi = np.interp(th, x, H)
    gx = np.linspace(-1.7, 1.7, NG)
    gy = np.linspace(-1.2, 2.2, NG)
    X, Y = np.meshgrid(gx, gy)
    cell = (gx[1] - gx[0]) * (gy[1] - gy[0])
    S = np.ones_like(X, dtype=bool)
    for t, h in zip(th, Hi):
        S &= (X * np.cos(t) + Y * np.sin(t) <= h)
        S &= (X * np.cos(t) + (1 - Y) * np.sin(t) <= h)
    cy = []
    for t in np.linspace(0, P2, NT):
        F = np.interp(t, x, H); G = np.interp(t + P2, x, H)
        mu = np.array([np.cos(t), np.sin(t)]); nu = np.array([-np.sin(t), np.cos(t)])
        z = (F - 1) * mu + (G - 1) * nu
        cy.append(z[1])
        a = (X - z[0]) * mu[0] + (Y - z[1]) * mu[1]
        b = (X - z[0]) * nu[0] + (Y - z[1]) * nu[1]
        S &= ~((a < 0) & (b < 0))
        ar = (X - z[0]) * mu[0] + ((1 - Y) - z[1]) * mu[1]
        br = (X - z[0]) * nu[0] + ((1 - Y) - z[1]) * nu[1]
        S &= ~((ar < 0) & (br < 0))
    return S.sum() * cell, max(cy)


def main() -> int:
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    print(__doc__.split("Usage")[0])
    import importlib.util
    sp = importlib.util.spec_from_file_location("sb", "ambi_sigma_ball.py")
    sb = importlib.util.module_from_spec(sp); sp.loader.exec_module(sb)
    x = np.linspace(0, np.pi, 4001)
    base = sb.sigma_radius(x)
    keep = np.abs(x - P2) < sb.SPIKE_W
    A0, M0 = rasterise(Hfun(base, x, 0.0), x)
    bias = A0 - AR
    print(f"  I11 regression: Sigma rasterises to {A0:.5f} against A_R* = {AR:.7f}")
    print(f"                  grid bias {bias:+.5f}, M = {M0:.4f} (< 1/2, so Sigma is connected)\n")
    rng = np.random.default_rng(20260802)
    rows = []
    for _ in range(n):
        p = sum(rng.uniform(-1, 1) * np.sin(rng.integers(1, 8) * x + rng.uniform(0, 2 * np.pi))
                for _ in range(rng.integers(1, 6)))
        p = p / max(1e-9, np.abs(p).max())
        r = sb.restore(np.where(keep, base, np.clip(base + rng.uniform(0.05, 0.6) * p, 0, 1)),
                       x, 1.0, keep)
        if r is None:
            continue
        A, M = rasterise(Hfun(r, x, rng.uniform(0.0, 2.5)), x)
        rows.append((A - bias, M))
    conn = [a for a, M in rows if M < 0.5]
    disc = [a for a, M in rows if M >= 0.5]
    print(f"  {len(rows)} admissible caps rasterised ((RC) by construction, forced boundary data)")
    print(f"    connected     (M < 1/2): {len(conn):4d}   max area "
          f"{max(conn) if conn else float('nan'):.5f}")
    print(f"    DISCONNECTED (M >= 1/2): {len(disc):4d}   max area "
          f"{max(disc) if disc else float('nan'):.5f}")
    best_d = max(disc) if disc else -1.0
    print(f"\n  A_R* = {AR:.7f}")
    if not disc:
        print(f"  NO cap with M >= 1/2 was reached, so this run says NOTHING about")
        print(f"  disconnected competitors.  Reported as inconclusive, not as a pass.")
        return 1
    print(f"  best disconnected competitor: {best_d:.5f}  "
          f"({'BEATS A_R* -- connectedness is load-bearing' if best_d > AR else 'below A_R*'})")
    print(f"  margin {AR - best_d:+.5f}")
    return 0 if best_d <= AR else 1


if __name__ == "__main__":
    sys.exit(main())
