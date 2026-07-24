"""USER-RUN heavy job: TRUE Hessian blocks (K=24, 32) with the exact oracle.

Decides item (iii) of the proof status: the K -> infinity trend of the TRUE
second variation's H1-normalized blocks (m_1 = 0.72, 0.70, 0.596 at
K = 6, 8, 16 so far -- the object the affine-junction family's envelope
recovers, and whose uniform negativity is the last spectral input).

Entries via 4-point cross differences of the kink-aware analytic oracle
(30 digits), h = 1e-3.  COST: K=24 -> 4704 oracle calls, roughly 4-6 hours
single-core.  Progress + ETA printed each row; CHECKPOINT after every row;
Ctrl-C safe; resume with the same command.

    python3 true_hessian_runner.py --K 24
    python3 true_hessian_runner.py --K 32     (roughly 4x longer)
"""
from __future__ import annotations
import argparse, math, os, sys, time
import numpy as np
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gerver_constants import solve_gerver_constants, _xt_full
from analytic_oracle import area

DPS = 30
HERE = os.path.dirname(os.path.abspath(__file__))


def traj_factory(p, coeffs, eps):
    """c_G + eps * sum_i coeffs[i] * mode_i, modes = (comp, k) sine family."""
    eps = mp.mpf(eps)
    act = [(c, k, mp.mpf(float(a))) for (c, k), a in coeffs if abs(a) > 1e-15]
    def traj(t):
        x, xp, xpp = _xt_full(t, p)
        ex = ey = e1x = e1y = e2x = e2y = mp.mpf(0)
        for c, k, a in act:
            s, sp, spp = mp.sin(2*k*t), 2*k*mp.cos(2*k*t), -4*k*k*mp.sin(2*k*t)
            if c == 'x': ex += a*s; e1x += a*sp; e2x += a*spp
            else:        ey += a*s; e1y += a*sp; e2y += a*spp
        return ((x[0]+eps*ex, x[1]+eps*ey), (xp[0]+eps*e1x, xp[1]+eps*e1y),
                (xpp[0]+eps*e2x, xpp[1]+eps*e2y))
    return traj


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--K", type=int, default=24)
    ap.add_argument("--h", type=float, default=1e-3)
    a = ap.parse_args()
    K, h = a.K, mp.mpf(a.h)
    p, _ = solve_gerver_constants(working_dps=DPS, verbose=False)
    mp.mp.dps = DPS
    modes = [(c, k) for c in ('x', 'y') for k in range(1, K+1)]
    n = len(modes)
    ck = os.path.join(HERE, f"true_hessian_K{K}.npz")
    Q = np.full((n, n), np.nan)
    if os.path.exists(ck):
        Q = np.load(ck)['Q']
        print(f"resumed: {int(np.isfinite(Q).sum())}/{n*n} cells")
    _, bk = area(traj_factory(p, [], 0), p, dps=DPS)
    A0 = area(traj_factory(p, [], 0), p, dps=DPS, b0=list(bk))[0]

    def g(coeffs, eps):
        A, _ = area(traj_factory(p, coeffs, eps), p, dps=DPS, b0=list(bk))
        return A - A0

    t0 = time.time(); done0 = int(np.isfinite(Q).sum())
    total = n*(n+1)//2
    for i in range(n):
        if np.isfinite(Q[i, i:]).all():
            continue
        for j in range(i, n):
            if np.isfinite(Q[i, j]):
                continue
            if i == j:
                gp = g([(modes[i], 1)], h); gm = g([(modes[i], 1)], -h)
                Q[i, i] = float((gp + gm)/(h*h))
            else:
                gpp = g([(modes[i], 1), (modes[j], 1)], h)
                gmm = g([(modes[i], 1), (modes[j], 1)], -h)
                gpm = g([(modes[i], 1), (modes[j], -1)], h)
                gmp = g([(modes[i], 1), (modes[j], -1)], -h)
                Q[i, j] = Q[j, i] = float((gpp + gmm - gpm - gmp)/(4*h*h))
        np.savez(ck, Q=Q)
        done = int(np.isfinite(np.triu(Q)).sum())
        el = time.time() - t0
        frac = max(done - done0, 1)/max(total - done0, 1)
        print(f"row {i+1:>3}/{n}  {100*frac:5.1f}%  elapsed {el/60:6.1f}m  "
              f"ETA {el/frac*(1-frac)/60:6.1f}m", flush=True)

    G = np.diag([math.pi/4*(1+4*k*k) for (_, k) in modes])
    S = np.diag(1/np.sqrt(np.diag(G)))
    ev = np.linalg.eigvalsh(S @ Q @ S)
    print(f"\nTRUE Hessian K={K}: H1 eigenvalues max={ev.max():+.5f} "
          f"min={ev.min():+.5f}")
    print(f"m_1(K={K}) = {-ev.max():.5f}" if ev.max() < 0
          else f"INDEFINITE ({(ev>=0).sum()} nonneg)")


if __name__ == "__main__":
    main()
