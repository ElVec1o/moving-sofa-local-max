"""sigma_struct_map.py — identify Sigma's boundary traversal in terms of the
ANALYTIC contact paths of both hallway families (input to the S7''' assembly).

The structure-following form Q_struct needs, per arc, the parameter range over
which that arc lies on the boundary, and the junction parameters where
consecutive arcs meet. This script determines them empirically once:

  1. build Sigma at c_R (shapely, fine grid);
  2. evaluate all 10 candidate analytic arcs (A,B,C,D,corner for the direct
     family; their rho-images for the reflected family) on a t-grid;
  3. walk d(Sigma) and label each boundary point with its nearest arc;
  4. condense into runs -> the ARCS table + junction parameters.

Contact paths (world frame, hallway H_t = R_t H + c(t), mu = R_t e_x,
nu = R_t e_y):
    A = c + <c',mu> nu + mu      (outer wall x=1)
    B = c + <c',mu> nu           (inner wall x=0)
    C = c - <c',nu> mu + nu      (outer wall y=1)
    D = c - <c',nu> mu           (inner wall y=0)
    X = c                        (reflex corner)
Reflected family: rho(p) = (p_x, 1 - p_y) applied to each.
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))

from shapely.affinity import rotate as srot, translate as strans, scale as sscale
from romik_hessian import tabulate_romik, HALLWAY, LHORIZ
from sofa_romik2017_reference import x_path, BETA

PI2 = math.pi / 2
KINKS = (0.0, BETA, PI2 - BETA, PI2)


def cjet(t, h=1e-6):
    """(c, c') at t, one-sided near the phase kinks so no stencil straddles."""
    lo, hi = t - h, t + h
    for k in KINKS:
        if lo < k < hi:
            if t <= k:
                hi = k
                lo = t - (hi - t)
            else:
                lo = k
                hi = t + (t - lo)
    lo = max(lo, 0.0); hi = min(hi, PI2)
    if hi - lo < 1e-12:          # collapsed at an endpoint: go one-sided
        if t + h <= PI2:
            lo, hi = t, t + h
        else:
            lo, hi = t - h, t
    c = np.asarray(x_path(t), float)
    p0 = np.asarray(x_path(lo), float)
    p1 = np.asarray(x_path(hi), float)
    return c, (p1 - p0) / (hi - lo)


def rho(p):
    q = np.array(p, float)
    q[..., 1] = 1.0 - q[..., 1]
    return q


def arc_table(ts):
    """dict label -> (len(ts), 2) array of contact points, both families."""
    out = {k: np.empty((len(ts), 2)) for k in ('A', 'B', 'C', 'D', 'X')}
    for i, t in enumerate(ts):
        c, cp = cjet(float(t))
        mu = np.array([math.cos(t), math.sin(t)])
        nu = np.array([-math.sin(t), math.cos(t)])
        dmu = float(cp @ mu); dnu = float(cp @ nu)
        out['A'][i] = c + dmu * nu + mu
        out['B'][i] = c + dmu * nu
        out['C'][i] = c - dnu * mu + nu
        out['D'][i] = c - dnu * mu
        out['X'][i] = c
    full = {}
    for k, v in out.items():
        full['d' + k] = v
        full['r' + k] = rho(v)
    return full


def build_sigma(n_theta=2401):
    th, cx, cy = tabulate_romik(n_theta)
    S = LHORIZ
    for t, x, y in zip(th, cx, cy):
        Hb = strans(srot(HALLWAY, math.degrees(t), origin=(0, 0)),
                    xoff=float(x), yoff=float(y))
        S = S.intersection(Hb)
    rhoS = sscale(S, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
    return S.intersection(rhoS)


def main():
    n_theta = int(sys.argv[1]) if len(sys.argv) > 1 else 2401
    n_probe = int(sys.argv[2]) if len(sys.argv) > 2 else 600
    n_t = 4001

    Sig = build_sigma(n_theta)
    print(f"area(Sigma) = {Sig.area:.7f}   (Romik 1.6449552)", flush=True)

    ts = np.linspace(1e-9, PI2 - 1e-9, n_t)
    tab = arc_table(ts)
    labels = list(tab.keys())

    ring = Sig.exterior
    L = ring.length
    pts = np.array([ring.interpolate(s * L / n_probe).coords[0]
                    for s in range(n_probe)])

    best_lab = []
    best_t = []
    best_d = []
    for P in pts:
        bl, bt, bd = None, None, 1e9
        for lab in labels:
            d2 = ((tab[lab] - P) ** 2).sum(axis=1)
            i = int(d2.argmin())
            d = math.sqrt(float(d2[i]))
            if d < bd:
                bd, bl, bt = d, lab, float(ts[i])
        best_lab.append(bl); best_t.append(bt); best_d.append(bd)

    print(f"max match distance = {max(best_d):.2e}   "
          f"median = {np.median(best_d):.2e}\n")

    # condense into runs (cyclically)
    runs = []
    for lab, t, d in zip(best_lab, best_t, best_d):
        if runs and runs[-1][0] == lab:
            runs[-1][2] = t
            runs[-1][3] = max(runs[-1][3], d)
        else:
            runs.append([lab, t, t, d])
    if len(runs) > 1 and runs[0][0] == runs[-1][0]:
        runs[0][1] = runs[-1][1]
        runs.pop()

    print("TRAVERSAL (counter-clockwise from the interpolation origin):")
    print(f"{'arc':>5} {'t_from':>9} {'t_to':>9} {'/PI2 from':>10} "
          f"{'/PI2 to':>9} {'maxdist':>10}")
    for lab, t0, t1, d in runs:
        print(f"{lab:>5} {t0:9.5f} {t1:9.5f} {t0/PI2:10.4f} {t1/PI2:9.4f} "
              f"{d:10.2e}")

    beta_u = BETA / PI2
    print(f"\nbeta = {BETA:.6f} = {beta_u:.4f}*PI2 ; "
          f"PI2-beta = {PI2-BETA:.6f} = {1-beta_u:.4f}*PI2")
    np.save(os.path.join(THIS, "sigma_struct_runs.npy"),
            np.array([(l, t0, t1) for l, t0, t1, _ in runs], dtype=object),
            allow_pickle=True)
    print("saved sigma_struct_runs.npy")


if __name__ == "__main__":
    main()
