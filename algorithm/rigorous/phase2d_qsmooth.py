"""Assemble Q_smooth[k,l] analytically from Lemma 8, using a GEOMETRICALLY
EXTRACTED active-normal map psi(theta).

Lemma 8 (manuscript): the smooth per-arc second-variation integrand at c_G is
    Q^smooth(eta) = C_ab(theta) <eta_a, eta_b'> + D_ab(theta) <eta_a, eta_b''>,
with, writing psi = 2*phi + 2*theta and n^w_body = (cos phi, sin phi),
    D_xx=.5(1+cos psi)  D_yy=.5(1-cos psi)  D_xy=.5 sin psi
    C_xx=-sin psi       C_yy=+sin psi       C_xy=cos psi+1  C_yx=cos psi-1.
Here phi is the BODY-frame normal angle of the binding hallway wall, so that
    psi(theta) = 2 * (WORLD-frame normal angle of the binding wall).
For the mu-wall (x=1) the world normal angle is theta -> psi=2 theta.
For the nu-wall (y=1) it is theta+pi/2 -> psi=pi+2 theta.

We MEASURE, for each theta, which hallway wall(s) bind the sofa boundary,
by intersecting the sofa boundary with the boundary of R(theta)H + c_G(theta),
then SNAP the (noisy) measured world-normal to the nearest of the only two
physical options {2 theta (mu-wall), pi+2 theta (nu-wall)}.  We assemble
Q_smooth on the sine basis phi_k(theta)=sin(2k theta) (x and y components).

IMPORTANT CAVEAT (validated by this script):  the diagonal sum rule
    Q_smooth[k,k]_x + Q_smooth[k,k]_y = -pi k^2
follows ALGEBRAICALLY from D_xx+D_yy==1 and C_xx+C_yy==0 and is therefore
INDEPENDENT of psi(theta).  It validates the assembly MACHINERY (and catches
the factor-2 symmetrisation bug) but it CANNOT validate the psi-map itself.
The OFF-DIAGONAL entries Q_smooth[k,l] do depend on psi, and the per-arc
active-normal map psi(theta) is exactly the open analytic item: it is not
pinned down by the sum rule, and the raw geometric measurement is too jittery
(two walls bind with near-equal segment length at most theta) to trust for
the off-diagonal.  Treat the off-diagonal output as psi-conditional.

Output: q_smooth_NxN.npz  (matrix + the snapped psi map), plus a printed
sum-rule check.  Lightweight (one sofa build + per-theta boundary probe).
"""
from __future__ import annotations
import math, time, json, os
import numpy as np
import mpmath as mp
from shapely.geometry import Polygon as SPoly, LineString, MultiLineString
from shapely.affinity import rotate as srot, translate as strans
from shapely.ops import unary_union

from gerver_constants import solve_gerver_constants, _xt_xtp

HERE = os.path.dirname(os.path.abspath(__file__))
K_BIG = 8.0
HALF = math.pi / 2


def hallway_poly(K=K_BIG):
    horiz = SPoly([(-K, 0), (1, 0), (1, 1), (-K, 1)])
    vert = SPoly([(0, -K), (1, -K), (1, 1), (0, 1)])
    return unary_union([horiz, vert])


HALLWAY = hallway_poly()


def tabulate_gerver(n_theta, dps=30):
    p, _ = solve_gerver_constants(working_dps=dps, verbose=False)
    th = np.linspace(0.0, HALF, n_theta)
    cx = np.empty(n_theta); cy = np.empty(n_theta)
    for i, t in enumerate(th):
        x, _ = _xt_xtp(mp.mpf(t), p)
        cx[i] = float(x[0]); cy[i] = float(x[1])
    return th, cx, cy


def build_sofa(th, cx, cy):
    S = None
    for t, x, y in zip(th, cx, cy):
        Hb = strans(srot(HALLWAY, math.degrees(t), origin=(0, 0)), xoff=x, yoff=y)
        S = Hb if S is None else S.intersection(Hb)
    return S


def measure_psi(th, cx, cy, S, tol=1e-7):
    """For each theta, find the world-normal angle(s) of the binding wall(s):
    the segments of S.boundary that lie on the boundary of R(theta)H+c(theta).
    Returns list per theta of (world_normal_angle, seg_length)."""
    Sb = S.boundary
    out = []
    for t, x, y in zip(th, cx, cy):
        Hb = strans(srot(HALLWAY, math.degrees(t), origin=(0, 0)), xoff=x, yoff=y)
        shared = Sb.intersection(Hb.boundary)
        segs = []
        geoms = []
        if isinstance(shared, (LineString,)):
            geoms = [shared]
        elif isinstance(shared, MultiLineString):
            geoms = list(shared.geoms)
        elif hasattr(shared, "geoms"):
            geoms = [g for g in shared.geoms if isinstance(g, LineString)]
        for g in geoms:
            if g.length < tol:
                continue
            (x0, y0), (x1, y1) = g.coords[0], g.coords[-1]
            ex, ey = x1 - x0, y1 - y0
            L = math.hypot(ex, ey)
            if L < tol:
                continue
            # outward normal of S along this edge: rotate edge dir by -90, then
            # orient outward (away from S centroid).
            nx, ny = ey / L, -ex / L
            cxc, cyc = S.centroid.x, S.centroid.y
            mxx, myy = (x0 + x1) / 2, (y0 + y1) / 2
            if (mxx - cxc) * nx + (myy - cyc) * ny < 0:
                nx, ny = -nx, -ny
            beta = math.atan2(ny, nx) % (2 * math.pi)
            segs.append((beta, g.length))
        out.append(segs)
    return out


def basis_derivs(th, N):
    k = np.arange(1, N + 1)
    arg = np.outer(th, 2 * k)             # (n_theta, N)
    phi = np.sin(arg)
    phip = (2 * k) * np.cos(arg)
    phipp = -((2 * k) ** 2) * np.sin(arg)
    return phi, phip, phipp


def coeffs(psi):
    cps, sps = np.cos(psi), np.sin(psi)
    D = {("x", "x"): 0.5 * (1 + cps), ("y", "y"): 0.5 * (1 - cps),
         ("x", "y"): 0.5 * sps, ("y", "x"): 0.5 * sps}
    C = {("x", "x"): -sps, ("y", "y"): sps,
         ("x", "y"): cps + 1, ("y", "x"): cps - 1}
    return C, D


def assemble(th, psi_theta, weight, N):
    """Q_smooth on the 2N-dim basis (x-block then y-block).
    Symmetric bilinear form of the quadratic Q(eta)=INT[C<eta,eta'>+D<eta,eta''>]:
      Q[(a,k),(b,l)] = 1/2 INT [ C_ab phi_k phi_l' + C_ba phi_l phi_k'
                               + D_ab phi_k phi_l'' + D_ba phi_l phi_k'' ] w dtheta.
    The leading 1/2 is required so the DIAGONAL (a=b, k=l) reproduces the
    quadratic-form value Q(e_k)=INT[C phi_k phi_k' + D phi_k phi_k''] rather than
    twice it; without it the sum rule comes out at -2 pi k^2 (exact factor 2).
    """
    phi, phip, phipp = basis_derivs(th, N)
    C, D = coeffs(psi_theta)
    comps = ["x", "y"]
    Q = np.zeros((2 * N, 2 * N))
    w = weight
    # trapezoid weights on the theta grid
    dt = np.gradient(th)
    for ia, a in enumerate(comps):
        for ib, b in enumerate(comps):
            Cab, Cba = C[(a, b)], C[(b, a)]
            Dab, Dba = D[(a, b)], D[(b, a)]
            for k in range(N):
                for l in range(N):
                    integ = (Cab * phi[:, k] * phip[:, l]
                             + Cba * phi[:, l] * phip[:, k]
                             + Dab * phi[:, k] * phipp[:, l]
                             + Dba * phi[:, l] * phipp[:, k]) * w
                    Q[ia * N + k, ib * N + l] = 0.5 * np.sum(integ * dt)
    return Q


def main():
    import sys
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    n_theta = int(sys.argv[2]) if len(sys.argv) > 2 else 2001
    print(f"[Q_smooth assembly]  N={N} modes/component, n_theta={n_theta}")
    t0 = time.time()
    th, cx, cy = tabulate_gerver(n_theta)
    S = build_sofa(th, cx, cy)
    print(f"  sofa area = {S.area:.7f}  (Gerver 2.2195317)   [{time.time()-t0:.1f}s]")

    segs = measure_psi(th, cx, cy, S)
    nwalls = np.array([len(s) for s in segs])
    print(f"  binding-wall count per theta: min={nwalls.min()} max={nwalls.max()} "
          f"mean={nwalls.mean():.2f}")
    # Build a single effective psi per theta: take the LONGEST binding segment
    # (dominant wall).  Also assemble the SUM over all walls, for comparison.
    psi_raw = np.full(n_theta, np.nan)
    for i, s in enumerate(segs):
        if s:
            beta = max(s, key=lambda z: z[1])[0]
            psi_raw[i] = 2 * beta
    # fill any gaps by nearest
    good = ~np.isnan(psi_raw)
    if not good.all():
        idx = np.where(good)[0]
        for i in np.where(~good)[0]:
            j = idx[np.argmin(np.abs(idx - i))]
            psi_raw[i] = psi_raw[j]
    # The only two physical binding walls give psi in {2 theta, pi + 2 theta}
    # (mu-wall x=1 vs nu-wall y=1).  The raw geometric beta is noisy, so SNAP
    # each theta to whichever of the two analytic values is angularly closest:
    # this keeps the geometric DECISION (which wall dominates) but removes the
    # measurement jitter that produced hundreds of spurious flips.
    def angdist(a, b):
        d = (a - b) % (2 * math.pi)
        return np.minimum(d, 2 * math.pi - d)
    psi_mu = (2 * th) % (2 * math.pi)
    psi_nu = (math.pi + 2 * th) % (2 * math.pi)
    pick_nu = angdist(psi_raw, psi_nu) < angdist(psi_raw, psi_mu)
    psi_dom = np.where(pick_nu, psi_nu, psi_mu)

    # report transitions of dominant wall (where cos psi flips sign of 2theta vs pi+2theta)
    # classify each theta: is psi ~ 2 theta (mu) or pi+2 theta (nu)?
    cls = np.where(np.isclose(np.cos(psi_dom), np.cos(2 * th), atol=0.1), "mu", "nu")
    # find class change indices
    changes = [float(th[i]) for i in range(1, n_theta) if cls[i] != cls[i-1]]
    print(f"  dominant-wall class transitions at theta = "
          + ", ".join(f"{c:.4f}" for c in changes))
    print(f"  (Romik breakpoints: 0.0392, 0.6813, 0.8895, 1.5316)")

    # Assemble with dominant single wall, weight=1
    Q = assemble(th, psi_dom, np.ones(n_theta), N)

    # sum-rule check on diagonal: Q[k,k]_x + Q[k,k]_y should be -pi k^2
    print("\n  sum-rule check  Q[k,k]_x + Q[k,k]_y  vs  -pi k^2:")
    ok = True
    for k in range(N):
        s = Q[k, k] + Q[N + k, N + k]
        target = -math.pi * (k + 1) ** 2
        rel = abs(s - target) / abs(target)
        flag = "" if rel < 0.02 else "  <-- OFF"
        if rel >= 0.02:
            ok = False
        print(f"    k={k+1:2d}: {s:+.4f}  target {target:+.4f}  rel {rel:.2%}{flag}")
    print(f"\n  SUM RULE {'HOLDS' if ok else 'FAILS'} for the dominant-wall psi map.")

    np.savez(os.path.join(HERE, f"q_smooth_N{N}.npz"),
             Q=Q, psi_dom=psi_dom, theta=th, nwalls=nwalls)
    print(f"  saved q_smooth_N{N}.npz   [{time.time()-t0:.1f}s total]")


if __name__ == "__main__":
    main()
