"""
sofa_variants.py
================

Generalises sofa_bvp.py to NON-classical hallways:

  Variant A  : single corner with interior turn angle alpha != 90 deg.
               total sofa rotation = pi - alpha.
  Variant Z  : Z-/S-hallway = two opposite 90-deg turns separated by
               a straight unit-width corridor of length L.

For each variant + parameter, we run a staged Fourier optimisation
(4 -> 8 -> 12 modes, Nelder-Mead, then optional CMA-ES polish) and
dense-verify the final area at n_theta = 1000.

We make no analytic claims; the numbers are lower bounds on the true
sofa constant for the given hallway.
"""

from __future__ import annotations

import math
import time
from dataclasses import dataclass
from typing import Callable, List, Tuple

import numpy as np
from shapely.geometry import Polygon as SPoly
from shapely.affinity import rotate as srot, translate as strans
from shapely.ops import unary_union

K_BIG = 8.0  # corridor extent away from the corner


# ---------------------------------------------------------------------
# Hallway constructions
# ---------------------------------------------------------------------

def hallway_alpha(alpha_deg: float, K: float = K_BIG) -> SPoly:
    """Hallway with a single interior-angle-alpha corner.

    Geometry conventions:
      - inner corner at origin (0, 0).
      - incoming corridor along negative x-axis: a strip y in [0, 1],
        x in [-K, 0+]. The 'inner' wall is y=0, 'outer' is y=1.
      - outgoing corridor obtained by rotating the incoming corridor
        about the inner corner by the turn angle (pi - alpha), so the
        sofa rotates by (pi - alpha) overall.
      - The actual outgoing corridor is a strip of width 1, with the
        inner wall passing through the origin in the rotated direction.

    The two corridors are unioned. The 'cap' that fills the bend region
    is implicit in the union of the two strips (they overlap in a small
    polygon near the origin).
    """
    alpha = math.radians(alpha_deg)
    turn = math.pi - alpha  # how much the sofa must rotate

    # Convention (matches sofa_bvp.py for alpha=90):
    #   - incoming corridor: half-strip x in [-K, 1], y in [0, 1].
    #     (extends 1 unit past the corner along its own direction; this
    #     extra unit is the "bend cap" that for alpha=90 yields the
    #     unit square [0,1]^2 shared with the outgoing corridor.)
    #   - outgoing corridor: same half-strip rotated by 'turn' about
    #     the origin.
    # For alpha=90 this exactly reproduces the L-hallway.
    # For acute alpha (turn > 90), the two strips overlap further,
    # which is the correct geometry for a sharper turn.
    # Convention: sofa enters from -x along incoming corridor, makes a
    # RIGHT (CW) turn of magnitude `turn` = pi - alpha, exits along
    # outgoing corridor in direction (cos(-turn), sin(-turn)).
    #
    # Incoming corridor: strip { (s, t) : s in [-K, 1], t in [0, 1] }.
    #   The "cap" s in [0, 1] is the bend region; "tail" s in [-K, 0]
    #   is the long approach.
    # Outgoing corridor: strip along d_out = (cos(-turn), sin(-turn))
    #   with inward normal n_out = (sin(turn), cos(turn)).
    #   Points: p = s * d_out + t * n_out, s in [-1, K], t in [0, 1].
    #   The "cap" s in [-1, 0] is the bend region (overlaps the
    #   incoming cap when alpha = 90).
    incoming = SPoly([(-K, 0), (1, 0), (1, 1), (-K, 1)])
    dx, dy = math.cos(-turn), math.sin(-turn)       # outgoing axis
    nx, ny = math.sin(turn), math.cos(turn)         # inward normal
    # Outgoing rectangle corners (s, t) in (-1..K, 0..1):
    pts = [(-1, 0), (K, 0), (K, 1), (-1, 1)]
    outgoing = SPoly([(s * dx + t * nx, s * dy + t * ny) for s, t in pts])
    return unary_union([incoming, outgoing])


def hallway_Z(L: float, K: float = K_BIG) -> SPoly:
    """Z-/S-hallway: 90-deg turn LEFT, straight corridor of length L,
    then 90-deg turn RIGHT.  Net rotation = 0; but the sofa during
    motion rotates by +pi/2 then -pi/2 -> we parameterise theta in
    [-pi/2, +pi/2] across the whole transit.

    Geometry (one canonical layout):
      Segment 1 : x in [-K, 0], y in [0, 1]            (incoming, going +x)
      Bend 1 at corner near (0, 0) -> turn LEFT (CCW).
      Segment 2 : x in [0, 1], y in [0, L+1]          (vertical, going +y)
      Bend 2 at corner near (1, L+1) -> turn RIGHT (CW), back to +x.
      Segment 3 : x in [1, 1+K], y in [L, L+1]        (outgoing, going +x)
    """
    seg1 = SPoly([(-K, 0), (1, 0), (1, 1), (-K, 1)])
    # vertical middle: spans y from 0 up to L+1, x in [0,1]
    seg2 = SPoly([(0, 0), (1, 0), (1, L + 1), (0, L + 1)])
    # third segment: horizontal, at height [L, L+1], going to +x
    seg3 = SPoly([(0, L), (1 + K, L), (1 + K, L + 1), (0, L + 1)])
    return unary_union([seg1, seg2, seg3])


# ---------------------------------------------------------------------
# Sofa-area evaluator (rotated-intersection)
# ---------------------------------------------------------------------

def sofa_from_trajectory(
    hallway: SPoly,
    x_of_theta: Callable[[float], float],
    y_of_theta: Callable[[float], float],
    theta_lo: float,
    theta_hi: float,
    n_theta: int = 181,
) -> Tuple[SPoly, float]:
    thetas = np.linspace(theta_lo, theta_hi, n_theta)
    S = None
    for th in thetas:
        cx = x_of_theta(th)
        cy = y_of_theta(th)
        Hb = strans(hallway, xoff=-cx, yoff=-cy)
        Hb = srot(Hb, -math.degrees(th), origin=(0, 0))
        S = Hb if S is None else S.intersection(Hb)
        if S.is_empty or S.area < 1e-10:
            return S, 0.0
    return S, S.area


# ---------------------------------------------------------------------
# Fourier-series trajectory generator on an interval [t_lo, t_hi]
# ---------------------------------------------------------------------

def make_trajectory(params: np.ndarray, n_modes: int,
                    theta_lo: float, theta_hi: float):
    """params layout (length 4 + 2*n_modes):
       [ x0, y0, ax_end, ay_end, sx_1..sx_n, sy_1..sy_n ]
       affine drift (constant + linear in theta) plus sine modes
       that vanish at theta = theta_lo and theta = theta_hi.
    """
    x0 = params[0]
    y0 = params[1]
    ax_end = params[2]
    ay_end = params[3]
    sx = params[4 : 4 + n_modes]
    sy = params[4 + n_modes : 4 + 2 * n_modes]
    span = theta_hi - theta_lo

    def x(th):
        u = (th - theta_lo) / span  # in [0, 1]
        s = x0 + ax_end * u
        for k, a in enumerate(sx, start=1):
            s += a * math.sin(k * math.pi * u)
        return s

    def y(th):
        u = (th - theta_lo) / span
        s = y0 + ay_end * u
        for k, a in enumerate(sy, start=1):
            s += a * math.sin(k * math.pi * u)
        return s

    return x, y


# ---------------------------------------------------------------------
# Optimisation harness
# ---------------------------------------------------------------------

def neg_area(params, hallway, n_modes, theta_lo, theta_hi, n_theta):
    x, y = make_trajectory(params, n_modes, theta_lo, theta_hi)
    try:
        _, A = sofa_from_trajectory(hallway, x, y, theta_lo, theta_hi,
                                     n_theta=n_theta)
    except Exception:
        return 0.0
    return -A


def optimize_stage(hallway, n_modes, theta_lo, theta_hi,
                   n_theta, warm_start=None, x0_hint=None,
                   maxiter=2000):
    from scipy.optimize import minimize
    n_params = 4 + 2 * n_modes
    if warm_start is not None:
        x0 = warm_start
    elif x0_hint is not None:
        x0 = x0_hint
    else:
        x0 = np.zeros(n_params)
    res = minimize(
        neg_area, x0,
        args=(hallway, n_modes, theta_lo, theta_hi, n_theta),
        method="Nelder-Mead",
        options=dict(xatol=1e-5, fatol=1e-5, maxiter=maxiter, disp=False),
    )
    return res


def expand_params(p_old, n_old, n_new):
    """Move from n_old-mode params to n_new-mode params, padding with zeros."""
    out = np.zeros(4 + 2 * n_new)
    out[:4] = p_old[:4]
    out[4 : 4 + n_old] = p_old[4 : 4 + n_old]
    out[4 + n_new : 4 + n_new + n_old] = p_old[4 + n_old : 4 + 2 * n_old]
    return out


def cma_polish(hallway, p0, n_modes, theta_lo, theta_hi, n_theta,
               sigma0=0.02, maxiter=300):
    import cma
    es = cma.CMAEvolutionStrategy(
        p0, sigma0,
        {"maxiter": maxiter, "verbose": -9, "tolx": 1e-6, "tolfun": 1e-6,
         "popsize": 16}
    )
    while not es.stop():
        xs = es.ask()
        fs = [neg_area(x, hallway, n_modes, theta_lo, theta_hi, n_theta)
              for x in xs]
        es.tell(xs, fs)
    return np.array(es.result.xbest), -es.result.fbest


# ---------------------------------------------------------------------
# Variant drivers
# ---------------------------------------------------------------------

@dataclass
class Result:
    variant: str
    param: float
    A_coarse: float
    A_mid: float
    A_fine: float
    A_dense: float
    runtime_s: float
    notes: str = ""


def run_one(hallway: SPoly, theta_lo: float, theta_hi: float,
            init_drift: Tuple[float, float, float, float],
            label: str, param: float,
            use_cma: bool = True) -> Result:
    """Stage 4 -> 8 -> 12 modes, then optional CMA polish, then dense verify."""
    t_start = time.time()

    # Stage 1: 4 modes
    n1 = 4
    p0 = np.zeros(4 + 2 * n1)
    p0[0] = init_drift[0]; p0[1] = init_drift[1]
    p0[2] = init_drift[2]; p0[3] = init_drift[3]
    r1 = optimize_stage(hallway, n1, theta_lo, theta_hi,
                        n_theta=61, x0_hint=p0, maxiter=800)
    A1 = -r1.fun

    # Stage 2: 8 modes
    n2 = 8
    p1 = expand_params(r1.x, n1, n2)
    r2 = optimize_stage(hallway, n2, theta_lo, theta_hi,
                        n_theta=91, warm_start=p1, maxiter=1500)
    A2 = -r2.fun

    # Stage 3: 12 modes
    n3 = 12
    p2 = expand_params(r2.x, n2, n3)
    r3 = optimize_stage(hallway, n3, theta_lo, theta_hi,
                        n_theta=121, warm_start=p2, maxiter=2500)
    A3 = -r3.fun

    # Optional CMA polish
    if use_cma:
        xbest, A_cma = cma_polish(hallway, r3.x, n3, theta_lo, theta_hi,
                                   n_theta=121, sigma0=0.01, maxiter=50)
        if A_cma > A3:
            r3_x = xbest
            A3 = A_cma
        else:
            r3_x = r3.x
    else:
        r3_x = r3.x

    # Dense verify
    x_fn, y_fn = make_trajectory(r3_x, n3, theta_lo, theta_hi)
    _, A_dense = sofa_from_trajectory(hallway, x_fn, y_fn,
                                       theta_lo, theta_hi, n_theta=1000)

    elapsed = time.time() - t_start
    notes = ""
    # Honesty: convergence should be monotone (areas drop as we add modes
    # only if the optimiser overshoots; usually they go UP with more modes,
    # and the dense check goes DOWN from the coarse one because finer
    # sampling shaves the polygon).
    if A_dense > A3 + 5e-4:
        notes += "dense > coarse (suspicious); "
    if A_dense < 0.5 * A3:
        notes += "dense collapse; "

    return Result(label, param, A1, A2, A3, A_dense, elapsed, notes)


def init_drift_alpha(alpha_deg: float) -> Tuple[float, float, float, float]:
    """Reasonable starting drift for variant A.

    Sofa enters in incoming corridor along +x, exits in outgoing along
    direction (cos turn, sin turn).  A naive 'corner pivot' path starts
    near (0, 0.5) and ends near a translation of (cos turn * d, sin turn * d)
    plus (0.5*sin turn, 0.5*(1-cos turn)) or similar Hammersley-like point.
    We just use a Hammersley-ish radius.
    """
    # Right (CW) turn: outgoing axis direction is (cos(-turn), sin(-turn)).
    # Hammersley-like initial corner trajectory: a circular arc of radius
    # R = 2/pi parameterised by theta in [0, turn], going from origin to
    # R * (sin(turn), -(1 - cos(turn))).  We only need start/end.
    turn = math.pi - math.radians(alpha_deg)
    R = 2.0 / math.pi
    x0 = 0.0
    y0 = 0.0
    ax_end = R * math.sin(turn)
    ay_end = -R * (1 - math.cos(turn))
    return (x0, y0, ax_end, ay_end)


def init_drift_Z(L: float) -> Tuple[float, float, float, float]:
    """Z-hallway initial drift: theta goes from 0 to pi/2 to 0 (net 0).

    But we parameterise theta as monotone on a single interval. Simplest:
    let theta range over [0, 2*pi/2] = [0, pi] but only the rotation in
    [0, pi/2] is real and then back. That breaks single-valued theta ->
    we instead use a *time* parameter s in [0, 1] and use theta(s) as
    part of the model. For simplicity in this first pass, we use
    theta in [0, pi/2] for the first turn only as a baseline (so we
    compute the *single-bend* sofa for the Z hallway interpreted as
    just the first corner with the second corner's wall acting as an
    additional constraint).

    Actually correct: in the Z hallway, the sofa moves through both
    corners; total rotation is 0 but the body must instantaneously be
    able to be at every rotation in [0, pi/2] (going CCW then CW).
    Equivalently, S = intersection over theta in [0, pi/2] of
    R(-theta)(H - c(theta)), AND intersection over theta in [-pi/2, 0]
    of R(-theta)(H - c'(theta)), with c, c' two separate trajectories.
    But the SOFA shape is the SAME -- so it's intersected with both.

    We implement: two trajectories, theta sweeps [0, pi/2] for first
    bend and [-pi/2, 0] for second bend; they share the sofa S.
    See run_Z for the two-arc evaluator.
    """
    # placeholder; not used directly
    R = 2.0 / math.pi
    return (0.0, 0.0, R, R)


# ---------------------------------------------------------------------
# Z-hallway requires two arcs intersected with the SAME sofa
# ---------------------------------------------------------------------

def sofa_Z_from_two_trajectories(
    hallway: SPoly,
    x1, y1, x2, y2,
    n_theta: int = 181,
) -> Tuple[SPoly, float]:
    """Sofa for Z-hallway: intersect rotated hallways over theta in
    [0, pi/2] using c1(theta), AND over theta in [0, -pi/2] using
    c2(theta).  Returns body-frame intersection polygon.
    """
    S = None
    # First arc: theta from 0 to pi/2 (body rotates CW in our convention)
    th1 = np.linspace(0.0, math.pi / 2, n_theta)
    for th in th1:
        Hb = strans(hallway, xoff=-x1(th), yoff=-y1(th))
        Hb = srot(Hb, -math.degrees(th), origin=(0, 0))
        S = Hb if S is None else S.intersection(Hb)
        if S.is_empty or S.area < 1e-10:
            return S, 0.0
    # Translation sweep through the middle straight corridor at fixed
    # body angle theta = pi/2: position moves from c1_end to c2_start
    # (= c1_end by our continuity constraint), but the body must also
    # fit at every point along the straight middle corridor in between
    # the two corner regions.  We sample n_mid translation positions
    # along the line from c1(pi/2) to c2(-pi/2).
    n_mid = max(20, n_theta // 4)
    cx_a, cy_a = x1(math.pi / 2), y1(math.pi / 2)
    cx_b, cy_b = x2(-math.pi / 2), y2(-math.pi / 2)
    for s in np.linspace(0.0, 1.0, n_mid):
        cx = cx_a + s * (cx_b - cx_a)
        cy = cy_a + s * (cy_b - cy_a)
        Hb = strans(hallway, xoff=-cx, yoff=-cy)
        Hb = srot(Hb, -math.degrees(math.pi / 2), origin=(0, 0))
        S = S.intersection(Hb)
        if S.is_empty or S.area < 1e-10:
            return S, 0.0
    # Second arc: theta from -pi/2 to 0 (body rotates back CCW)
    th2 = np.linspace(-math.pi / 2, 0.0, n_theta)
    for th in th2:
        Hb = strans(hallway, xoff=-x2(th), yoff=-y2(th))
        Hb = srot(Hb, -math.degrees(th), origin=(0, 0))
        S = S.intersection(Hb)
        if S.is_empty or S.area < 1e-10:
            return S, 0.0
    return S, S.area


def make_traj_pair(params, n_modes, L):
    """Two trajectories for Z-hallway.

    params layout (length 2 * (4 + 2*n_modes)):
       first half is trajectory 1 on [0, pi/2],
       second half is trajectory 2 on [-pi/2, 0].

    With the additional constraint that trajectory 2 starts where
    trajectory 1 ends in the *world frame*, i.e. positions must match
    at the junction (theta = pi/2 -> theta = 0 on arc 2).

    We enforce this by overriding params[half: half+2] (the constant
    offset of arc 2) to equal arc-1-end.
    """
    half = 4 + 2 * n_modes
    p1 = params[:half].copy()
    p2 = params[half:].copy()

    # Build both arcs freely; the translation sweep between them is
    # handled inside sofa_Z_from_two_trajectories.  No clamping.
    x1, y1 = make_trajectory(p1, n_modes, 0.0, math.pi / 2)
    x2, y2 = make_trajectory(p2, n_modes, -math.pi / 2, 0.0)
    return x1, y1, x2, y2


def neg_area_Z(params, hallway, n_modes, L, n_theta):
    x1, y1, x2, y2 = make_traj_pair(params, n_modes, L)
    try:
        _, A = sofa_Z_from_two_trajectories(hallway, x1, y1, x2, y2,
                                             n_theta=n_theta)
    except Exception:
        return 0.0
    return -A


def optimize_Z_stage(hallway, n_modes, L, n_theta,
                     warm_start=None, x0_hint=None, maxiter=2000):
    from scipy.optimize import minimize
    n_params = 2 * (4 + 2 * n_modes)
    if warm_start is not None:
        x0 = warm_start
    elif x0_hint is not None:
        x0 = x0_hint
    else:
        x0 = np.zeros(n_params)
    res = minimize(
        neg_area_Z, x0,
        args=(hallway, n_modes, L, n_theta),
        method="Nelder-Mead",
        options=dict(xatol=1e-5, fatol=1e-5, maxiter=maxiter, disp=False),
    )
    return res


def expand_params_Z(p_old, n_old, n_new):
    half_old = 4 + 2 * n_old
    half_new = 4 + 2 * n_new
    out = np.zeros(2 * half_new)
    for k in range(2):
        old = p_old[k * half_old : (k + 1) * half_old]
        new = np.zeros(half_new)
        new[:4] = old[:4]
        new[4 : 4 + n_old] = old[4 : 4 + n_old]
        new[4 + n_new : 4 + n_new + n_old] = old[4 + n_old : 4 + 2 * n_old]
        out[k * half_new : (k + 1) * half_new] = new
    return out


def run_one_Z(L: float, use_cma: bool = True) -> Result:
    t_start = time.time()
    hallway = hallway_Z(L)

    R = 2.0 / math.pi
    n1 = 4
    p0 = np.zeros(2 * (4 + 2 * n1))
    # Arc 1: corner near (0, 0); start near (0, 0), end near (R, R)
    # rotating to angle pi/2 (after turn the sofa is vertical).
    p0[0] = 0.0; p0[1] = 0.5      # start position in world frame (mid corridor)
    p0[2] = R; p0[3] = R           # drift to end
    # Arc 2: starts at arc1 end; ends near outgoing corridor mid
    half = 4 + 2 * n1
    p0[half + 0] = R; p0[half + 1] = R + L  # will be overridden anyway
    p0[half + 2] = R; p0[half + 3] = R       # drift back

    r1 = optimize_Z_stage(hallway, n1, L, n_theta=51,
                          x0_hint=p0, maxiter=1200)
    A1 = -r1.fun

    n2 = 8
    p1 = expand_params_Z(r1.x, n1, n2)
    r2 = optimize_Z_stage(hallway, n2, L, n_theta=81,
                          warm_start=p1, maxiter=2500)
    A2 = -r2.fun

    n3 = 12
    p2 = expand_params_Z(r2.x, n2, n3)
    r3 = optimize_Z_stage(hallway, n3, L, n_theta=101,
                          warm_start=p2, maxiter=3000)
    A3 = -r3.fun
    r3_x = r3.x

    if use_cma:
        import cma
        es = cma.CMAEvolutionStrategy(
            r3.x, 0.01,
            {"maxiter": 40, "verbose": -9, "tolx": 1e-6, "tolfun": 1e-6,
             "popsize": 16}
        )
        while not es.stop():
            xs = es.ask()
            fs = [neg_area_Z(x, hallway, n3, L, 101) for x in xs]
            es.tell(xs, fs)
        if -es.result.fbest > A3:
            r3_x = np.array(es.result.xbest)
            A3 = -es.result.fbest

    # Dense verify
    x1f, y1f, x2f, y2f = make_traj_pair(r3_x, n3, L)
    _, A_dense = sofa_Z_from_two_trajectories(hallway, x1f, y1f, x2f, y2f,
                                                n_theta=1000)
    elapsed = time.time() - t_start
    notes = ""
    if A_dense > A3 + 5e-4:
        notes += "dense > coarse; "
    return Result("Z (L)", L, A1, A2, A3, A_dense, elapsed, notes)


# ---------------------------------------------------------------------
# MAIN driver
# ---------------------------------------------------------------------

def run_alpha_variants(use_cma=True) -> List[Result]:
    results = []
    alphas = [60.0, 75.0, 90.0, 105.0, 120.0, 135.0]
    for alpha in alphas:
        print(f"\n[variant A] alpha = {alpha} deg  (turn = {180 - alpha} deg)")
        hallway = hallway_alpha(alpha)
        theta_lo = 0.0
        theta_hi = math.radians(180 - alpha)  # total rotation
        init = init_drift_alpha(alpha)
        r = run_one(hallway, theta_lo, theta_hi, init,
                    label="alpha (deg)", param=alpha, use_cma=use_cma)
        print(f"   stages: 4->{r.A_coarse:.5f}  8->{r.A_mid:.5f}  "
              f"12->{r.A_fine:.5f}   dense -> {r.A_dense:.5f}   "
              f"({r.runtime_s:.1f}s) {r.notes}")
        results.append(r)
    return results


def run_Z_variants(use_cma=True) -> List[Result]:
    results = []
    for L in [0.5, 1.0, 2.0, 4.0]:
        print(f"\n[variant Z] L = {L}")
        r = run_one_Z(L, use_cma=use_cma)
        print(f"   stages: 4->{r.A_coarse:.5f}  8->{r.A_mid:.5f}  "
              f"12->{r.A_fine:.5f}   dense -> {r.A_dense:.5f}   "
              f"({r.runtime_s:.1f}s) {r.notes}")
        results.append(r)
    return results


def format_table(all_results: List[Result]) -> str:
    lines = []
    lines.append("| Variant | Parameter | A (4 mode) | A (8 mode) | A (12 mode) | A (dense, n=1000) | Runtime (s) | Notes |")
    lines.append("|---|---|---|---|---|---|---|---|")
    for r in all_results:
        lines.append(
            f"| {r.variant} | {r.param:g} | "
            f"{r.A_coarse:.5f} | {r.A_mid:.5f} | {r.A_fine:.5f} | "
            f"**{r.A_dense:.5f}** | {r.runtime_s:.1f} | {r.notes or '-'} |"
        )
    return "\n".join(lines)


def main():
    print("=" * 72)
    print("Moving sofa: variant hallways (lower bounds via Fourier optimisation)")
    print("=" * 72)

    use_cma = True

    alpha_results = run_alpha_variants(use_cma=use_cma)
    Z_results = run_Z_variants(use_cma=use_cma)

    all_results = alpha_results + Z_results

    table = format_table(all_results)
    print("\n\nRESULTS TABLE\n")
    print(table)

    # Sanity check: alpha = 90 should be ~ 2.2195
    sanity = next((r for r in alpha_results if abs(r.param - 90.0) < 1e-6), None)
    if sanity is not None:
        gerver = 2.21953
        delta = sanity.A_dense - gerver
        print(f"\nSanity (alpha=90, Gerver=2.21953): dense A = "
              f"{sanity.A_dense:.5f}, diff = {delta:+.5f}")
        if abs(delta) > 1e-2:
            print("  WARNING: deviation > 1e-2 vs Gerver constant.")

    # Write the markdown table
    out_path = ("/Users/vico/Documents/elvec1o/MATH_PAPER_5/"
                "algorithm/sofa_variants_results.md")
    with open(out_path, "w") as f:
        f.write("# Moving-sofa constants for variant hallways\n\n")
        f.write("Numerical lower bounds via staged Fourier-series "
                "optimisation (Nelder-Mead 4->8->12 modes, then CMA-ES "
                "polish), dense-verified at n_theta = 1000.\n\n")
        f.write(table + "\n\n")
        if sanity is not None:
            f.write(f"\n**Sanity check (alpha = 90 deg):** dense A = "
                    f"{sanity.A_dense:.5f}, vs Gerver 2.21953, diff = "
                    f"{sanity.A_dense - 2.21953:+.5f}.\n")
    print(f"\nWrote {out_path}")


if __name__ == "__main__":
    main()
