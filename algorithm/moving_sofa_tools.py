"""
moving_sofa_tools.py
====================

A small library for computational moving-sofa problems on the
unit-width L-hallway.

ALGORITHMIC IDEA

At each rotation angle theta in [0, pi/2], the rotated polygon
R(theta) P must fit, by translation, inside the L-hallway

    H = {(x, y) : x <= 0,  0 <= y <= 1}
      union
        {(x, y) : y <= 0,  0 <= x <= 1}.

There are three structurally different feasibility cases:

  (A) The rotated polygon fits entirely inside the horizontal
      corridor.  Feasible iff   max(y_rot) - min(y_rot) <= 1.
      The translation puts the polygon deep in x < 0.

  (B) The rotated polygon fits entirely inside the vertical
      corridor.  Feasible iff   max(x_rot) - min(x_rot) <= 1.
      The translation puts the polygon deep in y < 0.

  (C) The rotated polygon STRADDLES the inner corner:  some
      vertices go in the horizontal corridor (y >= 0), others
      in the vertical corridor (x >= 0), with no vertex in the
      forbidden "outer corner" quadrant (x > 0 and y > 0).

      For a CONVEX polygon, the boundary partitions cleanly into
      one CCW arc that goes in horiz and the complementary arc
      in vert;  the boundary cuts the line y = -tan(beta) x for
      some beta in (-pi/2, 0), and the feasibility is determined
      by checking each candidate "split vertex" along the
      polygon CCW boundary.

We test (A), (B), and (C) analytically (no grid search).  Result:
no false negatives, fast, deterministic.

CONTRIBUTION

I do not know a clean Python implementation of the straddle case
for general convex polygons published as a public library.
The L-hallway non-convexity is the source of the difficulty;
the analysis above reduces it to a finite-case check over
candidate boundary splits.

Run with:  python3 moving_sofa_tools.py
"""

from __future__ import annotations

import math
from typing import Optional, Tuple

import numpy as np


# ---------------------------------------------------------------------
#  Polygon basics
# ---------------------------------------------------------------------

Polygon = np.ndarray  # (N, 2) CCW


def polygon_area(P: Polygon) -> float:
    x = P[:, 0]; y = P[:, 1]
    return 0.5 * abs(np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y))


def rotate(P: Polygon, theta: float) -> Polygon:
    c, s = math.cos(theta), math.sin(theta)
    R = np.array([[c, -s], [s, c]])
    return P @ R.T


def translate(P: Polygon, dx: float, dy: float) -> Polygon:
    out = P.copy(); out[:, 0] += dx; out[:, 1] += dy
    return out


def unit_disk(n: int = 64, r: float = 1.0) -> Polygon:
    t = np.linspace(0, 2 * math.pi, n, endpoint=False)
    return r * np.column_stack([np.cos(t), np.sin(t)])


def unit_square(side: float = 1.0) -> Polygon:
    s = 0.5 * side
    return np.array([[-s, -s], [s, -s], [s, s], [-s, s]])


def rectangle(width: float, height: float) -> Polygon:
    w, h = 0.5 * width, 0.5 * height
    return np.array([[-w, -h], [w, -h], [w, h], [-w, h]])


# ---------------------------------------------------------------------
#  Analytic feasibility test for one theta
# ---------------------------------------------------------------------

def _fits_horizontal_corridor(Pr: Polygon, eps: float = 1e-9) -> bool:
    """Case (A): fits in {x <= 0, 0 <= y <= 1}.
    Need max(y) - min(y) <= 1 (and we can take dx as negative as we like).
    """
    return (Pr[:, 1].max() - Pr[:, 1].min()) <= 1.0 + eps


def _fits_vertical_corridor(Pr: Polygon, eps: float = 1e-9) -> bool:
    """Case (B): fits in {y <= 0, 0 <= x <= 1}."""
    return (Pr[:, 0].max() - Pr[:, 0].min()) <= 1.0 + eps


def _fits_straddle(Pr: Polygon, eps: float = 1e-9) -> bool:
    """Case (C): straddle the inner corner.

    For each candidate CCW split (i, j) of the convex polygon
    boundary into two arcs --- one going to the horizontal
    corridor (y >= 0), one to the vertical corridor (x >= 0) ---
    test whether there exists (dx, dy) so that:
      * the horiz arc satisfies   x_arc <= 0,  0 <= y_arc <= 1
      * the vert  arc satisfies   y_arc <= 0,  0 <= x_arc <= 1

    For a convex polygon with N vertices there are N*(N-1)/2
    splits in the worst case, but only O(N) of them produce
    contiguous arcs;  we just try all O(N^2) and short-circuit.
    """
    N = len(Pr)
    for i in range(N):
        for j in range(i + 1, N + i):
            # arc1: vertices i, i+1, ..., j (CCW), takes the horiz corridor
            # arc2: vertices j, j+1, ..., i (CCW), takes the vert corridor
            arc1_idx = [(i + k) % N for k in range(j - i + 1)]
            arc2_idx = [(j + k) % N for k in range(N - (j - i) + 1)]
            arc1 = Pr[arc1_idx]; arc2 = Pr[arc2_idx]
            # horiz arc: need 0 <= y+dy <= 1, x+dx <= 0
            #   => -arc1_y_min <= dy <= 1 - arc1_y_max
            #      dx <= -arc1_x_max
            # vert arc:  need 0 <= x+dx <= 1, y+dy <= 0
            #   => -arc2_x_min <= dx <= 1 - arc2_x_max
            #      dy <= -arc2_y_max
            ay_min, ay_max = arc1[:, 1].min(), arc1[:, 1].max()
            ax_max = arc1[:, 0].max()
            bx_min, bx_max = arc2[:, 0].min(), arc2[:, 0].max()
            by_max = arc2[:, 1].max()
            # dy in [-ay_min, 1 - ay_max] intersected with (-inf, -by_max]
            dy_lo = -ay_min
            dy_hi = min(1.0 - ay_max, -by_max)
            if dy_lo > dy_hi + eps:
                continue
            # dx in (-inf, -ax_max] intersected with [-bx_min, 1 - bx_max]
            dx_lo = -bx_min
            dx_hi = min(-ax_max, 1.0 - bx_max)
            if dx_lo > dx_hi + eps:
                continue
            return True
    return False


def fits_in_hallway(P: Polygon, theta: float, eps: float = 1e-9) -> bool:
    """Does there exist a translation (dx, dy) such that
    R(theta) P + (dx, dy)  is contained in the L-hallway H ?
    """
    Pr = rotate(P, theta)
    if _fits_horizontal_corridor(Pr, eps):
        return True
    if _fits_vertical_corridor(Pr, eps):
        return True
    return _fits_straddle(Pr, eps)


# ---------------------------------------------------------------------
#  Continuous-motion test
# ---------------------------------------------------------------------

def navigates_hallway(
    P: Polygon,
    n_theta: int = 31,
    verbose: bool = False,
) -> bool:
    """Discretised feasibility test for the navigation problem.

    Returns True iff at every sampled theta in [0, pi/2] there is a
    feasible translation of R(theta) P.  This is a NECESSARY
    condition;  path-connectivity of feasible translations is not
    checked (so this can be a false positive, but never a false
    negative for the sampled grid).
    """
    thetas = np.linspace(0.0, math.pi / 2, n_theta)
    for theta in thetas:
        if not fits_in_hallway(P, theta):
            if verbose:
                print(f"  infeasible at theta = {theta:.4f} rad "
                      f"({math.degrees(theta):.2f} deg)")
            return False
    return True


def max_scale(
    P: Polygon,
    n_theta: int = 31,
    s_lo: float = 0.01,
    s_hi: float = 5.0,
    tol: float = 1e-3,
    verbose: bool = False,
) -> float:
    """Binary-search the largest scale s such that  s * P  navigates H."""
    lo, hi = s_lo, s_hi
    # First confirm s_lo navigates and s_hi does not, otherwise the search is meaningless
    if not navigates_hallway(s_lo * P, n_theta=n_theta):
        return 0.0
    if navigates_hallway(s_hi * P, n_theta=n_theta):
        if verbose:
            print(f"  s_hi = {s_hi} still navigates; increase s_hi")
        return s_hi
    while hi - lo > tol:
        mid = 0.5 * (lo + hi)
        ok = navigates_hallway(mid * P, n_theta=n_theta)
        if ok:
            lo = mid
        else:
            hi = mid
        if verbose:
            print(f"  s in [{lo:.5f}, {hi:.5f}]  (width {hi-lo:.5f})")
    return lo


# ---------------------------------------------------------------------
#  Self-tests
# ---------------------------------------------------------------------

def main() -> None:
    print("=" * 60)
    print("moving_sofa_tools.py self-tests")
    print("=" * 60)

    print("\n[1] Disk:  expected max-radius = 0.5")
    s = max_scale(unit_disk(64), n_theta=31, tol=1e-4)
    print(f"    found:   s = {s:.4f}     err = {abs(s - 0.5):.4f}")

    print("\n[2] Square 0.7 x 0.7:  expected navigable")
    sq = unit_square(0.7)
    print(f"    navigable? {navigates_hallway(sq, n_theta=31)}")

    print("\n[3] Square 1.2 x 1.2:  expected NOT navigable")
    sq = unit_square(1.2)
    print(f"    navigable? {navigates_hallway(sq, n_theta=31)}")

    print("\n[4] Rectangle 2 x 0.5:  expected navigable (thin sofa)")
    rt = rectangle(2.0, 0.5)
    print(f"    navigable? {navigates_hallway(rt, n_theta=31)}")
    print(f"    area:      {polygon_area(rt):.4f}")

    print("\n[5] Rectangle 3 x 0.9:  expected navigable (longer, tighter)")
    rt = rectangle(3.0, 0.9)
    print(f"    navigable? {navigates_hallway(rt, n_theta=31)}")
    print(f"    area:      {polygon_area(rt):.4f}")

    print("\n[6] Rectangle 1 x 1:  square at the corner, expect navigable")
    rt = rectangle(1.0, 1.0)
    print(f"    navigable? {navigates_hallway(rt, n_theta=31)}")

    print("\n[7] Largest scale of a 1 x 0.5 rectangle:")
    s = max_scale(rectangle(1.0, 0.5), n_theta=31, tol=1e-4)
    print(f"    s = {s:.4f}     area at max scale "
          f"= {polygon_area(rectangle(1.0, 0.5)) * s**2:.4f}")

    print("\n[8] Largest scale of a regular hexagon (in-radius 1):")
    n = 6
    t = np.linspace(0, 2 * math.pi, n, endpoint=False) + math.pi / 6
    hex6 = np.column_stack([np.cos(t), np.sin(t)])
    s = max_scale(hex6, n_theta=31, tol=1e-4)
    print(f"    s = {s:.4f}     "
          f"navigable hex with circumradius {s:.4f}")


if __name__ == "__main__":
    main()
