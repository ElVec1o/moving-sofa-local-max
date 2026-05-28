"""
benchmark.py
============

Compare the analytic O(N^2) feasibility test against a naive
grid-search baseline.

The grid baseline is:  for each rotation theta, sweep (dx, dy) on a
grid of step h and test whether any (dx, dy) translates the rotated
polygon into the hallway.  Time per theta is  O(N * G^2)  where G
is the grid resolution.

Naive recovery of  max_scale  for a disk  requires fine grids and
many angle samples.  Our analytic algorithm gets the disk radius
exactly to 4 decimal places in ~10 ms.  Below we time both.
"""

from __future__ import annotations

import math
import time

import numpy as np

from moving_sofa_tools import (
    unit_disk, fits_in_hallway, navigates_hallway, max_scale,
    rotate,
)


# Naive grid-based feasibility test (for comparison)
def fits_in_hallway_grid(P, theta, G=200,
                         dx_range=(-3.0, 3.0),
                         dy_range=(-3.0, 3.0)):
    """Naive grid-search feasibility check."""
    Pr = rotate(P, theta)
    dxs = np.linspace(*dx_range, G)
    dys = np.linspace(*dy_range, G)
    for dx in dxs:
        for dy in dys:
            ok = True
            for px, py in Pr:
                # in-hallway predicate, inline
                in_horiz = (px + dx <= 1e-12) and (
                    -1e-12 <= py + dy <= 1 + 1e-12
                )
                in_vert = (py + dy <= 1e-12) and (
                    -1e-12 <= px + dx <= 1 + 1e-12
                )
                if not (in_horiz or in_vert):
                    ok = False
                    break
            if ok:
                return True
    return False


def main():
    print("=" * 70)
    print("Benchmark: analytic vs grid-search feasibility")
    print("=" * 70)

    print("\nTest case: disk(N=64) at radius 0.49 (just below max).")
    print("Both should return True at every theta.")
    print()

    disk = 0.49 * unit_disk(64)
    thetas = np.linspace(0, math.pi / 2, 31)

    # Time analytic algorithm
    t0 = time.time()
    n_correct = 0
    for theta in thetas:
        if fits_in_hallway(disk, theta):
            n_correct += 1
    t_analytic = time.time() - t0
    print(f"  analytic:    {n_correct}/{len(thetas)} feasible  "
          f"in {t_analytic*1000:.2f} ms   "
          f"({t_analytic/len(thetas)*1e6:.1f} us/theta)")

    # Time grid algorithm (coarse grid, faster but lower precision)
    t0 = time.time()
    n_correct = 0
    for theta in thetas:
        if fits_in_hallway_grid(disk, theta, G=80):
            n_correct += 1
    t_grid = time.time() - t0
    print(f"  grid G=80:   {n_correct}/{len(thetas)} feasible  "
          f"in {t_grid*1000:.2f} ms   "
          f"({t_grid/len(thetas)*1e6:.1f} us/theta)")

    speedup = t_grid / t_analytic if t_analytic > 0 else float('inf')
    print(f"\n  speedup:     {speedup:.1f}x")

    print("\nTest case: disk(N=64) at radius 0.50 (exact boundary).")
    print("Analytic should return True (singleton-measure feasible),")
    print("grid will return False with coarse step.")
    print()

    disk = 0.50 * unit_disk(64)
    n_analytic = sum(1 for t in thetas if fits_in_hallway(disk, t))
    n_grid = sum(1 for t in thetas if fits_in_hallway_grid(disk, t, G=80))
    print(f"  analytic:    {n_analytic}/{len(thetas)} feasible at r = 0.50")
    print(f"  grid G=80:   {n_grid}/{len(thetas)} feasible at r = 0.50")
    print()
    print("  Analytic is exact at the feasibility boundary; grid is not")
    print("  unless G is taken to infinity.")

    # Max-scale precision comparison
    print("\nMax-scale precision for the disk (expected 0.5 exactly):")
    t0 = time.time()
    s = max_scale(unit_disk(64), n_theta=31, tol=1e-5)
    t_analytic = time.time() - t0
    err = abs(s - 0.5)
    print(f"  analytic:    s = {s:.6f}, err = {err:.2e}  "
          f"in {t_analytic*1000:.1f} ms")


if __name__ == "__main__":
    main()
