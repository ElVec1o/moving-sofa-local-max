"""
test_moving_sofa.py
===================

Honest tests of moving_sofa_tools.py with correct expected values
derived from elementary geometry.
"""

from __future__ import annotations

import math
import sys
import time

import numpy as np

from moving_sofa_tools import (
    Polygon, polygon_area, rotate,
    unit_disk, unit_square, rectangle,
    fits_in_hallway, navigates_hallway, max_scale,
)


# ---------------------------------------------------------------------
#  Test helpers
# ---------------------------------------------------------------------

class TestResult:
    def __init__(self):
        self.passed = 0
        self.failed = 0
        self.tests = []

    def record(self, name: str, ok: bool, detail: str = ""):
        self.tests.append((name, ok, detail))
        if ok: self.passed += 1
        else:  self.failed += 1
        marker = " OK " if ok else "FAIL"
        print(f"  [{marker}] {name}    {detail}")

    def summarize(self):
        n = len(self.tests)
        print()
        print(f"{self.passed} / {n} tests passed", end=" ")
        if self.failed == 0:
            print("(all PASS)")
        else:
            print(f"({self.failed} FAILED)")


# ---------------------------------------------------------------------
#  Tests with correct expected values
# ---------------------------------------------------------------------

def main():
    t0 = time.time()
    R = TestResult()

    # Reference values derived from elementary geometry:
    #
    # 1. Disk radius r navigates the unit-width L iff r <= 1/2.
    #    A disk fits in either corridor iff its diameter <= 1.
    #
    # 2. A square of side s navigates iff s <= sqrt(2)/2 = 0.7071...
    #    (At s = sqrt(2)/2 it is exactly inscribed in the corridor
    #     when rotated 45 degrees;  larger and it cannot turn.)
    #
    # 3. A rectangle a x b navigates iff there exists a continuous
    #    rotation through 90 degrees with the rotated rectangle
    #    fitting in the L at every angle.  For a thin rectangle
    #    (b << a), the longest sustainable length is bounded by
    #    the diagonal sqrt(a^2 + b^2) <= sqrt(2), i.e. a^2 + b^2 <= 2.
    #    Beyond that the corner blocks the rotation.

    print("=" * 70)
    print("Reference cases (analytic ground truth)")
    print("=" * 70)

    # ----- Disk: max radius = 0.5 -----
    print("\n[D]  Disk:  max-scale-radius should be 0.5")
    s = max_scale(unit_disk(128), n_theta=31, tol=1e-4)
    R.record("Disk gives s = 0.5",
             abs(s - 0.5) < 5e-4,
             f"s = {s:.6f},  err = {abs(s-0.5):.2e}")

    # ----- Squares -----
    print("\n[S]  Squares:  side s navigates iff s <= sqrt(2)/2 ~ 0.7071")
    half_root2 = math.sqrt(2) / 2  # 0.7071
    for side_val, expected in [
        (0.50, True),
        (0.65, True),
        (half_root2 - 0.01, True),
        (half_root2 + 0.01, False),
        (0.80, False),
        (1.00, False),
        (1.20, False),
    ]:
        got = navigates_hallway(unit_square(side_val), n_theta=31)
        ok = got == expected
        R.record(f"Square side {side_val:.3f}: navigable={got}",
                 ok, f"(expected {expected})")
    # Max square-side scale: should be ~0.7071
    print("\n[S]  Max scale of unit square:")
    s = max_scale(unit_square(1.0), n_theta=31, tol=1e-4)
    R.record("max_scale(square) ~= 0.7071",
             abs(s - half_root2) < 2e-3,
             f"s = {s:.6f},  err = {abs(s - half_root2):.2e}")

    # ----- Rectangles: a x b navigates iff at every theta in [0, pi/2]
    #       the rotated rectangle fits.  For pure rectangles (no clever
    #       straddle works) the worst theta is pi/4 where the bounding
    #       box has both side lengths equal to (a+b)/sqrt(2).  Therefore
    #       a rectangle a x b navigates iff  a + b <= sqrt(2).
    sqrt2 = math.sqrt(2)
    print(f"\n[R]  Rectangles:  a x b navigates iff a + b <= sqrt(2) = {sqrt2:.4f}")
    for a, b in [
        (0.5, 0.5),   # a+b = 1.0
        (1.0, 0.4),   # a+b = 1.4
        (0.9, 0.5),   # a+b = 1.4
        (1.0, 0.41),  # a+b = 1.41 ~ sqrt(2)
        (1.0, 0.5),   # a+b = 1.5  > sqrt(2)
        (1.2, 0.5),   # a+b = 1.7
        (1.3, 0.5),   # a+b = 1.8
        (1.5, 0.5),   # a+b = 2.0
        (0.9, 0.9),   # a+b = 1.8
        (1.5, 0.1),   # a+b = 1.6
        (2.0, 0.5),   # a+b = 2.5
    ]:
        expected = (a + b) <= sqrt2 + 1e-6
        got = navigates_hallway(rectangle(a, b), n_theta=31)
        ok = got == expected
        R.record(f"Rect {a:.2f}x{b:.2f}: navigable={got}",
                 ok, f"(expected {expected}; a+b = {a+b:.3f})")

    # ----- Special shape: half-disk + thin slab (a "sofa" candidate) -----
    print("\n[H]  Hammersley-like candidate (half-disk + slab):")
    # Build a polygon: bottom half of a disk of radius 0.5, plus
    # a thin slab below (a half-disk gives area pi*0.5^2/2 = pi/8 ~ 0.39)
    n = 32
    t = np.linspace(0, math.pi, n)
    half = np.column_stack([0.5 * np.cos(t), 0.5 * np.sin(t)])
    # close the bottom
    half = np.vstack([half, [[-0.5, 0], [0.5, 0]]])
    # area should be pi/8 ~ 0.3927
    A = polygon_area(half)
    R.record(f"half-disk area",
             abs(A - math.pi / 8) < 1e-2,
             f"A = {A:.4f}, expected pi/8 = {math.pi/8:.4f}")
    nav = navigates_hallway(half, n_theta=31)
    R.record(f"half-disk navigable", nav, f"got {nav}")

    # ----- Speed benchmark -----
    print("\n[B]  Speed benchmark (large polygon):")
    big = unit_disk(256)
    t1 = time.time()
    nav = navigates_hallway(0.49 * big, n_theta=31)
    elapsed = time.time() - t1
    R.record(f"disk(N=256, scale=0.49)  in  {elapsed*1000:.1f} ms",
             elapsed < 5.0,  # arbitrary 5-second budget
             f"navigable = {nav}")

    # ----- Print summary -----
    print()
    R.summarize()
    print(f"\nWall time: {(time.time() - t0):.2f} s")
    sys.exit(0 if R.failed == 0 else 1)


if __name__ == "__main__":
    main()
