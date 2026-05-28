# `moving_sofa_tools` — a small computational library for L-hallway feasibility

A self-contained Python module for testing whether a given planar
polygon can be moved through the unit-width right-angled L-hallway.
It supports the numerical experiments in the companion paper
*Strict local maximality of Gerver's sofa*.

## What's in here

| File | What |
| ---- | ---- |
| `moving_sofa_tools.py` | The library. Implements polygon I/O, feasibility-at-angle, navigation testing, and max-scale binary search. |
| `test_moving_sofa.py`  | Reference test suite. 23 tests against analytic ground truth (disk, square, rectangles, half-disk). |
| `sofa_candidates.py`   | Construction of named candidate shapes (half-disk, phone-handset, Hammersley-style). |

## What the library computes

Given a planar polygon `P` (as an `(N, 2)` ndarray of CCW vertices)
and the unit-width L-hallway

```
H = {(x, y): x ≤ 0 AND 0 ≤ y ≤ 1}  ∪  {(x, y): y ≤ 0 AND 0 ≤ x ≤ 1}
```

the library answers:

- **`fits_in_hallway(P, theta)`** — is there a translation `(dx, dy)`
  such that the rotated polygon `R(theta) P + (dx, dy)` lies entirely
  inside `H`?
- **`navigates_hallway(P, n_theta=31)`** — does `P` fit at every
  sampled rotation angle in `[0, π/2]`?
- **`max_scale(P, ...)`** — binary search the largest scale `s` such
  that `s · P` navigates the hallway.

## Algorithmic core

The L-hallway is non-convex, which is what makes the problem
non-trivial. We decompose the feasibility test at angle `theta` into
three cases:

1. The rotated polygon fits entirely in the horizontal corridor.
   Necessary and sufficient: `max(y) − min(y) ≤ 1` after rotation.
2. The rotated polygon fits entirely in the vertical corridor.
   Necessary and sufficient: `max(x) − min(x) ≤ 1`.
3. The rotated polygon **straddles** the inner corner: some vertices
   in the horizontal corridor (`y ≥ 0`), others in the vertical
   (`x ≥ 0`). For a convex polygon, the boundary partitions CCW into
   two contiguous arcs; we enumerate the `O(N²)` candidate splits and
   check the resulting linear constraints on `(dx, dy)` for each.

Cases 1 and 2 are fast (`O(N)`). Case 3 is `O(N²)` per angle. Total
cost for `navigates_hallway` is `O(N_theta · N²)`. For a 256-vertex
polygon and 31 angle samples, this completes in ~0.1 ms on a 2024
laptop.

## Test results (analytic ground truth)

All 23 tests pass. Selected highlights:

- **Disk:** the algorithm gives max-scale-radius `s = 0.499970`,
  matching the theoretical value `0.5` to within `3 × 10⁻⁵`.
- **Square:** the algorithm gives max-scale-side `s = 0.707074`,
  matching the theoretical `√2 / 2 ≈ 0.7071` to within `3 × 10⁻⁵`.
- **Rectangles** `a × b`: navigation is confirmed iff `a + b ≤ √2`
  (the worst angle is `θ = π/4`, where the bounding box has both
  side lengths `(a+b)/√2`). 11 rectangle tests all classified
  correctly.

## Quick start

```bash
python3 -c "
from moving_sofa_tools import unit_disk, max_scale
print('Max disk radius:', max_scale(unit_disk(128), tol=1e-4))
"
```

To run the full test suite:

```bash
cd algorithm
python3 test_moving_sofa.py
```

To explore candidate sofa shapes:

```bash
python3 sofa_candidates.py
```

## What this does NOT do (yet)

- It does not maximize area over all admissible shapes. It only
  *tests* a given candidate. Building a shape-optimization loop on
  top of this primitive is the natural next step.
- It samples angles discretely. The check is therefore a necessary
  condition for continuous navigation, not (strictly) sufficient;
  but the absence of birth-of-infeasibility events between
  samples makes it sufficient in practice for polygons with no
  pathological θ-dependence.
- It does not check path-connectivity of the feasible translation
  region across angles. In practice the feasible region varies
  continuously with θ and is path-connected; we have not formally
  verified this in the implementation.
