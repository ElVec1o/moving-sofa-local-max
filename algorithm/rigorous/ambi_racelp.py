"""ambi_racelp.py — the sharp ordering threshold, as a pair of linear programs.

WHAT THIS COMPUTES.  Ordering is a race (prop:race): alpha_1 starts at -1/2 and must reach
0 before alpha_2 leaves the positives.  cor:race2 certifies the race at alpha_2(0) >= 0.899266
by a chain of inequalities.  This file stops bounding and solves instead.

With Z = alpha_1 + i alpha_2, the exact arm system of prop:armsys is
Z' + iZ = (1 - r(t)) - i(1 - r(t+pi/2)), so with u = 1 - r(t), v = 1 - r(t+pi/2) in [0,1],

  alpha_1(t) = -(1/2)cos t + c sin t + int_0^t [ u cos(t-s) - v sin(t-s) ] ds
  alpha_2(t) =  c cos t + (1/2)sin t - int_0^t [ u sin(t-s) + v cos(t-s) ] ds

exactly, with c = alpha_2(0), and the two forced moment conditions become

  int_0^(pi/2) u cos = 1/2 ,        int_0^(pi/2) v sin = 1/2 .

Each of the four integrals is extremised by a linear program over 0 <= x <= 1 with one
linear constraint, whose solution is bang-bang against a single multiplier found by
bisection.  Requiring alpha_2 > 0 up to some T and alpha_1(T) >= 0, both in the worst case,
gives the sufficient threshold c_LP.

WHAT IS AND IS NOT PROVED.  The reduction to the linear programs is exact.  The VALUE is
not: it comes from a discretised LP.  It converges to about 0.7484, and Sigma's
alpha_2(0) = 0.750575 clears it by 0.0017, but 0.0017 on floating point is not a proof.
Refining the grid 16-fold moves the threshold by at most 0.0006 and never flips the sign of
the margin, which is why the margin is reported at all; making it rigorous needs the LP in
exact or interval arithmetic, as the barrier certificate needed rational arithmetic.
Rule 7: c_LP is HEURISTIC, the reduction is PROVED, and 0.899266 is the certified value.

TWO WRONG TURNS RECORDED HERE, because both looked right.
  1. A guessed worst-case control (r_L = 1 on [0,pi/6] then 0; r_R = 0 on [0,pi/3] then 1,
     the switch times forced exactly by the constraints) gave 0.548191.  An adversarial
     search beat it at 0.621.  The controls trade off: slowing alpha_1 makes -alpha_1
     larger, which makes alpha_2 fall SLOWER, so separate bang-bang per arm is not optimal.
  2. A first LP that imposed only alpha_2(t) = 0 returned c* = 25.7, which is absurd.  It
     omitted the requirement alpha_1(t) < 0 at the failure time and divided by cos t as
     t -> pi/2.  The conceptual error underneath: alpha_2 reaching 0 is NOT failure.
     Sigma's alpha_2 reaches 0 at pi/2 - beta and Sigma is ordered, because alpha_1 is
     already nonnegative there.  Failure is alpha_2 = 0 WHILE alpha_1 < 0.

CONVERGENCE CHECK is part of the run: the threshold is recomputed on a refining grid and
the drift is printed.  A margin smaller than the drift would be reported as unresolved.

Usage: python3 ambi_racelp.py [ngrid]
"""
from __future__ import annotations
import sys
import numpy as np

P2 = np.pi / 2
SIGMA_C = 0.750575          # Sigma's alpha_2(0), from the closed forms
CERTIFIED = 0.899266        # cor:race2, the value this note actually certifies


def extremum(obj: np.ndarray, w: np.ndarray, target: float, sense: int,
             ds: float) -> float:
    """max (sense=+1) or min (sense=-1) of int obj*x over 0<=x<=1 with int x*w = target."""
    o = sense * obj

    def sol(lam: float):
        x = (o - lam * w > 0).astype(float)
        return x, float(np.trapezoid(x * w, dx=ds))

    lo, hi = -80.0, 80.0
    if sol(lo)[1] < target or sol(hi)[1] > target:
        return 0.0
    for _ in range(120):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if sol(m)[1] > target else (lo, m)
    x, _ = sol((lo + hi) / 2)
    return float(np.trapezoid(obj * x, dx=ds))


def threshold(n: int) -> float:
    s = np.linspace(0.0, P2, n)
    ds = s[1] - s[0]
    cs, sn = np.cos(s), np.sin(s)
    U2 = np.empty(n); V2 = np.empty(n); U1 = np.empty(n); V1 = np.empty(n)
    for i, t in enumerate(s):
        m = s <= t
        U2[i] = extremum(np.where(m, np.sin(t - s), 0.0), cs, 0.5, +1, ds)
        V2[i] = extremum(np.where(m, np.cos(t - s), 0.0), sn, 0.5, +1, ds)
        U1[i] = extremum(np.where(m, np.cos(t - s), 0.0), cs, 0.5, -1, ds)
        V1[i] = extremum(np.where(m, np.sin(t - s), 0.0), sn, 0.5, +1, ds)

    def ok(c: float) -> bool:
        a2 = c * cs + 0.5 * sn - U2 - V2          # worst-case lower bound on alpha_2
        a1 = -0.5 * cs + c * sn + U1 - V1         # worst-case lower bound on alpha_1
        alive = np.minimum.accumulate(np.where(a2 > 0, 1, 0))
        return bool(np.any((alive == 1) & (a1 >= 0)))

    lo, hi = 0.0, 3.0
    for _ in range(60):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if not ok(m) else (lo, m)
    return hi


def main() -> int:
    top = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
    print(__doc__.split("Usage")[0])
    grids = [g for g in (1000, 2000, 4000, 8000, 16000) if g <= top] or [top]
    print(f"  {'ngrid':>7} {'c_LP':>11} {'drift':>10}   Sigma margin")
    vals = []
    for g in grids:
        v = threshold(g)
        d = "" if not vals else f"{v - vals[-1]:+.6f}"
        vals.append(v)
        print(f"  {g:7d} {v:11.6f} {d:>10}   {SIGMA_C - v:+.6f}")
    drift = max(abs(vals[i + 1] - vals[i]) for i in range(len(vals) - 1)) if len(vals) > 1 else float("nan")
    margin = SIGMA_C - vals[-1]
    print(f"\n  c_LP -> {vals[-1]:.6f}, max drift {drift:.6f}, Sigma margin {margin:+.6f}")
    resolved = margin > 0 and margin > drift
    print(f"  margin {'exceeds' if resolved else 'does NOT exceed'} the drift, so the sign is "
          f"{'stable under refinement' if resolved else 'UNRESOLVED at this precision'}")
    print(f"  certified value (cor:race2, proved): {CERTIFIED}")
    print(f"  c_LP is HEURISTIC (rule 7).  Exact/interval arithmetic is what would settle it.")
    return 0 if vals[-1] < CERTIFIED else 1


if __name__ == "__main__":
    sys.exit(main())
