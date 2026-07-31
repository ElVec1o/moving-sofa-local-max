"""ambi_excess.py — the order of vanishing of the flux excess E = V - |N| at Sigma.

THE QUESTION.  Write A := |C2| - 2|N| for the true area of the maximal sofa with cap data
H, so that A = Q + 2E with E = V - |N| >= 0 the flux excess and E(Sigma) = 0.  Sigma
minimises E, so d^2 E(Sigma) >= 0.  If it is ZERO then

    d^2 A(Sigma) = d^2 Q(Sigma) <= -0.73 ||eta||^2 ,

so the TRUE area functional is strictly concave at Sigma with the sharp constant of
Theorem "The sharp constant", and (RC) would be needed only for the non-local statement.
That is the pivot for widening the domain D.

WHY THE EARLIER MEASUREMENT WAS INCONCLUSIVE, and it was not what I first thought.

  (a) The gauge, not a tool bug.  A first sweep found a direction (bump at c0 = 1.4 with
      half-width 0.35) giving a clean constant E/eps^2 = 4.010e4, which would have refuted
      the pivot.  It is not a competitor at all.  sigma = (F-1) tan t + G-1 is finite at
      t = pi/2 only because F(pi/2) = H(pi/2) = 1 makes F-1 vanish there, and that is
      exactly the GAUGE.  A bump with bump(pi/2) != 0 breaks H(pi/2) = 1, sigma diverges
      and V is infinite; the eps^2 scaling was sigma^2 ~ eps^2 tan^2 t, the divergence
      being sampled at fixed quadrature nodes.  Admissible directions must satisfy
      eta(0) = eta(pi/2) = 0, and this file asserts that before measuring.

  (b) The noise floor is |N|, not V.  V is a one-dimensional integral of an analytic
      integrand and is converged at 200 Gauss-Legendre nodes per phase: it agrees to 14
      digits at 400 and 800.  |N| comes from the polygon oracle and carries a
      discretisation bias of order 1/n, which at eps = 0.02 is 40 times the excess itself:

          n        2000        4000        8000       16000
          E     3.976e-5    2.119e-5    1.192e-5    7.278e-6

      The differences halve cleanly (ratios 2.003, 1.997), so the bias is C/n with C
      independent of n, and Richardson removes it:  E_inf = 2 E(2n) - E(n).  At eps = 0.02
      both pairs give E_inf = 2.6e-6, against a raw reading of 2.1e-5.  Differencing two
      numbers of size 0.187 to extract 2.6e-6 is what the floor was.

WHAT THIS SCRIPT DOES.  Sweeps eps geometrically, measures E at three polygon resolutions,
Richardson-extrapolates in 1/n, and reports E_inf/eps^2 and E_inf/eps^3.  A constant
E_inf/eps^2 means d^2 E != 0 and the pivot fails; E_inf/eps^2 -> 0 with E_inf/eps^3
constant means d^2 E = 0 and the pivot holds.

Rule 8: the polygon oracle is superlinear in n (1.15 s, 3.20 s, 12.2 s at n = 1000, 2000,
4000), so the full sweep runs several minutes.  Progress, ETA and an atomic JSON
checkpoint are written after every eps, and a re-run resumes from the checkpoint.

Rule 7: this is floating point and is EVIDENCE, not proof.  The conclusion is labelled
accordingly.

Usage: python3 ambi_excess.py [outfile.json]
"""
from __future__ import annotations
import json, math, os, sys, time

import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from ambi_domination import bump, measure_N, V_of
from ambi_hessian import PI2

DIRS = [(1.0, 0.45), (0.6, 0.30)]
EPS = [0.08, 0.0566, 0.04, 0.0283, 0.02, 0.0141]
NS = [2000, 4000, 8000]


def gauge_ok(c0, w):
    """eta(0) = eta(pi/2) = 0 -- the unit-corridor normalisation."""
    b0 = bump(np.array([0.0]), c0, w)[0][0]
    bh = bump(np.array([PI2]), c0, w)[0][0]
    return abs(b0) < 1e-15 and abs(bh) < 1e-15


def save(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(data, f, indent=1)
    os.replace(tmp, path)                       # atomic


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(THIS, "excess_scan.json")
    data = {}
    if os.path.exists(out):
        with open(out) as f:
            data = json.load(f)
        print(f"resuming from {out}: {len(data)} cells already done", flush=True)

    for c0, w in DIRS:
        if not gauge_ok(c0, w):
            print(f"  direction ({c0},{w}) VIOLATES the gauge -- skipped", flush=True)
            continue

    todo = [(c0, w, e) for c0, w in DIRS if gauge_ok(c0, w) for e in EPS
            if f"{c0},{w},{e}" not in data]
    unit = sum(n**1.7 for n in NS)
    print(f"THE ORDER OF VANISHING OF THE FLUX EXCESS   ({len(todo)} cells to run)\n",
          flush=True)
    t0 = time.time(); done = 0
    for c0, w, e in todo:
        ts = time.time()
        row = {}
        for n in NS:
            N, _ = measure_N(e, c0, w, n)
            row[str(n)] = [N, V_of(e, c0, w, 200)]
        data[f"{c0},{w},{e}"] = row
        save(out, data)
        done += 1
        el = time.time() - t0
        eta = el/done*(len(todo) - done)
        print(f"  ({c0},{w}) eps={e:<7} done in {time.time()-ts:5.1f}s   "
              f"elapsed {el/60:5.2f}m   ETA {eta/60:5.2f}m", flush=True)

    print("\n  RICHARDSON IN 1/n.  bias is C/n, so E_inf = 2 E(2n) - E(n).\n", flush=True)
    for c0, w in DIRS:
        if not gauge_ok(c0, w):
            continue
        print(f"  direction: bump at c0 = {c0}, half-width {w}   (gauge respected)")
        print(f"    {'eps':>8} {'E(2000)':>11} {'E(4000)':>11} {'E(8000)':>11} "
              f"{'E_inf':>11} {'E_inf/e^2':>11} {'E_inf/e^3':>11}")
        for e in EPS:
            k = f"{c0},{w},{e}"
            if k not in data:
                continue
            r = data[k]
            E = {n: r[str(n)][1] - r[str(n)][0] for n in NS}
            lo = 2*E[4000] - E[2000]
            hi = 2*E[8000] - E[4000]
            print(f"    {e:8.4f} {E[2000]:11.3e} {E[4000]:11.3e} {E[8000]:11.3e} "
                  f"{hi:11.3e} {hi/e**2:11.3e} {hi/e**3:11.3e}"
                  + ("" if abs(hi - lo) < 0.5*abs(hi) + 1e-12 else "   (unstable)"))
        print()
    print("  READING.  E_inf/eps^2 tending to a nonzero constant => d^2 E != 0, the")
    print("  pivot FAILS.  E_inf/eps^2 -> 0 with E_inf/eps^3 settling => d^2 E = 0, the")
    print("  pivot HOLDS and the true functional is sharply concave at Sigma.")
    print("  Either way this is floating point: EVIDENCE, not proof (Rule 7).")


if __name__ == "__main__":
    main()
