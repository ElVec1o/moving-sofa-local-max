"""ambi_excess.py — how fast the flux excess turns on at the (RC) boundary.

THE QUESTION, AS I FIRST FRAMED IT, AND WHY THAT FRAMING WAS WRONG.

Write A := |C2| - 2|N| for the true area of the maximal sofa with cap data H, so that
A = Q + 2E with E = V - |N| >= 0 the flux excess and E(Sigma) = 0.  It looked as though
everything turned on whether d^2 E(Sigma) = 0, since then d^2 A(Sigma) = d^2 Q(Sigma) and
the TRUE functional would be sharply concave at Sigma.

It does, and the answer needs no measurement.  (RC) implies all three injectivity
conditions, hence V = |N|, hence E = 0 exactly; and (RC) holds on a C^2-neighbourhood of
Sigma.  So E vanishes IDENTICALLY near Sigma and d^2 E(Sigma) = 0 trivially.  The pivot is
TRUE and VACUOUS: it holds exactly on the domain D where the theorem already holds, and
buys no widening at all.

E is not a power of eps.  It is ZERO up to a threshold eps_c -- the eps at which the
perturbation first pushes max(H+H'') past 1 -- and grows past it.  Along the bump at
c0 = 1.0, w = 0.45 that threshold is eps_c = 0.006475, so an earlier sweep over
eps in [0.0141, 0.08] sampled only 2x to 12x past it: the far field, which says nothing
about the onset and produced a spurious "local exponent" drifting 3.14, 3.42, 3.81, 4.35
precisely because it was fitting a power of eps to a function of eps - eps_c.

THE QUESTION THAT ACTUALLY MATTERS is the ONSET exponent p in E ~ (eps - eps_c)^p.  If
p >= 2 then A = Q + 2E still has a non-positive second variation across the (RC) boundary
and D can be widened past (RC); if p < 2 the excess turns on too fast and (RC) is the true
limit.  This file measures p against eps_c, not against 0.

TWO MEASUREMENT TRAPS, both of which nearly became findings.

  (a) The gauge, not a tool bug.  A bump at c0 = 1.4, w = 0.35 gave a clean constant
      E/eps^2 = 4.010e4.  It is not a competitor.  sigma = (F-1) tan t + G-1 is integrated
      to t = pi/2 and stays finite only because F(pi/2) = H(pi/2) = 1 makes F-1 vanish
      there -- that is the GAUGE.  A bump with bump(pi/2) != 0 breaks it, sigma genuinely
      diverges, V is infinite, and the eps^2 scaling was sigma^2 ~ eps^2 tan^2 t sampled at
      fixed quadrature nodes.  This file ASSERTS eta(0) = eta(pi/2) = 0 before measuring.

  (b) The noise floor is |N|, not V.  V is a one-dimensional integral of an analytic
      integrand and is converged: 14 digits agreement at 200, 400 and 800 Gauss-Legendre
      nodes per phase.  |N| carries a clean 1/n polygon bias --

          n        2000        4000        8000       16000
          E     3.976e-5    2.119e-5    1.192e-5    7.278e-6

      whose differences halve with ratios 2.003 and 1.997.  So the bias is C/n and
      Richardson removes it: E_inf = 2 E(2n) - E(n).  At eps = 0.02 both pairs give
      2.6e-6 against a raw 2.1e-5 -- the floor was eight times the signal.

Rule 8: the polygon oracle is superlinear in n (1.15 s, 3.20 s, 12.2 s at n = 1000, 2000,
4000), so the sweep runs several minutes.  Progress, ETA and an atomic JSON checkpoint are
written after every eps, and a re-run resumes from the checkpoint.

Rule 7: this is floating point.  EVIDENCE, not proof.

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

    print("\n  THE (RC) THRESHOLD.  (RC) implies V = |N| exactly (result 31), so E is")
    print("  IDENTICALLY ZERO while max(H+H'') <= 1.  E is therefore not a power of eps")
    print("  at all: it is zero up to a threshold eps_c and grows past it.  d^2 E(Sigma)")
    print("  = 0 follows with no measurement, and is VACUOUS -- it holds exactly on the")
    print("  domain where the theorem already holds.  What matters is the ONSET exponent")
    print("  p in E ~ (eps - eps_c)^p: p >= 2 means A = Q + 2E stays C^2 with vanishing")
    print("  second derivative at the boundary, so D can be widened past (RC).\n", flush=True)
    from ambi_curvature import HpH2
    from ambi_hessian import PI
    th = np.linspace(1e-4, PI - 1e-4, 900)
    EPSC = {}
    for c0, w in DIRS:
        if not gauge_ok(c0, w):
            continue
        lo, hi = 0.0, 0.2
        for _ in range(45):
            m = (lo + hi)/2
            if HpH2(th, eps=m, c0=c0, w=w).max() <= 1.0: lo = m
            else: hi = m
        EPSC[(c0, w)] = lo
        print(f"    ({c0},{w}):  eps_c = {lo:.6f}   "
              f"(E = 0 proved below this)", flush=True)

    print("\n  RICHARDSON IN 1/n.  bias is C/n, so E_inf = 2 E(2n) - E(n).\n", flush=True)
    for c0, w in DIRS:
        if not gauge_ok(c0, w):
            continue
        print(f"  direction: bump at c0 = {c0}, half-width {w}   (gauge respected)")
        print(f"    {'eps':>8} {'E(2000)':>11} {'E(4000)':>11} {'E(8000)':>11} "
              f"{'E_inf':>11} {'eps-eps_c':>11} {'local p':>11} {'corr/E':>8}")
        ec = EPSC[(c0, w)]
        prev = None
        for e in EPS:
            k = f"{c0},{w},{e}"
            if k not in data:
                continue
            r = data[k]
            E = {n: r[str(n)][1] - r[str(n)][0] for n in NS}
            lo = 2*E[4000] - E[2000]
            hi = 2*E[8000] - E[4000]
            slope = ""
            if prev and hi > 0 and prev[1] > 0:
                slope = f"{math.log(prev[1]/hi)/math.log((prev[0]-ec)/(e-ec)):11.3f}"
            corr = E[8000] - hi           # the 1/n bias subtracted at n = 8000
            ratio = corr/hi if hi > 0 else float("inf")
            flag = "ok" if ratio < 1.0 else ("marginal" if ratio < 3.0 else "UNRELIABLE")
            print(f"    {e:8.4f} {E[2000]:11.3e} {E[4000]:11.3e} {E[8000]:11.3e} "
                  f"{hi:11.3e} {e-ec:11.4f} {slope:>11} {ratio:8.2f}  {flag}")
            prev = (e, hi)
        print()
    print("  corr/E is the 1/n bias SUBTRACTED at n = 8000 divided by what survives.")
    print("  Above 1 the extrapolation is removing more than it keeps, and the row is")
    print("  not evidence about p.  Read only the 'ok' rows.")
    print()
    print("  READING.  p >= 2 would mean A = Q + 2E keeps a non-positive second variation")
    print("  across the (RC) boundary, so D could be widened past it; p < 2 means the")
    print("  excess turns on too fast and (RC) is the true limit.  This is floating")
    print("  point, hence EVIDENCE at best (Rule 7).")


if __name__ == "__main__":
    main()
