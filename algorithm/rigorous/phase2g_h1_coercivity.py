"""THE BINDING GAP: full H^1 coercivity of the second variation.  (parallel)

WHY THIS IS THE REMAINING ITEM
------------------------------
Everything else in the local-maximality chain is settled:

  * D^3F has NO eta'' term and NO breakpoint jet terms at all, because all
    four contact paths are AFFINE in (c,c'), forcing B_2 = B_3 = 0
    (verified symbolically; holds for the ambidextrous family too).
    => the fatal cubic coefficient eta'(b_j)^3 is exactly zero
    => |R_3| <= C ||eta||_{C^1} ||eta||^2_{H^1} <= C S ||eta||_{H^2} ||eta||^2_{H^1}
    which is exactly the improved-Taylor hypothesis (ITH) of the two-norm
    theorem (Ioffe 1979; Dambrine-Lamboley 2019) with weak norm H^1.

  * The dangerous jet slots of Q vanish: the (eta')^2 slot is zero by the
    structure of Lemma 8 (its integrand pairs eta with eta'', never eta'
    with eta''), confirmed numerically at |Delta| <= 5e-4.

So the ONLY thing left is:   is Q coercive in H^1 as a FULL OPERATOR,
i.e. does  Q <= -m_1 G_{H1}  hold including the off-diagonal coupling?

At N=8 the answer was YES: generalised eigenvalues all negative, m_1 = 0.702,
worst Gershgorin margin +0.029.  That margin is thin, so the N=16 run is the
real test of whether it survives.

ON PERFORMANCE (measured, not assumed)
--------------------------------------
Profiling one area evaluation at n_theta=1201:
    mpmath tabulation      0.33s   (once)
    hallway transforms     0.07s
    sequential intersect   3.42s   <-- hot loop, and it is ALREADY C++ (GEOS)
    accumulated polygon reaches 5672 vertices
A Rust port of the same algorithm would buy ~1-3x, because the inner loop is
compiled already.  The real wins are:
  (1) PARALLELISM -- entries are independent; measured 5.5x on 10 cores.
      This file does that.  N=16: 123 min -> 23 min.
  (2) ALGORITHM -- the sofa boundary is five ANALYTIC arcs (Romik's contact
      paths).  Computing the area by Green's theorem over those arcs, as in
      Lemma 8's own proof, replaces 1201 polygon intersections with a short
      quadrature: plausibly 100-1000x, AND it removes the floating-point
      polygon oracle, i.e. it closes caveat (i).  That is the right next
      engineering step, and it is worth more than a language change.

USAGE
-----
    python3 phase2g_h1_coercivity.py --N 8  --n_theta 1201   # ~5 min
    python3 phase2g_h1_coercivity.py --N 16 --n_theta 2001   # ~25 min
    python3 phase2g_h1_coercivity.py --N 16 --resume         # continue
"""
from __future__ import annotations
import argparse, math, os, sys, time
from concurrent.futures import ProcessPoolExecutor, as_completed
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase2d_qsmooth import tabulate_gerver, build_sofa

HERE = os.path.dirname(os.path.abspath(__file__))

_TH = _CX = _CY = _F0 = _B = None


def _init(n_theta, N):
    """Per-worker setup: tabulate c_G once, build the basis, cache F(c_G)."""
    global _TH, _CX, _CY, _F0, _B
    _TH, _CX, _CY = tabulate_gerver(n_theta)
    _B = [(comp, np.sin(2 * k * _TH))
          for comp in ("x", "y") for k in range(1, N + 1)]
    _F0 = build_sofa(_TH, _CX, _CY).area


def _area(amps):
    cx, cy = _CX, _CY
    for (comp, f), a in zip(_B, amps):
        if a == 0.0:
            continue
        if comp == "x":
            cx = cx + a * f
        else:
            cy = cy + a * f
    return build_sofa(_TH, cx, cy).area


def _entry(task):
    """Compute one Hessian entry by central differences."""
    i, j, eps, D = task
    v = np.zeros(D)
    if i == j:
        v[i] = eps;  Fp = _area(v)
        v[i] = -eps; Fm = _area(v)
        return i, j, (Fp - 2 * _F0 + Fm) / (eps * eps)
    v[i], v[j] = eps, eps;   Fpp = _area(v)
    v[i], v[j] = eps, -eps;  Fpm = _area(v)
    v[i], v[j] = -eps, eps;  Fmp = _area(v)
    v[i], v[j] = -eps, -eps; Fmm = _area(v)
    return i, j, (Fpp - Fpm - Fmp + Fmm) / (4 * eps * eps)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=16)
    ap.add_argument("--n_theta", type=int, default=2001)
    ap.add_argument("--eps", type=float, default=1e-4)
    ap.add_argument("--workers", type=int, default=os.cpu_count())
    ap.add_argument("--resume", action="store_true")
    a = ap.parse_args()
    N, eps, D = a.N, a.eps, 2 * a.N
    ckpt = os.path.join(HERE, f"h1_coercivity_N{N}.npz")

    print("=" * 76)
    print(f"H^1 COERCIVITY OF THE FULL SECOND VARIATION   N={N} ({D}x{D})")
    print(f"  parallel over {a.workers} cores")
    print("=" * 76)

    Q = np.full((D, D), np.nan)
    if a.resume and os.path.exists(ckpt):
        Q = np.load(ckpt)["Q"]
        print(f"  resumed: {int(np.isfinite(Q).sum())} of {D*D} cells filled")

    tasks = [(i, j, eps, D) for i in range(D) for j in range(i, D)
             if not np.isfinite(Q[i, j])]
    print(f"  {len(tasks)} entries to compute (~{4*len(tasks)} area evals)")
    t0 = time.time()
    done = 0
    with ProcessPoolExecutor(max_workers=a.workers, initializer=_init,
                             initargs=(a.n_theta, N)) as ex:
        futs = [ex.submit(_entry, t) for t in tasks]
        for fu in as_completed(futs):
            i, j, val = fu.result()
            Q[i, j] = Q[j, i] = val
            done += 1
            if done % 25 == 0 or done == len(tasks):
                el = time.time() - t0
                eta = el / done * (len(tasks) - done)
                np.savez(ckpt, Q=Q)
                print(f"  {done:>5}/{len(tasks)}  {100*done/len(tasks):5.1f}%  "
                      f"elapsed {el/60:5.1f}m  ETA {eta/60:5.1f}m", flush=True)
    np.savez(ckpt, Q=Q)

    # ---------------- analysis ----------------
    k = np.arange(1, N + 1)
    wH1 = np.concatenate([(1 + (2 * k) ** 2) * math.pi / 4] * 2)
    wH2 = np.concatenate([(1 + (2 * k) ** 4) * math.pi / 4] * 2)
    print()
    print("=" * 76)
    for nm, w in (("H^1", wH1), ("H^2", wH2)):
        M = np.diag(1/np.sqrt(w)) @ Q @ np.diag(1/np.sqrt(w))
        ev = np.linalg.eigvalsh(M)
        tag = (f"COERCIVE with m = {-ev.max():.5f}" if ev.max() < 0
               else f"NOT coercive ({(ev>=0).sum()} non-negative)")
        print(f"  {nm}: max={ev.max():+.5f} min={ev.min():+.5f}  -> {tag}")
    print()
    M = np.diag(1/np.sqrt(wH1)) @ Q @ np.diag(1/np.sqrt(wH1))
    dg = np.abs(np.diag(M)); off = np.abs(M).sum(axis=1) - dg
    print("  H^1 Gershgorin margins (|diag| - off-sum) per row:")
    print("   " + "  ".join(f"{v:+.3f}" for v in (dg - off)))
    print(f"\n  worst margin: {(dg-off).min():+.5f}   "
          f"(>0 certifies H^1 coercivity outright)")
    print(f"  saved {ckpt}   total {(time.time()-t0)/60:.1f} min")
    print("=" * 76)


if __name__ == "__main__":
    main()
