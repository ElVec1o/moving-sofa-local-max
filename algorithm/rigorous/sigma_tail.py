"""sigma_tail.py — TAIL PROBE for Theorem 9 item 12, using the exact Rust
oracle (sigma_area.rs).

The covering argument says which mechanism must carry each component of a
perturbation, and therefore what the tail must look like:

  cap, eta_y   <- released nu-slot arcs, weight cos^2 t ~ 1  => k^2 growth
  cap, eta_x   <- nu-slot weight is sin^2 t ~ t^2 (degenerate), so the FAN
                  BITE carries it.  The bite is ~ (amplitude)^2, i.e.
                  FREQUENCY-INDEPENDENT L^2 coercivity — exactly what a tail
                  argument needs, and the one claim that could have failed.
  middle       <- full arc coverage => k^2 growth.

So the predictions, at frequencies far beyond the K<=24 ladders:
  (A) plain modes e_c sin(2kt):        -Q_true grows like k^2
  (B) cap-localized x-polarized:       -Q_true BOUNDED BELOW, ~flat in k
  (C) cap-localized y-polarized:       -Q_true grows like k^2
  (D) middle-localized:                -Q_true grows like k^2

A failure of (B) to stay positive would break the weld.

Usage: python3 sigma_tail.py [n_theta] [eps]
"""
from __future__ import annotations
import os, sys, math, subprocess, time
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from romik_hessian import tabulate_romik
from sofa_romik2017_reference import BETA

PI2 = math.pi/2
trapz = np.trapezoid


def rust_areas(th, trajs):
    inp = [f"{len(th)} {len(trajs)}", " ".join(f"{t:.17g}" for t in th)]
    for a, b in trajs:
        inp.append(" ".join(f"{p:.17g} {q:.17g}" for p, q in zip(a, b)))
    r = subprocess.run([os.path.join(THIS, "sigma_area")],
                       input="\n".join(inp), capture_output=True, text=True)
    if r.stderr.strip():
        print("  [warn]", r.stderr.strip()[:120])
    return [float(x) for x in r.stdout.split()]


def window(th, a, b):
    u = (th - a)/(b - a)
    return np.where((u > 0) & (u < 1), np.sin(np.pi*np.clip(u, 0, 1))**2, 0.0)


def main():
    n_theta = int(sys.argv[1]) if len(sys.argv) > 1 else 1201
    eps = float(sys.argv[2]) if len(sys.argv) > 2 else 1e-4
    th, cx, cy = tabulate_romik(n_theta)

    cases = []
    for k in (4, 8, 16, 32, 64, 128):
        s = np.sin(2*k*th)
        cases.append((f"A plain x  k={k:3d}", s, np.zeros_like(th), k))
        cases.append((f"A plain y  k={k:3d}", np.zeros_like(th), s, k))
    env = window(th, 0.03*BETA, 0.97*BETA)
    for w in (4, 8, 16, 32, 64, 128):
        osc = np.sin(w*math.pi*(th - 0.03*BETA)/(0.94*BETA))
        cases.append((f"B cap x    w={w:3d}", env*osc, np.zeros_like(th), w))
        cases.append((f"C cap y    w={w:3d}", np.zeros_like(th), env*osc, w))
    envm = window(th, BETA + 0.05, PI2 - BETA - 0.05)
    for w in (4, 16, 64, 128):
        osc = np.sin(w*math.pi*(th - BETA - 0.05)/(PI2 - 2*BETA - 0.1))
        cases.append((f"D mid x    w={w:3d}", envm*osc, np.zeros_like(th), w))

    trajs = [(cx, cy)]
    for _, gx, gy, _ in cases:
        nr = math.sqrt(trapz(gx*gx + gy*gy, th))
        gx, gy = gx/nr, gy/nr
        trajs.append((cx + eps*gx, cy + eps*gy))
        trajs.append((cx - eps*gx, cy - eps*gy))

    t0 = time.time()
    A = rust_areas(th, trajs)
    dt = time.time() - t0
    F0 = A[0]
    print(f"n_theta={n_theta}  eps={eps:g}  F(c_R)={F0:.10f}   "
          f"{len(trajs)} evals in {dt:.1f}s ({dt/len(trajs):.2f}s each)\n")
    print(f"{'direction':>18} {'-Q_true':>12} {'-Q/k^2':>10}   reading")
    prev = {}
    for i, (name, _, _, k) in enumerate(cases):
        q = (A[1+2*i] - 2*F0 + A[2+2*i])/eps**2
        fam = name[0]
        ratio = -q/(k*k)
        note = ""
        if fam in prev:
            note = f"x{-q/prev[fam][0]:.1f} for x{k/prev[fam][1]:.0f} in k"
        prev[fam] = (-q, k)
        print(f"{name:>18} {-q:12.3f} {ratio:10.4f}   {note}")


if __name__ == "__main__":
    main()
