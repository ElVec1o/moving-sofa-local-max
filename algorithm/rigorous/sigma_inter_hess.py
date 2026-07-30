"""sigma_inter_hess.py — S8: the ladder of the INTERSECTION reconstruction.

The construction that avoids all three failure modes is not a curve at all.  Take

    R_n(c) := intersection of H_{t_i}(c) over a grid t_1..t_n,

the finite-subfamily intersection.  Then

  * S(c) subset R_n(c) for EVERY c, by `superset_principle` -- rigorously, with no
    hypothesis about chords, supporting lines or simplicity.  Mode 1 cannot arise
    (there are no chords) and Mode 2 cannot arise (a region area is computed, not
    a signed Green sum).
  * |R_n(c)| is computed EXACTLY by polygon arithmetic (sigma_area.rs: half-plane
    clipping plus exact wedge subtraction).
  * |R_n(c_R)| = A_R* + C/n, so equality at the base point holds only in the
    limit.  That is harmless: if the Hessian margin m is uniform in n then
        A_true(c_R + eps eta)  <=  |R_n(c_R + eps eta)|
                               <=  A_R* + C/n - (m/2) eps^2 ||eta||^2,
    and letting n -> infinity gives the exact statement.  The offset vanishes; the
    quadratic decrease survives.

So the object to certify is the Hessian of |R_n|, and sigma_area.rs already
computes |R_n| -- it is the same binary this project has been calling "the true
area oracle".  What was recorded as its "offset C/n" is precisely the superset
slack.

This script computes that Hessian by central differences and reports its spectrum,
for a ladder of n so the uniformity in n can be read off.

Rule 8: all geometry is Rust; progress, ETA, atomic checkpoint, resume.

Usage: python3 sigma_inter_hess.py K [n_theta] [eps] [batch]
Checkpoint: sigma_inter_K{K}_n{n_theta}.npy
"""
from __future__ import annotations
import os, sys, math, time, subprocess
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from romik_hessian import tabulate_romik


def rust_areas(th, trajs):
    """|R_n| for a batch of trajectories -- NO 'RELEASED' flag, so this is the
    full intersection reconstruction, walls and wedges included."""
    inp = [f"{len(th)} {len(trajs)}", " ".join(f"{t:.17g}" for t in th)]
    for a, b in trajs:
        inp.append(" ".join(f"{p:.17g} {q:.17g}" for p, q in zip(a, b)))
    r = subprocess.run([os.path.join(THIS, "sigma_area")],
                       input="\n".join(inp), capture_output=True, text=True)
    return [float(x) for x in r.stdout.split()]


def save_atomic(path, arr):
    tmp = path + ".tmp.npy"
    np.save(tmp, arr)
    os.replace(tmp, path)


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    nth = int(sys.argv[2]) if len(sys.argv) > 2 else 2401
    eps = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-4
    nb = int(sys.argv[4]) if len(sys.argv) > 4 else 40

    th, cx, cy = tabulate_romik(nth)
    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    n = len(modes)
    B = {m: np.sin(2*m[1]*th) for m in modes}
    ck = os.path.join(THIS, f"sigma_inter_K{K}_n{nth}.npy")
    Q = np.load(ck) if os.path.exists(ck) else np.full((n, n), np.nan)
    if Q.shape != (n, n):
        Q = np.full((n, n), np.nan)

    todo = [(i, j) for i in range(n) for j in range(i, n)
            if not np.isfinite(Q[i, j])]
    total = n*(n+1)//2
    F0 = rust_areas(th, [(cx, cy)])[0]
    print(f"K={K}  n_theta={nth}  eps={eps:g}   {n} modes, {total} entries, "
          f"{len(todo)} remaining", flush=True)
    print(f"  |R_n|(c_R) = {F0:.10f}    A_R* = 1.6449552184    "
          f"superset slack {F0-1.6449552184:+.3e}", flush=True)

    def prof(i):
        c, k = modes[i]
        z = np.zeros_like(th)
        return (B[modes[i]], z) if c == 0 else (z, B[modes[i]])

    t0 = time.time()
    done0 = total - len(todo)
    for s in range(0, len(todo), nb):
        chunk = todo[s:s+nb]
        trajs = []
        for (i, j) in chunk:
            gx1, gy1 = prof(i); gx2, gy2 = prof(j)
            if i == j:
                trajs += [(cx + eps*gx1, cy + eps*gy1),
                          (cx - eps*gx1, cy - eps*gy1)]
            else:
                trajs += [(cx + eps*(gx1+gx2), cy + eps*(gy1+gy2)),
                          (cx - eps*(gx1+gx2), cy - eps*(gy1+gy2)),
                          (cx + eps*(gx1-gx2), cy + eps*(gy1-gy2)),
                          (cx - eps*(gx1-gx2), cy - eps*(gy1-gy2))]
        A = rust_areas(th, trajs)
        p = 0
        for (i, j) in chunk:
            if i == j:
                Q[i, i] = (A[p] - 2*F0 + A[p+1])/eps**2
                p += 2
            else:
                Q[i, j] = Q[j, i] = (A[p] + A[p+1] - A[p+2] - A[p+3])/(4*eps**2)
                p += 4
        save_atomic(ck, Q)
        done = done0 + s + len(chunk)
        el = time.time() - t0
        rate = (s + len(chunk))/max(el, 1e-9)
        print(f"  {done}/{total} ({100*done//total}%)  {rate:.1f} ent/s  "
              f"elapsed {el/60:.1f}m  ETA "
              f"{(len(todo)-s-len(chunk))/max(rate,1e-9)/60:.1f}m", flush=True)

    Qs = 0.5*(Q + Q.T)
    w = np.linalg.eigvalsh(Qs)
    print(f"\nspectrum of the |R_n| Hessian: min {w.min():.4f}  "
          f"max {w.max():.6f}")
    print(f"  8 largest: {np.round(w[-8:], 6)}")
    tr = np.array([(1.0/k if (c == 0 and k % 2 == 1) else 0.0)
                   for (c, k) in modes])
    tr = tr/np.linalg.norm(tr)
    U, sv, _ = np.linalg.svd(np.eye(n) - np.outer(tr, tr))
    P = U[:, sv > 1e-10]
    wp = np.linalg.eigvalsh(P.T @ Qs @ P)
    print(f"  translation projected out: max {wp.max():.6f}")
    print(f"  NEGATIVE DEFINITE: "
          f"{'YES' if wp.max() < 0 else 'NO'}   (margin "
          f"{-wp.max():.6f})")
    print(f"saved {os.path.basename(ck)}")


if __name__ == "__main__":
    main()
