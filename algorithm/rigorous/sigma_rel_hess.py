"""sigma_rel_hess.py — released Hessian Q_rel at arbitrary K, via the exact
Rust oracle (sigma_area.rs, RELEASED=1).

Thin driver: all geometry is Rust (measured 99% of wall time).  Rule 8
compliance: progress, ETA, atomic checkpoint saves, resume-from-checkpoint.

Usage: python3 sigma_rel_hess.py K [n_theta] [eps] [batch_entries]
Checkpoint: sigma_rel_K{K}.npy   (same format as the earlier FD ladders)
"""
from __future__ import annotations
import os, sys, math, time, subprocess
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from romik_hessian import tabulate_romik


def rust_areas(th, trajs):
    inp = [f"{len(th)} {len(trajs)}", " ".join(f"{t:.17g}" for t in th)]
    for a, b in trajs:
        inp.append(" ".join(f"{p:.17g} {q:.17g}" for p, q in zip(a, b)))
    r = subprocess.run([os.path.join(THIS, "sigma_area")],
                       input="\n".join(inp), capture_output=True, text=True,
                       env=dict(os.environ, RELEASED="1"))
    return [float(x) for x in r.stdout.split()]


def save_atomic(path, arr):
    tmp = path + ".tmp"
    np.save(tmp, arr)
    os.replace(tmp + ".npy" if os.path.exists(tmp + ".npy") else tmp, path)


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 32
    n_theta = int(sys.argv[2]) if len(sys.argv) > 2 else 1201
    eps = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-4
    nb = int(sys.argv[4]) if len(sys.argv) > 4 else 60

    th, cx, cy = tabulate_romik(n_theta)
    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    n = len(modes)
    B = {m: np.sin(2*m[1]*th) for m in modes}
    ck = os.path.join(THIS, f"sigma_rel_K{K}.npy")
    Q = np.load(ck) if os.path.exists(ck) else np.full((n, n), np.nan)
    if Q.shape != (n, n):
        Q = np.full((n, n), np.nan)

    todo = [(i, j) for i in range(n) for j in range(i, n)
            if not np.isfinite(Q[i, j])]
    total = n*(n+1)//2
    print(f"K={K}  {n} modes  {total} entries, {len(todo)} remaining  "
          f"(n_theta={n_theta}, eps={eps:g})", flush=True)
    if not todo:
        print("  already complete")
    F0 = rust_areas(th, [(cx, cy)])[0]
    print(f"  F_rel(c_R) = {F0:.10f}", flush=True)

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
                v = (A[p] + A[p+1] - A[p+2] - A[p+3])/(4*eps**2)
                Q[i, j] = Q[j, i] = v
                p += 4
        save_atomic(ck, Q)
        done = done0 + s + len(chunk)
        el = time.time() - t0
        rate = (s + len(chunk))/max(el, 1e-9)
        eta = (len(todo) - s - len(chunk))/max(rate, 1e-9)
        print(f"  {done}/{total} ({100*done//total}%)  "
              f"{rate:.1f} entries/s  elapsed {el/60:.1f}m  ETA {eta/60:.1f}m",
              flush=True)
    print(f"saved {os.path.basename(ck)}")


if __name__ == "__main__":
    main()
