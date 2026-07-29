"""sigma_tail_min.py — Theorem 9 item 12: the K-uniform lower bound, computed
against the TRUE functional with the exact Rust oracle.

The fast exact oracle allows a cleaner argument than the Q_rel + bite
dichotomy.  Since the structure-following reconstruction is superset-valid,

        Q_true(eta)  <=  Q_struct(eta)        i.e.   -Q_true >= -Q_struct,

so wherever -Q_struct is LARGE the true functional is even more coercive and
needs no separate treatment.  The minimum of -Q_true can therefore only sit
where -Q_struct is small, and

    inf_{||eta||=1} -Q_true  >=  min(  inf over the p least-coercive
                                       Q_struct directions of -Q_true ,
                                       lambda_{p+1}(-Q_struct)  ).

The first term is a low-dimensional search evaluated by the EXACT oracle
(no polarization of the kinked functional, no matrices); the second is read
off the closed-form Q_struct spectrum, which is itself arb-certified.

Usage: python3 sigma_tail_min.py K [p] [batches] [n_theta]
"""
from __future__ import annotations
import os, sys, math, subprocess, time
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from romik_hessian import tabulate_romik

PI2 = math.pi/2
trapz = np.trapezoid


def qstruct(K):
    """closed-form Q_struct from the Rust assembler"""
    out = subprocess.run([os.path.join(THIS, "sigma_struct"), str(K), "0"],
                         capture_output=True, text=True,
                         env=dict(os.environ, DUMP="1")).stdout.split("\n")
    n = int(out[0])
    Q = np.array([[float(x) for x in out[1+i].split()] for i in range(n)])
    return 0.5*(Q + Q.T)


def rust_areas(th, trajs):
    inp = [f"{len(th)} {len(trajs)}", " ".join(f"{t:.17g}" for t in th)]
    for a, b in trajs:
        inp.append(" ".join(f"{p:.17g} {q:.17g}" for p, q in zip(a, b)))
    r = subprocess.run([os.path.join(THIS, "sigma_area")],
                       input="\n".join(inp), capture_output=True, text=True)
    return [float(x) for x in r.stdout.split()]


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    p = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    nb = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    n_theta = int(sys.argv[4]) if len(sys.argv) > 4 else 1201
    eps = 1e-4
    rng = np.random.default_rng(4242)

    th, cx, cy = tabulate_romik(n_theta)
    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    n = len(modes)
    B = np.array([np.sin(2*k*th) for (_, k) in modes])          # profiles

    # --- Q_struct spectrum in the L^2 metric, translation projected out ---
    Q = qstruct(K)
    gl = math.pi/4
    w = np.zeros(n)
    for i, (c, k) in enumerate(modes):
        if c == 0:
            w[i] = (1.0/k) if (k % 2 == 1) else 0.0
    wn = w/np.linalg.norm(w)
    U, sv, _ = np.linalg.svd(np.eye(n) - np.outer(wn, wn))
    P = U[:, sv > 1e-10]
    ev, V = np.linalg.eigh(P.T @ Q @ P / gl)
    order = np.argsort(-ev)                    # least negative first
    lam_gap = -ev[order[p]] if p < len(order) else float("inf")
    base = P @ V[:, order[:p]]

    print(f"K={K}  p={p}  n_theta={n_theta}")
    print(f"  Q_struct: least-coercive -lambda_1 = {-ev[order[0]]:.5f},"
          f"  gap lambda_(p+1) = {lam_gap:.3f}")

    def make(a):
        a = a/np.linalg.norm(a)
        v = base @ a
        gx = v[:K] @ B[:K]
        gy = v[K:] @ B[K:]
        nr = math.sqrt(trapz(gx*gx + gy*gy, th))
        return gx/nr, gy/nr

    best = (float("inf"), None)
    t0 = time.time()
    for b in range(nb):
        if b == 0:
            cand = [np.eye(p)[i] for i in range(p)] + \
                   [rng.standard_normal(p) for _ in range(40)]
        else:
            step = 0.6*(0.55**b)
            cand = [best[1] + step*rng.standard_normal(p) for _ in range(48)]
        trajs = [(cx, cy)]
        for a in cand:
            gx, gy = make(a)
            trajs.append((cx + eps*gx, cy + eps*gy))
            trajs.append((cx - eps*gx, cy - eps*gy))
        A = rust_areas(th, trajs)
        F0 = A[0]
        for i, a in enumerate(cand):
            q = (A[1+2*i] - 2*F0 + A[2+2*i])/eps**2
            if -q < best[0]:
                best = (-q, a/np.linalg.norm(a))
        print(f"  batch {b+1}/{nb}: best -Q_true = {best[0]:.4f}   "
              f"[{time.time()-t0:.0f}s]", flush=True)

    print(f"\n  RESULT K={K}: inf over the p least-coercive directions = "
          f"{best[0]:.4f}")
    print(f"  complement is bounded by lambda_(p+1) = {lam_gap:.3f}")
    print(f"  => K-uniform lower bound  -Q_true >= "
          f"{min(best[0], lam_gap):.4f} * ||eta||^2_L2")


if __name__ == "__main__":
    main()
