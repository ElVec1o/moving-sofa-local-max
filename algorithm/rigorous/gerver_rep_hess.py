"""gerver_rep_hess.py — Part II's ladder recomputed against the CHORD-FREE A_rep.

The old ladder was computed against the chorded A_rec.  Its NUMBERS are not
corrupted by the rank-one defect (symmetric second differences annihilate a
linear term, verified to the last digit), but A_rep is a genuinely DIFFERENT
functional -- it drops the two constant arc pieces and closes on constraint
lines instead of chords -- so its Hessian must be computed afresh before any
certification means anything.

A_rep is stationary at c_G to 1.7e-10 on every mode (gerver_rep_green), so the
symmetric second difference is now the honest second variation, not a second
difference straddling a kink in the first derivative.

Rule 8: progress, ETA, atomic checkpoint, resume.  mpmath rather than Rust
because the contact machinery is mpmath; mitigated by being minutes not hours
(0.06 s/eval at dps=20) and by trivial memory (a 2K x 2K matrix).

Usage: python3 gerver_rep_hess.py [K] [dps] [eps]
Checkpoint: gerver_rep_K{K}.npy
"""
from __future__ import annotations
import os, sys, time
import numpy as np
import mpmath as mp

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from gerver_rep_green import area_rep
from analytic_oracle import _xt_full
from gerver_constants import solve_gerver_constants


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    dps = int(sys.argv[2]) if len(sys.argv) > 2 else 25
    eps = mp.mpf(sys.argv[3]) if len(sys.argv) > 3 else mp.mpf('1e-5')
    mp.mp.dps = dps
    p, _ = solve_gerver_constants(working_dps=dps, verbose=False)
    modes = [(c, k) for c in ("x", "y") for k in range(1, K+1)]
    n = len(modes)

    def traj_of(coef):
        """c_G + sum coef[i] * mode_i"""
        def traj(t):
            x, xp, xpp = _xt_full(t, p)
            sx = sxp = sxpp = mp.mpf(0)
            sy = syp = sypp = mp.mpf(0)
            for a, (c, k) in zip(coef, modes):
                if a == 0:
                    continue
                s = mp.sin(2*k*t); co = mp.cos(2*k*t)
                if c == "x":
                    sx += a*s; sxp += a*2*k*co; sxpp -= a*(2*k)**2*s
                else:
                    sy += a*s; syp += a*2*k*co; sypp -= a*(2*k)**2*s
            return ((x[0]+sx, x[1]+sy), (xp[0]+sxp, xp[1]+syp),
                    (xpp[0]+sxpp, xpp[1]+sypp))
        return traj

    def A(coef):
        return area_rep(traj_of(coef), p, dps)

    z = [mp.mpf(0)]*n
    F0 = A(z)
    print(f"K={K} dps={dps} eps={mp.nstr(eps,3)}   {n} modes, "
          f"{n*(n+1)//2} entries", flush=True)
    print(f"  A_rep(c_G) = {mp.nstr(F0, 12)}", flush=True)

    ck = os.path.join(THIS, f"gerver_rep_K{K}.npy")
    Q = np.load(ck) if os.path.exists(ck) else np.full((n, n), np.nan)
    if Q.shape != (n, n):
        Q = np.full((n, n), np.nan)
    todo = [(i, j) for i in range(n) for j in range(i, n)
            if not np.isfinite(Q[i, j])]
    print(f"  {len(todo)} entries remaining", flush=True)

    def e_(i, s):
        v = list(z); v[i] = s*eps
        return v

    t0 = time.time()
    for c_, (i, j) in enumerate(todo):
        if i == j:
            v = (A(e_(i, 1)) - 2*F0 + A(e_(i, -1)))/eps**2
        else:
            pp = list(z); pp[i] = eps;  pp[j] = eps
            mm = list(z); mm[i] = -eps; mm[j] = -eps
            pm = list(z); pm[i] = eps;  pm[j] = -eps
            mp_ = list(z); mp_[i] = -eps; mp_[j] = eps
            v = (A(pp) + A(mm) - A(pm) - A(mp_))/(4*eps**2)
        Q[i, j] = Q[j, i] = float(v)
        if (c_+1) % 40 == 0 or c_+1 == len(todo):
            tmp = ck + ".tmp.npy"
            np.save(tmp, Q); os.replace(tmp, ck)
            el = time.time()-t0
            rate = (c_+1)/max(el, 1e-9)
            print(f"  {c_+1}/{len(todo)}  {rate:.1f} ent/s  "
                  f"elapsed {el/60:.1f}m  ETA {(len(todo)-c_-1)/rate/60:.1f}m",
                  flush=True)
    Qs = 0.5*(Q + Q.T)
    w = np.linalg.eigvalsh(Qs)
    print(f"\nspectrum: min {w.min():.6f}  max {w.max():.6f}")
    print(f"  8 largest: {np.round(w[-8:], 6)}")
    print(f"  NEGATIVE DEFINITE: {'YES' if w.max() < 0 else 'NO'}")
    # translation mode projected out
    tr = np.array([(1.0/k if (c == "x" and k % 2 == 1) else 0.0)
                   for (c, k) in modes])
    tr = tr/np.linalg.norm(tr)
    U, sv, _ = np.linalg.svd(np.eye(n) - np.outer(tr, tr))
    P = U[:, sv > 1e-10]
    wp = np.linalg.eigvalsh(P.T @ Qs @ P)
    print(f"  with translation projected out: max {wp.max():.6f}  "
          f"-> {'NEGATIVE DEFINITE' if wp.max() < 0 else 'NOT nd'}")
    print(f"saved {os.path.basename(ck)}")


if __name__ == "__main__":
    main()
