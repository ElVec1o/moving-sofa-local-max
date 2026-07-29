"""gerver_active.py — the ACTIVE t-RANGE of each Gerver contact arc.

Part II integrates arc A over all of [0,pi/2], arc C over all of [0,pi/2],
arc D over [0,theta_R], arc B over [pi/2-theta_R,pi/2], and the corner X over
[phi,pi/2-phi].  Those ranges are ASSUMED.  This script measures them.

A contact point P = arc_w(t) lies on dS only if it lies in S at all, i.e. in
every hallway.  With  H_s = C_s \\ Q_s,

    C_s = {<P-c_s, mu_s> <= 1} ^ {<P-c_s, nu_s> <= 1},
    Q_s = {<P-c_s, mu_s> <  0} ^ {<P-c_s, nu_s> <  0},

membership is  P in H_s  <=>  viol_s(P) <= 0  with

    viol_s(P) = max( f_mu - 1,  f_nu - 1,  -max(f_mu, f_nu) ).

So V(t) := max_s viol_s(arc_w(t)) decides it: V <= 0 means the contact point is
genuinely on the sofa boundary at that t; V > 0 means the arc has been cut away
there by some other hallway and the assumed integration range is too long.

Pure numpy, ~40M evaluations, a few seconds.  No polygon library.

Usage: python3 gerver_active.py [n_t] [n_s]
"""
from __future__ import annotations
import os, sys, math
import numpy as np
import mpmath as mp

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from analytic_oracle import contact_wd, _xt_full
from gerver_constants import solve_gerver_constants

PI2 = math.pi / 2


def runs(mask, t):
    """maximal true-runs of `mask` as (t_lo, t_hi) pairs"""
    out = []
    i = 0
    n = len(mask)
    while i < n:
        if mask[i]:
            j = i
            while j + 1 < n and mask[j + 1]:
                j += 1
            out.append((t[i], t[j]))
            i = j + 1
        else:
            i += 1
    return out


def main():
    nt = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
    ns = int(sys.argv[2]) if len(sys.argv) > 2 else 2401
    mp.mp.dps = 20
    p, _ = solve_gerver_constants(working_dps=20, verbose=False)
    phi, theta = float(p['phi']), float(p['theta'])

    # hallway family, sampled in s
    s = np.linspace(0.0, PI2, ns)
    cx = np.empty(ns); cy = np.empty(ns)
    for i, u in enumerate(s):
        x, _, _ = _xt_full(mp.mpf(u), p)
        cx[i] = float(x[0]); cy[i] = float(x[1])
    mux, muy = np.cos(s), np.sin(s)
    nux, nuy = -np.sin(s), np.cos(s)

    def viol_max(P):
        """max_s viol_s(P) for an array P of shape (m,2) -> shape (m,)"""
        dx = P[:, 0:1] - cx[None, :]
        dy = P[:, 1:2] - cy[None, :]
        fm = dx*mux[None, :] + dy*muy[None, :]
        fn = dx*nux[None, :] + dy*nuy[None, :]
        v = np.maximum(np.maximum(fm - 1.0, fn - 1.0), -np.maximum(fm, fn))
        return v.max(axis=1)

    t = np.linspace(0.0, PI2, nt)
    ASSUMED = {"A": (0.0, PI2), "C": (0.0, PI2), "D": (0.0, theta),
               "B": (PI2 - theta, PI2), "X": (phi, PI2 - phi)}

    print(f"Gerver contact arcs: ASSUMED vs MEASURED active range")
    print(f"  n_t={nt}  n_s={ns}   phi={phi:.6f}  theta={theta:.6f}\n")
    print(f"{'arc':>4} {'assumed range':>22} {'measured active runs':>34}"
          f"  {'covered':>8}")
    verdict = []
    for w in ("A", "C", "D", "B", "X"):
        lo, hi = ASSUMED[w]
        tt = t[(t >= lo - 1e-12) & (t <= hi + 1e-12)]
        if w == "X":
            P = np.array([[float(_xt_full(mp.mpf(u), p)[0][0]),
                           float(_xt_full(mp.mpf(u), p)[0][1])] for u in tt])
        else:
            P = np.array([[float(v) for v in contact_wd(
                lambda z: _xt_full(z, p), mp.mpf(u), w)[0]] for u in tt])
        V = viol_max(P)
        tol = 5e-7
        ok = V <= tol
        rr = runs(ok, tt)
        frac = ok.mean()
        txt = " ".join(f"[{a:.4f},{b:.4f}]" for a, b in rr) or "(none)"
        print(f"{w:>4} [{lo:.4f},{hi:.4f}]{'':>7} {txt:>34}  {frac*100:7.1f}%")
        verdict.append((w, frac, rr, (lo, hi)))

    print("\nREADING:")
    bad = [v for v in verdict if v[1] < 0.999]
    if not bad:
        print("  every assumed range is fully active -> the arc table's RANGES "
              "are correct.")
    else:
        for w, frac, rr, (lo, hi) in bad:
            print(f"  arc {w}: only {frac*100:.1f}% of the assumed range "
                  f"[{lo:.4f},{hi:.4f}] lies on dS.")
        print("  -> Part II integrates contact arcs over t where they are NOT "
              "on the boundary.")
        print("     At c_G the extra pieces cancel (A_rec(c_G) = A* exactly); "
              "under perturbation they need not.")


if __name__ == "__main__":
    main()
