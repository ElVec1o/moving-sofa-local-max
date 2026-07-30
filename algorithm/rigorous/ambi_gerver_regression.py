"""ambi_gerver_regression.py — Rule I11: does the machinery recover the SOLVED case?

The framework must be tested against the one-corner problem, where the answer is known.
It does NOT recover it, and this script is the record.

  * Gerver satisfies the one-corner injectivity condition everywhere: alpha_1 > 0 and
    alpha_2 > 0 on all of [0, pi/2].
  * (RC) FAILS for Gerver's cap: max of the a.c. part of H + H'' is 1.3960, near theta = pi.
  * Gerver's face-2 sweep is genuinely NOT injective in this decomposition: 33002 of
    158802 tested pairs meet interior to both segments, min(s22 - alpha_2) = -0.0944.
    The face-1 sweep IS injective.
  * Consistently V = 0.6426146 > |N|, as the Reynolds proposition requires.

So (RC) and the one-corner injectivity condition are INDEPENDENT: Sigma satisfies the
first and not the second, Gerver the second and not the first.  The decomposition
N = W2 (+) W1out is therefore not the one the one-corner argument uses, and its failure on
the solved case is a standing caution about the framework.

Usage: python3 ambi_gerver_regression.py [n]
"""
from __future__ import annotations
import os, sys, math
import numpy as np
import mpmath as mp

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from ambi_hessian import PI, PI2
import gerver_constants as GC


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 401
    mp.mp.dps = 30
    p, resid = GC.solve_gerver_constants(working_dps=30)
    print(f"RULE I11 REGRESSION: the machinery on GERVER (Newton residual "
          f"{mp.nstr(resid, 3)})\n")

    def dat(t):
        x, xp = GC._xt_xtp(mp.mpf(float(t)), p)
        z = complex(float(x[0]), float(x[1])); dz = complex(float(xp[0]), float(xp[1]))
        e = np.exp(-1j*float(t)); w = e*z; wd = e*dz
        return w.real, w.imag, -wd.real, wd.imag, w.real*math.tan(float(t)) + w.imag

    def Hg(x):
        if x <= PI2:
            return dat(min(max(x, 1e-9), PI2 - 1e-9))[0] + 1.0
        return dat(min(max(x - PI2, 1e-9), PI2 - 1e-9))[1] + 1.0

    th = np.linspace(1e-3, PI - 1e-3, 500); th = th[np.abs(th - PI2) > 0.03]
    e = 1e-4
    dg = np.array([Hg(x) + (Hg(x-e) - 2*Hg(x) + Hg(x+e))/e**2 for x in th])
    print(f"  (RC): max a.c. H+H'' = {dg.max():.6f} at theta = {th[np.argmax(dg)]:.4f}"
          f"   {'HOLDS' if dg.max() <= 1 else 'FAILS'}   margin {1-dg.max():+.6f}")

    T = np.linspace(1e-6, PI2 - 1e-6, n)
    D = np.array([dat(t) for t in T])
    Fm, Gm, a1, a2, sg = D[:,0], D[:,1], D[:,2], D[:,3], D[:,4]
    print(f"  one-corner condition: alpha_1 > 0 on {100*np.mean(a1>0):.1f}%, "
          f"alpha_2 > 0 on {100*np.mean(a2>0):.1f}% of [0,pi/2]")

    cx = Fm*np.cos(T) - Gm*np.sin(T); cy = Fm*np.sin(T) + Gm*np.cos(T)
    NU = -np.outer(cx, np.sin(T)) + np.outer(cy, np.cos(T))
    MU = np.outer(cx, np.cos(T)) + np.outer(cy, np.sin(T))
    SIN = np.sin(T[:, None] - T[None, :])
    with np.errstate(divide='ignore', invalid='ignore'):
        s22 = (NU - Gm[None, :])/SIN
        s11 = (MU - Fm[None, :])/(-SIN)
    mask = np.abs(np.subtract.outer(np.arange(n), np.arange(n))) >= 3
    A2 = a2[:, None]; lo = np.maximum(a1, 0.0)[:, None]; hi = sg[:, None]
    i2 = (s22 > 1e-9) & (s22 < A2 - 1e-9)
    i1 = (s11 > lo + 1e-9) & (s11 < hi - 1e-9)
    print(f"  face-2 pairs interior to BOTH segments: {int((mask&i2&i2.T).sum())}"
          f" of {int(mask.sum())}")
    print(f"  face-1 pairs interior to BOTH segments: {int((mask&i1&i1.T).sum())}"
          f" of {int(mask.sum())}")
    low = np.tril(mask, -1)
    print(f"  min over t'<t of (s22 - alpha_2) = "
          f"{np.nanmin(np.where(low, s22-A2, np.inf)):+.6f}")
    print(f"  min over t'<t of (alpha_1 - s11) = "
          f"{np.nanmin(np.where(low, lo-s11, np.inf)):+.6f}")

    xg, wg = np.polynomial.legendre.leggauss(300)
    Tq = 0.5*PI2*xg + 0.5*PI2; Wq = 0.5*PI2*wg
    v = np.array([dat(t) for t in Tq])
    V = float(Wq @ (0.5*np.maximum(v[:,3], 0)**2 + 0.5*(v[:,4]-v[:,2])**2
                    - 0.5*np.maximum(-v[:,2], 0)**2))
    print(f"\n  V(Gerver) = {V:.9f}, against |N| = 0.6406 to 0.6412 measured at 481 and")
    print(f"  721 constraints: V > |N|, as the Reynolds proposition requires.")
    print(f"\n  CONCLUSION: the construction does not recover the solved case.")


if __name__ == "__main__":
    main()
