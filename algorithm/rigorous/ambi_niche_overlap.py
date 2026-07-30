"""ambi_niche_overlap.py — B1 SCOPING: do Sigma's two niches overlap?

GOAL (new): prove that Romik's ambidextrous sofa Sigma, area A_R* = 1.6449552184,
is the maximum-area AMBIDEXTROUS moving sofa, by transferring Baek's concavity
architecture (arXiv:2411.19826) from the one-corner problem.

Baek's engine, in one line: build an overestimating region whose area is a
QUADRATIC functional Q on a convex domain of convex bodies, show Q is CONCAVE
because it is a linear functional minus MAMIKON regions (Theorem 7.4.2: a Mamikon
region has area (1/2) int alpha(t)^2 dt with alpha convex-linear in K, hence a
CONVEX quadratic), and then only the FIRST derivative is needed (Theorem 7.1.5).

For the one-corner problem the sofa is  S = K \\ N(K),  cap minus ONE niche.  The
ambidextrous sofa is, in the decomposition this project already uses in
sigma_area.rs,

    Sigma = C2 \\ (U u rho U),      C2 = C ^ rho C  (still convex),

a convex cap minus the union of TWO niches, exchanged by rho(x,y) = (x, 1-y).

THE CRUX.  Inclusion-exclusion gives

    |U u rho U| = |U| + |rho U| - |U ^ rho U|,

and the last term enters Q with a PLUS sign.  Baek's concavity comes from
SUBTRACTING convex quadratics, so a subtracted |U ^ rho U| would be fine but an
ADDED one is exactly the wrong sign.  Hence:

    if U ^ rho U = empty, the architecture transfers with no new mathematics
    beyond redoing Baek's chapters for two corners;
    if U ^ rho U is non-empty, the overlap term is new mathematics and must be
    shown to be concave (or bounded by something concave) on its own.

This script decides it, by testing membership of a grid of points in both niches.

Membership criterion (proved this session): with points as complex numbers,
<q - c(t), mu_t> + i <q - c(t), nu_t> = e^{-i t}(q - c(t)), and Q_t is the open
third quadrant in that frame, so

    q in Q_t  <=>  f_mu(t) < 0 and f_nu(t) < 0,
    q in U    <=>  that holds for SOME t.

Usage: python3 ambi_niche_overlap.py [n_grid] [n_t]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from romik_hessian import tabulate_romik

PI2 = math.pi/2


def niche_depth(P, cx, cy, s):
    """for each point of P, max over t of min(-f_mu, -f_nu); > 0 means the point
    lies in some wedge Q_t, i.e. in the niche U"""
    mux, muy = np.cos(s), np.sin(s)
    nux, nuy = -np.sin(s), np.cos(s)
    best = np.full(len(P), -1e30)
    CH = 300
    for a in range(0, len(s), CH):
        b = min(a+CH, len(s))
        dx = P[:, 0:1] - cx[None, a:b]
        dy = P[:, 1:2] - cy[None, a:b]
        fm = dx*mux[None, a:b] + dy*muy[None, a:b]
        fn = dx*nux[None, a:b] + dy*nuy[None, a:b]
        best = np.maximum(best, np.minimum(-fm, -fn).max(axis=1))
    return best


def main():
    ng = int(sys.argv[1]) if len(sys.argv) > 1 else 700
    nt = int(sys.argv[2]) if len(sys.argv) > 2 else 24001
    s = np.linspace(0.0, PI2, nt)
    _, cx, cy = tabulate_romik(nt)

    # grid over a box containing Sigma (Sigma sits in roughly x in [-1.6,1.1],
    # y in [0,1]); the rho image of a point is (x, 1-y)
    xs = np.linspace(-2.6, 1.6, ng)
    ys = np.linspace(-0.2, 1.2, ng)
    X, Y = np.meshgrid(xs, ys, indexing="ij")
    P = np.column_stack([X.ravel(), Y.ravel()])
    Pr = np.column_stack([X.ravel(), 1.0 - Y.ravel()])      # rho of each point

    dU = niche_depth(P, cx, cy, s)          # depth in U
    dRU = niche_depth(Pr, cx, cy, s)        # depth in rho U (test rho(q) in U)

    inU = dU > 0
    inRU = dRU > 0
    both = inU & inRU
    cell = (xs[1]-xs[0])*(ys[1]-ys[0])

    print("B1 SCOPING -- do Sigma's two niches overlap?")
    print(f"  grid {ng}x{ng} over [-2.6,1.6]x[-0.2,1.2], cell area "
          f"{cell:.3e};  n_t = {nt}\n")
    print(f"  |U|      approx {inU.sum()*cell:.6f}   ({inU.sum()} cells)")
    print(f"  |rho U|  approx {inRU.sum()*cell:.6f}   ({inRU.sum()} cells)")
    print(f"  |U ^ rho U| approx {both.sum()*cell:.6f}   ({both.sum()} cells)")

    if both.sum():
        d = np.minimum(dU, dRU)[both]
        i = int(np.argmax(d))
        idx = np.where(both)[0][i]
        print(f"\n  deepest common point: ({P[idx,0]:+.5f}, {P[idx,1]:+.5f})  "
              f"with min-depth {d[i]:.3e}")
        print(f"  depth distribution over the overlap: max {d.max():.3e}  "
              f"median {np.median(d):.3e}")
        print("\n  -> the niches DO overlap.  |U ^ rho U| enters Q with a PLUS")
        print("     sign, so it is NOT covered by Baek's subtract-convex-quadratics")
        print("     mechanism.  This term is the new mathematics the ambidextrous")
        print("     transfer needs.")
    else:
        print("\n  -> the niches are DISJOINT on this grid.  Then")
        print("     |U u rho U| = |U| + |rho U|, both handled exactly as Baek's")
        print("     single niche, and the architecture transfers with no new")
        print("     mathematics beyond redoing his chapters for two corners.")
        print("     (A grid test is evidence, not proof: a separating-hyperplane")
        print("      or symmetry argument is then the thing to prove.)")


if __name__ == "__main__":
    main()
