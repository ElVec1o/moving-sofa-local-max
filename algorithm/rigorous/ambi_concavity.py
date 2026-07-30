"""ambi_concavity.py — Q = |C2| - 2V at Sigma: tight, critical, and concave.

Baek's Thm 7.1.5 needs three things of an upper-bound functional Q:

    (i)   Q >= |sofa| on the domain, with EQUALITY at the candidate;
    (ii)  the first derivative at the candidate is <= 0 in every admissible direction;
    (iii) Q is concave.

This script checks (i) as an identity, (ii), and (iii) for the functional built in the
note, in the single variable H(theta) = h_K(mu_theta) on [0,pi].

  |C2| = int_0^pi (H^2 - H'^2) dtheta - H(0) - H(pi)                             (A)
  V    = int_0^{pi/2} [ (1/2)(a2^+)^2 + (1/2)(sigma-a1)^2 - (1/2)(a1^-)^2 ] dt
  a1   = H(t+pi/2) - 1 - H'(t),   a2 = H(t) - 1 + H'(t+pi/2),
  sigma = (H(t)-1) tan t + H(t+pi/2) - 1
  gauge: H(0) = 1 (x-translation), H(pi/2) = 1 (unit corridor), so eta(0)=eta(pi/2)=0.

WHAT IS FOUND

  (i)   Q(Sigma) = 1.644955218425 = A_R* to 12 digits.  Note (A) is an INDEPENDENT
        route to the cap area from the niche formula, so this is a genuine
        cross-check of the whole chain |Sigma| = |C2| - 2|N| with |N| = V.
  (ii)  dQ = 0 in EVERY direction, to 1e-9 by central differences on Q itself.  So
        Romik's ODEs are the Euler-Lagrange equations of Q.  (An earlier analytic
        assembly reported a nonzero gradient on [0,beta) and [pi/2,pi/2+beta); that was
        a sign error on d(-(1/2)(a1^-)^2) = +a1^- da1, and the finite-difference check
        is what caught it.  The corrected analytic gradient agrees with FD.)
  (iii) d^2 Q is NEGATIVE DEFINITE at Sigma's own sign pattern, lam_max/h -> -0.71.
        It is NOT negative for every sign pattern: with E1 = E2 = [0.4,1.2] the form is
        +0.397.  Concavity therefore holds on Sigma's CELL -- which is convex, since
        a1, a2 are affine in H so each pointwise sign condition is a half-space -- and
        NOT on the whole domain.  An earlier scan suggested "tau1 <= tau2 suffices";
        that scan only tested intervals ANCHORED AT 0 and the claim is RETRACTED.

CONSEQUENCE, and what is still missing.  (i)+(ii)+(iii) give: Sigma maximises Q over
the convex cell of support functions sharing its sign pattern.  With Q >= |sofa| that
would give |T| <= Q(T) <= Q(Sigma) = |Sigma| there.  But Q >= |sofa| is exactly the
statement that the two sweeps are disjoint, injective and covering for COMPETITORS,
which is measured only at Sigma.  That is Baek's Ch. 3-6 half and it is NOT done, so no
optimality claim follows.

THE CAP'S BOUNDARY, incidentally determined.  H + H'' is the surface-measure density:
  theta in (-beta, beta)          0            the vertex P = (1, 1/2)
  theta in [beta, pi/2-beta)      0.836 -> 0.5
  theta in (pi/2-beta, pi/2+beta) 0.5          a circular arc of radius EXACTLY 1/2,
                                               centred at (1 - 2a_1, 1/2)
  theta = pi/2                    atom 1.167050  the corridor ceiling y = 1, a facet
  theta in (pi-beta, pi]          0            the second vertex
plus the rho-mirror below.  The ceiling facet sits between the two halves of the
radius-1/2 arc, and its rho-image is the corridor floor -- which is where the face-1
sweep terminates.

Usage: python3 ambi_concavity.py [m_intervals]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from ambi_hessian import Hats, gl_split, PI, PI2, H_and_dH
from ambi_functional import data, A_R
from sofa_romik2017_reference import BETA, A1_const


def hess_sets(m, E1, E2, nq=8):
    """(1/2) d^2 Q with E1 = {a1 < 0}, E2 = {a2 > 0} given as lists of intervals"""
    B = Hats(m)
    base = set(B.nodes.tolist()) | {PI2, BETA, PI2 - BETA}
    for lo, hi in list(E1) + list(E2):
        base |= {lo, hi, lo + PI2, hi + PI2}
    bps = np.array(sorted(x for x in base if 0 <= x <= PI))
    M = np.zeros((B.dim, B.dim))
    def acc(W, v, s): return s*((v*W[:, None]).T @ v)
    T, W = gl_split(bps, nq); P, D = B.val_grad(T)
    M += acc(W, P, 1.0) + acc(W, D, -1.0)                              # cap
    for lo, hi in E2:                                                   # face-2, good
        if hi - lo < 1e-12: continue
        sub = np.array(sorted(set(bps[(bps >= lo) & (bps <= hi)].tolist()) | {lo, hi}))
        T, W = gl_split(sub, nq)
        P, _ = B.val_grad(T); _, D2 = B.val_grad(T + PI2)
        M += acc(W, P + D2, -1.0)
    T, W = gl_split(np.array(sorted(set(bps[bps <= PI2].tolist()) | {PI2})), nq)
    P, D = B.val_grad(T)
    M += acc(W, P*np.tan(T)[:, None] + D, -1.0)                        # sigma, good
    for lo, hi in E1:                                                   # obstruction
        if hi - lo < 1e-12: continue
        sub = np.array(sorted(set(bps[(bps >= lo) & (bps <= hi)].tolist()) | {lo, hi}))
        T, W = gl_split(sub, nq)
        P2, _ = B.val_grad(T + PI2); _, D = B.val_grad(T)
        M += acc(W, P2 - D, 1.0)
    return B, 0.5*(M + M.T)


def make_Q(B, nq=12):
    """Q(H_Sigma + eps * phi_j), evaluated from the formulas, for FD gradients"""
    bps = np.array(sorted(set(B.nodes.tolist()) |
                          {BETA, PI2 - BETA, PI2, PI2 + BETA, PI - BETA}))
    bps = bps[(bps >= 0) & (bps <= PI)]
    Tq, Wq = gl_split(bps, nq)
    H0, dH0 = H_and_dH(Tq); Hn, _ = H_and_dH([PI])
    Tv, Wv = gl_split(bps[bps <= PI2], nq)
    a10, a20, sg0 = data(Tv)
    Pq, Dq = B.val_grad(Tq); Pv, Dv = B.val_grad(Tv); Pv2, Dv2 = B.val_grad(Tv + PI2)
    PpiV = B.val_grad([PI])[0]
    tanv = np.tan(Tv)

    def Q(eps, j):
        H = H0 + eps*Pq[:, j]; dH = dH0 + eps*Dq[:, j]
        C2 = float(Wq @ (H*H - dH*dH)) - 1.0 - (Hn[0] + eps*PpiV[0, j])
        a1 = a10 + eps*(Pv2[:, j] - Dv[:, j])
        a2 = a20 + eps*(Pv[:, j] + Dv2[:, j])
        sg = sg0 + eps*(Pv[:, j]*tanv + Pv2[:, j])
        V = float(Wv @ (0.5*np.maximum(a2, 0.0)**2 + 0.5*(sg - a1)**2
                        - 0.5*np.maximum(-a1, 0.0)**2))
        return C2 - 2*V
    return Q


def main():
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 64
    B = Hats(m); Q = make_Q(B)

    print("Q = |C2| - 2V  AT SIGMA:  TIGHT, CRITICAL, CONCAVE\n")
    print(f"(i)   Q(Sigma) = {Q(0.0, 0):.12f}")
    print(f"      A_R*     = {A_R:.12f}      diff {Q(0.0,0)-A_R:+.2e}")
    print(f"      (independent of the polygon oracle: (A) and V are both analytic)\n")

    g = np.array([(Q(1e-6, j) - Q(-1e-6, j))/2e-6 for j in range(B.dim)])
    print(f"(ii)  central-difference gradient, gauge eta(0)=eta(pi/2)=0, dim {B.dim}")
    print(f"      ||dQ||_inf / h = {np.abs(g).max()/B.h:.3e}"
          f"   ||dQ||_2 / h = {np.linalg.norm(g)/B.h:.3e}")
    print(f"      worst node theta = {B.keep[np.argmax(np.abs(g))]*B.h:.5f}")
    print(f"      => CRITICAL to numerical precision, in every direction.\n")

    print("(iii) the Hessian, by sign pattern.  lam_max/h < 0 means concave.")
    cases = [([(0.0, BETA)], [(0.0, PI2 - BETA)], "Sigma's own pattern"),
             ([(0.0, 0.0)], [(0.0, PI2)], "Baek's injectivity (a1>0, a2>0)"),
             ([(0.0, PI2)], [(0.0, PI2)], "a1<0 everywhere, a2>0 everywhere"),
             ([(0.0, PI2)], [(0.0, 0.0)], "crude worst case: E2 empty, E1 all"),
             ([(0.4, 1.2)], [(0.4, 1.2)], "E1 = E2 = [0.4,1.2] (NOT anchored at 0)"),
             ([(0.0, 0.3), (0.7, 1.0), (1.3, PI2)],
              [(0.0, 0.3), (0.7, 1.0), (1.3, PI2)], "E1 = E2, three pieces")]
    print(f"      {'sign pattern':>38} {'m=32':>9} {'m=64':>9} {'m=128':>9}")
    for E1, E2, lab in cases:
        row = []
        for mm in (32, 64, 128):
            Bm, M = hess_sets(mm, E1, E2)
            row.append(np.linalg.eigvalsh(M).max()/Bm.h)
        print(f"      {lab:>38} " + "".join(f"{v:>9.4f}" for v in row))
    print("\n      Sigma's cell is CONVEX (a1, a2 affine in H, so each pointwise sign")
    print("      condition is a half-space), so concave + critical => Sigma maximises")
    print("      Q there.  Concavity FAILS on other cells, so nothing global follows.")

    print("\n(iv)  the cap's boundary, from the surface-measure density H + H''")
    e = 1e-5
    def d(th):
        a, _ = H_and_dH([th-e]); b, _ = H_and_dH([th]); c, _ = H_and_dH([th+e])
        return b[0] + (a[0] - 2*b[0] + c[0])/e**2
    for th, lab in ((0.15, "vertex P=(1,1/2)"), (0.5, "smooth arc"),
                    (0.9, "smooth arc"), (PI2 - 0.02, "radius-1/2 arc"),
                    (1.70, "radius-1/2 arc"), (PI2 + BETA + 0.02, "smooth arc"),
                    (2.6, "smooth arc"), (3.0, "second vertex")):
        print(f"        theta = {th:7.4f}   H+H'' = {d(th):9.6f}   {lab}")
    a, _ = H_and_dH([PI2 - 1e-9]); b, _ = H_and_dH([PI2 + 1e-9])
    _, da = H_and_dH([PI2 - 1e-9]); _, db = H_and_dH([PI2 + 1e-9])
    print(f"        theta = pi/2     atom  = {db[0]-da[0]:9.6f}   ceiling facet y=1")
    print(f"        radius-1/2 arc centre = (1 - 2a_1, 1/2) = "
          f"({1-2*A1_const:.9f}, 0.5)")


if __name__ == "__main__":
    main()
