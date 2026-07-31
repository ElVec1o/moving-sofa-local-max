"""ambi_system.py — the SHARP concavity constant, as a 2x2 Sturm-Liouville system.

The decoupled chain of ambi_sturm.py splits the second variation into two scalar
eigenvalue problems by two Cauchy-Schwarz steps, and certifies 2/3 against a measured
sharp value.  The splitting is unnecessary.  The two halves of [0,pi] are the SAME
interval re-indexed, so setting

    p(t) = eta(t),   q(t) = eta(t + pi/2),    t in [0, pi/2],

turns the whole of (Q2) into a single quadratic form in the pair (p,q) on [0,pi/2]:

  (1/2) d^2 Q = int_0^{pi/2} L,
  L = 2p^2 - 2p'^2 + q^2 - q'^2 - 1_{E2}(p + q')^2 + 1_{E1}(q - p')^2 ,

with E1 = [0,beta), E2 = [0,pi/2-beta).  The boundary conditions are all forced:
p(0) = 0 and p(pi/2) = 0 are the gauge H(0) = H(pi/2) = 1; q(0) = eta(pi/2) = 0 is the
same gauge seen from the other half; and q(pi/2) = eta(pi) is FREE, so it gets the
natural condition.  No approximation has been made, so the first eigenvalue of this
system IS the sharp constant.

WHAT THE STRUCTURE SHOWS.  Writing M := -L piecewise as
a p'^2 + b q'^2 + g p^2 + d q^2 + 2e p q' + 2f q p':

             piece          a    b    g    d    e    f
          [0,beta)          1    2   -1   -2    1    1
    [beta,pi/2-beta)        2    2   -1   -1    1    0
    [pi/2-beta,pi/2)        2    1   -2   -1    0    0

On [0,beta) -- exactly where the obstruction lives -- e = f = 1, and

    2 p q' + 2 q p' = 2 (p q)'

is a TOTAL DERIVATIVE.  The E1 obstruction and the E2 resource cancel there up to the
single boundary value 2 p(beta) q(beta).  The coupling was never pointwise, which is why
any pointwise Cauchy-Schwarz splitting loses; this formulation loses nothing.

SOLVING IT.  With p' and q' eliminated in favour of the momenta P = a p' + f q and
Q = b q' + e p, the Euler-Lagrange system is first order in (p,P,q,Q) with piecewise
CONSTANT coefficient matrix

    A(c) = [[0, 1/a, -f/a, 0], [g-c-e^2/b, 0, 0, e/b],
            [-e/b, 0, 0, 1/b], [0, f/a, d-c-f^2/a, 0]] ,

so each piece contributes exp(A(c) * length) and the transfer is a product of three
4x4 matrix exponentials.  The left conditions p(0) = q(0) = 0 leave a two-dimensional
solution space; propagating its basis and imposing p(pi/2) = 0 and Q(pi/2) = 0 gives a
2x2 determinant Phi(c) whose zeros are exactly the eigenvalues.

  Phi(c) = 0  first at  c* = 0.7309566...

CERTIFYING IT.  For a scalar problem Sturm oscillation makes one sign evaluation a
lower bound.  For a system the oscillation count is a Maslov index and is not as cheap.
It is not needed.  Two facts compose:

  (a)  c_1 >= 2/3, PROVED by the decoupled chain and certified in ambi_certify.py;
  (b)  Phi(c) != 0 for every c in [2/3, 73/100], certified by covering that interval
       with finitely many balls and checking that none of the enclosures contains 0.

Together they give c_1 > 73/100 with no floating-point step anywhere:

    (1/2) d^2 Q[eta]  <=  -0.73 ||eta||^2_{L^2(0,pi)} .

That is 99.9% of the sharp 0.7309566, against 91.2% for the decoupled 2/3.

A CORRECTION THIS FORCED.  Earlier turns quoted the sharp constant as 0.7323, the P1
finite-element value at m = 256.  Rayleigh-Ritz gives an UPPER bound on an eigenvalue,
and that sequence had not converged: 0.733086, 0.732285, 0.731311, 0.731247, 0.731073
at m = 128 ... 2048, decreasing towards 0.7309566.  The true sharp constant is
0.7309566, and every "sharp value" quoted before this file is an over-estimate by about
0.2%.  No conclusion changes -- every certificate was a lower bound and every FEM number
an upper bound, so the two never crossed -- but the target was mis-stated.

Usage: python3 ambi_system.py [precision_bits]
"""
from __future__ import annotations
import os, sys, math
from fractions import Fraction as Q

import numpy as np
from flint import arb, arb_mat, ctx

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from ambi_certify import certify_u, qarb
from sofa_romik2017_reference import BETA

PI2f = math.pi/2

# (a, b, g, d, e, f) on [0,beta), [beta,pi/2-beta), [pi/2-beta,pi/2)
COEF = [(Q(1), Q(2), Q(-1), Q(-2), Q(1), Q(1)),
        (Q(2), Q(2), Q(-1), Q(-1), Q(1), Q(0)),
        (Q(2), Q(1), Q(-2), Q(-1), Q(0), Q(0))]


def lengths_ball():
    """[beta, pi/2 - 2beta, beta] as arb balls, beta certified from u^3+3u=2."""
    u_lo, u_hi = certify_u()
    lo = arb((qarb(u_lo)/2).atan().lower())
    hi = arb((qarb(u_hi)/2).atan().upper())
    B = lo.union(hi)
    return [B, arb.pi()/2 - 2*B, B]


def Phi(c, lens):
    """the 2x2 shooting determinant; c may be a point ball or an interval ball."""
    Y = arb_mat([[0, 0], [1, 0], [0, 0], [0, 1]])          # p=q=0, P and Q free
    for L, (a, b, g, d, e, f) in zip(lens, COEF):
        A = arb_mat([[arb(0),               qarb(1/a),  -qarb(f/a),           arb(0)],
                     [qarb(g)-c-qarb(e*e/b), arb(0),     arb(0),              qarb(e/b)],
                     [-qarb(e/b),            arb(0),     arb(0),              qarb(1/b)],
                     [arb(0),                qarb(f/a),  qarb(d)-c-qarb(f*f/a), arb(0)]])
        Y = (A*L).exp() * Y
    return Y[0, 0]*Y[3, 1] - Y[0, 1]*Y[3, 0]               # rows p and Q at pi/2


def form_numpy(p, dp, q, dq, t):
    """M evaluated pointwise, for the equivalence cross-check."""
    out = np.zeros_like(t)
    for i, ti in enumerate(t):
        k = 0 if ti < BETA else (1 if ti < PI2f - BETA else 2)
        a, b, g, d, e, f = [float(x) for x in COEF[k]]
        out[i] = (a*dp[i]**2 + b*dq[i]**2 + g*p[i]**2 + d*q[i]**2
                  + 2*e*p[i]*dq[i] + 2*f*q[i]*dp[i])
    return out


def main():
    prec = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    ctx.prec = prec
    lens = lengths_ball()
    print("THE SHARP CONCAVITY CONSTANT, AS A 2x2 SYSTEM   (arb, %d bits)\n" % prec)

    print("(1) EQUIVALENCE CHECK: the system form must equal the hat-basis Hessian.")
    from ambi_hessian import Hats, gl_split, mass_stiff, PI, PI2
    from ambi_concavity import hess_sets
    rng = np.random.default_rng(11)
    for m in (64, 128):
        B, Mh = hess_sets(m, [(0.0, BETA)], [(0.0, PI2 - BETA)])
        nd = np.array(sorted(set(B.nodes.tolist()) | {BETA, PI2 - BETA, PI2}))
        nd = nd[(nd >= 0) & (nd <= PI2)]
        T, W = gl_split(nd, 12)
        P0, D0 = B.val_grad(T); P1, D1 = B.val_grad(T + PI2)
        worst = 0.0
        for _ in range(3):
            v = rng.standard_normal(B.dim)
            p, dp = P0 @ v, D0 @ v
            q, dq = P1 @ v, D1 @ v
            sysval = -float(W @ form_numpy(p, dp, q, dq, T))       # int L = -int M
            worst = max(worst, abs(sysval - v @ Mh @ v)/max(1.0, abs(v @ Mh @ v)))
        print(f"      m = {m:4d}   max relative discrepancy over 3 random eta: {worst:.2e}")
    print("      (the system is a re-indexing, not an approximation)\n")

    print("(2) THE SHOOTING DETERMINANT.  Zeros are exactly the eigenvalues.")
    print(f"      {'c':>10} {'Phi(c)':>18}   contains 0?")
    for lab, c in (("0", Q(0)), ("1/2", Q(1, 2)), ("2/3", Q(2, 3)), ("0.72", Q(18, 25)),
                   ("0.73", Q(73, 100)), ("0.7309", Q(7309, 10000)),
                   ("0.7310", Q(731, 1000)), ("0.74", Q(37, 50))):
        v = Phi(qarb(c), lens)
        print(f"      {lab:>10} {float(arb(v.mid())):+18.10f}   {v.contains(0)}")
    lo, hi = Q(7309, 10000), Q(731, 1000)
    for _ in range(60):
        mid = (lo + hi)/2
        if float(arb(Phi(qarb(mid), lens).mid())) > 0: lo = mid
        else: hi = mid
    print(f"\n      c* = {float(lo):.12f}   (bracketed by a sign change)\n")

    print("(3) THE CERTIFICATE.  Sturm oscillation is a Maslov index for systems, and is")
    print("    not needed: (a) c_1 >= 2/3 is PROVED by the decoupled chain, certified in")
    print("    ambi_certify.py; (b) cover [2/3, 73/100] and show Phi vanishes nowhere.")
    target = Q(73, 100)
    for N in (20, 60, 200, 600):
        bad = [i for i in range(N)
               if Phi(qarb(Q(2, 3) + (target - Q(2, 3))*Q(i, N))
                      .union(qarb(Q(2, 3) + (target - Q(2, 3))*Q(i+1, N))), lens).contains(0)]
        print(f"      N = {N:4d} subintervals:  enclosures containing 0: {len(bad)}"
              + ("   CERTIFIED" if not bad else "   refine"))
        if not bad:
            ok = True
            break
    else:
        ok = False
    print()

    print("(4) NEGATIVE CONTROL (I12).  The same covering must FAIL past the eigenvalue.")
    over = Q(74, 100)
    badN = [i for i in range(200)
            if Phi(qarb(Q(2, 3) + (over - Q(2, 3))*Q(i, 200))
                   .union(qarb(Q(2, 3) + (over - Q(2, 3))*Q(i+1, 200))), lens).contains(0)]
    print(f"      covering [2/3, 0.74] at N = 200: enclosures containing 0: {len(badN)}")
    print(f"      -> {'correctly refuses (the eigenvalue is inside)' if badN else '*** SPURIOUS ***'}\n")

    if ok and badN:
        print("  CERTIFIED.  c_1 > 73/100, hence")
        print("      (1/2) d^2 Q[eta] <= -0.73 ||eta||^2_{L^2(0,pi)}   PROVED")
        print(f"  sharp value {float(lo):.7f}; the certificate captures "
              f"{100*0.73/float(lo):.1f}% of it (decoupled 2/3 captured "
              f"{100*(2/3)/float(lo):.1f}%).")
        return 0
    print("  *** NOT CERTIFIED ***")
    return 1


if __name__ == "__main__":
    sys.exit(main())
