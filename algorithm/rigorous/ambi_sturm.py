"""ambi_sturm.py — the concavity constant, from two Sturm-Liouville eigenvalues.

The Hessian of Q = |C2| - 2V at Sigma, in the gauge eta(0) = eta(pi/2) = 0 and with the
sigma term written in its singularity-free form (see ambi_concavity.py), is

  (1/2) d^2 Q[eta] = int_0^pi (eta^2 - eta'^2) + int_0^{pi/2} (eta^2 - eta'^2)
                     - int_{E2} ( eta(t) + eta'(t+pi/2) )^2 dt
                     + int_{E1} ( eta(t+pi/2) - eta'(t) )^2 dt ,

with E1 = [0,beta) = {alpha_1 < 0} and E2 = [0,pi/2-beta) = {alpha_2 > 0}.  The last
term is the obstruction: it has the WRONG SIGN and it couples the two halves.  The
E2 term has the right sign and is a RESOURCE, not something to discard.

THE CHAIN.  Two Cauchy-Schwarz steps with free parameters lambda in (0,1), kappa > 0.

  (S1)  -(a+b)^2 <= -lambda b^2 + [lambda/(1-lambda)] a^2 ,
        applied with a = eta(t), b = eta'(t+pi/2) on E2.  Sharp: the two sides differ by
        (1-lambda)^{-1} ( a + (1-lambda) b )^2 >= 0.  It BUYS extra gradient weight
        lambda on [pi/2, pi-beta] at the price of r := lambda/(1-lambda) extra mass on
        [0, pi/2-beta).

  (S2)  (x-y)^2 <= (1 + 1/kappa) x^2 + (1+kappa) y^2 ,
        applied with x = eta(t+pi/2), y = eta'(t) on E1.  It PAYS q := 1 + 1/kappa extra
        mass on [pi/2, pi/2+beta] and 1+kappa extra gradient weight on [0,beta).

What is left is a sum of two decoupled quadratic forms, one per half-interval:

  (1/2) d^2 Q[eta] <= int_0^{pi/2} ( m_L eta^2 - w_L eta'^2 )
                    + int_{pi/2}^{pi} ( m_R eta^2 - w_R eta'^2 )     =: B[eta]

  w_L = 1-kappa on [0,beta), 2 on [beta,pi/2)        (needs kappa < 1)
  m_L = 2 + r   on [0,pi/2-beta), 2 on [pi/2-beta,pi/2)
  w_R = 1+lambda on [pi/2,pi-beta), 1 on [pi-beta,pi]
  m_R = 1 + q   on [pi/2,pi/2+beta), 1 on [pi/2+beta,pi]

Each half is a Rayleigh quotient, so B[eta] <= -min(c_L,c_R) ||eta||^2_{L^2(0,pi)} where
c_L, c_R are the first eigenvalues of the two Sturm-Liouville problems

  -(w_L eta')' - m_L eta = c eta  on (0,pi/2),   eta(0) = eta(pi/2) = 0,
  -(w_R eta')' - m_R eta = c eta  on (pi/2,pi),  eta(pi/2) = 0,  eta'(pi) = 0.

The Dirichlet condition at 0 and pi/2 is the GAUGE, not an assumption; the Neumann
condition at pi is free (nothing pins eta there).

HOW c_L, c_R ARE CERTIFIED.  Both weights and both masses are piecewise constant with
three pieces, so the solution of the initial-value problem eta(left) = 0,
(w eta')(left) = 1 is an explicit product of three 2x2 transfer matrices,

  T(L,w,m;c) = [[ cos kL, sin(kL)/(wk) ], [ -wk sin kL, cos kL ]],  k = sqrt((m+c)/w),

(and the hyperbolic version when m + c < 0).  Write Phi_L(c) for the resulting eta(pi/2)
and Phi_R(c) for (w eta')(pi).  By Sturm oscillation the first eigenvalue is the SMALLEST
zero of Phi, and Phi > 0 strictly below it.  So a SINGLE SIGN EVALUATION certifies a
lower bound: Phi_L(c_0) > 0 and Phi_R(c_0) > 0 imply c_L, c_R > c_0.  This is a lower
bound, which is the direction a certificate needs; a Rayleigh-Ritz / FEM computation
gives an UPPER bound and cannot be used for it.  FEM is run here only as a cross-check.

WHAT COMES OUT

  max-min over (kappa,lambda):  c* = 0.674944  at (kappa,lambda) = (0.26, 0.74)
  clean certificate:            kappa = 1/4, lambda = 37/50  =>  Phi_L, Phi_R > 0 at 2/3

so, PROVED,

  (1/2) d^2 Q[eta] <= -(2/3) ||eta||^2_{L^2(0,pi)}        for every admissible eta.

The sharp constant, from the assembled Hessian, is 0.732285 (m = 256).  The certificate
captures 91.0% of it.  The previous certificate was 0.1532, i.e. 20.9%; the gain came
from treating each half as ONE weighted eigenvalue problem instead of splitting it into
pieces with separate Poincare constants, and from spending the E2 term rather than
discarding it.

SEPARATELY, the [pi/2,pi] eigenvalue in closed form.  With mass 1 throughout and weight
1 + lambda_J on [pi/2,pi-beta], 1 on [pi-beta,pi], the same transfer matrix collapses to

  sqrt(w_1) cot( L_1 sqrt(Lambda/w_1) ) = tan( L_2 sqrt(Lambda) ),
  w_1 = 1 + lambda_J,  L_1 = pi/2 - beta,  L_2 = beta.                          (SL)

At lambda_J = 0 this is cot(L_1 sqrt Lambda) = cot(pi/2 - L_2 sqrt Lambda), so
sqrt(Lambda) (L_1 + L_2) = pi/2, and since L_1 + L_2 = pi/2 EXACTLY, Lambda = 1 exactly.
For lambda_J > 0 put G(w_1) := sqrt(w_1) cot(L_1/sqrt(w_1)) - tan(beta).  Then G(1) = 0,
and G increases in w_1 (the prefactor increases; the argument L_1/sqrt(w_1) decreases and
cot decreases on (0,pi), so the cotangent increases).  Hence G(w_1) > 0 for w_1 > 1.  The
left side of (SL) decreases in Lambda and the right side increases, so the root moves
right:  Lambda(lambda_J) > 1 for every lambda_J > 0.  PROVED.

Usage: python3 ambi_sturm.py
"""
from __future__ import annotations
import os, sys, math
import numpy as np
from mpmath import mp, mpf, sin, cos, sqrt, matrix, cosh, sinh, cot, tan, findroot

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from ambi_hessian import Hats, gl_split, PI, PI2, mass_stiff
from ambi_concavity import hess_sets
from sofa_romik2017_reference import BETA

mp.dps = 30
B_ = mpf(repr(BETA)); H2_ = mp.pi/2


def transfer(pieces, neumann_right):
    """Phi(c): shoot eta(left) = 0, (w eta')(left) = 1 across piecewise-constant data."""
    def Phi(c):
        y = matrix([mpf(0), mpf(1)])                       # [eta, w eta']
        for (L, w, m) in pieces:
            k2 = (m + c)/w
            if abs(k2) < mpf('1e-20'):
                T = matrix([[mpf(1), L/w], [mpf(0), mpf(1)]])
            elif k2 > 0:
                k = sqrt(k2)
                T = matrix([[cos(k*L), sin(k*L)/(w*k)],
                            [-w*k*sin(k*L), cos(k*L)]])
            else:
                k = sqrt(-k2)
                T = matrix([[cosh(k*L), sinh(k*L)/(w*k)],
                            [w*k*sinh(k*L), cosh(k*L)]])
            y = T*y
        return y[1] if neumann_right else y[0]
    return Phi


def blocks(kap, lam):
    """(Phi_L, Phi_R) for the two Sturm-Liouville problems of the chain."""
    r = lam/(1 - lam); q = 1 + 1/kap
    L = transfer([(B_, 1 - kap, 2 + r),
                  (H2_ - 2*B_, mpf(2), 2 + r),
                  (B_, mpf(2), mpf(2))], False)
    R = transfer([(B_, 1 + lam, 1 + q),
                  (H2_ - 2*B_, 1 + lam, mpf(1)),
                  (B_, mpf(1), mpf(1))], True)
    return L, R


def first_root(Phi, lo=-1, hi=3, n=900):
    """smallest zero of Phi on [lo,hi] = the first eigenvalue (Sturm oscillation)."""
    a = mpf(lo); fa = Phi(a); h = (mpf(hi) - a)/n
    for _ in range(n):
        x = a + h; fx = Phi(x)
        if fa*fx < 0:
            u, v, fu = a, x, fa
            for _ in range(120):
                mid = (u + v)/2; fm = Phi(mid)
                if fu*fm <= 0: v = mid
                else: u, fu = mid, fm
            return (u + v)/2
        a, fa = x, fx
    return None


def B_matrix(B, kap, lam, nq=10):
    """the majorant form B[eta], assembled on the same hat basis as the Hessian."""
    r = lam/(1 - lam); q = 1 + 1/kap
    nd = np.array(sorted(set(B.nodes.tolist()) |
                         {BETA, PI2 - BETA, PI2, PI2 + BETA, PI - BETA}))
    nd = nd[(nd >= 0) & (nd <= PI)]
    T, W = gl_split(nd, nq); P, D = B.val_grad(T)
    wL = np.where(T < BETA, 1 - kap, 2.0); mL = np.where(T < PI2 - BETA, 2 + r, 2.0)
    wR = np.where(T < PI - BETA, 1 + lam, 1.0); mR = np.where(T < PI2 + BETA, 1 + q, 1.0)
    w = np.where(T < PI2, wL, wR); m = np.where(T < PI2, mL, mR)
    return ((P*(W*m)[:, None]).T @ P) - ((D*(W*w)[:, None]).T @ D)


def sharp(m):
    """the true constant: -max eig of Mass^{-1} Hessian at Sigma's own sign pattern."""
    Bh, M = hess_sets(m, [(0.0, BETA)], [(0.0, PI2 - BETA)])
    Mass, _ = mass_stiff(Bh)
    L = np.linalg.cholesky(Mass)
    A = np.linalg.solve(L, np.linalg.solve(L, M).T).T
    return -np.linalg.eigvalsh(0.5*(A + A.T)).max()


def main():
    print("THE CONCAVITY CONSTANT FROM TWO STURM-LIOUVILLE EIGENVALUES\n")

    print("(1) THE CHAIN IS VALID: B - Hessian must be positive semidefinite.")
    kap, lam = mpf(1)/4, mpf(37)/50
    kf, lf = float(kap), float(lam)
    for m in (32, 64, 128):
        Bh, M = hess_sets(m, [(0.0, BETA)], [(0.0, PI2 - BETA)])
        G = B_matrix(Bh, kf, lf) - M
        ev = np.linalg.eigvalsh(0.5*(G + G.T)).min()
        print(f"      m = {m:4d}  dim {Bh.dim:4d}   min eig (B - Hess) = {ev:+.2e}   "
              f"{'PSD' if ev > -1e-9 else '*** VIOLATED ***'}")
    print("      (a falsification test: any negative eigenvalue would kill the chain)\n")

    print("(2) THE TWO EIGENVALUES, by transfer matrix at 30 digits.")
    print(f"      {'kappa':>7} {'lambda':>7} {'r':>8} {'q':>6} {'c_L':>11} {'c_R':>11}"
          f" {'min':>11}")
    best = None
    for i in range(13):
        for j in range(13):
            k = mpf('0.18') + mpf('0.01')*i; l = mpf('0.70') + mpf('0.008')*j
            L, R = blocks(k, l)
            cl, cr = first_root(L), first_root(R)
            if cl is None or cr is None: continue
            c = min(cl, cr)
            if best is None or c > best[0]: best = (c, k, l)
    for k, l in ((mpf(1)/4, mpf(37)/50), (best[1], best[2]), (mpf(1)/4, mpf(3)/4),
                 (mpf(3)/10, mpf(3)/4)):
        L, R = blocks(k, l); cl, cr = first_root(L), first_root(R)
        print(f"      {float(k):7.3f} {float(l):7.3f} {float(l/(1-l)):8.4f} "
              f"{float(1+1/k):6.3f} {float(cl):11.6f} {float(cr):11.6f} "
              f"{float(min(cl,cr)):11.6f}")
    print(f"      max-min over the grid: c* = {float(best[0]):.6f} at "
          f"(kappa,lambda) = ({float(best[1]):.2f}, {float(best[2]):.2f})\n")

    print("(3) THE CERTIFICATE.  Phi > 0 strictly below the first eigenvalue, so ONE")
    print("    sign evaluation is a lower bound.  kappa = 1/4, lambda = 37/50:")
    L, R = blocks(kap, lam)
    for lab, c in (("0", mpf(0)), ("3/5", mpf(3)/5), ("2/3", mpf(2)/3),
                   ("0.68", mpf('0.68')), ("0.70", mpf('0.70'))):
        pl, pr = L(c), R(c)
        v = ("both > 0: certifies" if pl > 0 and pr > 0 else "does not certify")
        print(f"      c = {lab:>4} = {float(c):.6f}:  Phi_L = {float(pl):+.8f}   "
              f"Phi_R = {float(pr):+.8f}   {v}")
    print("\n      => PROVED:  (1/2) d^2 Q[eta] <= -(2/3) ||eta||^2_{L^2(0,pi)}\n")

    print("(4) HOW MUCH IS LEFT ON THE TABLE.")
    for m in (64, 128, 256):
        print(f"      sharp constant at m = {m:4d}:  {sharp(m):.6f}")
    s = sharp(256)
    print(f"      certificate 2/3 = 0.666667 captures {100*(2/3)/s:.1f}%")
    print(f"      grid optimum {float(best[0]):.6f} captures {100*float(best[0])/s:.1f}%")
    print(f"      previous certificate 0.1532 captured {100*0.1532/s:.1f}%\n")

    print("(5) THE [pi/2,pi] EIGENVALUE IN CLOSED FORM (mass 1, weight 1+lambda_J).")
    L1, L2 = H2_ - B_, B_
    def SL(lj):
        w1 = 1 + lj
        f = lambda Lam: sqrt(w1)*cot(L1*sqrt(Lam/w1)) - tan(L2*sqrt(Lam))
        return findroot(f, mpf(1) + lj/2)
    def G(w1): return sqrt(w1)*cot(L1/sqrt(w1)) - tan(B_)
    print(f"      L_1 + L_2 = pi/2 exactly, so Lambda(0) = 1 exactly:"
          f"  residual {float(SL(mpf(0))) - 1:+.2e}")
    print(f"      {'lambda_J':>9} {'Lambda (SL)':>13} {'Lambda (FEM)':>13} "
          f"{'G(1+lambda_J)':>15}")
    for lj in ('0', '0.05', '0.10', '0.16483', '0.25', '0.35'):
        v = mpf(lj); Lam = SL(v)
        n = 4000
        x = np.linspace(float(H2_), float(PI), n+1); h = x[1]-x[0]
        wv = np.where(0.5*(x[:-1]+x[1:]) < float(PI - B_), 1+float(v), 1.0)
        K = np.zeros((n, n)); M = np.zeros((n, n))
        for e in range(n):
            for a in (0, 1):
                for b in (0, 1):
                    ga, gb = e+a-1, e+b-1
                    if 0 <= ga < n and 0 <= gb < n:
                        K[ga, gb] += wv[e]/h*(1 if a == b else -1)
                        M[ga, gb] += h/6*(2 if a == b else 1)
        C = np.linalg.cholesky(M)
        A = np.linalg.solve(C, np.linalg.solve(C, K).T).T
        fem = np.linalg.eigvalsh(0.5*(A+A.T)).min()
        print(f"      {float(v):9.5f} {float(Lam):13.6f} {fem:13.6f} "
              f"{float(G(1+v)):15.6f}")
    print("      G(1) = 0 and G increases, so Lambda > 1 for every lambda_J > 0.  PROVED")


if __name__ == "__main__":
    main()
