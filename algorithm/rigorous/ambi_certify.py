"""ambi_certify.py — the concavity constant 2/3, in RIGOROUS arithmetic.

Theorem "Concavity, sharp order" ends in two sign evaluations,

    Phi_L(2/3) > 0    and    Phi_R(2/3) > 0 ,

of the shooting functions of two Sturm-Liouville problems.  ambi_sturm.py computes
them at 30 working digits.  That is floating point, hence EVIDENCE, not proof
(Rule 7).  This script replaces both by certified enclosures, so that the constant
2/3 carries the label PROVED with nothing floating-point left in the chain.

Three things have to be made rigorous, not one.

(1) THE CONSTANT beta.  It is not a decimal but the root of a cubic: tan(beta) = u/2
    with u^3 + 3u = 2.  Certified by EXACT RATIONAL bisection --- f(u) = u^3+3u-2 is
    strictly increasing, so a sign change on a rational interval is a proof of
    enclosure --- followed by a ball-arithmetic arctangent.

(2) THE TRANSFER MATRICES.  Every weight and mass is an exact rational at
    kappa = 1/4, lambda = 37/50, c = 2/3, so each k^2 = (m+c)/w is exact:

      LEFT   pieces [0,beta], [beta,pi/2-beta], [pi/2-beta,pi/2]
             w = 3/4, 2, 2        m = 63/13, 63/13, 2
             k^2 = 860/117, 215/78, 4/3
      RIGHT  pieces [pi/2,pi/2+beta], [pi/2+beta,pi-beta], [pi-beta,pi]
             w = 87/50, 87/50, 1  m = 6, 1, 1
             k^2 = 1000/261, 250/261, 5/3

    The only inexact inputs are the three lengths beta, pi/2-2beta, beta and the
    trigonometric functions of k*length.  Both are handled in arb ball arithmetic
    with rigorous error bounds, and cross-checked in mpmath's independent interval
    arithmetic, with beta re-certified there from tan(beta) = u/2 alone.

(3) THE OSCILLATION ARGUMENT.  `Phi(2/3) > 0` gives `c_1 > 2/3` only if 2/3 also
    lies below the SECOND eigenvalue: Phi is positive on (-inf, c_1), negative on
    (c_1, c_2), positive again on (c_2, c_3), so a positive value alone does not
    locate 2/3.  The min-max principle closes this.  Since
    int w eta'^2 >= w_min int eta'^2 and -int m eta^2 >= -m_max int eta^2,

        c_k  >=  w_min * lambda_k  -  m_max ,

    with lambda_k the constant-coefficient eigenvalues on an interval of length
    pi/2: (2k)^2 for Dirichlet-Dirichlet, (2k-1)^2 for Dirichlet-Neumann.  Hence

        LEFT   c_2 >= (3/4)(16) - 63/13 = 7.153...  >  2/3
        RIGHT  c_2 >= (1)(9)   - 6      = 3         >  2/3

    so 2/3 is below c_2 in both, and Phi(2/3) > 0 forces 2/3 < c_1.  (The same
    bound at k = 1 gives -1.84 and -5, useless: the second eigenvalue is far enough
    away to be reachable crudely while the first is not.  That asymmetry is the
    whole reason the transfer matrix is needed at all.)

Usage: python3 ambi_certify.py [precision_bits]
"""
from __future__ import annotations
import sys
from fractions import Fraction as Q

from flint import arb, ctx


# ----------------------------------------------------------------- (1) beta

def certify_u(digits=60):
    """rational [lo,hi] enclosing the root of u^3+3u-2, by exact bisection."""
    f = lambda x: x*x*x + 3*x - 2
    lo, hi = Q(0), Q(1)
    assert f(lo) < 0 < f(hi)
    for _ in range(4*digits):
        mid = (lo + hi)/2
        if f(mid) < 0: lo = mid
        else: hi = mid
    return lo, hi


def beta_ball(u_lo, u_hi):
    """beta = arctan(u/2) as an arb ball containing the true value."""
    t_lo = arb(u_lo.numerator)/arb(u_lo.denominator)/2
    t_hi = arb(u_hi.numerator)/arb(u_hi.denominator)/2
    b_lo, b_hi = t_lo.atan(), t_hi.atan()
    lo = arb(b_lo.lower()); hi = arb(b_hi.upper())
    return lo.union(hi)


# ------------------------------------------------- (2) the transfer matrices

def qarb(q: Q) -> arb:
    return arb(q.numerator)/arb(q.denominator)


def phi(pieces, neumann_right):
    """(eta, w eta') at the right endpoint, from eta = 0, w eta' = 1 at the left.

    pieces: list of (length : arb, w : Fraction, k2 : Fraction) with k2 = (m+c)/w."""
    y0, y1 = arb(0), arb(1)                      # eta, w eta'
    for (L, w, k2) in pieces:
        k = qarb(k2).sqrt()
        wk = qarb(w)*k
        kl = k*L
        c_, s_ = kl.cos(), kl.sin()
        y0, y1 = c_*y0 + (s_/wk)*y1, (-wk*s_)*y0 + c_*y1
    return y1 if neumann_right else y0


# kappa = 1/4, lambda = 37/50  =>  r = 37/13, q = 5.  (length, w, m) per piece.
WL = [(Q(3,4), Q(2)+Q(37,13)), (Q(2), Q(2)+Q(37,13)), (Q(2), Q(2))]
WR = [(Q(87,50), Q(6)), (Q(87,50), Q(1)), (Q(1), Q(1))]


def blocks(B, half_pi, c=Q(2,3)):
    """the two problems at kappa = 1/4, lambda = 37/50, at the trial value c."""
    mid = half_pi - 2*B
    lens = [B, mid, B]
    L = [(lens[i], w, (m + c)/w) for i, (w, m) in enumerate(WL)]
    R = [(lens[i], w, (m + c)/w) for i, (w, m) in enumerate(WR)]
    return L, R


# ------------------------------------------------------ independent recheck

def mpmath_recheck(u_lo, u_hi):
    """mpmath's interval arithmetic, with beta re-certified from tan(beta) = u/2.

    mpmath.iv has no arctangent, so beta is enclosed the other way round: pick
    rational bounds and verify tan(b_lo) < u/2 < tan(b_hi) in interval arithmetic.
    Since tan is increasing on (0,pi/2) that is a proof of enclosure, and it uses
    NO shared code with the arb path."""
    from mpmath import iv
    iv.dps = 50
    b_lo, b_hi = Q(2896538208173208, 10**16), Q(2896538208173210, 10**16)
    t_lo = iv.tan(iv.mpf([float(b_lo), float(b_lo)]))
    t_hi = iv.tan(iv.mpf([float(b_hi), float(b_hi)]))
    half_u_lo = iv.mpf([float(u_lo)/2, float(u_lo)/2])
    half_u_hi = iv.mpf([float(u_hi)/2, float(u_hi)/2])
    ok = (t_lo.b < half_u_lo.a) and (t_hi.a > half_u_hi.b)
    B = iv.mpf([float(b_lo), float(b_hi)])
    mid = iv.pi/2 - 2*B

    def ivphi(pieces, neumann):
        y0, y1 = iv.mpf(0), iv.mpf(1)
        for (L, w, k2) in pieces:
            k = iv.sqrt(iv.mpf(k2.numerator)/iv.mpf(k2.denominator))
            wk = (iv.mpf(w.numerator)/iv.mpf(w.denominator))*k
            kl = k*L
            c_, s_ = iv.cos(kl), iv.sin(kl)
            y0, y1 = c_*y0 + (s_/wk)*y1, (-wk*s_)*y0 + c_*y1
        return y1 if neumann else y0

    c = Q(2,3); lens = [B, mid, B]
    Lp = [(lens[i], w, (m + c)/w) for i, (w, m) in enumerate(WL)]
    Rp = [(lens[i], w, (m + c)/w) for i, (w, m) in enumerate(WR)]
    return ok, ivphi(Lp, False), ivphi(Rp, True)


# ------------------------------------------------------------------- report

def main():
    prec = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    ctx.prec = prec
    print("THE CONSTANT 2/3, IN RIGOROUS ARITHMETIC   (arb, prec = %d bits)\n" % prec)

    print("(1) beta, from the cubic rather than from a decimal")
    u_lo, u_hi = certify_u()
    f = lambda x: x*x*x + 3*x - 2
    print(f"      u^3+3u-2 at the rational endpoints:  {float(f(u_lo)):+.3e}  {float(f(u_hi)):+.3e}")
    print(f"      strictly increasing, so u is enclosed to width {float(u_hi-u_lo):.2e}")
    B = beta_ball(u_lo, u_hi)
    print(f"      beta = arctan(u/2) = {B}")
    print(f"      radius {B.rad()}\n")

    half_pi = arb.pi()/2
    L, R = blocks(B, half_pi)
    print("(2) the two shooting functions at c = 2/3, in ball arithmetic")
    print("      every weight and mass is an exact rational; k^2 = (m+c)/w is exact")
    PL, PR = phi(L, False), phi(R, True)
    okL, okR = PL.lower() > 0, PR.lower() > 0
    print(f"      Phi_L(2/3) = {PL}")
    print(f"                   lower bound {arb(PL.lower())}   "
          f"{'STRICTLY POSITIVE' if okL else '*** NOT CERTIFIED ***'}")
    print(f"      Phi_R(2/3) = {PR}")
    print(f"                   lower bound {arb(PR.lower())}   "
          f"{'STRICTLY POSITIVE' if okR else '*** NOT CERTIFIED ***'}\n")

    print("(3) 2/3 is below the SECOND eigenvalue too, by min-max")
    print("      c_k >= w_min * lambda_k - m_max,  lambda_k = (2k)^2 (DD), (2k-1)^2 (DN)")
    cL2 = Q(3,4)*16 - Q(63,13)
    cR2 = Q(1)*9 - Q(6)
    print(f"      LEFT   c_2 >= (3/4)(16) - 63/13 = {float(cL2):.6f}   > 2/3: {cL2 > Q(2,3)}")
    print(f"      RIGHT  c_2 >= (1)(9) - 6        = {float(cR2):.6f}   > 2/3: {cR2 > Q(2,3)}")
    cL1 = Q(3,4)*4 - Q(63,13); cR1 = Q(1)*1 - Q(6)
    print(f"      (the same bound at k=1 gives {float(cL1):.3f} and {float(cR1):.3f}: useless,")
    print(f"       which is why the transfer matrix is needed for c_1 and not for c_2)\n")

    print("(4) INDEPENDENT RECHECK in mpmath interval arithmetic")
    print("      beta re-certified from tan(beta) = u/2, sharing no code with (1)")
    okb, mL, mR = mpmath_recheck(u_lo, u_hi)
    print(f"      tan(b_lo) < u/2 < tan(b_hi) verified: {okb}")
    print(f"      Phi_L(2/3) in [{float(mL.a):+.12f}, {float(mL.b):+.12f}]   "
          f"{'positive' if mL.a > 0 else 'FAILED'}")
    print(f"      Phi_R(2/3) in [{float(mR.a):+.12f}, {float(mR.b):+.12f}]   "
          f"{'positive' if mR.a > 0 else 'FAILED'}\n")

    print("(5) NEGATIVE CONTROL (I12).  The certificate must FAIL above the true")
    print("    eigenvalues c_L = 0.6778..., c_R = 0.6741...  If it certifies there,")
    print("    it is certifying nothing.")
    print(f"      {'c':>8} {'Phi_L lower':>16} {'Phi_R lower':>16}   verdict")
    for cc in (Q(0), Q(3,5), Q(2,3), Q(17,25), Q(7,10), Q(3,4)):
        Lc, Rc = blocks(B, half_pi, cc)
        pl, pr = phi(Lc, False), phi(Rc, True)
        v = "certifies" if (pl.lower() > 0 and pr.lower() > 0) else "correctly refuses"
        print(f"      {str(cc):>8} {float(arb(pl.lower())):+16.9f} "
              f"{float(arb(pr.lower())):+16.9f}   {v}")
    Lc, Rc = blocks(B, half_pi, Q(17,25))
    neg_ok = not (phi(Lc, False).lower() > 0 and phi(Rc, True).lower() > 0)
    print(f"      c = 17/25 = 0.68 is above c_R: refused as it must be -> {neg_ok}\n")

    good = neg_ok and okL and okR and cL2 > Q(2,3) and cR2 > Q(2,3) and okb and mL.a > 0 and mR.a > 0
    if good:
        print("  CERTIFIED.  c_L > 2/3 and c_R > 2/3, hence")
        print("      (1/2) d^2 Q[eta] <= -(2/3) ||eta||^2_{L^2(0,pi)}")
        print("  with no floating-point step anywhere in the chain.   PROVED")
    else:
        print("  *** NOT CERTIFIED ***")
    return 0 if good else 1


if __name__ == "__main__":
    sys.exit(main())
