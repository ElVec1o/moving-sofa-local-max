"""ambi_precision.py — Q(Sigma) = A_R* at 40 digits (item 4).

The identity chain established in the note is

    |Sigma| = |C2| - 2|N|,     |N| = V,     |C2| = int_0^pi (H^2 - H'^2) dtheta - H(0) - H(pi)

so  Q(Sigma) := |C2| - 2V  should equal  A_R* = u^2 + 1 + arctan(u/2)  with u^3 + 3u = 2.
The two sides share no computation, so this is a real cross-check.  In double precision
it held to 5e-13; here it is redone with mpmath at 60 working digits so that the residual
is limited by the mathematics and not by the arithmetic.

This is still floating point, not an interval enclosure -- Rule 7 -- but a 40-digit
agreement between two independent closed-form routes is much stronger evidence than a
13-digit one, and it rules out the possibility that the earlier agreement was a
coincidence of double-precision rounding.

CONSTANTS, all from closed forms:
    u  : u^3 + 3u = 2                       beta = arctan(u/2)
    a1 = sqrt(4+u^2)/(4u)                   (equivalently 4 a1 sin beta = 1)
    f1 = (4/3) a1 cos beta / ( cos(beta/2) + (1-sqrt2) sin(beta/2) )
    f2 = (1-sqrt2) f1
    kappa1 = (1-a1, 1/2), kappa6 = (1-(4/3)a1, 1/2), kappa5 = (1-(5/3)a1, 1/2)

PATHS, in complex form (J <-> i):
    SOL1  z = a1 e^{2it}          - (1 + i/2) e^{it} + kappa1     on [0, beta)
    SOL6  z = (f1 - i f2) e^{3it/2} - (1 + i) e^{it} + kappa6     on [beta, pi/2-beta]
    SOL5  z = a1 e^{2it}          - (1/2 + i) e^{it} + kappa5     on (pi/2-beta, pi/2]

The only delicate point is sigma = (F-1) tan t + G - 1 at t = pi/2, where F-1 -> 0 and
tan t -> infinity.  On the last phase F - 1 = A cos t + (1/2) sin t - 1/2 with
A = 1 - (2/3) a1, and (1 - sin t)/cos t = tan(pi/4 - t/2), so

    sigma = A sin t - (1/2) sin t * tan(pi/4 - t/2) + G - 1,

which is smooth up to and including t = pi/2.  Used there in place of the tan form.

Usage: python3 ambi_precision.py [digits]
"""
from __future__ import annotations
import sys
import mpmath as mp


def constants():
    u = mp.findroot(lambda x: x**3 + 3*x - 2, mp.mpf("0.596"))
    beta = mp.atan(u/2)
    a1 = mp.sqrt(4 + u**2)/(4*u)
    s2 = mp.sqrt(2)
    f1 = (mp.mpf(4)/3*a1*mp.cos(beta) /
          (mp.cos(beta/2) + (1 - s2)*mp.sin(beta/2)))
    f2 = (1 - s2)*f1
    return u, beta, a1, f1, f2


def make_path(a1, f1, f2, beta):
    K1 = mp.mpc(1 - a1, mp.mpf(1)/2)
    K6 = mp.mpc(1 - mp.mpf(4)/3*a1, mp.mpf(1)/2)
    K5 = mp.mpc(1 - mp.mpf(5)/3*a1, mp.mpf(1)/2)
    c6 = mp.mpc(f1, -f2)

    def z(t):
        if t < beta:
            return a1*mp.e**(2j*t) - mp.mpc(1, mp.mpf(1)/2)*mp.e**(1j*t) + K1
        if t <= mp.pi/2 - beta:
            return c6*mp.e**(mp.mpf(3)/2*1j*t) - mp.mpc(1, 1)*mp.e**(1j*t) + K6
        return a1*mp.e**(2j*t) - mp.mpc(mp.mpf(1)/2, 1)*mp.e**(1j*t) + K5

    def dz(t):
        if t < beta:
            return 2j*a1*mp.e**(2j*t) - 1j*mp.mpc(1, mp.mpf(1)/2)*mp.e**(1j*t)
        if t <= mp.pi/2 - beta:
            return (mp.mpf(3)/2*1j*c6*mp.e**(mp.mpf(3)/2*1j*t)
                    - 1j*mp.mpc(1, 1)*mp.e**(1j*t))
        return 2j*a1*mp.e**(2j*t) - 1j*mp.mpc(mp.mpf(1)/2, 1)*mp.e**(1j*t)
    return z, dz


def main():
    dig = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    mp.mp.dps = dig
    u, beta, a1, f1, f2 = constants()
    z, dz = make_path(a1, f1, f2, beta)
    P2 = mp.pi/2
    A = 1 - mp.mpf(2)/3*a1

    def FG(t):
        """F(t)-1 = <c,mu_t>, G(t)-1 = <c,nu_t>"""
        w = mp.e**(-1j*t)*z(t)
        return mp.re(w), mp.im(w)

    def arms(t):
        w = mp.e**(-1j*t)*dz(t)
        return -mp.re(w), mp.im(w)          # alpha_1, alpha_2

    def sigma(t):
        Fm1, Gm1 = FG(t)
        if t > P2 - beta:                    # smooth form, no tan singularity
            return (A*mp.sin(t) - mp.sin(t)*mp.tan(mp.pi/4 - t/2)/2 + Gm1)
        return Fm1*mp.tan(t) + Gm1

    def vint(t):
        a1t, a2t = arms(t)
        sg = sigma(t)
        return (mp.mpf(1)/2*max(a2t, mp.mpf(0))**2
                + mp.mpf(1)/2*(sg - a1t)**2
                - mp.mpf(1)/2*max(-a1t, mp.mpf(0))**2)

    V = (mp.quad(vint, [0, beta]) + mp.quad(vint, [beta, P2 - beta])
         + mp.quad(vint, [P2 - beta, P2]))

    def H(th):
        if th <= P2:
            return FG(th)[0] + 1
        return FG(th - P2)[1] + 1

    def dH(th):
        if th <= P2:
            a1t, _ = arms(th)
            return -a1t + FG(th)[1]
        s = th - P2
        _, a2t = arms(s)
        return a2t - FG(s)[0]

    def capint(th):
        return H(th)**2 - dH(th)**2

    bps = [mp.mpf(0), beta, P2 - beta, P2, P2 + beta, mp.pi - beta, mp.pi]
    C2 = sum(mp.quad(capint, [bps[i], bps[i+1]]) for i in range(len(bps)-1))
    C2 = C2 - H(mp.mpf(0)) - H(mp.pi)

    A_R = u**2 + 1 + mp.atan(u/2)
    Q = C2 - 2*V

    show = min(dig - 8, 45)
    print(f"Q(Sigma) = A_R*  AT {dig} WORKING DIGITS\n")
    print(f"  u          = {mp.nstr(u, show)}   (u^3+3u=2)")
    print(f"  beta       = {mp.nstr(beta, show)}")
    print(f"  a1         = {mp.nstr(a1, show)}   4 a1 sin beta - 1 = "
          f"{mp.nstr(4*a1*mp.sin(beta)-1, 5)}")
    print(f"  f1         = {mp.nstr(f1, show)}")
    print(f"  1-(2/3)a1  = {mp.nstr(A, show)}   (= x(pi/2), right end of the floor "
          f"facet)")
    print()
    print(f"  V          = {mp.nstr(V, show)}")
    print(f"  |C2|       = {mp.nstr(C2, show)}")
    print(f"  Q = |C2|-2V= {mp.nstr(Q, show)}")
    print(f"  A_R*       = {mp.nstr(A_R, show)}")
    print()
    d = Q - A_R
    print(f"  Q - A_R*   = {mp.nstr(d, 8)}")
    print(f"  |Q - A_R*| = 10^({mp.nstr(mp.log10(abs(d)), 6)}) "
          f"relative {mp.nstr(abs(d)/A_R, 6)}")
    print()
    print("  Rule 7: still floating point, not an enclosure.  But the two sides share")
    print("  no computation, so agreement at this many digits rules out a")
    print("  double-precision coincidence.")


if __name__ == "__main__":
    main()
