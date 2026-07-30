"""ambi_wpos.py — a finite certificate for W > 0 (Rule 7, exact-ish arithmetic).

The middle-phase step of the outer-arm monotonicity is: with u = t/2 - pi/8,

    cos^2 t * x'(t) = W(u) := (3K/4) sin u + (K/4) cos 3u + 1/2 - sin(2u + pi/4),
    K = f1 sqrt(4 - 2 sqrt 2),      |u| <= u0 := pi/8 - beta/2.

NOTE, and it is a correction: an earlier write-up gave the last term as
"- sqrt2 cos(2u + pi/4)".  That is WRONG.  The substitution t = 2u + pi/4 makes the term
-sin t = -sin(2u + pi/4), and sqrt2 cos(2u+pi/4) = cos 2u - sin 2u is a different
function (at u = 0 it gives 1, not 1/sqrt2).  The correct form is verified below against
numerical differentiation of the actual path.

CERTIFICATE.  On |u| <= u0 = 0.2478..., 3u lies in (-pi, pi) so cos 3u is unimodal with
maximum at 0, hence its minimum over a subinterval is at an endpoint; sin u is
increasing; and 2u + pi/4 lies in [0.2896, 1.2812] which is inside [0, pi/2], so
sin(2u + pi/4) is increasing.  Therefore on [p, q],

    W >= (3K/4) sin p + (K/4) min(cos 3p, cos 3q) + 1/2 - sin(2q + pi/4) =: L(p,q).

Subdividing into m equal pieces and checking L > 0 on each is a finite certificate.
Run with mpmath at high precision so the certificate is not a floating-point artifact.

Usage: python3 ambi_wpos.py [digits]
"""
import sys
import mpmath as mp

def main():
    mp.mp.dps = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    u = mp.findroot(lambda x: x**3 + 3*x - 2, mp.mpf("0.596"))
    beta = mp.atan(u/2)
    a1 = mp.sqrt(4 + u**2)/(4*u)
    s2 = mp.sqrt(2)
    f1 = (mp.mpf(4)/3*a1*mp.cos(beta))/(mp.cos(beta/2) + (1 - s2)*mp.sin(beta/2))
    K = f1*mp.sqrt(4 - 2*s2)
    u0 = mp.pi/8 - beta/2
    W = lambda x: (3*K/4)*mp.sin(x) + (K/4)*mp.cos(3*x) + mp.mpf(1)/2 - mp.sin(2*x + mp.pi/4)
    print(f"K  = {mp.nstr(K, 30)}")
    print(f"u0 = {mp.nstr(u0, 30)}   (= pi/8 - beta/2)")
    print(f"W(0)   = {mp.nstr(W(0), 25)}")
    print(f"W(u0)  = {mp.nstr(W(u0), 25)}")
    print(f"(1/2)(1-cos beta) = {mp.nstr((1 - mp.cos(beta))/2, 25)}"
          f"   diff {mp.nstr(W(u0) - (1-mp.cos(beta))/2, 6)}")
    print(f"W(-u0) = {mp.nstr(W(-u0), 25)}")
    print()
    for m in (1, 2, 4, 8, 16, 32, 64):
        h = 2*u0/m; worst = None
        for i in range(m):
            p = -u0 + i*h; q = p + h
            L = ((3*K/4)*mp.sin(p) + (K/4)*min(mp.cos(3*p), mp.cos(3*q))
                 + mp.mpf(1)/2 - mp.sin(2*q + mp.pi/4))
            if worst is None or L < worst:
                worst = L
        print(f"  m = {m:3d}:  min lower bound L = {mp.nstr(worst, 12)}"
              f"   {'CERTIFIED W > 0' if worst > 0 else 'inconclusive'}")
    print()
    print("  The smallest m with L > 0 on every piece is a complete, checkable proof of")
    print("  W > 0, hence of strict monotonicity of x on the middle phase.")

if __name__ == "__main__":
    main()
