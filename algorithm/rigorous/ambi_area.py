"""ambi_area.py — Q(Sigma) = A_R* at 50 digits, with the phase decomposition.

A_R* = u^2 + 1 + arctan(u/2) with u^3 + 3u = 2, and since u = 2 tan(beta),

    A_R* = 1 + 4 tan^2(beta) + beta .

The functional is Q = |C2| - 2V with

    |C2| = int_0^pi ( H^2 - H'^2 ) dtheta - H(0) - H(pi)
    V    = int_0^{pi/2} [ (1/2)(a2^+)^2 + (1/2)(sigma-a1)^2 - (1/2)(a1^-)^2 ] dt

and every integrand is made elementary by the proved identity

    sigma - alpha_1 = cos(t) x'(t),     x = (F-1)/cos t

(the face-1 line's x-intercept), which removes the tan-singularity at t = pi/2.

A symbolic evaluation of the same integrals was attempted (ambi_area_symbolic.py) and did
not terminate, so the identity is reported as HEURISTIC, against a closed-form target.

Usage: python3 ambi_area.py [digits]
"""
import sys
import mpmath as mp

def main():
    mp.mp.dps = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    u = mp.findroot(lambda x: x**3 + 3*x - 2, mp.mpf("0.596")); B = mp.atan(u/2)
    a1 = mp.sqrt(4 + u**2)/(4*u); s2 = mp.sqrt(2)
    f1 = (mp.mpf(4)/3*a1*mp.cos(B))/(mp.cos(B/2) + (1 - s2)*mp.sin(B/2))
    f2 = (1 - s2)*f1
    k6 = 1 - mp.mpf(4)/3*a1
    P2 = mp.pi/2
    Fm = {1: lambda t: mp.cos(t) + mp.sin(t)/2 - 1,
          6: lambda t: f1*mp.cos(t/2) + f2*mp.sin(t/2) - 1 + k6*mp.cos(t) + mp.sin(t)/2,
          5: lambda t: (1 - mp.mpf(2)/3*a1)*mp.cos(t) + mp.sin(t)/2 - mp.mpf(1)/2}
    Gm = {1: lambda t: (2*a1 - 1)*mp.sin(t) + mp.cos(t)/2 - mp.mpf(1)/2,
          6: lambda t: -f2*mp.cos(t/2) + f1*mp.sin(t/2) - 1 + mp.cos(t)/2 - k6*mp.sin(t),
          5: lambda t: (mp.mpf(8)/3*a1 - 1)*mp.sin(t) + mp.cos(t)/2 - 1}
    segs = [(1, 0, B), (6, B, P2 - B), (5, P2 - B, P2)]

    print(f"Q(Sigma) vs A_R* = 1 + 4 tan^2(beta) + beta,  at {mp.mp.dps} digits\n")
    C2 = mp.mpf(0)
    print("  |C2| blocks, int (H^2 - H'^2):")
    for tag, D in (("F", Fm), ("G", Gm)):
        for ph, lo, hi in segs:
            H = lambda t, ph=ph, D=D: D[ph](t) + 1
            v = mp.quad(lambda t: H(t)**2 - mp.diff(H, t)**2, [lo, hi])
            C2 += v
            print(f"    {tag}{ph}  = {mp.nstr(v, 22)}")
    C2 = C2 - (Fm[1](0) + 1) - (Gm[5](P2) + 1)
    print(f"    |C2| = {mp.nstr(C2, 25)}")

    V = mp.mpf(0)
    print("\n  V blocks:")
    for ph, lo, hi, a2p, a1n in ((1, 0, B, True, True), (6, B, P2 - B, True, False),
                                 (5, P2 - B, P2, False, False)):
        def ig(t, ph=ph, a2p=a2p, a1n=a1n):
            A1 = Gm[ph](t) - mp.diff(Fm[ph], t)
            A2 = Fm[ph](t) + mp.diff(Gm[ph], t)
            x = lambda s: Fm[ph](s)/mp.cos(s)
            r = (mp.cos(t)*mp.diff(x, t))**2/2
            if a2p: r += A2**2/2
            if a1n: r += -A1**2/2
            return r
        v = mp.quad(ig, [lo, hi]); V += v
        print(f"    phase {ph} = {mp.nstr(v, 22)}")
    print(f"    V = {mp.nstr(V, 25)}")

    Q = C2 - 2*V
    AR = 1 + 4*mp.tan(B)**2 + B
    print(f"\n  Q(Sigma)                = {mp.nstr(Q, 30)}")
    print(f"  1 + 4 tan^2(beta) + beta = {mp.nstr(AR, 30)}")
    print(f"  residual                 = {mp.nstr(Q - AR, 6)}")

if __name__ == "__main__":
    main()
