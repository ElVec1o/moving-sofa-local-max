"""ambi_outerarm.py — P3c: is the OUTER arm convex-linear too?

ambi_split.py proved (measured, exactly disjoint, exactly covering):

    N  =  W_2  disjoint-union  W_1out                                          (*)

    W_2    = sweep of [ c(t), c(t) - alpha_2(t) mu_t ]        (face 2, advancing part)
    W_1out = sweep of [ c(t) - alpha_1(t)^+ nu_t , exit of K ] (face 1, advancing part)

with alpha_1 = -<c',mu_t>, alpha_2 = <c',nu_t>, both AFFINE-LINEAR in the support
function hence convex-linear on Baek's domain.  |W_2| = (1/2) int alpha_2^2 to 6
digits, a convex quadratic.  So the ONLY non-convex-linear ingredient left in an exact
formula for |N| is the outer endpoint S_1(t) of the face-1 segment.

THE OBSERVATION THIS SCRIPT TESTS.  W_1out has bounding box y-min exactly 0, and the
face-1 direction is  -nu_t = (sin t, -cos t),  which points DOWN.  If the face-1 ray
leaves the cap through the corridor floor y = 0 then

    S_1(t) = c_y(t) / cos t,

which is convex-linear in K, because c is affine-linear in the support function and
cos t does not depend on K.  Then (*) is an exact formula for |N| in convex-linear
data alone, every term is a convex quadratic, and P3c closes.

Measured here, per t:  exit length along -nu_t, the prediction c_y/cos t, which
constraint is actually active at the exit point, and the corrected swept-area integral

    |N| =? int_0^{pi/2} [ (1/2)(alpha_2^+)^2 + I_1(t) ] dt,
    I_1(t) = int_{alpha_1^+}^{S_1} (s - alpha_1) ds
           = (1/2)(S_1 - alpha_1)^2                if alpha_1 >= 0
           = (1/2) S_1^2 - alpha_1 S_1             if alpha_1 <  0.

Usage: python3 ambi_outerarm.py [n_hall] [n_sweep]
"""
from __future__ import annotations
import os, sys, math
import numpy as np
from shapely.geometry import Polygon, Point
from shapely.ops import unary_union
from shapely.affinity import scale as sscale

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sofa_romik2017_reference import x_path, BETA
from ambi_mamikon import build, arms, sweep, PI2
from ambi_split import sweep_range, exit_len


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 481
    nsw = int(sys.argv[2]) if len(sys.argv) > 2 else 1201
    ts, C1, S = build(n)
    rho = lambda G: sscale(G, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
    C2 = C1.intersection(rho(C1))
    N = C1.difference(S).intersection(C2)
    tw = np.linspace(0.0, PI2, nsw)
    cs, al1, al2 = arms(tw)

    # exit length along -nu_t, starting just past B(t) so a corner sitting on the
    # floor does not abort the bisection
    S1 = np.zeros(len(tw)); pred = np.zeros(len(tw))
    for i, t in enumerate(tw):
        t = float(t)
        d = (-math.sin(t), math.cos(t))
        s0 = max(al1[i], 0.0)
        base = (cs[i][0] - s0*d[0], cs[i][1] - s0*d[1])
        S1[i] = s0 + exit_len(base, d, C1)
        pred[i] = cs[i][1]/math.cos(t) if math.cos(t) > 1e-12 else float('inf')

    print("t         c_y        cos t     S1(exit)   c_y/cos t   alpha_1    match")
    for t in (0.0, 0.05, 0.15, BETA, 0.4, 0.6, math.pi/4, 1.0, 1.2,
              PI2 - BETA, 1.35, 1.45, 1.52):
        i = int(round(t/PI2*(nsw - 1)))
        m = ("EXIT=FLOOR" if abs(S1[i] - pred[i]) < 2e-3 else
             f"differ {S1[i]-pred[i]:+.5f}")
        print(f"{tw[i]:8.5f} {cs[i][1]:10.6f} {math.cos(tw[i]):9.6f} "
              f"{S1[i]:10.6f} {pred[i]:11.6f} {al1[i]:9.5f}   {m}")
    ok = np.abs(S1 - pred) < 2e-3
    print(f"\nfloor-exit holds on {ok.sum()}/{len(tw)} samples; "
          f"largest t with floor exit = "
          f"{tw[ok].max() if ok.any() else float('nan'):.6f}")
    bad = tw[~ok]
    if len(bad):
        print(f"fails on t in [{bad.min():.6f}, {bad.max():.6f}]  "
              f"({len(bad)} samples)")

    # corrected swept-area integral
    p2 = np.maximum(al2, 0.0)
    I1 = np.where(al1 >= 0, 0.5*np.maximum(S1 - al1, 0.0)**2,
                  0.5*S1**2 - al1*S1)
    tot = 0.5*np.trapezoid(p2**2, tw) + np.trapezoid(I1, tw)
    W2 = sweep(tw, cs, al2, 'mu')
    W1out = sweep_range(tw, cs, S1, 'nu', 0, len(tw) - 1, inner=np.maximum(al1, 0.0))
    print(f"\n|N| measured            = {N.area:.9f}")
    print(f"|W2| + |W1out|          = {W2.area + W1out.area:.9f}"
          f"   (overlap {W2.intersection(W1out).area:.2e})")
    print(f"(1/2)int alpha_2^2      = {0.5*np.trapezoid(p2**2, tw):.9f}"
          f"   |W2| = {W2.area:.9f}")
    print(f"int I_1 dt              = {np.trapezoid(I1, tw):.9f}"
          f"   |W1out| = {W1out.area:.9f}")
    print(f"total integral          = {tot:.9f}")

    # and the resulting bound, using the FLOOR prediction for S1 (convex-linear)
    S1p = np.where(np.isfinite(pred), np.minimum(pred, S1), S1)
    I1p = np.where(al1 >= 0, 0.5*np.maximum(S1p - al1, 0.0)**2,
                   0.5*S1p**2 - al1*S1p)
    V = 0.5*np.trapezoid(p2**2, tw) + np.trapezoid(I1p, tw)
    print(f"\nV (convex-linear data only) = {V:.9f}")
    print(f"|C2| - 2V                   = {C2.area - 2*V:.9f}"
          f"   A_R* = 1.644955218   slack {C2.area - 2*V - 1.6449552184:.9f}")


if __name__ == "__main__":
    main()
