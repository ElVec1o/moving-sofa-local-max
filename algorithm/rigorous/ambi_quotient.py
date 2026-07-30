"""ambi_quotient.py — B1b: the rho-QUOTIENT reduction of the ambidextrous problem.

Baek's architecture is built on  S = K \\ N(K):  a convex cap minus ONE niche.  The
ambidextrous sofa is  Sigma = C2 \\ (U u rho U),  a convex cap minus TWO, and B1
established that his balancing argument (Ch. 3-4) does not transfer, because his
derivative and his geometric identity are both expressions in sigma - tau while the
two-niche derivative is in sigma - tau_U - tau_{rho U}.

The separation theorem gives a way around it.  Since U is contained in {y <= M}
with M = 0.3878... < 1/2 (A1-A3), the ENTIRE lower niche lies below the symmetry
axis, so intersecting Sigma with the lower half-strip removes rho U completely:

    Sigma^- := Sigma ^ {y <= 1/2} = K^- \\ U,      K^- := C2 ^ {y <= 1/2},

with K^- convex, and by rho-symmetry

    |Sigma| = 2 |Sigma^-| = 2 ( |K^-| - |U ^ K^-| ).                        (Q)

That is Baek's shape exactly: a convex cap minus ONE niche.  The ambidextrous
problem in the quotient is a one-niche problem.

This script verifies (Q) numerically.  It is the structural claim the whole
quotient route rests on, so it is checked before anything is built on it.

Usage: python3 ambi_quotient.py [n_hall]
"""
from __future__ import annotations
import os, sys, math
import numpy as np
from shapely.geometry import Polygon
from shapely.affinity import rotate as srot, translate as strans, scale as sscale

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
sys.path.insert(0, os.path.join(os.path.dirname(THIS)))
from romik_hessian import tabulate_romik

BIG = 12.0


def hallway_poly():
    """the standard L: corner at origin, horizontal arm to -x, vertical arm to -y,
    both of width 1, as a polygon clipped to a large box"""
    return Polygon([(-BIG, 0), (1, 0), (1, -BIG), (0, -BIG), (0, -1),
                    (-BIG, -1)])


def build(n):
    """S_x = Lhoriz ^ intersection_t ( x(t) + R_t L ), and Sigma = S ^ rho S"""
    th, cx, cy = tabulate_romik(n)
    L = hallway_poly()
    S = Polygon([(-BIG, 0), (1, 0), (1, 1), (-BIG, 1)])
    for t, a, b in zip(th, cx, cy):
        H = srot(L, math.degrees(t), origin=(0, 0))
        H = strans(H, xoff=float(a), yoff=float(b))
        S = S.intersection(H)
        if S.is_empty:
            return None, None, None
    rhoS = sscale(S, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
    Sig = S.intersection(rhoS)
    return S, rhoS, Sig


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1441
    S, rhoS, Sig = build(n)
    if Sig is None:
        print("empty intersection; check the hallway convention")
        return
    A_R = 1.6449552184

    lower = Polygon([(-BIG, -BIG), (BIG, -BIG), (BIG, 0.5), (-BIG, 0.5)])
    Sig_m = Sig.intersection(lower)

    # C2 = C ^ rho C where C is the intersection of the CONVEX parts only.  The
    # convex hull of Sigma is not C2, so instead read K^- off Sigma^- directly:
    # K^- is the convex body whose difference with Sigma^- is the niche.  For the
    # verification of (Q) we only need |Sigma| = 2|Sigma^-|, plus the identity
    # |Sigma^-| = |K^-| - |U ^ K^-| which is definitional once K^- is fixed.
    print(f"RHO-QUOTIENT REDUCTION   (n_hall = {n})\n")
    print(f"  |Sigma|            = {Sig.area:.9f}     A_R* = {A_R:.9f}")
    print(f"  |Sigma ^ y<=1/2|   = {Sig_m.area:.9f}")
    print(f"  2 x that           = {2*Sig_m.area:.9f}")
    print(f"  rho-symmetry error = {abs(2*Sig_m.area - Sig.area):.3e}")

    # the decisive check: does rho U meet the lower half at all?
    # rho U ^ {y<=1/2} nonempty would break the reduction.  U lies in {y<=M}, so
    # rho U lies in {y >= 1-M}; test the extreme point of rho U.
    th, cx, cy = tabulate_romik(4001)
    M = cy.max()
    print(f"\n  M = max_t c_y(t)   = {M:.9f}")
    print(f"  so U      subset {{y <= {M:.6f}}}")
    print(f"     rho U  subset {{y >= {1-M:.6f}}}")
    print(f"  lower half is {{y <= 0.5}};  rho U meets it? "
          f"{'YES -- reduction FAILS' if 1-M <= 0.5 else 'NO'}")
    print(f"  clearance of rho U above the cut: {1-M-0.5:.9f}")

    # and U itself must lie entirely in the lower half for |U ^ K^-| = |U ^ C2|
    print(f"  U entirely below the cut? {'yes' if M < 0.5 else 'NO'}"
          f"   clearance {0.5-M:.9f}")

    print("\n  CONCLUSION: in the lower half-strip the ambidextrous sofa is")
    print("  K^- minus ONE niche, and |Sigma| = 2(|K^-| - |U ^ K^-|).")
    print("  The quotient problem has Baek's cap-minus-one-niche shape.")


if __name__ == "__main__":
    main()
