"""ambi_as_pi.py — the ambidextrous problem IS the one-corner problem at omega = pi.

Four attempts to transfer Baek's architecture have failed (direct balancing, the
rho-quotient, the prescribed-edge class, and injectivity -- the last failing on the
CANDIDATE itself).  This script records and checks a reformulation that explains why.

Sigma = S ^ rho S.  Now rho maps the hallway at angle s to the hallway at angle -s
with corner rho c(s), so

    intersection_{t in [-pi/2, 0]} H_t  =  intersection_{s in [0, pi/2]} rho H_s
                                       =  rho ( intersection_s H_s )  =  rho S,

whence

    Sigma  =  intersection_{t in [-pi/2, pi/2]} H_t,        c(-t) = rho c(t).      (*)

That is a SINGLE intersection over an angle range of length pi, with a
rho-symmetric corner path.  In other words the ambidextrous problem is the
one-corner problem at ROTATION ANGLE pi.

WHY THIS MATTERS.  Baek's framework is built for omega in (0, pi/2].  His Lemma
3.4.2 uses omega <= pi/2; his parallelogram P_omega is defined for that range; and
his Chapter 4 proves that a balanced maximum sofa has omega = pi/2 exactly, i.e.
pi/2 is the TOP of his range and the value his maximisers attain.  The ambidextrous
problem sits at omega = pi, outside the range entirely.

So the four failures are not four accidents.  They are one fact: the architecture is
designed for omega <= pi/2 and the ambidextrous problem is omega = pi.  In
particular Chapter 4's conclusion "omega = pi/2" is not a step that could ever have
transferred -- for the ambidextrous problem the corresponding statement is omega = pi,
and there is nothing to prove because the constraint family is given.

This script verifies (*) numerically: the intersection over [-pi/2, pi/2] with
c(-t) = rho c(t) reproduces S ^ rho S.

Usage: python3 ambi_as_pi.py [n_theta]
"""
from __future__ import annotations
import os, sys, math
import numpy as np
from shapely.geometry import Polygon
from shapely.affinity import rotate as srot, translate as strans, scale as sscale

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(THIS)))
from sofa_romik2017_reference import HALLWAY, x_path

BIG = 8.0
PI2 = math.pi/2


def corner(t):
    """c(t) for t >= 0, and rho c(-t) for t < 0, where rho(x,y) = (x, 1-y)"""
    if t >= 0:
        v = x_path(float(t))
        return float(v[0]), float(v[1])
    v = x_path(float(-t))
    return float(v[0]), 1.0 - float(v[1])


def inter(ts):
    S = Polygon([(-BIG, 0), (1, 0), (1, 1), (-BIG, 1)])
    for t in ts:
        ax, ay = corner(t)
        H = srot(HALLWAY, math.degrees(t), origin=(0, 0))
        if t < 0:
            # rho of the hallway at |t|: reflect the rotated-and-placed hallway
            H = srot(HALLWAY, math.degrees(-t), origin=(0, 0))
            H = sscale(H, xfact=1.0, yfact=-1.0, origin=(0.0, 0.0))
        H = strans(H, xoff=ax, yoff=ay)
        S = S.intersection(H)
        if S.is_empty:
            return S
    return S


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 721
    A_R = 1.6449552184

    # reference: S ^ rho S built the usual way
    ts_pos = np.linspace(0.0, PI2, n)
    S = inter(ts_pos)
    rhoS = sscale(S, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
    Sig_ref = S.intersection(rhoS)

    # the omega = pi form: one intersection over [-pi/2, pi/2]
    ts_all = np.linspace(-PI2, PI2, 2*n-1)
    Sig_pi = inter(ts_all)

    print(f"THE AMBIDEXTROUS PROBLEM AS omega = pi   (n = {n})\n")
    print(f"  |S|                              = {S.area:.9f}")
    print(f"  |S ^ rho S|         (reference)   = {Sig_ref.area:.9f}")
    print(f"  |cap_{{[-pi/2,pi/2]}} H_t|  (omega=pi) = {Sig_pi.area:.9f}")
    print(f"  A_R*                             = {A_R:.9f}")
    print(f"\n  agreement of the two constructions: "
          f"{abs(Sig_pi.area - Sig_ref.area):.3e}")
    print(f"  symmetric difference area: "
          f"{Sig_pi.symmetric_difference(Sig_ref).area:.3e}")
    print()
    print("  If the two agree, the ambidextrous problem is literally the one-corner")
    print("  problem at rotation angle pi with a rho-symmetric corner path, and")
    print("  Baek's framework -- built for omega <= pi/2, with Ch. 4 proving")
    print("  omega = pi/2 for its maximisers -- is outside its range here.")


if __name__ == "__main__":
    main()
