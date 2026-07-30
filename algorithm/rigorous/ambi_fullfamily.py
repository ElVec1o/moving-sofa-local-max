"""ambi_fullfamily.py — S1: does the FULL wedge family force M < 1/2?

A10-A12 settled the single-t question: Q_t u rho Q_t removes a full vertical segment
only when the apex exceeds h*(t), and h*(t) > 1/2 throughout (0, pi/2).  So no single
pair of wedges forces M <= 1/2, and the quotient reduction stayed conditional.

But a sofa must avoid EVERY wedge simultaneously.  The union
    W := union_t ( Q_t u rho Q_t )
is far larger than any single pair, so the real question is whether W disconnects
(or empties) the body whenever M > 1/2.

TEST.  Deform Romik's trajectory upward near its maximum, c_y -> c_y + delta*g(t)
with g a bump vanishing at both ends, so that M crosses 1/2, and ask what happens to
Sigma = S ^ rho S: does it stay a single connected piece, does it split, or does it
collapse?

If Sigma splits or loses area sharply as M crosses 1/2, S1 holds empirically and the
conditional hypothesis of the quotient reduction can be discharged.  If Sigma stays
connected with M > 1/2, S1 is false and the hypothesis is essential.

Usage: python3 ambi_fullfamily.py [n_theta]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS)
sys.path.insert(0, os.path.join(os.path.dirname(THIS)))
from shapely.geometry import Polygon
from shapely.affinity import rotate as srot, translate as strans, scale as sscale
from sofa_romik2017_reference import HALLWAY, x_path

BIG = 8.0
PI2 = math.pi/2


def build(n, delta, tpk=math.pi/4, width=0.9):
    """S = Lhoriz ^ intersect_t (x(t) + R_t L) with c_y bumped by
    delta * exp(-((t-tpk)/width)^2) * sin(2t)  (vanishes at 0 and pi/2)."""
    th = np.linspace(0.0, PI2, n)
    Lh = Polygon([(-BIG, 0), (1, 0), (1, 1), (-BIG, 1)])
    S = Lh
    cy_max = -1e9
    for t in th:
        v = x_path(float(t))
        bump = delta*math.exp(-((t-tpk)/width)**2)*math.sin(2*t)
        ax, ay = float(v[0]), float(v[1]) + bump
        cy_max = max(cy_max, ay)
        H = srot(HALLWAY, math.degrees(t), origin=(0, 0))
        H = strans(H, xoff=ax, yoff=ay)
        S = S.intersection(H)
        if S.is_empty:
            return None, cy_max, 0
    rhoS = sscale(S, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
    Sig = S.intersection(rhoS)
    npieces = 1 if Sig.geom_type == "Polygon" else len(Sig.geoms)
    return Sig, cy_max, npieces


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 901
    print(f"S1 -- does the FULL wedge family force M < 1/2?   (n_theta={n})")
    print("  bump c_y upward near t = pi/4 and watch Sigma as M crosses 1/2.\n")
    print(f"{'delta':>8} {'M':>10} {'|Sigma|':>12} {'pieces':>7}  note")
    base = None
    for delta in (0.0, 0.05, 0.10, 0.112, 0.13, 0.16, 0.20, 0.30):
        Sig, M, npc = build(n, delta)
        A = 0.0 if Sig is None else Sig.area
        if base is None:
            base = A
        flag = ""
        if M > 0.5:
            flag = "M > 1/2"
        if npc > 1:
            flag += "  SPLIT"
        if Sig is None or A < 1e-9:
            flag += "  EMPTY"
        print(f"{delta:8.3f} {M:10.6f} {A:12.7f} {npc:7d}  {flag}")
    print()
    print("  M = 1/2 is crossed at delta ~ 0.112 (since Romik's M = 0.387838).")
    print("  READING: if Sigma splits or collapses as M crosses 1/2, S1 holds and")
    print("  the conditional hypothesis can be discharged.  If it stays a single")
    print("  piece with M > 1/2, S1 is FALSE and the hypothesis is essential.")


if __name__ == "__main__":
    main()
