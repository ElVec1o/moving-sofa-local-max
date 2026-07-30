"""ambi_connected.py — does CONNECTEDNESS force the niche ceiling M < 1/2?

A gap in the quotient reduction, found while attempting B1d.  The reduction

    |Sigma| = 2 ( |K^-| - |U ^ K^-| )

rests on U being contained in {y <= M} with M := max_t c_y(t) < 1/2, which is a
property of ROMIK'S trajectory, not of an arbitrary competitor.  Worse, a
competitor with M >= 1/2 has OVERLAPPING niches, and overlap makes |U u rho U|
smaller, hence |Sigma| = |C2| - |U u rho U| LARGER.  So overlap is advantageous for
area and cannot simply be assumed away.

The way out should be connectedness.  A moving sofa is by definition connected.  If
some apex has c_y(t0) > 1/2 then the wedge Q_{t0} (opening down-left) and its
rho-image rho Q_{t0} (opening up-left, apex at height 1 - c_y(t0) < 1/2) have their
apexes vertically separated by 2c_y(t0) - 1 > 0, with the DOWN-opening cone above
the UP-opening one.  Just to the left of the common apex abscissa their union should
therefore cover a whole vertical line, cutting the body in two.

    CONJECTURED LEMMA.  For a connected ambidextrous sofa, max_t c_y(t) <= 1/2.

If true, the quotient reduction applies to every competitor and not only to Romik's
candidate, which is what the transfer needs.

This script tests the covering claim: for a single t0 and a given apex height h,
does Q_{t0} u rho Q_{t0} contain a full vertical segment spanning [0,1] at some x?

Usage: python3 ambi_connected.py
"""
from __future__ import annotations
import os, sys, math
import numpy as np

PI2 = math.pi/2


def in_wedge(px, py, ax, ay, t):
    """p in Q_t with apex (ax,ay): both frame coordinates negative"""
    c, s = math.cos(t), math.sin(t)
    dx, dy = px - ax, py - ay
    return (dx*c + dy*s < 0.0) and (-dx*s + dy*c < 0.0)


def covers_vertical(t, h, x, n=4001):
    """does Q_t (apex (0,h)) union rho Q_t (apex (0,1-h)) cover the whole segment
    {x} x [0,1]?  rho(p) = (p_x, 1-p_y), so p in rho Q_t iff rho(p) in Q_t with the
    SAME apex (0,h)."""
    ys = np.linspace(0.0, 1.0, n)
    for y in ys:
        inU = in_wedge(x, y, 0.0, h, t)
        inR = in_wedge(x, 1.0 - y, 0.0, h, t)
        if not (inU or inR):
            return False, float(y)
    return True, None


def main():
    print("Does Q_t u rho Q_t cover a full vertical line when the apex is above "
          "y = 1/2?")
    print("  apex of Q_t at (0,h); apex of rho Q_t at (0,1-h).")
    print("  For h > 1/2 the down-opening cone sits ABOVE the up-opening one.\n")
    print(f"{'t':>8} {'h':>7} {'x':>8}  covers [0,1]?   first gap y")
    for t in (0.3, 0.6, math.pi/4, 1.0, 1.3):
        for h in (0.40, 0.50, 0.55, 0.70):
            # look just left of the apex abscissa
            hit = None
            for x in (-0.02, -0.1, -0.3, -1.0, -3.0):
                ok, gap = covers_vertical(t, h, x)
                if ok:
                    hit = x
                    break
            if hit is not None:
                print(f"{t:8.4f} {h:7.2f} {hit:8.2f}  YES -- cut here")
            else:
                ok, gap = covers_vertical(t, h, -0.1)
                print(f"{t:8.4f} {h:7.2f} {-0.1:8.2f}  no          "
                      f"{gap:.4f}")
    print()
    print("READING.  A 'YES' row means the two wedges alone remove a full vertical")
    print("segment at that x, so any body meeting both sides of it is disconnected.")
    print("If every h > 1/2 gives a YES and every h < 1/2 gives a no, the")
    print("conjectured lemma holds for a single t, and the general case follows by")
    print("applying it at the maximising t0.")


if __name__ == "__main__":
    main()
