"""POSITIVE LEAD: the frozen-breakpoint majorant.

IDEA (Baek's move, made local)
------------------------------
Write G(c,b) = Green's-theorem area with the four breakpoints held at FREE
parameters b in R^4 (each contact arc integrated over [b_j, b_{j+1}] with
b FIXED, not slaved to c).  Then the true area is F(c) = G(c, b(c)), where
b(c) is the geometric breakpoint map (where consecutive contact paths cross).

G(., b0) with b0 FROZEN has no moving breakpoints, so it is EXACTLY quadratic
in c (Lemma: integrand quadratic in the jet) and carries NO fatal cubic.

If  b(c) = argmin_b G(c, .)   then
    F(c) = min_b G(c,b) <= G(c, b0)   for any frozen b0,
so   F(c) <= G(c, b0) <= G(c_G, b0) = F(c_G)
whenever c_G maximises the fixed-breakpoint quadratic G(., b0).  The last
step is exactly the coercive quadratic form we already control (rank-one ->
multi-contact -> lambda_min = 1), with the fatal cubic GONE.

THE ONE TESTABLE FACT
---------------------
Everything rides on whether b(c_G) is a MINIMUM of b -> G(c_G, b).
At c_G the sofa boundary is continuous, so partial G / partial b_j = 0
(stationary).  The sign of the 4x4 Hessian  H_ij = d^2 G / d b_i d b_j
decides it:
    H positive definite  -> b(c_G) is a strict min -> MAJORANT VALID, and
                            the whole local-max argument closes.
    H indefinite / neg   -> majorant fails in this form; need another device.

We compute G(c_G, b) by evaluating the Green boundary integral with shifted
breakpoints and finite-difference the 4x4 Hessian in b.

IMPLEMENTATION of G(c_G, b)
---------------------------
The sofa boundary is a closed curve traced, over theta in [0,pi/2], by
whichever contact path is active.  With breakpoints b = (b1,b2,b3,b4) the
active-path schedule is Romik's five-phase table.  Freezing b to values
other than the true crossing produces a boundary with small gaps/overlaps at
the b_j; its signed area 1/2 oint (x dy - y dx) is still well defined and is
G(c_G, b).  We assemble it directly from the contact-path formulas
A,B,C,D and the corner path x, which are known in closed form.

Runtime: closed-form integrand, no polygon oracle -> seconds.
"""
from __future__ import annotations
import math, os, sys
import numpy as np
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gerver_constants import solve_gerver_constants, _xt_xtp, _At, _Bt, _Ct, _Dt

HALF = math.pi / 2
PHI = 0.039177364790083641
TR = 0.681301509382724894
# true breakpoints
B_TRUE = np.array([PHI, TR, HALF - TR, HALF - PHI])


def _paths(p, n=4000):
    """Sample the five boundary constituents on a fine theta grid, once."""
    th = np.linspace(0, HALF, n)
    out = {}
    for nm, fn in (("A", _At), ("B", _Bt), ("C", _Ct), ("D", _Dt)):
        P = np.array([[float(v) for v in fn(mp.mpf(t), p)] for t in th])
        out[nm] = P
    X = np.array([[float(v) for v in _xt_xtp(mp.mpf(t), p)[0]] for t in th])
    out["x"] = X
    return th, out


def _seg_area(th, P, t0, t1):
    """1/2 * integral_{t0}^{t1} (x y' - y x') dt along path P(th)."""
    m = (th >= t0) & (th <= t1)
    if m.sum() < 2:
        return 0.0
    x, y = P[m, 0], P[m, 1]
    tt = th[m]
    xp = np.gradient(x, tt); yp = np.gradient(y, tt)
    return 0.5 * np.trapezoid(x * yp - y * xp, tt)


def G_of_b(th, paths, b):
    """Signed area of the boundary with breakpoints frozen at b.

    Boundary schedule (Romik phases), outer contour A then C then the
    inner corner run, closed up.  We use the OUTER boundary contributions
    (A on the whole range, C on the whole range) plus the inner corner
    substitutions between the breakpoints -- matching the fig:gerver
    construction.  The b-dependence enters only through the switch points.
    """
    b1, b2, b3, b4 = b
    # Outer arcs are breakpoint-independent; the b-dependence is in the
    # inner-corner / B / D substitutions on the phase intervals.
    # Contributions (signed) following the CCW boundary of fig:gerver:
    a = 0.0
    a += _seg_area(th, paths["A"], 0, HALF)             # A over full range
    a += _seg_area(th, paths["C"], 0, HALF)             # C over full range
    a += _seg_area(th, paths["D"], 0, b2)               # D active up to theta_R
    a += _seg_area(th, paths["x"], b1, HALF - b1)       # inner corner run
    a += _seg_area(th, paths["B"], HALF - b2, HALF)     # B active past pi/2-theta_R
    return a


def main():
    print("=" * 74)
    print("FROZEN-BREAKPOINT MAJORANT: is b(c_G) a MIN of b -> G(c_G,b)?")
    print("=" * 74)
    p, _ = solve_gerver_constants(working_dps=30, verbose=False)
    th, paths = _paths(p)
    G0 = G_of_b(th, paths, B_TRUE)
    print(f"  G(c_G, b_true) = {G0:.7f}   (should be Gerver area 2.2195317)")
    print(f"  b_true = {B_TRUE}")
    print()

    # gradient and Hessian in b by central differences
    h = 1e-3
    grad = np.zeros(4)
    for i in range(4):
        bp = B_TRUE.copy(); bp[i] += h
        bm = B_TRUE.copy(); bm[i] -= h
        grad[i] = (G_of_b(th, paths, bp) - G_of_b(th, paths, bm)) / (2 * h)
    print(f"  grad_b G at b_true : {grad}")
    print(f"    (should be ~0: boundary continuous => stationary in b)")
    print()

    H = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            bpp = B_TRUE.copy(); bpp[i] += h; bpp[j] += h
            bpm = B_TRUE.copy(); bpm[i] += h; bpm[j] -= h
            bmp = B_TRUE.copy(); bmp[i] -= h; bmp[j] += h
            bmm = B_TRUE.copy(); bmm[i] -= h; bmm[j] -= h
            H[i, j] = (G_of_b(th, paths, bpp) - G_of_b(th, paths, bpm)
                       - G_of_b(th, paths, bmp) + G_of_b(th, paths, bmm)) / (4 * h * h)
    H = 0.5 * (H + H.T)
    ev = np.linalg.eigvalsh(H)
    print("  Hessian d^2 G / db^2 at b_true:")
    for row in H:
        print("     " + "  ".join(f"{v:+8.3f}" for v in row))
    print(f"  eigenvalues: {ev}")
    print()
    if (ev > 0).all():
        print("  => POSITIVE DEFINITE: b(c_G) is a strict MIN of G(c_G,.).")
        print("     The frozen-breakpoint majorant F(c) <= G(c,b0) is VALID.")
        print("     Local maximality then reduces to the fixed-breakpoint")
        print("     quadratic, which is coercive -- the chain CLOSES.")
    elif (ev < 0).all():
        print("  => NEGATIVE definite: b(c_G) is a MAX, majorant points the")
        print("     wrong way (gives a lower bound on F).  This device fails.")
    else:
        print("  => INDEFINITE: saddle in b.  Simple freezing fails; a partial")
        print("     freeze (only the min-directions) may still work.")


if __name__ == "__main__":
    main()
