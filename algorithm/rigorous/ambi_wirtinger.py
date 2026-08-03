"""ambi_wirtinger.py — the cap is concave in EVERY admissible direction, affine only on two.

WHY THIS MATTERS.  ambi_atom.py proved |C_2| exactly affine along one direction, the atom.
That left A26 open: affine or concave in every admissible direction, which is what turns a
per-family statement into a global one.  It is not a new computation.  It is Wirtinger.

THE BOUNDARY CONDITIONS DO THE WORK.  An admissible perturbation eta of H preserves the
forced data H'(0) = 1/2, H(pi/2) = 1, H'(pi) = -1/2, so

    eta'(0) = 0 ,   eta(pi/2) = 0 ,   eta'(pi) = 0 .

That is Neumann at one end and Dirichlet at the other, on each half-interval [0, pi/2] and
[pi/2, pi], each of length pi/2.  The first eigenvalue of -d^2/dtheta^2 under those
conditions on an interval of length L is (pi/(2L))^2, here exactly 1.  Hence

    int (eta')^2 >= int eta^2 ,  i.e.  int_0^pi ( eta^2 - (eta')^2 ) <= 0 ,

for every admissible eta, so the cap area's quadratic term is nonpositive in EVERY
direction: |C_2| is concave, not merely affine along one line.

EQUALITY IS EXACTLY TWO DIRECTIONS.  In the eigenbasis
    [0, pi/2]:  cos((2k-1) theta)          [pi/2, pi]:  sin((2k-1)(theta - pi/2))
the quadratic form is a weighted sum of (1 - (2k-1)^2), which vanishes only at k = 1.  The
two first modes are cos theta -- the gauge direction, a horizontal translation, which moves
no area at all -- and sin(theta - pi/2), which IS the atom Phi of ambi_atom.py.  So the
atom's exact affineness is not a coincidence of that family: it is the statement that the
atom saturates Wirtinger.

CASH VALUE.  |C_2| concave in every direction, plus 2|N| convex in every direction, gives
|T| = |C_2| - 2|N| concave globally; with the critical point at Sigma that is global
optimality, and no eigenvalue covering of cells is needed anywhere.  This file establishes
the first half in general and checks the mode identity numerically.  The niche half remains
proved along the atom direction only (ambi_atom.py) and conjectural elsewhere.

Rule 0: the quadratic form's sign is PROVED (mode-by-mode, formalised as
`wirtinger_mode`, `wirtinger_mode_eq` and `cap_quadratic_nonpos`), conditional on the same
cap-area quadratic form ambi_atom.py quotes.

Usage: python3 ambi_wirtinger.py
"""
from __future__ import annotations
import numpy as np

P2 = np.pi / 2


def basis(k: int, th: np.ndarray):
    """The k-th admissible mode and its derivative, k >= 1, frequency n = 2k-1.

    cos(n theta) on [0, pi/2] and sin(n (theta - pi/2)) on [pi/2, pi]; each satisfies
    Neumann at the outer end and Dirichlet at pi/2, so any combination is admissible."""
    n = 2 * k - 1
    left = th <= P2
    e = np.where(left, np.cos(n * th), np.sin(n * (th - P2)))
    d = np.where(left, -n * np.sin(n * th), n * np.cos(n * (th - P2)))
    return e, d


def quad_form(coef_l, coef_r, m=400001):
    """int_0^pi (eta^2 - (eta')^2) for eta built from the two half-interval bases."""
    thl = np.linspace(0, P2, m)
    thr = np.linspace(P2, np.pi, m)
    el = sum(a * np.cos((2 * k - 1) * thl) for k, a in enumerate(coef_l, 1))
    dl = sum(-a * (2 * k - 1) * np.sin((2 * k - 1) * thl) for k, a in enumerate(coef_l, 1))
    er = sum(b * np.sin((2 * k - 1) * (thr - P2)) for k, b in enumerate(coef_r, 1))
    dr = sum(b * (2 * k - 1) * np.cos((2 * k - 1) * (thr - P2)) for k, b in enumerate(coef_r, 1))
    return (float(np.trapezoid(el ** 2 - dl ** 2, thl))
            + float(np.trapezoid(er ** 2 - dr ** 2, thr)))


def closed_form(coef_l, coef_r):
    """The same, in closed form: (pi/4) sum (1 - (2k-1)^2) (a_k^2 + b_k^2)."""
    s = 0.0
    for k, a in enumerate(coef_l, 1):
        s += (1 - (2 * k - 1) ** 2) * a ** 2
    for k, b in enumerate(coef_r, 1):
        s += (1 - (2 * k - 1) ** 2) * b ** 2
    return np.pi / 4 * s


def main() -> int:
    print(__doc__.split("Usage")[0])
    bad = 0
    rng = np.random.default_rng(20260803)

    print("  (1) the quadratic form, quadrature against closed form\n")
    print(f"  {'case':<26} {'quadrature':>13} {'closed form':>13} {'sign':>6}")
    cases = [("atom alone (k=1 right)", [0.0], [1.0]),
             ("gauge alone (k=1 left)", [1.0], [0.0]),
             ("gauge + atom", [0.7], [1.3]),
             ("k=2 right only", [0.0, 0.0], [0.0, 1.0]),
             ("k=3 left only", [0.0, 0.0, 1.0], [0.0, 0.0, 0.0])]
    for _ in range(6):
        cases.append(("random, 6 modes each",
                      list(rng.normal(size=6)), list(rng.normal(size=6))))
    worst = 0.0
    for name, cl, cr in cases:
        q, c = quad_form(cl, cr), closed_form(cl, cr)
        worst = max(worst, abs(q - c))
        sign = "0" if abs(c) < 1e-12 else ("<0" if c < 0 else ">0 !!")
        if c > 1e-12:
            print(f"  FAIL: positive quadratic form on {name}")
            bad += 1
        print(f"  {name:<26} {q:13.8f} {c:13.8f} {sign:>6}")
    ok = worst < 1e-6
    bad += not ok
    print(f"\n  worst |quadrature - closed form| = {worst:.2e}   {'OK' if ok else 'FAIL'}\n")

    print("  (2) the mode weights: 1 - n^2 for odd n\n")
    print(f"  {'k':>4} {'n = 2k-1':>9} {'1 - n^2':>9}")
    for k in range(1, 7):
        n = 2 * k - 1
        print(f"  {k:4d} {n:9d} {1 - n ** 2:9d}{'   <- the only zero' if k == 1 else ''}")
    print("\n  Every weight is nonpositive and only k = 1 vanishes, so the form is negative")
    print("  semidefinite with a two-dimensional kernel: cos theta (gauge, a horizontal")
    print("  translation) and sin(theta - pi/2) (the atom).  Those are exactly the two")
    print("  directions along which ambi_atom.py found the cap affine.\n")

    print("  (3) negative control: drop a boundary condition and the bound must fail\n")
    thl = np.linspace(0, P2, 400001)
    # eta = sin theta is NOT a control: it satisfies Dirichlet at 0 and Neumann at pi/2,
    # so it is the OTHER first eigenfunction and returns exactly 0.  A first attempt used
    # it and the control could not fire -- a vacuous control tests nothing.  The constant
    # violates the Dirichlet condition at pi/2 that the forced value H(pi/2) = 1 imposes,
    # and it is the direction the inequality must reject.
    e = np.ones_like(thl)                 # violates eta(pi/2) = 0
    d = np.zeros_like(thl)
    v = float(np.trapezoid(e ** 2 - d ** 2, thl))
    print(f"  eta = 1 on [0, pi/2] has eta(pi/2) = 1 != 0, and gives {v:+.8f} = pi/2")
    if v <= 0:
        print("  FAIL: the control did not fire; the bound cannot be using the boundary data")
        bad += 1
    else:
        print("  which is POSITIVE, as it must be: the inequality is carried by the forced")
        print("  boundary data, not by the interval length alone.\n")

    print(f"  {'ALL CHECKS PASS' if not bad else f'{bad} CHECK(S) FAILED'}")
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
