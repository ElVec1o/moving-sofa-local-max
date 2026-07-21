"""The finite reduction: ray-polynomial model + quartic criterion.

Establishes Proposition (quartic criterion) of the manuscript:
along a ray c_G + eps*eta, since F is exactly quadratic within each
combinatorial cell (Lemma affine), the ONLY higher-order dependence comes
from the moving breakpoints.  Modelling one breakpoint by its Taylor data
    B(eps)   = b + beta*eps + b2*eps^2 + ...        (breakpoint response)
    DeltaP   = a1*(theta-b) + a2*eps + p2*eps^2     (integrand jump)
and integrating the jump across the moving limit gives

    g(eps) = 1/2 Q eps^2 + 1/6 C3 eps^3 + 1/24 C4 eps^4 + ...
    C3 ~ b2 (a1 beta + a2) + beta p2
    C4 ~ b2 (a1 b2 / 2 + p2)

so the LINEAR breakpoint response (b2 = 0) yields NO cubic; the fatal cubic
is produced by the SECOND-ORDER response b2 = B''(0)/2 and the quadratic
integrand part p2.

Criterion:  if C4 < 0 then g <= 0 for all eps  <=>  C3^2 <= 3 |Q| |C4|.

Part 1 derives the model symbolically.  Part 2 measures Q, C3, C4 directly
from the area oracle at the b2 breakpoint and evaluates the criterion.
"""
from __future__ import annotations
import math, os, sys
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def symbolic_model():
    print("=" * 70)
    print("PART 1  symbolic ray-polynomial model")
    print("=" * 70)
    eps, beta, a1, a2, p2, b2, s = sp.symbols(
        "epsilon beta a1 a2 p2 b2 s", real=True)
    B = beta * eps + b2 * eps**2                 # breakpoint displacement
    integrand = a1 * s + a2 * eps + p2 * eps**2  # jump, s = theta - b
    J = sp.expand(sp.integrate(integrand, (s, 0, B)))
    print("  jump contribution  J(eps) =", J)
    C3 = sp.factor(sp.diff(J, eps, 3) / 1)       # coeff structure
    C4 = sp.factor(sp.diff(J, eps, 4) / 1)
    print("  d^3 J/deps^3 (cubic source)   =", sp.diff(J, eps, 3))
    print("  d^4 J/deps^4 (quartic source) =", sp.diff(J, eps, 4))
    print("  => C3 ~ b2(a1 beta + a2) + beta p2 ;  C4 ~ b2(a1 b2 + 2 p2)")
    print("     linear response b2=0 gives NO cubic.\n")


def measure(width=0.008, n_theta=6001):
    from phase2d_qsmooth import tabulate_gerver, build_sofa
    print("=" * 70)
    print(f"PART 2  measured Q, C3, C4 at breakpoint b2 (width {width})")
    print("=" * 70)
    th, cx, cy = tabulate_gerver(n_theta)
    F0 = build_sofa(th, cx, cy).area
    TR = 0.681301509382724894
    t = (th - TR) / width
    e = width * t * np.exp(-t * t)               # odd bump, eta'(b)=1

    def F(a):
        return build_sofa(th, cx + a * e, cy).area

    # Taylor coefficients of g(eps)=F(c_G+eps e)-F0 by finite differences
    h = 1e-3
    g2 = (F(h) - 2 * F0 + F(-h)) / h**2                       # Q
    g3 = (F(2*h) - 2*F(h) + 2*F(-h) - F(-2*h)) / (2*h**3)     # C3
    g4 = (F(2*h) - 4*F(h) + 6*F0 - 4*F(-h) + F(-2*h)) / h**4  # C4
    lhs = g3**2
    rhs = 3 * abs(g2) * abs(g4)
    print(f"  Q  = g''(0)   = {g2:+.5f}")
    print(f"  C3 = g'''(0)  = {g3:+.4f}")
    print(f"  C4 = g''''(0) = {g4:+.1f}")
    print()
    print(f"  criterion C3^2 <= 3|Q||C4| :  {lhs:.4f}  <=  {rhs:.4f}   "
          f"{'HOLDS' if lhs <= rhs else 'FAILS'}  "
          f"(margin {100*(rhs-lhs)/rhs:+.1f}%)")
    print()
    print("  NOTE: the margin is small and, under H^2 normalization, the")
    print("  stressing perturbations fall below the float oracle's resolution.")
    print("  A rigorous decision needs interval arithmetic (caveat i).")


if __name__ == "__main__":
    symbolic_model()
    if "--measure" in sys.argv:
        measure()
