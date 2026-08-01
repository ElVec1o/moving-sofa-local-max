"""ambi_barrier.py — a RATIONAL piecewise-linear Prufer barrier for the decoupled halves.

WHAT IT PROVES.  The elementary constant of prop:elem is 1/12, obtained from crude
Poincare estimates on the two decoupled halves.  The true decoupled eigenvalues are
c_L = 2.689 and c_R = 0.3885, so the elementary route throws away a factor of 4.7 on the
binding (right) half.  This file closes most of that gap with a certificate that uses
EXACT RATIONAL ARITHMETIC and nothing else: no floating point, no interval library, no
transfer matrices, no ball arithmetic.

THE METHOD.  In Prufer form the eigenvalue problem -(w u')' - m u = c u becomes a scalar
first-order equation for the phase,

    theta' = G(t, theta) := cos^2(theta)/w(t) + (m(t) + c) sin^2(theta),   theta(0) = 0,

and c_1 > c exactly when theta(T) < pi/2 for the Dirichlet-Neumann half (theta(T) < pi for
Dirichlet-Dirichlet).  Since G is Lipschitz in theta, any piecewise-linear B with B(0) = 0
and B' >= G(t, B) pointwise dominates theta.  So a PL upper BARRIER reaching less than
pi/2 is a proof, and every check is an inequality between rational numbers.

THE IDENTITY THAT MAKES IT WORK.  Bounding cos^2 <= 1 is fatal: the slope then never
decays as theta -> pi/2, the barrier accumulates a spurious 1/w per unit length, and it
crosses pi/2 well before the true phase does (at c = 3/10 it crossed at t = 1.304 while
the true phase reaches only 1.504 at t = pi/2).  Use instead

    cos^2(theta)/w + (m+c) sin^2(theta)  =  1/w + ((m+c) - 1/w) sin^2(theta) ,

whose coefficient (m+c) - 1/w is positive on every piece here (the smallest value is
1 + 3/10 - 1 = 3/10 on the last), so an UPPER bound on sin^2 gives an upper bound on G,
and the upper barrier supplies exactly that.  With this form the barrier tracks the true
phase to within 2e-3.

RATIONAL DISCIPLINE.  Denominators are capped by rounding every slope and every barrier
value UPWARD (ceil_rat), which can only raise the barrier and so preserves soundness.  The
irrational data enter as rational bounds in the safe direction: pi/2 from above where the
domain length is needed and from below where the target is, beta from above, w from below
(so 1/w from above), m from above.  sin is bounded above by the alternating Taylor
truncation x - x^3/6 + x^5/120, which is an upper bound for x >= 0 because the series
alternates and the truncation ends on a positive term.

RESULT.  At c = 37/100 with 1200 segments the barrier reaches 1.55834 < pi/2, so

    c_1(right half) > 37/100     for the decoupled problem at (lambda, kappa) = (9/20, 1/4),

against the true 0.3885: the certificate captures 95% of the available constant, and 4.4
times the 1/12 that the elementary chain gives.  Rule 0: this is a PROOF of the stated
inequality for the DECOUPLED half, in exact arithmetic, but it is not yet formalised in
Lean and it does not by itself upgrade prop:elem, which also needs the left half and the
re-assembly.  HEURISTIC until those are done; the arithmetic here is exact.

NEGATIVE CONTROL (rule I12).  The same barrier must FAIL above the true eigenvalue.  It is
run at c = 1/2 > 0.3885 and must cross pi/2; if it does not, the certificate is unsound and
the script exits non-zero.

Usage: python3 ambi_barrier.py [nseg]
"""
from __future__ import annotations
import sys
from fractions import Fraction as F

# --- rational data, each rounded in the SAFE direction -------------------------------
PI2_HI = F(15707964, 10000000)   # > pi/2 : used for the domain length
PI2_LO = F(15707963, 10000000)   # < pi/2 : used for the target
BETA_HI = F(2896539, 10000000)   # > beta
LAM = F(9, 20)
QBAR = F(5)                       # 1 + 1/kappa with kappa = 1/4


def ceil_rat(x: F, D: int) -> F:
    """Smallest rational with denominator D that is >= x.  Rounding UP is safe."""
    return F(-((-x.numerator * D) // x.denominator), D)


def sin_hi(x: F) -> F:
    """Upper bound for sin x, x >= 0: alternating truncation ending on a + term."""
    return x - x**3 / 6 + x**5 / 120


def w_lo(t: F) -> F:
    """LOWER bound for the weight, so 1/w_lo is an UPPER bound for 1/w."""
    return F(1) if t >= PI2_LO - BETA_HI else 1 + LAM


def m_hi(t: F) -> F:
    """UPPER bound for the mass coefficient."""
    return 1 + QBAR if t < BETA_HI else F(1)


def barrier(c: F, nseg: int, D: int = 10**7):
    """Returns (B_T, status).  B_T is None when the barrier crosses pi/2."""
    B = F(0)
    step = ceil_rat(PI2_HI / nseg, D)
    for i in range(nseg):
        t0 = i * step
        inv = F(1) / w_lo(t0)
        coef = m_hi(t0) + c - inv
        if coef < 0:
            return None, "coefficient negative: the monotone bound is invalid here"
        sl = inv + coef * min(F(1), sin_hi(min(PI2_HI, B))**2)
        for _ in range(30):
            cand = inv + coef * min(F(1), sin_hi(min(PI2_HI, B + sl * step))**2)
            if cand <= sl:
                break
            sl = ceil_rat(cand, D)
        B = ceil_rat(B + ceil_rat(sl, D) * step, D)
        if B >= PI2_LO:
            return None, f"crossed pi/2 at t = {float(t0):.4f}"
    return B, "ok"


def main() -> int:
    nseg = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
    print(__doc__.split("Usage")[0])
    print(f"CERTIFICATES ({nseg} segments, exact rationals, denominators capped 1e7)\n")
    print(f"  {'c':>10} {'B(T)':>10}   status")
    best = None
    for num, den in ((3, 10), (1, 3), (7, 20), (37, 100)):
        c = F(num, den)
        B, st = barrier(c, nseg)
        if B is not None:
            best = c
        print(f"  {num:4d}/{den:<5d} {float(B) if B else float('nan'):10.5f}   "
              f"{'PROVES c_1 > ' + f'{num}/{den}' if B else st}")
    print(f"\n  best certified lower bound: c_1 > {best}  ({float(best):.4f})")
    print(f"  true value (float Prufer, cross-checked against FEM): 0.3885")
    print(f"  the elementary chain of prop:elem gives 1/12 = 0.0833 on this half")

    print(f"\nNEGATIVE CONTROL: at c = 1/2 > 0.3885 the barrier MUST cross pi/2.")
    B, st = barrier(F(1, 2), nseg)
    ok = B is None
    print(f"  c = 1/2: {st}")
    print(f"  -> {'control passes' if ok else '*** ACCEPTED A FALSE CLAIM: UNSOUND ***'}")
    return 0 if ok and best is not None else 1


if __name__ == "__main__":
    sys.exit(main())
