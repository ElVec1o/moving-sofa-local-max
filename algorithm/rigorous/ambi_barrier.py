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

RESULT.  Scanning (lambda, kappa) and requiring BOTH halves to certify, the best is
(11/20, 1/5) with

    min(c_L, c_R) > 9/20 ,

5.4 times the 1/12 the elementary chain gives and 62% of the sharp c* = 0.7309566.  The
true decoupled values there are c_R = 0.4748 and c_L = 2.4414, so the certificate captures
95% of what is available and the RIGHT half binds.

Why those parameters and not the note's (9/20, 1/4): for the Dirichlet-Dirichlet left half
the phase runs to pi, and once an upper barrier passes pi/2 it knows only sin^2 <= 1,
because an upper bound on theta is a LOWER bound on sin there.  The left barrier is
therefore lossy, and at (9/20, 1/4) it -- not the right half -- was the limit.  Raising
kappa shrinks the left weight and makes the left half slack, after which the right half
binds and the certificate improves from 37/100 to 9/20.  A two-sided barrier would remove
the limitation outright and is the obvious next step; it is not built.  Rule 0: this is a PROOF of the stated
inequality for the DECOUPLED half, in exact arithmetic, but it is not yet formalised in
Lean and it does not by itself upgrade prop:elem, which also needs the left half and the
re-assembly.  HEURISTIC until those are done; the arithmetic here is exact.

NEGATIVE CONTROL (rule I12).  Each barrier must FAIL above the corresponding true
eigenvalue: the right half at c = 1 and the left at c = 3.  If either is accepted the
certificate is unsound and the script exits non-zero.

Usage: python3 ambi_barrier.py [nseg]
"""
from __future__ import annotations
import sys
from fractions import Fraction as F

# --- rational data, each rounded in the SAFE direction -------------------------------
PI2_HI = F(15707964, 10000000)   # > pi/2 : used for the domain length
PI2_LO = F(15707963, 10000000)   # < pi/2 : used for the target
BETA_HI = F(2896539, 10000000)   # > beta
# The decoupling parameters.  (9/20, 1/4) is the note's choice for prop:elem; a scan
# over both halves finds (11/20, 1/5) certifies more, because the LEFT half is the
# binding one for the barrier (see below) and a larger kappa shrinks its weight.
LAM = F(11, 20)
KAPPA = F(1, 5)
QBAR = 1 + 1/KAPPA
RCOEF = LAM/(1 - LAM)


def ceil_rat(x: F, D: int) -> F:
    """Smallest rational with denominator D that is >= x.  Rounding UP is safe."""
    return F(-((-x.numerator * D) // x.denominator), D)


def sin_hi(x: F) -> F:
    """Upper bound for sin x, x >= 0: alternating truncation ending on a + term."""
    return x - x**3 / 6 + x**5 / 120


PI_LO = F(31415926, 10000000)     # < pi : the Dirichlet-Dirichlet target


def w_lo_R(t: F) -> F:
    """RIGHT half: LOWER bound for the weight, so 1/w_lo is an UPPER bound for 1/w."""
    return F(1) if t >= PI2_LO - BETA_HI else 1 + LAM


def m_hi_R(t: F) -> F:
    """RIGHT half: UPPER bound for the mass coefficient."""
    return 1 + QBAR if t < BETA_HI else F(1)


def w_lo_L(t: F) -> F:
    """LEFT half: w = 1 - kappa on [0, beta), 2 after."""
    return F(1) - KAPPA if t < BETA_HI else F(2)


def m_hi_L(t: F) -> F:
    """LEFT half: m = 2 + r on [0, pi/2 - beta), 2 after."""
    return 2 + RCOEF if t < PI2_HI - F(2896538, 10000000) else F(2)


def barrier(c: F, nseg: int, D: int = 10**7, half: str = "R"):
    """Returns (B_T, status).  B_T is None when the barrier crosses its target.

    half = "R": Dirichlet-Neumann, target pi/2.   half = "L": Dirichlet-Dirichlet,
    target pi.  Note the sin upper bound degrades badly for large argument, so the
    left half certifies far less than its true eigenvalue -- which does not matter,
    because the assembly needs min(c_L, c_R) and the right half is the binding one."""
    w_lo, m_hi = (w_lo_R, m_hi_R) if half == "R" else (w_lo_L, m_hi_L)
    target = PI2_LO if half == "R" else PI_LO
    cap = PI2_HI if half == "R" else PI_LO
    B = F(0)
    step = ceil_rat(PI2_HI / nseg, D)
    for i in range(nseg):
        t0 = i * step
        inv = F(1) / w_lo(t0)
        coef = m_hi(t0) + c - inv
        if coef < 0:
            return None, "coefficient negative: the monotone bound is invalid here"
        sl = inv + coef * min(F(1), sin_hi(min(cap, B))**2)
        for _ in range(30):
            cand = inv + coef * min(F(1), sin_hi(min(cap, B + sl * step))**2)
            if cand <= sl:
                break
            sl = ceil_rat(cand, D)
        B = ceil_rat(B + ceil_rat(sl, D) * step, D)
        if B >= target:
            tgt = "pi/2" if half == "R" else "pi"
            return None, f"crossed {tgt} at t = {float(t0):.4f}"
    return B, "ok"


def main() -> int:
    nseg = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
    print(__doc__.split("Usage")[0])
    print(f"CERTIFICATES ({nseg} segments, exact rationals, denominators capped 1e7)\n")
    print(f"  {'c':>10} {'B(T)':>10}   status")
    best = None
    for num, den in ((37, 100), (2, 5), (9, 20), (1, 2)):
        c = F(num, den)
        B, st = barrier(c, nseg)
        if B is not None:
            best = c
        print(f"  {num:4d}/{den:<5d} {float(B) if B else float('nan'):10.5f}   "
              f"{'PROVES c_1 > ' + f'{num}/{den}' if B else st}")
    print(f"\n  best certified lower bound: c_1 > {best}  ({float(best):.4f})")
    print(f"  true value at these parameters (float Prufer): c_R = 0.4748, c_L = 2.4414")
    print(f"  the elementary chain of prop:elem gives 1/12 = 0.0833 on this half")

    print(f"\nLEFT HALF (Dirichlet-Dirichlet, target pi):")
    bestL = None
    for num, den in ((37, 100), (2, 5), (9, 20), (1, 2)):
        c = F(num, den)
        B, st = barrier(c, nseg, half="L")
        if B is not None:
            bestL = c
        print(f"  {num:4d}/{den:<5d} {float(B) if B else float('nan'):10.5f}   "
              f"{'PROVES c_L > ' + f'{num}/{den}' if B else st}")
    print(f"  At these parameters the left half is slack (true c_L = 2.44) and the RIGHT")
    print(f"  half binds, in the certificate and in truth alike.  The sin upper bound")
    print(f"  still degrades near pi -- past pi/2 an upper barrier knows only sin^2 <= 1,")
    print(f"  since an upper bound on theta gives a LOWER bound on sin there -- which is")
    print(f"  why a larger kappa, shrinking the left weight, was needed to make the left")
    print(f"  half slack.  A two-sided barrier would remove the limitation entirely.")

    if bestL is not None and best is not None:
        m = min(bestL, best)
        print(f"\n  ASSEMBLED HAND CONSTANT: min(c_L, c_R) > {m} = {float(m):.4f}")
        print(f"  against 1/12 = {1/12:.4f} from prop:elem, a factor of {float(m)*12:.2f},")
        print(f"  and {100*float(m)/0.7309566:.1f}% of the sharp c* = 0.7309566.")

    print(f"\nNEGATIVE CONTROLS (rule I12): each must FAIL.")
    B1, st1 = barrier(F(1), nseg, half="R")
    print(f"  right half at c = 1: {st1}")
    B2, st2 = barrier(F(3), nseg, half="L")
    print(f"  left half  at c = 3   > 2.689 : {st2}")
    ok = B1 is None and B2 is None
    print(f"  -> {'both controls pass' if ok else '*** A FALSE CLAIM WAS ACCEPTED ***'}")
    return 0 if ok and best is not None and bestL is not None else 1


if __name__ == "__main__":
    sys.exit(main())
