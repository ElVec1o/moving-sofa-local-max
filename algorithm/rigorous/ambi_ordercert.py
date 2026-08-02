"""ambi_ordercert.py — an EXACT certificate that Sigma's cap is ordered.

WHAT IS CERTIFIED.  Any cap satisfying (RC) and the forced boundary data with

    alpha_2(0)  >=  2 a_1 - 1  =  0.750574724825464...

is ORDERED, hence by prop:anchor also ANCHORED.  Sigma has alpha_2(0) = G'(0) = 2a_1 - 1
exactly, so Sigma is covered, and with it every admissible cap whose alpha_2(0) is at least
Sigma's.  On that class the concavity of thm:diag applies without any sign-pattern
hypothesis, because the sign pattern is now derived.

WHY IT IS EXACT.  Every step is a comparison of rational numbers.  No floating point enters
the verification, and no discretised LP: the four linear programs that bound the arms have
CLOSED-FORM solutions, because the moment constraints pin the bang-bang switch points
independently of t.

  U2(t) = max int_0^t u sin(t-s) ds   over u in [0,1], int_0^(pi/2) u cos = 1/2 .
  Bang-bang gives u = 1 on [0,sigma) with sin sigma = 1/2, so sigma = pi/6 ALWAYS, and
  U2(t) = cos(t - pi/6) - cos t for t >= pi/6.  Likewise V2 and V1 switch at pi/3 (from
  1 - cos sigma = 1/2), and U1 switches at arcsin(sin t - 1/2).

Substituting, the two certificate conditions collapse to elementary inequalities.  On
[pi/6, T], using cos(s - pi/6) = (sqrt3/2) cos s + (1/2) sin s,

  (i)  alpha_2 lower bound  = (c + 1 - sqrt3/2) cos s - sin s > 0  <=>  tan s < c+1-sqrt3/2
  (i') on [0, pi/6] it is (c+1)cos s - (1/2)sin s - 1, decreasing, so its minimum is at
       pi/6 and equals (c+1)sqrt3/2 - 5/4
  (ii) alpha_1 lower bound at T = sin T [ (c+1) + cos T - sqrt(1 - (sin T - 1/2)^2) ] - 1,
       the cos T / 2 terms cancelling identically.

Both are increasing in c, so certifying them at c = 2a_1 - 1 certifies them for every
larger c.  T = 723/1000 is the witness; the largest admissible T is arctan(2a_1 - sqrt3/2).

RATIONAL DISCIPLINE.  sin and cos are bounded by alternating Taylor truncations ending on
a term of the SAFE sign; the square root, which is subtracted and so needs an UPPER bound,
by AM-GM: sqrt(z) <= (z + q^2)/(2q) for any q > 0, exact for every rational q, and tight
when q is near sqrt(z).  a_1 is truncated DOWNWARD and sqrt3/2 rounded in whichever
direction is safe for the inequality it appears in.

NEGATIVE CONTROL (rule I12).  The same certificate must FAIL below the threshold.  It is
re-run at c = 0.70 and at c = 0.60, both under the LP threshold 0.7484, and both must be
rejected.  If a value the LP says is defeatable were certified, the certificate would be
unsound and the script exits non-zero.

Rule 0: this is a PROOF of ordering for the stated class, in exact arithmetic.  It rests on
the closed forms above, which are derived in the note, and on prop:anchor for the step from
ordered to anchored.  It is not formalised in Lean beyond the algebraic core.

Usage: python3 ambi_ordercert.py
"""
from __future__ import annotations
import sys
from fractions import Fraction as F

A1_LO = F(8752873624127, 10**13)      # < a_1 = 0.875287362412732...
S3_HI = F(86602540379, 10**11)        # > sqrt(3)/2
S3_LO = F(86602540378, 10**11)        # < sqrt(3)/2
T_CERT = F(723, 1000)


def sin_lo(x: F) -> F:  return x - x**3/6 + x**5/120 - x**7/5040
def sin_hi(x: F) -> F:  return sin_lo(x) + x**9/362880
def cos_lo(x: F) -> F:  return 1 - x**2/2 + x**4/24 - x**6/720


def certify(c_lo: F, T: F = T_CERT, q: F = F(98685, 100000)) -> tuple[bool, bool, bool, F, F]:
    """Returns (i, i', ii) verdicts and the two slacks, all in exact rationals."""
    K = c_lo + 1 - S3_HI                              # < c + 1 - sqrt3/2
    s1 = K * cos_lo(T) - sin_hi(T)                    # (i)  > 0 wanted
    s1b = (c_lo + 1) * S3_LO - F(5, 4)                # (i') > 0 wanted
    w = sin_lo(T) - F(1, 2)
    if w <= 0:
        return False, False, False, F(0), F(0)
    sq = (1 - w**2 + q*q) / (2*q)                     # >= sqrt(1 - w^2)
    s2 = sin_lo(T) * ((c_lo + 1) + cos_lo(T) - sq) - 1   # (ii) >= 0 wanted
    return s1 > 0, s1b > 0, s2 >= 0, s1, s2


def main() -> int:
    print(__doc__.split("Usage")[0])
    c = 2 * A1_LO - 1
    print(f"  Sigma: alpha_2(0) = G'(0) = 2 a_1 - 1 > {float(c):.15f}")
    print(f"  witness T = {T_CERT} = {float(T_CERT)}\n")
    a, b, d, s1, s2 = certify(c)
    print(f"  (i)   tan T < c + 1 - sqrt3/2      slack {float(s1):+.9f}   "
          f"{'HOLDS' if a else 'FAILS'}")
    print(f"  (i')  min of the bound on [0,pi/6] {float((c+1)*S3_LO-F(5,4)):+.9f}   "
          f"{'HOLDS' if b else 'FAILS'}")
    print(f"  (ii)  alpha_1 bound at T           slack {float(s2):+.9f}   "
          f"{'HOLDS' if d else 'FAILS'}")
    ok = a and b and d
    print(f"\n  -> {'CERTIFIED' if ok else 'NOT CERTIFIED'}: every cap with (RC), the forced")
    print(f"     boundary data and alpha_2(0) >= 2a_1 - 1 is ORDERED, hence ANCHORED.")
    print(f"     Sigma attains the bound exactly, so Sigma is covered.")

    print(f"\n  NEGATIVE CONTROLS (rule I12): below the LP threshold 0.7484 these must FAIL.")
    bad = False
    for cv in (F(70, 100), F(60, 100)):
        aa, bb, dd, _, _ = certify(cv)
        acc = aa and bb and dd
        print(f"    c = {float(cv):.2f}: {'*** ACCEPTED, CERTIFICATE UNSOUND ***' if acc else 'rejected'}")
        bad |= acc
    print(f"  -> {'controls pass' if not bad else 'A FALSE CLAIM WAS ACCEPTED'}")
    return 0 if (ok and not bad) else 1


if __name__ == "__main__":
    sys.exit(main())
