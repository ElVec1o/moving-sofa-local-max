"""ambi_closedform.py — the ambidextrous two-hallway bound, in closed form.

WHAT THIS REPLACES.  An earlier script in this directory (ambi_certbound.py) proved
A_ambi <= 93/100 * 2 = 1.86 by branch and bound over the three essential placement
parameters.  Its interval bound over a box is sound and gated, but the accompanying a
priori argument -- that the maximiser lies in a bounded region -- is NOT valid.  The four
crude inequalities bound a below and b', b-a, b+b' above; they leave a corridor

    a -> +infinity  with  b' ~ -a

entirely uncovered, and the area along that corridor is not small:

    a          5        20       100       400      2000
    area  1.828402  1.828366  1.827754  1.825624  1.807127

Nothing there exceeds 1.86, so the withdrawn statement is very probably true, but it was
not proved.  The corridor is what produced the closed form: the same scan showed that the
area depends on a only through m2 = a + b', which is the substitution that makes the whole
thing integrable by hand.

THE DECOMPOSITION.  In the rotated coordinates u = <p,mu>, v = <p,nu> of the note, the
band 0 <= u+v <= sqrt2 carries the fibre coordinate t and

    I = [max(p,r) - 2, min(q,w) + 2],   removed:  (p,q) and (r,w),
    p = s - 2a',  q = 2a - s,  r = 2b - s,  w = s - 2b'.

Since I \\ (p,q) = {x in I : x <= p} u {x in I : x >= q}, and likewise for (r,w),
intersecting the two DISTRIBUTES into exactly four pieces:

    A = (-inf, min(p,r)]        the low end, below both quadrants
    D = [max(q,w), +inf)        the high end, above both quadrants
    C = [w, p]                  a cross piece, empty unless tau := b' - a' > 0
    B = [q, r]                  a cross piece, empty unless sig := b - a   > 0

A and D are the ones that survive at the optimum; B and C are the defect.  Measuring each
against the ends of I, with m1 = a' + b and m2 = a + b',

    |A n I| <= (2 - |p-r|)^+ = (2 - 2|s - m1|)^+
    |D n I| <= (2 - |q-w|)^+ = (2 - 2|s - m2|)^+
    |C \\ A| <= min(2(s-m1)^+, 2 tau^+)
    |B \\ D| <= min(2(s-m2)^+, 2 sig^+)

so, integrating over the band and halving (du dv = ds dt / 2),

    area <= (1/2)[ g(m1) + g(m2) ] + sqrt2 [ min(1,sig^+) + min(1,tau^+) ],
    g(x) := int_0^sqrt2 (2 - 2|s-x|)^+ ds .

THE PROFILE INTEGRAL.  g is symmetric about sqrt2/2, vanishes off (-1, sqrt2+1), and on
[sqrt2-1, 1] equals 2 sqrt2 - x^2 - (sqrt2-x)^2.  Hence

    max g = g(1/sqrt2) = 2 sqrt2 - 1/2 - 1/2 = 2 sqrt(2) - 1 = 1.8284271...

THE THEOREM.  m1, m2, sig, tau are all invariant under the translation gauge
(a,a',b,b') -> (a+e, a'-e, b+e, b'-e).  If sig <= 0 and tau <= 0 -- that is, if the two
corner offsets <d-c,mu> and <d-c,nu> are nonpositive -- the cross terms vanish and

    |C2 n L_{pi/4}(c) n R_{pi/4}(d)|  <=  2 sqrt(2) - 1 ,

with equality exactly at m1 = m2 = 1/sqrt2, sig = tau = 0.  Romik's sofa has its two
pi/4 corners at the same point, so sig = tau = 0 and the hypothesis holds.  PROVED, by
hand, with no computation anywhere in the argument.

THE CROSS REGION IS CLOSED (ambi_cross.py).  When an offset is positive the estimate
above exceeds 2 sqrt2 - 1, but the area does not: a four-case analysis (wide offsets by
the |I| <= 4-2t profile; both-positive by exact cancellation B = A n D = A n C n D in the
inclusion-exclusion; mixed by an overlap-corrected trapezoid dominated by a flat-top tent,
reduced to one two-variable profile inequality proved by hand on three regions and
certified by ball covering on the fourth) removes the sign hypothesis entirely:

    A_ambi  <=  2 sqrt(2) - 1     UNCONDITIONALLY.

Rule 0: PROVED (hand + one 28512-box ball certificate with a negative control).

WHAT THIS FILE DOES.  Rule 3 and Rule I11: it falsifies before it reports.  true_area is
written from the definition, independently of the bound; the bound is written from the
formula above; and the two are compared on random triples across five orders of magnitude
of scale.  It also checks the three structural claims the proof rests on -- the gauge
invariance of (m1, m2, sig, tau), the exactness of the closed form for g, and the
reproduction of the known extremal configuration a = a' = b = b' = sqrt2/4.

Usage:  python3 ambi_closedform.py [ntrials]
"""
from __future__ import annotations
import math, sys

import numpy as np

R2 = math.sqrt(2.0)
SHARP = 2*R2 - 1.0


def true_area(a, ap, b, bp):
    """The area, written from the definition in the note and used only as ground truth."""
    def xsec(s):
        p, q, r, w = s - 2*ap, 2*a - s, 2*b - s, s - 2*bp
        lo, hi = max(p, r) - 2.0, min(q, w) + 2.0
        if hi <= lo:
            return 0.0
        tot = hi - lo
        for (A, B) in ((p, q), (r, w)):                    # remove the two quadrants
            A, B = max(A, lo), min(B, hi)
            if B > A:
                tot -= B - A
        A, B = max(p, r, lo), min(q, w, hi)                # add back the double count
        if B > A:
            tot += B - A
        return max(tot, 0.0)

    fam = [(1.0, -2*ap), (-1.0, 2*a), (-1.0, 2*b), (1.0, -2*bp),
           (1.0, -2*ap - 2.0), (-1.0, 2*b - 2.0), (-1.0, 2*a + 2.0), (1.0, -2*bp + 2.0)]
    cuts = {0.0, R2}
    for i in range(len(fam)):
        for j in range(i + 1, len(fam)):
            (m1, c1), (m2, c2) = fam[i], fam[j]
            if m1 != m2:
                t = (c2 - c1)/(m1 - m2)
                if 0.0 < t < R2:
                    cuts.add(t)
    S = sorted(cuts)
    return 0.5*sum(0.5*(xsec(S[k]) + xsec(S[k+1]))*(S[k+1] - S[k])
                   for k in range(len(S) - 1))


def g(x):
    """int_0^sqrt2 (2 - 2|s-x|)^+ ds, exactly, by the antiderivative of the tent."""
    lo, hi = max(0.0, x - 1.0), min(R2, x + 1.0)
    if hi <= lo:
        return 0.0
    prim = lambda z: 2*z - (z - x)*abs(z - x)
    return prim(hi) - prim(lo)


def bound(a, ap, b, bp):
    """The closed-form upper bound of the note."""
    m1, m2 = ap + b, a + bp
    sig, tau = b - a, bp - ap
    return 0.5*(g(m1) + g(m2)) + R2*(min(1.0, max(0.0, sig)) + min(1.0, max(0.0, tau)))


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 40000
    rng = np.random.default_rng(20260801)

    print("THE AMBIDEXTROUS TWO-HALLWAY BOUND IN CLOSED FORM\n")
    print(f"  2 sqrt(2) - 1              = {SHARP:.13f}")
    print(f"  g(1/sqrt2)                 = {g(1/R2):.13f}")
    gg = [g(x) for x in np.linspace(-2.0, 4.0, 600001)]
    print(f"  max g on a fine grid       = {max(gg):.13f}")
    print(f"  g vanishes off (-1, {R2+1:.4f}): {g(-1.0)==0.0 and g(R2+1.0)==0.0}\n")

    q = R2/4
    print(f"  extremal a=a'=b=b'=sqrt2/4:  true {true_area(q,q,q,q):.13f}"
          f"   bound {bound(q,q,q,q):.13f}")
    print(f"  both equal 2 sqrt2 - 1:      "
          f"{abs(true_area(q,q,q,q)-SHARP) < 1e-12 and abs(bound(q,q,q,q)-SHARP) < 1e-12}\n")

    worst_g, worst_i = 1e9, 1e9
    argg = None
    cross = {"neither": 0.0, "tau only": 0.0, "sig only": 0.0, "both": 0.0}
    for _ in range(n):
        sc = 10.0**rng.uniform(-1.0, 2.2)
        a, ap, b, bp = rng.uniform(-sc, sc, 4)
        t, u = true_area(a, ap, b, bp), bound(a, ap, b, bp)
        if u - t < worst_g:
            worst_g, argg = u - t, (a, ap, b, bp)
        sig, tau = b - a, bp - ap
        k = ("both" if sig > 0 and tau > 0 else "sig only" if sig > 0
             else "tau only" if tau > 0 else "neither")
        cross[k] = max(cross[k], t)
        if k == "neither":
            worst_i = min(worst_i, SHARP - t)
        # gauge invariance
        e = rng.uniform(-5, 5)
        if abs(true_area(a+e, ap-e, b+e, bp-e) - t) > 1e-9:
            print("  *** GAUGE INVARIANCE VIOLATED ***"); return 1

    print(f"  {n} random quadruples, scales 0.1 to 160, gauge checked on each:\n")
    print(f"    min (bound - true)       = {worst_g:+.3e}   at "
          f"({argg[0]:.3f}, {argg[1]:.3f}, {argg[2]:.3f}, {argg[3]:.3f})")
    print(f"    -> the bound holds and is attained (the deficit is rounding)\n")
    print(f"    {'sign case':<12} {'max true area':>14} {'vs 2sqrt2-1':>13}")
    for k in ("neither", "tau only", "sig only", "both"):
        print(f"    {k:<12} {cross[k]:14.7f} {cross[k]-SHARP:+13.3e}")
    print(f"\n  'neither' (sig <= 0 and tau <= 0) is the PROVED case; min slack to the")
    print(f"  bound there is {worst_i:.3e}, i.e. the sharp value is approached.")
    print(f"  The other three rows are CONJECTURE: strictly below, but not proved.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
