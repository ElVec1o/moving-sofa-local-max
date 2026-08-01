"""ambi_cross.py — closing the cross region: A_ambi <= 2 sqrt2 - 1 UNCONDITIONALLY.

WHAT REMAINED OPEN.  ambi_closedform.py proves |C2 n L n R| <= 2 sqrt2 - 1 when both
corner offsets d_mu = <d-c,mu> and d_nu = <d-c,nu> are nonpositive.  This file closes the
other sign cases.  Throughout, by the u <-> v swap symmetry (reflection across the
diagonal, which preserves the band and exchanges primes) assume WLOG t := d_nu >= d_mu,
and t > 0 (else the proved case applies).  m1 = a'+b, m2 = a+b', D = m2-m1 = t - d_mu >= 0.

THE THREE CASES.

CASE 1 (t >= 1).  In the middle window m1 < s < m2 the outer interval has length
|I| = 4-2t, and outside it |I| = 4-2t-2(m1-s)^+ resp. -2(s-m2)^+.  So pointwise
    ell(s) <= (4-2t-2(m1-s)^+-2(s-m2)^+)^+ <= 4-2t,
and integrating over the band of length sqrt2:  area <= sqrt2 (2-t)^+ <= sqrt2 < 2sqrt2-1.
PROVED (three lines; the |I| formulas are the same sign computations as in the note).

CASE 2 (0 < t < 1 and d_mu > 0).  Both cross pieces B = [q,r] and C = [w,p] are nonempty.
In the middle window B = A n D = A n C n D, so inclusion-exclusion for |A u C u D| loses
the -|A n D| and +|A n C n D| terms against each other, and the excess
    c(s) = |C n I| - |A n C n I| - |C n D n I| = 2t - 2(n2-s) - 2(s-n1) = 2D - 2t
        = -2 d_mu < 0.
The excess is NEGATIVE: the no-cross tent bound ell <= tent1 + tent2 holds verbatim, and
    area <= (1/2)[g(m1)+g(m2)] <= 2 sqrt2 - 1.
PROVED (the both-positive case is EASIER than the mixed one).

CASE 3 (0 < t < 1 and d_mu <= 0, so D = t+u with u = -d_mu >= 0).  The overlap-corrected
excess is a trapezoid c(s) = 2t - 2(m1+t-s)^+ - 2(s-m2+t)^+ on the window, and it is
dominated pointwise by the flat-top tent
    c(s) <= min(2(s-m1)^+, 2(m2-s)^+, 2 tau),   tau = min(t,u) <= min(1, D/2).
Hence, with E(m1,m2,tau) = int_0^sqrt2 of that flat-top tent,
    area <= (1/2)[ g(m1) + g(m2) + E(m1, m2, min(1, D/2)) ]           (E monotone in tau)
and everything reduces to

  LEMMA E.  g(m1) + g(m2) + E(m1, m2, min(1,(m2-m1)/2)) <= 2(2 sqrt2 - 1) for m1 <= m2.

PROOF OF LEMMA E, in four regions.
  (i)  Central square m1, m2 in [sqrt2-1, 1]:  by hand.  There g(m) = 2sqrt2-1-2(m-c0)^2
       exactly (c0 = sqrt2/2), and E <= area of the unclipped trapezoid <= D^2/2.  With
       x1 = m1-c0, x2 = m2-c0 and D^2 = (x2-x1)^2 <= 2(x1^2+x2^2):
           total <= 2(2sqrt2-1) - 2x1^2 - 2x2^2 + (x1^2+x2^2) <= 2(2sqrt2-1),
       equality only at m1 = m2 = c0 -- the extremal configuration, as it must be.
  (ii) Left tail m1 <= -1:  by hand.  g(m1) = 0 and E is increasing as m1 decreases, so
       total <= g(y) + int_0^sqrt2 min(2(y-s)^+, 2) ds =: h(y), y = m2.  Piecewise:
       y<=0: h=(1+y)^+^2<=1;  0<=y<=sqrt2-1: h=1+2y<=2sqrt2-1;  sqrt2-1<=y<=sqrt2+1:
       h = 2sqrt2-(y-sqrt2)^2 <= 2sqrt2;  y>=sqrt2+1: h=2sqrt2.  Max 2sqrt2 < 4sqrt2-2.
  (iii) Right tail m2 >= sqrt2+1: the mirror of (ii) under s -> sqrt2-s.
  (iv) The rest: R = {-1 <= m1 <= m2 <= sqrt2+1} minus the OPEN central square.  CERTIFIED
       HERE by adaptive ball-arithmetic covering: on every box the enclosure of
       2(2sqrt2-1) - g(m1) - g(m2) - E is strictly positive.  The infimum over (iv) is
       positive because the only equality point of Lemma E is interior to (i), so the
       covering terminates.

E IN CLOSED FORM (ball-evaluable, no branching): with al = max(0, m1),
be = max(al, min(sqrt2, m2)), k1 = m1+tau, k2 = m2-tau (k1 <= k2 always since
tau <= D/2), b1 = max(al, min(be, k1)), a3 = max(al, min(be, k2)):
    E = [(b1-m1)^2 - (al-m1)^2] + 2 tau (a3 - b1) + [(m2-a3)^2 - (m2-be)^2].
Each bracket is the exact integral of its linear piece; min/max of balls via
(x+y-|x-y|)/2, which arb encloses soundly.

RULE 3 RECORD (this file, mode "check"): the closed form for E agrees with direct
numerical integration to 6e-12 on 20000 random (m1,m2,tau); the Case 1/2/3 pointwise
bounds hold on 40000 samples each with min slack >= -9e-16 (rounding); the assembled
area bound holds against the true two-hallway area on 40000 random placements in the
cross region, min slack +1.6e-04 (attained near the no-cross boundary, as expected).

CONSEQUENCE (with ambi_closedform.py):  every ambidextrous moving sofa satisfies
    |S| <= 2 sqrt2 - 1 = 1.8284271247...,
no hypotheses.  The first upper bound specific to the ambidextrous problem, and sharp for
the two-hallway relaxation.

Usage:
  python3 ambi_cross.py check          # Rule 3 falsification battery
  python3 ambi_cross.py certify        # Lemma E region (iv), resumes from checkpoint
"""
from __future__ import annotations
import json, math, os, sys, time
from fractions import Fraction as Q

import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))

R2 = math.sqrt(2.0)
M2 = 2*(2*R2 - 1.0)


# ---------------------------------------------------------------- float versions
def g_f(x):
    lo = max(0.0, x - 1.0); hi = max(lo, min(R2, x + 1.0))
    prim = lambda z: 2*z - (z - x)*abs(z - x)
    return prim(hi) - prim(lo)


def E_f(m1, m2, tau):
    tau = min(tau, (m2 - m1)/2)          # cap never binds past D/2: same integrand
    al = max(0.0, m1); be = max(al, min(R2, m2))
    k1, k2 = m1 + tau, m2 - tau
    b1 = max(al, min(be, k1)); a3 = max(al, min(be, k2))
    return ((b1 - m1)**2 - (al - m1)**2) + 2*tau*(a3 - b1) \
        + ((m2 - a3)**2 - (m2 - be)**2)


def ell_f(s, a, ap, b, bp):
    p, q, r, w = s - 2*ap, 2*a - s, 2*b - s, s - 2*bp
    lo, hi = max(p, r) - 2.0, min(q, w) + 2.0
    if hi <= lo:
        return 0.0
    tot = hi - lo
    for (A, B) in ((p, q), (r, w)):
        A, B = max(A, lo), min(B, hi)
        if B > A:
            tot -= B - A
    A, B = max(p, r, lo), min(q, w, hi)
    if B > A:
        tot += B - A
    return max(tot, 0.0)


def area_f(a, ap, b, bp):
    fam = [(1.0, -2*ap), (-1.0, 2*a), (-1.0, 2*b), (1.0, -2*bp),
           (1.0, -2*ap - 2.0), (-1.0, 2*b - 2.0), (-1.0, 2*a + 2.0), (1.0, -2*bp + 2.0)]
    cuts = {0.0, R2}
    for i in range(len(fam)):
        for j in range(i + 1, len(fam)):
            (s1, c1), (s2, c2) = fam[i], fam[j]
            if s1 != s2:
                z = (c2 - c1)/(s1 - s2)
                if 0.0 < z < R2:
                    cuts.add(z)
    S = sorted(cuts)
    return 0.5*sum(0.5*(ell_f(S[k], a, ap, b, bp) + ell_f(S[k+1], a, ap, b, bp))
                   * (S[k+1] - S[k]) for k in range(len(S) - 1))


# ---------------------------------------------------------------- Rule 3 battery
def check():
    rng = np.random.default_rng(7)
    print("RULE 3 BATTERY\n")

    worst = 0.0
    for _ in range(20000):
        m1 = rng.uniform(-2, 3); m2 = m1 + rng.uniform(0, 3); tau = rng.uniform(0, 1)
        ss = np.linspace(0.0, R2, 3001)
        direct = np.trapezoid(np.minimum.reduce([2*np.maximum(ss - m1, 0),
                                                 2*np.maximum(m2 - ss, 0),
                                                 np.full_like(ss, 2*tau)]), ss)
        worst = max(worst, abs(direct - E_f(m1, m2, tau)))
    print(f"  E closed form vs direct integral, 20000 triples: max |diff| = {worst:.1e}")

    tests = [("case 1: ell <= (4-2t-...)^+, t>=1", 1), ("case 2: ell <= tents, both>0", 2),
             ("case 3: ell <= tents+flat-top", 3)]
    for name, mode in tests:
        worst = 1e9
        for _ in range(40000):
            ap = 0.0
            if mode == 1:
                t = rng.uniform(1.0, 2.5); dm = rng.uniform(-2.0, t)
            elif mode == 2:
                t = rng.uniform(1e-4, 1.0); dm = rng.uniform(1e-4, t)
            else:
                t = rng.uniform(1e-4, 1.0); dm = -rng.uniform(0.0, 3.0)
            bp = t; a = rng.uniform(-2, 3); b = a + dm
            m1, m2 = ap + b, a + bp
            s = rng.uniform(0.0, R2)
            if mode == 1:
                F = max(0.0, 4 - 2*t - 2*max(0.0, m1 - s) - 2*max(0.0, s - m2))
            else:
                F = max(0.0, 2 - 2*abs(s - m1)) + max(0.0, 2 - 2*abs(s - m2))
                if mode == 3:
                    tau = min(t, -dm)
                    F += max(0.0, min(2*(s - m1), 2*(m2 - s), 2*tau))
            worst = min(worst, F - ell_f(s, a, ap, b, bp))
        print(f"  {name}: 40000 samples, min slack = {worst:+.1e}")

    worst = 1e9
    for _ in range(40000):
        ap = 0.0; t = rng.uniform(1e-4, 2.5); bp = t
        dm = rng.uniform(-3.0, t)
        a = rng.uniform(-2, 3); b = a + dm
        m1, m2 = ap + b, a + bp
        if t >= 1:
            bnd = R2*max(0.0, 2 - t)
        elif dm > 0:
            bnd = 0.5*(g_f(m1) + g_f(m2))
        else:
            bnd = 0.5*(g_f(m1) + g_f(m2) + E_f(m1, m2, min(1.0, (m2 - m1)/2)))
        worst = min(worst, bnd - area_f(a, ap, b, bp))
    print(f"  assembled bound vs true area, 40000 cross placements: "
          f"min slack = {worst:+.1e}")
    print(f"\n  every bound <= 2sqrt2-1 target is Lemma E's job; run 'certify'.")


# ---------------------------------------------------------------- ball certificate
def qarb_local(x: Q):
    from flint import arb
    return arb(x.numerator)/arb(x.denominator)


def certify():
    from flint import arb, ctx
    ctx.prec = 120

    def bmin(x, y):
        return (x + y - abs(x - y))/2

    def bmax(x, y):
        return (x + y + abs(x - y))/2

    r2 = arb(2).sqrt()

    def g_b(x):
        lo = bmax(arb(0), x - 1); hi = bmax(lo, bmin(r2, x + 1))
        prim = lambda z: 2*z - (z - x)*abs(z - x)
        return prim(hi) - prim(lo)

    def E_b(m1, m2, tau):
        tau = bmin(tau, (m2 - m1)/2)
        al = bmax(arb(0), m1); be = bmax(al, bmin(r2, m2))
        k1, k2 = m1 + tau, m2 - tau
        b1 = bmax(al, bmin(be, k1)); a3 = bmax(al, bmin(be, k2))
        # x*x, not x**2: python-flint routes arb**arb through log, NaN on 0-straddle
        sq = lambda x: x*x
        return (sq(b1 - m1) - sq(al - m1)) + 2*tau*(a3 - b1) \
            + (sq(m2 - a3) - sq(m2 - be))

    def margin(m1, m2):
        D = m2 - m1
        tau = bmin(arb(1), D/2)
        return 2*(2*r2 - 1) - g_b(m1) - g_b(m2) - E_b(m1, m2, tau)

    # region (iv): [-1, sqrt2+1]^2 n {m1 <= m2}, minus the OPEN square (sqrt2-1, 1)^2.
    # rational outer box [-1, 5/2]; central square handled by hand (region (i)).
    # sqrt2-1 in [0.4142, 0.4143], 1 exact: a box is inside (i) iff
    # m1,m2 >= 4143/10000 and <= 1.  boxes with m2 < m1 are empty.
    SQL, SQH = Q(4143, 10000), Q(1)      # inner square: safe SUBSET of (sqrt2-1,1)
    out = os.path.join(THIS, "cross_lemE.json")
    state = {"stack": [["-1", "5/2", "-1", "5/2"]], "done": 0}
    if os.path.exists(out):
        state = json.load(open(out))
        print(f"  resuming: {len(state['stack'])} pending, {state['done']} certified",
              flush=True)
    t0 = time.time(); last = t0
    while state["stack"]:
        xl, xh, yl, yh = [Q(v) for v in state["stack"].pop()]
        if yh <= xl:                      # entirely m2 < m1: empty
            state["done"] += 1; continue
        if SQL <= xl and xh <= SQH and SQL <= yl and yh <= SQH:
            state["done"] += 1; continue  # inside region (i): proved by hand
        m1 = qarb_local(xl).union(qarb_local(xh))
        m2 = qarb_local(yl).union(qarb_local(yh))
        v = margin(m1, bmax(m1, m2))      # clamp m2 >= m1 inside the box
        if v > 0:
            state["done"] += 1
        else:
            if xh - xl < Q(1, 4096) and yh - yl < Q(1, 4096):
                print(f"  *** FAILED at [{float(xl):.5f},{float(xh):.5f}]x"
                      f"[{float(yl):.5f},{float(yh):.5f}] ***", flush=True)
                state["failed"] = [str(xl), str(xh), str(yl), str(yh)]
                json.dump(state, open(out + ".tmp", "w")); os.replace(out + ".tmp", out)
                return False
            if xh - xl >= yh - yl:
                xm = (xl + xh)/2
                state["stack"] += [[str(xl), str(xm), str(yl), str(yh)],
                                   [str(xm), str(xh), str(yl), str(yh)]]
            else:
                ym = (yl + yh)/2
                state["stack"] += [[str(xl), str(xh), str(yl), str(ym)],
                                   [str(xl), str(xh), str(ym), str(yh)]]
        if time.time() - last > 15:
            last = time.time()
            json.dump(state, open(out + ".tmp", "w")); os.replace(out + ".tmp", out)
            print(f"  {state['done']} certified, {len(state['stack'])} pending, "
                  f"{time.time()-t0:5.1f}s", flush=True)
    json.dump(state, open(out + ".tmp", "w")); os.replace(out + ".tmp", out)
    print(f"  COMPLETE: {state['done']} boxes, every margin enclosure > 0, "
          f"{time.time()-t0:5.1f}s", flush=True)
    return True


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "check"
    if mode == "check":
        check(); return 0
    if mode == "certify":
        ok = certify()
        print("CERTIFIED" if ok else "NOT CERTIFIED")
        return 0 if ok else 1
    print("unknown mode"); return 2


if __name__ == "__main__":
    sys.exit(main())
