"""ambi_certbound.py — branch and bound for the ambidextrous upper bound.

THE STATEMENT BEING CERTIFIED.  By the relaxation (note, Prop "relax") and the coordinate
reduction (Lemma "uv"), any ambidextrous moving sofa satisfies

    |S|  <=  sup over placements of  (1/2) int_0^{sqrt2} l(s) ds ,

where, in the gauge a' = 0 (legitimate by the translation invariance
(a,a',b,b') -> (a+e, a'-e, b+e, b'-e), which leaves the area unchanged),

    p = s,   q = 2a - s,   r = 2b - s,   w = s - 2b' ,
    I = [max(p,r) - 2,  min(q,w) + 2] ,
    l(s) = | I \\ ( (p,q) u (r,w) ) | .

Three parameters (a, b, b'), one integration variable s.  The conjecture is that the
supremum equals 2 sqrt(2) - 1 = 1.8284271, attained at a = b = sqrt2/2, b' = 0.

THE A PRIORI BOX, so that the branch and bound is over a compact set.  Since l <= |I| and
|I| is bounded by each of 2a - 2s + 4, -2b' + 4, 2a - 2b + 4 and 2s - 2b - 2b' + 4 (drop
one side of a max or min in each case), and area <= (sqrt2/2) * min of those, an area of
at least 2 sqrt(2) - 1 forces

    a >= -0.7072,   b' <= 0.7072,   a - b >= -0.7072,   b + b' <= 2.1214 .

For the upper end, if a >= sqrt2 - b' + 1 then for every s in the band the removed
interval (s, 2a-s) reaches the right end of I, leaving l <= 2 and area <= sqrt2 < the
target.  So the maximiser lies in

    a in [-1, 3],   b in [-3, 3],   b' in [-3, 1] ,

which is generous; the conjectured maximiser (sqrt2/2, sqrt2/2, 0) is interior.

THE BOUND USED ON EACH BOX.  On a box of parameters and a subinterval of s, every one of
p, q, r, w is linear, so its range is exact from the endpoints.  Then

    l  <=  |I|_max  -  |(p,q) n I|_min  -  |(r,w) n I|_min  +  |(p,q) n (r,w) n I|_max ,

each term evaluated by interval arithmetic on the endpoints.  Integrating the per-piece
upper bound over s gives an upper bound on the area for the whole parameter box.  A box is
DISCHARGED when that bound is below the target; otherwise it is split, longest side first.

Rule 7: the arithmetic is done in arb ball arithmetic, so the discharges are rigorous.

Rule 8: progress, ETA and an atomic checkpoint of the pending stack; a re-run resumes.

WHAT A COMPLETE RUN WOULD ESTABLISH.  If every box is discharged, then
A_ambi <= 2 sqrt(2) - 1 = 1.8284271, the first upper bound specific to the ambidextrous
problem; the trivial one inherited from Baek's one-corner theorem is 2.2195, and
A_R* = 1.6449552.  Until then nothing is claimed.

Usage: python3 ambi_certbound.py [target_numerator/denominator] [max_seconds]
"""
from __future__ import annotations
import json, math, os, sys, time
from fractions import Fraction as Q

import numpy as np
from flint import arb, ctx

THIS = os.path.dirname(os.path.abspath(__file__))


def qa(x: Q) -> arb:
    return arb(x.numerator)/arb(x.denominator)


def ivl(lo: Q, hi: Q) -> arb:
    return qa(lo).union(qa(hi))


def hull(*xs):
    h = xs[0]
    for x in xs[1:]:
        h = h.union(x)
    return h


# Rounding margin.  All quantities here are O(10) and the bound uses fewer than 100
# double-precision operations, so the accumulated error is below 100*10*2^-52 ~ 2e-13.
# Adding MARGIN = 1e-9 to every upper bound is therefore rigorous by a wide margin, and
# lets the search run vectorised instead of in ball arithmetic.
MARGIN = 1e-9


def area_upper_np(box, S0, S1):
    """upper bound on (1/2) int_0^{sqrt2} l(s) ds for the whole parameter box.

    Vectorised over the s-grid.  On each s-subinterval every one of p,q,r,w is linear in
    (s, a, b, b'), so its range over the box is exact from the endpoints.  Then
        l <= |I|_max - |(p,q)|_min - |(r,w)|_min + |(p,q) n (r,w)|_max ,
    using that the range of min(q,w) is [min of lowers, min of uppers] and of max(p,r) is
    [max of lowers, max of uppers] -- NOT the convex hull, which inflates |I| by the whole
    spread and stalls the bound near 3.46 where the truth is 1.83."""
    (a0, a1), (b0, b1), (p0, p1) = box
    a0, a1, b0, b1, p0, p1 = map(float, (a0, a1, b0, b1, p0, p1))
    p_lo, p_up = S0, S1
    q_lo, q_up = 2*a0 - S1, 2*a1 - S0
    r_lo, r_up = 2*b0 - S1, 2*b1 - S0
    w_lo, w_up = S0 - 2*p1, S1 - 2*p0
    qmin_hi = np.minimum(q_up, w_up)
    pmax_lo = np.maximum(p_lo, r_lo)
    I_up = qmin_hi - pmax_lo + 4.0
    rem_c = np.maximum(0.0, q_lo - p_up)
    rem_d = np.maximum(0.0, w_lo - r_up)
    both = np.maximum(0.0, qmin_hi - pmax_lo)
    v = np.maximum(0.0, I_up - rem_c - rem_d + both)
    return 0.5*float(np.dot(v, S1 - S0)) + MARGIN


def area_upper_exact(box, R2):
    """EXACT upper bound on (1/2) int l(s) ds for the whole parameter box.

    l = |I| - |J_c n I| - |J_d n I| + |J_c n J_d n I|, so an UPPER bound needs an upper
    bound on |I| and on the doubly-removed part, and LOWER bounds on the two removed
    parts.  The removed parts must be CLIPPED TO I: an earlier version subtracted a lower
    bound on |J_c| itself, which is not a lower bound on |J_c n I| unless J_c is contained
    in I, and that containment fails on many boxes.  It made the bound unsound on 3054 of
    36000 sampled (box, interior point) pairs, by as much as 1.414.

    With J_c = (p,q), J_d = (r,w), I = [max(p,r)-2, min(q,w)+2]:
        J_c n I = ( max(s, 2b-s-2),  min(2a-s, s-2b'+2) )
        J_d n I = ( max(2b-s, s-2),  min(s-2b', 2a-s+2) )
    and the box-extreme choices below give a lower bound on each length.  Every term is
    piecewise linear in s, so the integral is computed exactly on the breakpoints."""
    (a0, a1), (b0, b1), (p0, p1) = box
    a0, a1, b0, b1, p0, p1 = map(float, (a0, a1, b0, b1, p0, p1))

    def E(s):
        qmin_hi = min(2*a1 - s, s - 2*p0)          # upper end of min(q,w)
        pmax_lo = max(s, 2*b0 - s)                 # lower end of max(p,r)
        base = qmin_hi - pmax_lo
        I_up = base + 4.0
        remc = max(0.0, min(2*a0 - s, s - 2*p1 + 2.0) - max(s, 2*b1 - s - 2.0))
        remd = max(0.0, min(s - 2*p1, 2*a0 - s + 2.0) - max(2*b1 - s, s - 2.0))
        return I_up - remc - remd + max(0.0, base)

    up = [2*a1, -2*p0, 0.0, 2*b0, 2*a0, -2*p1 + 2.0, 2*b1 - 2.0,
          -2*p1, 2*a0 + 2.0, 2*b1, -2.0]
    slope = [-1, 1, 1, -1, -1, 1, -1, 1, -1, -1, 1]
    bps = {0.0, R2}
    for i in range(len(up)):
        for j in range(i + 1, len(up)):
            if slope[i] != slope[j]:
                t = (up[j] - up[i])/(slope[i] - slope[j])
                if 0.0 < t < R2: bps.add(t)
    S = sorted(bps)
    tot = 0.0
    for i in range(len(S) - 1):
        s0, s1 = S[i], S[i+1]
        e0, e1 = E(s0), E(s1)
        if e0 <= 0.0 and e1 <= 0.0:
            continue
        if e0 >= 0.0 and e1 >= 0.0:
            tot += 0.5*(e0 + e1)*(s1 - s0)
        else:
            sc = s0 + (s1 - s0)*e0/(e0 - e1)
            if e0 > 0.0: tot += 0.5*e0*(sc - s0)
            else:        tot += 0.5*e1*(s1 - sc)
    return 0.5*tot + MARGIN



def main():
    tgt = float(Q(sys.argv[1])) if len(sys.argv) > 1 else 2.0
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 300.0
    nS = int(sys.argv[3]) if len(sys.argv) > 3 else 64
    out = os.path.join(THIS, "certbound.json")
    R2 = math.sqrt(2)
    edges = np.linspace(0.0, R2, nS + 1)
    S0, S1 = edges[:-1], edges[1:]
    BX = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    box0 = [(Q(-BX), Q(3*BX)), (Q(-3*BX), Q(3*BX)), (Q(-3*BX), Q(BX))]
    state = {"stack": [[[str(x) for x in s_] for s_ in box0]], "done": 0}
    if os.path.exists(out):
        state = json.load(open(out))
        print(f"  resuming: {len(state['stack'])} pending, {state['done']} discharged",
              flush=True)
    print(f"BRANCH AND BOUND.  target {tgt:.7f}   nS = {nS}   "
          f"(2sqrt2-1 = {2*math.sqrt(2)-1:.7f})\n", flush=True)
    t0 = time.time(); last = t0
    MINW = Q(1, int(sys.argv[5])) if len(sys.argv) > 5 else Q(1, 4096)
    while state["stack"]:
        if time.time() - t0 > budget:
            json.dump(state, open(out + ".tmp", "w")); os.replace(out + ".tmp", out)
            print(f"\n  BUDGET REACHED.  {state['done']} discharged, "
                  f"{len(state['stack'])} pending.  NOT COMPLETE.", flush=True)
            return 2
        raw = state["stack"].pop()
        box = [(Q(x[0]), Q(x[1])) for x in raw]
        if area_upper_exact(box, R2) < tgt:
            state["done"] += 1
        else:
            widths = [b - a for a, b in box]
            k = max(range(3), key=lambda i: widths[i])
            if widths[k] < MINW:
                json.dump(state, open(out + ".tmp", "w")); os.replace(out + ".tmp", out)
                print(f"  *** STALLED at {[(float(a),float(b)) for a,b in box]}, "
                      f"bound {area_upper_exact(box,R2):.6f} ***", flush=True)
                return 1
            m = (box[k][0] + box[k][1])/2
            for lohi in ((box[k][0], m), (m, box[k][1])):
                nb = list(box); nb[k] = lohi
                state["stack"].append([[str(x) for x in s_] for s_ in nb])
        if time.time() - last > 20:
            last = time.time()
            json.dump(state, open(out + ".tmp", "w")); os.replace(out + ".tmp", out)
            print(f"  {state['done']:9d} discharged, {len(state['stack']):5d} pending, "
                  f"{time.time()-t0:6.0f}s", flush=True)
    json.dump(state, open(out + ".tmp", "w")); os.replace(out + ".tmp", out)
    print(f"\n  COMPLETE: {state['done']} boxes, all discharged, "
          f"{time.time()-t0:.0f}s")
    print(f"  A_ambi <= {tgt:.7f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
