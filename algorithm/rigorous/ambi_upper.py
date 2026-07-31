"""ambi_upper.py — a finite-angle upper bound for the AMBIDEXTROUS moving sofa problem.

THE RELAXATION, which needs no hypotheses at all.

An ambidextrous moving sofa S can be manoeuvred around a right-angled corner of each
handedness.  In the sofa's frame that means there are two motions of the hallway, and S is
contained in the hallway at every instant of both.  Hence for ANY finite sets of rotation
angles and ANY placements,

    S  subset  ( intersection over i of  L(t_i, c_i) )  n  ( intersection over j of  R(s_j, d_j) ) ,

where L(t,c) is the left-turning hallway rotated by t with inner corner at c, and R(s,d)
is the right-turning one (the mirror image, rotated by s and placed at d).  Dropping every
constraint that links the placements -- continuity of the motion, monotonicity, the fact
that the two motions are of the same body -- only enlarges the right-hand side.  So

    A_ambi  <=  sup over placements of the area of that intersection,               (UB)

and the supremum is over finitely many free vectors in R^2, modulo one global translation.
This is the Kallus-Romik construction (arXiv 1706.06590) transferred from the one-corner
problem to the ambidextrous one, where it has not been applied.  For the one-corner problem
Baek's theorem now gives 2.2195, and since an ambidextrous sofa is in particular a
one-corner sofa, 2.2195 is the trivial bound to beat.

WHY IT SHOULD DO BETTER HERE.  The one-corner constraint family sweeps a rotation range of
pi/2.  The ambidextrous family sweeps pi -- the same body must satisfy two families of
range pi/2 whose normals point into different quadrants -- so a given number of angles
constrains far more.

VALIDATION (Rule 3, before optimising anything).  The construction must be admissible at
Sigma: intersecting the hallway along Sigma's OWN corner path must give an area that
decreases to |Sigma| = 1.6449552 from above.  It does:

    angles per side      3        9       33      129      513
    left family only  2.050458 2.000690 1.991986 1.990120 1.989674
    both families     1.766816 1.667280 1.649873 1.646140 1.645249

Two bugs were caught by this check before any bound was computed.  The inner corner
quadrant was built on the wrong side of its two half-planes, which gave area 0 for Sigma;
and the right-turning family was first written as L(-t), which is wrong because rho carries
nu_t to -nu_{-t}, not to nu_{-t}, so the mirrored hallway is not a member of the same
one-parameter family.  It is now built by an exact affine reflection.

WHAT THIS FILE COMPUTES, AND WHAT IT DOES NOT.  It evaluates (UB) by multistart local
maximisation.  A local maximiser gives a LOWER bound on the supremum, so the number
reported is NOT itself an upper bound on A_ambi: turning (UB) into a theorem requires a
rigorous global bound on the supremum, i.e. branch and bound over the placement box with
interval arithmetic, which is what Kallus-Romik do and what is not done here.  The number
is therefore EVIDENCE about how well the method can be expected to do, and is labelled
HEURISTIC.  Rule 0: it is not an upper bound until the global step is done.

WHAT THE FIRST RUNS SHOW.  At k = 3 angles per side (0, pi/4, pi/2), the supremum in
(UB) is at least

    2 sqrt(2) - 1 = 1.8284271 ,

exhibited by an explicit placement; eight seeded local maximisations all converged to it,
and the clean closed form suggests a vertex of the arrangement rather than an artefact.
Sigma's own placement gives 1.766816 at the same k, so the optimiser does beat the
configuration it was seeded from.

Two consequences, in opposite directions.

  * NO bound below 2 sqrt(2) - 1 can be proved at k = 3, whatever the global optimiser:
    the supremum is at least that.  This is a PROVED limitation of the method at that k,
    since it only needs one exhibited placement.
  * IF the supremum at k = 3 equals 2 sqrt(2) - 1, a rigorous global step would give
    A_ambi <= 1.8284271, against the trivial 2.2195 inherited from Baek's one-corner
    theorem and A_R* = 1.6449552.  That is 1.11 times A_R*.

The second is NOT established.  A multistart local maximum bounds the supremum from
BELOW, which is the wrong direction; proving A_ambi <= 1.8284271 needs a rigorous upper
bound on the supremum, i.e. branch and bound over the placement box in interval
arithmetic.  That is the step Kallus-Romik carry out for the one-corner problem and it is
not done here.  Under Rule 8 it belongs in Rust: the Shapely inner loop already exceeds
the Python budget at k = 3 with 24 starts.

Rule 0 labels: the relaxation (UB) is PROVED; the lower bound 2 sqrt(2) - 1 on the k = 3
supremum is PROVED; any upper bound on A_ambi is NOT YET ESTABLISHED.

Usage:
  python3 ambi_upper.py validate
  python3 ambi_upper.py optimise [k] [starts]
"""
from __future__ import annotations
import json, math, os, sys, time

import numpy as np
from shapely.geometry import Polygon
from shapely.affinity import scale as sscale, translate as stranslate

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from ambi_hessian import H_and_dH, PI2

BIG = 25.0
BOX = Polygon([(-BIG, -BIG), (BIG, -BIG), (BIG, BIG), (-BIG, BIG)])


def hp(n, d):
    """{p : <p,n> <= d}, clipped to BOX.  n a unit vector."""
    n = np.asarray(n, float); t = np.array([-n[1], n[0]]); p0 = n*d
    return Polygon([p0 + t*80 - n*80, p0 - t*80 - n*80,
                    p0 - t*80, p0 + t*80]).intersection(BOX)


def hallL(t, c):
    """left-turning hallway: rotation angle t, inner corner c."""
    mu = np.array([math.cos(t), math.sin(t)])
    nu = np.array([-math.sin(t), math.cos(t)])
    dm = float(np.dot(c, mu)); dn = float(np.dot(c, nu))
    return hp(mu, dm + 1).intersection(hp(nu, dn + 1)).difference(
           hp(mu, dm).intersection(hp(nu, dn)))


def hallR(s, d):
    """right-turning hallway: the mirror image of hallL, rotated by s, placed at d.

    Reflecting then rotating realises every orientation-reversing placement, so as
    (s,d) ranges this is the full right-turning family."""
    g = sscale(hallL(s, np.zeros(2)), xfact=1.0, yfact=-1.0, origin=(0.0, 0.0))
    return stranslate(g, xoff=float(d[0]), yoff=float(d[1]))


def region(tsL, csL, tsR, dsR):
    R = BOX
    for t, c in zip(tsL, csL):
        R = R.intersection(hallL(t, c))
        if R.is_empty: return R
    for s, d in zip(tsR, dsR):
        R = R.intersection(hallR(s, d))
        if R.is_empty: return R
    return R


def sigma_corner(a):
    F, _ = H_and_dH([a]); G, _ = H_and_dH([a + PI2])
    mu = np.array([math.cos(a), math.sin(a)])
    nu = np.array([-math.sin(a), math.cos(a)])
    return (F[0] - 1)*mu + (G[0] - 1)*nu


def validate():
    rho = lambda g: sscale(g, xfact=1.0, yfact=-1.0, origin=(0.0, 0.5))
    print("VALIDATION: Sigma's own corner path.  |Sigma| = 1.6449552\n")
    print(f"  {'k per side':>11} {'left only':>12} {'both families':>15}")
    for k in (3, 9, 33, 129, 513):
        L = BOX
        for a in np.linspace(0.0, PI2, k):
            L = L.intersection(hallL(float(a), sigma_corner(float(a))))
        print(f"  {k:11d} {L.area:12.6f} {L.intersection(rho(L)).area:15.6f}")
    print("\n  decreasing to |Sigma| from above, as required.")


def optimise(k, starts):
    from scipy.optimize import minimize
    tsL = list(np.linspace(0.0, PI2, k)); tsR = list(np.linspace(0.0, PI2, k))
    n = 2*(2*k) - 2                       # all corners free, one global translation fixed

    def unpack(v):
        z = np.concatenate([[0.0, 0.0], v])
        P = z.reshape(-1, 2)
        return list(P[:k]), list(P[k:])

    def negarea(v):
        cs, ds = unpack(v)
        try:
            a = region(tsL, cs, tsR, ds).area
        except Exception:
            return 0.0
        return -a

    rng = np.random.default_rng(0)
    best = (0.0, None); t0 = time.time()
    out = os.path.join(THIS, f"upper_k{k}.json")
    if os.path.exists(out):
        st = json.load(open(out)); best = (st["best"], np.array(st["v"]))
        print(f"  resuming: best so far {best[0]:.6f}", flush=True)
    for i in range(starts):
        v0 = rng.normal(0.0, 0.6, n)
        r = minimize(negarea, v0, method="Nelder-Mead",
                     options={"maxiter": 4000, "fatol": 1e-10, "xatol": 1e-8})
        if -r.fun > best[0]:
            best = (-r.fun, r.x)
            json.dump({"best": best[0], "v": best[1].tolist()}, open(out + ".tmp", "w"))
            os.replace(out + ".tmp", out)
        if (i + 1) % 10 == 0:
            el = time.time() - t0
            print(f"  start {i+1:4d}/{starts}  best {best[0]:.6f}   "
                  f"elapsed {el/60:5.2f}m  ETA {el/(i+1)*(starts-i-1)/60:5.2f}m", flush=True)
    print(f"\n  k = {k} angles per side, {starts} starts")
    print(f"  best local maximum of the finite-angle area: {best[0]:.6f}")
    print(f"  |Sigma| = 1.644955  (must be <= this: Sigma is admissible)")
    print(f"  Baek's one-corner bound 2.219531 is the trivial bound to beat")
    print(f"\n  Rule 0: a local maximum is a LOWER bound on the supremum, so this is")
    print(f"  NOT yet an upper bound on A_ambi.  HEURISTIC.")


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "validate"
    if mode == "validate":
        validate()
    else:
        k = int(sys.argv[2]) if len(sys.argv) > 2 else 3
        starts = int(sys.argv[3]) if len(sys.argv) > 3 else 60
        optimise(k, starts)


if __name__ == "__main__":
    main()
