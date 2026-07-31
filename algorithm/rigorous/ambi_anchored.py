"""ambi_anchored.py — concavity on EVERY ordered anchored cell, by reduction and covering.

THE THEOREM BEING ASSEMBLED.  Write the second variation on a cell with sign sets
E1 = {alpha_1 < 0}, E2 = {alpha_2 > 0} as (singularity-free form, p = eta(t),
q = eta(t+pi/2) on [0,pi/2]):

  B_{E1,E2}[eta] = int_0^{pi/2} [2p^2-2p'^2+q^2-q'^2] - int_{E2}(p+q')^2 + int_{E1}(q-p')^2

with p(0) = p(pi/2) = q(0) = 0 and q(pi/2) free.

  LEMMA M (monotonicity).  If E1 subset E2 then

      B_{E1,E2}[eta] = B_{E2,E2}[eta] - int_{E2 \\ E1} (q - p')^2  <=  B_{E2,E2}[eta] .

  One line, no hypotheses on the sets beyond inclusion.  So concavity for EVERY cell
  with E1 subset E2 and E2 = [0,tau) ANCHORED reduces to the DIAGONAL family
  D_tau := B_{[0,tau),[0,tau)},  tau in [0, pi/2].

  THEOREM D (diagonal concavity).  D_tau[eta] <= 0 for every tau in [0, pi/2].

  Proof in three ranges.
  (a) tau <= 1/sqrt(3):  by hand.  On [0,tau) the integrand combines (F28) to
      (p^2-p'^2) + 2(q^2-q'^2) - 2(pq)', so
      D_tau = B_bare + int_0^tau [(p'^2-p^2)+(q^2-q'^2)] - 2 p(tau) q(tau),
      B_bare := int 2(p^2-p'^2)+(q^2-q'^2) <= -(3/2) int p'^2   (Poincare DD 4, DN 1).
      With p(tau)^2 <= tau int_0^tau p'^2, q(tau)^2 <= tau int_0^tau q'^2,
      int_0^tau q^2 <= tau^2 int_0^tau q'^2, and Young at s = 1/(2tau):
      D_tau <= [-(3/2)+1+(1/2)] int p'^2 + (3 tau^2 - 1) int_0^tau q'^2 <= 0.
  (b) sigma := pi/2 - tau <= 1/18:  by hand, spectral splitting.  q = a sin t + r with
      r orthogonal to sin t in the Dirichlet-Neumann eigenbasis; the marginal mode
      (0, sin t) has D_{pi/2}-value 0 and the gap to the next eigenvalue (= 9) plus the
      damping -(1/2) a^2 sin 2(sigma) close the estimate; see the note for constants.
  (c) tau in [0.55, 1.5153]:  CERTIFIED here.  The cell form is exactly the 2x2
      Sturm-Liouville system of ambi_system.py with pieces
          [0,tau):    (a,b,g,d,e,f) = (1,2,-1,-2,1,1)     (the F28 total-derivative piece)
          [tau,pi/2): (2,1,-2,-1,0,0)                     (bare)
      i.e. lens [tau, 0, pi/2 - tau] in ambi_system's COEF.  Its eigenvalues are the
      zeros of the shooting determinant Phi(c; lens).  Two facts give D_tau <= 0:
        (i)  c_1 >= -4:  pointwise, 2pq' >= -(2p^2 + q'^2/2) and 2qp' >= -(2q^2 + p'^2/2)
             absorb the cross terms leaving nonneg derivative coefficients, so
             -D_tau[eta] >= -int(3p^2+4q^2) >= -4 ||eta||^2.  PROVED, one line.
        (ii) Phi(c; tau) != 0 for every (c, tau) in [-4, 0] x [0.55, 1.5153]:
             certified by ADAPTIVE INTERVAL COVERING in ball arithmetic; no enclosure
             of Phi over any box contains 0.
      Together: no eigenvalue lies in [-4, 0], and none lies below -4, so c_1 > 0,
      i.e. D_tau < 0 ... <= 0 on the closed range.  QED

  The three ranges overlap: [0, 0.5773] u [0.55, 1.5153] u [1.5153, pi/2].

  COROLLARY (ordered anchored concavity).  delta^2 Q <= 0 on every cell whose sign sets
  satisfy {alpha_1 < 0} subset {alpha_2 > 0} and {alpha_2 > 0} = [0, tau) anchored.
  This upgrades the eleven-entry measured table of Proposition "beyond" to a theorem,
  with a WEAKER hypothesis: E1 need not be an interval.

  THEOREM M' (mirror family, uniform constant).  For mirror caps the anchored cell is
  (tau, pi/2 - tau) with one parameter; its form is ambi_system's structure with lens
  [tau, pi/2 - 2tau, tau].  Certified here: c_1(tau) > 3/10 for every tau in [0, pi/4],
  by covering [-4, 3/10] x [0, 0.7854].  The tau-range strictly contains pi/4 =
  0.78539816...; for tau slightly past pi/4 the middle length crosses zero and the
  transfer formula is an analytic continuation, which is harmless: the enclosure
  covers every real tau in the ball, in particular all of [0, pi/4] where the formula
  IS the shooting determinant of the cell form.  Hence on the mirror class
      (1/2) delta^2 Q <= -(3/10) ||eta||^2_{L^2(0,pi)}
  on every anchored cell, uniformly.  (Measured: c_1 decreases 0.875 -> 0.370 along the
  family; Sigma's cell, tau = beta, has 0.733.)

WHY THE DECOUPLED CHAIN CANNOT DO THIS.  The scalar chain of ambi_sturm.py, optimised
over its two parameters, gives -0.04 at tau = pi/4 and -1.9 at tau = 1.45 on the diagonal
against true values +0.37 and +0.08: past tau ~ 0.6 the pointwise Cauchy-Schwarz losses
exceed the whole eigenvalue.  Only the system formulation reaches the family.

RULE 3 RECORD.  Lemma M: 60 random (t1,t2,eta), min slack +1.49e-2, no violation.  The
hand ranges: 1000 random checks of the small-tau chain and 600 of the corner claim, zero
violations.  Measurements: diagonal c_1 >= 0 on a 12-point grid (marginal at both ends,
mode (0, sin t)); mirror c_1 in [0.370, 0.875] on a 12-point grid.

Usage:
  python3 ambi_anchored.py measure
  python3 ambi_anchored.py certify-diagonal   [resumes from checkpoint]
  python3 ambi_anchored.py certify-mirror     [resumes from checkpoint]
"""
from __future__ import annotations
import json, math, os, sys, time
from fractions import Fraction as Q

import numpy as np
from flint import arb, ctx

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from ambi_certify import qarb
from ambi_system import Phi, lengths_ball

PI2 = math.pi/2


def qball(lo: Q, hi: Q) -> arb:
    return qarb(lo).union(qarb(hi))


def lens_diagonal(tlo: Q, thi: Q):
    """lens [tau, 0, pi/2 - tau] as balls, tau enclosed in [tlo, thi]."""
    t = qball(tlo, thi)
    return [t, arb(0), arb.pi()/2 - t]


def lens_mirror(tlo: Q, thi: Q):
    """lens [tau, pi/2 - 2 tau, tau]."""
    t = qball(tlo, thi)
    return [t, arb.pi()/2 - 2*t, t]


def cover(tag, lens_of, t_lo: Q, t_hi: Q, c_lo: Q, c_hi: Q, out, min_w=Q(1, 4096)):
    """certify Phi(c; tau) != 0 on [c_lo,c_hi] x [t_lo,t_hi] by adaptive bisection.

    Stack of boxes; a box passes when the arb enclosure of Phi over it excludes 0.
    Atomic checkpoint of the remaining stack; resume on restart."""
    state = {"stack": [[str(t_lo), str(t_hi), str(c_lo), str(c_hi)]], "done": 0}
    if os.path.exists(out):
        state = json.load(open(out))
        print(f"  resuming: {len(state['stack'])} boxes on the stack, "
              f"{state['done']} certified", flush=True)
    t0 = time.time(); last = t0
    while state["stack"]:
        tl, th, cl, ch = [Q(x) for x in state["stack"].pop()]
        v = Phi(qball(cl, ch), lens_of(tl, th))
        if not v.contains(0):
            state["done"] += 1
        else:
            if th - tl < min_w and ch - cl < min_w:
                print(f"  *** FAILED at box tau=[{float(tl):.6f},{float(th):.6f}] "
                      f"c=[{float(cl):.6f},{float(ch):.6f}] ***", flush=True)
                state["failed"] = [str(tl), str(th), str(cl), str(ch)]
                json.dump(state, open(out + ".tmp", "w")); os.replace(out + ".tmp", out)
                return False
            if (th - tl) * 4 > (ch - cl):
                tm = (tl + th)/2
                state["stack"] += [[str(tl), str(tm), str(cl), str(ch)],
                                   [str(tm), str(th), str(cl), str(ch)]]
            else:
                cm = (cl + ch)/2
                state["stack"] += [[str(tl), str(th), str(cl), str(cm)],
                                   [str(tl), str(th), str(cm), str(ch)]]
        if time.time() - last > 20:
            last = time.time()
            json.dump(state, open(out + ".tmp", "w")); os.replace(out + ".tmp", out)
            print(f"  [{tag}] {state['done']} boxes certified, "
                  f"{len(state['stack'])} pending, {time.time()-t0:6.1f}s", flush=True)
    json.dump(state, open(out + ".tmp", "w")); os.replace(out + ".tmp", out)
    print(f"  [{tag}] COMPLETE: {state['done']} boxes, no enclosure contained 0, "
          f"{time.time()-t0:6.1f}s", flush=True)
    return True


def measure():
    from ambi_hessian import mass_stiff
    from ambi_concavity import hess_sets
    def c1(E1, E2, m=96):
        B, M = hess_sets(m, E1, E2); Ms, _ = mass_stiff(B)
        L = np.linalg.cholesky(Ms)
        A = np.linalg.solve(L, np.linalg.solve(L, M).T).T
        return -np.linalg.eigvalsh(0.5*(A + A.T)).max()
    print("mirror family (tau, pi/2-tau):")
    for t in (0.0, 0.15, 0.2897, 0.45, 0.65, 0.7854):
        print(f"  tau={t:6.4f}  c1={c1([(0.0,t)],[(0.0,PI2-t)]):.5f}")
    print("diagonal family (tau, tau):")
    for t in (0.0, 0.25, 0.5774, 0.7854, 1.1, 1.4, 1.5153, 1.5708):
        print(f"  tau={t:6.4f}  c1={c1([(0.0,t)],[(0.0,t)]):.5f}")


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "measure"
    ctx.prec = 350
    if mode == "measure":
        measure(); return 0
    if mode == "certify-diagonal":
        ok = cover("diag", lens_diagonal, Q(11, 20), Q(15153, 10000), Q(-4), Q(0),
                   os.path.join(THIS, "anchored_diag.json"))
    elif mode == "certify-mirror":
        ok = cover("mirr", lens_mirror, Q(0), Q(7854, 10000), Q(-4), Q(3, 10),
                   os.path.join(THIS, "anchored_mirr.json"))
    else:
        print("unknown mode"); return 2
    print("CERTIFIED" if ok else "NOT CERTIFIED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
