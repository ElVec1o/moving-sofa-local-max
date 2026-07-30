"""ambi_injectivity.py — is  {V = |N|}  cut out by LINEAR inequalities in H?

CRUX (I1).  Find a convex subdomain K' of the domain, containing Sigma, on which
V(H) = |N(H)|.  Then Q = |C2| - 2V >= |sofa| there, and the three facts already
established (Q(Sigma) = A_R*, dQ(Sigma) = 0, d^2 Q < 0 on Sigma's cell) compose into a
conditional optimality statement.  Unblocking label: PROVED.

WHY LINEARITY IS PLAUSIBLE.  ambi_domination.py showed V >= |N| always, with equality
iff nothing is re-swept, i.e. iff the combined sweep is INJECTIVE.  Injectivity is a
statement about when two parameters give the same point, and each sweep lies on a line:

    face 2 at t :  l2(t) = { <p,nu_t> = G(t)-1 },   p = c(t) - s mu_t,  s in [0, a2(t)]
    face 1 at t :  l1(t) = { <p,mu_t> = F(t)-1 },   p = c(t) - s nu_t,  s in [a1(t)^+, sig(t)]

Two distinct lines meet in one point, so a double cover forces that point into both
segments.  Solving l2(t) ^ l2(t') for the s-coordinate on l2(t):

    <c(t),nu_t'> - s <mu_t, nu_t'> = G(t')-1,    <mu_t,nu_t'> = sin(t-t'),
    s22(t,t') = [ <c(t),nu_t'> - (G(t')-1) ] / sin(t-t') ,

and as t' -> t this tends to a2(t) (the envelope point D(t)), since the numerator
vanishes at t' = t with derivative -a2(t).  So nearby lines meet AT the far end of the
face-2 segment, and the segment is free of self-intersections as soon as

    (C22)   s22(t,t') >= a2(t)      for all t' != t.

Clearing the denominator, that is

    [ <c(t),nu_t'> - (G(t')-1) ] - a2(t) sin(t-t')  >= 0   for t' < t,   <= 0 for t' > t,

and BOTH SIDES ARE AFFINE IN H: c(t) = (F(t)-1) mu_t + (G(t)-1) nu_t is affine in the
support function, G(t')-1 is affine, a2(t) = F(t)-1+G'(t) is affine, and sin(t-t') is a
constant.  So (C22) is a family of LINEAR inequalities in H and cuts out a CONVEX set.

Face 1 is the mirror image.  s11(t,t') = [ <c(t),mu_t'> - (F(t')-1) ] / sin(t'-t) tends
to a1(t) as t' -> t, which is the NEAR end of the face-1 segment [a1^+, sig], so the
condition points the other way:

    (C11)   s11(t,t') <= a1(t)      for all t' != t,

again linear.  The cross condition (C21) asks that l2(t) ^ l1(t') not lie in both
segments; it is a disjunction of linear inequalities, so not convex on its own, and is
measured here rather than assumed.

WHAT THIS SCRIPT DOES
  1. Measures the gaps of (C22), (C11) at Sigma over a t-grid: are they >= 0, and with
     what margin?
  2. Measures (C21) at Sigma.
  3. NEGATIVE CONTROL (I12): runs the same at the perturbed H where ambi_domination.py
     found V - |N| = 5e-3.  The conditions MUST fail there.  If they hold there too,
     the conditions are not what governs V = |N| and the analysis is wrong.

Usage: python3 ambi_injectivity.py [n_grid]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from ambi_hessian import H_and_dH, PI, PI2
from ambi_domination import H_pert, bump
from sofa_romik2017_reference import BETA


def data_at(T, eps, c0, w):
    """F-1, G-1, alpha_1, alpha_2, sigma at the grid T, for H = H_Sigma + eps*bump"""
    F, dF = H_pert(T, eps, c0, w)
    G, dG = H_pert(T + PI2, eps, c0, w)
    Fm, Gm = F - 1.0, G - 1.0
    a1 = Gm - dF
    a2 = Fm + dG
    sg = Fm*np.tan(T) + Gm
    return Fm, Gm, a1, a2, sg


def gaps(n, eps=0.0, c0=1.0, w=0.45, skip=3):
    """gap22[i,j] = s22(t_i,t_j) - a2(t_i);  gap11[i,j] = a1(t_i) - s11(t_i,t_j).
    Pairs with |i-j| < skip are dropped (the 0/0 limit is the envelope, gap -> 0)."""
    T = np.linspace(1e-9, PI2 - 1e-9, n)
    Fm, Gm, a1, a2, sg = data_at(T, eps, c0, w)
    cx = Fm*np.cos(T) - Gm*np.sin(T)
    cy = Fm*np.sin(T) + Gm*np.cos(T)
    # <c(t_i), nu_{t_j}> = -cx_i sin t_j + cy_i cos t_j
    NU = (-np.outer(cx, np.sin(T)) + np.outer(cy, np.cos(T)))
    MU = (np.outer(cx, np.cos(T)) + np.outer(cy, np.sin(T)))
    SIN_ij = np.sin(T[:, None] - T[None, :])            # sin(t_i - t_j)
    with np.errstate(divide='ignore', invalid='ignore'):
        s22 = (NU - Gm[None, :])/SIN_ij
        s11 = (MU - Fm[None, :])/(-SIN_ij)              # sin(t_j - t_i)
    g22 = s22 - a2[:, None]
    g11 = a1[:, None] - s11
    mask = np.abs(np.subtract.outer(np.arange(n), np.arange(n))) >= skip
    return T, g22, g11, mask, a1, a2, sg


def report(n, eps, label):
    T, g22, g11, mask, a1, a2, sg = gaps(n, eps)
    m22 = g22[mask]; m11 = g11[mask]
    i22 = np.unravel_index(np.nanargmin(np.where(mask, g22, np.inf)), g22.shape)
    i11 = np.unravel_index(np.nanargmin(np.where(mask, g11, np.inf)), g11.shape)
    print(f"  {label}")
    print(f"    (C22)  min [ s22 - a2 ]     = {np.nanmin(m22):+.6f}"
          f"   at (t,t') = ({T[i22[0]]:.4f}, {T[i22[1]]:.4f})"
          f"   {'HOLDS' if np.nanmin(m22) >= -1e-9 else 'VIOLATED'}")
    print(f"    (C11)  min [ a1 - s11 ]     = {np.nanmin(m11):+.6f}"
          f"   at (t,t') = ({T[i11[0]]:.4f}, {T[i11[1]]:.4f})"
          f"   {'HOLDS' if np.nanmin(m11) >= -1e-9 else 'VIOLATED'}")
    frac22 = 100.0*np.mean(m22 < -1e-9)
    frac11 = 100.0*np.mean(m11 < -1e-9)
    print(f"    violating pairs: (C22) {frac22:.3f}%   (C11) {frac11:.3f}%")
    return np.nanmin(m22), np.nanmin(m11)


def cross(n, eps=0.0, c0=1.0, w=0.45):
    """(C21): does l2(t) ^ l1(t') land in BOTH segments?"""
    T = np.linspace(1e-9, PI2 - 1e-9, n)
    Fm, Gm, a1, a2, sg = data_at(T, eps, c0, w)
    bad = 0; tot = 0; worst = None
    for i in range(n):
        # p solves <p,nu_ti> = Gm_i  and  <p,mu_tj> = Fm_j  for all j
        ci, si = math.cos(T[i]), math.sin(T[i])
        for j in range(n):
            cj, sj = math.cos(T[j]), math.sin(T[j])
            det = (-si)*sj - ci*cj                     # det[[-si,ci],[cj,sj]]
            if abs(det) < 1e-12:
                continue
            px = (Gm[i]*sj - Fm[j]*ci)/det
            py = ((-si)*Fm[j] - cj*Gm[i])/det
            s2 = Fm[i] - (px*ci + py*si)
            s1 = Gm[j] - (-px*sj + py*cj)
            tot += 1
            if (1e-9 < s2 < a2[i] - 1e-9) and (max(a1[j], 0.0) + 1e-9 < s1
                                               < sg[j] - 1e-9):
                bad += 1
                d = min(s2, a2[i]-s2, s1-max(a1[j], 0.0), sg[j]-s1)
                if worst is None or d > worst[0]:
                    worst = (d, T[i], T[j])
    return bad, tot, worst


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 401
    print("IS {V = |N|} CUT OUT BY LINEAR INEQUALITIES IN H?   (n = %d)\n" % n)
    print("(1) AT SIGMA")
    report(n, 0.0, "H = H_Sigma")
    b, t, wst = cross(min(n, 241), 0.0)
    print(f"    (C21)  l2(t) ^ l1(t') inside both segments: {b} of {t} pairs"
          + (f"   worst depth {wst[0]:.2e} at ({wst[1]:.4f},{wst[2]:.4f})" if wst
             else ""))
    print()
    print("(2) NEGATIVE CONTROL (I12): the perturbations where V - |N| was 5e-3.")
    print("    The conditions MUST fail here.  If they hold, the analysis is wrong.")
    for eps in (0.20, -0.20, 0.10, -0.10):
        report(n, eps, f"H = H_Sigma + {eps:+.2f} * bump")
    print()
    print("  READING.  If (C22),(C11) hold at Sigma with a margin and fail on the")
    print("  perturbations, then {V = |N|} is governed by these LINEAR conditions, the")
    print("  set they cut out is CONVEX and contains Sigma, and the architecture can be")
    print("  repaired by restricting the domain to it.")


if __name__ == "__main__":
    main()
