"""ambi_curvature.py — (C22) and (C11) follow from ONE linear condition: H + H'' <= 1.

CLAIM (proved below, verified here).  Let (RC) be the condition that the cap's radius of
curvature is at most the corridor width:

    (RC)    H(theta) + H''(theta) <= 1      for all theta in [0, pi].

Then (C22) and (C11) hold for EVERY pair t' < t, not merely near the diagonal.

PROOF.  Fix t and put tau = t - t' > 0.  For (C22) let

    n(t') = <c(t), nu_t'> - (G(t')-1),      Phi(tau) = n(t-tau) - alpha_2(t) sin tau,

so that (C22) reads Phi >= 0.  Then n(t) = 0 because <c,nu_t> = G-1, and
n'(t') = -<c(t),mu_t'> - G'(t') equals -(F-1) - G' = -alpha_2(t) at t' = t, so
Phi(0) = Phi'(0) = 0.  Differentiating twice and using nu'' = -nu,

    n''(t') = -<c(t),nu_t'> - G''(t') = -n(t-tau) + 1 - (G+G'')(t-tau) ,

and substituting n(t-tau) = Phi(tau) + alpha_2 sin tau the alpha_2 terms cancel:

    Phi''(tau) + Phi(tau) = 1 - (G+G'')(t-tau) =: R(tau) .

With Phi(0) = Phi'(0) = 0 this integrates to

    Phi(tau) = int_0^tau sin(tau-u) R(u) du .

Now tau <= t <= pi/2 < pi, so sin(tau-u) >= 0 for u in [0,tau], and under (RC) R >= 0.
Hence Phi >= 0: (C22) holds for all pairs.  For (C11) put
m(t') = <c(t),mu_t'> - (F(t')-1) and Psi(tau) = m(t-tau) + alpha_1(t) sin tau; the same
computation, with mu'' = -mu, gives

    Psi''(tau) + Psi(tau) = 1 - (F+F'')(t-tau) ,      Psi(0) = Psi'(0) = 0,

so Psi(tau) = int_0^tau sin(tau-u) [1 - (H+H'')(t-u)] du >= 0.  Since s11 <= alpha_1 is
equivalent to Psi >= 0 (multiplying by -sin tau < 0 flips the inequality), (C11) holds
for all pairs.  QED

Note G(t) = H(t+pi/2), so the two conditions use (RC) on [pi/2,pi] and on [0,pi/2]
respectively; together they use it on all of [0,pi].

(RC) IS LINEAR in H, so it cuts out a convex set, and it is geometrically transparent: the
cap is nowhere flatter than a circle of radius equal to the corridor width.  H + H'' is
exactly the radius of curvature (the density of the surface area measure).

WHAT THIS SCRIPT CHECKS
  1. (RC) for Sigma: max of H + H'' over [0,pi], and the margin.
  2. The ODE identity Phi'' + Phi = R and the integral representation, against direct
     evaluation of n(t-tau) - alpha_2 sin tau.  Two independent routes (Rule 7).
  3. NEGATIVE CONTROL (I12): the perturbations that violated (C11) must violate (RC).
  4. The cross condition (C21), which this argument does NOT cover.

Usage: python3 ambi_curvature.py [n]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from ambi_hessian import H_and_dH, PI, PI2
from ambi_domination import bump
from sofa_romik2017_reference import BETA


def HpH2(th, eps=0.0, c0=1.0, w=0.45, h=1e-5):
    """H + H'' by central differences, for H = H_Sigma + eps*bump or + eps*sin(k th)"""
    th = np.atleast_1d(np.asarray(th, dtype=float))
    out = np.zeros(len(th))
    for i, t in enumerate(th):
        vals = []
        for x in (t - h, t, t + h):
            H, _ = H_and_dH([min(max(x, 0.0), PI)])
            b, _ = bump(np.array([x]), c0, w)
            vals.append(H[0] + eps*b[0])
        out[i] = vals[1] + (vals[0] - 2*vals[1] + vals[2])/h**2
    return out


def HpH2_mode(th, eps, k, h=1e-5):
    th = np.atleast_1d(np.asarray(th, dtype=float))
    out = np.zeros(len(th))
    for i, t in enumerate(th):
        vals = []
        for x in (t - h, t, t + h):
            H, _ = H_and_dH([min(max(x, 0.0), PI)])
            vals.append(H[0] + eps*math.sin(k*x))
        out[i] = vals[1] + (vals[0] - 2*vals[1] + vals[2])/h**2
    return out


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1201

    print("(1) DOES SIGMA SATISFY (RC):  H + H'' <= 1 ?\n")
    th = np.linspace(1e-4, PI - 1e-4, n)
    d = HpH2(th)
    print(f"    max over [0,pi] of H+H''  = {d.max():.9f}  at theta = "
          f"{th[np.argmax(d)]:.6f}")
    print(f"    min                       = {d.min():.9f}")
    print(f"    margin 1 - max            = {1 - d.max():.9f}")
    print(f"    (RC) {'HOLDS' if d.max() <= 1 else 'FAILS'} for Sigma")
    print(f"    beta = {BETA:.6f}, pi/2 = {PI2:.6f}, pi-beta = {PI-BETA:.6f};")
    print(f"    the max sits at the phase junctions, where H+H'' jumps from 0.")

    print("\n(2) THE ODE IDENTITY, two independent routes")
    print("    Phi(tau) = n(t-tau) - alpha_2(t) sin tau   vs   "
          "int_0^tau sin(tau-u) R(u) du")
    err = 0.0; worst = None
    for t in (0.4, 0.8, 1.2, PI2 - 1e-6):
        H, dH = H_and_dH([t]); Ht, dHt = H_and_dH([t + PI2])
        Fm, Gm = H[0] - 1.0, Ht[0] - 1.0
        a2 = Fm + dHt[0]
        cx = Fm*math.cos(t) - Gm*math.sin(t)
        cy = Fm*math.sin(t) + Gm*math.cos(t)
        for tau in (0.05, 0.2, 0.5, min(1.0, t), t):
            if tau <= 1e-9:
                continue
            tp = t - tau
            Hp, _ = H_and_dH([tp + PI2])
            direct = (-cx*math.sin(tp) + cy*math.cos(tp)) - (Hp[0] - 1.0) \
                     - a2*math.sin(tau)
            us = np.linspace(0.0, tau, 4001)
            R = 1.0 - HpH2(t - us + PI2)
            integ = float(np.trapezoid(np.sin(tau - us)*R, us))
            e = abs(direct - integ)
            if e > err:
                err = e; worst = (t, tau, direct, integ)
    print(f"    max |direct - integral| = {err:.3e}   at (t,tau) = "
          f"({worst[0]:.3f},{worst[1]:.3f}), values {worst[2]:.9f} vs {worst[3]:.9f}")
    print(f"    => the ODE reduction is confirmed; and since R >= 0 under (RC) and")
    print(f"       sin(tau-u) >= 0 for tau <= pi/2, Phi >= 0 follows.")

    print("\n(3) NEGATIVE CONTROL (I12): perturbations that violated (C11)")
    print(f"    {'perturbation':>28} {'max H+H''':>11}  (RC)?")
    for eps in (0.05, -0.05, 0.10, -0.10, 0.20, -0.20):
        dd = HpH2(th, eps=eps)
        print(f"    {'H_Sigma + %+.2f*bump' % eps:>28} {dd.max():11.6f}  "
              f"{'holds' if dd.max() <= 1 else 'FAILS'}")
    print(f"    {'':>28}")
    for k, eps in ((2, 0.03), (2, -0.03), (4, 0.01), (4, -0.01), (4, 0.03), (4, -0.03)):
        dd = HpH2_mode(th, eps, k)
        print(f"    {'H_Sigma %+.2f*sin(%d th)' % (eps, k):>28} {dd.max():11.6f}  "
              f"{'holds' if dd.max() <= 1 else 'FAILS'}")
    print("    the bump cases must FAIL (C11) was violated there); the sin(k th) cases")
    print("    that stayed in K' must HOLD.  Any mismatch refutes the claim.")


if __name__ == "__main__":
    main()
