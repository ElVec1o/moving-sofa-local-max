"""THE decisive test for the Gerver chain: is the fatal cubic coefficient zero?

WHY THIS MATTERS
----------------
The Green integrand L = 1/2(P1 P2' - P2 P1') is QUADRATIC in the jet
(c,c',c''), verified symbolically: d^3 L/d eps^3 = 0 for all four contact
paths.  So within a fixed combinatorial cell F is exactly quadratic, and the
ENTIRE third variation comes from the moving breakpoints b_j(c).

An earlier draft claimed the affineness of the contact paths kills the
breakpoint jet terms in D^3F.  That reasoning was wrong: affineness governs
the integrand, not the moving limits.  So the coefficient of eta'(b_j)^3 --
the ONLY monomial whose growth defeats the H^1 two-norm estimate
(|eta'(b)|^p / ||eta||^2_{H1} = eps^{p-2} k^{(4-p)/2}, divergent only at p=3)
-- is currently unknown.

  coefficient zero    -> |R_3| <= C ||eta||_{C^1} ||eta||^2_{H^1} holds,
                         two-norm chain closes, strict local max in an
                         H^2-ball.
  coefficient nonzero -> the chain BREAKS for Gerver too, and the two-norm
                         difficulty is real after all.

METHOD
------
Odd bump at a breakpoint: eta(b)=0, eta'(b)=1, and ||eta||^2_{H1} ~ w -> 0.
The fatal term contributes C_3 * (eta'(b))^3 = C_3, INDEPENDENT of w; every
other term carries extra powers of w.  So

    D^3F(odd bump at b_j)  ->  C_3   as w -> 0   (saturates)  => FATAL
                           ->  0                 (decays)     => SAFE

Controls at non-breakpoints must decay; if a control saturates the probe is
measuring something else and the test is void.

Third derivative by the 4-point central stencil
    D^3F ~ [F(+2e) - 2F(+e) + 2F(-e) - F(-e*2)] / (2 e^3)
which is delicate, so we sweep several eps and require stability.
"""
from __future__ import annotations
import math, os, sys, time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase2d_qsmooth import tabulate_gerver, build_sofa

HALF = math.pi / 2
PHI = 0.039177364790083641
TR = 0.681301509382724894
BREAKS = [("b2", TR), ("b3", HALF - TR)]
CONTROLS = [("ctl 0.45", 0.45), ("ctl 1.05", 1.05)]


def D3(th, cx, cy, t0, w, comp, eps):
    """Third variation along the odd bump, 4-point stencil."""
    t = (th - t0) / w
    e = w * t * np.exp(-t * t)          # eta(t0)=0, eta'(t0)=1

    def F(a):
        if comp == "x":
            return build_sofa(th, cx + a * e, cy).area
        return build_sofa(th, cx, cy + a * e).area

    return (F(2 * eps) - 2 * F(eps) + 2 * F(-eps) - F(-2 * eps)) / (2 * eps ** 3)


def main():
    n_theta = int(sys.argv[1]) if len(sys.argv) > 1 else 1501
    th, cx, cy = tabulate_gerver(n_theta)
    print("=" * 74)
    print("FATAL CUBIC TEST:  coefficient of eta'(b_j)^3 in D^3F")
    print("=" * 74)
    print(f"  n_theta={n_theta}\n")
    widths = [0.06, 0.04, 0.025]
    epss = [3e-3, 1e-3]
    for comp in ("x", "y"):
        print(f"--- component {comp} ---")
        print(f"  {'location':>10} {'eps':>8} " +
              "".join(f"{'w='+str(w):>12}" for w in widths))
        for name, t0 in BREAKS + CONTROLS:
            for eps in epss:
                row = [D3(th, cx, cy, t0, w, comp, eps) for w in widths]
                print(f"  {name:>10} {eps:>8.0e} " +
                      "".join(f"{v:>12.3f}" for v in row))
        print()
    print("=" * 74)
    print("READING:  breakpoint rows SATURATING (w-independent, nonzero)")
    print("          => fatal cubic PRESENT => Gerver chain breaks.")
    print("          breakpoint rows DECAYING with w, like the controls")
    print("          => fatal cubic ABSENT  => chain closes.")
    print("          eps-instability => stencil noise, inconclusive.")


if __name__ == "__main__":
    main()
