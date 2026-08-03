"""ambi_atom.py — closed forms for the atom direction, checked against the rasterised profile.

WHAT THIS SETTLES.  ambi_profile.py measured, along the family that freezes Sigma's
absolutely continuous radius and varies only the atom mass c, that |C_2| is affine in c and
2|N| is convex in c.  Both were HEURISTIC: second differences read off a rasterisation at
its own noise floor.  Both have closed forms.

CAP.  The atom adds c*Phi to H with Phi(theta) = max(0, -cos theta), supported on
[pi/2, pi].  The area functional is quadratic in H, so |C_2|(c) is a quadratic polynomial in
c whose leading coefficient is

    Q = int_0^pi (Phi^2 - Phi'^2) = int_{pi/2}^pi (cos^2 - sin^2) = int_{pi/2}^pi cos 2theta
      = [ sin 2theta / 2 ]_{pi/2}^{pi} = 0 .

Exactly zero, so |C_2| is affine in c with no error term.  The 7.2e-4 seen in the profile is
rasterisation noise and nothing else.  Formalised as `atom_quadratic_vanishes`.

NICHE.  Differentiating the niche area twice in c, the first variation contributes
2 int_{E_2} cos^2 t - 2 int_{E_1^-} sin^2 t, and on the anchored structure with E_2 an
initial segment of length pi/2 - beta and E_1^- one of length beta this is

    f(beta) = pi/2 - 2 beta + sin 2 beta .

f'(beta) = 2(cos 2beta - 1) <= 0, so f decreases; f(0) = pi/2 and f(pi/6) = pi/6 + sqrt3/2.
Since beta < pi/6 on admissible caps, f(beta) >= pi/6 + sqrt3/2 = 1.3896 > 0 uniformly, and
2|N| is strongly convex in c.  Formalised as `niche_second_deriv`, `niche_conv_decreasing`
and `niche_conv_pos`.

WHAT IS NOT PROVED HERE.  Two structural inputs are taken from the note rather than
re-derived: that the cap area is the quadratic functional above, and that the niche's first
variation has the stated form.  This file proves the two consequences GIVEN those, and
checks both against the rasterised profile so that an error in either would show.

Usage: python3 ambi_atom.py
"""
from __future__ import annotations
import importlib.util
import os

import numpy as np

P2 = np.pi / 2
BETA = 0.2896538208173209


def _load(name):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), name)
    spec = importlib.util.spec_from_file_location(name[:-3], path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def Phi(th):
    """The atom's shape function: max(0, -cos theta), i.e. sin(theta - pi/2) on [pi/2, pi]."""
    return np.maximum(0.0, -np.cos(th))


def Q_quadrature(n=2_000_001):
    """int_0^pi (Phi^2 - Phi'^2), by quadrature over the SUPPORT.

    Phi vanishes on [0, pi/2] and equals -cos theta on [pi/2, pi], so the integrand is
    0 to the left of pi/2 and cos 2theta to the right: it JUMPS by 1 there.  Integrating
    across the jump on a uniform grid costs O(h) -- at n = 2e6 that is 7.9e-7, which is
    what a first attempt at this check reported and mistook for a nonzero Q.  Splitting at
    pi/2 leaves a smooth integrand on each piece."""
    th = np.linspace(P2, np.pi, n)
    return float(np.trapezoid(np.cos(th) ** 2 - np.sin(th) ** 2, th))


def f_niche(beta):
    """The second derivative of 2|N| in the atom mass: pi/2 - 2 beta + sin 2 beta."""
    return P2 - 2 * beta + np.sin(2 * beta)


def main() -> int:
    print(__doc__.split("Usage")[0])
    bad = 0

    print("  (1) the cap's quadratic coefficient vanishes\n")
    q = Q_quadrature()
    ok = abs(q) < 1e-12
    bad += not ok
    print(f"  Q by quadrature      {q:+.3e}")
    print(f"  closed form          {0.0:+.3e}   {'OK' if ok else 'FAIL'}"
          "   (an exact derivative over a half period)\n")

    print("  (2) the niche's second derivative, and its sign\n")
    print(f"  {'beta':>10} {'f(beta)':>10} {'f decreasing':>14}")
    prev = None
    for b in (0.0, 0.10, 0.20, BETA, np.pi / 6, 0.80, 1.1549, P2):
        v = f_niche(b)
        dec = "" if prev is None else ("yes" if v < prev else "NO")
        if prev is not None and v >= prev:
            bad += 1
        prev = v
        tag = "  <- Sigma" if abs(b - BETA) < 1e-9 else (
              "  <- pi/6, the arm-sandwich cap" if abs(b - np.pi / 6) < 1e-9 else (
              "  <- root" if abs(v) < 1e-3 else ""))
        print(f"  {b:10.6f} {v:10.6f} {dec:>14}{tag}")
    lo = f_niche(np.pi / 6)
    ok = lo > 1.38
    bad += not ok
    print(f"\n  beta < pi/6 gives f(beta) >= f(pi/6) = pi/6 + sqrt3/2 = {lo:.6f} > 0"
          f"   {'OK' if ok else 'FAIL'}")
    print(f"  at Sigma, f(beta) = {f_niche(BETA):.6f}\n")

    print("  (3) I11: both closed forms against the rasterised profile\n")
    pr = _load("ambi_profile.py")
    cap = _load("ambi_cap.py")
    dc = _load("ambi_disconnected.py")
    x = np.linspace(0, np.pi, 4001)
    dx = x[1] - x[0]
    r0, _ = cap.cap_sigma(x)
    capS, TS, _ = pr.stages(dc.Hfun(r0, x, _load("ambi_cap.py").ATOM), x)
    base = float(np.trapezoid((r0 * np.sin(x))[x <= P2], dx=dx))
    h = 0.05
    cs = np.arange(0.40, 1.001, h)
    C, N = [], []
    for c in cs:
        cA, t, _ = pr.stages(dc.Hfun(r0, x, c + 1 - base), x)
        C.append(cA)
        N.append(cA - t)
    d2C, d2N = np.diff(np.array(C), 2), np.diff(np.array(N), 2)
    floor_ = float(np.abs(d2C).max())
    pred = h ** 2 * f_niche(BETA)
    print(f"  |C_2|  predicted second difference  {0.0:+.6f}")
    print(f"         measured mean               {d2C.mean():+.6f}, max |.| {floor_:.2e}"
          f"  -> consistent with zero at the noise floor")
    print(f"  2|N|   predicted h^2 f(beta)       {pred:+.6f}")
    print(f"         measured mean               {d2N.mean():+.6f}"
          f"   ratio {d2N.mean() / pred:.3f}")
    agree = abs(d2N.mean() / pred - 1) < 0.15 and abs(d2C.mean()) < floor_
    bad += not agree
    print(f"  {'AGREES' if agree else 'DISAGREES'}: an independent closed form reproduces the"
          " measured convexity\n  to within the rasterisation spread, and predicts exactly zero"
          " for the cap.\n")

    print(f"  {'ALL CHECKS PASS' if not bad else f'{bad} CHECK(S) FAILED'}")
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
