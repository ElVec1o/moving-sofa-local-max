"""ambi_a27.py — re-derive the two structural inputs everything else has been quoting.

WHY THIS FILE EXISTS.  Six results now rest on two formulas that had been taken from the
note rather than re-derived in the shipped machinery:

  prop:cap   |C_2| = int_0^pi (H^2 - H'^2) dtheta - H(0) - H(pi)
  prop:V     |N|   = int_0^{pi/2} [ (1/2)(alpha_2^+)^2 + (1/2)(sigma - alpha_1)^2
                                    - (1/2)(alpha_1^-)^2 ] dt

Quoting a formula that six results depend on is the same defect that cost this project two
rounds elsewhere, so both are checked here by routes independent of the note.

WHAT IS ESTABLISHED.

prop:V, the algebra.  From the corner c(t) = (F-1) mu_t + (G-1) nu_t, differentiating and
pairing against the frame recovers the arms:

    alpha_1 = -<c', mu> = G - 1 - F' ,     alpha_2 = <c', nu> = F - 1 + G'

exactly as the note defines them.  The two sweeps then have Jacobians

    Phi(s,t) = c - s mu :  det = s - alpha_2
    Psi(s,t) = c - s nu :  det = s - alpha_1

and integrating |det| over each sweep's range gives (1/2)(alpha_2^+)^2 and
(1/2)(sigma-alpha_1)^2 - (1/2)(alpha_1^-)^2.  All symbolic, in sympy, independent of the
note's own manipulation.

prop:cap.  Checked against the rasteriser, which computes the cap area from half-plane
constraints on a pixel grid and knows nothing about support functions.  They agree to 0.32
percent over the atom range 0.50 to 1.10, and at Sigma the formula gives 2.013356 against
the 2.013341613 the note reports.

WHAT IS NOT ESTABLISHED.  prop:V's GEOMETRIC hypotheses -- that the two sweeps are
injective, disjoint, and cover the niche -- are not re-derived here.  Those are the content
of the note's Chapter-3-to-6 half and rest on (RC).  This file re-derives the algebra that
turns those hypotheses into the formula, and regression-checks prop:cap; it does not
reprove the hypotheses.  Rule 0: the algebra is PROVED, the geometry stays quoted.

Usage: python3 ambi_a27.py
"""
from __future__ import annotations
import importlib.util
import os

import numpy as np
import sympy as sp

P2 = np.pi / 2


def _load(name):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), name)
    spec = importlib.util.spec_from_file_location(name[:-3], path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def sweep_algebra():
    """Return (arms_ok, det2_ok, det1_ok, alpha1, alpha2) from the corner, symbolically."""
    t, s = sp.symbols('t s', real=True)
    F, G = sp.Function('F')(t), sp.Function('G')(t)
    mu = sp.Matrix([sp.cos(t), sp.sin(t)])
    nu = sp.Matrix([-sp.sin(t), sp.cos(t)])
    c = (F - 1) * mu + (G - 1) * nu
    cp = sp.diff(c, t)
    a1 = sp.simplify(-(cp.T * mu)[0])
    a2 = sp.simplify((cp.T * nu)[0])
    arms_ok = (sp.simplify(a1 - (G - 1 - sp.diff(F, t))) == 0
               and sp.simplify(a2 - (F - 1 + sp.diff(G, t))) == 0)

    def det_of(vec):
        Ph = c - s * vec
        return sp.simplify(sp.Matrix.hstack(sp.diff(Ph, s), sp.diff(Ph, t)).det())

    return (arms_ok,
            sp.simplify(det_of(mu) - (s - a2)) == 0,
            sp.simplify(det_of(nu) - (s - a1)) == 0,
            a1, a2)


def cap_formula(H, x):
    """int_0^pi (H^2 - H'^2) - H(0) - H(pi), splitting the derivative at the atom's kink."""
    dx = x[1] - x[0]
    L, R = x <= P2, x >= P2
    dL, dR = np.gradient(H[L], dx), np.gradient(H[R], dx)
    return (float(np.trapezoid(H[L] ** 2 - dL ** 2, x[L]))
            + float(np.trapezoid(H[R] ** 2 - dR ** 2, x[R])) - H[0] - H[-1])


def main() -> int:
    print(__doc__.split("Usage")[0])
    bad = 0

    print("  (1) prop:V's algebra, from the corner, in sympy\n")
    arms_ok, d2_ok, d1_ok, a1, a2 = sweep_algebra()
    for lbl, ok in (("arms = -<c',mu>, <c',nu> match eq:arm1 and eq:a2", arms_ok),
                    ("face-2 Jacobian det = s - alpha_2", d2_ok),
                    ("face-1 Jacobian det = s - alpha_1", d1_ok)):
        bad += not ok
        print(f"  {lbl:<52} {'OK' if ok else 'FAIL'}")
    print(f"  alpha_1 = {a1}")
    print(f"  alpha_2 = {a2}")

    s, al1, al2, sig = sp.symbols('s alpha1 alpha2 sigma', real=True)
    i2 = sp.simplify(sp.integrate(al2 - s, (s, 0, al2)))
    i1 = sp.simplify(sp.expand(sp.integrate(s - al1, (s, al1, sig))))
    ok2 = sp.simplify(i2 - al2 ** 2 / 2) == 0
    ok1 = sp.simplify(i1 - (sig - al1) ** 2 / 2) == 0
    bad += (not ok2) + (not ok1)
    print(f"\n  int_0^a2 (a2 - s) ds = {i2}   -> (1/2)(alpha_2^+)^2   {'OK' if ok2 else 'FAIL'}")
    print(f"  int_a1^sig (s - a1) ds = {i1}")
    print(f"    = (1/2)(sigma - alpha_1)^2   {'OK' if ok1 else 'FAIL'}, and clipping the lower")
    print("    limit at 0 when alpha_1 < 0 subtracts (1/2)(alpha_1^-)^2, as prop:V states.\n")

    print("  (2) prop:cap against the rasteriser, which knows nothing about H\n")
    cap = _load("ambi_cap.py")
    dc = _load("ambi_disconnected.py")
    pr = _load("ambi_profile.py")
    x = np.linspace(0, np.pi, 400001)
    xs = np.linspace(0, np.pi, 20001)
    r0, _ = cap.cap_sigma(xs)
    base = float(np.trapezoid((r0 * np.sin(xs))[xs <= P2], dx=xs[1] - xs[0]))
    rf, _ = cap.cap_sigma(x)
    print(f"  {'atom c':>8} {'prop:cap':>12} {'raster':>12} {'rel':>8}")
    worst = 0.0
    for c in (0.50, 0.65, 0.7506, 0.90, 1.10):
        val = cap_formula(dc.Hfun(rf, x, c + 1 - base), x)
        capA, _, _ = pr.stages(dc.Hfun(r0, xs, c + 1 - base), xs)
        rel = abs(val - capA) / capA
        worst = max(worst, rel)
        tag = "   <- Sigma; the note reports 2.013341613" if abs(c - 0.7506) < 1e-4 else ""
        print(f"  {c:8.4f} {val:12.6f} {capA:12.6f} {rel:8.2%}{tag}")
    ok = worst < 0.02
    bad += not ok
    print(f"\n  worst relative gap {worst:.2%}   {'AGREE' if ok else 'DISAGREE'}\n")

    print(f"  {'ALL CHECKS PASS' if not bad else f'{bad} CHECK(S) FAILED'}")
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
