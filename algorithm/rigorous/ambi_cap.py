"""ambi_cap.py — the single constructor for a cap: (absolutely continuous part, atom mass).

WHY THIS FILE EXISTS.  Seven errors in this project trace to one cause: the atom at pi/2 is
a DISTRIBUTION, and code that represents it as a finite-difference spike inside the
curvature-radius array is wrong in a way that some functionals notice and others do not.

  * AREA functionals integrate r, so a spike of the right mass gives the right answer and
    the regression gate passes.
  * ARM functionals read r pointwise, so a spike is not the same object as an atom, and
    the sign sets E1, E2 come out wrong.

The failure mode is therefore silent exactly where it matters most.  Interpolating the
spike away is not a fix either: it removes the atom together with Sigma's genuine a.c.
content near pi/2, which is what invalidated the concavity test.

THE FIX.  Sigma's curvature radius is available in CLOSED FORM.  Differentiating the note's
phase formulas for F and G analytically, H + H'' collapses on each phase:

  SOL1  H = cos t + (1/2) sin t                    ->  H + H'' = 0
  SOL6  H = f1 cos(t/2) + f2 sin(t/2) + kappa cos t + (1/2) sin t
                                                   ->  H + H'' = (3/4)(f1 cos(t/2) + f2 sin(t/2))
  SOL5  H = (1 - 2a1/3) cos t + (1/2) sin t + 1/2  ->  H + H'' = 1/2

and the same on [pi/2, pi] with G.  So

  theta in [0, beta)          r = 0
  theta in [beta, pi/2-beta)  r = (3/4)( f1 cos(theta/2) + f2 sin(theta/2) )
  theta in [pi/2-beta, pi/2)  r = 1/2
  theta in [pi/2, pi/2+beta)  r = 1/2
  theta in [pi/2+beta, pi-beta) r = (3/4)( -f2 cos(s/2) + f1 sin(s/2) ),  s = theta - pi/2
  theta in [pi-beta, pi]      r = 0

with the atom carried SEPARATELY, of mass G'(0) - F'(pi/2), the jump in H' at pi/2.

Two independent confirmations that this is the right object, both checked in main():
  * on SOL6, r = (3/4) f1 sqrt(4 - 2 sqrt2) cos(theta/2 + pi/8) after the phase shift, so
    max r = (3/4) f1 sqrt(4-2 sqrt2) cos(beta/2 + pi/8), which is the note's closed form
    for max (H+H'')_ac.  It is attained at theta = beta.
  * both forced moment conditions hold, and alpha_2(0) comes out at 2 a1 - 1.

CONTRACT.  cap_sigma() returns the pair (r_ac, atom).  No caller ever sees a smeared
surrogate; every consumer states which of the two it uses.  Rule I10: this is the frozen
v1.0 of the representation, and any change to it drops the label of every atom that reads r.

Usage: python3 ambi_cap.py
"""
from __future__ import annotations
import numpy as np

A1 = 0.875287362412732
F1 = 1.202938908156911389070223
F2 = (1 - np.sqrt(2)) * F1
BETA = 0.2896538208173209
P2 = np.pi / 2
ATOM = 1.1670497                      # G'(0) - F'(pi/2), the jump in H' at pi/2


def cap_sigma(x: np.ndarray) -> tuple[np.ndarray, float]:
    """Sigma's cap as (absolutely continuous curvature radius on [0,pi], atom mass at pi/2).

    Closed form, phase by phase.  No finite differences, no spike, no interpolation."""
    r = np.zeros_like(x)
    m6 = (x >= BETA) & (x < P2 - BETA)
    r[m6] = 0.75 * (F1 * np.cos(x[m6] / 2) + F2 * np.sin(x[m6] / 2))
    r[(x >= P2 - BETA) & (x < P2 + BETA)] = 0.5
    s = x - P2
    m6b = (x >= P2 + BETA) & (x < np.pi - BETA)
    r[m6b] = 0.75 * (-F2 * np.cos(s[m6b] / 2) + F1 * np.sin(s[m6b] / 2))
    return r, ATOM


def arms(r: np.ndarray, x: np.ndarray, atom: float) -> tuple[np.ndarray, np.ndarray]:
    """alpha_1(t) = H(t+pi/2) - 1 - H'(t)  and  alpha_2(t) = H(t) - 1 + H'(t+pi/2) on [0,pi/2].

    THE ATOM MAKES H' TWO-VALUED AT pi/2 AND THE ARMS NEED OPPOSITE LIMITS.  alpha_1 reads
    H' at t in [0, pi/2], so the atom has not been crossed: LEFT limit.  alpha_2 reads H'
    at t + pi/2 in [pi/2, pi], so it has: RIGHT limit.  Using the right limit in both places
    flips alpha_1 at the single point t = pi/2 from +0.7506 to -0.4165 and reports Sigma
    UNORDERED on one endpoint.  Eighth atom error, and the first whose mechanism is a
    two-valued derivative rather than a smeared mass."""
    dx = x[1] - x[0]
    rs, rc = r * np.sin(x), r * np.cos(x)
    cs = np.concatenate([[0.0], np.cumsum(rs[1:] + rs[:-1]) * dx / 2])
    cc = np.concatenate([[0.0], np.cumsum(rc[1:] + rc[:-1]) * dx / 2])
    H = np.cos(x) + 0.5 * np.sin(x) + (np.sin(x) * cc - np.cos(x) * cs)
    Hp = -np.sin(x) + 0.5 * np.cos(x) + (np.cos(x) * cc + np.sin(x) * cs)
    Hatom = H + np.where(x > P2, atom * np.sin(x - P2), 0.0)
    Hp_right = Hp + np.where(x >= P2, atom * np.cos(x - P2), 0.0)
    h = (len(x) - 1) // 2
    return Hatom[h:] - 1 - Hp[:h + 1], Hatom[:h + 1] - 1 + Hp_right[h:]


def rc_max_closed() -> float:
    """The note's closed form for max (H+H'')_ac, attained at theta = beta."""
    return 0.75 * F1 * np.sqrt(4 - 2 * np.sqrt(2)) * np.cos(BETA / 2 + np.pi / 8)


def main() -> int:
    print(__doc__.split("Usage")[0])
    x = np.linspace(0, np.pi, 200001)
    dx = x[1] - x[0]
    r, atom = cap_sigma(x)
    c = np.cos(x)
    mL = float(np.trapezoid((r * c)[x <= P2], dx=dx))
    mR = float(np.trapezoid((r * c)[x >= P2], dx=dx))
    a20 = float(np.trapezoid((r * np.sin(x))[x <= P2], dx=dx)) - 1 + atom
    print(f"  {'quantity':<34} {'computed':>14} {'expected':>14} {'ok':>4}")
    rows = [
        ("max r (a.c.)", r.max(), rc_max_closed(), 1e-6),
        ("argmax r / beta", x[int(np.argmax(r))] / BETA, 1.0, 1e-3),
        ("int_0^(pi/2) r cos", mL, 0.5, 1e-5),
        ("int_(pi/2)^pi r cos", mR, -0.5, 1e-5),
        ("alpha_2(0) = 2a1 - 1", a20, 2 * A1 - 1, 1e-5),
        ("r on [0,beta)", float(r[x < BETA].max()), 0.0, 1e-12),
        ("r on [pi-beta,pi]", float(r[x > np.pi - BETA].max()), 0.0, 1e-12),
    ]
    bad = 0
    for name, got, want, tol in rows:
        ok = abs(got - want) < tol
        bad += not ok
        print(f"  {name:<34} {got:14.9f} {want:14.9f} {'OK' if ok else 'FAIL':>4}")
    print(f"\n  {'ALL CHECKS PASS' if not bad else f'{bad} CHECK(S) FAILED'}")
    print(f"  note's max (H+H'')_ac = 0.8388253494; closed form here = {rc_max_closed():.10f}")
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
