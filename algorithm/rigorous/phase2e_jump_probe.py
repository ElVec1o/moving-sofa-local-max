"""Decide crux C3: are the breakpoint jump coefficients Delta_j nonzero,
and if so what SIGN does the breakpoint jet form have?

BACKGROUND
----------
The second variation splits as   Q = Q_bulk + Q_jump,  where (after the
integration by parts verified in phase2f_ibp_check) Q_bulk is an H^1 form
and Q_jump is a finite-rank quadratic form in the breakpoint 1-jets
(eta(b_j), eta'(b_j)).

DECISIVE TEST
-------------
Probe Q on a NARROW BUMP of height h and width w centred at theta_0:

    bulk contribution   ~  -m_1 * h^2 * w      -> 0   as w -> 0
    jump contribution   ~  Delta_j * h^2       -> survives

So the ratio  Q(bump) / (jet amplitude)^2  saturates to the jet-form
coefficient at a breakpoint, and decays to 0 at a non-breakpoint.

Two bump shapes isolate the two jet slots:
    EVEN bump  g(t) = exp(-t^2/w^2)          -> eta(b)=h, eta'(b)=0
    ODD  bump  g(t) = (t/w) exp(-t^2/w^2)    -> eta(b)=0, eta'(b)=h/(w*e^{1/2})...
                                                (slope normalised below)

CONTROLS (I12)
--------------
Non-breakpoint locations must show the ratio DECAYING with w.  If a
control location saturates too, the probe is measuring something else
(e.g. grid artefacts) and the test is void.

SIGN IS THE POINT
-----------------
If the jet form has a POSITIVE direction, then narrow spikes there make
Q > 0 at arbitrarily small H^2 norm, i.e. the trajectory is NOT a local
maximum.  For Gerver this must come out <= 0 (Baek's global result
forces it) -- which is itself a check on the method.  For Romik's Sigma
no such guarantee exists, so the sign there is decisive.

Runtime: ~2-4 min, single sofa build per evaluation, no OOM risk.
"""
from __future__ import annotations
import math, os, sys, time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase2d_qsmooth import tabulate_gerver, build_sofa

HALF = math.pi / 2
# Romik breakpoints: phi, theta_R, pi/2-theta_R, pi/2-phi
PHI = 0.039177364790083641
THETA_R = 0.681301509382724894
BREAKS = [PHI, THETA_R, HALF - THETA_R, HALF - PHI]
# Control locations: interior of arcs, far from every breakpoint
CONTROLS = [0.35, 1.15]


def F_of(th, cx, cy):
    return build_sofa(th, cx, cy).area


def bump(th, t0, w, kind):
    """Localised bump centred at t0 with width w.
    kind='even' -> eta(t0)=1, eta'(t0)=0
    kind='odd'  -> eta(t0)=0, eta'(t0)=1
    Both are C^inf and decay fast, so they are legitimate H^2 directions.
    """
    t = (th - t0) / w
    g = np.exp(-t * t)
    if kind == "even":
        return g                      # value 1 at centre, slope 0
    else:
        return w * t * g * math.e**0  # eta = (th-t0)*exp(...); slope 1 at centre


def probe(th, cx, cy, F0, t0, w, kind, comp, eps):
    """Central-difference Q(eta) for the localised direction eta."""
    e = bump(th, t0, w, kind)
    if comp == "x":
        Fp = F_of(th, cx + eps * e, cy)
        Fm = F_of(th, cx - eps * e, cy)
    else:
        Fp = F_of(th, cx, cy + eps * e)
        Fm = F_of(th, cx, cy - eps * e)
    Q = (Fp - 2 * F0 + Fm) / (eps * eps)
    # H^1 norm^2 of the direction (for the bulk comparison)
    d = np.gradient(e, th)
    h1sq = np.trapezoid(e * e + d * d, th)
    return Q, h1sq


def main():
    n_theta = int(sys.argv[1]) if len(sys.argv) > 1 else 3001
    eps = float(sys.argv[2]) if len(sys.argv) > 2 else 1e-4
    widths = [0.08, 0.05, 0.03, 0.02]

    print("=" * 78)
    print("C3 PROBE: breakpoint jet form via narrow-spike second variation")
    print("=" * 78)
    print(f"  n_theta={n_theta}  eps={eps}  widths={widths}")
    t0 = time.time()
    th, cx, cy = tabulate_gerver(n_theta)
    F0 = F_of(th, cx, cy)
    print(f"  F(c_G) = {F0:.9f}   (Gerver 2.2195317)   [{time.time()-t0:.1f}s]")
    print()
    print("  Reading the table:  Q/jet^2 SATURATES (w-independent) => Delta != 0")
    print("                      Q/jet^2 DECAYS like w            => bulk only")
    print()

    locs = [(f"BREAK b{j+1}", b) for j, b in enumerate(BREAKS)] + \
           [(f"CONTROL    ", c) for c in CONTROLS]

    for comp in ("x", "y"):
        for kind in ("even", "odd"):
            slot = "eta(b)" if kind == "even" else "eta'(b)"
            print(f"--- component {comp},  jet slot {slot} "
                  f"({'value' if kind=='even' else 'slope'}) ---")
            print(f"  {'location':<14} {'theta':>7} " +
                  "".join(f"{'w='+str(w):>12}" for w in widths))
            for name, t0loc in locs:
                row = []
                for w in widths:
                    Q, h1sq = probe(th, cx, cy, F0, t0loc, w, kind, comp, eps)
                    row.append(Q)
                print(f"  {name:<14} {t0loc:>7.4f} " +
                      "".join(f"{q:>12.4f}" for q in row))
            print()

    print("=" * 78)
    print("VERDICT GUIDE")
    print("  - Breakpoint rows saturating to a nonzero constant  => Delta_j != 0,")
    print("    the jet form is real and C3 branch (b) holds (genuine barrier).")
    print("  - All rows decaying with w                          => Delta_j = 0,")
    print("    C3 branch (a): the local-max argument CLOSES.")
    print("  - ANY breakpoint value saturating POSITIVE          => positive")
    print("    direction at arbitrarily small H^2 norm => NOT a local max.")
    print(f"  total {time.time()-t0:.1f}s")
    print("=" * 78)


if __name__ == "__main__":
    main()
