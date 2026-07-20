"""Close the two holes left by phase2e_jump_probe:

  (1) the CROSS slot  eta(b_j) * eta'(b_j)  was never measured (each probe
      set one jet slot to zero);
  (2) breakpoints b1 = phi and b4 = pi/2 - phi were CONTAMINATED, because a
      bump of width w = 0.08 centred at 0.0392 is truncated by the domain
      edge theta = 0, which destroys the jet normalisation.

METHOD
------
Polarisation.  With e = even bump (eta(b)=1, eta'(b)=0) and
o = odd bump (eta(b)=0, eta'(b)=1),

    Q(e+o) - Q(e) - Q(o)  =  2*Delta_cross  -  2*m1*<e,o>_{H1}

and <e,o>_{H1} = 0 by parity (e*o is odd; e'*o' is odd), so the left side
measures 2*Delta_cross directly.

WHY THE CROSS SLOT MATTERS
--------------------------
eta(b) IS bounded by ||eta||_{H1} (H1 -> C^0 in 1D), so a pure eta(b)^2 jet
term is harmless.  eta'(b) is NOT H1-bounded, so:
    - the (eta')^2 slot is dangerous  -> measured ~0 in phase2e;
    - the cross slot eta(b)*eta'(b) is LINEAR in eta'(b), hence still not
      H1-controllable, and is therefore also dangerous.
If the cross slot is ~0 too, the entire dangerous part of the jet form
vanishes and the two-norm argument closes.

For b1/b4 we use widths that FIT (w <= 0.012) on a finer theta grid.
"""
from __future__ import annotations
import math, os, sys, time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase2d_qsmooth import tabulate_gerver, build_sofa

HALF = math.pi / 2
PHI = 0.039177364790083641
THETA_R = 0.681301509382724894
EDGE_BREAKS = [("b1 (phi)", PHI), ("b4 (pi/2-phi)", HALF - PHI)]
MID_BREAKS = [("b2 (theta_R)", THETA_R), ("b3 (pi/2-theta_R)", HALF - THETA_R)]
CONTROLS = [("control 0.35", 0.35), ("control 1.15", 1.15)]


def F_of(th, cx, cy):
    return build_sofa(th, cx, cy).area


def shape(th, t0, w, kind):
    t = (th - t0) / w
    g = np.exp(-t * t)
    if kind == "even":
        return g
    if kind == "odd":
        return w * t * g
    return g + w * t * g          # "both": eta(b)=1, eta'(b)=1


def Q_of(th, cx, cy, F0, t0, w, kind, comp, eps):
    e = shape(th, t0, w, kind)
    if comp == "x":
        Fp, Fm = F_of(th, cx + eps * e, cy), F_of(th, cx - eps * e, cy)
    else:
        Fp, Fm = F_of(th, cx, cy + eps * e), F_of(th, cx, cy - eps * e)
    return (Fp - 2 * F0 + Fm) / (eps * eps)


def h1sq(th, t0, w, kind):
    e = shape(th, t0, w, kind)
    d = np.gradient(e, th)
    return np.trapezoid(e * e + d * d, th)


def run_block(title, locs, widths, n_theta, eps):
    print("=" * 78)
    print(f"{title}   (n_theta={n_theta}, widths={widths})")
    print("=" * 78)
    t_start = time.time()
    th, cx, cy = tabulate_gerver(n_theta)
    F0 = F_of(th, cx, cy)
    print(f"  F(c_G) = {F0:.9f}    [{time.time()-t_start:.1f}s]\n")

    for comp in ("x", "y"):
        print(f"--- component {comp} ---")
        print(f"  {'location':<18} {'w':>7} {'D_value':>10} {'D_slope':>10} "
              f"{'D_CROSS':>10} {'m1(bulk)':>9}")
        for name, t0 in locs:
            for w in widths:
                Qe = Q_of(th, cx, cy, F0, t0, w, "even", comp, eps)
                Qo = Q_of(th, cx, cy, F0, t0, w, "odd", comp, eps)
                Qb = Q_of(th, cx, cy, F0, t0, w, "both", comp, eps)
                Ne = h1sq(th, t0, w, "even")
                No = h1sq(th, t0, w, "odd")
                # bulk coercivity from the odd probe (bulk -> 0 there)
                m1 = -Qo / No
                D_slope = Qo + m1 * No          # ~0 by construction of m1
                D_value = Qe + m1 * Ne
                D_cross = 0.5 * (Qb - Qe - Qo)
                print(f"  {name:<18} {w:>7.3f} {D_value:>10.4f} "
                      f"{D_slope:>10.4f} {D_cross:>10.4f} {m1:>9.4f}")
            print()
    print(f"  block time {time.time()-t_start:.1f}s\n")


def main():
    eps = 1e-4
    # Block 1: mid breakpoints + controls, cross slot, standard grid
    run_block("BLOCK 1  cross slot at mid breakpoints and controls",
              MID_BREAKS + CONTROLS, [0.05, 0.03, 0.02], 2001, eps)
    # Block 2: edge breakpoints with widths that FIT inside the domain
    run_block("BLOCK 2  edge breakpoints b1,b4 with fitting widths",
              EDGE_BREAKS, [0.012, 0.008, 0.005], 8001, eps)

    print("=" * 78)
    print("VERDICT GUIDE")
    print("  D_slope and D_CROSS are the DANGEROUS slots (involve eta'(b),")
    print("  which is NOT bounded by ||eta||_{H1}).")
    print("    both ~0 at every breakpoint  => dangerous jet part VANISHES")
    print("                                 => two-norm argument CLOSES.")
    print("    either clearly nonzero       => genuine barrier remains.")
    print("  D_value may be nonzero and is harmless (eta(b) IS H1-bounded);")
    print("  a NEGATIVE D_value additionally helps the maximum.")
    print("=" * 78)


if __name__ == "__main__":
    main()
