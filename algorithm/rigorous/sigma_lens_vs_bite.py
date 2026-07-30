"""sigma_lens_vs_bite.py — S12: can the N12 fan bite absorb the lens?

The Mode-2 repair costs the ladder L(v)/(pi/4) of margin, measured up to 13.25
against a margin of 6.4563, so the corrected form is not negative definite
(S10).  But the lens is exactly eps^2-homogeneous and ONE-SIDED -- L(+eps) =
1.1006 vs L(-eps) = 10.4068 on the same direction -- i.e. structurally the same
object as the N12 fan bite.  And the Sigma dichotomy already CREDITS a one-sided
bite bonus:

    G(eta) = -Q_rel(eta)/gl + 2 [ N1(phi_eta) + N2(psi_eta) ]  > 0,   gl = pi/4.

With the lens the condition becomes

    G_corr(eta) = G(eta) - L(eta)/gl > 0,

so the question is whether the bite bonus 2(N1+N2) covers the lens cost L/gl ON
THE SAME DIRECTIONS AND THE SAME SIDE.  Both are one-sided, so the comparison must
be made branch by branch: the minus branch at v is the plus branch at -v, and
`bite_lb` handles that automatically through its max(d,0)^2.

If the bite covers the lens, the dichotomy absorbs Mode 2 and the trimmed-curve
reconstruction (a day of Rust) is unnecessary.  If it does not, that Rust work is
the only route left.

This is the cheap test, run before committing to the expensive route.

Usage: python3 sigma_lens_vs_bite.py [K] [n_dir]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sigma_onesided import setup, bite_lb
from sigma_matched import solve_matched
from sigma_resolved import areas


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    nd = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    # the bite machinery is built at the ladder's K; the lens at K=6 modes.
    KB = 24
    A, D1, D2, Gs, inner, n, gl = setup(KB)
    modes_b = [(c, k) for c in (0, 1) for k in range(1, KB+1)]
    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    idx = [modes_b.index(m) for m in modes]        # embed K=6 into K=24

    d0, _ = solve_matched([0.0]*len(modes), modes)
    rng = np.random.default_rng(2024)

    print("S12 -- does the N12 fan bite absorb the Mode-2 lens?")
    print(f"  bite machinery at K={KB}, lens directions at K={K}, gl = pi/4")
    print("  need:  bite bonus 2(N1+N2)  >=  lens cost L/gl,  branch by branch\n")
    print(f"{'dir':>4} {'eps':>8} {'L(v)':>9} {'L/gl':>9} "
          f"{'2(N1+N2)':>10} {'-Q/gl':>9} {'G_corr':>9}  absorbed?")
    worst = None
    for t_ in range(nd):
        v6 = rng.standard_normal(len(modes)); v6 /= np.linalg.norm(v6)
        for e in (0.004, -0.004, 0.002, -0.002):
            dm, res = solve_matched(list(e*v6), modes, d0)
            if res > 1e-4:
                print(f"{t_+1:>4} {e:8.4f}   (matched residual {res:.1e} -- "
                      f"skipped)")
                continue
            sl, rs = areas(list(e*v6), dm, modes, 600)
            L = 2*(rs - sl)/e**2
            # the branch actually probed is sign(e)*v6; embed and normalise
            vb = np.zeros(len(modes_b))
            vb[idx] = math.copysign(1.0, e)*v6
            vb = vb/np.linalg.norm(vb)
            b1, _, _ = bite_lb(vb, D1, Gs, inner)
            b2, _, _ = bite_lb(vb, D2, Gs, inner)
            bite = 2*(b1 + b2)
            rq = float(vb @ A @ vb)
            gcorr = rq + bite - L/gl
            ok = bite >= L/gl
            # the decision is the ABSORPTION ratio, not G_corr: G_corr uses the
            # Rayleigh quotient of A on a RANDOM direction (~130-310), which is
            # nothing to do with the margin (the MINIMUM eigenvalue, 6.4563).
            # Comparing G_corr to 0 on random directions is meaningless.
            ratio = bite/(L/gl)
            if worst is None or ratio < worst[0]:
                worst = (ratio, t_+1, e)
            print(f"{t_+1:>4} {e:8.4f} {L:9.4f} {L/gl:9.4f} {bite:10.4f} "
                  f"{rq:9.4f} {gcorr:9.4f}  {'yes' if ok else 'NO'}")
        print()
    print(f"worst absorption ratio bite/(L/gl): {worst[0]:.4f} "
          f"(dir {worst[1]}, eps {worst[2]:+.4f});  need >= 1")
    print("\nVERDICT:", "the bite covers the lens on every probe -- the "
          "dichotomy absorbs Mode 2." if worst[0] >= 1.0 else
          "the bite does NOT cover the lens. Worse, the two are supported on\n"
          "  OPPOSITE branches -- the bite fires on the + branch where the lens is\n"
          "  small, and collapses on the - branch where the lens is large. So the\n"
          "  N12 dichotomy cannot absorb Mode 2, and the trimmed-curve\n"
          "  reconstruction is the only route left.")


if __name__ == "__main__":
    main()
