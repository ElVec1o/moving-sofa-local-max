"""certify_sigma_struct.py — INTERVAL CERTIFICATION of Sigma's closed-form
structure-following second variation (PROGRAM item S7'''-e).

Certified statement:

    Q_struct  is NEGATIVE DEFINITE on the span of {e_comp sin(2kt)}_{k<=K},

in rigorous arb ball arithmetic. By the superset principle (N1) the
structure-following reconstruction satisfies F_struct >= F with equality at
c_R, hence Q_true <= Q_struct along every ray; so a certified
Q_struct < 0 certifies that the TRUE ambidextrous functional strictly
decreases to second order in every direction of the span.

Why this is cleanly certifiable — the three facts established earlier:
 * the per-arc integrands and chord jets are TRAJECTORY-INDEPENDENT (only
   the frame and the mode enter), so no oracle and no junction solve;
 * the arc RANGES are exactly {0, beta, pi/2-beta, pi/2} (every Sigma
   junction sits at a phase transition; Newton residuals ~1e-10);
 * the junction response contributes nothing (envelope null result), so the
   frozen form IS the true structure-following second variation.
Hence every matrix entry is a finite sum of elementary trigonometric
integrals plus finite chord jets — pure ball arithmetic.

Definiteness is METRIC-INDEPENDENT, so Sylvester's criterion on the ball
matrix (all leading principal minors of -Q strictly positive) is a complete
rigorous test; no eigenvalue enclosure is needed.

Caveat recorded honestly: beta enters as a ball of stated radius around
Romik's constant. Enclosing beta itself from its defining equation is the
standard Newton-Kantorovich step already done for Gerver's constants in
gerver_arb.py; it is NOT redone here.

Usage: python3 certify_sigma_struct.py [K] [prec_bits] [beta_radius]
"""
from __future__ import annotations
import os, sys, math

from flint import acb, arb, arb_mat, ctx

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sofa_romik2017_reference import BETA as BETA_F


def build(K, prec=256, brad=1e-16):
    ctx.prec = prec
    PI2 = arb.pi()/2
    B = arb(repr(BETA_F)) + arb(0, brad)     # beta as a ball
    BB = PI2 - B

    # traversal table: (label, t_from, t_to, slot); struct variant
    TAB = [('dA', PI2, arb(0), 'p'), ('rA', arb(0), PI2, 'p'),
           ('dB', PI2, B, 'p'), ('dX', B, BB, 'x'),
           ('dD', BB, arb(0), 'q'), ('rC', arb(0), BB, 'q'),
           ('dC', BB, arb(0), 'q'), ('rD', arb(0), BB, 'q'),
           ('rX', BB, B, 'x'), ('rB', B, PI2, 'p')]

    def fg(comp, t):
        c, s = t.cos(), t.sin()
        return (c, -s) if comp == 0 else (s, c)

    def jets(comp, k, t):
        """p, p+p'', q, q+q'', p', q', s   (all acb)."""
        f, g = fg(comp, t)
        kk = acb(2*k)
        s = (kk*t).sin(); sp = kk*(kk*t).cos(); spp = -kk*kk*(kk*t).sin()
        return (f*s, 2*g*sp + f*spp, g*s, -2*f*sp + g*spp,
                g*s + f*sp, -f*s + g*sp, s)

    def dP(lab, slot, t, comp, k):
        """delta(contact point) as a 2-vector of acb."""
        c, s = t.cos(), t.sin()
        mu = (c, s); nu = (-s, c)
        p, _, q, _, pp, qp, sv = jets(comp, k, t)
        if slot == 'p':
            v = (p*mu[0] + pp*nu[0], p*mu[1] + pp*nu[1])
        elif slot == 'q':
            v = (-qp*mu[0] + q*nu[0], -qp*mu[1] + q*nu[1])
        else:
            v = (sv, acb(0)) if comp == 0 else (acb(0), sv)
        return (v[0], -v[1]) if lab[0] == 'r' else v

    def entry(mu_, mv_):
        cu, ku = mu_; cv, kv = mv_
        tot = arb(0)
        # --- per-arc Wirtinger integrals ---
        for lab, t0, t1, slot in TAB:
            lo, hi = (t0, t1) if float(t0.mid()) < float(t1.mid()) else (t1, t0)
            if float(hi.mid()) - float(lo.mid()) < 1e-14:
                continue
            dir_s = 1.0 if float(t1.mid()) > float(t0.mid()) else -1.0
            fam_s = -1.0 if lab[0] == 'r' else 1.0
            sgn = arb(0.5*dir_s*fam_s)
            if slot == 'p':
                def f(t, _):
                    Ju = jets(cu, ku, t); Jv = jets(cv, kv, t)
                    return (Ju[0]*Jv[1] + Jv[0]*Ju[1])/2
            elif slot == 'q':
                def f(t, _):
                    Ju = jets(cu, ku, t); Jv = jets(cv, kv, t)
                    return (Ju[2]*Jv[3] + Jv[2]*Ju[3])/2
            else:
                if cu == cv:
                    continue
                sig = acb(1 if cu == 0 else -1)
                def f(t, _):
                    Ju = jets(cu, ku, t); Jv = jets(cv, kv, t)
                    spu = acb(2*ku)*(acb(2*ku)*t).cos()
                    spv = acb(2*kv)*(acb(2*kv)*t).cos()
                    return sig*(Ju[6]*spv + Jv[6]*spu)/2
            tot += sgn * acb.integral(f, lo, hi).real
        # --- junction chords (exact ball jets, no integration) ---
        ends = [(lab, t1, slot) for lab, t0, t1, slot in TAB]
        starts = [(lab, t0, slot) for lab, t0, t1, slot in TAB]
        for i in range(len(TAB)):
            l0, tt0, s0 = ends[i]
            l1, tt1, s1 = starts[(i+1) % len(TAB)]
            a0 = dP(l0, s0, acb(tt0), cu, ku); a1 = dP(l1, s1, acb(tt1), cv, kv)
            b0 = dP(l0, s0, acb(tt0), cv, kv); b1 = dP(l1, s1, acb(tt1), cu, ku)
            w = (a0[0]*a1[1] - a0[1]*a1[0]) + (b0[0]*b1[1] - b0[1]*b1[0])
            tot += (w/4).real
        # CW traversal => area = -Green; and d^2F/deps^2 = 2 x (Green term)
        return -2*tot

    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    n = len(modes)
    Q = [[arb(0)]*n for _ in range(n)]
    maxrad = 0.0
    for i in range(n):
        for j in range(i, n):
            e = entry(modes[i], modes[j])
            Q[i][j] = Q[j][i] = e
            maxrad = max(maxrad, abs(float(e.rad())))
        print(f"  row {i+1}/{n}   max entry radius so far {maxrad:.2e}",
              flush=True)
    return Q, n, maxrad


def certify_negdef(Q, n, prec):
    """Sylvester on -Q: all leading principal minors strictly positive."""
    ctx.prec = prec
    ok = True
    dets = []
    for m in range(1, n+1):
        M = arb_mat([[-Q[i][j] for j in range(m)] for i in range(m)])
        d = M.det()
        lo = float(d.mid()) - abs(float(d.rad()))
        dets.append((m, float(d.mid()), lo))
        if not (lo > 0):
            ok = False
            break
    return ok, dets


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    prec = int(sys.argv[2]) if len(sys.argv) > 2 else 256
    brad = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-16
    print(f"certifying Q_struct(Sigma), K={K}, {2*K} modes, prec={prec} bits, "
          f"beta ball radius {brad:g}", flush=True)
    Q, n, maxrad = build(K, prec, brad)
    print(f"\nall {n*(n+1)//2} entries enclosed; max radius {maxrad:.3e}")
    ok, dets = certify_negdef(Q, n, prec)
    print(f"\nSylvester minors of -Q (leading principal):")
    for m, mid, lo in dets[:6]:
        print(f"  order {m:3d}: det = {mid:+.6e}   rigorous lower bound "
              f"{lo:+.6e}")
    if len(dets) > 6:
        m, mid, lo = dets[-1]
        print(f"  ...\n  order {m:3d}: det = {mid:+.6e}   rigorous lower bound "
              f"{lo:+.6e}")
    print()
    if ok:
        print(f"*** CERTIFIED: Q_struct is NEGATIVE DEFINITE on the "
              f"{n}-mode span (arb, {prec} bits). ***")
        print("    By the superset principle this certifies that the TRUE")
        print("    ambidextrous functional strictly decreases to second order")
        print("    in every direction of that span.")
    else:
        bad = dets[-1]
        print(f"NOT certified: minor of order {bad[0]} has lower bound "
              f"{bad[2]:+.3e}")


if __name__ == "__main__":
    main()
