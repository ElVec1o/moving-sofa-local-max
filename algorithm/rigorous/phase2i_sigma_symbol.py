"""Tally the multi-contact principal symbol for Romik's AMBIDEXTROUS Sigma.

This is the one ingredient Proposition (multi-contact principal symbol) needs
in the ambidextrous case, and the only thing standing between the structural
chain and a conclusion about Sigma.

WHY MEASURE RATHER THAN READ OFF
--------------------------------
For Gerver we could read (n_mu, n_nu) straight off Romik's five-phase
contact sets.  For Sigma the path uses SOL1 / SOL6 / SOL5, and ODE6's contact
set is not recorded in our formula sheet (it is unused for Gerver).  But the
symbol prediction is itself a sharp, parameter-free test: for Gerver

    <e_x, D_tot e_x> = n_mu cos^2(theta) + n_nu sin^2(theta)
    <e_y, D_tot e_y> = n_mu sin^2(theta) + n_nu cos^2(theta)

reproduced directly measured Rayleigh quotients to 3-4 decimals.  So we can
run the same localized probe on F_ambi and READ the counts off the data.

SUBTLETY FOR SIGMA
------------------
Sigma = S cap rho(S) with rho the reflection across y = 1/2, whose linear part
is diag(1,-1).  Hence rho(mu_theta) = mu_{-theta} and rho(nu_theta) =
-nu_{-theta}: the reflected family contributes normals at angle -theta.  So

    D_tot = n_mu  mu_t  mu_t^T  + n_nu  nu_t  nu_t^T
          + m_mu  mu_-t mu_-t^T + m_nu  nu_-t nu_-t^T

and because mu_t and mu_{-t} are NOT orthogonal, the eigenvalues are no longer
simply the counts.  We therefore fit all four counts to the measured
directional quotients and then report lambda_min(D_tot) directly.

METHOD
------
Odd (slope) bumps at several theta isolate the bulk (their H^1 norm decays
like w), so |Q|/||eta||^2_{H^1} converges to <e, D_tot e> for e = e_x, e_y.
"""
from __future__ import annotations
import math, os, sys, time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from romik_hessian import ambi_area_from_arrays, tabulate_romik

HALF = math.pi / 2
BETA = 0.2897          # Romik's ambidextrous breakpoint (3 arcs)


def probe(th, cx, cy, F0, t0, w, comp, eps=1e-4):
    t = (th - t0) / w
    e = w * t * np.exp(-t * t)              # odd bump: eta(t0)=0, eta'(t0)=1
    if comp == "x":
        Fp = ambi_area_from_arrays(th, cx + eps * e, cy)
        Fm = ambi_area_from_arrays(th, cx - eps * e, cy)
    else:
        Fp = ambi_area_from_arrays(th, cx, cy + eps * e)
        Fm = ambi_area_from_arrays(th, cx, cy - eps * e)
    Q = (Fp - 2 * F0 + Fm) / (eps * eps)
    d = np.gradient(e, th)
    return -Q / np.trapezoid(e * e + d * d, th)


def sym(t, nmu, nnu, mmu, mnu):
    """D_tot for Sigma: direct family at +t, reflected family at -t."""
    def P(a):
        mu = np.array([math.cos(a), math.sin(a)])
        nu = np.array([-math.sin(a), math.cos(a)])
        return np.outer(mu, mu), np.outer(nu, nu)
    Mp, Np = P(t)
    Mm, Nm = P(-t)
    return nmu * Mp + nnu * Np + mmu * Mm + mnu * Nm


def main():
    n_theta = int(sys.argv[1]) if len(sys.argv) > 1 else 1201
    print("=" * 74)
    print("SIGMA multi-contact principal symbol  (ambidextrous)")
    print("=" * 74)
    t0 = time.time()
    th, cx, cy = tabulate_romik(n_theta)
    F0 = ambi_area_from_arrays(th, cx, cy)
    print(f"  F_ambi(c_R) = {F0:.9f}   (Romik 1.6449552)  [{time.time()-t0:.1f}s]")
    print(f"  breakpoints at beta={BETA:.4f} and pi/2-beta={HALF-BETA:.4f}\n")

    locs = [0.12, 0.20, 0.45, 0.70, 0.90, 1.15, 1.40]
    w = 0.05
    print(f"  {'theta':>7} {'phase':>8} {'<ex,De_x>':>11} {'<ey,De_y>':>11} {'trace':>8}")
    data = []
    for t in locs:
        ph = "1" if t < BETA else ("3" if t > HALF - BETA else "2")
        qx = probe(th, cx, cy, F0, t, w, "x")
        qy = probe(th, cx, cy, F0, t, w, "y")
        data.append((t, qx, qy))
        print(f"  {t:>7.2f} {ph:>8} {qx:>11.4f} {qy:>11.4f} {qx+qy:>8.4f}")

    print("\n  trace(D_tot) = n_mu+n_nu+m_mu+m_nu is theta-INDEPENDENT,")
    print("  so a constant trace column confirms the model and gives the")
    print("  total contact count directly.\n")

    # fit the four counts (nonneg integers) to the measured quotients
    best = None
    for nmu in range(4):
        for nnu in range(4):
            for mmu in range(4):
                for mnu in range(4):
                    err = 0.0
                    for t, qx, qy in data:
                        D = sym(t, nmu, nnu, mmu, mnu)
                        err += (D[0, 0] - qx) ** 2 + (D[1, 1] - qy) ** 2
                    if best is None or err < best[0]:
                        best = (err, nmu, nnu, mmu, mnu)
    err, nmu, nnu, mmu, mnu = best
    print(f"  best integer contact counts: direct (n_mu,n_nu)=({nmu},{nnu})  "
          f"reflected (m_mu,m_nu)=({mmu},{mnu})   rms={math.sqrt(err/(2*len(data))):.4f}")
    lm = [np.linalg.eigvalsh(sym(t, nmu, nnu, mmu, mnu))[0] for t, _, _ in data]
    print(f"  lambda_min(D_tot) over probed theta: min={min(lm):.4f} "
          f"max={max(lm):.4f}")
    print()
    if min(lm) > 0.5:
        print(f"  => delta_Sigma = {min(lm):.3f} > 0 : Garding constant available,")
        print("     the Gerver chain transfers and Sigma's local maximality follows")
        print("     on the same conditional footing.")
    else:
        print("  => lambda_min too small / degenerate: chain does NOT transfer as-is.")
    print(f"  total {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
