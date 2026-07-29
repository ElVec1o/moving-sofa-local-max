"""sigma_fanbite.py — THE FAN-BITE FUNCTIONAL N (PROGRAM item N12 / S7'''-c).

At a stationary wall fan (lam_A == 0) the whole family of wall lines passes
through ONE point P_A. At Sigma's cap BOTH families' fans are frozen at the
same point P_A = (1, 1/2): the direct family with normals mu_t (t in [0,beta])
and the reflected family with normals mu_{-t}. Perturbing c -> c + eps*eta
displaces the line with normal mu_s by exactly eps*phi(s), where

    phi(s) = <eta(|s|), mu_{|s|}>            (even on [-beta, beta])

because both families produce the SAME displacement p(t) = <eta(t), mu_t>.
Hence, locally in u = x - P_A,

    Sigma_eps  =  { u : <u, mu_s> <= eps*phi(s),  |s| <= beta }  =:  K_eps
               =  eps * K_1                     (EXACT homogeneity)

and the fan-released set (extreme walls only) is W_eps = eps*W_1. Therefore

    F_rel(c + eps eta) - F(c + eps eta)  =  eps^2 * N(phi),
    N(phi) := |W_1 \\ K_1|  >= 0,

an EXACTLY quadratic, one-signed (favourable) loss. Consequences:

    Q_true(eta) = Q_rel(eta) - 2 N(phi)

with N positively homogeneous of degree 2 but NOT a quadratic form (N(phi)
and N(-phi) differ) — this is the exact source of the one-sided kink, and it
is the coercivity that repairs the released form's flat directions.

Closed form (all constraints active, i.e. phi + phi'' >= 0):

    N(phi) = phi(beta)^2 tan(beta) + int_0^beta ( phi'^2 - phi^2 ) ds

(check: phi = const c gives c^2 (tan beta - beta), the exact area between a
circular arc of radius c and its two tangent lines — correct).

Elementary rigorous LOWER bound (one interior cut is contained in the bite):

    N(phi) >= max_{|s|<beta} [d(s)]_+^2 * sin(2 beta) /
                             (2 sin(beta - s) sin(beta + s)),
    d(s) = phi(beta) cos(s)/cos(beta) - phi(s).

For an oscillatory phi this is ~ (oscillation amplitude)^2: L^2-type
coercivity on exactly the cap-concentrated directions where Q_rel degenerates.

This script validates the identity F_rel - F = eps^2 N against the true
ambidextrous oracle.
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))

from shapely.geometry import Polygon as SPoly
from romik_hessian import tabulate_romik, ambi_area_from_arrays
from sigma_hessian_released import released_area
from sofa_romik2017_reference import BETA

BIG = 4000.0
trapz = np.trapezoid


def half_plane(normal, offset, big=BIG):
    """Polygon approximating { u : <u, n> <= c } inside a big box."""
    n = np.array(normal, float)
    n = n/np.linalg.norm(n)
    t = np.array([-n[1], n[0]])
    p0 = n*offset
    return SPoly([p0 + t*big, p0 - t*big,
                  p0 - t*big - n*2*big, p0 + t*big - n*2*big])


def bite_area(phi_func, beta=BETA, m=1200):
    """N(phi) = |W_1 \\ K_1| by direct half-plane intersection."""
    ss = np.linspace(-beta, beta, m)
    W = half_plane((math.cos(beta), math.sin(beta)), phi_func(beta))
    W = W.intersection(half_plane((math.cos(-beta), math.sin(-beta)),
                                  phi_func(-beta)))
    K = W
    for s in ss[1:-1]:
        K = K.intersection(half_plane((math.cos(s), math.sin(s)), phi_func(s)))
    R = 1500.0
    box = SPoly([(-R, -R), (R, -R), (R, R), (-R, R)])
    return float(W.intersection(box).area - K.intersection(box).area)


def bite_closedform(phi_func, beta=BETA, m=4000):
    """phi(beta)^2 tan beta + int_0^beta (phi'^2 - phi^2)  (all-active form)."""
    ss = np.linspace(0.0, beta, m)
    ph = np.array([phi_func(float(s)) for s in ss])
    dp = np.gradient(ph, ss)
    return float(phi_func(beta)**2*math.tan(beta) + trapz(dp*dp - ph*ph, ss))


def bite_lowerbound(phi_func, beta=BETA, m=2000):
    """max over one interior cut — a rigorous lower bound on N."""
    best = 0.0
    pb = phi_func(beta)
    for s in np.linspace(-beta*0.999, beta*0.999, m):
        d = pb*math.cos(s)/math.cos(beta) - phi_func(float(s))
        if d <= 0:
            continue
        a = d*d*math.sin(2*beta)/(2*math.sin(beta-s)*math.sin(beta+s))
        best = max(best, a)
    return best


def main():
    n_theta = 1201
    th, cx, cy = tabulate_romik(n_theta)
    F0t = ambi_area_from_arrays(th, cx, cy)
    F0r = released_area(th, cx, cy)
    print(f"F_true(c_R) = {F0t:.8f}   F_rel(c_R) = {F0r:.8f}   "
          f"diff = {F0r-F0t:+.2e}\n")

    # cap-supported x-polarized test directions
    def bump(t, a, b):
        u = (t - a)/(b - a)
        return np.where((u > 0) & (u < 1), np.sin(np.pi*np.clip(u, 0, 1))**2, 0.0)

    tests = [
        ("half-cap bump",   lambda t: bump(t, 0.05*BETA, 0.55*BETA)),
        ("wide cap bump",   lambda t: bump(t, 0.02*BETA, 0.98*BETA)),
        ("2-lobe oscill.",  lambda t: bump(t, 0.05*BETA, 0.5*BETA)
                                      - bump(t, 0.5*BETA, 0.95*BETA)),
    ]
    print(f"{'direction':>16} {'eps':>9} {'(F_rel-F)/eps^2':>16} "
          f"{'N geom':>10} {'N closed':>10} {'N lower':>10}")
    for name, gf in tests:
        g = gf(th)
        nrm = math.sqrt(trapz(g*g, th)); g = g/nrm
        # phi(s) = <eta(|s|), mu_|s|> = g(|s|) cos(|s|)   for eta = e_x g
        gi = lambda s: float(np.interp(abs(s), th, g))*math.cos(abs(s))
        Ng = bite_area(gi)
        Nc = bite_closedform(gi)
        Nl = bite_lowerbound(gi)
        for eps in (4e-3, 2e-3, 1e-3):
            Ft = ambi_area_from_arrays(th, cx + eps*g, cy)
            Fr = released_area(th, cx + eps*g, cy)
            ratio = (Fr - Ft - (F0r - F0t))/eps**2
            print(f"{name:>16} {eps:9.1e} {ratio:16.5f} "
                  f"{Ng:10.5f} {Nc:10.5f} {Nl:10.5f}", flush=True)
        print()


if __name__ == "__main__":
    main()
