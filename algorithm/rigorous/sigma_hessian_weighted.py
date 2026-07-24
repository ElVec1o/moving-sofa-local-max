"""G1: Sigma true-Hessian block (Shapely ambi oracle) + WEIGHTED-metric ladder.

Weight (DERIVED, exact): on the mu-slot the regular mask vanishes on the cap
phases (lam_A == 0 identically for theta < beta and mirrored -- the
stationary-contact mechanism, same algebra as Gerver phase 1), so
    w_mu(theta) = min(1, sin^2 theta / sin^2 beta, cos^2 theta / sin^2 beta),
    w_nu(theta) = 1.
Weighted H^1 Gram on sine modes: G_w[u,v] = int [w_mu <u',mu><v',mu>
 + w_nu <u',nu><v',nu>] + <u,v>.  Ladder: generalized eigenvalues of Q_Sigma
against G_w at increasing K: flat negative margin = weighted local-Sigma
coercivity (the missing G1 statement, computed form).
Checkpointed; resume by re-running.   python3 sigma_hessian_weighted.py [K]
"""
import sys, os, math, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from romik_hessian import tabulate_romik, ambi_area_from_arrays

HERE = os.path.dirname(os.path.abspath(__file__))
BETA = 0.289653820817320941

def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    n_theta = 1201
    th, cx, cy = tabulate_romik(n_theta)
    F0 = ambi_area_from_arrays(th, cx, cy)
    print(f"F0 = {F0:.7f} (Romik 1.64495), K={K}", flush=True)
    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    n = len(modes); eps = 1e-4
    ck = os.path.join(HERE, f"sigma_hessian_K{K}.npy")
    Q = np.load(ck) if os.path.exists(ck) else np.full((n, n), np.nan)
    basis = {m: np.sin(2*m[1]*th) for m in modes}
    def area(pert):
        cx2, cy2 = cx.copy(), cy.copy()
        for (c, k), a in pert:
            if c == 0: cx2 = cx2 + a*basis[(c, k)]
            else:      cy2 = cy2 + a*basis[(c, k)]
        return ambi_area_from_arrays(th, cx2, cy2)
    t0 = time.time(); total = n*(n+1)//2
    done = int(np.isfinite(np.triu(Q)).sum())
    for i in range(n):
        if np.isfinite(Q[i, i:]).all(): continue
        for j in range(i, n):
            if np.isfinite(Q[i, j]): continue
            if i == j:
                gp = area([(modes[i], eps)]) - F0
                gm = area([(modes[i], -eps)]) - F0
                Q[i, i] = (gp + gm)/eps**2
            else:
                gpp = area([(modes[i], eps), (modes[j], eps)]) - F0
                gmm = area([(modes[i], -eps), (modes[j], -eps)]) - F0
                gpm = area([(modes[i], eps), (modes[j], -eps)]) - F0
                gmp = area([(modes[i], -eps), (modes[j], eps)]) - F0
                Q[i, j] = Q[j, i] = (gpp + gmm - gpm - gmp)/(4*eps**2)
        np.save(ck, Q)
        done = int(np.isfinite(np.triu(Q)).sum())
        el = time.time() - t0
        print(f"row {i+1}/{n}  {100*done/total:.0f}%  elapsed {el/60:.1f}m", flush=True)
    # weighted Gram
    sb2 = math.sin(BETA)**2
    wmu = np.minimum(1.0, np.minimum(np.sin(th)**2, np.cos(th)**2)/sb2)
    G = np.zeros((n, n))
    for i, (ci, ki) in enumerate(modes):
        for j, (cj, kj) in enumerate(modes):
            # u' = e_ci * 2ki cos(2ki th): <u',mu> etc.
            mu = np.array([np.cos(th), np.sin(th)]); nu = np.array([-np.sin(th), np.cos(th)])
            du = 2*ki*np.cos(2*ki*th); dv = 2*kj*np.cos(2*kj*th)
            umu = mu[ci]*du; unu = nu[ci]*du
            vmu = mu[cj]*dv; vnu = nu[cj]*dv
            uval = np.sin(2*ki*th) if ci == cj else 0
            integ = wmu*umu*vmu + unu*vnu
            if ci == cj: integ = integ + np.sin(2*ki*th)*np.sin(2*kj*th)
            G[i, j] = np.trapezoid(integ, th)
    L = np.linalg.cholesky(G); Li = np.linalg.inv(L)
    ev = np.linalg.eigvalsh(0.5*((Li@Q@Li.T)+(Li@Q@Li.T).T))
    print(f"\nWEIGHTED ladder, Sigma, K={K}: max={ev.max():+.5f} min={ev.min():+.5f}")
    print(f"{'NEG DEF in the weighted metric, m_w = %.5f' % -ev.max() if ev.max()<0 else 'INDEF(%d)' % (ev>=0).sum()}")
    # unweighted comparison
    G0 = np.diag([np.pi/4*(1+4*k*k) for (_, k) in modes])
    S0 = np.diag(1/np.sqrt(np.diag(G0)))
    e0 = np.linalg.eigvalsh(S0@Q@S0)
    print(f"unweighted H1 for contrast: max={e0.max():+.5f}")
if __name__ == "__main__":
    main()
