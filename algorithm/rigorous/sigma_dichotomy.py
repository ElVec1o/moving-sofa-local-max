"""sigma_dichotomy.py — THE CAP DICHOTOMY (PROGRAM item S7'''-d).

Goal: a K-uniform lower bound for the TRUE second variation of Sigma,

    -Q_true(eta) = -Q_rel(eta) + [ N_1(phi)+N_1(-phi) + N_2(psi)+N_2(-psi) ]
                >= m ||eta||^2_{L2}     for all eta _|_ (translation),

where Q_rel is the fan-released form (computed FD ladder) and N is the
fan-bite functional N12. Both terms are >= 0, so the statement is a
DICHOTOMY: wherever the released form degenerates, the bite must take over.

Structure used (all proved):
 * bite lower bound (N12b): N(phi) >= max_s [d(s)]_+^2 G(s),
     d(s) = phi(beta) cos s / cos beta - phi(s),
     G(s) = sin(2 beta) / (2 sin(beta-s) sin(beta+s)),  G >= G(0) = cot beta.
   Using BOTH branches (N(phi) and N(-phi)) covers [d]_+ and [d]_-, so
     N(phi) + N(-phi) >= max_s d(s)^2 G(s) >= cot(beta) * ||d||_inf^2.
 * TRANSLATION INVARIANCE of d: replacing phi by phi + c cos(s) leaves d
   unchanged (the cos-mode is the kernel of h -> h + h'', i.e. exactly the
   rigid-translation data of a fan). So d measures the distance of the cap
   data from the translation direction — the unique true null direction —
   and the bound is compatible with the quotient.
 * cap data: phi(s) = <eta(|s|), mu_{|s|}>   (cap 1, mu-fan at (1,1/2));
   psi(sigma) = <eta(pi/2-|sigma|), nu_{pi/2-|sigma|}>  (cap 2, nu-fan).

The search is restricted to the span of the released form's least-negative
eigenvectors — where -Q_rel is small and the bite must do the work.

Usage: python3 sigma_dichotomy.py [p_dim] [n_samples]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sofa_romik2017_reference import BETA

PI2 = math.pi/2
trapz = np.trapezoid
COTB = 1.0/math.tan(BETA)


def cap_bite_lb(phi_vals, ss):
    """max_s d^2 G over both branches (>= N(phi) + N(-phi) contribution)."""
    pb = float(np.interp(BETA, ss, phi_vals))
    d = pb*np.cos(ss)/math.cos(BETA) - phi_vals
    inner = (ss > 1e-9) & (ss < BETA - 1e-9)
    if not inner.any():
        return 0.0, 0.0
    s = ss[inner]; dd = d[inner]
    G = math.sin(2*BETA)/(2*np.sin(BETA - s)*np.sin(BETA + s))
    plus = np.maximum(dd, 0.0)**2*G
    minus = np.maximum(-dd, 0.0)**2*G
    return float(plus.max()), float(minus.max())


def bites(ex, ey, th):
    """Total bite lower bound over both caps and both branches."""
    ss = np.linspace(0.0, BETA, 800)
    # cap 1: mu-fan.  phi(s) = <eta(s), mu_s>
    ex1 = np.interp(ss, th, ex); ey1 = np.interp(ss, th, ey)
    phi = ex1*np.cos(ss) + ey1*np.sin(ss)
    b1p, b1m = cap_bite_lb(phi, ss)
    # cap 2: nu-fan at t = pi/2 - sigma.  psi(sigma) = <eta(t), nu_t>
    tt = PI2 - ss
    ex2 = np.interp(tt, th, ex); ey2 = np.interp(tt, th, ey)
    psi = -ex2*np.sin(tt) + ey2*np.cos(tt)
    b2p, b2m = cap_bite_lb(psi, ss)
    return b1p + b1m + b2p + b2m


def load_rel(K):
    Q = np.load(os.path.join(THIS, f"sigma_rel_K{K}.npy"))
    return 0.5*(Q + Q.T)


def main():
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    nsamp = int(sys.argv[2]) if len(sys.argv) > 2 else 40000
    th = np.linspace(0.0, PI2, 1601)
    rng = np.random.default_rng(20260729)

    print(f"cot(beta) = {COTB:.4f};  search over the p={p} least-negative "
          f"released directions, {nsamp} samples + polish\n")
    print(f"{'K':>4} {'m_rel(L2)':>11} {'min -Q_rel':>11} {'min bite':>10} "
          f"{'MIN TOTAL':>11} {'at bite frac':>13}")
    for K in (10, 16, 24):
        Q = load_rel(K)
        n = 2*K
        modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
        # L2 Gram is (pi/4) I on this basis
        gl = math.pi/4
        # translation direction u = const e_x : overlaps <sin 2kt, 1> = 1/k (k odd)
        w = np.zeros(n)
        for i, (c, k) in enumerate(modes):
            if c == 0:
                w[i] = (1.0/k) if (k % 2 == 1) else 0.0
        # orthonormal (L2) basis of w-orthogonal complement
        wn = w/np.linalg.norm(w)
        M = np.eye(n) - np.outer(wn, wn)
        U, sv, _ = np.linalg.svd(M)
        B = U[:, sv > 1e-10]                      # n x (n-1), L2-orthonormal cols
        Qp = B.T @ Q @ B / gl                     # quadratic form in L2-normalized coords
        ev, V = np.linalg.eigh(Qp)
        order = np.argsort(-ev)                   # least negative first
        sub = V[:, order[:p]]
        base = B @ sub                            # n x p, columns L2-orthonormal/sqrt(gl)

        def evaluate(a):
            a = a/np.linalg.norm(a)
            v = base @ a                          # coefficients in the sine basis
            ex = sum(v[i]*np.sin(2*k*th) for i, (c, k) in enumerate(modes) if c == 0)
            ey = sum(v[i]*np.sin(2*k*th) for i, (c, k) in enumerate(modes) if c == 1)
            nl2 = trapz(ex*ex + ey*ey, th)
            ex, ey = ex/math.sqrt(nl2), ey/math.sqrt(nl2)
            qrel = float(v @ Q @ v)/nl2
            bl = bites(ex, ey, th)
            return -qrel, bl

        best = None
        A = rng.standard_normal((nsamp, p))
        for a in A:
            nq, bl = evaluate(a)
            tot = nq + bl
            if best is None or tot < best[0]:
                best = (tot, nq, bl, a.copy())
        # local polish
        step = 0.35
        for _ in range(60):
            improved = False
            for _ in range(120):
                cand = best[3] + step*rng.standard_normal(p)
                nq, bl = evaluate(cand)
                if nq + bl < best[0]:
                    best = (nq + bl, nq, bl, cand.copy()); improved = True
            if not improved:
                step *= 0.6
        tot, nq, bl, _ = best
        lam_p = -ev[order[p-1]] if p-1 < len(order) else float('inf')
        lam_next = -ev[order[p]] if p < len(order) else float('inf')
        print(f"{K:4d} {-ev[order[0]]:11.5f} {nq:11.5f} {bl:10.5f} "
              f"{tot:11.5f} {bl/max(tot,1e-12):13.1%}   "
              f"[lam_p={lam_p:.2f}, lam_(p+1)={lam_next:.2f} "
              f"{'SAFE' if lam_next >= tot else 'NOT SAFE'}]", flush=True)


if __name__ == "__main__":
    main()
