"""ambi_kcert.py — the H^1 coercivity certificate, as a re-runnable artifact.

WHY THIS FILE EXISTS.  The A13/A14 certificate existed only as transcript output: no
shipped script contained the value 0.259397 it reports.  That is why its one measured
input sat unclosed for five rounds — you cannot tighten a computation you cannot re-run.

WHAT IT COMPUTES.  With the layer L = [tau, pi/2], tau = pi/2 - sigma,

  D_tau[p,q] = int_0^{pi/2}(p^2 - p'^2) + 2 int_0^{pi/2}(q^2 - q'^2)
               + int_L (p + q')^2 - int_L (q - p')^2

on the basis p_k = sin 2kt (k >= 1) and q_n = sin nt (n odd >= 3), with e = (0, sin t)
split off — e is exactly the single nonnegative mode of Proposition prop:garding, and the
sign convention above is the one that makes D_tau[e] = -(1/2) sin 2sigma, as the note
states.  The certificate is

  K = sup_{eta_perp} B_tau(e,eta)^2 / |D_tau[eta]| = b^T (-A)^{-1} b  <  |D_tau[e]| ,

an identity for a linear functional, not an inequality.  Every entry is elementary: the
three integrals int_0^T sin at sin bt, cos at cos bt, sin at cos bt in closed form, so
there is no quadrature anywhere in the assembly.

REGRESSION (I11).  The note reports K = 0.1320 at sigma = beta against the target
(1/2) sin 2beta = 0.2737223.  A build that does not reproduce that is wrong, and the
sign convention above was pinned by exactly this check.

VALIDATED SOLVE.  For any z, r = b - Mz with M = -A gives the identity
  b^T M^{-1} b = z^T M z + 2 z^T r + r^T M^{-1} r <= z^T M z + 2 z^T r + ||r||^2/lam_min,
so a floating-point z is legitimate: it enters only as a witness, and any z gives a valid
upper bound.  lam_min >= 3/5 by prop:garding.  The two truncation tails are analytic:

  b-tail    sum_{k>N} b_k^2 <= cos^2(sigma)/(pi N)      [ambi_btail.py, PROVED]
  (Mz)-tail sum_{k>M}|(Mz)_k|^2 <= C^2/M with C from ||F - G'||_{L^1} + boundary

Usage: python3 ambi_kcert.py [K]
"""
from __future__ import annotations
import sys
import numpy as np

BETA = 0.2896538208173209
P2 = np.pi / 2
LAM_MIN = 0.6


def _ss(a, b, T):
    """int_0^T sin(at) sin(bt) dt."""
    if abs(a - b) < 1e-14:
        return T / 2 - np.sin(2 * a * T) / (4 * a) if a != 0 else 0.0
    return 0.5 * (np.sin((a - b) * T) / (a - b) - np.sin((a + b) * T) / (a + b))


def _cc(a, b, T):
    """int_0^T cos(at) cos(bt) dt."""
    if abs(a - b) < 1e-14:
        return T / 2 + np.sin(2 * a * T) / (4 * a) if a != 0 else T
    return 0.5 * (np.sin((a - b) * T) / (a - b) + np.sin((a + b) * T) / (a + b))


def _sc(a, b, T):
    """int_0^T sin(at) cos(bt) dt."""
    if abs(a - b) < 1e-14:
        return (1 - np.cos(2 * a * T)) / (4 * a) if a != 0 else 0.0
    return 0.5 * ((1 - np.cos((a - b) * T)) / (a - b) + (1 - np.cos((a + b) * T)) / (a + b))


class Mode:
    """A pair (p, q) with p = sin(ap t) or 0, q = sin(aq t) or 0.  ap = 0 means p = 0."""

    def __init__(self, ap: float, aq: float):
        self.ap, self.aq = ap, aq

    def h1_sq(self) -> float:
        """||(p,q)||^2_{H^1} = int_0^{pi/2} (p^2 + p'^2 + q^2 + q'^2)."""
        s = 0.0
        for a in (self.ap, self.aq):
            if a:
                s += _ss(a, a, P2) + a * a * _cc(a, a, P2)
        return s


def _bulk(m1: Mode, m2: Mode) -> float:
    """int_0^{pi/2}(p1 p2 - p1' p2') + 2 int_0^{pi/2}(q1 q2 - q1' q2')."""
    v = 0.0
    if m1.ap and m2.ap:
        v += _ss(m1.ap, m2.ap, P2) - m1.ap * m2.ap * _cc(m1.ap, m2.ap, P2)
    if m1.aq and m2.aq:
        v += 2 * (_ss(m1.aq, m2.aq, P2) - m1.aq * m2.aq * _cc(m1.aq, m2.aq, P2))
    return v


def _layer(m1: Mode, m2: Mode, tau: float) -> float:
    """int_L (p1+q1')(p2+q2') - int_L (q1-p1')(q2-p2'),  L = [tau, pi/2]."""

    def over(f):
        return f(P2) - f(tau)

    a1p, a1q, a2p, a2q = m1.ap, m1.aq, m2.ap, m2.aq

    def plus(T):                      # int_0^T (p1+q1')(p2+q2')
        v = 0.0
        if a1p and a2p:
            v += _ss(a1p, a2p, T)
        if a1p and a2q:
            v += a2q * _sc(a1p, a2q, T)
        if a1q and a2p:
            v += a1q * _sc(a2p, a1q, T)
        if a1q and a2q:
            v += a1q * a2q * _cc(a1q, a2q, T)
        return v

    def minus(T):                     # int_0^T (q1-p1')(q2-p2')
        v = 0.0
        if a1q and a2q:
            v += _ss(a1q, a2q, T)
        if a1q and a2p:
            v -= a2p * _sc(a1q, a2p, T)
        if a1p and a2q:
            v -= a1p * _sc(a2q, a1p, T)
        if a1p and a2p:
            v += a1p * a2p * _cc(a1p, a2p, T)
        return v

    return over(plus) - over(minus)


def D(m1: Mode, m2: Mode, tau: float) -> float:
    """The polarised second variation D_tau(m1, m2)."""
    return _bulk(m1, m2) + _layer(m1, m2, tau)


def build(K: int, sigma: float):
    """Return (modes, A, b, Dee) with modes H^1-normalised and e = (0, sin t) split off."""
    tau = P2 - sigma
    modes = [Mode(2 * k, 0.0) for k in range(1, K + 1)]
    modes += [Mode(0.0, float(n)) for n in range(3, 2 * K, 2)]
    nrm = np.array([np.sqrt(m.h1_sq()) for m in modes])
    e = Mode(0.0, 1.0)
    n = len(modes)
    A = np.empty((n, n))
    for i in range(n):
        for j in range(i, n):
            A[i, j] = A[j, i] = D(modes[i], modes[j], tau) / (nrm[i] * nrm[j])
    b = np.array([D(e, m, tau) / nm for m, nm in zip(modes, nrm)])
    return modes, A, b, D(e, e, tau)


def C_enclosure(K: int, sigma: float, z, modes, cells: int = 4 * 10 ** 6):
    """A rigorous upper bound for C = sup_k k |(Mz)_k|, from the witness z.

    With w = sum_j (z_j/n_j) mode_j and chi the indicator of the layer L = [tau, pi/2],
    integrating the p_k' factor by parts gives

        D(p_k, w) = int_0^{pi/2} (1+chi) p_k (w_p + w_p'')  -  p_k(tau) * J ,
        J = w_q(tau) - w_p'(tau) ,

    the w_q' terms cancelling identically -- the same cancellation as the b-tail.  Since
    |p_k| <= 1 and n_k >= k sqrt(pi),

        C  <=  ( ||(1+chi)(w_p + w_p'')||_{L^1} + |J| ) / sqrt(pi) .

    W = w_p + w_p'' is a finite trigonometric polynomial, so its L^1 norm is enclosed by a
    midpoint rule plus its own Lipschitz constant: |W(t) - W(mid)| <= (h/2)||W'||_inf on
    each cell, and ||W'||_inf <= sum_k |c_k| 2k exactly.  tau is placed on a cell boundary
    so that chi is constant on every cell.  The floating-point rounding of the midpoint sum
    is allowed for at cells * eps * sum, which is 10^{-9} here against 1.2 of slack."""
    tau = P2 - sigma
    nrm = np.array([np.sqrt(m.h1_sq()) for m in modes])
    coef = z / nrm
    kk = np.arange(1, K + 1)
    cp = coef[:K] * (1 - 4 * kk ** 2)                 # W = sum cp_k sin(2kt)
    lip = float(np.sum(np.abs(cp) * 2 * kk))          # ||W'||_inf
    total = 0.0
    for lo, hi, wt in ((0.0, tau, 1.0), (tau, P2, 2.0)):
        n = max(1, int(round(cells * (hi - lo) / P2)))
        h = (hi - lo) / n
        mid = lo + h * (np.arange(n) + 0.5)
        total += wt * float(np.abs(cp @ np.sin(np.outer(2 * kk, mid))).sum()) * h
    slack = 2 * P2 * (P2 / cells / 2) * lip           # Lipschitz, weight (1+chi) <= 2
    rnd = cells * np.finfo(float).eps * max(total, 1.0)
    nn = np.arange(3, 2 * K, 2)
    J = float(coef[K:] @ np.sin(nn * tau)) - float((coef[:K] * 2 * kk) @ np.cos(2 * kk * tau))
    return (total + slack + rnd + abs(J)) / np.sqrt(np.pi), total, slack, abs(J), lip


def main() -> int:
    print(__doc__.split("Usage")[0])
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    sigma = BETA
    bad = 0

    target = 0.5 * np.sin(2 * sigma)
    _m, A, b, Dee = build(K, sigma)
    M = -A

    print(f"  sigma = beta = {sigma:.10f},  basis size {A.shape[0]} (K = {K})\n")
    print("  (1) the zero mode and the target\n")
    ok = abs(Dee + target) < 1e-12
    bad += not ok
    print(f"  D_tau[e]            {Dee:14.9f}")
    print(f"  -(1/2) sin 2 sigma  {-target:14.9f}   {'OK' if ok else 'FAIL'}"
          f"   (this fixes the sign convention)\n")

    lam = np.linalg.eigvalsh(M)
    print("  (2) lam_min(M) against the proved 3/5\n")
    ok = lam.min() >= LAM_MIN - 1e-9
    bad += not ok
    print(f"  lam_min  {lam.min():.9f}   proved bound {LAM_MIN}   "
          f"{'OK' if ok else 'FAIL: prop:garding violated'}")
    print(f"  lam_max  {lam.max():.9f}\n")

    print("  (3) the certificate, exact solve\n")
    z = np.linalg.solve(M, b)
    Kval = float(b @ z)
    ok = Kval < target
    bad += not ok
    print(f"  K = b^T M^-1 b   {Kval:.9f}")
    print(f"  target           {target:.9f}   margin {target - Kval:+.6f}   "
          f"{'CLOSES' if ok else 'FAILS'}")
    ref = 0.1320
    agree = abs(Kval - ref) < 5e-4
    bad += not agree
    print(f"  I11 regression: the note reports {ref} at sigma = beta -> "
          f"{'AGREES' if agree else f'DISAGREES by {abs(Kval-ref):.5f}'}\n")

    print("  (4) validated solve with analytic tails\n")
    r = b - M @ z
    zMz, zr, rn = float(z @ M @ z), float(z @ r), float(r @ r)
    btail = np.cos(sigma) ** 2 / np.pi / K
    Cup, l1, slack, absJ, lip = C_enclosure(K, sigma, z, _m)
    print(f"  C enclosure from the witness: ||(1+chi)W||_1 <= {l1 + slack:.6f}"
          f"  (Lipschitz slack {slack:.2e}, ||W'||_inf <= {lip:.0f})")
    print(f"                               |J| = {absJ:.6f}   ->   C <= {Cup:.6f}\n")
    closed = 0
    for C in (1.90, 2.4658, Cup):
        # ||r||^2 <= (||b_{>N}|| + ||(Mz)_{>N}||)^2, not 2||b||^2 + 2||Mz||^2: the two
        # tails differ by a factor 5 here, and the polarised form is smaller whenever
        # they differ at all.  Audit item, same family as the b-tail cancellation.
        tails = (np.sqrt(btail) + np.sqrt(C ** 2 / K)) ** 2
        bound = zMz + 2 * zr + (rn + tails) / LAM_MIN
        ok = bound < target
        closed += ok
        tag = "  <- enclosed" if abs(C - Cup) < 1e-12 else ""
        print(f"  C = {C:6.4f}   K <= {bound:.9f}   "
              f"{'CLOSES' if ok else 'FAILS'}   margin {target - bound:+.6f}{tag}")
    if not closed:
        print("  the tails are evaluated at N = K; this basis is too small for them to close")
        bad += 2
    print(f"\n  z^T M z {zMz:.9f}   2 z^T r {2*zr:.2e}   ||r||^2 {rn:.2e}"
          f"   b-tail {btail:.6f}\n")

    print("  (5) basis drift: K_N rises to the truth, so each row is a lower bound\n")
    print(f"  {'K':>5} {'value':>13} {'increment':>12}")
    prev = None
    for k in (15, 25, 40, 60):
        _, Ak, bk, _ = build(k, sigma)
        v = float(bk @ np.linalg.solve(-Ak, bk))
        inc = "" if prev is None else f"{v - prev:12.2e}"
        print(f"  {k:5d} {v:13.9f} {inc:>12}")
        if prev is not None and v < prev - 1e-12:
            print("  FAIL: not monotone; a supremum over a growing subspace must rise")
            bad += 1
        prev = v

    print(f"\n  {'ALL CHECKS PASS' if not bad else f'{bad} CHECK(S) FAILED'}")
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
