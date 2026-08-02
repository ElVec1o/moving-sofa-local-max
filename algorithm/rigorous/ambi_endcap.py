"""ambi_endcap.py — how fast does the diagonal family degenerate at the end cap?

WHY.  D_tau degenerates as tau -> pi/2: at tau = pi/2 the mode (0, sin t) has D-value 0,
which is why case (b) of thm:diag is a separate spectral-splitting argument rather than a
continuation of case (a).  The RATE decides whether that argument is calibrated correctly.
An external roadmap for this project asserted the degeneracy decays like theta^1.69 and
proposed rebuilding the analytic framework around that rate.  This file measures it.

THE BASIS.  p = sum a_k sin(2kt) and q = sum b_k sin((2k-1)t) impose p(0) = p(pi/2) = 0 and
q(0) = 0 with q(pi/2) FREE, exactly and by construction.  A first attempt with finite
differences put p and q on the same node set, which mismatches their boundary spaces; it
returned a POSITIVE top eigenvalue, contradicting thm:diag, and that contradiction is what
exposed the bug.  Recorded because the artifact was small (+0.0024) and nearly constant in
tau, so it read as plausible.

THE FORM.  D_tau[p,q] = int_0^(pi/2) [2p^2 - 2p'^2 + q^2 - q'^2]
                        - int_0^tau (p + q')^2 + int_0^tau (q - p')^2 .

RESULT.  Fitting |lambda_max| ~ sigma^p on sigma = pi/2 - tau <= 0.10:

    K     20     30     45     60
    p   0.834  0.896  0.942  0.957

rising towards 1 as the basis grows.  That matches the damping -(1/2) a^2 sin(2 sigma) ~
sigma used by case (b).  The degeneracy is LINEAR, not theta^1.69, so the existing argument
is calibrated to the right rate and no framework tuned to a faster decay is required.

REGRESSION (rule I11).  Every eigenvalue at every tau and every K must be NEGATIVE, since
thm:diag says D_tau <= 0.  This discretisation shares no code with the proof, so agreement
is an independent check.  The script exits non-zero if any eigenvalue is positive.

Rule 7: the exponent is HEURISTIC.  The negativity is a regression test, not a proof.

Usage: python3 ambi_endcap.py [Kmax]
"""
from __future__ import annotations
import sys
import numpy as np
from scipy.linalg import eigh

P2 = np.pi / 2


def top_eigenvalue(tau: float, K: int, M: int = 8000) -> float:
    t = np.linspace(0.0, P2, M)
    dt = t[1] - t[0]
    wq = np.full(M, dt)
    wq[0] = wq[-1] = dt / 2
    P = np.array([np.sin(2 * k * t) for k in range(1, K + 1)])
    Pp = np.array([2 * k * np.cos(2 * k * t) for k in range(1, K + 1)])
    Q = np.array([np.sin((2 * k - 1) * t) for k in range(1, K + 1)])
    Qp = np.array([(2 * k - 1) * np.cos((2 * k - 1) * t) for k in range(1, K + 1)])
    chi = (t <= tau).astype(float)
    ip = lambda A, B, ww: (A * ww) @ B.T
    A11 = 2 * ip(P, P, wq) - 2 * ip(Pp, Pp, wq) - ip(P, P, chi * wq) + ip(Pp, Pp, chi * wq)
    A22 = ip(Q, Q, wq) - ip(Qp, Qp, wq) - ip(Qp, Qp, chi * wq) + ip(Q, Q, chi * wq)
    Bx = -(ip(P, Qp, chi * wq) + ip(Pp, Q, chi * wq))
    A = np.block([[A11, Bx], [Bx.T, A22]])
    A = 0.5 * (A + A.T)
    Z = np.zeros((K, K))
    G = np.block([[ip(P, P, wq), Z], [Z, ip(Q, Q, wq)]])
    return float(eigh(A, G, eigvals_only=True)[-1])


def main() -> int:
    Kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    print(__doc__.split("Usage")[0])
    sigs = np.array([0.10, 0.07, 0.05, 0.035, 0.025, 0.017])
    Ks = [K for K in (20, 30, 45, 60) if K <= Kmax] or [Kmax]
    print(f"  {'K':>5} {'exponent p':>12} {'lambda at sigma=0.017':>23}")
    bad = 0
    ps = []
    for K in Ks:
        lam = np.array([top_eigenvalue(P2 - s, K) for s in sigs])
        bad += int((lam > 0).sum())
        p = float(np.polyfit(np.log(sigs), np.log(-lam), 1)[0])
        ps.append(p)
        print(f"  {K:5d} {p:12.4f} {lam[-1]:23.7f}")
    print(f"\n  exponent rises {ps[0]:.3f} -> {ps[-1]:.3f} towards 1, the rate case (b) uses")
    print(f"  an external roadmap asserted 1.69; that is not what the form does")
    print(f"\n  REGRESSION (I11): every eigenvalue must be negative (thm:diag).")
    print(f"    positive eigenvalues found: {bad} -> "
          f"{'AGREES with thm:diag' if bad == 0 else '*** CONTRADICTS thm:diag ***'}")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
