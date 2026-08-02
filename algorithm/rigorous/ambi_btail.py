"""ambi_btail.py — the b-tail constant, by an exact cancellation the old estimate discarded.

THE CLAIM.  In the H^1 coercivity certificate the p-mode coefficients are

    b_k = (1/||p_k||_{H^1}) * int_tau^{pi/2} [ cos t * sin 2kt + 2k * sin t * cos 2kt ] dt

and the note bounded the numerator by integrating the second term by parts, keeping
|numerator| <= 2 + 2 sigma.  That estimate is lossy, and lossy in this project's
characteristic way: the two pieces cancel.  The integrand is

    d/dt [ sin t * sin 2kt ]  =  cos t * sin 2kt + 2k * sin t * cos 2kt

EXACTLY, so the integral is a boundary term and nothing else:

    numerator = [ sin t sin 2kt ]_tau^{pi/2} = sin(pi/2) sin(k pi) - sin(tau) sin(2k tau)
              = - sin(tau) sin(2k tau),          since sin(k pi) = 0 for integer k.

Hence |numerator| <= sin(tau) = cos(sigma), and with ||p_k||_{H^1}^2 = pi/4 + k^2 pi >= k^2 pi,

    sum_{k>N} b_k^2  <=  cos^2(sigma) / (pi N).

At sigma = beta this is 0.292342/N against the note's 2.117661/N: a factor 7.2438.

WHY IT MATTERS.  The note's certificate closed at K <= 0.259397171 against the target
(1/2) sin 2beta = 0.273722337, a margin of 0.0143, and its only sub-PROVED input was a
bound C <= 1.90 on an L^1 norm evaluated by floating-point quadrature.  With the exact
b-tail the margin becomes 0.0549 and the requirement on C relaxes from 1.90 to 2.4658.
The measured C converges to about 1.88, so the rigorous enclosure now has 30 percent of
headroom instead of having to be sharp.  A one-line cancellation buys the last label.

The identity is formalised in lean/MovingSofa/MovingSofa/Anchor.lean as `btail_numerator`.

Usage: python3 ambi_btail.py
"""
from __future__ import annotations
import numpy as np
from scipy.integrate import quad

BETA = 0.2896538208173209
SIGMA = BETA
TAU = np.pi / 2 - SIGMA
TARGET = 0.5 * np.sin(2 * BETA)          # (1/2) sin 2beta = 0.273722337
LAM_MIN = 0.6                            # Proposition prop:garding
ZMZ = 0.132114949                        # certified block value at K = 150
N_CERT = 150
C_MEASURED = 1.90                        # the note's value for the (Mz)-tail constant


def numerator_closed(k: int, tau: float = TAU) -> float:
    """The exact value of the b_k numerator: a boundary term."""
    return -np.sin(tau) * np.sin(2 * k * tau)


def numerator_quad(k: int, tau: float = TAU) -> float:
    """The same integral by quadrature, as an independent check."""
    return quad(lambda t: np.cos(t) * np.sin(2 * k * t)
                + 2 * k * np.sin(t) * np.cos(2 * k * t), tau, np.pi / 2, limit=400)[0]


def btail_const(sigma: float = SIGMA) -> float:
    """cos^2(sigma)/pi, the constant in sum_{k>N} b_k^2 <= const/N."""
    return np.cos(sigma) ** 2 / np.pi


def btail_const_note(sigma: float = SIGMA) -> float:
    """(2+2 sigma)^2/pi, the constant the note used."""
    return (2 + 2 * sigma) ** 2 / np.pi


def certificate(btail_c: float, C: float, N: int = N_CERT) -> float:
    """K <= z^T M z + [ 2*b-tail + 2*(Mz)-tail ] / lambda_min, with both tails analytic."""
    return ZMZ + (2 * btail_c / N + 2 * C ** 2 / N) / LAM_MIN


def C_admissible(btail_c: float, N: int = N_CERT) -> float:
    """The largest C for which the certificate still closes."""
    slack = TARGET - ZMZ - (2 * btail_c / N) / LAM_MIN
    return np.sqrt(slack * LAM_MIN * N / 2)


def main() -> int:
    print(__doc__.split("Usage")[0])
    bad = 0

    print("  (1) the numerator is a boundary term\n")
    print(f"  {'k':>5} {'quadrature':>15} {'closed form':>15} {'|diff|':>10}")
    worst = 0.0
    for k in (1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233):
        q, c = numerator_quad(k), numerator_closed(k)
        worst = max(worst, abs(q - c))
        print(f"  {k:5d} {q:15.9f} {c:15.9f} {abs(q - c):10.2e}")
    ok = worst < 1e-11
    bad += not ok
    print(f"\n  worst deviation {worst:.2e}  {'OK' if ok else 'FAIL'}"
          f"  (an exact derivative, not an estimate)\n")

    print("  (2) the tail bound, against the true tail summed to k = 20000\n")
    print(f"  {'N':>6} {'true tail':>13} {'exact bound':>13} {'note bound':>13} {'exact/true':>11}")
    ks = np.arange(1, 20001)
    terms = (np.sin(TAU) * np.sin(2 * ks * TAU)) ** 2 / (np.pi / 4 + ks ** 2 * np.pi)
    for N in (60, 120, 150, 200):
        true = float(terms[N:].sum())
        e, n = btail_const() / N, btail_const_note() / N
        valid = e > true
        bad += not valid
        print(f"  {N:6d} {true:13.8f} {e:13.8f} {n:13.8f} {e / true:11.3f}"
              f"  {'OK' if valid else 'FAIL: bound below the true tail'}")
    print(f"\n  constant: exact {btail_const():.6f}   note {btail_const_note():.6f}"
          f"   improvement {btail_const_note() / btail_const():.4f}x\n")

    print("  (3) what it buys the certificate at K = 150\n")
    k_note = certificate(btail_const_note(), C_MEASURED)
    k_new = certificate(btail_const(), C_MEASURED)
    print(f"  {'':24} {'K bound':>12} {'target':>12} {'margin':>10}")
    print(f"  {'note b-tail':24} {k_note:12.7f} {TARGET:12.7f} {TARGET - k_note:10.5f}")
    print(f"  {'exact b-tail':24} {k_new:12.7f} {TARGET:12.7f} {TARGET - k_new:10.5f}")
    for name, val in (("note", k_note), ("exact", k_new)):
        if val >= TARGET:
            print(f"  FAIL: the {name} chain does not close")
            bad += 1
    print(f"\n  margin gain {(TARGET - k_new) / (TARGET - k_note):.3f}x\n")

    print("  (4) the requirement on the one remaining measured constant\n")
    c_old = C_admissible(btail_const_note())
    c_new = C_admissible(btail_const())
    print(f"  largest admissible C, note b-tail   {c_old:.4f}")
    print(f"  largest admissible C, exact b-tail  {c_new:.4f}")
    print(f"  measured C converges to about 1.88; headroom goes from"
          f" {100 * (c_old / 1.88 - 1):+.1f}% to {100 * (c_new / 1.88 - 1):+.1f}%")
    rel = c_new > 2.4
    bad += not rel
    print(f"  {'OK' if rel else 'FAIL'}: the enclosure of C no longer has to be sharp\n")

    print(f"  {'ALL CHECKS PASS' if not bad else f'{bad} CHECK(S) FAILED'}")
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
