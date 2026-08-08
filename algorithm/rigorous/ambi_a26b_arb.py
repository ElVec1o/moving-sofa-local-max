"""ambi_a26b_arb.py — certify the niche second variation positive definite, in ball arithmetic.

WHY THIS FILE EXISTS.  ambi_a26b.py found lam_min = 0 to machine precision with a
one-dimensional kernel, but also found the spectrum accumulating at zero: at 52 modes the
smallest nonzero eigenvalues are 3e-10, and the three terms of D on those directions are
individually of order one and cancel,

    0.020503 + 1.903802 - 1.924305 = 2.97e-10 .

Six orders above the rounding floor of an order-one difference is not a certificate.
Floating point cannot decide the sign there.  Ball arithmetic can.

THE TAN DISAPPEARS.  The obstacle to an exact assembly looked like the reach term
int (eta_F tan t + eta_F')^2, whose integrand is singular at pi/2.  Polarising the
integration by parts that gave the left-half identity,

    int_0^{pi/2} u_i u_j = int_0^{pi/2} ( eta'_i eta'_j - eta_i eta_j ) ,

so tan cancels in the BILINEAR form, not just on the diagonal.  On the admissible basis this
block is diagonal with entries (pi/4)(n^2 - 1) -- exactly the Wirtinger weights of
ambi_wirtinger.py, zero only at n = 1.  Every entry of D is then an elementary trigonometric
integral, and the O(h) quadrature error from the singularity disappears with it.

THE CERTIFICATE.  D is positive semidefinite with kernel the gauge, so it is not positive
definite and no Cholesky of D can succeed.  Deflate: the gauge is cos(theta) on both halves,
which in this basis is (left n=1) - (right n=1), so dropping the first right mode leaves a
complement of the kernel on which D must be positive definite.  A Cholesky in ball
arithmetic on that submatrix certifies it: every pivot is a ball provably above zero, so the
conclusion holds for every real matrix in the enclosure.

WHAT IS CERTIFIED, AND WHAT IS NOT.  This certifies D > 0 on the deflated span of the first
N modes, for N up to 32, at 800 bits.  It says nothing about modes beyond the truncation.
The tail needs a separate analytic bound, of the kind that closed the coercivity
certificate's two tails.  Rule 0: the truncated statement is VERIFIED by interval arithmetic;
the full statement remains open on the tail.

Usage: python3 ambi_a26b_arb.py [max_K]
"""
from __future__ import annotations
import sys

from flint import arb, ctx

PREC = 800


def _p2():
    return arb.pi() / 2


def _beta():
    """Sigma's beta as a ball, widened past its printed precision."""
    b = arb("0.2896538208173209")
    return arb(b.mid(), 1e-16)


def ss(a, b, T):
    a, b = arb(a), arb(b)
    if a == b:
        return T / 2 - (2 * a * T).sin() / (4 * a)
    return ((a - b) * T).sin() / (2 * (a - b)) - ((a + b) * T).sin() / (2 * (a + b))


def cc(a, b, T):
    a, b = arb(a), arb(b)
    if a == b:
        return T / 2 + (2 * a * T).sin() / (4 * a)
    return ((a - b) * T).sin() / (2 * (a - b)) + ((a + b) * T).sin() / (2 * (a + b))


def sc(a, b, T):
    a, b = arb(a), arb(b)
    if a == b:
        return (1 - (2 * a * T).cos()) / (4 * a)
    return (1 - ((a - b) * T).cos()) / (2 * (a - b)) + (1 - ((a + b) * T).cos()) / (2 * (a + b))


def freq(i, K):
    return 2 * (i % K) + 1


def pair(i, K):
    """(delta alpha_1, delta alpha_2) for basis mode i, as (coefficient, frequency, kind).

    Left mode n:  eta_F = cos nt, eta_K = 0   ->  d a1 = n sin nt,  d a2 = cos nt
    Right mode n: eta_F = 0, eta_K = sin nt   ->  d a1 = sin nt,    d a2 = n cos nt"""
    n = freq(i, K)
    if i < K:
        return (arb(n), n, 's'), (arb(1), n, 'c')
    return (arb(1), n, 's'), (arb(n), n, 'c')


def ip(p, q, T):
    (c1, n1, k1), (c2, n2, k2) = p, q
    if k1 == 's' and k2 == 's':
        v = ss(n1, n2, T)
    elif k1 == 'c' and k2 == 'c':
        v = cc(n1, n2, T)
    elif k1 == 's':
        v = sc(n1, n2, T)
    else:
        v = sc(n2, n1, T)
    return c1 * c2 * v


def build(K):
    """D on the first K left and K right modes, every entry a ball."""
    N, T2, beta = 2 * K, _p2() - _beta(), _beta()
    M = [[arb(0)] * N for _ in range(N)]
    for i in range(N):
        p1i, p2i = pair(i, K)
        for j in range(i, N):
            p1j, p2j = pair(j, K)
            v = 2 * ip(p2i, p2j, T2) - 2 * ip(p1i, p1j, beta)
            if i < K and j < K and freq(i, K) == freq(j, K):
                v = v + (arb.pi() / 2) * (freq(i, K) ** 2 - 1)      # the reach block
            M[i][j] = v
            M[j][i] = v
    return M


def cholesky_certifies(M, idx):
    """True iff a ball Cholesky of M[idx][idx] has every pivot provably positive."""
    n = len(idx)
    L = [[arb(0)] * n for _ in range(n)]
    smallest = None
    for i in range(n):
        for j in range(i + 1):
            s = M[idx[i]][idx[j]]
            for k in range(j):
                s = s - L[i][k] * L[j][k]
            if i == j:
                if not (s > 0):
                    return False, s, smallest
                smallest = s if smallest is None or (s < smallest) else smallest
                L[i][i] = s.sqrt()
            else:
                L[i][j] = s / L[j][j]
    return True, arb(0), smallest


def cap_form(K):
    """The cap's second variation, diagonal: (pi/2)(1 - n^2) on every mode."""
    return [(arb.pi() / 2) * (1 - freq(i, K) ** 2) for i in range(2 * K)]


def T_form(K):
    """-delta^2 |T| = D_niche - D_cap, the object that must be positive semidefinite."""
    M = build(K)
    cap = cap_form(K)
    for i in range(2 * K):
        M[i][i] = M[i][i] - cap[i]
    return M


def main() -> int:
    print(__doc__.split("Usage")[0])
    ctx.prec = PREC
    maxK = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    bad = 0

    b = _beta()
    f_beta = _p2() - 2 * b + (2 * b).sin()
    print(f"  precision {PREC} bits;  beta as a ball of radius 1e-16\n")
    print(f"  {'K':>4} {'modes':>7} {'verdict':>14} {'smallest pivot':>34}")
    piv = None
    for K in (3, 4, 6, 8, 12, 16):
        if K > maxK:
            break
        M = build(K)
        idx = [i for i in range(2 * K) if i != K]          # drop the gauge's right component
        ok, bad_pivot, smallest = cholesky_certifies(M, idx)
        bad += not ok
        piv = smallest
        print(f"  {K:4d} {2*K:7d} {'CERTIFIED PD' if ok else 'FAILED':>14} "
              f"{str(smallest if ok else bad_pivot)[:34]:>34}")

    print(f"\n  The smallest pivot is the atom's own value f(beta) = pi/2 - 2 beta + sin 2 beta")
    print(f"  = {str(f_beta)[:34]}")
    same = piv is not None and (piv - f_beta).abs_upper() < 1e-9
    bad += not same
    print(f"  smallest pivot equals f(beta): {'OK' if same else 'FAIL'}"
          "   (the atom is the tightest deflated direction)\n")

    print("  Every pivot is a ball strictly above zero, so D is positive definite on the")
    print("  deflated span for every real matrix in the enclosure.  This is a certificate,")
    print("  not a measurement.  It covers the first 32 modes only; the tail beyond the")
    print("  truncation needs a separate analytic bound and is NOT established here.\n")

    print("  the object that actually matters: -delta^2|T| = D_niche - D_cap\n")
    print("  The niche form alone is not coercive -- its spectrum accumulates at zero.  But")
    print("  |T| = |C_2| - 2|N|, so the relevant form is D_niche MINUS the cap's, and the")
    print("  cap is negative definite off its own kernel.  The two non-coercivities cancel.\n")
    print(f"  {'K':>4} {'modes':>7} {'verdict':>14} {'smallest pivot':>30}")
    for K in (3, 4, 6, 8, 12, 16):
        if K > maxK:
            break
        MT = T_form(K)
        idx = [i for i in range(2 * K) if i != K]
        ok, bp, sm = cholesky_certifies(MT, idx)
        bad += not ok
        print(f"  {K:4d} {2*K:7d} {'CERTIFIED PD' if ok else 'FAILED':>14} "
              f"{str(sm if ok else bp)[:30]:>30}")
    print("\n  Unlike the niche form, this one has a spectral GAP: in floating point lam_2 is")
    print("  3.0589, 3.0288, 3.0237, 3.0217, 3.0195, 3.0180 at 8, 16, 24, 32, 40 and 52")
    print("  modes -- stable, not collapsing.  The diagonal grows quadratically: at 52 modes")
    print("  (-d2|T|)_nn / n^2 is 2.7563, 2.8334, 2.8374, 2.8419 at n = 7, 17, 31, 51.  So")
    print("  |T| is strictly concave modulo the gauge with a uniform margin, and the tail")
    print("  beyond any truncation is controlled by that quadratic growth rather than being")
    print("  the delicate cancellation the niche form alone presents.\n")

    print("  the gap, certified rather than measured\n")
    print("  Deflating removes the zero but does NOT hand over the full matrix's lam_2:")
    print("  by Cauchy interlacing the submatrix's least eigenvalue lies between 0 and")
    print("  lam_2, and it is bounded above by the smallest Cholesky pivot, f(beta).")
    print("  So 3.018 is not certifiable here; what is, is a gap up to f(beta).\n")
    print(f"  {'K':>4} {'modes':>7} {'g':>7} {'verdict':>12} {'smallest pivot':>26}")
    for K in (8, 16):
        if K > maxK:
            break
        MT = T_form(K)
        idx = [i for i in range(2 * K) if i != K]
        for g in (0.5, 1.0, 1.5, 3.0):
            M2 = [[MT[i][j] - (arb(g) if i == j else arb(0)) for j in range(2 * K)]
                  for i in range(2 * K)]
            ok, bp, sm = cholesky_certifies(M2, idx)
            # g = 3 is expected to FAIL: interlacing caps the deflated least eigenvalue
            # by the smallest pivot f(beta) = 1.5389, so 3 is out of reach.  Counting it
            # as an error would be counting a documented negative control as a defect.
            expect = g < 1.6
            bad += (ok != expect)
            print(f"  {K:4d} {2*K:7d} {g:7.2f} {'CERTIFIED' if ok else 'fails, expected':>15} "
                  f"{str(sm if ok else bp)[:26]:>26}")
    print("\n  So -delta^2|T| >= 1.5 I on the deflated span of the first 32 modes, in ball")
    print("  arithmetic: coercivity with an explicit constant, not merely positivity.")
    print("  g = 3 fails with pivot exactly f(beta) - 3, confirming the interlacing bound.\n")

    print("  the tail: Gershgorin does NOT close it\n")
    import math

    def _ssf(a, b, T):
        if a == b:
            return T / 2 - math.sin(2 * a * T) / (4 * a)
        return 0.5 * (math.sin((a - b) * T) / (a - b) - math.sin((a + b) * T) / (a + b))

    def _ccf(a, b, T):
        if a == b:
            return T / 2 + math.sin(2 * a * T) / (4 * a)
        return 0.5 * (math.sin((a - b) * T) / (a - b) + math.sin((a + b) * T) / (a + b))

    def _scf(a, b, T):
        if a == b:
            return (1 - math.cos(2 * a * T)) / (4 * a)
        return 0.5 * ((1 - math.cos((a - b) * T)) / (a - b)
                      + (1 - math.cos((a + b) * T)) / (a + b))

    def _ipf(p, q, T):
        (c1, n1, k1), (c2, n2, k2) = p, q
        v = (_ssf(n1, n2, T) if (k1 == 's' and k2 == 's') else
             _ccf(n1, n2, T) if (k1 == 'c' and k2 == 'c') else
             _scf(n1, n2, T) if k1 == 's' else _scf(n2, n1, T))
        return c1 * c2 * v

    def _pairf(i, K):
        n = freq(i, K)
        return ((n, n, 's'), (1.0, n, 'c')) if i < K else ((1.0, n, 's'), (n, n, 'c'))

    # float closed form: O(N^2) memory.  The earlier quadrature route built an N x N x M
    # array -- 8.7 GB at 52 modes and 4e5 points -- which is why this uses closed forms.
    Kg = 64
    P2f, bf = math.pi / 2, 0.2896538208173209
    T2f = P2f - bf
    N = 2 * Kg
    A = [[0.0] * N for _ in range(N)]
    for i in range(N):
        a1i, a2i = _pairf(i, Kg)
        for j in range(i, N):
            a1j, a2j = _pairf(j, Kg)
            v = 2 * _ipf(a2i, a2j, T2f) - 2 * _ipf(a1i, a1j, bf)
            if freq(i, Kg) == freq(j, Kg) and ((i < Kg) == (j < Kg)):
                v += (math.pi / 2) * (freq(i, Kg) ** 2 - 1)
                if i < Kg:
                    v += (math.pi / 2) * (freq(i, Kg) ** 2 - 1)
            A[i][j] = A[j][i] = v
    print(f"  {'n':>5} {'diagonal':>12} {'row radius':>12} {'ratio':>8}")
    worst = 0.0
    for i in (5, 10, 20, 40):
        n = freq(i, Kg)
        rad = sum(abs(A[i][j]) for j in range(N)) - abs(A[i][i])
        r = rad / A[i][i]
        worst = max(worst, r)
        print(f"  {n:5d} {A[i][i]:12.2f} {rad:12.2f} {r:8.3f}")
    dom = worst < 1.0
    print(f"\n  diagonally dominant? {dom}.  The ratios exceed 1, so the off-diagonal mass is")
    print("  comparable to the diagonal and Gershgorin cannot close the tail.  What holds is")
    print("  that lam_min stays at machine zero out to 128 modes; the tail needs a Schur")
    print("  complement or the S-relation, not a diagonal-dominance argument.\n")

    print(f"  {'ALL CHECKS PASS' if not bad else f'{bad} CHECK(S) FAILED'}")
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
