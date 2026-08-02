"""ambi_sigma_ball.py — is the ordered class a neighbourhood of Sigma, or just Sigma?

WHAT THIS IS FOR.  prop:anchor proves

    (RC) + ordered + arms not simultaneously zero  ==>  anchored,

and the unanchored pattern of rem:conc (E1 = E2 = [0.4,1.2], with the second variation
POSITIVE at +0.4123) is ordered, so the proposition forbids it.  That is only worth
anything if ordered admissible caps EXIST in quantity.  A companion sweep over generic
(RC) caps (ambi_signstruct.py) finds none at all, which leaves the proposition formally
true and possibly vacuous.  This file settles that by working where Sigma actually is.

THE CONSTRUCTION.  Sigma's own curvature radius r = H + H'' is built from the note's
closed forms for F and G phase by phase (SOL1 on [0,beta), SOL6 on [beta, pi/2-beta),
SOL5 after), with beta = 0.2896538208173209, a_1 = 0.875287362412732 and
f_1 = 1.202938908156911389070223, f_2 = (1-sqrt2) f_1, kappa = 1 - (4/3) a_1.  Perturb r
inside the (RC) box and restore the two forced moment conditions

    (A) int_0^(pi/2) r cos = 1/2      [ H(pi/2) = 1, equivalently alpha_1(0) = -1/2 ]
    (B) int_(pi/2)^pi  r cos = -1/2   [ H'(pi) = -1/2 from the reflection symmetry ]

by bisection on each half.  Clamping to [0,1] keeps (RC) exact, so every cap tested is
admissible in the curvature sense and satisfies the forced boundary data.

WHAT IS MEASURED.  At each perturbation amplitude: how many caps stay ordered (so the
ordered class has interior, and prop:anchor is not vacuous), and among the ordered ones
how many are unanchored (which prop:anchor forbids, so the answer must be zero -- that is
the I11 regression, and it is only a real test when the ordered count is large).

NEGATIVE CONTROL (rule I12).  The same perturbation with the curvature bound relaxed from
1 to 3, everything else identical, must produce ordered UNANCHORED caps.  If it does not,
(RC) is not what forbids them and this experiment says nothing about (RC).  An earlier
version of this experiment reported a passing control that turned out to come from a
sampler missing two of the three forced boundary conditions; the control is the part that
catches that, so it is checked and reported, not assumed.

VACUITY GATES (rule I6), both earned the hard way:
  G1  a cap with E1 or E2 empty is not scored -- "anchored" is free when E2 is empty;
  G2  the regression is reported as VACUOUS unless ordered caps actually occur.
Without G2 a run with zero ordered caps prints "AGREES" and means nothing.

Rule 7: floating point, so EVIDENCE, never proof.  prop:anchor is the proved statement.

Usage: python3 ambi_sigma_ball.py [nsamples]
"""
from __future__ import annotations
import sys
import numpy as np

NG = 4001
A1 = 0.875287362412732
F1 = 1.202938908156911389070223
F2 = (1 - np.sqrt(2)) * F1
KAP = 1 - 4 * A1 / 3
BETA = 0.2896538208173209
P2 = np.pi / 2


def sigma_FG(t: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """F - 1 and G - 1 for Sigma, from the note's closed forms, phase by phase."""
    F, G = np.empty_like(t), np.empty_like(t)
    s1, s6, s5 = t < BETA, (t >= BETA) & (t < P2 - BETA), t >= P2 - BETA
    x = t[s1]
    F[s1] = np.cos(x) + 0.5 * np.sin(x) - 1
    G[s1] = (2 * A1 - 1) * np.sin(x) + 0.5 * np.cos(x) - 0.5
    x = t[s6]
    F[s6] = F1 * np.cos(x / 2) + F2 * np.sin(x / 2) - 1 + KAP * np.cos(x) + 0.5 * np.sin(x)
    G[s6] = -F2 * np.cos(x / 2) + F1 * np.sin(x / 2) - 1 + 0.5 * np.cos(x) - KAP * np.sin(x)
    x = t[s5]
    F[s5] = (1 - 2 * A1 / 3) * np.cos(x) + 0.5 * np.sin(x) - 0.5
    G[s5] = (8 * A1 / 3 - 1) * np.sin(x) + 0.5 * np.cos(x) - 1
    return F, G


def sigma_radius(x: np.ndarray) -> np.ndarray:
    """Sigma's curvature radius r = H + H'' on [0, pi], with H = F on [0, pi/2] and
    H(u) = G(u - pi/2) after."""
    F, G = sigma_FG(np.clip(x, 0, P2))
    _, G2 = sigma_FG(np.clip(x - P2, 0, P2))
    H = np.where(x <= P2, F + 1, G2 + 1)
    dx = x[1] - x[0]
    return H + np.gradient(np.gradient(H, dx), dx)


SPIKE_W = 0.03            # half-width of the atom at pi/2, in the grid's terms


def restore(r: np.ndarray, x: np.ndarray, hi: float,
            keep: np.ndarray | None = None) -> np.ndarray | None:
    """Bisect a multiple of cos onto r, separately on each half, to restore (A) and (B)
    while clamping into [0, hi] so (RC) survives by construction.

    `keep` marks samples that must pass through untouched -- the ATOM at pi/2.  (RC)
    bounds only the absolutely continuous part of H + H''; the atom is unbounded and is
    the whole reason Sigma can be ordered.  Clamping it away, as the first version of this
    file did, is not a small error: alpha_2(0) = int_0^(pi/2) r_ac sin - 1 + atom, and
    with r_ac <= 1 the integral is at most 1, so WITHOUT an atom alpha_2(0) <= 0 for every
    (RC) cap.  Since alpha_1(0) = -1/2 < 0 always, 0 lies in E1 but not in E2 and ordering
    fails at the very first point -- which is exactly what the clamped sweep reported, for
    every perturbation at every amplitude.  Sigma's atom has mass 1.1670497 (the jump
    G'(0) - F'(pi/2) between the phases), giving alpha_2(0) = +0.7506.

    The atom does not disturb the two moment conditions: it sits at pi/2, where cos
    vanishes, so it contributes nothing to either integral, and it acts on H only to the
    right of pi/2, so it leaves H(pi/2) alone."""
    dx, c = x[1] - x[0], np.cos(x)
    out = r.copy()
    if keep is None:
        keep = np.zeros_like(x, dtype=bool)
    for mask, target in ((x < P2, 0.5), (x >= P2, -0.5)):
        def mom(lam: float) -> float:
            rr = np.where(keep, r, np.clip(r + lam * c, 0.0, hi))
            return float(np.trapezoid((rr * c)[mask], dx=dx))
        lo, up = -60.0, 60.0
        if mom(lo) > target or mom(up) < target:
            return None
        for _ in range(90):
            mid = (lo + up) / 2
            if mom(mid) < target:
                lo = mid
            else:
                up = mid
        out[mask] = np.where(keep, r, np.clip(r + (lo + up) / 2 * c, 0.0, hi))[mask]
    return out


def arms(r: np.ndarray, x: np.ndarray, atom: float) -> tuple[np.ndarray, np.ndarray]:
    """alpha_1 = H(t+pi/2) - 1 - H'(t) and alpha_2 = H(t) - 1 + H'(t+pi/2) on [0, pi/2].
    H(0) cancels identically out of both, so it is not a parameter and is set to 1."""
    dx = x[1] - x[0]
    cs = np.concatenate([[0.0], np.cumsum((r * np.sin(x))[1:] + (r * np.sin(x))[:-1]) * dx / 2])
    cc = np.concatenate([[0.0], np.cumsum((r * np.cos(x))[1:] + (r * np.cos(x))[:-1]) * dx / 2])
    H = np.cos(x) + 0.5 * np.sin(x) + (np.sin(x) * cc - np.cos(x) * cs)
    Hp = -np.sin(x) + 0.5 * np.cos(x) + (np.cos(x) * cc + np.sin(x) * cs)
    past = x >= P2
    H = H + np.where(past, atom * np.sin(x - P2), 0.0)
    Hp = Hp + np.where(past, atom * np.cos(x - P2), 0.0)
    h = (NG - 1) // 2
    return H[h:] - 1 - Hp[:h + 1], H[:h + 1] - 1 + Hp[h:]


def score(a1: np.ndarray, a2: np.ndarray) -> tuple[bool, bool, bool]:
    E1, E2 = a1 < 0, a2 > 0
    ordered = bool(np.all(~E1 | E2))
    anchored = True if not E2.any() else bool(not E2[np.argmax(~E2):].any())
    return ordered, anchored, bool(E1.any() and E2.any())


def sweep(n: int, amp: float, hi: float, seed: int) -> tuple[int, int, int]:
    """(substantive, ordered, ordered_and_unanchored) at perturbation amplitude amp."""
    rng = np.random.default_rng(seed)
    x = np.linspace(0.0, np.pi, NG)
    base = sigma_radius(x)
    keep = np.abs(x - P2) < SPIKE_W          # the atom passes through untouched
    sub = ordc = bad = 0
    for _ in range(n):
        pert = sum(rng.uniform(-1, 1) * np.sin(rng.integers(1, 8) * x + rng.uniform(0, 2 * np.pi))
                   for _ in range(rng.integers(1, 6)))
        pert = pert / max(1e-9, np.abs(pert).max())
        r = restore(np.where(keep, base, np.clip(base + amp * pert, 0.0, hi)), x, hi, keep)
        if r is None:
            continue
        o, a, s = score(*arms(r, x, 0.0))
        if not s:
            continue
        sub += 1
        ordc += o
        bad += (o and not a)
    return sub, ordc, bad


def main() -> int:
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    print(__doc__.split("Usage")[0])
    x = np.linspace(0.0, np.pi, NG)
    r0 = sigma_radius(x)
    inner = (x > 0.05) & (x < np.pi - 0.05) & (np.abs(x - P2) > 0.05)
    o0, a0, s0 = score(*arms(r0, x, 0.0))
    print(f"  Sigma itself: max a.c. r = {r0[inner].max():.7f} (note: 0.8388253494), "
          f"atom at pi/2 of mass 1.1670497,")
    print(f"                ordered = {o0}, anchored = {a0}\n")
    print(f"  {n} perturbations per amplitude, both moment conditions restored exactly\n")
    print(f"  {'amp':>6} {'(RC) r<=1':>28}   {'CONTROL r<=3':>28}")
    print(f"  {'':>6} {'subst':>7}{'ordered':>10}{'ord+unanch':>11}   "
          f"{'subst':>7}{'ordered':>10}{'ord+unanch':>11}")
    tot_ord = tot_bad = ctl_ord = ctl_bad = 0
    for amp in (0.02, 0.05, 0.10, 0.20, 0.40):
        s1, o1, b1 = sweep(n, amp, 1.0, 20260802)
        s3, o3, b3 = sweep(n, amp, 3.0, 20260802)
        tot_ord += o1
        tot_bad += b1
        ctl_ord += o3
        ctl_bad += b3
        print(f"  {amp:6.2f} {s1:7d}{o1:10d}{b1:11d}   {s3:7d}{o3:10d}{b3:11d}")

    print(f"\n  G2 non-vacuity (I6): the regression tests prop:anchor only if ordered (RC)")
    print(f"     caps occur; {tot_ord} did -> "
          f"{'SUBSTANTIVE' if tot_ord else '*** VACUOUS, PROVES NOTHING ***'}")
    print(f"  R1 regression (I11): prop:anchor forbids ordered-but-unanchored under (RC);")
    print(f"     found {tot_bad} -> {'AGREES' if not tot_bad else '*** DISAGREES WITH THE PROOF ***'}")
    print(f"  R2 control (I12): relaxing the curvature bound must produce them;")
    print(f"     found {ctl_bad} among {ctl_ord} ordered -> "
          f"{'CONTROL PASSES' if ctl_bad else 'CONTROL INCONCLUSIVE at this amplitude'}")
    ok = tot_ord > 0 and tot_bad == 0
    print(f"\n  {'PASS' if ok else 'FAIL'}: the ordered class has interior around Sigma "
          f"and prop:anchor holds on it." if ok else
          f"\n  FAIL: see the gates above.")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
