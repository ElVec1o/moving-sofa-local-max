"""ambi_signstruct.py — does admissibility force the ordered/anchored sign structure?

WHY THIS MATTERS.  The concavity theorem of the note covers every ORDERED ANCHORED cell,
and rem:conc exhibits a sign pattern on which the second variation is POSITIVE:
E1 = E2 = [0.4, 1.2], unanchored, with sup (1/2) d2Q/||eta||^2 = +0.4123.  So concavity is
not merely unproved off the anchored cells, it is false there.  That is only an obstruction
to the global theorem if some admissible cap realises such a pattern.

WHAT IS PROVED, AND WHERE.  prop:anchor and lean/MovingSofa/Anchor.lean prove

    (RC) + ordered + arms not simultaneously zero  ==>  anchored.

This script does NOT re-prove that.  It does two other things: it REGRESSION-TESTS the
theorem (rule I11 -- a proof that disagrees with a sampler is one of them wrong), and it
tests the one direction that is NOT proved, namely whether (RC) also forces ORDEREDNESS.
That remains a CONJECTURE and is labelled as such in the note.

THE ARMS.  With p(t) = H(t) and q(t) = H(t + pi/2) on [0, pi/2],

    alpha_1(t) = q(t) - 1 - p'(t) ,        alpha_2(t) = p(t) - 1 + q'(t) ,

which is the differentiated form of the note's dalpha_1 = eta(t+pi/2) - eta'(t) and
dalpha_2 = eta(t) + eta'(t+pi/2).  E1 = {alpha_1 < 0}, E2 = {alpha_2 > 0}; ordered means
E1 subset E2, anchored means E2 is an initial segment [0, tau).

SAMPLING (RC) BY CONSTRUCTION, NOT BY REJECTION.  (RC) says the absolutely continuous part
of H + H'' is at most 1 -- the radius of curvature never exceeds that of the unit circle.
So rather than sample H and reject, sample the CURVATURE RADIUS r = H + H'' in [0, 1]
directly and integrate,

    H(x) = H(0) cos x + H'(0) sin x + int_0^x r(s) sin(x - s) ds ,

which satisfies (RC) exactly, by construction, for every r in the box.  This reaches the
whole (RC) class rather than the thin slice a rejection filter would find near a base
point, so it is a far more adversarial test: the earlier version of this experiment
perturbed Sigma and had a 6.5% acceptance rate, meaning it only ever saw caps close to
Sigma.  H'(0) = 1/2 is forced by the rho-symmetry of the cap (see the note); H(0) is a
free parameter and is swept.

NEGATIVE CONTROL (rule I12).  The same sampler with r allowed to exceed 1 -- (RC)
violated, everything else identical -- must produce ordered-but-unanchored caps.  If it
does not, the filter is not what is doing the work and the experiment says nothing.  This
control is the whole point: a positive result with a broken control is worthless.

Rule 7: everything here is floating point and is EVIDENCE, never proof.  The proved
statement is prop:anchor; this file supports the conjectured converse and guards the proof.

Usage: python3 ambi_signstruct.py [nsamples]
"""
from __future__ import annotations
import sys
import numpy as np

NGRID = 2001          # grid on [0, pi], so [0, pi/2] and the shift by pi/2 both land on it
HALF = (NGRID - 1) // 2


def build_H(r: np.ndarray, H0: float, x: np.ndarray,
            atom: float = 0.0) -> tuple[np.ndarray, np.ndarray]:
    """H and H' on the grid from the curvature radius r, via the variation-of-constants
    solution of H'' + H = r + atom * delta(x - pi/2) with H(0) = H0 and H'(0) = 1/2.

    THE ATOM IS NOT OPTIONAL.  (RC) bounds only the ABSOLUTELY CONTINUOUS part of H + H''
    and explicitly permits atoms at +-pi/2; an atom of mass a there makes H' jump by +a
    across pi/2.  Since alpha_2(t) = H(t) - 1 + H'(t + pi/2) reads H' on [pi/2, pi], the
    atom sits exactly inside it.  Dropping it (as the first version of this script did)
    depresses alpha_2 by the atom mass, drives E2 empty in every sample, and makes the
    whole experiment vacuous -- 100% of caps came back "anchored" only because there was
    nothing to anchor.  Rule I6: a 100/0 split is a sampler diagnosis, not a result."""
    dx = x[1] - x[0]
    # int_0^x r(s) sin(x-s) ds  and its derivative int_0^x r(s) cos(x-s) ds, both by the
    # trapezoid rule on the same grid (the kernel vanishes at s = x, so this is clean)
    S, C = np.zeros_like(x), np.zeros_like(x)
    rs, rc = r * np.sin(x), r * np.cos(x)
    cs = np.concatenate([[0.0], np.cumsum((rs[1:] + rs[:-1]) * dx / 2)])
    cc = np.concatenate([[0.0], np.cumsum((rc[1:] + rc[:-1]) * dx / 2)])
    S = np.sin(x) * cc - np.cos(x) * cs          # int r(s) sin(x-s) ds
    C = np.cos(x) * cc + np.sin(x) * cs          # its x-derivative
    H = H0 * np.cos(x) + 0.5 * np.sin(x) + S
    Hp = -H0 * np.sin(x) + 0.5 * np.cos(x) + C
    if atom:
        past = x >= np.pi / 2
        H = H + np.where(past, atom * np.sin(x - np.pi / 2), 0.0)
        Hp = Hp + np.where(past, atom * np.cos(x - np.pi / 2), 0.0)
    return H, Hp


def admissible_profile(prof: np.ndarray, x: np.ndarray, hi: float) -> np.ndarray | None:
    """Bend the radius profile onto the two forced boundary conditions.

    THIS IS CODIMENSION 2 AND WAS THE WHOLE PROBLEM.  The cap is symmetric under the
    REFLECTION rho(x, y) = (x, 1 - y) -- not a rotation; the note's leftmost point is
    rho-FIXED, which a rotation could not do -- so H(theta) = sin theta + H(-theta).
    Differentiating at 0 and pi forces H'(0) = 1/2 and H'(pi) = -1/2.  Integrating
    H'' + H = r from H'(0) = 1/2,

        H'(pi) = -1/2 - int_0^pi r cos ,       H(pi/2) = 1/2 + int_0^(pi/2) r cos ,

    and H(pi/2) = 1 is forced too (it is what makes alpha_1(0) = -1/2).  So

        (A)  int_0^(pi/2) r(s) cos s ds =  1/2 ,
        (B)  int_(pi/2)^pi r(s) cos s ds = -1/2 .

    Neither involves H(0): the H(0) terms cancel identically out of BOTH arms, so H(0) is
    not a parameter of this problem at all.  Sigma satisfies (A) and (B) to the printed
    precision; r == 1/2 satisfies both exactly, so the constraint set has interior inside
    the (RC) box.

    Adding lam * cos separately on each half before clamping to [0, hi] moves each moment
    monotonically and independently, so two bisections land on both constraints exactly
    while keeping r in [0, hi] -- (RC) still holds by construction, not by rejection."""
    dx = x[1] - x[0]
    c = np.cos(x)
    L, R = x < np.pi / 2, x >= np.pi / 2
    out = prof.copy()
    for mask, target in ((L, 0.5), (R, -0.5)):
        def moment(lam: float) -> float:
            r = np.clip(prof + lam * c, 0.0, hi)
            return float(np.trapezoid((r * c)[mask], dx=dx))
        lo, up = -40.0, 40.0
        if moment(lo) > target or moment(up) < target:
            return None                  # unreachable from this profile inside the box
        for _ in range(90):
            mid = (lo + up) / 2
            if moment(mid) < target:
                lo = mid
            else:
                up = mid
        out[mask] = np.clip(prof + (lo + up) / 2 * c, 0.0, hi)[mask]
    return out


def classify(H: np.ndarray, Hp: np.ndarray) -> tuple[bool, bool, bool]:
    """(ordered, anchored, substantive) for the arms on [0, pi/2].

    `substantive` is the rule I6 gate: both sign sets must be NONEMPTY.  If E2 is empty
    then "anchored" holds for nothing and the sample is evidence for nothing; counting
    such samples as successes is what made the first run of this script report a
    meaningless 100%.  Vacuous samples are tallied separately and never scored."""
    p, pp = H[:HALF + 1], Hp[:HALF + 1]
    q, qp = H[HALF:], Hp[HALF:]
    a1 = q - 1.0 - pp
    a2 = p - 1.0 + qp
    E1, E2 = a1 < 0, a2 > 0
    ordered = bool(np.all(~E1 | E2))                    # E1 subset E2
    # anchored: E2 is an initial segment, i.e. no True after the first False
    if not E2.any():
        anchored = True
    else:
        first_false = np.argmax(~E2) if (~E2).any() else len(E2)
        anchored = bool(not E2[first_false:].any())
    return ordered, anchored, bool(E1.any() and E2.any())


def sample(n: int, rc: bool, seed: int) -> dict[str, int]:
    """n random caps; rc=True keeps the curvature radius in [0,1] ((RC) holds), rc=False
    lets it reach 3 ((RC) violated).  Everything else is identical."""
    rng = np.random.default_rng(seed)
    x = np.linspace(0.0, np.pi, NGRID)
    tally = {"ord_anch": 0, "ord_unanch": 0, "unord_anch": 0, "unord_unanch": 0,
             "vacuous": 0}
    hi = 1.0 if rc else 3.0
    for _ in range(n):
        # a random radius profile: a few Fourier modes with general phases, squashed into
        # [0, hi] by a smooth clamp so the bound is respected exactly
        k = rng.integers(1, 6)
        prof = sum(rng.uniform(-1, 1) * np.sin(rng.integers(1, 7) * x + rng.uniform(0, 2 * np.pi))
                   for _ in range(k))
        r = hi * (0.5 + 0.5 * np.tanh(prof / max(1e-9, np.abs(prof).max()) * 1.5))
        r = admissible_profile(r, x, hi)
        if r is None:
            tally["vacuous"] += 1
            continue
        # H(0) cancels out of both arms, so its value is irrelevant; Sigma has H(0) = 1
        H, Hp = build_H(r, 1.0, x, atom=rng.uniform(0.0, 2.0))
        o, a, sub = classify(H, Hp)
        if not sub:
            tally["vacuous"] += 1
            continue
        tally["ord_anch" if o and a else "ord_unanch" if o else
              "unord_anch" if a else "unord_unanch"] += 1
    return tally


def main() -> int:
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    print(__doc__.split("Usage")[0])
    print(f"{n} caps per arm, curvature radius sampled directly so (RC) holds by "
          f"construction\n")
    rows = []
    for label, rc, seed in (("(RC) HOLDS   r <= 1", True, 20260802),
                            ("(RC) VIOLATED r <= 3", False, 20260803)):
        t = sample(n, rc, seed)
        rows.append((label, t))
        tot = max(1, sum(t.values()) - t["vacuous"])
        print(f"  {label}   ({tot} substantive of {n}; {t['vacuous']} vacuous, "
              f"E1 or E2 empty, not scored)")
        print(f"    ordered & anchored     {t['ord_anch']:6d}  ({100*t['ord_anch']/tot:5.1f}%)")
        print(f"    ordered & UNANCHORED   {t['ord_unanch']:6d}  "
              f"({100*t['ord_unanch']/tot:5.1f}%)   <- the rem:conc pattern")
        print(f"    unordered & anchored   {t['unord_anch']:6d}  ({100*t['unord_anch']/tot:5.1f}%)")
        print(f"    unordered & unanchored {t['unord_unanch']:6d}  "
              f"({100*t['unord_unanch']/tot:5.1f}%)\n")

    rc_t, no_t = rows[0][1], rows[1][1]
    # R1 (regression, rule I11): prop:anchor forbids ordered-but-unanchored under (RC).
    reg_ok = rc_t["ord_unanch"] == 0
    # R2 (negative control, rule I12): without (RC) the pattern must appear, else the
    # filter is not what is doing the work.
    ctl_ok = no_t["ord_unanch"] > 0
    # R3 (non-vacuity, rule I6): the (RC) arm must contain substantive samples at all.
    sub_ok = (sum(rc_t.values()) - rc_t["vacuous"]) > 0
    print("  R1 regression (I11): prop:anchor forbids ordered-but-unanchored under (RC);")
    print(f"     the sampler found {rc_t['ord_unanch']} such caps -> "
          f"{'AGREES' if reg_ok else '*** DISAGREES WITH THE PROOF ***'}")
    print("  R2 negative control (I12): dropping (RC) must let the pattern appear;")
    print(f"     it appears {no_t['ord_unanch']} times -> "
          f"{'CONTROL PASSES' if ctl_ok else '*** CONTROL FAILS, (RC) IS NOT THE CAUSE ***'}")

    ordered_rate = (100 * (rc_t["ord_anch"] + rc_t["ord_unanch"])
                    / max(1, sum(rc_t.values()) - rc_t["vacuous"]))
    print(f"\n  THE OPEN DIRECTION.  Of the substantive (RC) caps, {ordered_rate:.1f}% are ordered.")
    if ordered_rate < 99.9:
        print("  Orderedness is NOT forced by (RC) alone at this sampling width: the "
              "sampler")
        print("  reaches unordered (RC) caps.  So prop:anchor's orderedness hypothesis "
              "needs")
        print("  a further admissibility input (the cap must bound an actual sofa), and "
              "the")
        print("  converse stays CONJECTURE.  Reported as measured, not as hoped for.")
    else:
        print("  No unordered (RC) cap was found, which is consistent with -- but does "
              "not")
        print("  prove -- the conjecture that admissibility forces orderedness.")
    print(f"  R3 non-vacuity (I6): the (RC) arm must contain caps with BOTH sign sets")
    print(f"     nonempty; it contains {sum(rc_t.values()) - rc_t['vacuous']} -> "
          f"{'SUBSTANTIVE' if sub_ok else '*** VACUOUS, THE RUN PROVES NOTHING ***'}")
    return 0 if (reg_ok and ctl_ok and sub_ok) else 1


if __name__ == "__main__":
    sys.exit(main())
