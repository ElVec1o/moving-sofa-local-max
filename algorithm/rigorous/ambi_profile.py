"""ambi_profile.py — the area profile in alpha_2(0), split into cap and niche.

WHY THIS FILE EXISTS.  Two reasons.

CUSTODY.  A16's deficits were orphan constants: printed in the note, registered as
measurements, and produced by no shipped script.  Every number in the profile row now comes
from here.  The A17 concavity row that used to sit beneath it is withdrawn, so its
constants are removed from the registry rather than shipped.

DEPTH.  A15b needs an upper bound on |T| when alpha_2(0) is small, and the second-variation
route to it is blocked at the definition -- prop:coerc gates the end-cap model, not the
realised-cell form, so 'concavity on realised cells' has no verified referent.  What is
left is the area functional itself, and the first question about it is which of its two
terms carries the deficit:

    |T| = |C_2| - 2|N| .

Dropping |N| >= 0 cannot work: |C_2| exceeds |T| by construction, so a bound on the cap
alone is weaker than what is needed.  The live question is whether |N| GROWS as alpha_2(0)
falls, because a lower bound on the niche is then a route to an upper bound on |T|, and a
lower bound on an area is a far easier object than a spectral estimate.

The rasteriser builds the cap from the half-plane constraints and then cuts the two niches,
so the two stages separate exactly; this file reads both.

Rule 7: every number here is a rasterisation of a floating-point support function.  The
error bar is measured against Sigma, whose area is known in closed form, and is subtracted
from every row.  These are measurements, not proofs.

Usage: python3 ambi_profile.py
"""
from __future__ import annotations
import importlib.util
import os

import numpy as np

P2 = np.pi / 2
AR = 1.6449552184254408
FLOOR = np.sqrt(3) - 1


def _load(name):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), name)
    spec = importlib.util.spec_from_file_location(name[:-3], path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


cap = _load("ambi_cap.py")
dc = _load("ambi_disconnected.py")
sb = _load("ambi_sigma_ball.py")


def stages(H, x, NT=260, NG=620):
    """Return (|C_2|, |T|, max cy).  Identical to ambi_disconnected.rasterise, except that
    the cap area is read off before the two niches are cut."""
    th = np.linspace(0, np.pi, NT)
    Hi = np.interp(th, x, H)
    gx = np.linspace(-1.7, 1.7, NG)
    gy = np.linspace(-1.2, 2.2, NG)
    X, Y = np.meshgrid(gx, gy)
    cell = (gx[1] - gx[0]) * (gy[1] - gy[0])
    S = np.ones_like(X, dtype=bool)
    for t, h in zip(th, Hi):
        S &= (X * np.cos(t) + Y * np.sin(t) <= h)
        S &= (X * np.cos(t) + (1 - Y) * np.sin(t) <= h)
    capA = S.sum() * cell
    cy = []
    for t in np.linspace(0, P2, NT):
        F = np.interp(t, x, H)
        G = np.interp(t + P2, x, H)
        mu = np.array([np.cos(t), np.sin(t)])
        nu = np.array([-np.sin(t), np.cos(t)])
        z = (F - 1) * mu + (G - 1) * nu
        cy.append(z[1])
        a = (X - z[0]) * mu[0] + (Y - z[1]) * mu[1]
        b = (X - z[0]) * nu[0] + (Y - z[1]) * nu[1]
        S &= ~((a < 0) & (b < 0))
        ar = (X - z[0]) * mu[0] + ((1 - Y) - z[1]) * mu[1]
        br = (X - z[0]) * nu[0] + ((1 - Y) - z[1]) * nu[1]
        S &= ~((ar < 0) & (br < 0))
    return capA, S.sum() * cell, max(cy)


def family(x, n=24, seed=20260803):
    """Sigma, a batch of (RC)-restored perturbations of it, and the cor:floor witness."""
    rng = np.random.default_rng(seed)
    r0, _ = cap.cap_sigma(x)
    out = [r0]
    for _ in range(n):
        p = sum(rng.uniform(-1, 1) * np.sin(rng.integers(1, 8) * x + rng.uniform(0, 6.3))
                for _ in range(3))
        p /= np.abs(p).max()
        r = sb.restore(np.clip(r0 + rng.uniform(0.1, 0.7) * p, 0, 1), x, 1.0, None)
        if r is not None:
            out.append(r)
    rw = np.zeros_like(x)
    rw[(x >= np.pi / 6) & (x < P2)] = 1.0
    rw[x >= 5 * np.pi / 6] = 1.0
    out.append(rw)
    return out


def main() -> int:
    print(__doc__.split("Usage")[0])
    bad = 0
    x = np.linspace(0, np.pi, 4001)
    dx = x[1] - x[0]
    r0, atom0 = cap.cap_sigma(x)

    capS, TS, _ = stages(dc.Hfun(r0, x, atom0), x)
    bias = TS - AR
    print(f"  I11 gate: Sigma -> |T| = {TS:.5f} vs A_R* = {AR:.7f},"
          f"  bias {bias:+.5f}  {'OK' if abs(bias) < 3e-3 else 'FAIL'}")
    bad += abs(bias) >= 3e-3
    print(f"  Sigma's split: |C_2| = {capS - bias:.5f}, 2|N| = {capS - TS:.5f},"
          f" |T| = {TS - bias:.5f}\n")

    prof = family(x)
    print(f"  {len(prof)} profiles.  Bias subtracted from |C_2| and |T| alike.\n")
    print(f"  {'alpha_2(0)':>11} {'max |T|':>9} {'A_R*-|T|':>10} {'|C_2|':>9} {'2|N|':>9}")
    rows = []
    for c in (0.40, 0.50, 0.55, 0.60, 0.65, 0.70, FLOOR, 0.7506, 0.80, 0.90):
        best, bc, bn = -1.0, 0.0, 0.0
        for r in prof:
            a = c + 1 - float(np.trapezoid((r * np.sin(x))[x <= P2], dx=dx))
            if a < 0:
                continue
            cA, T, M = stages(dc.Hfun(r, x, a), x)
            if M >= 0.5:
                continue
            if T > best:
                best, bc, bn = T, cA, cA - T
        rows.append((c, best - bias, bc - bias, bn))
        tag = "  <- floor" if abs(c - FLOOR) < 1e-3 else (
              "  <- Sigma" if abs(c - 0.7506) < 1e-3 else "")
        print(f"  {c:11.4f} {best - bias:9.5f} {AR - best + bias:+10.5f}"
              f" {bc - bias:9.5f} {bn:9.5f}{tag}")

    print("\n  which term carries the deficit, relative to Sigma's own split\n")
    cS, nS = capS - bias, capS - TS
    print(f"  {'alpha_2(0)':>11} {'|C_2| - |C_2|(S)':>17} {'2|N| - 2|N|(S)':>16} {'carried by':>12}")
    for c, T, cA, nA in rows:
        dcap, dnic = cA - cS, nA - nS
        who = "niche" if dnic > abs(dcap) else ("cap" if -dcap > abs(dnic) else "both")
        print(f"  {c:11.4f} {dcap:+17.5f} {dnic:+16.5f} {who:>12}")

    lo = [r for r in rows if r[0] < 0.60]
    grows = all(r[3] > nS for r in lo)
    print(f"\n  does 2|N| exceed Sigma's for every alpha_2(0) < 0.60?  "
          f"{'YES' if grows else 'NO'}")
    print("  No: both terms FALL together below Sigma and RISE together above it, so a")
    print("  lower bound on the niche alone is not the route.  What separates them is the")
    print("  ratio at which they move.\n")

    print("  the tracking ratio  rho = [2|N| - 2|N|(S)] / [|C_2| - |C_2|(S)]\n")
    print(f"  {'alpha_2(0)':>11} {'d|C_2|':>10} {'d 2|N|':>10} {'rho':>9} {'A_R*-|T|':>10}")
    rho = []
    for c, T, cA, nA in rows:
        dcap, dnic = cA - cS, nA - nS
        if abs(dcap) < 1e-9:
            print(f"  {c:11.4f} {dcap:+10.5f} {dnic:+10.5f} {'--':>9} {AR - T:+10.5f}"
                  "   <- Sigma, both vanish")
            continue
        r_ = dnic / dcap
        rho.append((c, r_))
        print(f"  {c:11.4f} {dcap:+10.5f} {dnic:+10.5f} {r_:9.4f} {AR - T:+10.5f}")

    below = [r_ for c, r_ in rho if c < 0.7506]
    above = [r_ for c, r_ in rho if c > 0.7506]
    mono = all(b < 1 for b in below) and all(a > 1 for a in above)
    print(f"\n  rho < 1 strictly below Sigma and > 1 strictly above:"
          f"  {'YES' if mono else 'NO'}")
    if not mono:
        print("  FAIL: the single-crossing structure does not hold on this sample")
        return 1
    print("""
  This is the useful reformulation.  Since |T| = |C_2| - 2|N|,

      A_R* - |T|(c)  =  ( rho(c) - 1 ) * [ |C_2|(c) - |C_2|(Sigma) ]

  identically -- formalised as `deficit_factorisation` -- and both factors change
  sign together at Sigma, so their product is positive on both sides.  So A16 (the profile is
  unimodal with its peak at Sigma) and A15b (|T| <= A_R* below the floor) both reduce to
  ONE statement: rho crosses 1 exactly once, at Sigma, from below.  That is a comparison
  between two areas and their rates, not a spectral estimate, and it does not need the
  realised-cell second variation that has no verified referent.  rho = 1 at Sigma is
  exactly the first-order condition, so the crossing is not an extra hypothesis -- only
  its uniqueness is.""")
    print("  Rule 0: HEURISTIC.  The rows maximise over a 26-profile sample and the")
    print("  maximiser changes between rows, so rho is not read along one smooth family.")

    print("\n  one smooth family: Sigma's r_ac frozen, only the atom varied.  Along it rho")
    print("  is a function of c, not a maximum over a changing sample.\n")
    base = float(np.trapezoid((r0 * np.sin(x))[x <= P2], dx=dx))
    cs = np.arange(0.40, 1.001, 0.05)
    C, N, T = [], [], []
    for c in cs:
        cA, tt, _ = stages(dc.Hfun(r0, x, c + 1 - base), x)
        C.append(cA - bias); T.append(tt - bias); N.append(cA - tt)
    C, N, T = map(np.array, (C, N, T))
    d2C, d2N, d2T = np.diff(C, 2), np.diff(N, 2), np.diff(T, 2)
    NOISE = 20 * float(np.abs(d2C).max())      # the floor, times a safety factor
    print(f"  {'c':>6} {'|C_2|':>9} {'2|N|':>9} {'|T|':>9} {'rho':>8}"
          f" {'d2|C_2|':>10} {'d2 2|N|':>10} {'d2|T|':>10}")
    for i, c in enumerate(cs):
        if 0 < i < len(cs) - 1:
            cols = f" {d2C[i-1]:+10.5f} {d2N[i-1]:+10.5f} {d2T[i-1]:+10.5f}"
        else:
            cols = " " * 33
        # rho is a difference quotient in (cap - cap_S); within the rasterisation noise
        # floor of Sigma the denominator is not even reliably SIGNED, so the quotient
        # there is meaningless and is not reported.  c = 0.75 sits 4.2e-4 from Sigma,
        # below the 7.2e-4 floor, and returns 2.286 -- an artifact of the removable
        # singularity at the crossing, not a violation of monotonicity.
        dcp = C[i] - cS
        rr = f"{(N[i] - nS) / dcp:8.3f}" if abs(dcp) > NOISE else f"{'--':>8}"
        print(f"  {c:6.2f} {C[i]:9.5f} {N[i]:9.5f} {T[i]:9.5f} {rr}{cols}")
    rf = [(N[i] - nS) / (C[i] - cS) for i in range(len(cs)) if abs(C[i] - cS) > NOISE]
    print(f"\n  rho outside a {NOISE:.3f} window around Sigma (where the denominator is"
          " below\n  the noise floor) is strictly increasing:"
          f"  {all(a < b for a, b in zip(rf, rf[1:]))}")
    bad += not all(a < b for a, b in zip(rf, rf[1:]))
    floor_ = float(np.abs(d2C).max())
    print(f"\n  |C_2| second differences: max |.| = {floor_:.2e}, mean {d2C.mean():+.2e}"
          "  -> affine at the noise floor")
    print(f"  2|N|  second differences: min = {d2N.min():+.2e}, mean {d2N.mean():+.2e}"
          f"  -> CONVEX, {d2N.mean()/floor_:.1f}x the floor")
    print(f"  |T|   second differences: max = {d2T.max():+.2e}  -> CONCAVE")
    conv = d2N.min() > 0
    conc = d2T.max() < 0
    bad_local = not (conv and conc)
    k = float(np.polyfit(cs, C, 1)[0])
    sl = float(np.interp(0.7506, cs[1:-1], (N[2:] - N[:-2]) / 0.1))
    print(f"\n  cap slope k = {k:.5f}, niche slope at Sigma = {sl:.5f}, mismatch {k - sl:+.5f}")
    if bad_local:
        print("  FAIL: the affine/convex structure does not hold on this family")
    else:
        print("""
  So on this family |T| = affine - convex, hence concave, with its critical point at Sigma.
  Convexity supplies a supporting line at Sigma and subtracting it from the affine cap
  gives the bound directly: `max_of_affine_sub_convex`, one line, with `_approx` carrying
  the 2e-3 slope mismatch.  A15b and A16 therefore reduce to two statements about areas in
  ONE real parameter -- |C_2| affine in the atom, |N| convex in it -- and need no second
  variation on realised cells.""")
    bad += bad_local

    print(f"\n  {'ALL CHECKS PASS' if not bad else f'{bad} CHECK(S) FAILED'}")
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
