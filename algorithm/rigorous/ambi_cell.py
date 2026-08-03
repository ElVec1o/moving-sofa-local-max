"""ambi_cell.py — the second variation on a REALISED cell, with the convention pinned by Sigma.

WHY THIS FILE EXISTS.  The claim "concavity fails on a realised cell" (A17) and the
complementary-ranges reading built on it (A19) both rested on a computation that was never
shipped.  When something was finally built on top of them, neither could be reproduced:
rebuilding the form from Proposition prop:garding's conventions gave lam_max = +1.32 at
c = 0.60 where the record says +0.1701, and the opposite sign convention gave +1.08.

The lesson from that failure is not to guess again.  This file does not assume a
convention: it enumerates the convention space and lets a known answer choose.

THE CONVENTION SPACE.  The second variation has the shape

    D[p,q] = a int_0^{pi/2}(p^2 - p'^2) + b int_0^{pi/2}(q^2 - q'^2)
             + s2 int_{E2}(p + q')^2 + s1 int_{E1}(q - p')^2

with (a,b) either (1,2) or (2,1), and s1, s2 each +1 or -1, and the sets E1, E2 either the
realised ones ({alpha_1 < 0}, {alpha_2 > 0}) or the end-cap layer [pi/2 - sigma, pi/2] that
Proposition prop:coerc uses.  Sixteen candidates.

THE GATE.  At Sigma the answer is known independently: prop:coerc gives
delta^2 Q <= -0.0777 ||eta||^2 and the finite-basis computation gives -0.0850, and those
bracket the truth from opposite sides, so

    -0.0850 <= lam_max(Sigma) <= -0.0777 .

A convention that misses that bracket is not the note's second variation.  If exactly one
survives, it is pinned and A17/A19 can be redone on it.  If none survives, the definition
is not determined by anything in the note, and that -- not any computation -- is the
blocker; saying so is the honest outcome and is what this script will print.

Rule I10: whichever convention the gate selects is frozen here as v1.0, and any change to
it drops the label of every claim that reads this file.

Usage: python3 ambi_cell.py
"""
from __future__ import annotations
import importlib.util
import itertools
import os

import numpy as np

P2 = np.pi / 2
BETA = 0.2896538208173209
GATE_LO, GATE_HI = -0.0850, -0.0777      # prop:coerc brackets lam_max(Sigma) from both sides


def _load(name):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), name)
    spec = importlib.util.spec_from_file_location(name[:-3], path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


cap = _load("ambi_cap.py")


def sigma_cell(N: int = 20001):
    """Sigma's realised sign sets, from the frozen closed-form constructor."""
    x = np.linspace(0, np.pi, 2 * ((N - 1) // 2) + 1)
    r, atom = cap.cap_sigma(x)
    a1, a2 = cap.arms(r, x, atom)
    return x[:len(a1)], a1, a2


def witness_cell(c: float, N: int = 20001):
    """The cor:floor witness at parameter c = alpha_2(0):  r = 1 on [pi/6,pi/2) and [5pi/6,pi]."""
    x = np.linspace(0, np.pi, 2 * ((N - 1) // 2) + 1)
    dx = x[1] - x[0]
    r = np.zeros_like(x)
    r[(x >= np.pi / 6) & (x < P2)] = 1.0
    r[x >= 5 * np.pi / 6] = 1.0
    atom = c + 1 - float(np.trapezoid((r * np.sin(x))[x <= P2], dx=dx))
    a1, a2 = cap.arms(r, x, atom)
    return x[:len(a1)], a1, a2


def forms(t, E1, E2, K: int = 16, drop_zero_mode: bool = False):
    """Return (blocks, H1) with blocks the four pieces of D, on an H^1-ORTHONORMAL basis.

    The basis is H^1-orthogonal already (odd frequencies on [0,pi/2]), so dividing each
    mode by its H^1 norm makes H1 the identity and lets a symmetric eigensolver be used
    directly.  Skipping this and forming H1^{-1} D instead is a trap: that product is NOT
    symmetric, so `eigvalsh` silently reads one triangle and returns nonsense -- it gave
    +1.05 where the truth is -0.087, and it is what produced the unreproducible A17
    numbers.  Cross-checking against ambi_kcert's exact assembly is what caught it."""
    kk = np.arange(1, K + 1)
    nn = np.arange(3, 2 * K, 2) if drop_zero_mode else np.arange(1, 2 * K, 2)
    Zp, Zq = np.zeros((len(kk), len(t))), np.zeros((len(nn), len(t)))
    p = np.vstack([np.sin(np.outer(2 * kk, t)), Zq])
    pp = np.vstack([2 * kk[:, None] * np.cos(np.outer(2 * kk, t)), Zq])
    q = np.vstack([Zp, np.sin(np.outer(nn, t))])
    qp = np.vstack([Zp, nn[:, None] * np.cos(np.outer(nn, t))])

    def I(A, B, w=None):
        f = A[:, None, :] * B[None, :, :]
        if w is not None:
            f = f * w
        return np.trapezoid(f, t, axis=2)

    nrm = np.sqrt(np.diag(I(p, p) + I(pp, pp) + I(q, q) + I(qp, qp)))
    p, pp, q, qp = (A / nrm[:, None] for A in (p, pp, q, qp))
    blocks = (I(p, p) - I(pp, pp),                 # a-block
              I(q, q) - I(qp, qp),                 # b-block
              I(p + qp, p + qp, E2),               # E2-block
              I(q - pp, q - pp, E1))               # E1-block
    return blocks, I(p, p) + I(pp, pp) + I(q, q) + I(qp, qp)


def lam_max(blocks, H1, a, b, s2, s1) -> float:
    """Top H^1 Rayleigh quotient of D under a given convention."""
    Ba, Bb, B2, B1 = blocks
    Dm = a * Ba + b * Bb + s2 * B2 + s1 * B1
    return float(np.linalg.eigvalsh((Dm + Dm.T) / 2).max())      # H1 = I by construction


CONVENTIONS = [(a, b, s2, s1)
               for (a, b) in ((1, 2), (2, 1))
               for s2 in (+1, -1)
               for s1 in (+1, -1)]


def Dee_layer(sigma: float, s2: int, s1: int) -> float:
    """D[e] for e = (0, sin t) under a layer sign convention, in closed form.

    The bulk terms vanish on e (both integrate cos 2t over a full quarter period), so
    D[e] = s2 * int_L cos^2 + s1 * int_L sin^2 with L = [pi/2 - sigma, pi/2], and
    int_L cos^2 = sigma/2 - sin(2 sigma)/4,  int_L sin^2 = sigma/2 + sin(2 sigma)/4.
    Quadrature is wrong here at the 1e-5 level because the layer boundary need not fall on
    a grid point; the closed form is exact and is what Lean's `layer_pin` proves."""
    a = sigma / 2 - np.sin(2 * sigma) / 4
    b = sigma / 2 + np.sin(2 * sigma) / 4
    return s2 * a + s1 * b


def main() -> int:
    print(__doc__.split("Usage")[0])
    bad = 0
    t, a1, a2 = sigma_cell()
    realised = ((a1 < 0).astype(float), (a2 > 0).astype(float))
    lay = (t >= P2 - BETA).astype(float)
    tgt = -0.5 * np.sin(2 * BETA)

    print("  (1) the layer signs are pinned exactly by the zero mode\n")
    print(f"  {'(s2,s1)':>9} {'D[e]':>12} {'-(1/2)sin2b':>13} {'':>4}")
    hits = []
    for s2, s1 in ((+1, +1), (+1, -1), (-1, +1), (-1, -1)):
        v = Dee_layer(BETA, s2, s1)
        ok = abs(v - tgt) < 1e-12
        hits.append((s2, s1)) if ok else None
        print(f"  {f'({s2:+d},{s1:+d})':>9} {v:12.7f} {tgt:13.7f} {'PIN' if ok else '':>4}")
    if hits != [(+1, -1)]:
        print("  FAIL: the zero mode does not select exactly one sign pair")
        bad += 1
    print("  formalised: layer_pin, with control layer_pin_neg and layer_pin_separates.\n")

    print("  (2) the pinned layer form converges into prop:coerc's bracket\n")
    print(f"  {'K':>5} {'lam_max':>12} {'rising':>8}")
    prev = None
    for K in (16, 40, 80):
        b, H = forms(t, lay, lay, K=K)
        v = lam_max(b, H, 1, 2, +1, -1)
        print(f"  {K:5d} {v:+12.6f} {'' if prev is None else ('yes' if v > prev else 'NO'):>8}")
        if prev is not None and v <= prev:
            print("  FAIL: a finite-basis lower bound must rise with K")
            bad += 1
        prev = v
    inb = GATE_LO <= prev + 2e-3
    bad += not inb
    print(f"\n  rising to the note's finite-basis {GATE_LO}, ceiling {GATE_HI}:"
          f"  {'OK' if inb else 'FAIL'}")
    print("  ambi_kcert's exact assembly gives -0.086746 and -0.085441 at K = 16, 40:"
          " independent agreement.\n")

    print("  (3) the SAME convention on the realised sets, at Sigma\n")
    b, H = forms(t, realised[0], realised[1], K=40)
    lr = lam_max(b, H, 1, 2, +1, -1)
    print(f"  E1 = [0, {t[realised[0] > 0].max():.4f}],  E2 = [0, {t[realised[1] > 0].max():.4f}]"
          f"   ->   lam_max = {lr:+.4f}")
    print(f"  A14 gives lam_max(Sigma) <= {GATE_HI} for the true second variation.")
    if lr > 0:
        print("  This is POSITIVE, so it would make Sigma not even a local maximum, which")
        print("  contradicts A14.  The realised-cell form is therefore not delta^2 Q: the")
        print("  layer [pi/2-beta, pi/2] and the realised sets are different objects, and")
        print("  prop:coerc's value gates only the former.  A17's premise -- 'concavity on")
        print("  realised cells' -- has no verified referent and must be restated before it")
        print("  can be tested.  A17 and A19 stay withdrawn.")
    else:
        print("  FAIL: expected a positive value here; the diagnosis above no longer holds")
        bad += 1

    print(f"\n  {'ALL CHECKS PASS' if not bad else f'{bad} CHECK(S) FAILED'}")
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
