"""sigma_matched.py — is the MATCHED junction response superset-valid?

sigma_envelope.py's contract is:

    "Every such reconstruction is superset-valid, so its second-order
     coefficient Q_beta bounds the true second variation from above for EVERY
     beta, and the envelope over beta is attained at the implicit-function
     response:  Q_true = min_beta Q_beta = Q_frz - C^T H_bb^{-1} C."

The measured defect is precisely in "for EVERY beta".  With beta = 0 the six
INTERIOR closures (at t = beta_R and pi/2 - beta_R) open up under perturbation --
measured gaps 1.63e-2, 8.49e-3, 5.59e-3, 9.22e-3, 5.59e-3, 8.49e-3 at eps = 1e-3
-- and area_rec closes them with CHORDS.  Chords are not constraint boundaries,
so those members of the family are NOT superset-valid, and a minimum taken over
all beta can dip below the true second variation.

(The four closures at t = 0 and t = pi/2 stay shut to 1e-17, since the
perturbations vanish there.)

So the repair is to restrict the minimisation to the MATCHED response: the beta
for which the ten interior arc ends coincide pairwise, leaving no chords at all.
That is a square system -- 5 interior junctions x 2 arcs = 10 free parameters,
5 junctions x 2 coordinates = 10 equations -- and this script

  1. solves it by Newton for a given perturbation,
  2. confirms the gaps close,
  3. tests whether the matched reconstruction dominates the true area.

If (3) passes, Theorem 9 is repairable by restricting the envelope to matched
responses.  If it fails, the chords are not the only problem.

Usage: python3 sigma_matched.py [K] [n_dir]
"""
from __future__ import annotations
import os, sys, math, subprocess
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
import sigma_envelope as SE
from romik_hessian import tabulate_romik


def gaps(amps, delta, modes):
    """the ten interior-junction mismatch coordinates"""
    shifts = {}
    for d, (pi_, which) in zip(delta, SE.FREE):
        shifts[(pi_, which)] = d
    ends = []
    for i, (lab, t0, t1, slot) in enumerate(SE.TAB):
        a0 = t0 + shifts.get((i, 't0'), 0.0)
        a1 = t1 + shifts.get((i, 't1'), 0.0)
        ends.append((SE.arc_point(lab, slot, a0, amps, modes),
                     SE.arc_point(lab, slot, a1, amps, modes)))
    out = []
    n = len(ends)
    for i in range(n):
        e = np.asarray(ends[i][1]); s0 = np.asarray(ends[(i+1) % n][0])
        if np.linalg.norm(e - s0) > 1e-12 or True:
            # keep only the closures that are NOT anchored at t=0 / t=pi/2
            t1 = SE.TAB[i][2]
            t0n = SE.TAB[(i+1) % n][1]
            anchored = (min(abs(t1), abs(t1 - math.pi/2)) < 1e-9 and
                        min(abs(t0n), abs(t0n - math.pi/2)) < 1e-9)
            if not anchored:
                out += [e[0] - s0[0], e[1] - s0[1]]
    return np.array(out)


def _newton(amps, modes, d, it=15, h=1e-6, cap=0.05, tol=1e-11, jevery=5):
    """Newton on the ten gap equations.  The Jacobian costs 20 `gaps` calls, so
    it is refreshed only every `jevery` iterations (the system is mildly
    nonlinear and the stale Jacobian still contracts)."""
    J = None
    for k in range(it):
        r = gaps(amps, d, modes)
        if np.max(np.abs(r)) < tol:
            break
        if J is None or k % jevery == 0:
            J = np.empty((len(r), len(d)))
            for j in range(len(d)):
                dp = d.copy(); dp[j] += h
                dm = d.copy(); dm[j] -= h
                J[:, j] = (gaps(amps, dp, modes) - gaps(amps, dm, modes))/(2*h)
        step, *_ = np.linalg.lstsq(J, -r, rcond=None)
        nrm = np.linalg.norm(step)
        if nrm > cap:
            step *= cap/nrm
        d = d + step
    return d, float(np.max(np.abs(gaps(amps, d, modes))))


def solve_matched(amps, modes, delta0=None, it=15, h=1e-6, nsteps=None,
                  tol=1e-11):
    """Solve for the matched junction response.

    A plain Newton from delta0 fails on roughly a quarter of probes (residuals
    up to 5.6e-2): at the amplitudes of interest the matched response is too far
    from delta0 for the linearisation to reach.  Fix (S7c): CONTINUATION in the
    amplitude.  Walk the amplitude from 0 to 1 in `ns` equal stages, re-solving
    at each and starting from the previous solution, so every solve begins inside
    its own basin.  A stage that fails aborts that ladder rung immediately --
    carrying a non-converged d forward was the bug in the first version.
    """
    d0 = np.zeros(len(SE.FREE)) if delta0 is None else delta0.copy()
    A = np.asarray(amps, dtype=float)
    best = (d0, float("inf"))
    for ns in ([1, 3, 8] if nsteps is None else [nsteps]):
        d = d0.copy()
        res = float("inf")
        for i in range(1, ns+1):
            d, res = _newton(list(A*(i/ns)), modes, d, it, h, tol=tol)
            if res > tol:
                break                      # abort this rung, do not carry on
        if res < best[1]:
            best = (d, res)
        if res <= tol:
            return d, res
    return best


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    nd = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    modes = [(c, k) for c in (0, 1) for k in range(1, K+1)]
    z = np.zeros(len(SE.FREE))
    nt = 4801
    th, cx, cy = tabulate_romik(nt)

    def rust(gx, gy):
        inp = [f"{nt} 1", " ".join(f"{t:.17g}" for t in th),
               " ".join(f"{u:.17g} {v:.17g}" for u, v in zip(gx, gy))]
        r = subprocess.run([os.path.join(THIS, "sigma_area")],
                           input="\n".join(inp), capture_output=True, text=True)
        return float(r.stdout.split()[0])

    d0, res0 = solve_matched([0.0]*len(modes), modes)
    A0 = SE.area_rec([0.0]*len(modes), d0, modes)
    T0 = rust(cx, cy)
    base = A0 - T0
    print(f"MATCHED-RESPONSE TEST   (K={K})")
    print(f"  matched delta at c_R: max |gap| = {res0:.2e}")
    print(f"  A_rec_matched(c_R) = {A0:.9f}   A_true = {T0:.9f}   "
          f"offset {base:+.3e} (subtracted)\n")
    print(f"{'dir':>6} {'eps':>8} {'max|gap|':>10} {'Delta frozen':>14} "
          f"{'Delta matched':>14} {'D/eps^2 m':>10}")
    rng = np.random.default_rng(2024)
    B = {m: np.sin(2*m[1]*th) for m in modes}
    negm = negf = tot = 0
    for t_ in range(nd):
        v = rng.standard_normal(len(modes)); v /= np.linalg.norm(v)
        gx = sum(v[i]*B[m] for i, m in enumerate(modes) if m[0] == 0)
        gy = sum(v[i]*B[m] for i, m in enumerate(modes) if m[0] == 1)
        for e in (0.004, -0.004, 0.002, -0.002):
            amps = list(e*v)
            dm, res = solve_matched(amps, modes, d0)
            At = rust(cx + e*gx, cy + e*gy)
            Af = SE.area_rec(amps, z, modes)
            Am = SE.area_rec(amps, dm, modes)
            df = (Af - At) - base
            dmv = (Am - At) - base
            tot += 1
            if df < 0:
                negf += 1
            if dmv < 0:
                negm += 1
            print(f"{t_+1:>6} {e:8.4f} {res:10.1e} {df:14.3e} {dmv:14.3e} "
                  f"{dmv/e**2:10.4f}")
        print()
    print(f"frozen  (beta=0): {negf}/{tot} probes with Delta < 0")
    print(f"matched         : {negm}/{tot} probes with Delta < 0")
    print("\nVERDICT:", "MATCHED response dominates -- Theorem 9 is repairable "
          "by restricting the envelope to matched beta."
          if negm == 0 else
          "matched response ALSO fails -- chords are not the only problem.")


if __name__ == "__main__":
    main()
