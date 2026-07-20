"""A24b: does SUMMING Lemma 8 over all binding walls reproduce the measured
H^1 diagonal, and hence supply an ANALYTIC lower bound  Q[k,k] <= -m1 w^{H1}_k ?

THE HYPOTHESIS
--------------
Lemma 8's sum rule  Q_smooth[k,k]_x + Q_smooth[k,k]_y = -pi k^2  assumes ONE
active wall per theta.  But phase2d measured a mean of 2.97 binding walls per
theta, and the empirical diagonal exceeds the single-wall prediction by a
factor of ~2.7.  Those two numbers agreeing is unlikely to be a coincidence:
the Green's-theorem boundary integral decomposes ARC-WISE, one term per active
contact path, so Q_smooth should be a SUM over the active walls:

    Q_smooth = sum_i  int_{theta : wall i active}
                 [ C(psi_i) <eta,eta'> + D(psi_i) <eta,eta''> ] dtheta

If that is right then the corrected sum rule is ~ -(#walls) pi k^2, and the
H^1 diagonal quotient  |Q[k,k]| / w^{H1}_k  should land near the measured
1.1 rather than the single-wall value 0.40.

WHY IT MATTERS NOW
------------------
Coercivity needs a LOWER bound on |Q[k,k]| valid for ALL k.  thm:hypV bounds
|Q[k,k]| from ABOVE, which is the wrong direction.  A correct multi-wall
Q_smooth would supply the lower bound analytically instead of empirically
(we only have measurements out to k=32).

OUTPUT
------
For each mode k: the single-wall and multi-wall predictions, the measured
value from hypV_sweep.json, and the H^1 quotients.  Lightweight (~10s).
"""
from __future__ import annotations
import json, math, os, sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase2d_qsmooth import (tabulate_gerver, build_sofa, measure_psi,
                             basis_derivs, coeffs)

HERE = os.path.dirname(os.path.abspath(__file__))


def assemble_multiwall(th, segs, N, mode):
    """Diagonal Q_smooth[k,k]_x and _y, summing over binding walls.

    mode='dominant' -> longest segment only (what phase2d did)
    mode='sum'      -> every binding wall contributes its own integrand
    mode='lenwt'    -> walls weighted by their share of contact length
    """
    phi, phip, phipp = basis_derivs(th, N)
    dt = np.gradient(th)
    Qx = np.zeros(N)
    Qy = np.zeros(N)
    for i, s in enumerate(segs):
        if not s:
            continue
        if mode == "dominant":
            items = [(max(s, key=lambda z: z[1])[0], 1.0)]
        elif mode == "sum":
            items = [(b, 1.0) for b, _ in s]
        else:
            tot = sum(L for _, L in s) or 1.0
            items = [(b, L / tot * len(s)) for b, L in s]
        for beta, wt in items:
            psi = 2 * beta
            C, D = coeffs(np.array([psi]))
            for k in range(N):
                base = phi[i, k] * phip[i, k]
                curv = phi[i, k] * phipp[i, k]
                Qx[k] += wt * (C[("x", "x")][0] * base
                               + D[("x", "x")][0] * curv) * dt[i]
                Qy[k] += wt * (C[("y", "y")][0] * base
                               + D[("y", "y")][0] * curv) * dt[i]
    return Qx, Qy


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    n_theta = int(sys.argv[2]) if len(sys.argv) > 2 else 2001
    th, cx, cy = tabulate_gerver(n_theta)
    S = build_sofa(th, cx, cy)
    segs = measure_psi(th, cx, cy, S)
    nw = np.array([len(s) for s in segs])
    print(f"  binding walls per theta: mean={nw.mean():.2f} "
          f"min={nw.min()} max={nw.max()}")

    meas = {}
    p = os.path.join(HERE, "hypV_sweep.json")
    if os.path.exists(p):
        d = json.load(open(p))
        rows = d if isinstance(d, list) else d.get("rows", d)
        for r in rows:
            meas[r["k"]] = (r["Qx"], r["Qy"])

    print()
    print("  Sum rule  Q_x+Q_y  vs  -pi k^2, and H^1 diagonal quotient")
    print(f"  {'k':>3} {'single':>10} {'SUM':>10} {'lenwt':>10} "
          f"{'measured':>10} | {'m1_sum':>7} {'m1_meas':>8}")
    for mode in ("dominant", "sum", "lenwt"):
        pass
    Qd = assemble_multiwall(th, segs, N, "dominant")
    Qs = assemble_multiwall(th, segs, N, "sum")
    Ql = assemble_multiwall(th, segs, N, "lenwt")
    for k in range(N):
        kk = k + 1
        sd = Qd[0][k] + Qd[1][k]
        ss = Qs[0][k] + Qs[1][k]
        sl = Ql[0][k] + Ql[1][k]
        wH1 = 2 * (1 + (2 * kk) ** 2) * math.pi / 4   # both components
        m1s = abs(ss) / wH1
        if kk in meas:
            mm = meas[kk][0] + meas[kk][1]
            m1m = abs(mm) / wH1
            print(f"  {kk:>3} {sd:>10.3f} {ss:>10.3f} {sl:>10.3f} "
                  f"{mm:>10.3f} | {m1s:>7.3f} {m1m:>8.3f}")
        else:
            print(f"  {kk:>3} {sd:>10.3f} {ss:>10.3f} {sl:>10.3f} "
                  f"{'-':>10} | {m1s:>7.3f} {'-':>8}")
    print()
    print("  single-wall m1 should be ~0.40; measured ~1.1.")
    print("  If SUM lands near the measured column, the multi-wall reading is")
    print("  confirmed and A24b has an analytic route.")


if __name__ == "__main__":
    main()
