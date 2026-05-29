"""Falsifiable test of the finite-rank Q_jump hypothesis.

Claim:  Q = Q_smooth + Q_jump, where
   (a) Q_smooth[k,k]_x + Q_smooth[k,k]_y = -pi*k^2   (Lemma 8 sum rule, exact), and
   (b) Q_jump is FINITE-RANK, supported on the 1-jets {eta(b_j), eta'(b_j)}
       at the FOUR known breakpoints b_j.

For the basis phi_k(theta)=sin(2k theta):
       eta(b_j)  ~ sin(2k b_j)
       eta'(b_j) ~ 2k cos(2k b_j)
A diagonal jump entry is a quadratic in this 1-jet.  Summed over x,y the
leading O(k^2) piece comes from the eta'(b_j)^2 ~ 4k^2 cos^2(2k b_j) terms.
So the empirical EXCESS
       E[k] := (Qx + Qy) - (-pi k^2)
should be reproduced by a small fixed-frequency model

       E[k] = sum_j [ A_j * k^2 cos^2(2k b_j)
                    + B_j * k   sin(2k b_j) cos(2k b_j)
                    + C_j *     sin^2(2k b_j) ]

with the FOUR b_j FIXED at their known values.  If a fit with the known
breakpoint frequencies nails E[k] across all k (and beats random
frequencies decisively) -> strong confirmation of finite rank.  If it
cannot -> refuted.
"""
from __future__ import annotations
import json, os, math
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))

# Known breakpoints (phi, theta, pi/2-theta, pi/2-phi)
B = np.array([0.039177, 0.681301, math.pi/2 - 0.681301, math.pi/2 - 0.039177])

def load():
    with open(os.path.join(HERE, "hypV_sweep.json")) as f:
        rows = json.load(f)["rows"]
    k = np.array([r["k"] for r in rows], float)
    Q = np.array([r["Qx"] + r["Qy"] for r in rows], float)
    E = Q - (-math.pi * k**2)        # excess attributed to jump
    return k, Q, E

def design(k, bps, orders=("k2","k1","k0")):
    """Build design matrix from breakpoint-jet basis at frequencies bps."""
    cols = []
    names = []
    for j, b in enumerate(bps):
        c = np.cos(2*k*b); s = np.sin(2*k*b)
        if "k2" in orders:
            cols.append(k**2 * c**2); names.append(f"k2cos2_{j}")
        if "k1" in orders:
            cols.append(k * s * c);   names.append(f"k1sincos_{j}")
        if "k0" in orders:
            cols.append(s**2);        names.append(f"k0sin2_{j}")
    return np.array(cols).T, names

def fit(k, E, A):
    coef, *_ = np.linalg.lstsq(A, E, rcond=None)
    pred = A @ coef
    resid = E - pred
    ss_res = float(resid @ resid)
    ss_tot = float(((E - E.mean()) @ (E - E.mean())))
    R2 = 1 - ss_res/ss_tot
    rel = np.abs(resid) / (np.abs(E) + 1e-12)
    return coef, pred, resid, R2, rel

def main():
    k, Q, E = load()
    print(f"# data points: {len(k)}  k = {k.astype(int)}")
    print(f"# E[k] = (Qx+Qy) - (-pi k^2)  (the jump excess)")
    for i in range(len(k)):
        print(f"  k={int(k[i]):3d}  E={E[i]:12.4f}   E/k^2={E[i]/k[i]**2:8.4f}")

    print("\n=== FIT 1: known breakpoints, full jet basis (12 params) ===")
    A, names = design(k, B)
    coef, pred, resid, R2, rel = fit(k, E, A)
    print(f"  params={A.shape[1]}  R^2 = {R2:.8f}  max|rel resid| = {rel.max():.3e}")

    print("\n=== FIT 2: known breakpoints, k^2 term only (4 params) ===")
    A2, _ = design(k, B, orders=("k2",))
    _, _, _, R2b, relb = fit(k, E, A2)
    print(f"  params={A2.shape[1]}  R^2 = {R2b:.8f}  max|rel resid| = {relb.max():.3e}")

    print("\n=== FIT 3: known breakpoints, k^2 + k^1 (8 params) ===")
    A3, _ = design(k, B, orders=("k2","k1"))
    _, _, _, R2c, relc = fit(k, E, A3)
    print(f"  params={A3.shape[1]}  R^2 = {R2c:.8f}  max|rel resid| = {relc.max():.3e}")

    print("\n=== CONTROL: random frequencies (1000 trials, 12 params) ===")
    rng = np.random.default_rng(0)
    best = -np.inf; beat = 0; n = 1000
    for _ in range(n):
        rb = rng.uniform(0, math.pi/2, size=4)
        Ar, _ = design(k, rb)
        _, _, _, R2r, _ = fit(k, E, Ar)
        best = max(best, R2r)
        if R2r >= R2: beat += 1
    print(f"  best random R^2 = {best:.8f}  ; trials beating known-bp R^2: {beat}/{n}")

    print("\n=== VERDICT ===")
    print(f"  known-bp full-jet R^2 = {R2:.6f}")
    print(f"  best of {n} random    = {best:.6f}")
    if R2 > 0.999 and beat == 0:
        print("  -> STRONG: known breakpoints reproduce the excess; random cannot match.")
    elif R2 > 0.99:
        print("  -> SUPPORTIVE but not decisive (check control margin).")
    else:
        print("  -> REFUTED / inconclusive: known breakpoints do NOT explain the excess.")

if __name__ == "__main__":
    main()
