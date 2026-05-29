"""Decisive discriminator for finite-rank Q_jump.

A finite-rank operator supported on the breakpoint 1-jets predicts a
diagonal excess whose leading term is

   E[k] ~ sum_j A_j * (2k cos(2k b_j))^2  =  sum_j A_j k^2 (1 + cos(4k b_j))/2 * ...

i.e. E[k]/k^2 MUST contain oscillation in k at the FOUR frequencies 4*b_j
(plus a DC term).  A smooth, mode-uniform excess (e.g. an extra
differential-operator term c*||eta'||^2 or c*||eta''||^2) gives E[k]/k^2 =
const with NO oscillation.

Discriminator: is the empirical E[k]/k^2 oscillating at 4*b_j, or flat?
We compare:
   model O  (oscillating): DC + sum_j a_j cos(4k b_j) + b_j sin(4k b_j)  (9 params)
   model S  (smooth):      low-order polynomial in k                    (<=4 params)
and we look at whether the OSCILLATING amplitudes are significant, and
whether they sit at the breakpoint frequencies vs anywhere.
"""
from __future__ import annotations
import json, os, math
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
B = np.array([0.039177, 0.681301, math.pi/2 - 0.681301, math.pi/2 - 0.039177])

def load():
    rows = json.load(open(os.path.join(HERE, "hypV_sweep.json")))["rows"]
    k = np.array([r["k"] for r in rows], float)
    E = np.array([r["Qx"]+r["Qy"] for r in rows], float) + math.pi*k**2
    return k, E

def lstsq_R2(A, y):
    c,*_ = np.linalg.lstsq(A, y, rcond=None)
    r = y - A@c
    R2 = 1 - (r@r)/(((y-y.mean())@(y-y.mean())))
    return c, R2, r

def main():
    k, E = load()
    # Restrict to the trustworthy band: high-k decay (k>=20) is oracle
    # under-resolution of the rapidly oscillating sin(2k theta) basis, so we
    # analyse k<=16 where the oracle resolves the mode.
    m = k <= 16
    kk, Ek = k[m], E[m]
    y = Ek / kk**2     # the per-mode excess density
    print("k   E/k^2")
    for a,b in zip(kk.astype(int), y): print(f"{a:3d}  {b:8.4f}")
    print(f"\nmean(E/k^2) = {y.mean():.4f}   std = {y.std():.4f}   "
          f"std/mean = {abs(y.std()/y.mean()):.3%}")

    # Model S: smooth (constant, then +1/k correction)
    AS = np.column_stack([np.ones_like(kk), 1.0/kk])
    _, R2s, rs = lstsq_R2(AS, y)
    print(f"\n[smooth]  y = a + b/k         R^2 = {R2s:.5f}  rms resid = {np.sqrt((rs@rs)/len(rs)):.4f}")

    # Model O: DC + oscillation at the breakpoint frequencies 4*b_j
    cols = [np.ones_like(kk)]
    for b in B:
        cols += [np.cos(4*kk*b), np.sin(4*kk*b)]
    AO = np.column_stack(cols)
    cO, R2o, ro = lstsq_R2(AO, y)
    osc_amp = [math.hypot(cO[1+2*j], cO[2+2*j]) for j in range(4)]
    print(f"[oscill]  DC + sum cos/sin(4k b_j)  R^2 = {R2o:.5f}  ({AO.shape[1]} params)")
    print(f"          DC = {cO[0]:.4f} ; oscillation amplitudes at 4b_j = "
          + ", ".join(f"{a:.3f}" for a in osc_amp))

    print("\n=== READING ===")
    print(f"  If finite-rank-at-breakpoints dominated the O(k^2) excess, the")
    print(f"  oscillation amplitudes would be COMPARABLE to the DC term {abs(cO[0]):.2f}.")
    print(f"  Largest osc amplitude / |DC| = {max(osc_amp)/abs(cO[0]):.3%}")
    if max(osc_amp)/abs(cO[0]) < 0.10 and abs(y.std()/y.mean()) < 0.12:
        print("  -> The excess is SMOOTH & mode-uniform, NOT oscillating at 4b_j.")
        print("     => leading O(k^2) excess is NOT finite-rank point-supported.")
        print("     => finite-rank Q_jump hypothesis NOT supported by diagonal data.")
    else:
        print("  -> Significant breakpoint-frequency oscillation present.")
        print("     => consistent with finite-rank point support.")

if __name__ == "__main__":
    main()
