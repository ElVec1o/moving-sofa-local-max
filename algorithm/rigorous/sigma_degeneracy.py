"""sigma_degeneracy.py — does Sigma have Gerver's wall-coincidence degeneracy?

Gerver's Part II defect traces to a single structural fact: contact arc A is
CONSTANT on [0,phi] and arc C on [pi/2-phi,pi/2], pinned at a corner of the
sofa while the hallway sweeps.  A constant arc contributes nothing to Green's
integral at c_G but starts moving under perturbation, and the closing chord
then picks up a first-order sliver -- the rank-one defect -(l/2) L.

Sigma's reconstruction has clean first variations (~1e-6) on every mode, so it
has no such defect.  This script confirms the STRUCTURAL reason rather than
assuming it: if no Sigma arc is stationary anywhere on its range, the
degeneracy cannot occur.

Test: min |dP/dt| over each of the 10 arcs.  Gerver's arcs A and C hit exactly
0 on a whole interval; Sigma's should be bounded away from 0.

Usage: python3 sigma_degeneracy.py [n]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sigma_envelope import arc_point, TAB


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4001
    print("SIGMA: is any contact arc stationary on its range?")
    print("  (Gerver's arcs A and C are identically CONSTANT on an interval,")
    print("   which is what makes Part II's reconstruction non-stationary.)\n")
    print("%6s %20s %14s %14s" % ("arc", "range", "min|dP/dt|", "at t"))
    worst = None
    for (lab, t0, t1, slot) in TAB:
        ts = np.linspace(t0, t1, n)
        P = np.array([arc_point(lab, slot, t, [], []) for t in ts])
        # ranges may DESCEND (t0 > t1): take |dt| or the speed comes
        # out negative and argmin picks the most negative, not the
        # smallest magnitude.
        d = np.linalg.norm(np.diff(P, axis=0), axis=1)/np.abs(np.diff(ts))
        i = int(d.argmin())
        print("%6s [%7.5f,%7.5f] %14.6e %14.6f"
              % (lab, t0, t1, d[i], ts[i]))
        if worst is None or d[i] < worst[0]:
            worst = (d[i], lab, ts[i])
    print("\nsmallest speed anywhere on dSigma: %.6e  (arc %s at t=%.5f)"
          % worst)
    print("\nVERDICT:", "NO arc is stationary -- Sigma cannot have Gerver's\n"
          "  wall-coincidence degeneracy, and its clean first variations are\n"
          "  explained structurally, not accidentally."
          if worst[0] > 1e-3 else
          "*** an arc is (near-)stationary -- Sigma may share the defect ***")


if __name__ == "__main__":
    main()
