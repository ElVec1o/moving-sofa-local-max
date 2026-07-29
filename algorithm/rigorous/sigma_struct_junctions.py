"""sigma_struct_junctions.py — exact junction data for Sigma's structure-
following reconstruction (S7''' assembly input).

The traversal found by sigma_struct_map.py is the 10-arc cycle

    dA -> rA -> dB -> dX -> dD -> rC -> dC -> rD -> rX -> rB -> (dA)

(d = direct family, r = its rho-image; A,B = mu-slot walls x=1,x=0;
C,D = nu-slot walls y=1,y=0; X = reflex-corner path). Consecutive arcs meet
at a point of the plane, at DIFFERENT parameters on each arc — exactly as
Gerver's four junctions do. This script solves each meeting by Gauss-Newton
on |arc1(t) - arc2(s)|, giving the frozen parameter table the closed-form
assembly needs, and checks the cap stationarity lam_A == 0 directly on the
arc.
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sigma_struct_map import cjet, rho, PI2
from sofa_romik2017_reference import BETA


def arc_pt(lab, t):
    """Contact point of arc `lab` at parameter t (labels d?/r? with ?=ABCDX)."""
    t = min(max(float(t), 0.0), PI2)
    fam, kind = lab[0], lab[1]
    c, cp = cjet(t)
    mu = np.array([math.cos(t), math.sin(t)])
    nu = np.array([-math.sin(t), math.cos(t)])
    dmu = float(cp @ mu); dnu = float(cp @ nu)
    p = {'A': c + dmu*nu + mu,
         'B': c + dmu*nu,
         'C': c - dnu*mu + nu,
         'D': c - dnu*mu,
         'X': c}[kind]
    return rho(p) if fam == 'r' else p


def solve_junction(l1, t0, l2, s0, iters=80):
    t, s = float(t0), float(s0)
    h = 1e-6
    for _ in range(iters):
        F = arc_pt(l1, t) - arc_pt(l2, s)
        J1 = (arc_pt(l1, t+h) - arc_pt(l1, t-h)) / (2*h)
        J2 = -(arc_pt(l2, s+h) - arc_pt(l2, s-h)) / (2*h)
        J = np.column_stack([J1, J2])
        if abs(np.linalg.det(J)) < 1e-14:
            break
        d = np.linalg.solve(J, -F)
        # damped step, clamped to the parameter interval
        lam = 1.0
        while lam > 1e-6:
            tt = min(max(t + lam*d[0], 0.0), PI2)
            ss = min(max(s + lam*d[1], 0.0), PI2)
            if np.linalg.norm(arc_pt(l1, tt) - arc_pt(l2, ss)) < np.linalg.norm(F):
                break
            lam *= 0.5
        t, s = tt, ss
        if lam*np.linalg.norm(d) < 1e-15:
            break
    return t, s, float(np.linalg.norm(arc_pt(l1, t) - arc_pt(l2, s)))


def arc_speed(lab, t, h=1e-6):
    return float(np.linalg.norm(
        (arc_pt(lab, t+h) - arc_pt(lab, t-h)) / (2*h)))


def main():
    print("CAP STATIONARITY CHECK (lam_A == 0 on (0,beta) predicted):")
    P0 = arc_pt('dA', 1e-7)
    for t in (1e-7, 0.05, 0.12, 0.20, 0.28, BETA, 0.40, 0.70):
        P = arc_pt('dA', t)
        print(f"  t={t:7.4f}  dA=({P[0]:+.9f},{P[1]:+.9f})  "
              f"|dA-dA(0)|={np.linalg.norm(P-P0):.3e}  speed={arc_speed('dA',t):.4f}")

    print(f"\n  (the A-contact is FROZEN on (0,beta): the cap point is on the "
          f"mirror axis? y={P0[1]:.9f} vs 0.5)")

    PAIRS = [('dA', 0.301, 'rA', 0.292),
             ('rA', 1.552, 'dB', 1.568),
             ('dB', 0.334, 'dX', 0.295),
             ('dX', 1.281, 'dD', 1.217),
             ('dD', 0.018, 'rC', 0.004),
             ('rC', 1.270, 'dC', 1.279),
             ('dC', 0.018, 'rD', 0.003),
             ('rD', 1.237, 'rX', 1.276),
             ('rX', 0.290, 'rB', 0.354),
             ('rB', 1.552, 'dA', 1.567)]

    print("\nJUNCTIONS (traversal order; each row = arc1 ends / arc2 begins):")
    print(f"{'#':>2} {'arc1':>4} {'t1':>10} {'arc2':>5} {'t2':>10} "
          f"{'residual':>10}   point")
    rows = []
    for i, (l1, t0, l2, s0) in enumerate(PAIRS, 1):
        t, s, r = solve_junction(l1, t0, l2, s0)
        P = arc_pt(l1, t)
        rows.append((l1, t, l2, s, r, P))
        print(f"{i:2d} {l1:>4} {t:10.6f} {l2:>5} {s:10.6f} {r:10.2e}   "
              f"({P[0]:+.6f},{P[1]:+.6f})")

    print(f"\nreference: beta={BETA:.6f}  PI2-beta={PI2-BETA:.6f}  PI2={PI2:.6f}")
    np.save(os.path.join(THIS, "sigma_struct_junctions.npy"),
            np.array([(l1, t, l2, s) for l1, t, l2, s, _, _ in rows],
                     dtype=object), allow_pickle=True)
    print("saved sigma_struct_junctions.npy")


if __name__ == "__main__":
    main()
