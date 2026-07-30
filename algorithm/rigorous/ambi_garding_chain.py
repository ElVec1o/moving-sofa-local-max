"""ambi_garding_chain.py — the explicit constants of the concavity proof.

The note proves d^2 Q <= 0 on Sigma's cell by the chain

    coef J1 = A tan^2(beta) - delta P1 + 1 + lambda/(1-lambda)
    coef J2 = 1 - P2 + lambda/(1-lambda)
    coef J3 = 1 - P3 = 0
    coef int_{pi/2}^{pi-beta} eta'^2 = B beta^2/2 - lambda

with A = (1+kappa)/(1-delta) - 1, B = (1+1/kappa)/(1-delta) + 1, and the Poincare constants
P1 = (pi/2beta)^2, P2 = (pi/2(pi/2-beta))^2, P3 = 1, each for one Dirichlet and one free end.
This script tabulates the coefficients over (delta, kappa, lambda) and reports the choice
used in the note.

Usage: python3 ambi_garding_chain.py
"""
import math

def main():
    b = 0.2896538208173209; H = math.pi/2
    P1 = (math.pi/(2*b))**2
    P2 = (math.pi/(2*(H - b)))**2
    P3 = 1.0
    tb2 = math.tan(b)**2
    print("POINCARE CONSTANTS")
    print(f"  P1 = (pi/2beta)^2          = {P1:.6f}   [0,beta],   eta(0)=0")
    print(f"  P2 = (pi/2(pi/2-beta))^2   = {P2:.6f}   [beta,pi/2], eta(pi/2)=0")
    print(f"  P3 = 1                     = {P3:.6f}   [pi/2,pi],  eta(pi/2)=0")
    print(f"  tan^2(beta) = {tb2:.6f}    beta^2/2 = {b*b/2:.6f}\n")
    print(f"  {'delta':>6} {'kappa':>6} {'lambda':>8} {'J1':>10} {'J2':>10} {'J3':>6} "
          f"{'eta''^2':>10}  ok")
    best = None
    for d in (0.05, 0.10, 0.15, 0.20):
        for k in (0.5, 1.0, 2.0):
            A = (1 + k)/(1 - d) - 1
            Bc = (1 + 1/k)/(1 - d) + 1
            need = Bc*b*b/2
            for lam in (need + 0.005, 0.2, 0.3):
                if not (need < lam < 1):
                    continue
                c1 = A*tb2 - d*P1 + 1 + lam/(1 - lam)
                c2 = 1 - P2 + lam/(1 - lam)
                c3 = 1 - P3
                c4 = need - lam
                ok = c1 < 0 and c2 < 0 and c3 <= 0 and c4 < 0
                if ok and (best is None or min(-c1, -c2) > best[0]):
                    best = (min(-c1, -c2), d, k, lam, c1, c2, c3, c4)
                print(f"  {d:6.2f} {k:6.1f} {lam:8.3f} {c1:10.4f} {c2:10.4f} {c3:6.2f} "
                      f"{c4:10.5f}  {'yes' if ok else ''}")
    sc, d, k, lam, c1, c2, c3, c4 = best
    print(f"\n  chosen: delta = {d}, kappa = {k}, lambda = {lam:.3f}")
    print(f"    (1/2) d^2 Q <= {c1:.4f} J1 + {c2:.4f} J2 + {c3:.4f} J3 "
          f"{c4:+.5f} int_[pi/2,pi-beta] eta'^2")
    print(f"    all coefficients <= 0, so d^2 Q <= 0; implied L^2(0,pi/2) constant "
          f"{2*sc:.4f}")
    print(f"    (measured supremum over L^2(0,pi): -0.7285, see ambi_garding.py)")

if __name__ == "__main__":
    main()
