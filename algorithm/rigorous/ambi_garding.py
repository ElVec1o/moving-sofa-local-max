import sys, math, numpy as np
import os
THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from ambi_concavity import hess_sets
from ambi_hessian import Hats, PI2, PI, mass_stiff
b = 0.2896538208173209

def mass(B):
    """L^2 mass matrix, correctly assembled (see mass_stiff)"""
    return mass_stiff(B)[0]

print("GARDING CONSTANT: sup over eta of  d^2Q[eta] / ||eta||_{L^2}^2")
print("  (symmetric generalized eigenproblem via Cholesky, not Mass^-1 M)\n")
print(f"  {'m':>5} {'dim':>5} {'sup ratio':>12} {'2nd':>12}")
for m in (32, 64, 128, 256):
    B, M = hess_sets(m, [(0.0, b)], [(0.0, PI2-b)])
    Ms = mass(B)
    L = np.linalg.cholesky(Ms)
    A = np.linalg.solve(L, np.linalg.solve(L, M).T).T
    A = 0.5*(A + A.T)
    w = np.linalg.eigvalsh(A)
    print(f"  {m:5d} {B.dim:5d} {w.max():12.6f} {w[-2]:12.6f}")
print("\n  a negative supremum bounded away from 0 as m grows is a Garding inequality")
print("  d^2Q <= -c ||eta||^2 with that c.")
