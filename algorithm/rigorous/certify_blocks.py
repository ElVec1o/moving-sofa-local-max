"""(F3), linear-algebra half: arb-certified spectral statements (flint, 256-bit).

1) K=16 frozen block: all 32 leading principal minors of the H1-normalized
   matrix alternate in sign STRICTLY (ball excludes 0) => NEGATIVE DEFINITE,
   conditional only on entrywise enclosures of radius 1e-10 around the
   25-digit assembled values.
2) K=32 frozen block: rigorous Rayleigh quotient along the computed extremal
   vector = [0.06563222 +/- 3.82e-9] > 0 => INDEFINITENESS certified.

Remaining for full (F3): interval quadrature of the closed-form entry
integrands (replacing the 1e-10 enclosure premise by computed balls).
Run: python3 certify_blocks.py
"""
import numpy as np, os
from flint import arb, arb_mat, ctx
ctx.prec = 256
HERE = os.path.dirname(os.path.abspath(__file__))
RAD = 1e-10

def ball_mat(M):
    n = M.shape[0]; A = arb_mat(n, n)
    for i in range(n):
        for j in range(n):
            A[i, j] = arb(float(M[i, j])) + arb(0, RAD)
    return A

def h1_normalized(npz):
    Z = np.load(os.path.join(HERE, npz)); Q, G = Z['Q'], Z['G']
    S = np.diag(1/np.sqrt(np.diag(G)))
    return S @ Q @ S

def certify_negdef(M):
    A = ball_mat(M); n = M.shape[0]
    for m in range(1, n+1):
        sub = arb_mat(m, m)
        for i in range(m):
            for j in range(m):
                sub[i, j] = A[i, j]
        d = sub.det()
        lo, hi = float(d.mid()-abs(d.rad())), float(d.mid()+abs(d.rad()))
        if (m % 2 == 0 and not lo > 0) or (m % 2 == 1 and not hi < 0):
            return False, m
    return True, n

def certify_positive_direction(M, x):
    n = M.shape[0]; num = arb(0); den = arb(0)
    for i in range(n):
        den += arb(float(x[i]))**2
        for j in range(n):
            num += (arb(float(M[i, j]))+arb(0, RAD))*arb(float(x[i]))*arb(float(x[j]))
    r = num/den
    return float(r.mid()-abs(r.rad())) > 0, r

if __name__ == "__main__":
    M16 = h1_normalized('qfrz_block_K16.npz')
    ok, m = certify_negdef(M16)
    print(f"K=16 frozen block negative definite (arb-certified minors): {ok}")
    M32 = h1_normalized('qfrz_block_K32.npz')
    w, V = np.linalg.eigh(M32)
    ok2, r = certify_positive_direction(M32, V[:, -1])
    print(f"K=32 indefiniteness certified (Rayleigh {r}): {ok2}")
