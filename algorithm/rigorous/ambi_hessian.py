"""ambi_hessian.py — is  Q = |C2| - 2V  concave?  The Hessian on support-function
perturbations.

ONE VARIABLE.  Since nu_t = mu_{t+pi/2}, everything is a functional of the single
function

    H(theta) := h_K(mu_theta),   theta in [0, pi],      F(t) = H(t),  G(t) = H(t+pi/2).

THE CAP IS AN EXACT QUADRATIC FORM.  rho(x,y) = (x, 1-y) is a reflection through the
line y = 1/2, NOT through the origin, so rho p = Rp + (0,1) with R = diag(1,-1) and
therefore

    h_{rho A}(u) = h_A(Ru) + u_y ,

which is why the support function of C2 = C ^ rho C is NOT H(|theta|):

    h_2(theta) = H(theta)                     theta in [0, pi]
    h_2(theta) = H(-theta) + sin theta        theta in [-pi, 0].

(Checked against the polygon: at theta = -pi/2, H(pi/2) - 1 = 0, and the polygon's
support value is 0.000000; at theta = -2.4, H(2.4) + sin(-2.4) = 0.726083 against
0.726083.  Using H(|theta|) instead gives 4.347 for the area against the true 2.013.)

For any support function in H^1 of the circle the area is A = (1/2) int h_2 d(sigma_2)
with sigma_2 = (h_2 + h_2'') dtheta as a measure, and the distributional pairing
<h_2'', h_2> = -int h_2'^2 needs no boundary or atom terms on a circle.  Splitting the
circle at theta = 0, pi and using the two branches above,

    |C2| = int_0^pi [ H^2 - H'^2 - H sin s + H' cos s - (1/2) cos 2s ] ds
         = int_0^pi ( H^2 - H'^2 ) ds  -  H(0) - H(pi) ,                         (A)

the second form because int_0^pi cos 2s ds = 0 and
int_0^pi H' cos s ds = -H(0) - H(pi) + int_0^pi H sin s ds.  Verified: 4.347441246 -
1 - 1.334100 = 2.013341, against A_R* + 2V = 2.013341613.

The correction -H(0) - H(pi) is LINEAR in H, so it does not enter the Hessian: still

    d^2 |C2| [eta] = 2 int_0^pi ( eta^2 - eta'^2 ) dtheta .

Formula (A) is also translation-invariant in x, as it must be: under H -> H + v cos
theta both int(H^2-H'^2) and -H(0)-H(pi) are unchanged, and so are alpha_1, alpha_2 and
sigma.  So eta = cos theta is an exact null direction, excluded here by the gauge.

THE NICHE.  From the note,

    alpha_1(t) = G-1-F' ,  alpha_2(t) = F-1+G' ,  sigma(t) = (F-1) tan t + G-1,
    V = int_0^{pi/2} [ (1/2)(alpha_2^+)^2 + (1/2)(sigma-alpha_1)^2
                                          - (1/2)(alpha_1^-)^2 ] dt.

Perturb H -> H + eta.  Then d(alpha_1) = eta(t+pi/2) - eta'(t),
d(alpha_2) = eta(t) + eta'(t+pi/2), d(sigma) = eta(t) tan t + eta(t+pi/2), and the
eta(t+pi/2) CANCELS in the middle term:

    d(sigma - alpha_1) = eta(t) tan t + eta'(t).

So, with the sign pattern of Sigma frozen (alpha_2 > 0 exactly on [0,pi/2-beta],
alpha_1 < 0 exactly on [0,beta), and the integrand C^1 across both, so the moving
boundaries contribute nothing at second order),

  (1/2) d^2 Q[eta] = int_0^pi (eta^2 - eta'^2) dtheta
                   - int_0^{pi/2-beta} ( eta(t) + eta'(t+pi/2) )^2 dt
                   - int_0^{pi/2}      ( eta(t) tan t + eta'(t) )^2 dt
                   + int_0^{beta}      ( eta(t+pi/2) - eta'(t) )^2 dt .          (Q2)

GAUGE.  c(0) = (H(0)-1, H(pi/2)-1), so fixing the translation gives H(0) = 1, and the
unit corridor forces H(pi/2) = h((0,1)) = 1 -- which is also exactly what makes
sigma tan-integrable at t = pi/2.  Admissible perturbations therefore satisfy

    eta(0) = eta(pi/2) = 0.

THE PRINCIPAL SYMBOL IS NEGATIVE.  Collecting the coefficient of eta'(theta)^2 in (Q2):
-1 (cap) -1 (sigma term) +1 (obstruction) = -1 on [0,beta); -1-1 = -2 on [beta,pi/2];
-1-1 = -2 on (pi/2,pi-beta); -1 on [pi-beta,pi].  Negative throughout, so (Q2) is
bounded above and has at most finitely many non-negative eigenvalues.  Concavity is
therefore a finite question, which this script answers numerically in a hat basis.

Usage: python3 ambi_hessian.py [m_intervals]
"""
from __future__ import annotations
import os, sys, math
import numpy as np

THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
from sofa_romik2017_reference import BETA
from ambi_functional import z_and_dz, data, PI2, A_R

PI = math.pi


# ------------------------------------------------------------------ #
#  H and H' for Sigma, from the corner path                          #
# ------------------------------------------------------------------ #

def H_and_dH(th):
    """H(theta) = h_K(mu_theta) and H'(theta), for theta in [0, pi].
       theta <= pi/2 :  H = <c(theta), mu_theta> + 1,  H' = -alpha_1 + (H(theta+pi/2)-1)
       theta >  pi/2 :  H = <c(s), nu_s> + 1 (s=theta-pi/2), H' = alpha_2(s) - (H(s)-1)"""
    out = np.zeros(len(th)); dout = np.zeros(len(th))
    for i, t in enumerate(th):
        t = float(t)
        if t <= PI2:
            z, dz = z_and_dz(min(t, PI2 - 1e-12))
            w = np.exp(-1j*t)*z
            out[i] = w.real + 1.0
            zb, dzb = z_and_dz(max(min(t, PI2 - 1e-12), 1e-12))
            wb = np.exp(-1j*t)*dzb
            a1 = -wb.real
            # G(t) - 1 = <c(t), nu_t>
            dout[i] = -a1 + w.imag
        else:
            s = t - PI2
            z, dz = z_and_dz(min(max(s, 1e-12), PI2 - 1e-12))
            w = np.exp(-1j*s)*z
            out[i] = w.imag + 1.0
            wb = np.exp(-1j*s)*dz
            a2 = wb.imag
            dout[i] = a2 - w.real
    return out, dout


# ------------------------------------------------------------------ #
#  quadrature helpers                                                #
# ------------------------------------------------------------------ #

def gl(lo, hi, n=24):
    x, w = np.polynomial.legendre.leggauss(n)
    return 0.5*(hi-lo)*x + 0.5*(hi+lo), 0.5*(hi-lo)*w


def gl_split(bps, n=24):
    """Gauss nodes on each interval between consecutive breakpoints"""
    T = []; W = []
    for a, b in zip(bps[:-1], bps[1:]):
        if b - a < 1e-14:
            continue
        t, w = gl(a, b, n)
        T.append(t); W.append(w)
    return np.concatenate(T), np.concatenate(W)


def check_cap():
    """verify |C2| = int_0^pi (H^2 - H'^2) dtheta against the polygonal values"""
    bps = [0.0, BETA, PI2 - BETA, PI2, PI2 + BETA, PI - BETA, PI]
    for n in (24, 48, 96):
        T, W = gl_split(bps, n)
        H, dH = H_and_dH(T)
        H0, _ = H_and_dH([0.0]); Hp, _ = H_and_dH([PI])
        A = float(W @ (H*H - dH*dH)) - H0[0] - Hp[0]
        print(f"    n={n:3d}:  int(H^2-H'^2) - H(0) - H(pi) = {A:.9f}")
    T, W = gl_split(bps, 96)
    H, dH = H_and_dH(T)
    H0, _ = H_and_dH([0.0]); Hp, _ = H_and_dH([PI])
    print(f"    H(0) = {H0[0]:.9f}   H(pi) = {Hp[0]:.9f}   "
          f"int(H^2-H'^2) = {float(W @ (H*H - dH*dH)):.9f}")
    return float(W @ (H*H - dH*dH)) - H0[0] - Hp[0]


# ------------------------------------------------------------------ #
#  the hat basis and the Hessian                                     #
# ------------------------------------------------------------------ #

class Hats:
    """piecewise-linear hats on [0,pi] with m intervals; the hats at theta=0 and
    theta=pi/2 are DROPPED, enforcing eta(0) = eta(pi/2) = 0"""

    def __init__(self, m):
        assert m % 2 == 0
        self.m = m
        self.h = PI/m
        self.nodes = np.arange(m+1)*self.h
        keep = [j for j in range(m+1) if j != 0 and j != m//2]
        self.keep = np.array(keep)
        self.idx = -np.ones(m+1, dtype=int)
        self.idx[self.keep] = np.arange(len(keep))
        self.dim = len(keep)

    def val_grad(self, th):
        """coefficient vectors of eta -> eta(th) and eta -> eta'(th), as (dim,) arrays
        for each of the given points; returns (P, D) of shape (len(th), dim)"""
        th = np.atleast_1d(np.asarray(th, dtype=float))
        P = np.zeros((len(th), self.dim)); D = np.zeros((len(th), self.dim))
        for i, t in enumerate(th):
            t = min(max(t, 0.0), PI - 1e-15)
            j = int(t/self.h)
            if j >= self.m:
                j = self.m - 1
            xi = (t - j*self.h)/self.h
            for node, v, d in ((j, 1.0 - xi, -1.0/self.h),
                              (j+1, xi, 1.0/self.h)):
                k = self.idx[node]
                if k >= 0:
                    P[i, k] += v; D[i, k] += d
        return P, D


def hessian(m, nq=8, worst=False):
    B = Hats(m)
    # breakpoints: every hat node, plus the sign-change points, plus their pi/2 shifts
    base = set(B.nodes.tolist())
    for x in (BETA, PI2 - BETA, PI2 + BETA, PI - BETA, PI2):
        base.add(x)
    bps_full = np.array(sorted(base))
    M = np.zeros((B.dim, B.dim))

    def accum(T, W, vecs, sign):
        A = np.zeros((B.dim, B.dim))
        for v in [vecs]:
            pass
        A += (vecs * W[:, None]).T @ vecs
        return sign*A

    # 1) cap:  int_0^pi (eta^2 - eta'^2)
    T, W = gl_split(bps_full[(bps_full >= 0) & (bps_full <= PI)], nq)
    P, D = B.val_grad(T)
    M += accum(T, W, P, +1.0) + accum(T, W, D, -1.0)

    # 2) - int_{E2} (eta(t) + eta'(t+pi/2))^2 ;  worst case E2 = empty (drop it)
    hi2 = 0.0 if worst else (PI2 - BETA)
    sub = bps_full[(bps_full >= 0) & (bps_full <= hi2)]
    if hi2 > 0:
        sub = np.unique(np.concatenate([sub, np.array([hi2])]))
        T, W = gl_split(sub, nq)
        P, _ = B.val_grad(T)
        _, D2 = B.val_grad(T + PI2)
        M += accum(T, W, P + D2, -1.0)

    # 3) - int_0^{pi/2} (eta(t) tan t + eta'(t))^2
    sub = bps_full[(bps_full >= 0) & (bps_full <= PI2)]
    T, W = gl_split(sub, nq)
    P, D = B.val_grad(T)
    M += accum(T, W, P*np.tan(T)[:, None] + D, -1.0)

    # 4) + int_{E1} (eta(t+pi/2) - eta'(t))^2 ;  worst case E1 = all of [0,pi/2]
    hi1 = PI2 if worst else BETA
    sub = bps_full[(bps_full >= 0) & (bps_full <= hi1)]
    sub = np.unique(np.concatenate([sub, np.array([hi1])]))
    T, W = gl_split(sub, nq)
    P2, _ = B.val_grad(T + PI2)
    _, D = B.val_grad(T)
    M += accum(T, W, P2 - D, +1.0)

    return B, 0.5*(M + M.T)


def main():
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    print("Q = |C2| - 2V :  IS IT CONCAVE?\n")
    print("(a) the cap as an exact quadratic form,  |C2| = int_0^pi (H^2 - H'^2)")
    A = check_cap()
    print(f"    polygonal |C2|: 2.013345504 (n=241), 2.013342045 (n=481,721),")
    print(f"    decreasing to the exact value; and A_R* + 2V = "
          f"{A_R + 2*0.184193197089:.9f}")
    print(f"    formula (A) gives {A:.9f}   "
          f"diff from A_R*+2V: {A - (A_R + 2*0.184193197089):+.2e}\n")

    for worst in (False, True):
        tag = ("(c) WORST-CASE sign pattern: E2 = empty, E1 = [0,pi/2].  The true "
               "Hessian on\n    every cell is <= this one, so if THIS is <= 0 then Q "
               "is concave GLOBALLY."
               if worst else
               "(b) the Hessian at Sigma's own sign pattern, hat basis, "
               "eta(0) = eta(pi/2) = 0")
        print(tag)
        print(f"    {'m':>6} {'dim':>5} {'lam_max':>13} {'lam_max/h':>12} "
              f"{'#(lam>0)':>9} {'lam_min':>13}")
        for mm in (m//2, m, 2*m):
            if mm % 2:
                continue
            B, M = hessian(mm, worst=worst)
            ev = np.linalg.eigvalsh(M)
            print(f"    {mm:6d} {B.dim:5d} {ev.max():13.5e} "
                  f"{ev.max()/B.h:12.5f} {int((ev>1e-9).sum()):9d} "
                  f"{ev.min():13.5e}")
        B, M = hessian(2*m, worst=worst)
        ev, U = np.linalg.eigh(M)
        print(f"    top 5: {', '.join(f'{v:+.3e}' for v in ev[-5:])}")
        if ev.max() > 1e-9:
            pk = B.keep[np.argmax(np.abs(U[:, -1]))]*B.h
            print(f"    ==> NOT <= 0.  lam_max = {ev.max():+.6e}, worst direction "
                  f"peaks at theta = {pk:.6f}")
            print(f"        (beta = {BETA:.6f}, pi/2 = {PI2:.6f}, "
                  f"pi-beta = {PI-BETA:.6f})\n")
        else:
            print(f"    ==> NEGATIVE DEFINITE.  lam_max = {ev.max():+.6e}; "
                  f"the L^2-normalised value lam_max/h is bounded away from 0.\n")


if __name__ == "__main__":
    main()
