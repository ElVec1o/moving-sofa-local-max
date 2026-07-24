"""The notch bulk form: per-arc Wirtinger identities + blind predictions.

PART 1 (symbolic proof).  In the moving frame p=<eta,mu>, q=<eta,nu>:
    delta A = p mu + p' nu,        delta A ^ delta A' = p(p+p'')
    delta B = delta A
    delta C = delta D = -q' mu + q nu,   wedge = q(q+q'')
    corner path:  eta ^ eta'  ==  0  for fixed-direction eta = e f(t)   (exact)
Also the envelope-speed identity in the rotating frame  x = R_t v + kappa:
    lambda_D := 2<x',mu> - <x'',nu>  =  -(v_2 + v_2'')
giving phase-wise closed forms (phase 1: +1/2; phase 2: b1+1-t/2; phase 3: -(c2+t)).

PART 2 (consequence).  For the normalized odd bump at beta in direction e:
    Q(eta_hat) = -(1/5) w^2 [ (chi_A+chi_B) <e,mu(beta)>^2
                            + (chi_C+chi_D) <e,nu(beta)>^2 ]  + o?(w^2)
with chi = fraction of int f'^2 inside the arc's parameter range (1 interior,
1/2 at an endpoint, 0 outside).  G-coefficient = Q/(2w^2).

chi table: b1=phi:        A1 C1 D1 B0  -> G = -0.1[<e,mu>^2 + 2<e,nu>^2]
           b2=theta_R:    A1 C1 D.5 B0 -> G = -0.1[<e,mu>^2 + 1.5<e,nu>^2]
           b3=pi/2-th_R:  A1 C1 D0 B.5 -> G = -0.1[1.5<e,mu>^2 + <e,nu>^2]
           b4=pi/2-phi:   A1 C1 D0 B1  -> G = -0.1[2<e,mu>^2 + <e,nu>^2]

Already verified: b1-x measured -0.10015 vs predicted -0.1001535 (5 digits,
parameter-free).  PART 3 makes BLIND predictions (printed before measuring):
b1-y and b4-y = -0.1998465; b3-x chi-form -0.1198287 (mirror of b2).
PART 4 probes the w->0 drift at b2-x: does G converge to the chi-form?
"""
from __future__ import annotations
import sys, os
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gerver_constants import solve_gerver_constants
from analytic_oracle import make_traj, area

DPS = 30


def part1_symbolic():
    import sympy as sp
    t = sp.Symbol('t', real=True)
    pf, qf = sp.Function('p')(t), sp.Function('q')(t)
    mu = sp.Matrix([sp.cos(t), sp.sin(t)]); nu = sp.Matrix([-sp.sin(t), sp.cos(t)])
    eta = pf*mu + qf*nu
    etap = eta.diff(t)
    wedge = lambda U, V: sp.simplify(U[0]*V[1] - U[1]*V[0])
    # arc variations
    dA = eta + (etap.dot(mu))*nu
    dC = eta - (etap.dot(nu))*mu
    okA = sp.simplify(wedge(dA, dA.diff(t)) - pf*(pf + pf.diff(t, 2))) == 0
    okC = sp.simplify(wedge(dC, dC.diff(t)) - qf*(qf + qf.diff(t, 2))) == 0
    # corner path, fixed direction
    e1, e2 = sp.symbols('e1 e2', real=True); f = sp.Function('f')(t)
    ef = sp.Matrix([e1*f, e2*f])
    okX = sp.simplify(wedge(ef, ef.diff(t))) == 0
    # rotating-frame lambda identity
    v1, v2 = sp.Function('v1')(t), sp.Function('v2')(t)
    R = sp.Matrix([[sp.cos(t), -sp.sin(t)], [sp.sin(t), sp.cos(t)]])
    x = R*sp.Matrix([v1, v2])
    xp = x.diff(t); xpp = x.diff(t, 2)
    lamD = 2*(xp.dot(mu)) - (xpp.dot(nu))
    okL = sp.simplify(lamD + v2 + v2.diff(t, 2)) == 0
    print("PART 1  symbolic proofs")
    print(f"  delta A ^ delta A' = p(p+p'')      : {'PROVED' if okA else 'FAIL'}")
    print(f"  delta C ^ delta C' = q(q+q'')      : {'PROVED' if okC else 'FAIL'}")
    print(f"  corner eta^eta' = 0 (fixed dir)    : {'PROVED' if okX else 'FAIL'}")
    print(f"  lambda_D = -(v2 + v2'')            : {'PROVED' if okL else 'FAIL'}")
    return okA and okC and okX and okL


def h2n(b, w):
    def eta2(t):
        s = (t - b)/w
        return (w*s*mp.e**(-s*s))**2
    def etapp2(t):
        s = (t - b)/w
        return ((1/w)*mp.e**(-s*s)*(4*s**3 - 6*s))**2
    lo, hi = b - 12*w, b + 12*w
    return mp.sqrt(mp.quad(eta2, [lo, b, hi]) + mp.quad(etapp2, [lo, b, hi]))


def Gcoef(p, beta, comp, w):
    """Richardson-extrapolated G-coefficient: G/eps^2 at eps->0."""
    beta = mp.mpf(beta); w = mp.mpf(w)
    nrm = h2n(beta, w)
    _, bk = area(make_traj(p, mp.mpf(0), beta, w, comp), p, dps=DPS)
    A0 = area(make_traj(p, mp.mpf(0), beta, w, comp), p, dps=DPS, b0=list(bk))[0]
    vals = {}
    b0 = list(bk)
    for es in ('0.1', '0.2'):
        eps = mp.mpf(es)
        A, b0n = area(make_traj(p, eps/nrm, beta, w, comp), p, dps=DPS, b0=b0)
        b0 = list(b0n)
        vals[es] = (A - A0)/(w*w*eps*eps)
    return 2*vals['0.1'] - vals['0.2'], vals


def main():
    ok = part1_symbolic()
    p, _ = solve_gerver_constants(working_dps=DPS, verbose=False)
    mp.mp.dps = DPS
    PHI = p['phi']; TR = p['theta']; PI2 = mp.pi/2
    lamD_TR = float(p['b1'] + 1 - TR/2)
    print(f"\n  lambda_D(theta_R-) = b1+1-theta_R/2 = {lamD_TR:+.6f}  (NONZERO)")

    import math
    c2, s2 = math.cos(float(PHI))**2, math.sin(float(PHI))**2
    cT, sT = math.cos(float(TR))**2, math.sin(float(TR))**2
    pred = {
        ('b1', 'y'): -0.1*(s2 + 2*c2),
        ('b4', 'y'): -0.1*(2*c2 + s2),
        ('b3', 'x'): -0.1*(1.5*sT + cT),
    }
    print("\nPART 3  BLIND predictions (printed before measurement):")
    for k, v in pred.items():
        print(f"  {k}: chi-form G = {v:+.7f}")
    locs = {'b1': PHI, 'b3': PI2 - TR, 'b4': PI2 - PHI}
    w = mp.mpf('0.005')
    print(f"\n  measurements (w={float(w)}):")
    for (loc, comp), v in pred.items():
        g, vals = Gcoef(p, locs[loc], comp, w)
        print(f"  {loc}-{comp}: measured G(eps->0) = {float(g):+.7f}   "
              f"predicted {v:+.7f}   diff {float(g)-v:+.5f}")

    print("\nPART 4  w-drift at b2-x  (chi-form limit candidate -0.1198287):")
    print(f"  {'w':>9} {'G(eps->0)':>12}")
    for ws in ('0.01', '0.005', '0.0025', '0.00125', '0.0006', '0.0003'):
        g, _ = Gcoef(p, TR, 'x', mp.mpf(ws))
        print(f"  {ws:>9} {float(g):>+12.7f}", flush=True)
    print("\n  drifting toward -0.11983 => chi-form exact in the limit, J -> 0;")
    print("  converging elsewhere     => residual junction term J != 0.")


if __name__ == "__main__":
    main()
