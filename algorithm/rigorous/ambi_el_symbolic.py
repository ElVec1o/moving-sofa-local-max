import sys
"""Symbolic verification of the Euler-Lagrange equations of Q at Sigma, phase by phase."""
import sympy as sp

t = sp.symbols('t', real=True)
a1, f1, f2 = sp.symbols('a1 f1 f2', real=True, positive=True)
S2 = sp.sqrt(2)

# F(t)-1 and G(t)-1 per phase, from the complex closed forms
# phase 1 [0,beta):  z = a1 e^{2it} - (1+i/2)e^{it} + (1-a1+i/2)
Fm1 = sp.cos(t) + sp.Rational(1,2)*sp.sin(t) - 1
Gm1 = (2*a1-1)*sp.sin(t) + sp.Rational(1,2)*sp.cos(t) - sp.Rational(1,2)
# phase 6 [beta,pi/2-beta]: z = (f1 - i f2) e^{3it/2} - (1+i)e^{it} + (1-(4/3)a1 + i/2)
k6 = 1 - sp.Rational(4,3)*a1
Fm6 = (f1*sp.cos(t/2) + f2*sp.sin(t/2) - 1 + k6*sp.cos(t)
       + sp.Rational(1,2)*sp.sin(t))
Gm6 = (-f2*sp.cos(t/2) + f1*sp.sin(t/2) - 1 + sp.Rational(1,2)*sp.cos(t)
       - k6*sp.sin(t))
# phase 5 (pi/2-beta,pi/2]: z = a1 e^{2it} - (1/2+i)e^{it} + (1-(5/3)a1 + i/2)
k5 = 1 - sp.Rational(5,3)*a1
Fm5 = (1 - sp.Rational(2,3)*a1)*sp.cos(t) + sp.Rational(1,2)*sp.sin(t) - sp.Rational(1,2)
Gm5 = (a1 + k5)*sp.sin(t)*(-1) + a1*sp.sin(t) - 1 + sp.Rational(1,2)*sp.cos(t)
Gm5 = sp.simplify((sp.Rational(8,3)*a1 - 1)*sp.sin(t) + sp.Rational(1,2)*sp.cos(t) - 1)

def arms(Fm, Gm):
    a1_ = Gm - sp.diff(Fm, t)
    a2_ = Fm + sp.diff(Gm, t)
    sg  = Fm*sp.tan(t) + Gm
    return a1_, a2_, sg

def HpH2(Fm):
    H = Fm + 1
    return sp.simplify(H + sp.diff(H, t, 2))

print("EULER-LAGRANGE EQUATIONS, SYMBOLIC, PHASE BY PHASE")
print("(a1, f1, f2 kept as free symbols; residual 0 means an identity in them)\n")

# ---- theta in (0, pi/2): H+H'' = a2^+ + (sig-a1) tan th - (sig-a1)' + (a1^-)'
cases = [("[0,beta)  F1/G1", Fm1, Gm1, True,  True),
         ("[b,pi/2-b] F6/G6", Fm6, Gm6, True,  False),
         ("(pi/2-b,pi/2] F5/G5", Fm5, Gm5, False, False)]
for lab, Fm, Gm, a2pos, a1neg in cases:
    A1, A2, SG = arms(Fm, Gm)
    rhs = (SG - A1)*sp.tan(t) - sp.diff(SG - A1, t)
    if a2pos: rhs += A2
    if a1neg: rhs += sp.diff(-A1, t)
    res = sp.simplify(sp.expand_trig(sp.simplify(HpH2(Fm) - rhs)))
    print(f"  theta in {lab:22s}  residual = {res}")

# ---- theta in (pi/2, pi): H+H'' = -(a2^+)'(s) + a1^-(s)
print()
shift = [("(pi/2,pi/2+b) from G1", Fm1, Gm1, True,  True),
         ("(pi/2+b,pi-b) from G6", Fm6, Gm6, True,  False),
         ("(pi-b,pi]     from G5", Fm5, Gm5, False, False)]
for lab, Fm, Gm, a2pos, a1neg in shift:
    A1, A2, SG = arms(Fm, Gm)
    lhs = sp.simplify((Gm+1) + sp.diff(Gm+1, t, 2))
    rhs = 0
    if a2pos: rhs += -sp.diff(A2, t)
    if a1neg: rhs += -A1
    res = sp.simplify(sp.expand_trig(sp.simplify(lhs - rhs)))
    print(f"  theta in {lab:22s}  residual = {res}")
