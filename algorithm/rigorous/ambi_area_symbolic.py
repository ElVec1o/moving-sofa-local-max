import sympy as sp
t, B = sp.symbols('t beta', positive=True)
a1, f1, f2 = sp.symbols('a1 f1 f2', positive=True)
S2 = sp.sqrt(2); k6 = 1 - sp.Rational(4,3)*a1
Fm1 = sp.cos(t) + sp.Rational(1,2)*sp.sin(t) - 1
Gm1 = (2*a1-1)*sp.sin(t) + sp.Rational(1,2)*sp.cos(t) - sp.Rational(1,2)
Fm6 = f1*sp.cos(t/2)+f2*sp.sin(t/2)-1+k6*sp.cos(t)+sp.Rational(1,2)*sp.sin(t)
Gm6 = -f2*sp.cos(t/2)+f1*sp.sin(t/2)-1+sp.Rational(1,2)*sp.cos(t)-k6*sp.sin(t)
Fm5 = (1-sp.Rational(2,3)*a1)*sp.cos(t)+sp.Rational(1,2)*sp.sin(t)-sp.Rational(1,2)
Gm5 = (sp.Rational(8,3)*a1-1)*sp.sin(t)+sp.Rational(1,2)*sp.cos(t)-1
P2 = sp.pi/2

# |C2| = int_0^pi (H^2 - H'^2) - H(0) - H(pi), H piecewise; shift the G-blocks
blocks = [(Fm1+1, 0, B), (Fm6+1, B, P2-B), (Fm5+1, P2-B, P2),
          (Gm1+1, 0, B), (Gm6+1, B, P2-B), (Gm5+1, P2-B, P2)]
C2 = 0
for H, lo, hi in blocks:
    C2 += sp.integrate(sp.expand_trig(sp.expand(H**2 - sp.diff(H,t)**2)), (t, lo, hi))
C2 = sp.simplify(C2 - (Fm1+1).subs(t,0) - (Gm5+1).subs(t,P2))

# V, with each region's sign pattern fixed
V = 0
for Fm, Gm, lo, hi, a2pos, a1neg in ((Fm1,Gm1,0,B,True,True),
                                     (Fm6,Gm6,B,P2-B,True,False),
                                     (Fm5,Gm5,P2-B,P2,False,False)):
    A1 = Gm - sp.diff(Fm,t); A2 = Fm + sp.diff(Gm,t); SG = Fm*sp.tan(t)+Gm
    integ = sp.Rational(1,2)*(SG-A1)**2
    if a2pos: integ += sp.Rational(1,2)*A2**2
    if a1neg: integ += -sp.Rational(1,2)*A1**2
    V += sp.integrate(sp.simplify(sp.expand_trig(sp.expand(sp.simplify(integ)))), (t, lo, hi))
Q = sp.simplify(C2 - 2*V)
target = 1 + 4*sp.tan(B)**2 + B
print("Q - (1 + 4 tan^2 beta + beta), before substituting the constant relations:")
res = sp.simplify(Q - target)
print(" ", sp.nsimplify(res, rational=False) if res.free_symbols else res)
# now impose the relations
u = 2*sp.tan(B)
rel = {f2: (1-S2)*f1,
       f1: (sp.Rational(4,3)*a1*sp.cos(B))/(sp.cos(B/2)+(1-S2)*sp.sin(B/2)),
       a1: 1/(4*sp.sin(B))}
res2 = res.subs(f2, rel[f2]).subs(f1, rel[f1]).subs(a1, rel[a1])
res2 = sp.simplify(sp.expand_trig(sp.simplify(res2)))
print("\nafter f2=(1-sqrt2)f1, f1 from the junction, a1 = 1/(4 sin beta):")
print(" ", res2)
print("\nnumeric check at beta = arctan(u/2), u^3+3u=2:")
uu = sp.nsolve(sp.Symbol('x')**3+3*sp.Symbol('x')-2, 0.596)
bb = sp.atan(uu/2)
print("  residual =", sp.N(res2.subs(B, bb), 30))
