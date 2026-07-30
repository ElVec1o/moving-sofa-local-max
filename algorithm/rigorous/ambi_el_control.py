import sys
import sympy as sp, sys, math
import os
THIS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, THIS); sys.path.insert(0, os.path.dirname(THIS))
t = sp.symbols('t', real=True)
a1, f1, f2 = sp.symbols('a1 f1 f2', real=True, positive=True)
Fm1 = sp.cos(t) + sp.Rational(1,2)*sp.sin(t) - 1
Gm1 = (2*a1-1)*sp.sin(t) + sp.Rational(1,2)*sp.cos(t) - sp.Rational(1,2)
k6 = 1 - sp.Rational(4,3)*a1
Fm6 = f1*sp.cos(t/2)+f2*sp.sin(t/2)-1+k6*sp.cos(t)+sp.Rational(1,2)*sp.sin(t)
Gm6 = -f2*sp.cos(t/2)+f1*sp.sin(t/2)-1+sp.Rational(1,2)*sp.cos(t)-k6*sp.sin(t)
Fm5 = (1-sp.Rational(2,3)*a1)*sp.cos(t)+sp.Rational(1,2)*sp.sin(t)-sp.Rational(1,2)
Gm5 = (sp.Rational(8,3)*a1-1)*sp.sin(t)+sp.Rational(1,2)*sp.cos(t)-1

# (A) NUMERICAL CROSS-CHECK of every phase formula against the reference path
from ambi_hessian import H_and_dH, PI2
from sofa_romik2017_reference import A1_const, F1_const, F2_const, BETA
sub = {a1: A1_const, f1: F1_const, f2: F2_const}
print("(A) phase formulas vs the reference path H(theta)-1, H(theta+pi/2)-1")
worst = 0.0
for lab, Fm, Gm, lo, hi in (("1", Fm1, Gm1, 1e-6, BETA),
                            ("6", Fm6, Gm6, BETA, PI2-BETA),
                            ("5", Fm5, Gm5, PI2-BETA, PI2-1e-6)):
    for x in [lo+(hi-lo)*k/4 for k in range(1,4)]:
        F,_ = H_and_dH([x]); G,_ = H_and_dH([x+PI2])
        eF = abs(float(Fm.subs(sub).subs(t,x)) - (F[0]-1.0))
        eG = abs(float(Gm.subs(sub).subs(t,x)) - (G[0]-1.0))
        worst = max(worst, eF, eG)
    print(f"    phase {lab}: max |formula - reference| so far = {worst:.2e}")

def arms(Fm, Gm):
    return Gm - sp.diff(Fm,t), Fm + sp.diff(Gm,t), Fm*sp.tan(t)+Gm
def HpH2(Fm):
    H = Fm+1; return sp.simplify(H + sp.diff(H,t,2))

# (B) NEGATIVE CONTROL: deliberately wrong variants must NOT simplify to 0
print("\n(B) NEGATIVE CONTROL on sympy's simplify: perturbed equations must give nonzero")
A1,A2,SG = arms(Fm6,Gm6)
correct = HpH2(Fm6) - (A2 + (SG-A1)*sp.tan(t) - sp.diff(SG-A1,t))
variants = {
 "correct                     ": correct,
 "sign flip on (sig-a1) tan   ": HpH2(Fm6) - (A2 - (SG-A1)*sp.tan(t) - sp.diff(SG-A1,t)),
 "drop the a2 term            ": HpH2(Fm6) - ((SG-A1)*sp.tan(t) - sp.diff(SG-A1,t)),
 "drop the derivative term    ": HpH2(Fm6) - (A2 + (SG-A1)*sp.tan(t)),
 "a1 <-> a2 swapped           ": HpH2(Fm6) - (A1 + (SG-A2)*sp.tan(t) - sp.diff(SG-A2,t)),
 "H+H'' -> H-H''              ": sp.simplify((Fm6+1) - sp.diff(Fm6+1,t,2)) - (A2 + (SG-A1)*sp.tan(t) - sp.diff(SG-A1,t)),
}
for lab, e in variants.items():
    r = sp.simplify(sp.expand_trig(sp.simplify(e)))
    z = (r == 0)
    print(f"    {lab} -> {'ZERO' if z else 'nonzero'}"
          + ("" if z else f"  (e.g. at t=1: {float(r.subs(sub).subs(t,1)):+.6f})"))
print("\n  If only 'correct' is ZERO, simplify is discriminating and the six identities")
print("  of the previous run are genuine.")
