import sys, numpy as np, mpmath as mp
sys.path.insert(0,'/Users/vico/Documents/elvec1o/MATH_PAPER_5/algorithm/rigorous')
from gerver_constants import solve_gerver_constants, _xt_full
from analytic_oracle import area
DPS=25; p,_=solve_gerver_constants(working_dps=DPS,verbose=False); mp.mp.dps=DPS
a=np.load('/tmp/eta32_coeffs.npy')   # slope-free mode coefficients, k=3..32 x then y
ks=list(range(3,33))
terms=[]
for i,co in enumerate(a):
    comp = 0 if i<30 else 1
    k = ks[i%30]
    s = 1.0 if k%2==0 else -1.0
    al, be = -k*(1-s)/2.0, -k*(1+s)/4.0
    for (kk,cc) in ((k,co),(1,al*co),(2,be*co)):
        terms.append((comp,kk,cc))
# merge duplicate (comp,k)
from collections import defaultdict
m=defaultdict(float)
for c,k,v in terms: m[(c,k)]+=v
T=[(c,k,v) for (c,k),v in m.items() if abs(v)>1e-14]
def traj_factory(eps):
    eps=mp.mpf(eps)
    def traj(t):
        x,xp,xpp=_xt_full(t,p)
        e=[mp.mpf(0)]*6
        for c,k,v in T:
            s,sp,spp=mp.sin(2*k*t),2*k*mp.cos(2*k*t),-4*k*k*mp.sin(2*k*t)
            e[c]+=v*s; e[2+c]+=v*sp; e[4+c]+=v*spp
        return ((x[0]+eps*e[0],x[1]+eps*e[1]),(xp[0]+eps*e[2],xp[1]+eps*e[3]),
                (xpp[0]+eps*e[4],xpp[1]+eps*e[5]))
    return traj
_,bk=area(traj_factory(0),p,dps=DPS)
A0=area(traj_factory(0),p,dps=DPS,b0=list(bk))[0]
print("mpmath oracle along eta*(K=32 spurious direction), h-sweep of Rayleigh:")
for hs in ('2e-5','1e-5','5e-6'):
    h=mp.mpf(hs)
    gp=area(traj_factory(h),p,dps=DPS,b0=list(bk))[0]-A0
    gm=area(traj_factory(-h),p,dps=DPS,b0=list(bk))[0]-A0
    q=(gp+gm)/(h*h)
    print(f"  h={hs}: Q = {float(q):+.5f}   (Rust matrix gave +0.944; true-F must be <0)")
print("P32DONE")
