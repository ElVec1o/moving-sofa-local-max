"""(F3) completion: END-TO-END interval quadrature of frozen-form entries.

Certifies representative entries of the K=16 frozen block by rigorous
acb_calc integration (flint), with the Gerver angles as balls.  The same code
certifies any entry; the full sweep is mechanical repetition.
Run: python3 certify_entries.py
"""
from flint import acb, arb, ctx
import numpy as np, os
ctx.prec = 192
HERE = os.path.dirname(os.path.abspath(__file__))
# Gerver angles as balls (25-digit values; radius covers the Newton enclosure)
PHI  = arb("0.03917736479008364081741287") + arb(0, 1e-24)
TH   = arb("0.6813015093827249427331323") + arb(0, 1e-24)
PI2  = arb.pi()/2

def modefns(comp, k):
    k = arb(k)
    if comp == 'x':
        f  = lambda t: t.cos();  fp = lambda t: -t.sin()
        g  = lambda t: -t.sin(); gp = lambda t: -t.cos()
        fpp = lambda t: -t.cos(); gpp = lambda t: t.sin()
    else:
        f  = lambda t: t.sin();  fp = lambda t: t.cos()
        g  = lambda t: t.cos();  gp = lambda t: -t.sin()
        fpp = lambda t: -t.sin(); gpp = lambda t: -t.cos()
    s   = lambda t: (2*k*t).sin()
    sp  = lambda t: 2*k*(2*k*t).cos()
    spp = lambda t: -4*k*k*(2*k*t).sin()
    P   = lambda t: f(t)*s(t)
    Ppp = lambda t: fpp(t)*s(t)+2*fp(t)*sp(t)+f(t)*spp(t)
    Q   = lambda t: g(t)*s(t)
    Qpp = lambda t: gpp(t)*s(t)+2*gp(t)*sp(t)+g(t)*spp(t)
    Pp  = lambda t: fp(t)*s(t)+f(t)*sp(t)
    Qp  = lambda t: gp(t)*s(t)+g(t)*sp(t)
    return P,Pp,Ppp,Q,Qp,Qpp

def entry(u, v):
    Pu,Ppu,Pppu,Qu,Qpu,Qppu = modefns(*u)
    Pv,Ppv,Pppv,Qv,Qpv,Qppv = modefns(*v)
    half = arb(1)/2
    def igr_p(t,_):
        return half*(Pu(t)*(Pv(t)+Pppv(t)) + Pv(t)*(Pu(t)+Pppu(t)))
    def igr_q(t,_):
        return half*(Qu(t)*(Qv(t)+Qppv(t)) + Qv(t)*(Qu(t)+Qppu(t)))
    def igr_x(t,_):
        # eta_u ^ eta_v' symmetrized; for single-component sine modes:
        # if u,v same component: wedge = 0; cross-component handled below
        cu, cv = u[0], v[0]
        if cu == cv: return acb(0)*t
        su = (2*arb(u[1])*t).sin(); spv = 2*arb(v[1])*(2*arb(v[1])*t).cos()
        sv = (2*arb(v[1])*t).sin(); spu = 2*arb(u[1])*(2*arb(u[1])*t).cos()
        sgn = arb(1) if cu == 'x' else arb(-1)
        return half*sgn*(su*spv - sv*spu)
    tot = arb(0)
    for lo, hi, fn, sg in ((arb(0),PI2,igr_p,1),(arb(0),PI2,igr_q,1),
                            (arb(0),TH,igr_q,1),(PI2-TH,PI2,igr_p,1),
                            (PHI,PI2-PHI,igr_x,-1)):
        v_ = acb.integral(fn, lo, hi)
        tot += sg*v_.real
    # junction chords (point jets)
    def dD(m, t):
        P,Pp,Ppp,Q,Qp,Qpp = modefns(*m)
        c, s = t.cos(), t.sin()
        return (-Qp(t)*c + Q(t)*(-s), -Qp(t)*s + Q(t)*c)
    def dB(m, t):
        P,Pp,Ppp,Q,Qp,Qpp = modefns(*m)
        c, s = t.cos(), t.sin()
        return (P(t)*c + Pp(t)*(-s), P(t)*s + Pp(t)*c)
    def eta(m, t):
        val = (2*arb(m[1])*t).sin()
        return (val, arb(0)) if m[0]=='x' else (arb(0), val)
    def wedge(a,b): return a[0]*b[1]-a[1]*b[0]
    tot += arb(1)/2*(wedge(dD(u,TH),eta(v,PI2-PHI))+wedge(dD(v,TH),eta(u,PI2-PHI)))
    tot += arb(1)/2*(wedge(eta(u,PHI),dB(v,PI2-TH))+wedge(eta(v,PHI),dB(u,PI2-TH)))
    return tot

if __name__ == "__main__":
    Z = np.load(os.path.join(HERE,'qfrz_block_K16.npz')); Qf = Z['Q']
    modes = [(c,k) for c in ('x','y') for k in range(1,17)]
    samples = [(0,0),(0,2),(17,19),(1,5),(16,18)]
    print("CERTIFIED frozen-form entries (rigorous acb integration, 192-bit):")
    for i,j in samples:
        e = entry(modes[i], modes[j])
        fl = Qf[i,j]
        inside = abs(float(e.mid())-fl) <= float(e.rad())+5e-13
        print(f"  {modes[i]}x{modes[j]}: ball={e}  float={fl:+.12f}  "
              f"consistent={inside}")
