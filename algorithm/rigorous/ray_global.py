"""Certified global bound along a ray: the miniature of the G3 machine.
On each subinterval [a,b]: junctions frozen at the midpoint; the frozen
reconstruction area is EXACTLY quadratic in eps, so the parabola through
(a, m, b) IS g_frozen; by the superset lemma it upper-bounds the true area
pointwise. Certify sup_[a,b] parabola < A*; subdivide otherwise."""
import subprocess, numpy as np
ASTAR=2.219531668871968
BIN='/Users/vico/Documents/elvec1o/MATH_PAPER_5/algorithm/rigorous/true_hessian'
def frozen3(terms_file, a, b):
    m=(a+b)/2
    out=subprocess.run([BIN,'fray',terms_file,str(m),str(a),str(m),str(b)],
                       capture_output=True,text=True).stdout.split()
    return [float(x) for x in out[-3:]]
def sup_parabola(a,b,fa,fm,fb):
    # exact quadratic through 3 points; sup over [a,b]
    m=(a+b)/2
    co=np.polyfit([a,m,b],[fa,fm,fb],2)
    xs=np.array([a,b] + ([-co[1]/(2*co[0])] if co[0]<0 else []))
    xs=xs[(xs>=a)&(xs<=b)]
    return max(np.polyval(co,x) for x in xs)
def certify(terms_file, lo, hi, margin=1e-6, maxdepth=18):
    stack=[(lo,hi,0)]; pieces=0; worst=-1e9
    while stack:
        a,b,d=stack.pop()
        fa,fm,fb=frozen3(terms_file,a,b)
        s=sup_parabola(a,b,fa,fm,fb)
        if s < ASTAR - margin:
            pieces+=1; worst=max(worst,s); continue
        if d>=maxdepth: return False,pieces,worst,(a,b)
        m=(a+b)/2
        stack.append((a,m,d+1)); stack.append((m,b,d+1))
    return True,pieces,worst,None
import sys
tf=sys.argv[1]; lo=float(sys.argv[2]); hi=float(sys.argv[3])
ok,pieces,worst,bad=certify(tf,lo,hi)
if ok:
    print(f"CERTIFIED: frozen upper envelope < A* on [{lo},{hi}]")
    print(f"  pieces: {pieces}   worst sup: {worst:.9f}  (A* = {ASTAR:.9f})")
    print(f"  => area(c_G + eps*eta) < A* for ALL eps in [{lo},{hi}] along this ray")
else:
    print(f"not certified; stuck near {bad} after {pieces} pieces")
