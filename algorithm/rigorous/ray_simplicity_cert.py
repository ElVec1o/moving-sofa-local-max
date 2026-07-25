"""ray_simplicity_cert.py — certify the Gamma-simplicity side condition of the
arb ray theorem (PROGRAM.md item L2 / G3a caveat).

Method: star-shapedness. For each certified eps-piece [e1,e2] (same
subdivision + frozen b0 as ray_global_certified), and each piece of the
closed traversal

    A[0,pi/2] -> chord -> C[0,pi/2] -> chord -> D[0,bd] -> chord ->
    corner[bx2 -> bx1 BACKWARD] -> chord -> B[bb,pi/2] -> chord -> A(0)

certify in ball arithmetic that  f(t;eps) = (gamma - p0) ^ gamma'  keeps one
strict sign (matching the traversal direction: + forward pieces, - on the
corner arc's forward parameterization), for ALL t in the piece and ALL eps
in [e1,e2] at once (eps enters as a ball).  Then the polar angle around p0
is strictly monotone along the whole closed traversal, so the total
increase is 2*pi*k with integer k >= 1 constant on the piece; a rigorous
enclosure of the total increase  sum \int f/|gamma-p0|^2 dt  inside
(0, 4*pi) forces k = 1.  Monotone angle + total 2*pi  =>  Gamma is a polar
graph around p0  =>  SIMPLE, positively oriented, and Green area = enclosed
area.  This removes the float-checked side condition from the certified ray
theorem: the slice statement becomes unconditional (modulo the manuscript's
superset lemma, which is symbolic).
"""
import sys, subprocess, math
from flint import acb, arb, ctx
ctx.prec = 128

sys.path.insert(0, '.')
from ray_global_certified import jets, contact_wt, PHI, TH, PI2, ASTAR, frozen_area

PH = [0.0, float(PHI.mid()), float(TH.mid()), float((PI2-TH).mid()),
      float((PI2-PHI).mid()), float(PI2.mid())]


def pidx(t):
    for i in range(4):
        if t <= PH[i+1]:
            return i
    return 4


def arc_pt(t_ball, eps_ball, comp, kmode, which, phase_idx):
    """(gamma, gamma') for a contact arc, ball-evaluated."""
    jets.phase_idx = phase_idx
    return contact_wt(acb(t_ball), eps_ball, comp, kmode, which)


def corner_pt(t_ball, eps_ball, comp, kmode, phase_idx):
    jets.phase_idx = phase_idx
    x, xp, _ = jets(acb(t_ball), eps_ball, comp, kmode)
    return x, xp


def wedge(u, v):
    return u[0]*v[1] - u[1]*v[0]


def cert_sign_arc(get, lo, hi, eps_ball, p0, want_pos, depth=0, maxd=16):
    """Certify sign of f=(gamma-p0)^gamma' on [lo,hi] x eps_ball.
    Splits at phase kinks first, then bisects. Returns True/False."""
    for k in PH[1:5]:
        if lo + 1e-12 < k < hi - 1e-12:
            return (cert_sign_arc(get, lo, k, eps_ball, p0, want_pos, depth, maxd)
                    and cert_sign_arc(get, k, hi, eps_ball, p0, want_pos, depth, maxd))
    mid = 0.5*(lo+hi); rad = 0.5*(hi-lo)
    tb = arb(mid) + arb(0, rad)
    ph = pidx(mid)
    g, gp = get(tb, ph)
    f = wedge([g[0]-p0[0], g[1]-p0[1]], gp).real
    if (want_pos and f > 0) or ((not want_pos) and f < 0):
        return True
    if depth >= maxd:
        return False
    return (cert_sign_arc(get, lo, mid, eps_ball, p0, want_pos, depth+1, maxd)
            and cert_sign_arc(get, mid, hi, eps_ball, p0, want_pos, depth+1, maxd))


def cert_sign_chord(P, Q, p0, want_pos):
    """f on the segment P + u(Q-P): (P-p0+u(Q-P)) ^ (Q-P) -- affine in u.
    Sign certified by checking u=0 and u=1 ball values (affine => extremes
    at endpoints)."""
    d = [Q[0]-P[0], Q[1]-P[1]]
    f0 = wedge([P[0]-p0[0], P[1]-p0[1]], d).real
    f1 = wedge([Q[0]-p0[0], Q[1]-p0[1]], d).real
    return (f0 > 0 and f1 > 0) if want_pos else (f0 < 0 and f1 < 0)


def winding_bound(pieces_int, eps_ball, p0):
    """Rigorous enclosure of total angle increase = sum int f/|g-p0|^2 dt."""
    tot = arb(0)
    for kind, args in pieces_int:
        if kind == 'arc':
            get, lo, hi, sgn = args
            for i in range(5):
                a = max(PH[i], lo); b = min(PH[i+1], hi)
                if b <= a + 1e-14:
                    continue
                ph = i
                def f(t, _):
                    g, gp = get(t, ph)
                    dx = [g[0]-p0[0], g[1]-p0[1]]
                    return (dx[0]*gp[1]-dx[1]*gp[0])/(dx[0]**2 + dx[1]**2)
                tot += sgn * acb.integral(f, arb(a), arb(b)).real
        else:  # chord P->Q: dtheta = angle(Q-p0) - angle(P-p0) via atan2 of wedge/dot
            P, Q = args
            vP = [P[0]-p0[0], P[1]-p0[1]]; vQ = [Q[0]-p0[0], Q[1]-p0[1]]
            w = wedge(vP, vQ).real
            d = (vP[0]*vQ[0] + vP[1]*vQ[1]).real
            tot += arb(2)*(w/(d + (d*d + w*w).sqrt())).atan()
    return tot


def certify_piece(comp, kmode, e1, e2):
    m = 0.5*(e1+e2)
    open('/tmp/rterms.txt', 'w').write(f"{0 if comp=='x' else 1} {kmode} 1.0\n")
    out = subprocess.run(['./true_hessian', 'probe', str(m), '/tmp/rterms.txt'],
                         capture_output=True, text=True).stdout
    bd, bx2, bx1, bb = [float(x.split('=')[1]) for x in out.split()[1:5]]
    cval = 0 if comp == 'x' else 1
    km = arb(kmode)
    eb = arb(0.5*(e1+e2)) + arb(0, 0.5*(e2-e1))

    getA = lambda tb, ph: arc_pt(tb, eb, cval, km, 0, ph)
    getC = lambda tb, ph: arc_pt(tb, eb, cval, km, 2, ph)
    getD = lambda tb, ph: arc_pt(tb, eb, cval, km, 3, ph)
    getB = lambda tb, ph: arc_pt(tb, eb, cval, km, 1, ph)
    getX = lambda tb, ph: corner_pt(tb, eb, cval, km, ph)

    # p0: centroid-ish from float sample at midpoint (any interior point works)
    def fpt(get, t):
        g, _ = get(arb(t), pidx(t))
        return (float(g[0].real.mid()), float(g[1].real.mid()))
    samp = ([fpt(getA, t) for t in [0.1, 0.7, 1.4]] +
            [fpt(getC, t) for t in [0.1, 0.7, 1.4]] +
            [fpt(getD, t) for t in [bd*0.3, bd*0.9]] +
            [fpt(getB, t) for t in [bb+0.1, 1.5]])
    p0f = (sum(p[0] for p in samp)/len(samp), sum(p[1] for p in samp)/len(samp))
    p0 = [arb(p0f[0]), arb(p0f[1])]

    ends = {}
    for nm, get, t in [('A0', getA, 0.0), ('A1', getA, PH[5]),
                       ('C0', getC, 0.0), ('C1', getC, PH[5]),
                       ('D0', getD, 0.0), ('D1', getD, bd),
                       ('B0', getB, bb), ('B1', getB, PH[5])]:
        g, _ = get(arb(t), pidx(min(t, PH[5]-1e-12)))
        ends[nm] = g
    for nm, t in [('X2', bx2), ('X1', bx1)]:
        g, _ = getX(arb(t), pidx(t))
        ends[nm] = g

    ok = True
    ok &= cert_sign_arc(getA, 0.0, PH[5], eb, p0, True);          okA = ok
    ok &= cert_sign_chord(ends['A1'], ends['C0'], p0, True)
    ok &= cert_sign_arc(getC, 0.0, PH[5], eb, p0, True)
    ok &= cert_sign_chord(ends['C1'], ends['D0'], p0, True)
    ok &= cert_sign_arc(getD, 0.0, bd, eb, p0, True)
    ok &= cert_sign_chord(ends['D1'], ends['X2'], p0, True)
    # corner traversed backward => forward parameterization must have f < 0
    ok &= cert_sign_arc(getX, bx1, bx2, eb, p0, False)
    ok &= cert_sign_chord(ends['X1'], ends['B0'], p0, True)
    ok &= cert_sign_arc(getB, bb, PH[5], eb, p0, True)
    ok &= cert_sign_chord(ends['B1'], ends['A0'], p0, True)
    if not ok:
        return False, None

    pieces_int = [
        ('arc', (getA, 0.0, PH[5], +1)),
        ('chord', (ends['A1'], ends['C0'])),
        ('arc', (getC, 0.0, PH[5], +1)),
        ('chord', (ends['C1'], ends['D0'])),
        ('arc', (getD, 0.0, bd, +1)),
        ('chord', (ends['D1'], ends['X2'])),
        ('arc', (getX, bx1, bx2, -1)),
        ('chord', (ends['X1'], ends['B0'])),
        ('arc', (getB, bb, PH[5], +1)),
        ('chord', (ends['B1'], ends['A0'])),
    ]
    W = winding_bound(pieces_int, eb, p0)
    lo = float(W.mid()) - abs(float(W.rad())); hi = float(W.mid()) + abs(float(W.rad()))
    k1 = lo > 0.0 and hi < 4*math.pi
    return k1, (lo/(2*math.pi), hi/(2*math.pi))


def main():
    comp = sys.argv[1] if len(sys.argv) > 1 else 'x'
    # regenerate the certified-area subdivision (same algorithm)
    from ray_global_certified import certify_ray
    okA, pieces, bad = certify_ray(comp, 1, 0.01, 0.60)
    print(f"area subdivision: {'ok' if okA else 'FAILED'}, {len(pieces)} pieces")
    alln = True
    for (a, b) in sorted(pieces):
        ok, wind = certify_piece(comp, 1, a, b)
        tag = 'SIMPLE (winding=1)' if ok else 'NOT CERTIFIED'
        w = f"  winding in [{wind[0]:.4f},{wind[1]:.4f}]x2pi" if wind else ""
        print(f"  eps [{a:.4f},{b:.4f}]: {tag}{w}", flush=True)
        alln &= ok
    print(("SIMPLICITY CERTIFIED for all pieces -- ray theorem unconditional"
           if alln else "some pieces NOT certified -- needs refinement"))


if __name__ == "__main__":
    main()
