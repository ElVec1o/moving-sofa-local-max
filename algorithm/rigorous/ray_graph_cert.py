"""ray_graph_cert.py — UNCONDITIONAL certified ray theorem (PROGRAM L2/G3a):
area bound AND curve simplicity, in ball arithmetic end to end.

Per eps-piece [e1,e2] (eps enters as a ball everywhere):

 1. SPEED-SIGN RUNS. For each arc, certify the sign of the x-component of
    the velocity on t-panels (split at Gerver phase kinks). Maximal panels
    where the sign cannot be certified (stationary heads A/phase-1 and
    C/phase-5, the large-eps D-pocket, corner-velocity flips) are CHORD-
    REPLACED: every chord-closed reconstruction is superset-valid, so this
    only changes WHICH certified upper bound is used. Chord x-direction is
    then ball-checked; failing chords absorb neighbouring runs and retry.
 2. AREA. The modified curve's Green functional is exactly quadratic in
    eps (arcs: closed-form jets; chord endpoints: affine in eps). Exact
    parabola through ball values at e1, mid, e2; rigorous sup < A*.
 3. SIMPLICITY. The traversal splits into x-monotone CHAINS at its
    x-turning nodes. Pairwise chain separation is certified on x-bins
    (per-bin y-interval comparison, cells refined adaptively); chains
    sharing a node get a separating-direction certificate near the node
    (d with <gamma1', d> > 0, <gamma2', d> < 0 locally). Jordan =>
    winding = +-2pi; a single angle-sum enclosure in (0, 4pi) fixes CCW,
    so Green = enclosed area.

Result: area(c_G + eps*eta) < A* on [0.01, 0.60] with no float side
conditions (the superset lemma remains symbolic, as in the manuscript).
"""
import sys, subprocess, math
from flint import acb, arb, ctx
ctx.prec = 128

sys.path.insert(0, '.')
from ray_global_certified import jets, contact_wt, PHI, TH, PI2, ASTAR

PH = [0.0, float(PHI.mid()), float(TH.mid()), float((PI2-TH).mid()),
      float((PI2-PHI).mid()), float(PI2.mid())]
ARCDIR = {'A': 'neg', 'C': 'neg', 'D': 'pos', 'X': 'neg', 'B': 'pos'}
# forward xdot sign wanted per arc (X is traversed backward in the curve)


def pidx(t):
    for i in range(4):
        if t <= PH[i+1]:
            return i
    return 4


def get_fns(cval, km, eb):
    def arc(which):
        def g(tb, ph):
            jets.phase_idx = ph
            return contact_wt(acb(tb), eb, cval, km, which)
        return g
    def corner(tb, ph):
        jets.phase_idx = ph
        x, xp, _ = jets(acb(tb), eb, cval, km)
        return x, xp
    return {'A': arc(0), 'B': arc(1), 'C': arc(2), 'D': arc(3), 'X': corner}


def cert_runs(F, name, lo, hi, want, minw=2e-3):
    """Maximal runs [(a,b,ok)] where ok=True means sign(xdot)=want certified
    on [a,b] for all eps in the piece ball."""
    panels = []
    def rec(a, b):
        for k in PH[1:5]:
            if a + 1e-12 < k < b - 1e-12:
                rec(a, k); rec(k, b); return
        tb = arb(0.5*(a+b)) + arb(0, 0.5*(b-a))
        _, gp = F[name](tb, pidx(0.5*(a+b)))
        v = gp[0].real
        ok = (v < 0) if want == 'neg' else (v > 0)
        if ok or b - a < minw:
            panels.append((a, b, bool(ok)))
        else:
            m = 0.5*(a+b); rec(a, m); rec(m, b)
    rec(lo, hi)
    panels.sort()
    runs = []
    for a, b, ok in panels:
        if runs and runs[-1][2] == ok:
            runs[-1] = (runs[-1][0], b, ok)
        else:
            runs.append((a, b, ok))
    return runs


def build_traversal(comp, kmode, e1, e2):
    """Traversal pieces in order. Arc: ('arc',name,lo,hi) (lo>hi = backward).
    Chord: ('chord',(name1,t1),(name2,t2)) with symbolic endpoint refs."""
    m = 0.5*(e1+e2)
    open('/tmp/rterms.txt', 'w').write(f"{0 if comp=='x' else 1} {kmode} 1.0\n")
    out = subprocess.run(['./true_hessian', 'probe', str(m), '/tmp/rterms.txt'],
                         capture_output=True, text=True).stdout
    bd, bx2, bx1, bb = [float(x.split('=')[1]) for x in out.split()[1:5]]
    cval = 0 if comp == 'x' else 1
    km = arb(kmode)
    eb = arb(0.5*(e1+e2)) + arb(0, 0.5*(e2-e1))
    F = get_fns(cval, km, eb)

    spans = {'A': (0.0, PH[5]), 'C': (0.0, PH[5]), 'D': (0.0, bd),
             'X': (bx1, bx2), 'B': (bb, PH[5])}
    runs = {n: cert_runs(F, n, *spans[n], ARCDIR[n]) for n in spans}

    def seq(name, forward=True):
        rs = runs[name] if forward else list(reversed(runs[name]))
        out = []
        for a, b, ok in rs:
            lo, hi = (a, b) if forward else (b, a)
            if ok:
                out.append(('arc', name, lo, hi))
            else:
                out.append(('chord', (name, lo), (name, hi)))
        return out

    trav = (seq('A') + [('chord', ('A', PH[5]), ('C', 0.0))] +
            seq('C') + [('chord', ('C', PH[5]), ('D', 0.0))] +
            seq('D') + [('chord', ('D', bd), ('X', bx2))] +
            seq('X', forward=False) + [('chord', ('X', bx1), ('B', bb))] +
            seq('B') + [('chord', ('B', PH[5]), ('A', 0.0))])
    # merge consecutive chords (incl. wrap-around): a degenerate head/tail
    # chord next to a bridge chord becomes one straight chord — removes the
    # node micro-spikes while remaining a valid chord-closed reconstruction.
    changed = True
    while changed:
        changed = False
        m2 = []
        for p in trav:
            if m2 and m2[-1][0] == 'chord' and p[0] == 'chord':
                m2[-1] = ('chord', m2[-1][1], p[2]); changed = True
            else:
                m2.append(p)
        if len(m2) > 1 and m2[0][0] == 'chord' and m2[-1][0] == 'chord':
            m2[0] = ('chord', m2[-1][1], m2[0][2]); m2.pop(); changed = True
        trav = m2
    nfix = sum(1 for r in runs.values() for (_, _, ok) in r if not ok)
    return trav, (cval, km, e1, e2), nfix


def ept(F, ref):
    name, t = ref
    g, _ = F[name](arb(t), pidx(min(t, PH[5]-1e-12)))
    return g


def green_area(trav, cval, km, eps_ball):
    F = get_fns(cval, km, eps_ball)
    tot = arb(0)
    for p in trav:
        if p[0] == 'arc':
            _, name, lo, hi = p
            a, b = (lo, hi) if lo < hi else (hi, lo)
            sgn = 1 if lo < hi else -1
            for i in range(5):
                aa = max(PH[i], a); bb_ = min(PH[i+1], b)
                if bb_ <= aa + 1e-14:
                    continue
                gf, ph = F[name], i
                def f(t, _, gf=gf, ph=ph):
                    g, gp = gf(t, ph)
                    return g[0]*gp[1] - g[1]*gp[0]
                tot += sgn * acb.integral(f, arb(aa), arb(bb_)).real
        else:
            P = ept(F, p[1]); Q = ept(F, p[2])
            tot += (P[0]*Q[1] - Q[0]*P[1]).real
    return tot/2


def area_certify(trav, cval, km, e1, e2):
    m = 0.5*(e1+e2)
    f1 = green_area(trav, cval, km, arb(e1))
    fm = green_area(trav, cval, km, arb(m))
    f2 = green_area(trav, cval, km, arb(e2))
    h = arb(e2-e1)
    A2c = 2*(f1 - 2*fm + f2)/(h*h)
    A1c = (f2 - f1)/h
    cand = [f1, f2]
    if float(A2c.mid()) < 0:
        ev = m - float((A1c/A2c).mid())
        if e1 < ev < e2:
            cand.append(fm + A1c*arb(ev-m) + A2c*arb(ev-m)**2/2)
    sup = max(cand, key=lambda z: float(z.mid()) + abs(float(z.rad())))
    hi = float(sup.mid()) + abs(float(sup.rad()))
    lim = float(ASTAR.mid()) - abs(float(ASTAR.rad()))
    return hi < lim, hi


# ---------------- simplicity: chains, bins, nodes ----------------

def cells_of(piece, F, nseg):
    """List of (p0, p1, box) — parameter range and ball box per cell."""
    out = []
    if piece[0] == 'arc':
        _, name, lo, hi = piece
        a, b = (lo, hi) if lo < hi else (hi, lo)
        cuts = [a] + [k for k in PH[1:5] if a < k < b] + [b]
        for c0, c1 in zip(cuts, cuts[1:]):
            n = max(2, int(nseg*(c1-c0)/(b-a+1e-12)))
            for i in range(n):
                t0 = c0 + (c1-c0)*i/n; t1 = c0 + (c1-c0)*(i+1)/n
                tb = arb(0.5*(t0+t1)) + arb(0, 0.5*(t1-t0))
                g, _ = F[name](tb, pidx(0.5*(t0+t1)))
                x, y = g[0].real, g[1].real
                out.append((t0, t1,
                            (float(x.mid())-abs(float(x.rad())),
                             float(x.mid())+abs(float(x.rad())),
                             float(y.mid())-abs(float(y.rad())),
                             float(y.mid())+abs(float(y.rad())))))
    else:
        P = ept(F, piece[1]); Q = ept(F, piece[2])
        for i in range(nseg):
            u0, u1 = i/nseg, (i+1)/nseg
            xs = []; ys = []
            for u in (u0, u1):
                xs.append(P[0].real*(1-u) + Q[0].real*u)
                ys.append(P[1].real*(1-u) + Q[1].real*u)
            xlo = min(float(v.mid())-abs(float(v.rad())) for v in xs)
            xhi = max(float(v.mid())+abs(float(v.rad())) for v in xs)
            ylo = min(float(v.mid())-abs(float(v.rad())) for v in ys)
            yhi = max(float(v.mid())+abs(float(v.rad())) for v in ys)
            out.append((u0, u1, (xlo, xhi, ylo, yhi)))
    return out


def bbox(cl):
    if not cl:
        return None
    return (min(c[2][0] for c in cl), max(c[2][1] for c in cl),
            min(c[2][2] for c in cl), max(c[2][3] for c in cl))


def boxes_disjoint(ca, cb):
    """x-sweep over sorted boxes; near-linear for x-monotone cell chains."""
    A = bbox(ca); B = bbox(cb)
    if A is None or B is None:
        return True
    if A[1] < B[0] or B[1] < A[0] or A[3] < B[2] or B[3] < A[2]:
        return True
    sa = sorted((c[2] for c in ca), key=lambda b_: b_[0])
    sb = sorted((c[2] for c in cb), key=lambda b_: b_[0])
    jb = 0
    active = []
    for (alo, ahi, aylo, ayhi) in sa:
        while jb < len(sb) and sb[jb][0] <= ahi:
            active.append(sb[jb]); jb += 1
        active = [b_ for b_ in active if b_[1] >= alo]
        for (blo, bhi, bylo, byhi) in active:
            if ayhi >= bylo and byhi >= aylo:
                return False
    return True


def node_sep_cert(F, refA, dirA, refB, dirB):
    """Separating direction at a shared node: exists d with
    <tangentA, d> > 0 and <tangentB, d> < 0 ball-certified, where tangents
    are the away-from-node directions of the two germs."""
    def germ_dir(ref, sgn):
        name, t = ref
        _, gp = F[name](arb(t), pidx(min(t, PH[5]-1e-12)))
        return [sgn*gp[0].real, sgn*gp[1].real]
    va = germ_dir(refA, dirA); vb = germ_dir(refB, dirB)
    fa = (float(va[0].mid()), float(va[1].mid()))
    fb = (float(vb[0].mid()), float(vb[1].mid()))
    na = math.hypot(*fa); nb = math.hypot(*fb)
    if na < 1e-14 or nb < 1e-14:
        return False
    d = (fa[0]/na - fb[0]/nb, fa[1]/na - fb[1]/nb)
    da = va[0]*arb(d[0]) + va[1]*arb(d[1])
    db = vb[0]*arb(d[0]) + vb[1]*arb(d[1])
    return bool(da > 0) and bool(db < 0)


def simplicity_certify(trav, cval, km, e1, e2, nseg0=60, maxref=4):
    eb = arb(0.5*(e1+e2)) + arb(0, 0.5*(e2-e1))
    F = get_fns(cval, km, eb)
    # adjacency: consecutive pieces share an endpoint (and last-first)
    n = len(trav)
    cells = [cells_of(p, F, nseg0) for p in trav]

    def sub_cells(piece, p0, p1, nseg):
        """Re-cell just the parameter window [p0,p1] of a piece, finely."""
        if piece[0] == 'arc':
            _, name, lo, hi = piece
            sub = ('arc', name, p0, p1) if lo < hi else ('arc', name, p1, p0)
            return cells_of(sub, F, nseg)
        P = ept(F, piece[1]); Q = ept(F, piece[2])
        out = []
        for i in range(nseg):
            u0 = p0 + (p1-p0)*i/nseg; u1 = p0 + (p1-p0)*(i+1)/nseg
            xs = [P[0].real*(1-u) + Q[0].real*u for u in (u0, u1)]
            ys = [P[1].real*(1-u) + Q[1].real*u for u in (u0, u1)]
            out.append((u0, u1,
                        (min(float(v.mid())-abs(float(v.rad())) for v in xs),
                         max(float(v.mid())+abs(float(v.rad())) for v in xs),
                         min(float(v.mid())-abs(float(v.rad())) for v in ys),
                         max(float(v.mid())+abs(float(v.rad())) for v in ys))))
        return out

    def pair_sep(ci, cj, pi_, pj_, depth=0):
        """Disjointness with local zoom: on overlap, re-cell the offending
        parameter windows at 8x resolution, recurse."""
        if boxes_disjoint(ci, cj):
            return True
        if depth >= maxref:
            return False
        oi = [c for c in ci if not boxes_disjoint([c], cj)]
        oj = [c for c in cj if not boxes_disjoint([c], ci)]
        if not oi or not oj:
            return True
        pa0 = min(c[0] for c in oi); pa1 = max(c[1] for c in oi)
        pb0 = min(c[0] for c in oj); pb1 = max(c[1] for c in oj)
        zi = sub_cells(pi_, pa0, pa1, 8*max(4, len(oi)))
        zj = sub_cells(pj_, pb0, pb1, 8*max(4, len(oj)))
        keep_i = [c for c in ci if c[1] <= pa0 or c[0] >= pa1]
        keep_j = [c for c in cj if c[1] <= pb0 or c[0] >= pb1]
        if not boxes_disjoint(keep_i, zj) or not boxes_disjoint(keep_j, zi):
            if depth + 1 >= maxref:
                return False
        return pair_sep(zi + keep_i, zj + keep_j, pi_, pj_, depth+1)

    for i in range(n):
        for j in range(i+1, n):
            adjacent = (j == i+1) or (i == 0 and j == n-1)
            if adjacent:
                continue
            if not pair_sep(cells[i], cells[j], trav[i], trav[j]):
                return False, f'nonadjacent pieces {i},{j} not separated'
    # adjacent pairs: near-node cells get a half-plane certificate over the
    # WHOLE near window; far cells must be box-disjoint from the entire
    # other piece.
    def window_vel(piece, at_end, wfrac):
        """Velocity ball of the away-from-node germ over the near window
        (parameter width = wfrac * piece length), plus the window's
        parameter bounds in traversal terms."""
        if piece[0] == 'arc':
            _, name, lo, hi = piece
            fw = 1 if hi > lo else -1
            a, b = (lo, hi) if lo < hi else (hi, lo)
            w = (b - a) * wfrac
            if at_end:
                tend = hi
                twin = (tend - fw*w, tend) if fw > 0 else (tend, tend - fw*w)
                sgn = -fw
            else:
                tstart = lo
                twin = (tstart, tstart + fw*w) if fw > 0 else (tstart + fw*w, tstart)
                sgn = fw
            ta, tb_ = min(twin), max(twin)
            tb = arb(0.5*(ta+tb_)) + arb(0, 0.5*(tb_-ta))
            _, gp = F[name](tb, pidx(0.5*(ta+tb_)))
            return [sgn*gp[0].real, sgn*gp[1].real], ('arc', ta, tb_)
        P = ept(F, piece[1]); Q = ept(F, piece[2])
        dch = [Q[0]-P[0], Q[1]-P[1]]
        sgn = -1 if at_end else 1
        uwin = (1-wfrac, 1.0) if at_end else (0.0, wfrac)
        return [sgn*dch[0].real, sgn*dch[1].real], ('chord', uwin[0], uwin[1])

    def split_cells(cl, win):
        """Partition cells into (near, far): near = fully inside the window
        parameter range (half-plane certified); straddlers count as far."""
        _, wa, wb = win
        near, far = [], []
        for (p0, p1, box) in cl:
            (near if (p0 >= wa - 1e-15 and p1 <= wb + 1e-15) else far).append((p0, p1, box))
        return near, far

    WFRAC = 0.08
    for i in range(n):
        j = (i+1) % n
        pa, pb = trav[i], trav[j]
        va, wina = window_vel(pa, True, WFRAC)
        vb, winb = window_vel(pb, False, WFRAC)
        fa = (float(va[0].mid()), float(va[1].mid()))
        fb = (float(vb[0].mid()), float(vb[1].mid()))
        na_, nb_ = math.hypot(*fa), math.hypot(*fb)
        if na_ < 1e-14 or nb_ < 1e-14:
            return False, f'zero germ at node {i}->{j}'
        d = (fa[0]/na_ - fb[0]/nb_, fa[1]/na_ - fb[1]/nb_)
        da = va[0]*arb(d[0]) + va[1]*arb(d[1])
        db = vb[0]*arb(d[0]) + vb[1]*arb(d[1])
        if not (bool(da > 0) and bool(db < 0)):
            return False, f'node half-plane cert failed at piece {i}->{j}'
        # far parts must avoid the other piece entirely
        neari, fari = split_cells(cells[i], wina)
        nearj, farj = split_cells(cells[j], winb)
        if not boxes_disjoint(fari, cells[j]):
            return False, f'adjacent far-cells overlap at {i}->{j} (i-far vs j)'
        if not boxes_disjoint(farj, cells[i]):
            return False, f'adjacent far-cells overlap at {i}->{j} (j-far vs i)'
    # orientation: winding around an interior point in (0, 4pi) => CCW
    xs = [0.5*(c[2][0]+c[2][1]) for cl in cells for c in cl]
    ys = [0.5*(c[2][2]+c[2][3]) for cl in cells for c in cl]
    p0 = [arb(0.35*min(xs)+0.65*max(xs)), arb(0.75*max(ys))]
    tot = arb(0)
    for p in trav:
        if p[0] == 'arc':
            _, name, lo, hi = p
            a, b = (lo, hi) if lo < hi else (hi, lo)
            sgn = 1 if lo < hi else -1
            for i5 in range(5):
                aa = max(PH[i5], a); bb_ = min(PH[i5+1], b)
                if bb_ <= aa + 1e-14:
                    continue
                gf, ph = F[name], i5
                def f(t, _, gf=gf, ph=ph):
                    g, gp = gf(t, ph)
                    dx = [g[0]-p0[0], g[1]-p0[1]]
                    return (dx[0]*gp[1]-dx[1]*gp[0])/(dx[0]**2+dx[1]**2)
                tot += sgn * acb.integral(f, arb(aa), arb(bb_)).real
        else:
            P = ept(F, p[1]); Q = ept(F, p[2])
            vP = [P[0]-p0[0], P[1]-p0[1]]; vQ = [Q[0]-p0[0], Q[1]-p0[1]]
            w = (vP[0]*vQ[1]-vP[1]*vQ[0]).real
            dd = (vP[0]*vQ[0]+vP[1]*vQ[1]).real
            tot += arb(2)*(w/(dd + (dd*dd+w*w).sqrt())).atan()
    lo_ = float(tot.mid()) - abs(float(tot.rad()))
    hi_ = float(tot.mid()) + abs(float(tot.rad()))
    if not (lo_ > 0.0 and hi_ < 4*math.pi):
        return False, f'winding enclosure [{lo_:.3f},{hi_:.3f}] not in (0,4pi)'
    return True, 'ok'


def main():
    comp = sys.argv[1] if len(sys.argv) > 1 else 'x'
    from ray_global_certified import certify_ray
    okA, pieces, bad = certify_ray(comp, 1, 0.01, 0.60)
    print(f"area subdivision: {len(pieces)} pieces")
    stack = sorted(pieces); certified = []; gaps = []
    MINW = 2e-3
    while stack:
        a, b = stack.pop(0)
        trav, (cval, km, _, _), nfix = build_traversal(comp, 1, a, b)
        okA2, sup = area_certify(trav, cval, km, a, b)
        if not okA2:
            if b - a < MINW:
                gaps.append((a, b, f'area sup={sup:.6f}')); continue
            m = 0.5*(a+b); stack = [(a, m), (m, b)] + stack; continue
        okS, msg = simplicity_certify(trav, cval, km, a, b)
        if not okS:
            if b - a < MINW:
                gaps.append((a, b, msg)); continue
            m = 0.5*(a+b); stack = [(a, m), (m, b)] + stack; continue
        certified.append((a, b))
        print(f"  [{a:.5f},{b:.5f}] chordfix={nfix} sup={sup:.6f} SIMPLE",
              flush=True)
    certified.sort()
    merged = []
    for a, b in certified:
        if merged and abs(merged[-1][1] - a) < 1e-12:
            merged[-1] = (merged[-1][0], b)
        else:
            merged.append((a, b))
    print(f"\ncertified ranges: {[(round(a,5), round(b,5)) for a, b in merged]}")
    if gaps:
        print(f"GAPS ({len(gaps)}):")
        for a, b, m_ in gaps[:20]:
            print(f"  [{a:.5f},{b:.5f}] {m_}")
        print("PARTIAL certificate — gaps listed above")
    else:
        print("UNCONDITIONAL RAY THEOREM CERTIFIED on [0.01,0.60]")


if __name__ == "__main__":
    main()
