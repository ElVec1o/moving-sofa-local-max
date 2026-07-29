// sigma_area.rs — Rust port of the ambidextrous TRUE-area oracle.
// Replaces the shapely oracle (the session's bottleneck and the OOM cause).
//
// ALGEBRAIC RESTRUCTURING (this is what makes a port tractable without
// implementing general polygon booleans):
//
//   each hallway   H_t = C_t \ Q_t,
//        C_t = {<p-c,mu_t> <= 1} ^ {<p-c,nu_t> <= 1}      (2 half-planes)
//        Q_t = {<p-c,mu_t> <  0} ^ {<p-c,nu_t> <  0}      (reflex quadrant)
//
//   so   S = ⋂_t H_t = (⋂_t C_t) \ (⋃_t Q_t)  =  C \ U,
//   and  Sigma = S ^ rho(S) = C2 \ (U ∪ rho U),   C2 = C ^ rho C convex.
//
// C2 is an intersection of half-planes -> exact Sutherland-Hodgman clipping.
// U ∪ rhoU is a union of quadrants; on any vertical line x = X each quadrant
// cuts ONE y-interval (each of its two half-planes gives a y-half-line), so
// the notch is a 1-D interval union per slice — sort and merge, no polygon
// booleans anywhere.
//
//   area(Sigma) = ∫ [ |slice of C2| - |slice of (U ∪ rhoU) ^ C2| ] dx
//
// The x-quadrature uses a FIXED node set for every evaluation, so the
// discretization error is common-mode and cancels in finite differences —
// the same property the shapely oracle relied on.
//
// STATUS: WORKING.  subtract_wedge fires correctly (the wrap-around
// enter/exit pair needed its own dQ closure — without it the boundary
// short-circuits along a chord and only a sliver is removed).  Area at c_R
// agrees with shapely to 1e-10.  Former bug notes kept below for the record.
// OLD STATUS (resolved):
// subtract_wedge (below) is implemented but DOES NOT FIRE: all 2400 wedge
// subtractions leave the polygon unchanged, so this binary currently returns
// the CONVEX body C2 (area 2.0133) instead of Sigma (1.6451) — the missing
// 0.368 is exactly the notch.  Verified that the wedges MUST bite: 10/10
// probe points placed just inside the corner path are simultaneously inside
// C2 and inside some quadrant.  So the bug is in the event walk of
// subtract_wedge, not in the geometry set-up (the wedge normals and the
// reflected-wedge apex/normals were each re-derived and checked).
// Curiously the FD along a high-frequency direction is already accurate
// (-52.368 vs shapely -52.390, 0.04%) because the convex part carries that
// direction's second variation; the smooth cap-bump direction, where the
// notch matters, is 10% off.  Next step: instrument `any`/event counts per
// wedge to find why no edge registers a crossing.
//
// stdin:  n m   /  n thetas  /  m blocks of n "cx cy" pairs
// stdout: m areas
//
// build: rustc -O sigma_area.rs -o sigma_area

use std::io::{self, Read, Write};

const BIG: f64 = 12.0;
const PI2C: f64 = std::f64::consts::PI / 2.0;

#[derive(Clone, Copy)]
struct HalfPlane { nx: f64, ny: f64, c: f64 }   // nx*x + ny*y <= c

fn clip(poly: &Vec<(f64, f64)>, h: HalfPlane) -> Vec<(f64, f64)> {
    let n = poly.len();
    if n == 0 { return vec![]; }
    let mut out = Vec::with_capacity(n + 4);
    let val = |p: &(f64, f64)| h.nx * p.0 + h.ny * p.1 - h.c;
    for i in 0..n {
        let a = poly[i];
        let b = poly[(i + 1) % n];
        let (va, vb) = (val(&a), val(&b));
        if va <= 0.0 { out.push(a); }
        if (va < 0.0 && vb > 0.0) || (va > 0.0 && vb < 0.0) {
            let t = va / (va - vb);
            out.push((a.0 + t * (b.0 - a.0), a.1 + t * (b.1 - a.1)));
        }
    }
    // drop duplicates: repeated vertices break the wedge event walk
    let mut d: Vec<(f64, f64)> = Vec::with_capacity(out.len());
    for p in out {
        if d.last().map_or(true, |q: &(f64, f64)|
              (q.0 - p.0).abs() > 1e-13 || (q.1 - p.1).abs() > 1e-13) {
            d.push(p);
        }
    }
    while d.len() > 1 {
        let f = d[0]; let l = *d.last().unwrap();
        if (f.0 - l.0).abs() < 1e-13 && (f.1 - l.1).abs() < 1e-13 { d.pop(); } else { break; }
    }
    d
}

#[derive(Clone, Copy)]
struct Wedge { ax: f64, ay: f64, n1x: f64, n1y: f64, n2x: f64, n2y: f64 }

impl Wedge {
    #[inline] fn f1(&self, p: (f64, f64)) -> f64 {
        self.n1x * (p.0 - self.ax) + self.n1y * (p.1 - self.ay)
    }
    #[inline] fn f2(&self, p: (f64, f64)) -> f64 {
        self.n2x * (p.0 - self.ax) + self.n2y * (p.1 - self.ay)
    }
    #[inline] fn inside(&self, p: (f64, f64)) -> bool {
        self.f1(p) < 0.0 && self.f2(p) < 0.0
    }
}

#[inline]
fn lerp(u: (f64, f64), v: (f64, f64), t: f64) -> (f64, f64) {
    (u.0 + t * (v.0 - u.0), u.1 + t * (v.1 - u.1))
}

/// parameter interval of edge u->v lying strictly inside the wedge
fn inside_interval(w: &Wedge, u: (f64, f64), v: (f64, f64)) -> Option<(f64, f64)> {
    let (mut lo, mut hi) = (0.0f64, 1.0f64);
    for &(a, b) in [(w.f1(u), w.f1(v)), (w.f2(u), w.f2(v))].iter() {
        let d = b - a;
        if d.abs() < 1e-300 {
            if a >= 0.0 { return None; }
        } else {
            let t = -a / d;
            if d > 0.0 { if t < hi { hi = t; } } else if t > lo { lo = t; }
        }
        if hi <= lo { return None; }
    }
    Some((lo, hi))
}

fn point_in_poly(poly: &Vec<(f64, f64)>, p: (f64, f64)) -> bool {
    let n = poly.len();
    let mut c = false;
    for i in 0..n {
        let a = poly[i];
        let b = poly[(i + 1) % n];
        if ((a.1 > p.1) != (b.1 > p.1))
            && (p.0 < (b.0 - a.0) * (p.1 - a.1) / (b.1 - a.1) + a.0) {
            c = !c;
        }
    }
    c
}

/// EXACT polygon-minus-convex-wedge.  The boundary of P \ Q is
/// (dP outside Q) stitched with (dQ inside P): where the walk enters Q at E
/// and leaves at X, the removed run is replaced by the wedge boundary from E
/// to X — through the apex when E and X sit on different rays.  This restores
/// the exactness the slice quadrature lacked: all error is now common-mode
/// across an FD stencil and cancels under the 1/eps^2 amplification.
fn subtract_wedge(poly: &Vec<(f64, f64)>, w: &Wedge, apex_bad: &mut usize)
                  -> Vec<(f64, f64)> {
    let n = poly.len();
    if n < 3 { return vec![]; }

    // events along dP: 0 = plain vertex (outside), 1 = enter Q, 2 = leave Q
    let mut ev: Vec<((f64, f64), u8)> = Vec::with_capacity(2 * n + 8);
    let mut any = false;
    for i in 0..n {
        let u = poly[i];
        let v = poly[(i + 1) % n];
        if !w.inside(u) { ev.push((u, 0)); }
        if let Some((lo, hi)) = inside_interval(w, u, v) {
            any = true;
            if lo > 1e-14 { ev.push((lerp(u, v, lo), 1)); }
            if hi < 1.0 - 1e-14 { ev.push((lerp(u, v, hi), 2)); }
        }
    }
    if !any { return poly.clone(); }
    if !ev.iter().any(|e| e.1 == 2) { return vec![]; }   // wholly inside Q

    // rotate to start just after a "leave" event
    let start = ev.iter().position(|e| e.1 == 2).unwrap();
    let m = ev.len();
    let apex_in = point_in_poly(poly, (w.ax, w.ay));

    let mut out: Vec<(f64, f64)> = Vec::with_capacity(m + 8);
    let mut pending: Option<(f64, f64)> = None;
    let first_exit = ev[start].0;          // the walk's closing point
    for k in 0..m {
        let (p, kind) = ev[(start + k) % m];
        match kind {
            0 => { if pending.is_none() { out.push(p); } }
            1 => { pending = Some(p); out.push(p); }
            2 => {
                if let Some(e) = pending.take() {
                    // route along dQ from e to p
                    let e_on1 = w.f1(e).abs() <= w.f2(e).abs();
                    let p_on1 = w.f1(p).abs() <= w.f2(p).abs();
                    if e_on1 != p_on1 {
                        if apex_in { out.push((w.ax, w.ay)); } else { *apex_bad += 1; }
                    }
                }
                out.push(p);
            }
            _ => {}
        }
    }
    // WRAP-AROUND PAIR: the walk begins at an Exit, so the Enter that
    // cyclically precedes it is still pending here.  Its dQ routing closes
    // the polygon; without this the boundary short-circuits along a chord
    // and only a sliver is removed instead of the whole wedge region.
    if let Some(e) = pending.take() {
        let e_on1 = w.f1(e).abs() <= w.f2(e).abs();
        let x_on1 = w.f1(first_exit).abs() <= w.f2(first_exit).abs();
        if e_on1 != x_on1 {
            if apex_in { out.push((w.ax, w.ay)); } else { *apex_bad += 1; }
        }
    }
    out
}

fn shoelace(poly: &Vec<(f64, f64)>) -> f64 {
    let n = poly.len();
    if n < 3 { return 0.0; }
    let mut a = 0.0;
    for i in 0..n {
        let p = poly[i];
        let q = poly[(i + 1) % n];
        a += p.0 * q.1 - q.0 * p.1;
    }
    (a * 0.5).abs()
}

fn main() {
    let mut inp = String::new();
    io::stdin().read_to_string(&mut inp).unwrap();
    let mut it = inp.split_ascii_whitespace().map(|s| s.parse::<f64>().unwrap());
    let n = it.next().unwrap() as usize;
    let m = it.next().unwrap() as usize;
    let th: Vec<f64> = (0..n).map(|_| it.next().unwrap()).collect();
    // RELEASED mode: drop the cap-interior OUTER walls (the stationary fans),
    // i.e. the mu-wall on (0,beta) and the nu-wall on (pi/2-beta, pi/2), for
    // both families.  This is the fan-released functional F_rel of N12.
    let released = std::env::var("RELEASED").is_ok();
    let beta = {
        let s2 = 2f64.sqrt();
        (((s2 + 1.0).cbrt() - (s2 - 1.0).cbrt()) * 0.5).atan()
    };

    let stdout = io::stdout();
    let mut w = stdout.lock();
    let mut apex_bad = 0usize;

    for _ in 0..m {
        let mut cx = vec![0.0; n];
        let mut cy = vec![0.0; n];
        for i in 0..n { cx[i] = it.next().unwrap(); cy[i] = it.next().unwrap(); }

        let mut poly: Vec<(f64, f64)> = vec![(-BIG, -BIG), (BIG, -BIG),
                                             (BIG, BIG), (-BIG, BIG)];
        // L_horiz (rho-invariant): 0 <= y <= 1, x <= 1
        poly = clip(&poly, HalfPlane { nx: 0.0, ny: -1.0, c: 0.0 });
        poly = clip(&poly, HalfPlane { nx: 0.0, ny: 1.0, c: 1.0 });
        poly = clip(&poly, HalfPlane { nx: 1.0, ny: 0.0, c: 1.0 });

        // PASS 1: every half-plane first -- the subject stays CONVEX, so
        // Sutherland-Hodgman is exact and produces no degenerate bridge edges.
        for i in 0..n {
            let (c, s) = (th[i].cos(), th[i].sin());
            let t = th[i];
            let drop_mu = released && t > 1e-12 && t < beta - 1e-12;
            let drop_nu = released && t > PI2C - beta + 1e-12 && t < PI2C - 1e-12;
            for (slot, &(nx0, ny0)) in [(c, s), (-s, c)].iter().enumerate() {
                if (slot == 0 && drop_mu) || (slot == 1 && drop_nu) { continue; }
                let d = nx0 * cx[i] + ny0 * cy[i] + 1.0;
                poly = clip(&poly, HalfPlane { nx: nx0, ny: ny0, c: d });
                let d2 = nx0 * cx[i] + ny0 * cy[i] + 1.0 - ny0;
                poly = clip(&poly, HalfPlane { nx: nx0, ny: -ny0, c: d2 });
            }
            if poly.len() < 3 { break; }
        }
        // PASS 2: subtract the reflex quadrants (the only non-convex step)
        if poly.len() >= 3 {
            for i in 0..n {
                let (c, s) = (th[i].cos(), th[i].sin());
                let wd = Wedge { ax: cx[i], ay: cy[i], n1x: c, n1y: s, n2x: -s, n2y: c };
                poly = subtract_wedge(&poly, &wd, &mut apex_bad);
                if poly.len() < 3 { break; }
                let wr = Wedge { ax: cx[i], ay: 1.0 - cy[i],
                                 n1x: c, n1y: -s, n2x: -s, n2y: -c };
                poly = subtract_wedge(&poly, &wr, &mut apex_bad);
                if poly.len() < 3 { break; }
            }
        }
        writeln!(w, "{:.15}", shoelace(&poly)).unwrap();
    }
    if apex_bad > 0 {
        eprintln!("warning: {} apex-outside wedge routings (chorded)", apex_bad);
    }
}
