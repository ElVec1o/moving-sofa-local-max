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
// stdin:  n m   /  n thetas  /  m blocks of n "cx cy" pairs
// stdout: m areas
//
// build: rustc -O sigma_area.rs -o sigma_area

use std::io::{self, Read, Write};

const BIG: f64 = 12.0;

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
    out
}

/// y-extent of a convex polygon on the vertical line x = xq
fn yspan(poly: &Vec<(f64, f64)>, xq: f64) -> Option<(f64, f64)> {
    let n = poly.len();
    if n < 3 { return None; }
    let (mut lo, mut hi) = (f64::INFINITY, f64::NEG_INFINITY);
    for i in 0..n {
        let a = poly[i];
        let b = poly[(i + 1) % n];
        if (a.0 - xq) * (b.0 - xq) <= 0.0 && (a.0 - b.0).abs() > 1e-15 {
            let t = (xq - a.0) / (b.0 - a.0);
            if t >= -1e-12 && t <= 1.0 + 1e-12 {
                let y = a.1 + t * (b.1 - a.1);
                if y < lo { lo = y; }
                if y > hi { hi = y; }
            }
        }
        if (a.0 - xq).abs() < 1e-15 {
            if a.1 < lo { lo = a.1; }
            if a.1 > hi { hi = a.1; }
        }
    }
    if hi > lo { Some((lo, hi)) } else { None }
}

/// y-interval cut by the quadrant { <p-c,u> <= 0 } ^ { <p-c,v> <= 0 } on x=xq
#[inline]
fn quad_interval(cx: f64, cy: f64, ux: f64, uy: f64, vx: f64, vy: f64,
                 xq: f64, ylo: f64, yhi: f64) -> Option<(f64, f64)> {
    let (mut lo, mut hi) = (ylo, yhi);
    for &(nx, ny) in [(ux, uy), (vx, vy)].iter() {
        // nx*(xq-cx) + ny*(y-cy) <= 0
        let r = -nx * (xq - cx) + ny * cy;         // ny*y <= r
        if ny.abs() < 1e-14 {
            if nx * (xq - cx) > 0.0 { return None; }
        } else if ny > 0.0 {
            let b = r / ny; if b < hi { hi = b; }
        } else {
            let b = r / ny; if b > lo { lo = b; }
        }
        if hi <= lo { return None; }
    }
    Some((lo, hi))
}

fn main() {
    let mut inp = String::new();
    io::stdin().read_to_string(&mut inp).unwrap();
    let mut it = inp.split_ascii_whitespace().map(|s| s.parse::<f64>().unwrap());
    let n = it.next().unwrap() as usize;
    let m = it.next().unwrap() as usize;
    let th: Vec<f64> = (0..n).map(|_| it.next().unwrap()).collect();
    let nx_q: usize = std::env::var("NXQ").ok()
        .and_then(|s| s.parse().ok()).unwrap_or(4000);

    let stdout = io::stdout();
    let mut w = stdout.lock();

    for _ in 0..m {
        let mut cx = vec![0.0; n];
        let mut cy = vec![0.0; n];
        for i in 0..n { cx[i] = it.next().unwrap(); cy[i] = it.next().unwrap(); }

        // ---- convex part C2 = L_horiz ^ ⋂_t C_t ^ rho(same) --------------
        let mut poly: Vec<(f64, f64)> = vec![(-BIG, -BIG), (BIG, -BIG),
                                             (BIG, BIG), (-BIG, BIG)];
        // L_horiz: 0 <= y <= 1, x <= 1   (rho-invariant)
        poly = clip(&poly, HalfPlane { nx: 0.0, ny: -1.0, c: 0.0 });
        poly = clip(&poly, HalfPlane { nx: 0.0, ny: 1.0, c: 1.0 });
        poly = clip(&poly, HalfPlane { nx: 1.0, ny: 0.0, c: 1.0 });
        for i in 0..n {
            let (c, s) = (th[i].cos(), th[i].sin());
            let (mx, my) = (c, s);            // mu
            let (vx, vy) = (-s, c);           // nu
            for &(nx0, ny0) in [(mx, my), (vx, vy)].iter() {
                // direct: <p - c, n> <= 1
                let d = nx0 * cx[i] + ny0 * cy[i] + 1.0;
                poly = clip(&poly, HalfPlane { nx: nx0, ny: ny0, c: d });
                // reflected: <rho p - c, n> <= 1,  rho p = (x, 1-y)
                let d2 = nx0 * cx[i] + ny0 * cy[i] + 1.0 - ny0;
                poly = clip(&poly, HalfPlane { nx: nx0, ny: -ny0, c: d2 });
            }
            if poly.len() < 3 { break; }
        }
        if poly.len() < 3 { writeln!(w, "0.0").unwrap(); continue; }

        let xmin = poly.iter().fold(f64::INFINITY, |a, p| a.min(p.0));
        let xmax = poly.iter().fold(f64::NEG_INFINITY, |a, p| a.max(p.0));

        // ---- integrate  |C2 slice| - |notch slice|  over x ---------------
        // midpoint rule on a FIXED uniform grid: common-mode error cancels
        // in finite differences.
        let dx = (xmax - xmin) / nx_q as f64;
        let mut area = 0.0;
        let mut iv: Vec<(f64, f64)> = Vec::with_capacity(4 * n);
        for q in 0..nx_q {
            let xq = xmin + (q as f64 + 0.5) * dx;
            let (ylo, yhi) = match yspan(&poly, xq) { Some(v) => v, None => continue };
            iv.clear();
            for i in 0..n {
                let (c, s) = (th[i].cos(), th[i].sin());
                // direct quadrant: <p-c,mu> <=0 ^ <p-c,nu> <=0
                if let Some(t) = quad_interval(cx[i], cy[i], c, s, -s, c, xq, ylo, yhi) {
                    iv.push(t);
                }
                // reflected quadrant: apply rho to the direct one
                // rho(p) in Q  <=>  p in rho(Q); rho maps y -> 1-y
                if let Some(t) = quad_interval(cx[i], 1.0 - cy[i], c, -s, -s, -c,
                                               xq, ylo, yhi) {
                    iv.push(t);
                }
            }
            let mut covered = 0.0;
            if !iv.is_empty() {
                iv.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
                let (mut cs, mut ce) = iv[0];
                for k in 1..iv.len() {
                    if iv[k].0 > ce { covered += ce - cs; cs = iv[k].0; ce = iv[k].1; }
                    else if iv[k].1 > ce { ce = iv[k].1; }
                }
                covered += ce - cs;
            }
            area += (yhi - ylo - covered) * dx;
        }
        writeln!(w, "{:.15}", area).unwrap();
    }
}
