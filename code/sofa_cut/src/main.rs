//! sofa_cut — the cut set T(p), and the collapse of prop:V's three hypotheses into one.
//!
//! CRUX (Rule I1).  Proposition prop:V computes |N| as two truncated sweep integrals under
//! three hypotheses: (i) each sweep injective, (ii) the sweeps disjoint, (iii) together they
//! cover N.  (i) is Baek's for one corner; (ii) and (iii) had no prior art and were being
//! tracked as two separate open problems.
//!
//! THE MOVING FRAME.  Put u(t) = <c(t) - p, mu_t>, v(t) = <c(t) - p, nu_t>.  Differentiating
//! c(t) = (F-1) mu_t + (G-1) nu_t gives c'(t) = -alpha_1 mu_t + alpha_2 nu_t, so
//!
//!     u' = v - alpha_1(t),        v' = -u + alpha_2(t).
//!
//! Rotation plus forcing, with the arms AS the forcing.  Three consequences, all tested here:
//!
//!   A.  The corner covers p at time t iff u > 0 and v > 0.  Write T(p) for that set.
//!   B.  The two sweep Jacobians are alpha_2 - s (face 2) and s - alpha_1 (face 1), so the
//!       truncation windows [0, alpha_2^+] and [alpha_1^+, sigma] are exactly the sets where
//!       the Jacobian is nonnegative.  On the face-2 edge v = 0, u = s the outward normal
//!       velocity is v' = alpha_2 - s; on the face-1 edge u = 0, v = s it is u' = s - alpha_1.
//!       So THE WINDOWS ARE EXACTLY THE ENTRY POINTS of T(p): a boundary point is in the
//!       window iff the trajectory is crossing INTO the cut region there.
//!   C.  Hence V = integral over N of #(entries of p), while |N| is the integral of 1.  All
//!       three hypotheses therefore say one thing:
//!
//!           T(p) is a nonempty interval, for almost every p in N.
//!
//!       Covering is "at least one entry"; injectivity and disjointness together are "at most
//!       one entry".  Two open problems become one.
//!
//! WHAT THIS PROGRAM DOES.  Rule 3 says falsify before proving, and Rule I13 says run the
//! machinery on what is known.  So this measures, over a grid of points p:
//!
//!   1. the histogram of #components of T(p), area-weighted.  Any mass at >= 2 refutes
//!      disjointness outright and refutes prop:V's equality;
//!   2. the fraction of N cut already at t = 0, the one case where covering's entry does not
//!      exist (the argument needs T(p) to start strictly inside (0, pi/2]);
//!   3. whether every entry offset lands in its window, which is claim B above and is the
//!      falsifiable content of the entry/Jacobian identification;
//!   4. mean #entries against V/|N| from prop:V's own integrand, an independent check of C.
//!
//! Rule 8: O(grid) memory, closed-form support function, no tensor, seconds not minutes.
//!
//! Usage: cargo run --release -- [pgrid] [nt]

use std::time::Instant;

const F1: f64 = 1.202_938_908_156_911_4;
const BETA: f64 = 0.289_653_820_817_320_9;
const ATOM: f64 = 1.167_049_7;

fn p2() -> f64 { std::f64::consts::FRAC_PI_2 }

/// Sigma's absolutely continuous curvature radius, phase by phase (ambi_cap's closed form).
fn r_ac(x: f64) -> f64 {
    let f2 = (1.0 - 2.0f64.sqrt()) * F1;
    if x >= BETA && x < p2() - BETA {
        0.75 * (F1 * (x / 2.0).cos() + f2 * (x / 2.0).sin())
    } else if x >= p2() - BETA && x < p2() + BETA {
        0.5
    } else if x >= p2() + BETA && x < std::f64::consts::PI - BETA {
        let s = x - p2();
        0.75 * (-f2 * (s / 2.0).cos() + F1 * (s / 2.0).sin())
    } else {
        0.0
    }
}

/// H and H' on [0, pi], by quadrature of the closed-form radius plus the atom at pi/2.
fn support(n: usize) -> (Vec<f64>, Vec<f64>, Vec<f64>) {
    let mut x = Vec::with_capacity(n);
    let mut h = vec![0.0f64; n];
    let mut hp = vec![0.0f64; n];
    let dx = std::f64::consts::PI / (n - 1) as f64;
    for i in 0..n { x.push(i as f64 * dx); }
    let (mut cs, mut cc_) = (0.0f64, 0.0f64);
    let mut prev_s = 0.0;
    let mut prev_c = r_ac(0.0);
    for i in 0..n {
        let xi = x[i];
        let rs = r_ac(xi) * xi.sin();
        let rc = r_ac(xi) * xi.cos();
        if i > 0 { cs += (rs + prev_s) * dx / 2.0; cc_ += (rc + prev_c) * dx / 2.0; }
        prev_s = rs; prev_c = rc;
        let base_h = xi.cos() + 0.5 * xi.sin() + (xi.sin() * cc_ - xi.cos() * cs);
        let base_hp = -xi.sin() + 0.5 * xi.cos() + (xi.cos() * cc_ + xi.sin() * cs);
        h[i] = base_h + if xi > p2() { ATOM * (xi - p2()).sin() } else { 0.0 };
        hp[i] = base_hp + if xi >= p2() { ATOM * (xi - p2()).cos() } else { 0.0 };
    }
    (x, h, hp)
}

fn interp(x: &[f64], y: &[f64], t: f64) -> f64 {
    let dx = x[1] - x[0];
    let k = ((t / dx).floor() as usize).min(x.len() - 2);
    let w = (t - x[k]) / dx;
    y[k] * (1.0 - w) + y[k + 1] * w
}

/// Everything the cut test needs at one time, precomputed once and reused for every point.
struct Frame { cx: f64, cy: f64, mx: f64, my: f64, nx: f64, ny: f64,
               a1: f64, a2: f64, sig: f64 }

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let pg: usize = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(500);
    let nt: usize = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(3000);

    println!("sofa_cut — the cut set T(p), and prop:V's three hypotheses as one\n");
    println!("Moving frame: u = <c-p, mu>, v = <c-p, nu>, and c' = -alpha_1 mu + alpha_2 nu,");
    println!("so u' = v - alpha_1 and v' = -u + alpha_2.  The sweep windows are the entry");
    println!("points of T(p) = {{t : u>0, v>0}}, so V = int_N #entries while |N| = int_N 1.");
    println!("All three hypotheses reduce to: T(p) is a nonempty interval.\n");

    let (x, mut h, mut hp) = support(20001);

    // NORMALISATION.  sigma(t) = (F-1) tan t + G - 1 is the distance from the corner down to
    // the floor, so it stays finite only if the corner reaches the floor at t = pi/2, that is
    // only if H(pi/2) = 1.  Quadrature of r_ac leaves a small drift there, and tan t then
    // magnifies it without bound: with the drift left in, the face-1 term reads 1.076 against
    // a true |N| near 0.19.  Subtracting eps*sin(theta) translates the cap by (0, -eps), which
    // changes no area and leaves BOTH arms untouched (alpha_1 and alpha_2 are the corner
    // velocity, hence translation invariant); only sigma moves, by -eps/cos t.
    let eps = interp(&x, &h, p2()) - 1.0;
    for i in 0..x.len() { h[i] -= eps * x[i].sin(); hp[i] -= eps * x[i].cos(); }
    println!("  H(pi/2) - 1 before normalising   {:.3e}", eps);

    // ---- the frames, and V from prop:V's own integrand ------------------------------------
    let mut fr: Vec<Frame> = Vec::with_capacity(nt);
    let mut v_int = 0.0f64;
    let mut tv = [0.0f64; 3];
    let (mut smax, mut sarg) = (0.0f64, 0.0f64);
    let dt = p2() / (nt - 1) as f64;
    for q in 0..nt {
        let t = q as f64 * dt;
        let f = interp(&x, &h, t);
        let g = interp(&x, &h, t + p2());
        let fp = interp(&x, &hp, t);
        let gp = interp(&x, &hp, t + p2());
        let a1 = g - 1.0 - fp;
        let a2 = f - 1.0 + gp;
        let sig = (f - 1.0) * t.tan().min(1e6) + g - 1.0;
        let (mx, my) = (t.cos(), t.sin());
        let (nx, ny) = (-t.sin(), t.cos());
        fr.push(Frame { cx: (f - 1.0) * mx + (g - 1.0) * nx,
                        cy: (f - 1.0) * my + (g - 1.0) * ny,
                        mx, my, nx, ny, a1, a2, sig });
        let w = if q == 0 || q == nt - 1 { 0.5 } else { 1.0 };
        let integrand = 0.5 * a2.max(0.0).powi(2) + 0.5 * (sig - a1).powi(2)
                      - 0.5 * (-a1).max(0.0).powi(2);
        v_int += w * integrand * dt;
        tv[0] += w * 0.5 * a2.max(0.0).powi(2) * dt;
        tv[1] += w * 0.5 * (sig - a1).powi(2) * dt;
        tv[2] += w * 0.5 * (-a1).max(0.0).powi(2) * dt;
        if sig.abs() > smax { smax = sig.abs(); sarg = t; }
    }
    println!("  V from prop:V's integrand        {:.6}", v_int);
    println!("    face-2 term  1/2 (a2^+)^2      {:.6}", tv[0]);
    println!("    face-1 term  1/2 (sig - a1)^2  {:.6}", tv[1]);
    println!("    subtracted   1/2 (a1^-)^2      {:.6}", tv[2]);
    println!("    max |sigma|  {:.6} at t = {:.6}", smax, sarg);

    // ---- sweep the point grid --------------------------------------------------------------
    let (lo, hi) = (-1.7f64, 1.7f64);
    let (ylo, yhi) = (-1.2f64, 2.2f64);
    let cell = ((hi - lo) / pg as f64) * ((yhi - ylo) / pg as f64);
    let t0 = Instant::now();

    let mut hist = [0usize; 8];      // #components of T(p), capped at 7
    let mut n_cells = 0usize;        // cells with T(p) nonempty: this is N
    let mut cut_at_zero = 0usize;    // cells already cut at t = 0
    let mut entries_total = 0usize;
    let mut entries_in_window = 0usize;
    let mut worst_window_miss = 0.0f64;

    // The niche is what the corner removes FROM THE CAP, so p must lie in C_2: above the
    // floor and inside every supporting half-plane.  Without this the quadrant runs off to
    // the edge of the box and |N| comes out an order of magnitude too large.
    let ncap = 720usize;
    let cap: Vec<(f64, f64, f64)> = (0..ncap).map(|k| {
        let th = k as f64 / (ncap - 1) as f64 * std::f64::consts::PI;
        (th.cos(), th.sin(), interp(&x, &h, th))
    }).collect();
    let in_cap = |px: f64, py: f64| -> bool {
        py >= 0.0 && cap.iter().all(|&(ex, ey, hh)| px * ex + py * ey <= hh)
    };

    for jy in 0..pg {
        if jy % (pg / 10).max(1) == 0 {
            let done = jy as f64 / pg as f64;
            let el = t0.elapsed().as_secs_f64();
            println!("  ... {:>3.0}%  elapsed {:>5.1}s  eta {:>5.1}s",
                     100.0 * done, el, if done > 0.0 { el / done - el } else { 0.0 });
        }
        let py = ylo + (jy as f64 + 0.5) / pg as f64 * (yhi - ylo);
        for ix in 0..pg {
            let px = lo + (ix as f64 + 0.5) / pg as f64 * (hi - lo);
            if !in_cap(px, py) { continue; }
            let mut comps = 0usize;
            let mut prev_cut = false;
            let mut zero_cut = false;
            let (mut pu, mut pv) = (0.0f64, 0.0f64);
            for (q, f) in fr.iter().enumerate() {
                let (dx, dy) = (f.cx - px, f.cy - py);
                let u = dx * f.mx + dy * f.my;
                let v = dx * f.nx + dy * f.ny;
                let cut = u > 0.0 && v > 0.0;
                if cut && !prev_cut {
                    comps += 1;
                    if q == 0 { zero_cut = true; }
                    else if pu > 0.0 || pv > 0.0 {
                        // Entry: exactly one coordinate was nonpositive a step ago, and that
                        // is the one that crossed.  The OTHER one is the sweep offset s.
                        // (Both nonpositive is a corner entry: ambiguous, so not scored.)
                        entries_total += 1;
                        let (s, loj, hij) = if pu <= 0.0 {
                            (v, f.a1.max(0.0), f.sig)     // face 1: u crossed, offset is v
                        } else {
                            (u, 0.0, f.a2.max(0.0))       // face 2: v crossed, offset is u
                        };
                        let miss = (loj - s).max(s - hij).max(0.0);
                        if miss <= 8.0 * dt { entries_in_window += 1; }
                        else if miss > worst_window_miss { worst_window_miss = miss; }
                    }
                }
                prev_cut = cut; pu = u; pv = v;
            }
            if comps > 0 {
                n_cells += 1;
                hist[comps.min(7)] += 1;
                if zero_cut { cut_at_zero += 1; }
            }
        }
    }

    let area_n = n_cells as f64 * cell;
    println!("\n  |N| rasterised                   {:.6}", area_n);
    println!("  cells with T(p) nonempty         {}", n_cells);
    println!("\n  components of T(p)   cells        fraction");
    let mut mean = 0.0f64;
    for k in 1..8 {
        if hist[k] > 0 {
            let f = hist[k] as f64 / n_cells.max(1) as f64;
            println!("  {:>18}   {:>8}   {:>12.8}", if k == 7 { 7 } else { k }, hist[k], f);
            mean += k as f64 * f;
        }
    }
    println!("\n  mean #components                 {:.8}", mean);
    println!("  V / |N| from the integrand       {:.8}", v_int / area_n.max(1e-12));
    let frac_zero = cut_at_zero as f64 / n_cells.max(1) as f64;
    println!("  cut already at t = 0             {} cells, {:.8} of N", cut_at_zero, frac_zero);
    let wfrac = entries_in_window as f64 / entries_total.max(1) as f64;
    println!("  entries with offset in window    {} of {}, {:.8}",
             entries_in_window, entries_total, wfrac);
    println!("  worst out-of-window miss         {:.6}", worst_window_miss);
    println!("  elapsed                          {:.1}s", t0.elapsed().as_secs_f64());

    println!();
    let multi = hist[2..].iter().sum::<usize>();
    if multi > 0 {
        println!("  T(p) IS NOT ALWAYS AN INTERVAL: {} cells, {:.6} of N, carry two or more",
                 multi, multi as f64 / n_cells.max(1) as f64);
        println!("  components.  Those cells are counted once in |N| and once per component in");
        println!("  V, so prop:V's equality fails on them unless the mass vanishes with");
        println!("  resolution.  Re-run at a finer grid before reading this either way.");
    } else {
        println!("  T(p) is an interval on every sampled cell, so on this grid prop:V's three");
        println!("  hypotheses hold simultaneously.  That is evidence for the reduction, not a");
        println!("  proof of it: a grid cannot see a set of small measure.");
    }
    if wfrac > 0.999 {
        println!("  The entry/window identification survives: every entry offset lands in its");
        println!("  own truncation window, which is claim B and the reason the two hypotheses");
        println!("  collapse into one.");
    } else {
        println!("  The entry/window identification FAILS on {:.4} of entries.  Claim B is",
                 1.0 - wfrac);
        println!("  wrong as stated and the reduction does not hold.");
    }
}
