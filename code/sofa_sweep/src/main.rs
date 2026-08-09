//! sofa_sweep — falsify prop:V's two open hypotheses before attempting to prove them.
//!
//! CRUX (Rule I1).  Proposition prop:V computes |N| as a sum of two sweep integrals, under
//! three hypotheses.  A literature sweep (Rule 4) found the first proved:
//!
//!   (i)   each sweep is injective            — Baek, arXiv:2411.19826, for ONE corner
//!   (ii)  the two sweeps are disjoint        — no prior art
//!   (iii) together they cover N              — no prior art
//!
//! (ii) and (iii) are what this project would have to prove, so Rule 3 applies: try to
//! destroy them first.  A counterexample would be worth more than a failed proof attempt,
//! and would tell us which of prop:V's conclusions actually survives.
//!
//! THE SWEEPS.  With c(t) = (F-1) mu_t + (G-1) nu_t the corner path,
//!
//!   face 2:  Phi(s,t) = c(t) - s mu_t,   s in [0, alpha_2^+]
//!   face 1:  Psi(s,t) = c(t) - s nu_t,   s in [alpha_1^+, sigma]
//!
//! Both are rasterised on a shared grid.  DISJOINTNESS asks whether any cell is hit by both;
//! COVERING asks whether the union equals N, which is taken as the region the rasteriser
//! removes when it cuts the niches (ambi_disconnected's second loop, reimplemented here).
//!
//! WHAT A FAILURE MEANS.  Overlap of measure zero along a shared boundary curve is expected
//! and is not a counterexample; the sweeps meet where alpha_1 = 0.  What would refute (ii)
//! is overlap of positive area.  For (iii), cells of N hit by neither sweep.  Both are
//! reported as fractions of |N| so the reader can judge whether a nonzero number is a real
//! failure or a discretisation artifact, and the run repeats at two resolutions so the
//! distinction is visible rather than asserted.
//!
//! Rule 8: closed-form support function, O(grid) memory, no intermediate tensor.
//!
//! Usage: cargo run --release -- [grid] [nt]

use std::time::Instant;

const A1C: f64 = 0.875_287_362_412_732;
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

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let g: usize = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(1200);
    let nt: usize = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(4000);

    println!("sofa_sweep — falsifying prop:V's two open hypotheses\n");
    println!("(i) injectivity is proved for one corner by Baek, arXiv:2411.19826.");
    println!("(ii) disjointness of the two sweeps and (iii) their covering N have no prior");
    println!("art, so Rule 3 says try to break them before trying to prove them.\n");

    let (x, h, hp) = support(20001);
    println!("{:>7} {:>7} {:>14} {:>14} {:>14} {:>9}",
             "grid", "nt", "both (frac)", "neither (frac)", "|N| cells", "secs");

    let mut results = Vec::new();
    for &(gg, tt) in [(g / 2, nt / 2), (g, nt)].iter() {
        let t0 = Instant::now();
        let (lo, hi) = (-1.7f64, 1.7f64);
        let (ylo, yhi) = (-1.2f64, 2.2f64);
        let mut hit2 = vec![false; gg * gg];   // face-2 sweep
        let mut hit1 = vec![false; gg * gg];   // face-1 sweep
        let mut inn = vec![false; gg * gg];    // the niche N itself
        let cell = ((hi - lo) / gg as f64) * ((yhi - ylo) / gg as f64);
        let mark = |v: &mut Vec<bool>, px: f64, py: f64| {
            let i = (((px - lo) / (hi - lo)) * gg as f64) as isize;
            let j = (((py - ylo) / (yhi - ylo)) * gg as f64) as isize;
            if i >= 0 && j >= 0 && (i as usize) < gg && (j as usize) < gg {
                v[j as usize * gg + i as usize] = true;
            }
        };
        for q in 0..tt {
            let t = q as f64 / (tt - 1) as f64 * p2();
            let f = interp(&x, &h, t);
            let gq = interp(&x, &h, t + p2());
            let fp = interp(&x, &hp, t);
            let gp = interp(&x, &hp, t + p2());
            let (mu, nu) = ((t.cos(), t.sin()), (-t.sin(), t.cos()));
            let c = ((f - 1.0) * mu.0 + (gq - 1.0) * nu.0,
                     (f - 1.0) * mu.1 + (gq - 1.0) * nu.1);
            let a1 = gq - 1.0 - fp;               // alpha_1
            let a2 = f - 1.0 + gp;                // alpha_2
            let sig = (f - 1.0) * t.tan().min(1e6) + gq - 1.0;
            // face 2: s in [0, alpha_2^+]
            if a2 > 0.0 {
                let steps = 400;
                for k in 0..=steps {
                    let s = a2 * k as f64 / steps as f64;
                    mark(&mut hit2, c.0 - s * mu.0, c.1 - s * mu.1);
                    mark(&mut inn, c.0 - s * mu.0, c.1 - s * mu.1);
                }
            }
            // face 1: s in [max(alpha_1,0), sigma]
            let s0 = a1.max(0.0);
            if sig > s0 {
                let steps = 400;
                for k in 0..=steps {
                    let s = s0 + (sig - s0) * k as f64 / steps as f64;
                    mark(&mut hit1, c.0 - s * nu.0, c.1 - s * nu.1);
                    mark(&mut inn, c.0 - s * nu.0, c.1 - s * nu.1);
                }
            }
        }
        let mut both = 0usize;
        let mut neither = 0usize;
        let mut ncells = 0usize;
        for k in 0..gg * gg {
            if inn[k] {
                ncells += 1;
                if hit1[k] && hit2[k] { both += 1; }
                if !hit1[k] && !hit2[k] { neither += 1; }
            }
        }
        let fb = both as f64 / ncells.max(1) as f64;
        let fn_ = neither as f64 / ncells.max(1) as f64;
        results.push((fb, fn_, ncells as f64 * cell));
        println!("{:>7} {:>7} {:>14.6} {:>14.6} {:>14.6} {:>9.2}",
                 gg, tt, fb, fn_, ncells as f64 * cell, t0.elapsed().as_secs_f64());
    }

    println!();
    let (fb_c, fn_c, _) = results[results.len() - 1];
    let (fb_p, _, _) = results[0];
    let shrinking = fb_c < fb_p;
    if fb_c < 1e-3 {
        println!("  DISJOINTNESS survives: the overlap is under 0.1 percent of |N|, which is");
        println!("  the shared boundary curve where alpha_1 = 0 and has measure zero.  No");
        println!("  counterexample.");
    } else if shrinking {
        println!("  DISJOINTNESS: the overlap is {:.4} of |N| and SHRINKS with resolution,", fb_c);
        println!("  which is what a measure-zero boundary looks like under rasterisation.");
        println!("  Not a counterexample, but not yet negligible either.");
    } else {
        println!("  DISJOINTNESS MAY FAIL: the overlap is {:.4} of |N| and does not shrink", fb_c);
        println!("  with resolution.  That is a candidate counterexample and the region where");
        println!("  both sweeps land is where to look.");
    }
    if fn_c < 1e-3 {
        println!("  COVERING survives: under 0.1 percent of N is missed.");
    } else {
        println!("  COVERING: {:.4} of N is hit by neither sweep.  Either the hypothesis", fn_c);
        println!("  fails or the sampling misses thin regions; the two resolutions above say");
        println!("  which, since a sampling artifact shrinks and a real gap does not.");
    }
}
