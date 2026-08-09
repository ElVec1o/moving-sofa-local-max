//! sofa_stadium — the negative control that breaks prop:V's reduction.
//!
//! WHAT IS BEING TESTED.  Remark rem:v4 claimed V = int_N #entries, and concluded that
//! prop:V's three hypotheses reduce to "T(p) is a nonempty interval".  The area formula
//! actually gives int int |det| = int over the WHOLE PLANE of #preimages, so
//!
//!     V = int_N #entries  +  int_{R^2 \ C2} #entries,
//!
//! and the reduction silently drops the second term.  The covering argument proves that
//! every point of N IS a sweep value; it never proves the sweeps stay INSIDE the cap.
//!
//! THE CONTROL.  The stadium cap H(th) = 1/2 + (1/2) sin th + L |cos th| is the Minkowski
//! sum of the disc of radius 1/2 centred (0,1/2) with the segment [-L,L] x {0}.  It meets
//! every condition rem:v5 imposes:
//!
//!   r = H + H'' = 1/2 identically off th = pi/2, so r < 1 with room;
//!   a single atom at pi/2, of mass 2L, exactly Sigma's structure;
//!   H(pi/2) = 1 on the nose, so the corner starts on the floor;
//!   convex, symmetric about y = 1/2, contained in 0 <= y <= 1.
//!
//! Its arms are Sigma's own SOL1 forms with L in place of a1:
//!   alpha_1 = 2L sin t - 1/2,   alpha_2 = 2L cos t - 1/2.
//!
//! Membership is exact and needs no support-function scan: p is in the cap iff its distance
//! to the segment from (-L,1/2) to (L,1/2) is at most 1/2.  That also fixes a real defect in
//! sofa_cut, whose in_cap tested only the upper-half constraints and so tested C n {y>=0}
//! rather than C2 = C n rho C.
//!
//! Rule 8: three boolean rasters, a few MB, no quadrature tensor, seconds.
//!
//! Usage: cargo run --release -- [grid] [nt] [L ...]

const P2: f64 = std::f64::consts::FRAC_PI_2;

fn h(th: f64, l: f64) -> f64 { 0.5 + 0.5 * th.sin() + l * th.cos().abs() }

/// H', valid away from th = pi/2 where the atom sits.
fn hp(th: f64, l: f64) -> f64 {
    0.5 * th.cos() - l * th.sin() * if th.cos() >= 0.0 { 1.0 } else { -1.0 }
}

/// Exact membership in the stadium: distance to the core segment is at most 1/2.
fn in_cap(px: f64, py: f64, l: f64) -> bool {
    let dx = (px.abs() - l).max(0.0);
    let dy = py - 0.5;
    dx * dx + dy * dy <= 0.25 + 1e-12
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let g: usize = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(900);
    let nt: usize = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(4000);
    let ls: Vec<f64> = if a.len() > 3 {
        a[3..].iter().filter_map(|s| s.parse().ok()).collect()
    } else { vec![1.10, 1.20, 1.30, 1.40, 1.50] };

    println!("sofa_stadium — negative control for the V = int_N #entries reduction\n");
    println!("Stadium cap: r = 1/2 off a single atom at pi/2, H(pi/2) = 1, convex, in the");
    println!("unit strip.  Every hypothesis rem:v5 imposes holds.  If V != |N| here, the");
    println!("reduction is wrong and the missing lemma is containment of the sweeps in C2.\n");
    println!("{:>6} {:>10} {:>10} {:>12} {:>12} {:>10} {:>7}",
             "L", "V", "|N|", "sweep in C2", "sweep out", "V - |N|", "multi");

    for &l in &ls {
        // ---- V from prop:V's integrand -------------------------------------------------
        let mut v_int = 0.0f64;
        let dt = P2 / nt as f64;
        for q in 0..=nt {
            let t = (q as f64 + 0.5).min(nt as f64 - 0.5) * dt;
            if t >= P2 { continue; }
            let a1 = 2.0 * l * t.sin() - 0.5;
            let a2 = 2.0 * l * t.cos() - 0.5;
            let sig = (h(t, l) - 1.0) * t.tan() + h(t + P2, l) - 1.0;
            v_int += (0.5 * a2.max(0.0).powi(2) + 0.5 * (sig - a1).powi(2)
                      - 0.5 * (-a1).max(0.0).powi(2)) * dt;
        }

        // ---- rasters -------------------------------------------------------------------
        let (lo, hi) = (-(l + 1.5), l + 1.5);
        let (ylo, yhi) = (-1.5f64, 2.0f64);
        let cell = ((hi - lo) / g as f64) * ((yhi - ylo) / g as f64);
        let mut swept = vec![false; g * g];     // union of the two truncated sweeps
        let mut cut = vec![false; g * g];       // the cut set, intersected with the cap
        let mut multi = 0usize;

        let mark = |v: &mut Vec<bool>, px: f64, py: f64| {
            let i = (((px - lo) / (hi - lo)) * g as f64) as isize;
            let j = (((py - ylo) / (yhi - ylo)) * g as f64) as isize;
            if i >= 0 && j >= 0 && (i as usize) < g && (j as usize) < g {
                v[j as usize * g + i as usize] = true;
            }
        };

        for q in 0..nt {
            let t = (q as f64 + 0.5) * dt;
            let a1 = 2.0 * l * t.sin() - 0.5;
            let a2 = 2.0 * l * t.cos() - 0.5;
            let sig = (h(t, l) - 1.0) * t.tan() + h(t + P2, l) - 1.0;
            let (mu, nu) = ((t.cos(), t.sin()), (-t.sin(), t.cos()));
            let c = ((h(t, l) - 1.0) * mu.0 + (h(t + P2, l) - 1.0) * nu.0,
                     (h(t, l) - 1.0) * mu.1 + (h(t + P2, l) - 1.0) * nu.1);
            let steps = 700;
            if a2 > 0.0 {
                for k in 0..=steps {
                    let s = a2 * k as f64 / steps as f64;
                    mark(&mut swept, c.0 - s * mu.0, c.1 - s * mu.1);
                }
            }
            let s0 = a1.max(0.0);
            if sig > s0 {
                for k in 0..=steps {
                    let s = s0 + (sig - s0) * k as f64 / steps as f64;
                    mark(&mut swept, c.0 - s * nu.0, c.1 - s * nu.1);
                }
            }
        }

        // ---- the cut set, and its component count, streamed one point at a time --------
        for jy in 0..g {
            let py = ylo + (jy as f64 + 0.5) / g as f64 * (yhi - ylo);
            for ix in 0..g {
                let px = lo + (ix as f64 + 0.5) / g as f64 * (hi - lo);
                if !in_cap(px, py, l) { continue; }
                let mut comps = 0usize;
                let mut prev = false;
                for q in 0..nt {
                    let t = (q as f64 + 0.5) * dt;
                    let (mu, nu) = ((t.cos(), t.sin()), (-t.sin(), t.cos()));
                    let c = ((h(t, l) - 1.0) * mu.0 + (h(t + P2, l) - 1.0) * nu.0,
                             (h(t, l) - 1.0) * mu.1 + (h(t + P2, l) - 1.0) * nu.1);
                    let (dx, dy) = (c.0 - px, c.1 - py);
                    let cc = dx * mu.0 + dy * mu.1 > 0.0 && dx * nu.0 + dy * nu.1 > 0.0;
                    if cc && !prev { comps += 1; }
                    prev = cc;
                }
                if comps > 0 { cut[jy * g + ix] = true; }
                if comps > 1 { multi += 1; }
            }
        }

        let mut n_cells = 0usize;
        let (mut sw_in, mut sw_out) = (0usize, 0usize);
        for jy in 0..g {
            let py = ylo + (jy as f64 + 0.5) / g as f64 * (yhi - ylo);
            for ix in 0..g {
                let px = lo + (ix as f64 + 0.5) / g as f64 * (hi - lo);
                let k = jy * g + ix;
                if cut[k] { n_cells += 1; }
                if swept[k] {
                    if in_cap(px, py, l) { sw_in += 1; } else { sw_out += 1; }
                }
            }
        }
        println!("{:>6.2} {:>10.5} {:>10.5} {:>12.5} {:>12.5} {:>10.5} {:>7}",
                 l, v_int, n_cells as f64 * cell, sw_in as f64 * cell,
                 sw_out as f64 * cell, v_int - n_cells as f64 * cell, multi);
    }

    println!("\n  A nonzero 'sweep out' column with V - |N| tracking it is the refutation:");
    println!("  the hypotheses hold, T(p) stays an interval (multi = 0), and eq:V still");
    println!("  overstates |N| by exactly the sweep mass that leaves the cap.");
}
