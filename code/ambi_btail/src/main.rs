// ambi_btail.py — the b-tail constant, by an exact cancellation the old estimate discarded.
// Rust port. See algorithm/rigorous/ambi_btail.py for the full mathematical writeup.
//
// The only non-trivial numeric dependency in the original is scipy.integrate.quad, used
// purely as an independent check against the closed-form numerator (part (1) of main()).
// It is replaced here with a plain adaptive Gauss-Kronrod-free Simpson quadrature that is
// refined until successive halvings agree to 1e-13, comfortably inside the 1e-11 tolerance
// the check uses. This is a different quadrature algorithm from QUADPACK but converges to
// the same integral to far higher precision than the check requires.

use std::f64::consts::PI;

const BETA: f64 = 0.2896538208173209;
const SIGMA: f64 = BETA;
const LAM_MIN: f64 = 0.6;
const ZMZ: f64 = 0.132114949;
const N_CERT: usize = 150;
const C_MEASURED: f64 = 1.90;

fn tau() -> f64 {
    PI / 2.0 - SIGMA
}
fn target() -> f64 {
    0.5 * (2.0 * BETA).sin()
}

fn numerator_closed(k: f64, t: f64) -> f64 {
    -t.sin() * (2.0 * k * t).sin()
}

/// Adaptive Simpson quadrature of f on [a,b] to (very tight) tolerance.
fn adaptive_simpson<F: Fn(f64) -> f64>(f: &F, a: f64, b: f64, tol: f64, depth: u32) -> f64 {
    let simpson = |a: f64, b: f64| -> f64 {
        let c = (a + b) / 2.0;
        (b - a) / 6.0 * (f(a) + 4.0 * f(c) + f(b))
    };
    fn rec<F: Fn(f64) -> f64>(
        f: &F,
        a: f64,
        b: f64,
        whole: f64,
        tol: f64,
        depth: u32,
    ) -> f64 {
        let c = (a + b) / 2.0;
        let left = {
            let cc = (a + c) / 2.0;
            (c - a) / 6.0 * (f(a) + 4.0 * f(cc) + f(c))
        };
        let right = {
            let cc = (c + b) / 2.0;
            (b - c) / 6.0 * (f(c) + 4.0 * f(cc) + f(b))
        };
        let sum = left + right;
        if depth == 0 || (sum - whole).abs() < 15.0 * tol {
            return sum + (sum - whole) / 15.0;
        }
        rec(f, a, c, left, tol / 2.0, depth - 1) + rec(f, c, b, right, tol / 2.0, depth - 1)
    }
    let whole = simpson(a, b);
    rec(f, a, b, whole, tol, depth)
}

fn numerator_quad(k: f64, t: f64) -> f64 {
    let f = |s: f64| s.cos() * (2.0 * k * s).sin() + 2.0 * k * s.sin() * (2.0 * k * s).cos();
    adaptive_simpson(&f, t, PI / 2.0, 1e-12, 20)
}

fn btail_const(sigma: f64) -> f64 {
    sigma.cos().powi(2) / PI
}
fn btail_const_note(sigma: f64) -> f64 {
    (2.0 + 2.0 * sigma).powi(2) / PI
}

fn certificate(btail_c: f64, c: f64, n: usize) -> f64 {
    ZMZ + (2.0 * btail_c / n as f64 + 2.0 * c * c / n as f64) / LAM_MIN
}

fn c_admissible(btail_c: f64, n: usize) -> f64 {
    let slack = target() - ZMZ - (2.0 * btail_c / n as f64) / LAM_MIN;
    (slack * LAM_MIN * n as f64 / 2.0).sqrt()
}

fn main() {
    let mut bad = 0i32;
    let t = tau();

    println!("  (1) the numerator is a boundary term\n");
    println!("  {:>5} {:>15} {:>15} {:>10}", "k", "quadrature", "closed form", "|diff|");
    let mut worst = 0.0_f64;
    for &k in &[1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233] {
        let q = numerator_quad(k as f64, t);
        let c = numerator_closed(k as f64, t);
        worst = worst.max((q - c).abs());
        println!("  {:5} {:15.9} {:15.9} {:10.2e}", k, q, c, (q - c).abs());
    }
    let ok = worst < 1e-11;
    if !ok {
        bad += 1;
    }
    println!(
        "\n  worst deviation {:.2e}  {}  (an exact derivative, not an estimate)\n",
        worst,
        if ok { "OK" } else { "FAIL" }
    );

    println!("  (2) the tail bound, against the true tail summed to k = 20000\n");
    println!(
        "  {:>6} {:>13} {:>13} {:>13} {:>11}",
        "N", "true tail", "exact bound", "note bound", "exact/true"
    );
    let ks: Vec<f64> = (1..=20000).map(|k| k as f64).collect();
    let terms: Vec<f64> = ks
        .iter()
        .map(|&k| (t.sin() * (2.0 * k * t).sin()).powi(2) / (PI / 4.0 + k * k * PI))
        .collect();
    for &n in &[60usize, 120, 150, 200] {
        let true_tail: f64 = terms[n..].iter().sum();
        let e = btail_const(SIGMA) / n as f64;
        let nn = btail_const_note(SIGMA) / n as f64;
        let valid = e > true_tail;
        if !valid {
            bad += 1;
        }
        println!(
            "  {:6} {:13.8} {:13.8} {:13.8} {:11.3}  {}",
            n,
            true_tail,
            e,
            nn,
            e / true_tail,
            if valid { "OK" } else { "FAIL: bound below the true tail" }
        );
    }
    println!(
        "\n  constant: exact {:.6}   note {:.6}   improvement {:.4}x\n",
        btail_const(SIGMA),
        btail_const_note(SIGMA),
        btail_const_note(SIGMA) / btail_const(SIGMA)
    );

    println!("  (3) what it buys the certificate at K = 150\n");
    let k_note = certificate(btail_const_note(SIGMA), C_MEASURED, N_CERT);
    let k_new = certificate(btail_const(SIGMA), C_MEASURED, N_CERT);
    println!("  {:24} {:>12} {:>12} {:>10}", "", "K bound", "target", "margin");
    println!(
        "  {:24} {:12.7} {:12.7} {:10.5}",
        "note b-tail",
        k_note,
        target(),
        target() - k_note
    );
    println!(
        "  {:24} {:12.7} {:12.7} {:10.5}",
        "exact b-tail",
        k_new,
        target(),
        target() - k_new
    );
    for (name, val) in [("note", k_note), ("exact", k_new)] {
        if val >= target() {
            println!("  FAIL: the {} chain does not close", name);
            bad += 1;
        }
    }
    println!(
        "\n  margin gain {:.3}x\n",
        (target() - k_new) / (target() - k_note)
    );

    println!("  (4) the requirement on the one remaining measured constant\n");
    let c_old = c_admissible(btail_const_note(SIGMA), N_CERT);
    let c_new = c_admissible(btail_const(SIGMA), N_CERT);
    println!("  largest admissible C, note b-tail   {:.4}", c_old);
    println!("  largest admissible C, exact b-tail  {:.4}", c_new);
    println!(
        "  measured C converges to about 1.88; headroom goes from {:+.1}% to {:+.1}%",
        100.0 * (c_old / 1.88 - 1.0),
        100.0 * (c_new / 1.88 - 1.0)
    );
    let rel = c_new > 2.4;
    if !rel {
        bad += 1;
    }
    println!(
        "  {}: the enclosure of C no longer has to be sharp\n",
        if rel { "OK" } else { "FAIL" }
    );

    println!(
        "  {}",
        if bad == 0 {
            "ALL CHECKS PASS".to_string()
        } else {
            format!("{} CHECK(S) FAILED", bad)
        }
    );

    std::process::exit(if bad == 0 { 0 } else { 1 });
}
