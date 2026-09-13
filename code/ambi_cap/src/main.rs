// ambi_cap.py — the single constructor for a cap: (absolutely continuous part, atom mass).
// Rust port. See algorithm/rigorous/ambi_cap.py for the full mathematical writeup.
// Plain f64, no external deps, direct translation of the closed-form numerics and checks.

use std::f64::consts::PI;

const A1: f64 = 0.875287362412732;
const BETA: f64 = 0.2896538208173209;
const P2: f64 = PI / 2.0;
const ATOM: f64 = 1.1670497; // G'(0) - F'(pi/2), the jump in H' at pi/2

fn f1() -> f64 {
    1.202938908156911389070223
}
fn f2() -> f64 {
    (1.0 - 2.0_f64.sqrt()) * f1()
}

fn linspace(a: f64, b: f64, n: usize) -> Vec<f64> {
    let step = (b - a) / (n as f64 - 1.0);
    (0..n).map(|i| a + step * i as f64).collect()
}

/// Sigma's cap as (a.c. curvature radius on [0,pi], atom mass at pi/2).
fn cap_sigma(x: &[f64]) -> (Vec<f64>, f64) {
    let f1v = f1();
    let f2v = f2();
    let r: Vec<f64> = x
        .iter()
        .map(|&xi| {
            if xi >= BETA && xi < P2 - BETA {
                0.75 * (f1v * (xi / 2.0).cos() + f2v * (xi / 2.0).sin())
            } else if xi >= P2 - BETA && xi < P2 + BETA {
                0.5
            } else if xi >= P2 + BETA && xi < PI - BETA {
                let s = xi - P2;
                0.75 * (-f2v * (s / 2.0).cos() + f1v * (s / 2.0).sin())
            } else {
                0.0
            }
        })
        .collect();
    (r, ATOM)
}

fn trapz(y: &[f64], dx: f64) -> f64 {
    let n = y.len();
    let mut s = 0.0;
    for i in 0..n - 1 {
        s += (y[i] + y[i + 1]) * dx / 2.0;
    }
    s
}

fn rc_max_closed() -> f64 {
    0.75 * f1() * (4.0 - 2.0 * 2.0_f64.sqrt()).sqrt() * (BETA / 2.0 + PI / 8.0).cos()
}

fn main() {
    let n = 200001usize;
    let x = linspace(0.0, PI, n);
    let dx = x[1] - x[0];
    let (r, atom) = cap_sigma(&x);

    let mut r_max = f64::MIN;
    let mut argmax = 0usize;
    for (i, &v) in r.iter().enumerate() {
        if v > r_max {
            r_max = v;
            argmax = i;
        }
    }

    let idx_le_p2: Vec<usize> = (0..n).filter(|&i| x[i] <= P2).collect();
    let idx_ge_p2: Vec<usize> = (0..n).filter(|&i| x[i] >= P2).collect();

    let rc_le: Vec<f64> = idx_le_p2.iter().map(|&i| r[i] * x[i].cos()).collect();
    let rc_ge: Vec<f64> = idx_ge_p2.iter().map(|&i| r[i] * x[i].cos()).collect();
    let m_l = trapz(&rc_le, dx);
    let m_r = trapz(&rc_ge, dx);

    let rs_le: Vec<f64> = idx_le_p2.iter().map(|&i| r[i] * x[i].sin()).collect();
    let a20 = trapz(&rs_le, dx) - 1.0 + atom;

    let r_beta_max = x
        .iter()
        .zip(r.iter())
        .filter(|(&xi, _)| xi < BETA)
        .map(|(_, &ri)| ri)
        .fold(f64::MIN, f64::max);
    let r_tail_max = x
        .iter()
        .zip(r.iter())
        .filter(|(&xi, _)| xi > PI - BETA)
        .map(|(_, &ri)| ri)
        .fold(f64::MIN, f64::max);

    println!("  {:<34} {:>14} {:>14} {:>4}", "quantity", "computed", "expected", "ok");

    let rows: Vec<(&str, f64, f64, f64)> = vec![
        ("max r (a.c.)", r_max, rc_max_closed(), 1e-6),
        ("argmax r / beta", x[argmax] / BETA, 1.0, 1e-3),
        ("int_0^(pi/2) r cos", m_l, 0.5, 1e-5),
        ("int_(pi/2)^pi r cos", m_r, -0.5, 1e-5),
        ("alpha_2(0) = 2a1 - 1", a20, 2.0 * A1 - 1.0, 1e-5),
        ("r on [0,beta)", r_beta_max, 0.0, 1e-12),
        ("r on [pi-beta,pi]", r_tail_max, 0.0, 1e-12),
    ];

    let mut bad = 0;
    for (name, got, want, tol) in &rows {
        let ok = (got - want).abs() < *tol;
        if !ok {
            bad += 1;
        }
        println!(
            "  {:<34} {:14.9} {:14.9} {:>4}",
            name,
            got,
            want,
            if ok { "OK" } else { "FAIL" }
        );
    }
    println!(
        "\n  {}",
        if bad == 0 {
            "ALL CHECKS PASS".to_string()
        } else {
            format!("{} CHECK(S) FAILED", bad)
        }
    );
    println!(
        "  note's max (H+H'')_ac = 0.8388253494; closed form here = {:.10}",
        rc_max_closed()
    );

    std::process::exit(if bad == 0 { 0 } else { 1 });
}
