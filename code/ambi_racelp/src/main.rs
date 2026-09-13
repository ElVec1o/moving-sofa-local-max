// ambi_racelp.py — the sharp ordering threshold, as a pair of linear programs.
// Rust port. See algorithm/rigorous/ambi_racelp.py for the full mathematical writeup.
// Ported: plain f64, no external deps, direct line-for-line translation of the numerics.

use std::f64::consts::PI;

const P2: f64 = PI / 2.0;
const SIGMA_C: f64 = 0.750575; // Sigma's alpha_2(0), from the closed forms
const CERTIFIED: f64 = 0.899266; // cor:race2, the value this note actually certifies

/// max (sense=+1) or min (sense=-1) of int obj*x over 0<=x<=1 with int x*w = target.
fn extremum(obj: &[f64], w: &[f64], target: f64, sense: f64, ds: f64) -> f64 {
    let n = obj.len();
    let o: Vec<f64> = obj.iter().map(|v| sense * v).collect();

    // trapezoid of x*w with dx=ds
    let sol = |lam: f64| -> (Vec<f64>, f64) {
        let x: Vec<f64> = (0..n).map(|i| if o[i] - lam * w[i] > 0.0 { 1.0 } else { 0.0 }).collect();
        let xw: Vec<f64> = (0..n).map(|i| x[i] * w[i]).collect();
        let val = trapz(&xw, ds);
        (x, val)
    };

    let mut lo = -80.0_f64;
    let mut hi = 80.0_f64;
    let (_, vlo) = sol(lo);
    let (_, vhi) = sol(hi);
    if vlo < target || vhi > target {
        return 0.0;
    }
    for _ in 0..120 {
        let m = (lo + hi) / 2.0;
        let (_, vm) = sol(m);
        if vm > target {
            lo = m;
        } else {
            hi = m;
        }
    }
    let (x, _) = sol((lo + hi) / 2.0);
    let ox: Vec<f64> = (0..n).map(|i| obj[i] * x[i]).collect();
    trapz(&ox, ds)
}

fn trapz(y: &[f64], dx: f64) -> f64 {
    let n = y.len();
    if n < 2 {
        return 0.0;
    }
    let mut s = 0.0;
    for i in 0..n - 1 {
        s += (y[i] + y[i + 1]) * dx / 2.0;
    }
    s
}

fn linspace(a: f64, b: f64, n: usize) -> Vec<f64> {
    if n == 1 {
        return vec![a];
    }
    let step = (b - a) / (n as f64 - 1.0);
    (0..n).map(|i| a + step * i as f64).collect()
}

fn threshold(n: usize) -> f64 {
    let s = linspace(0.0, P2, n);
    let ds = s[1] - s[0];
    let cs: Vec<f64> = s.iter().map(|t| t.cos()).collect();
    let sn: Vec<f64> = s.iter().map(|t| t.sin()).collect();

    let mut u2 = vec![0.0; n];
    let mut v2 = vec![0.0; n];
    let mut u1 = vec![0.0; n];
    let mut v1 = vec![0.0; n];

    for i in 0..n {
        let t = s[i];
        // masked arrays: value where s<=t else 0
        let sin_tms: Vec<f64> = (0..n)
            .map(|j| if s[j] <= t { (t - s[j]).sin() } else { 0.0 })
            .collect();
        let cos_tms: Vec<f64> = (0..n)
            .map(|j| if s[j] <= t { (t - s[j]).cos() } else { 0.0 })
            .collect();

        u2[i] = extremum(&sin_tms, &cs, 0.5, 1.0, ds);
        v2[i] = extremum(&cos_tms, &sn, 0.5, 1.0, ds);
        u1[i] = extremum(&cos_tms, &cs, 0.5, -1.0, ds);
        v1[i] = extremum(&sin_tms, &sn, 0.5, 1.0, ds);
    }

    let ok = |c: f64| -> bool {
        let mut alive_running = 1i32;
        let mut any_ok = false;
        for i in 0..n {
            let a2 = c * cs[i] + 0.5 * sn[i] - u2[i] - v2[i];
            let a1 = -0.5 * cs[i] + c * sn[i] + u1[i] - v1[i];
            let cur = if a2 > 0.0 { 1 } else { 0 };
            alive_running = alive_running.min(cur);
            if alive_running == 1 && a1 >= 0.0 {
                any_ok = true;
            }
        }
        any_ok
    };

    let mut lo = 0.0_f64;
    let mut hi = 3.0_f64;
    for _ in 0..60 {
        let m = (lo + hi) / 2.0;
        if !ok(m) {
            lo = m;
        } else {
            hi = m;
        }
    }
    hi
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let top: usize = if args.len() > 1 {
        args[1].parse().unwrap_or(8000)
    } else {
        8000
    };

    let grids: Vec<usize> = [1000usize, 2000, 4000, 8000, 16000]
        .into_iter()
        .filter(|&g| g <= top)
        .collect();
    let grids = if grids.is_empty() { vec![top] } else { grids };

    println!("  {:>7} {:>11} {:>10}   Sigma margin", "ngrid", "c_LP", "drift");
    let mut vals: Vec<f64> = Vec::new();
    for &g in &grids {
        let v = threshold(g);
        let d = if vals.is_empty() {
            String::new()
        } else {
            format!("{:+.6}", v - vals[vals.len() - 1])
        };
        vals.push(v);
        println!(
            "  {:7} {:11.6} {:>10}   {:+.6}",
            g,
            v,
            d,
            SIGMA_C - v
        );
    }
    let drift = if vals.len() > 1 {
        (0..vals.len() - 1)
            .map(|i| (vals[i + 1] - vals[i]).abs())
            .fold(0.0_f64, f64::max)
    } else {
        f64::NAN
    };
    let margin = SIGMA_C - vals[vals.len() - 1];
    println!(
        "\n  c_LP -> {:.6}, max drift {:.6}, Sigma margin {:+.6}",
        vals[vals.len() - 1],
        drift,
        margin
    );
    let resolved = margin > 0.0 && margin > drift;
    println!(
        "  margin {} the drift, so the sign is {}",
        if resolved { "exceeds" } else { "does NOT exceed" },
        if resolved {
            "stable under refinement"
        } else {
            "UNRESOLVED at this precision"
        }
    );
    println!("  certified value (cor:race2, proved): {}", CERTIFIED);
    println!("  c_LP is HEURISTIC (rule 7).  Exact/interval arithmetic is what would settle it.");

    std::process::exit(if vals[vals.len() - 1] < CERTIFIED { 0 } else { 1 });
}
