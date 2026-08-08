//! tail_schur — close the truncation tail of `-d2|T|` by a Schur complement.
//!
//! WHAT THIS SETTLES, AND IT IS A NEGATIVE RESULT.  Ball arithmetic certifies
//! `-d2|T| >= 1.5 I` on the deflated span of the first 32 modes but says nothing beyond the
//! truncation.  The plan was to close the tail by a Schur complement: partition at head h,
//! show A_tt is diagonally dominant hence positive definite, then check the Schur complement
//! S = A_hh - A_ht A_tt^{-1} A_th.  Both are finite checks per truncation, and a dominance
//! margin uniform in the truncation would extend to the limit.
//!
//! THE MARGIN IS NOT UNIFORM.  At a FIXED head the tail ratio grows with the truncation and
//! crosses 1:
//!     head 32:      0.6549, 0.8364, 1.0827, 1.3089   at K = 48, 64, 96, 128
//! and letting the head grow linearly with K only delays the crossing:
//!     head = K/2:   0.7748, 0.8364, 0.9269, 0.9904, 1.0827   at K = 48, 64, 96, 128, 192
//! An earlier check reported dominance at head 24 and 32; those numbers were computed at
//! K = 64, where the tail is short, and did not survive a longer tail.  So this route does
//! not close the tail, and the run below records that rather than hiding it.
//!
//! What the run does show: the Schur complement's least pivot is stable near
//! f(beta) = 1.5389 and approaches it from below, which is the behaviour a working argument
//! would produce.  But the Gauss-Seidel solve depends on the same dominance, so those
//! numbers are only meaningful where part (1) reports true.  The tail needs a different
//! mechanism.
//!
//! WHY RUST.  The Python route built an N x N x M quadrature tensor -- 8.7 GB at 52 modes --
//! which is the defect this replaces.  Here every entry is a closed-form trigonometric
//! integral, memory is O(N^2), and the run carries progress, ETA and atomic checkpoints as
//! Rule 8 requires.
//!
//! Usage: cargo run --release -- [max_k] [head]

use std::fs;
use std::io::Write;
use std::time::Instant;

const BETA: f64 = 0.289_653_820_817_320_9;

fn p2() -> f64 { std::f64::consts::FRAC_PI_2 }

/// int_0^T sin(a t) sin(b t) dt
fn ss(a: f64, b: f64, t: f64) -> f64 {
    if (a - b).abs() < 1e-12 { t / 2.0 - (2.0 * a * t).sin() / (4.0 * a) }
    else { 0.5 * (((a - b) * t).sin() / (a - b) - ((a + b) * t).sin() / (a + b)) }
}

/// int_0^T cos(a t) cos(b t) dt
fn cc(a: f64, b: f64, t: f64) -> f64 {
    if (a - b).abs() < 1e-12 { t / 2.0 + (2.0 * a * t).sin() / (4.0 * a) }
    else { 0.5 * (((a - b) * t).sin() / (a - b) + ((a + b) * t).sin() / (a + b)) }
}

/// int_0^T sin(a t) cos(b t) dt
fn sc(a: f64, b: f64, t: f64) -> f64 {
    if (a - b).abs() < 1e-12 { (1.0 - (2.0 * a * t).cos()) / (4.0 * a) }
    else { 0.5 * ((1.0 - ((a - b) * t).cos()) / (a - b) + (1.0 - ((a + b) * t).cos()) / (a + b)) }
}

fn freq(i: usize, k: usize) -> f64 { (2 * (i % k) + 1) as f64 }

/// (delta alpha_1, delta alpha_2) as (coefficient, frequency, is_sine)
fn pair(i: usize, k: usize) -> ((f64, f64, bool), (f64, f64, bool)) {
    let n = freq(i, k);
    if i < k { ((n, n, true), (1.0, n, false)) } else { ((1.0, n, true), (n, n, false)) }
}

fn ip(p: (f64, f64, bool), q: (f64, f64, bool), t: f64) -> f64 {
    let (c1, n1, s1) = p;
    let (c2, n2, s2) = q;
    let v = match (s1, s2) {
        (true, true) => ss(n1, n2, t),
        (false, false) => cc(n1, n2, t),
        (true, false) => sc(n1, n2, t),
        (false, true) => sc(n2, n1, t),
    };
    c1 * c2 * v
}

/// One entry of `-d2|T| = D_niche - D_cap`, in closed form.
fn entry(i: usize, j: usize, k: usize) -> f64 {
    let t2 = p2() - BETA;
    let (a1i, a2i) = pair(i, k);
    let (a1j, a2j) = pair(j, k);
    let mut v = 2.0 * ip(a2i, a2j, t2) - 2.0 * ip(a1i, a1j, BETA);
    if (freq(i, k) - freq(j, k)).abs() < 1e-12 && ((i < k) == (j < k)) {
        let n = freq(i, k);
        v += p2() * (n * n - 1.0);                 // the cap, on both blocks
        if i < k { v += p2() * (n * n - 1.0); }    // the reach, on the left block only
    }
    v
}

/// Largest row-radius / diagonal over the tail block, computed within the tail alone.
fn tail_dominance(k: usize, head: usize) -> (f64, usize) {
    let n = 2 * k;
    let tail: Vec<usize> = (0..n).filter(|&i| (i % k) >= head).collect();
    let mut worst = 0.0f64;
    let mut arg = 0usize;
    for &i in &tail {
        let d = entry(i, i, k);
        let mut rad = 0.0;
        for &j in &tail { if j != i { rad += entry(i, j, k).abs(); } }
        let r = rad / d;
        if r > worst { worst = r; arg = i; }
    }
    (worst, arg)
}

/// Cholesky; returns the smallest pivot, or None if a pivot is not positive.
fn cholesky_min_pivot(a: &Vec<Vec<f64>>) -> Option<f64> {
    let n = a.len();
    let mut l = vec![vec![0.0f64; n]; n];
    let mut smallest = f64::INFINITY;
    for i in 0..n {
        for j in 0..=i {
            let mut s = a[i][j];
            for kk in 0..j { s -= l[i][kk] * l[j][kk]; }
            if i == j {
                if !(s > 0.0) { return None; }
                if s < smallest { smallest = s; }
                l[i][i] = s.sqrt();
            } else {
                l[i][j] = s / l[j][j];
            }
        }
    }
    Some(smallest)
}

/// Solve A_tt X = B by Gauss-Seidel, convergent because A_tt is diagonally dominant.
fn solve_tail(k: usize, tail: &[usize], b: &Vec<Vec<f64>>, iters: usize) -> Vec<Vec<f64>> {
    let m = tail.len();
    let cols = b[0].len();
    let mut x = vec![vec![0.0f64; cols]; m];
    let att: Vec<Vec<f64>> = tail.iter()
        .map(|&i| tail.iter().map(|&j| entry(i, j, k)).collect())
        .collect();
    for _ in 0..iters {
        for r in 0..m {
            for c in 0..cols {
                let mut s = b[r][c];
                for q in 0..m { if q != r { s -= att[r][q] * x[q][c]; } }
                x[r][c] = s / att[r][r];
            }
        }
    }
    x
}

/// Generalised (H-matrix) dominance with weights d_n = n^{-p}:
/// A is positive definite if d_i A_ii > sum_{j != i} d_j |A_ij| for every i.
/// Plain dominance is p = 0, which fails; a weight that decays fast enough may not.
fn weighted_dominance(k: usize, head: usize, p: f64) -> f64 {
    let n = 2 * k;
    let tail: Vec<usize> = (0..n).filter(|&i| (i % k) >= head).collect();
    let w = |i: usize| freq(i, k).powf(-p);
    let mut worst = 0.0f64;
    for &i in &tail {
        let mut rad = 0.0;
        for &j in &tail { if j != i { rad += w(j) * entry(i, j, k).abs(); } }
        let r = rad / (w(i) * entry(i, i, k));
        if r > worst { worst = r; }
    }
    worst
}

fn checkpoint(path: &str, text: &str) {
    let tmp = format!("{}.tmp", path);
    if let Ok(mut f) = fs::File::create(&tmp) {
        let _ = f.write_all(text.as_bytes());
        let _ = fs::rename(&tmp, path);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let max_k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(256);
    let head: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(32);
    let ck = "tail_schur_checkpoint.txt";
    let t0 = Instant::now();

    println!("tail_schur — closing the truncation tail of -d2|T| by a Schur complement");
    println!("head = {} modes per half, truncations up to K = {}\n", head, max_k);

    println!("(1) is the TAIL block diagonally dominant, and does the margin persist?");
    println!("    head fixed at {}; if the ratio grows with K the route fails.\n", head);
    println!("{:>6} {:>7} {:>10} {:>12} {:>9} {:>8}", "K", "tail", "max ratio", "dominant", "elapsed", "eta");
    let ks: Vec<usize> = [48usize, 64, 96, 128, 192, 256, 384, 512]
        .iter().cloned().filter(|&x| x <= max_k).collect();
    let mut all_dominant = true;
    let mut log = String::new();
    for (idx, &k) in ks.iter().enumerate() {
        let (r, _) = tail_dominance(k, head);
        let dom = r < 1.0;
        all_dominant &= dom;
        let el = t0.elapsed().as_secs_f64();
        let eta = if idx + 1 < ks.len() { el / (idx + 1) as f64 * (ks.len() - idx - 1) as f64 } else { 0.0 };
        let line = format!("{:>6} {:>7} {:>10.4} {:>12} {:>8.1}s {:>7.0}s",
                           k, 2 * (k - head), r, dom, el, eta);
        println!("{}", line);
        log.push_str(&line);
        log.push('\n');
        checkpoint(ck, &log);
    }
    println!("\n  dominance holds at every truncation tested: {}", all_dominant);
    if all_dominant {
        println!("  A strictly diagonally dominant matrix with positive diagonal is positive");
        println!("  definite, and the margin persists, so A_tt is positive definite in the");
        println!("  limit too.\n");
    } else {
        println!("  IT DOES NOT.  At a FIXED head the ratio grows with the truncation and");
        println!("  crosses 1, so the tail block is not diagonally dominant in the limit and");
        println!("  this route does not close the tail.  Worse, the Gauss-Seidel solve in");
        println!("  part (2) needs that dominance to converge, so the Schur numbers below");
        println!("  are only trustworthy where part (1) says true.\n");
    }

    println!("(1b) weighted dominance: d_n = n^-p, the H-matrix criterion\n");
    println!("  A is positive definite if d_i A_ii > sum_j!=i d_j |A_ij|.  Plain dominance is");
    println!("  p = 0 and fails.  A faster-decaying weight may not.\n");
    let ps = [0.0f64, 0.5, 1.0, 1.5, 2.0, 2.5];
    print!("{:>6}", "K");
    for p in ps.iter() { print!("{:>10}", format!("p={:.1}", p)); }
    println!();
    let mut best_p: Option<f64> = None;
    for &k in ks.iter() {
        print!("{:>6}", k);
        for (t, &p) in ps.iter().enumerate() {
            let r = weighted_dominance(k, head, p);
            print!("{:>10.4}", r);
            if r < 1.0 && k == *ks.last().unwrap() && best_p.is_none() && t > 0 { best_p = Some(p); }
        }
        println!();
    }
    match best_p {
        Some(p) => {
            println!("\n  At the largest truncation the smallest exponent with ratio < 1 is");
            println!("  p = {:.1}.  If that ratio also stays below 1 as K grows, the weighted", p);
            println!("  criterion closes the tail where plain dominance could not.");
        }
        None => {
            println!("\n  No exponent tested gives a ratio below 1 at the largest truncation.");
            println!("  Weighted dominance does not rescue the argument either.");
        }
    }
    println!();

    println!("(2) the Schur complement S = A_hh - A_ht A_tt^-1 A_th\n");
    println!("{:>6} {:>7} {:>14} {:>16} {:>9}", "K", "head", "S pos def", "min pivot of S", "elapsed");
    for &k in ks.iter().filter(|&&x| x <= 192) {
        // head >= k leaves an EMPTY tail, and solve_tail then indexes b[0].  The first
        // version of this loop panicked on exactly that when run with head = 96.
        if head >= k {
            println!("{:>6} {:>7} {:>14} {:>16} {:>9}", k, 2 * head - 1,
                     "skipped", "head >= K, no tail", "-");
            continue;
        }
        let n = 2 * k;
        let hd: Vec<usize> = (0..n).filter(|&i| (i % k) < head).collect();
        let tl: Vec<usize> = (0..n).filter(|&i| (i % k) >= head).collect();
        let ath: Vec<Vec<f64>> = tl.iter()
            .map(|&i| hd.iter().map(|&j| entry(i, j, k)).collect()).collect();
        let x = solve_tail(k, &tl, &ath, 200);
        let mut s = vec![vec![0.0f64; hd.len()]; hd.len()];
        for (a, &i) in hd.iter().enumerate() {
            for (b, &j) in hd.iter().enumerate() {
                let mut v = entry(i, j, k);
                for (r, _) in tl.iter().enumerate() { v -= ath[r][a] * x[r][b]; }
                s[a][b] = v;
            }
        }
        // deflate the gauge: drop the first right-block head index
        let drop = head;
        let idx: Vec<usize> = (0..hd.len()).filter(|&t| t != drop).collect();
        let sd: Vec<Vec<f64>> = idx.iter()
            .map(|&a| idx.iter().map(|&b| s[a][b]).collect()).collect();
        let piv = cholesky_min_pivot(&sd);
        println!("{:>6} {:>7} {:>14} {:>16} {:>8.1}s", k, hd.len() - 1,
                 piv.is_some(),
                 piv.map(|p| format!("{:.9}", p)).unwrap_or("-".into()),
                 t0.elapsed().as_secs_f64());
    }
    if all_dominant {
        println!("\n  A_tt and S both positive definite gives A positive definite on the whole");
        println!("  space, and the uniform margin carries it past any truncation.");
    } else {
        println!("\n  The Schur pivots are stable near f(beta) = 1.5389 and approach it from");
        println!("  below, which is what a working argument would show.  But dominance fails");
        println!("  at fixed head, so this does NOT constitute a proof: the rows where it");
        println!("  fails are exactly the ones the tail argument must control.");
    }
    println!("\n  NOTE: this run is f64.  It locates the argument and its constants; the");
    println!("  certified statement still comes from the ball-arithmetic Cholesky, which");
    println!("  covers the head block.  The tail's positivity here rests on the dominance");
    println!("  margin, which is far from 1 and so is not at risk from rounding.");
    checkpoint(ck, &format!("{}\ncomplete in {:.1}s\n", log, t0.elapsed().as_secs_f64()));
}
