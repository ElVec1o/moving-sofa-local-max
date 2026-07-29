// sigma_struct.rs — closed-form structure-following second variation of
// Romik's Sigma, in pure Rust (no crates, no BLAS).
//
// Replaces the numpy assembler.  Justified by the three structural facts
// established earlier: the per-arc Wirtinger integrands and the chord jets
// are TRAJECTORY-INDEPENDENT, the arc ranges are exactly
// {0, beta, pi/2-beta, pi/2}, and the junction response is null.  So the
// whole matrix is elementary trigonometric quadrature — no geometry oracle,
// no polygon booleans, no junction solve.  beta is closed form:
//     beta = atan( ( (sqrt2+1)^(1/3) - (sqrt2-1)^(1/3) ) / 2 ).
//
// Arc traversal (clockwise; area = -Green):
//   dA[pi/2->0] rA[0->pi/2] dB[pi/2->b] dX[b->B] dD[B->0]
//   rC[0->B]    dC[B->0]    rD[0->B]    rX[B->b] rB[b->pi/2]
// slots: p = mu-wall Wirtinger form, q = nu-wall, x = corner path;
// reflected arcs (r*) carry det(rho_0) = -1.
//
// build: rustc -O sigma_struct.rs -o sigma_struct
// run:   ./sigma_struct K [n_quad]

const PI: f64 = std::f64::consts::PI;

fn beta() -> f64 {
    let s2 = 2f64.sqrt();
    (((s2 + 1.0).cbrt() - (s2 - 1.0).cbrt()) * 0.5).atan()
}

/// Gauss–Legendre nodes/weights on [a,b] (Newton on P_n).
fn gauss_legendre(n: usize, a: f64, b: f64) -> (Vec<f64>, Vec<f64>) {
    let mut x = vec![0.0; n];
    let mut w = vec![0.0; n];
    let m = (n + 1) / 2;
    for i in 0..m {
        let mut z = (PI * (i as f64 + 0.75) / (n as f64 + 0.5)).cos();
        let mut pp = 0.0;
        for _ in 0..100 {
            let (mut p1, mut p2) = (1.0f64, 0.0f64);
            for j in 0..n {
                let p3 = p2;
                p2 = p1;
                p1 = ((2.0 * j as f64 + 1.0) * z * p2 - j as f64 * p3) / (j as f64 + 1.0);
            }
            pp = n as f64 * (z * p1 - p2) / (z * z - 1.0);
            let dz = p1 / pp;
            z -= dz;
            if dz.abs() < 1e-16 {
                break;
            }
        }
        let xm = 0.5 * (b + a);
        let xl = 0.5 * (b - a);
        x[i] = xm - xl * z;
        x[n - 1 - i] = xm + xl * z;
        let ww = 2.0 * xl / ((1.0 - z * z) * pp * pp);
        w[i] = ww;
        w[n - 1 - i] = ww;
    }
    (x, w)
}

#[inline]
fn fg(comp: usize, t: f64) -> (f64, f64) {
    let (c, s) = (t.cos(), t.sin());
    if comp == 0 { (c, -s) } else { (s, c) }
}

/// p, p+p'', q, q+q'', p', q', s   for eta = e_comp sin(2kt)
#[inline]
fn jets(comp: usize, k: f64, t: f64) -> [f64; 7] {
    let (f, g) = fg(comp, t);
    let kk = 2.0 * k;
    let s = (kk * t).sin();
    let sp = kk * (kk * t).cos();
    let spp = -kk * kk * (kk * t).sin();
    [f * s, 2.0 * g * sp + f * spp, g * s, -2.0 * f * sp + g * spp,
     g * s + f * sp, -f * s + g * sp, s]
}

/// delta(contact point) at parameter t, as (x,y)
#[inline]
fn dpt(refl: bool, slot: u8, t: f64, comp: usize, k: f64) -> (f64, f64) {
    let (c, s) = (t.cos(), t.sin());
    let j = jets(comp, k, t);
    let v = match slot {
        0 => (j[0] * c + j[4] * (-s), j[0] * s + j[4] * c),      // p: p mu + p' nu
        1 => (-j[5] * c + j[2] * (-s), -j[5] * s + j[2] * c),    // q: -q' mu + q nu
        _ => if comp == 0 { (j[6], 0.0) } else { (0.0, j[6]) },  // corner: eta
    };
    if refl { (v.0, -v.1) } else { v }
}

/// symmetric Jacobi eigenvalues
fn jacobi_eigenvalues(a: &mut Vec<Vec<f64>>) -> Vec<f64> {
    let n = a.len();
    for _sweep in 0..100 {
        let mut off = 0.0;
        for i in 0..n {
            for j in (i + 1)..n {
                off += a[i][j] * a[i][j];
            }
        }
        if off.sqrt() < 1e-13 {
            break;
        }
        for p in 0..n {
            for q in (p + 1)..n {
                if a[p][q].abs() < 1e-18 {
                    continue;
                }
                let theta = (a[q][q] - a[p][p]) / (2.0 * a[p][q]);
                let t = theta.signum() / (theta.abs() + (theta * theta + 1.0).sqrt());
                let c = 1.0 / (t * t + 1.0).sqrt();
                let s = t * c;
                for k in 0..n {
                    let akp = a[k][p];
                    let akq = a[k][q];
                    a[k][p] = c * akp - s * akq;
                    a[k][q] = s * akp + c * akq;
                }
                for k in 0..n {
                    let apk = a[p][k];
                    let aqk = a[q][k];
                    a[p][k] = c * apk - s * aqk;
                    a[q][k] = s * apk + c * aqk;
                }
            }
        }
    }
    (0..n).map(|i| a[i][i]).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k_max: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(10);
    let nq: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
    let b = beta();
    let pi2 = PI / 2.0;
    let bb = pi2 - b;
    let nq = if nq > 0 { nq } else { (8 * k_max + 200).min(4000) };

    // (reflected?, t_from, t_to, slot)  slot: 0=p, 1=q, 2=corner
    let tab: Vec<(bool, f64, f64, u8)> = vec![
        (false, pi2, 0.0, 0), (true, 0.0, pi2, 0),
        (false, pi2, b, 0),   (false, b, bb, 2),
        (false, bb, 0.0, 1),  (true, 0.0, bb, 1),
        (false, bb, 0.0, 1),  (true, 0.0, bb, 1),
        (true, bb, b, 2),     (true, b, pi2, 0),
    ];

    let modes: Vec<(usize, f64)> = (0..2)
        .flat_map(|c| (1..=k_max).map(move |k| (c, k as f64)))
        .collect();
    let n = modes.len();
    let mut q = vec![vec![0.0f64; n]; n];

    // ---- per-arc Wirtinger integrals ----
    for &(refl, t0, t1, slot) in &tab {
        let (lo, hi) = if t0 < t1 { (t0, t1) } else { (t1, t0) };
        if hi - lo < 1e-14 {
            continue;
        }
        let dir = if t1 > t0 { 1.0 } else { -1.0 };
        let fam = if refl { -1.0 } else { 1.0 };
        let sgn = 0.5 * dir * fam;
        let (xs, ws) = gauss_legendre(nq, lo, hi);
        // U[i][node], V[i][node]
        let mut u = vec![vec![0.0f64; nq]; n];
        let mut v = vec![vec![0.0f64; nq]; n];
        for (i, &(c, kk)) in modes.iter().enumerate() {
            for (m, &t) in xs.iter().enumerate() {
                let j = jets(c, kk, t);
                match slot {
                    0 => { u[i][m] = j[0]; v[i][m] = j[1]; }
                    1 => { u[i][m] = j[2]; v[i][m] = j[3]; }
                    _ => { u[i][m] = j[6]; v[i][m] = 2.0 * kk * (2.0 * kk * t).cos(); }
                }
            }
        }
        for i in 0..n {
            for jj in i..n {
                if slot == 2 && modes[i].0 == modes[jj].0 {
                    continue;
                }
                let mut acc = 0.0;
                for m in 0..nq {
                    // corner slot: the wedge eta_u ^ eta_v' polarizes with the
                    // DIFFERENCE (E is antisymmetric, so E*(W-W^T) is symmetric)
                    acc += ws[m] * if slot == 2 {
                        u[i][m] * v[jj][m] - u[jj][m] * v[i][m]
                    } else {
                        u[i][m] * v[jj][m] + u[jj][m] * v[i][m]
                    };
                }
                let e = if slot == 2 {
                    if modes[i].0 == 0 { 1.0 } else { -1.0 }
                } else { 1.0 };
                let val = sgn * e * 0.5 * acc;
                q[i][jj] += val;
                if jj != i { q[jj][i] += val; }
            }
        }
    }

    // ---- junction chords ----
    for idx in 0..tab.len() {
        let (r0, _, te, s0) = tab[idx];
        let (r1, ts, _, s1) = tab[(idx + 1) % tab.len()];
        let d0: Vec<(f64, f64)> = modes.iter().map(|&(c, kk)| dpt(r0, s0, te, c, kk)).collect();
        let d1: Vec<(f64, f64)> = modes.iter().map(|&(c, kk)| dpt(r1, s1, ts, c, kk)).collect();
        for i in 0..n {
            for jj in i..n {
                let w1 = d0[i].0 * d1[jj].1 - d0[i].1 * d1[jj].0;
                let w2 = d0[jj].0 * d1[i].1 - d0[jj].1 * d1[i].0;
                let val = 0.25 * (w1 + w2);
                q[i][jj] += val;
                if jj != i { q[jj][i] += val; }
            }
        }
    }

    // orientation (CW traversal => area = -Green) and d^2F/deps^2 convention
    for i in 0..n {
        for j in 0..n {
            q[i][j] *= -2.0;
        }
    }

    // emit the matrix for a LAPACK eigensolve (the O(n^3) step); the
    // expensive part -- assembly -- is done here.
    if std::env::var("DUMP").is_ok() {
        println!("{}", n);
        for i in 0..n {
            let row: Vec<String> = (0..n).map(|j| format!("{:.17e}", q[i][j])).collect();
            println!("{}", row.join(" "));
        }
        return;
    }

    // L^2 and H^1 normalized spectra
    for (name, h1) in [("L^2", false), ("H^1", true)] {
        let mut m = vec![vec![0.0f64; n]; n];
        for i in 0..n {
            for j in 0..n {
                let gi = if h1 { PI / 4.0 * (1.0 + 4.0 * modes[i].1 * modes[i].1) } else { PI / 4.0 };
                let gj = if h1 { PI / 4.0 * (1.0 + 4.0 * modes[j].1 * modes[j].1) } else { PI / 4.0 };
                m[i][j] = q[i][j] / (gi.sqrt() * gj.sqrt());
            }
        }
        let ev = jacobi_eigenvalues(&mut m);
        let mx = ev.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
        let mn = ev.iter().cloned().fold(f64::INFINITY, f64::min);
        println!("  K={:3}  {}: max={:+.6} min={:+.4}  {}",
                 k_max, name, mx, mn,
                 if mx < 0.0 { format!("NEG DEF m={:.6}", -mx) }
                 else { format!("NOT neg def") });
    }
}
