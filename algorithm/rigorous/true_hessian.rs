// TRUE Hessian blocks for the moving-sofa second variation (exact analytic
// oracle, f64).  Pure std Rust: no crates, flat ~MB memory, no OOM risk.
//
//   rustc -O true_hessian.rs -o true_hessian && ./true_hessian K [h]
//
// Progress + ETA per row; interim save (text matrix) after every row; safe to
// interrupt and re-run (resumes from the save file).
//
// Method: area of the perturbed sofa via Green's theorem over the analytic
// contact arcs, with the junction pair solved by damped Newton using the
// PROVED envelope-tangency Jacobians (D' = lam_D mu, B' = lam_B nu).  Hessian
// entries by 4-point cross stencils at step h (default 1e-3).  f64 quadrature
// error ~1e-13 on the area => ~1e-7 on entries: ample for the spectral trend.

const PHI: f64 = 0.03917736479008364;
const THETA: f64 = 0.68130150938272493;
const A1: f64 = 1.2103224220726888;
const A2: f64 = -0.25;
const B1: f64 = -0.52762459802678462;
const B2: f64 = 0.92025838516063763;
const C1: f64 = 0.62604552284846587;
const C2: f64 = -0.94475080394643075;
const D1: f64 = 1.3130227614242329;
const D2: f64 = -0.52538267041455443;
const E1: f64 = 1.2103224220726888;
const E2: f64 = 0.25;
const K11: f64 = -0.21032242207268876;
const K12: f64 = 0.25;
const K21: f64 = -0.91917929277159333;
const K22: f64 = 0.47240661975080547;
const K31: f64 = -0.61376322943025167;
const K32: f64 = 0.88962647900322186;
const K41: f64 = -0.30834716608891001;
const K42: f64 = 0.47240661975080547;
const K51: f64 = -1.0172040367878146;
const K52: f64 = 0.25;
const PI2: f64 = std::f64::consts::FRAC_PI_2;

#[derive(Clone, Copy)]
struct Jet {
    x: [f64; 2],
    xp: [f64; 2],
    xpp: [f64; 2],
}

// perturbation: coefficient list (comp 0=x/1=y, k, amplitude)
#[derive(Clone)]
struct Pert {
    terms: Vec<(usize, f64, f64)>,
    eps: f64,
}

fn traj(t: f64, pert: &Pert) -> Jet {
    // base c_G by phase
    let (v, vp, vpp): ([f64; 2], [f64; 2], [f64; 2]);
    let (kx, ky): (f64, f64);
    let (c, s) = (t.cos(), t.sin());
    if t <= PHI {
        v = [A1 * c + A2 * s - 1.0, -A2 * c + A1 * s - 0.5];
        vp = [-A1 * s + A2 * c, A2 * s + A1 * c];
        vpp = [-A1 * c - A2 * s, A2 * c - A1 * s];
        kx = K11; ky = K12;
    } else if t <= THETA {
        v = [-0.25 * t * t + B1 * t + B2, 0.5 * t - B1 - 1.0];
        vp = [-0.5 * t + B1, 0.5];
        vpp = [-0.5, 0.0];
        kx = K21; ky = K22;
    } else if t <= PI2 - THETA {
        v = [C1 - t, C2 + t];
        vp = [-1.0, 1.0];
        vpp = [0.0, 0.0];
        kx = K31; ky = K32;
    } else if t <= PI2 - PHI {
        v = [-0.5 * t + D1 - 1.0, -0.25 * t * t + D1 * t + D2];
        vp = [-0.5, -0.5 * t + D1];
        vpp = [0.0, -0.5];
        kx = K41; ky = K42;
    } else {
        v = [E1 * c + E2 * s - 0.5, -E2 * c + E1 * s - 1.0];
        vp = [-E1 * s + E2 * c, E2 * s + E1 * c];
        vpp = [-E1 * c - E2 * s, E2 * c - E1 * s];
        kx = K51; ky = K52;
    }
    // x = R v + kappa ; x' = R(v' + J v) ; x'' = R(v'' + 2 J v' - v)
    let rot = |u: [f64; 2]| [c * u[0] - s * u[1], s * u[0] + c * u[1]];
    let jmul = |u: [f64; 2]| [-u[1], u[0]];
    let x0 = rot(v);
    let a1v = [vp[0] + jmul(v)[0], vp[1] + jmul(v)[1]];
    let a2v = [vpp[0] + 2.0 * jmul(vp)[0] - v[0], vpp[1] + 2.0 * jmul(vp)[1] - v[1]];
    let mut j = Jet {
        x: [x0[0] + kx, x0[1] + ky],
        xp: rot(a1v),
        xpp: rot(a2v),
    };
    // add eps * eta
    for &(comp, k, a) in &pert.terms {
        let (sv, spv, sppv) = ((2.0 * k * t).sin(), 2.0 * k * (2.0 * k * t).cos(),
                               -4.0 * k * k * (2.0 * k * t).sin());
        j.x[comp] += pert.eps * a * sv;
        j.xp[comp] += pert.eps * a * spv;
        j.xpp[comp] += pert.eps * a * sppv;
    }
    j
}

fn contact(t: f64, j: &Jet, which: u8) -> ([f64; 2], [f64; 2]) {
    // value and EXACT tangent of A/B/C/D via envelope identities
    let (c, s) = (t.cos(), t.sin());
    let mu = [c, s];
    let nu = [-s, c];
    let dmu = j.xp[0] * mu[0] + j.xp[1] * mu[1];
    let dnu = j.xp[0] * nu[0] + j.xp[1] * nu[1];
    let ddmu = j.xpp[0] * mu[0] + j.xpp[1] * mu[1];
    let ddnu = j.xpp[0] * nu[0] + j.xpp[1] * nu[1];
    match which {
        0 => { // A = x + <x',mu>nu + mu ; A' = (2<x',nu> + <x'',mu> + 1) nu
            let lam = 2.0 * dnu + ddmu + 1.0;
            ([j.x[0] + dmu * nu[0] + mu[0], j.x[1] + dmu * nu[1] + mu[1]],
             [lam * nu[0], lam * nu[1]])
        }
        1 => { // B = x + <x',mu>nu ; B' = (2<x',nu> + <x'',mu>) nu
            let lam = 2.0 * dnu + ddmu;
            ([j.x[0] + dmu * nu[0], j.x[1] + dmu * nu[1]],
             [lam * nu[0], lam * nu[1]])
        }
        2 => { // C = x - <x',nu>mu + nu ; C' = (lam_D - 1) mu
            let lam = 2.0 * dmu - ddnu - 1.0;
            ([j.x[0] - dnu * mu[0] + nu[0], j.x[1] - dnu * mu[1] + nu[1]],
             [lam * mu[0], lam * mu[1]])
        }
        _ => { // D = x - <x',nu>mu ; D' = (2<x',mu> - <x'',nu>) mu
            let lam = 2.0 * dmu - ddnu;
            ([j.x[0] - dnu * mu[0], j.x[1] - dnu * mu[1]],
             [lam * mu[0], lam * mu[1]])
        }
    }
}

// 40-point Gauss-Legendre nodes on [-1,1] via Newton on P_n
fn gl40() -> ([f64; 40], [f64; 40]) {
    let n = 40usize;
    let mut xs = [0.0f64; 40];
    let mut ws = [0.0f64; 40];
    for i in 0..n {
        let mut x = (std::f64::consts::PI * (i as f64 + 0.75) / (n as f64 + 0.5)).cos();
        for _ in 0..60 {
            let (mut p0, mut p1) = (1.0f64, 0.0f64);
            for j in 0..n {
                let p2 = p1;
                p1 = p0;
                p0 = (((2 * j + 1) as f64) * x * p1 - (j as f64) * p2) / ((j + 1) as f64);
            }
            let dp = (n as f64) * (x * p0 - p1) / (x * x - 1.0);
            let dx = p0 / dp;
            x -= dx;
            if dx.abs() < 1e-16 {
                let (mut q0, mut q1) = (1.0f64, 0.0f64);
                for j in 0..n {
                    let q2 = q1; q1 = q0;
                    q0 = (((2 * j + 1) as f64) * x * q1 - (j as f64) * q2) / ((j + 1) as f64);
                }
                let dq = (n as f64) * (x * q0 - q1) / (x * x - 1.0);
                ws[i] = 2.0 / ((1.0 - x * x) * dq * dq);
                break;
            }
        }
        xs[i] = x;
    }
    (xs, ws)
}

fn integrate<F: Fn(f64) -> f64>(f: &F, panels: &[f64], xs: &[f64; 40], ws: &[f64; 40]) -> f64 {
    let mut tot = 0.0;
    for w in panels.windows(2) {
        let (a, b) = (w[0], w[1]);
        if b <= a { continue; }
        let (m, r) = (0.5 * (a + b), 0.5 * (b - a));
        let mut sacc = 0.0;
        for i in 0..40 { sacc += ws[i] * f(m + r * xs[i]); }
        tot += r * sacc;
    }
    tot
}

fn solve_junction_clamped(pert: &Pert, which: u8, t0: f64, s0: f64,
                          tlo: f64, thi: f64) -> (f64, f64, f64) {
    // Env(t) = x(s) with t CLAMPED to one smooth phase side [tlo, thi]:
    // within a phase the residual is smooth and Newton is quadratic.
    let (mut t, mut s) = (t0.max(tlo).min(thi), s0);
    let clamp = |v: f64| v.max(tlo).min(thi);
    let res = |t: f64, s: f64| -> [f64; 2] {
        let (p, _) = contact(t, &traj(t, pert), which);
        let xj = traj(s, pert);
        [p[0] - xj.x[0], p[1] - xj.x[1]]
    };
    let mut r = res(t, s);
    let mut nr = (r[0] * r[0] + r[1] * r[1]).sqrt();
    for _ in 0..60 {
        if nr < 1e-13 { break; }
        let (_, dp) = contact(t, &traj(t, pert), which);
        let xp = traj(s, pert).xp;
        let (a, b, c, d) = (dp[0], -xp[0], dp[1], -xp[1]);
        let det = a * d - b * c;
        let dt = (-r[0] * d + r[1] * b) / det;
        let ds = (c * r[0] - a * r[1]) / det;
        let mut lam = 1.0;
        loop {
            let (t2, s2) = (clamp(t + lam * dt), s + lam * ds);
            let r2 = res(t2, s2);
            let nr2 = (r2[0] * r2[0] + r2[1] * r2[1]).sqrt();
            if nr2 < nr { t = t2; s = s2; r = r2; nr = nr2; break; }
            lam *= 0.5;
            if lam < 1e-10 { return (t, s, nr); }
        }
    }
    (t, s, nr)
}

fn solve_junction(pert: &Pert, which: u8, t0: f64, s0: f64) -> (f64, f64) {
    // side-resolved: the base junction parameter sits EXACTLY on a phase kink
    // of c_G'', so solve clamped to each smooth side and keep the converged
    // side (the piecewise residual defeats plain Newton at the kink).
    let tk = if which == 3 { THETA } else { PI2 - THETA }; // D- vs B-junction kink
    let w = 0.25;
    let (ta, sa, ra) = solve_junction_clamped(pert, which, t0.min(tk), s0, tk - w, tk);
    let (tb, sb, rb) = solve_junction_clamped(pert, which, t0.max(tk), s0, tk, tk + w);
    // BRANCH CONTINUITY: among converged sides, take the root CLOSEST to the
    // warm start t0 (residual-based choice can jump to a second crossing when
    // both sides converge -- the multi-crossing branch bug in new clothing).
    let ok_a = ra < 1e-11;
    let ok_b = rb < 1e-11;
    if ok_a && ok_b {
        if (ta - t0).abs() <= (tb - t0).abs() { (ta, sa) } else { (tb, sb) }
    } else if ok_a { (ta, sa) }
    else if ok_b { (tb, sb) }
    else if ra <= rb { (ta, sa) } else { (tb, sb) }
}

#[allow(dead_code)]
fn solve_junction_old(pert: &Pert, which: u8, t0: f64, s0: f64) -> (f64, f64) {
    let (mut t, mut s) = (t0, s0);
    let res = |t: f64, s: f64| -> [f64; 2] {
        let (p, _) = contact(t, &traj(t, pert), which);
        let xj = traj(s, pert);
        [p[0] - xj.x[0], p[1] - xj.x[1]]
    };
    let mut r = res(t, s);
    let mut nr = (r[0] * r[0] + r[1] * r[1]).sqrt();
    for _ in 0..60 {
        if nr < 1e-14 { break; }
        let (_, dp) = contact(t, &traj(t, pert), which);
        let xp = traj(s, pert).xp;
        let (a, b, c, d) = (dp[0], -xp[0], dp[1], -xp[1]);
        let det = a * d - b * c;
        let dt = (-r[0] * d + r[1] * b) / det;
        let ds = (c * r[0] - a * r[1]) / det;
        let mut lam = 1.0;
        loop {
            let (t2, s2) = (t + lam * dt, s + lam * ds);
            let r2 = res(t2, s2);
            let nr2 = (r2[0] * r2[0] + r2[1] * r2[1]).sqrt();
            if nr2 < nr { t = t2; s = s2; r = r2; nr = nr2; break; }
            lam *= 0.5;
            if lam < 1e-9 { return (t, s); }
        }
    }
    (t, s)
}

fn junctions_continued(pert: &Pert, nsteps: usize) -> (f64, f64, f64, f64) {
    // eps-continuation: walk eps from 0 to pert.eps in nsteps, warm-starting
    // each junction Newton from the previous solution.  This tracks the
    // ORIGINAL root branch through the multi-crossing landscape and prevents
    // basin jumps (the corruption seen without it).
    let (mut bd, mut bx2) = (THETA, PI2 - PHI);
    let (mut bb, mut bx1) = (PI2 - THETA, PHI);
    for i in 1..=nsteps {
        let p = Pert {
            terms: pert.terms.clone(),
            eps: pert.eps * (i as f64) / (nsteps as f64),
        };
        let (a, b) = solve_junction(&p, 3, bd, bx2);
        bd = a; bx2 = b;
        let (c, d) = solve_junction(&p, 1, bb, bx1);
        bb = c; bx1 = d;
    }
    (bd, bx2, bx1, bb)
}

fn area(pert: &Pert, gl: &([f64; 40], [f64; 40])) -> f64 {
    let (xs, ws) = gl;
    let (bd, bx2, bx1, bb) = junctions_continued(pert, 16);
    let kinks = [PHI, THETA, PI2 - THETA, PI2 - PHI];
    let mut extra: Vec<f64> = Vec::new();
    for &(_, k, _) in &pert.terms { let _ = k; }
    // frequency-aware panels: subpanel length <= 2 wavelengths of the highest
    // perturbation mode, so GL40 keeps >= 20 nodes per wavelength.
    let kmaxf = pert.terms.iter().map(|&(_, k, _)| k).fold(1.0f64, f64::max);
    let dxmax = (std::f64::consts::PI / kmaxf) * 2.0;
    let panels = |lo: f64, hi: f64| -> Vec<f64> {
        let mut v = vec![lo];
        for &k in kinks.iter() { if k > lo && k < hi { v.push(k); } }
        for &e in extra.iter() { if e > lo && e < hi { v.push(e); } }
        v.push(hi);
        v.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let mut out = vec![v[0]];
        for w in v.windows(2) {
            let (a, b) = (w[0], w[1]);
            if b <= a { continue; }
            let nsub = ((b - a) / dxmax).ceil().max(1.0) as usize;
            for m in 1..=nsub { out.push(a + (b - a) * (m as f64) / (nsub as f64)); }
        }
        out
    };
    let wedge = |which: u8| move |t: f64| -> f64 {
        let j = traj(t, pert);
        let (p, dp) = contact(t, &j, which);
        p[0] * dp[1] - p[1] * dp[0]
    };
    let xw = |t: f64| -> f64 {
        let j = traj(t, pert);
        j.x[0] * j.xp[1] - j.x[1] * j.xp[0]
    };
    let ia = integrate(&wedge(0), &panels(0.0, PI2), xs, ws);
    let ic = integrate(&wedge(2), &panels(0.0, PI2), xs, ws);
    let id = integrate(&wedge(3), &panels(0.0, bd), xs, ws);
    let ix = integrate(&xw, &panels(bx1, bx2), xs, ws);
    let ib = integrate(&wedge(1), &panels(bb, PI2), xs, ws);
    let cval = |t: f64, which: u8| contact(t, &traj(t, pert), which).0;
    let seg = |p0: [f64; 2], p1: [f64; 2]| 0.5 * (p0[0] * p1[1] - p1[0] * p0[1]);
    0.5 * (ia + ic + id - ix + ib)
        + seg(cval(PI2, 0), cval(0.0, 2))
        + seg(cval(PI2, 2), cval(0.0, 3))
        + seg(cval(PI2, 1), cval(0.0, 0))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 && args[1] == "probe" {
        // ./true_hessian probe <eps> <terms-file: lines "comp k coeff">
        let eps: f64 = args[2].parse().unwrap();
        let txt = std::fs::read_to_string(&args[3]).unwrap();
        let mut terms: Vec<(usize, f64, f64)> = Vec::new();
        for line in txt.lines() {
            let f: Vec<f64> = line.split_whitespace()
                .map(|x| x.parse().unwrap()).collect();
            terms.push((f[0] as usize, f[1], f[2]));
        }
        let gl = gl40();
        let pert = Pert { terms, eps };
        let (bd, bx2, bx1, bb) = junctions_continued(&pert, 16);
        println!("junctions: bd={:.15} bx2={:.15} bx1={:.15} bb={:.15}",
                 bd, bx2, bx1, bb);
        println!("area = {:.17}", area(&pert, &gl));
        return;
    }
    if args.len() > 1 && args[1] == "cross" {
        // ./true_hessian cross <K0> <L> <h>: rectangular coupling block
        // rows: slope-free low modes v_k (k=3..K0, both comps);
        // cols: tail modes w_l = sin2lt - (l/(l+2)) sin(2(l+2)t), l=K0+1..L
        //       (slope-free, frequencies >= K0+1: exactly G-orthogonal to lows).
        let k0: usize = args[2].parse().unwrap();
        let lmax: usize = args[3].parse().unwrap();
        let h: f64 = args[4].parse().unwrap();
        let gl = gl40();
        let mut lows: Vec<Vec<(usize, f64, f64)>> = Vec::new();
        if k0 == 0 {
            // slope-carrier rows: pure sin(2t), sin(4t) per component
            for c in 0..2usize {
                lows.push(vec![(c, 1.0, 1.0)]);
                lows.push(vec![(c, 2.0, 1.0)]);
            }
        } else {
            for c in 0..2usize {
                for k in 3..=k0 {
                    let kf = k as f64;
                    let sgn = if k % 2 == 0 { 1.0 } else { -1.0 };
                    lows.push(vec![(c, kf, 1.0), (c, 1.0, -kf * (1.0 - sgn) / 2.0),
                                   (c, 2.0, -kf * (1.0 + sgn) / 4.0)]);
                }
            }
        }
        let tail_start = if k0 == 0 { 65 } else { k0 + 1 };
        let mut tails: Vec<Vec<(usize, f64, f64)>> = Vec::new();
        for c in 0..2usize {
            for l in tail_start..=lmax {
                let lf = l as f64;
                tails.push(vec![(c, lf, 1.0), (c, lf + 2.0, -lf / (lf + 2.0))]);
            }
        }
        let (nr, nc) = (lows.len(), tails.len());
        let a0 = area(&Pert { terms: vec![], eps: 0.0 }, &gl);
        println!("A0 = {:.15}; cross block {} x {}", a0, nr, nc);
        let save = format!("cross_K{}_L{}.txt", k0, lmax);
        let mut q = vec![vec![f64::NAN; nc]; nr];
        if let Ok(txt) = std::fs::read_to_string(&save) {
            for (i, line) in txt.lines().enumerate() {
                for (j, tok) in line.split_whitespace().enumerate() {
                    if let Ok(v) = tok.parse::<f64>() { q[i][j] = v; }
                }
            }
            println!("resumed");
        }
        let g = |terms: Vec<(usize, f64, f64)>, eps: f64| -> f64 {
            area(&Pert { terms, eps }, &gl) - a0
        };
        let t0 = std::time::Instant::now();
        for i in 0..nr {
            if q[i].iter().all(|v| v.is_finite()) { continue; }
            for j in 0..nc {
                if q[i][j].is_finite() { continue; }
                let merge = |sj: f64| -> Vec<(usize, f64, f64)> {
                    let mut v: Vec<(usize, f64, f64)> = lows[i].clone();
                    for &(c, k, a) in &tails[j] { v.push((c, k, sj * a)); }
                    v
                };
                let mc = merge(1.0).iter().map(|&(_, _, a)| a.abs())
                    .fold(0.0f64, f64::max);
                let fmax = merge(1.0).iter().map(|&(_, k, _)| k)
                    .fold(1.0f64, f64::max);
                // respect the H^2 scale: the stencil must keep eps*||eta''||
                // small (else the envelope speeds lam are corrupted O(1))
                let hh = (h / (1.0 + mc)).min(0.02 / (4.0 * fmax * fmax));
                let gpp = g(merge(1.0), hh);
                let gmm = g(merge(1.0), -hh);
                let gpm = g(merge(-1.0), hh);
                let gmp = g(merge(-1.0), -hh);
                q[i][j] = (gpp + gmm - gpm - gmp) / (4.0 * hh * hh);
            }
            let txt: String = q.iter().map(|row| row.iter()
                .map(|v| format!("{:.17e}", v)).collect::<Vec<_>>().join(" "))
                .collect::<Vec<_>>().join("
");
            std::fs::write(&save, txt).unwrap();
            let el = t0.elapsed().as_secs_f64();
            let frac = (i + 1) as f64 / nr as f64;
            println!("row {:>3}/{}  elapsed {:6.1}s  ETA {:6.1}s",
                     i + 1, nr, el, el / frac * (1.0 - frac));
        }
        println!("saved {}", save);
        return;
    }
    let kmax: usize = if args.len() > 1 { args[1].parse().unwrap() } else { 24 };
    let h: f64 = if args.len() > 2 { args[2].parse().unwrap() } else { 1e-3 };
    let gl = gl40();
    // Endpoint-slope-free basis: v_k = sin(2kt) + a_k sin(2t) + b_k sin(4t)
    // with v'(0) = v'(pi/2) = 0 (a_k = -k(1-(-1)^k)/2, b_k = -k(1+(-1)^k)/4),
    // k = 3..K.  On this subspace all endpoint jets vanish, the outer corners
    // are inert, and the chord-closed analytic oracle EQUALS the true F.
    let mut modes: Vec<Vec<(usize, f64, f64)>> = Vec::new();
    for c in 0..2usize {
        for k in 3..=kmax {
            let kf = k as f64;
            let sgn = if k % 2 == 0 { 1.0 } else { -1.0 };
            let a = -kf * (1.0 - sgn) / 2.0;
            let b = -kf * (1.0 + sgn) / 4.0;
            modes.push(vec![(c, kf, 1.0), (c, 1.0, a), (c, 2.0, b)]);
        }
    }
    let n = modes.len();

    let a0 = area(&Pert { terms: vec![], eps: 0.0 }, &gl);
    println!("A(c_G) = {:.15}  (target 2.219531668871968)", a0);

    let save = format!("true_hessian_K{}_rust.txt", kmax);
    let mut q = vec![vec![f64::NAN; n]; n];
    if let Ok(txt) = std::fs::read_to_string(&save) {
        for (i, line) in txt.lines().enumerate() {
            for (j, tok) in line.split_whitespace().enumerate() {
                if let Ok(v) = tok.parse::<f64>() { q[i][j] = v; }
            }
        }
        println!("resumed from {}", save);
    }
    let g = |terms: Vec<(usize, f64, f64)>, eps: f64| -> f64 {
        area(&Pert { terms, eps }, &gl) - a0
    };
    let t_start = std::time::Instant::now();
    let total = (n * (n + 1) / 2) as f64;
    let mut done = 0f64;
    for i in 0..n {
        let row_done = (i..n).all(|j| q[i][j].is_finite());
        if !row_done {
            for j in i..n {
                if q[i][j].is_finite() { done += 1.0; continue; }
                let merge = |si: f64, sj: f64| -> Vec<(usize, f64, f64)> {
                    let mut v: Vec<(usize, f64, f64)> = Vec::new();
                    for &(c, k, a) in &modes[i] { v.push((c, k, si * a)); }
                    for &(c, k, a) in &modes[j] { v.push((c, k, sj * a)); }
                    v
                };
                let mc = merge(1.0, 1.0).iter().map(|&(_, _, a)| a.abs())
                    .fold(0.0f64, f64::max);
                let hh = h / (1.0 + mc);
                let val = if i == j {
                    let gp = g(merge(1.0, 0.0), hh);
                    let gm = g(merge(1.0, 0.0), -hh);
                    (gp + gm) / (hh * hh)
                } else {
                    let gpp = g(merge(1.0, 1.0), hh);
                    let gmm = g(merge(1.0, 1.0), -hh);
                    let gpm = g(merge(1.0, -1.0), hh);
                    let gmp = g(merge(1.0, -1.0), -hh);
                    (gpp + gmm - gpm - gmp) / (4.0 * hh * hh)
                };
                q[i][j] = val;
                q[j][i] = val;
                done += 1.0;
            }
            let txt: String = q.iter()
                .map(|row| row.iter().map(|v| format!("{:.17e}", v))
                     .collect::<Vec<_>>().join(" "))
                .collect::<Vec<_>>().join("\n");
            std::fs::write(&save, txt).unwrap();
            let el = t_start.elapsed().as_secs_f64();
            let frac = done / total;
            println!("row {:>3}/{}  {:5.1}%  elapsed {:6.1}s  ETA {:6.1}s",
                     i + 1, n, 100.0 * frac, el, el / frac * (1.0 - frac));
        } else { done += (n - i) as f64; }
    }
    println!("saved {}", save);
}
