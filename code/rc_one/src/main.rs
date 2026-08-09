//! rc_one -- does the cut set stay an interval when r_ac = 1 on a positive-measure set?
//!
//! OBSTRUCTION (a).  The Sturm/Wronskian step in Anchor.lean (`wronskian_strictAntiOn`,
//! `pos_between_of_strictAnti`) needs q = r - 1 < 0 STRICTLY.  Class D only gives
//! 0 <= r_ac <= 1.  On a set where r_ac = 1 the Wronskian G = W' sin(.-x) - W cos(.-x)
//! has G' = 0, so it is only ANTITONE, not strictly antitone.  Claim under test: antitone
//! is enough, because the contradiction comes from G(x) = -W(x) < 0 and not from strictness.
//!
//! CONSTRUCTION.  A member of D is determined by its curvature radius.  With
//!     H(th) = cos th + (1/2) sin th + sin th * A(th) - cos th * B(th),
//!     A(th) = int_0^th r cos,   B(th) = int_0^th r sin,
//! one gets H(0) = 1, H'(0) = 1/2 and H'' + H = r automatically.  The gauge H(pi/2) = 1 is
//! then exactly the single linear constraint
//!     int_0^{pi/2} r_ac(s) cos s ds = 1/2 .
//! Extending by H(pi - th) = H(th) puts an atom of mass -2 H'(pi/2^-) at pi/2, gives
//! H'(pi) = -1/2, and makes the body rho-invariant about y = 1/2.  So ANY measurable
//! r_ac : [0,pi/2] -> [0,1] with int r cos = 1/2 and H'(pi/2^-) <= 0 gives a member of D
//! (hypotheses (c) and (d) are then checked, not imposed).
//!
//! Since int_0^{pi/2} cos = 1, the constraint int r cos = 1/2 with r <= 1 leaves r = 1 on a
//! set of measure at most pi/3, attained by r = 1_{[pi/6, pi/2]}: two thirds of the window,
//! running right up to the atom.  That is the extremal test case.
//!
//! WHAT IS MEASURED, per cap and over a grid of points p in C_2:
//!   1. #components of T(p) = {t in [0,pi/2] : W(t) > 0 and W(t+pi/2) > 0};
//!   2. #components of {W > 0} on [0,pi/2) and on (pi/2,pi] separately;
//!   3. #strict entries of T(p), which is the number of preimages under the union of the two
//!      truncated sweeps for a.e. p;
//!   4. the sign of W(pi/2) (it must be -p_y, so the atom is never in the cut set);
//!   5. hypotheses (c) c_y <= 1/2 and (d) a threshold T with alpha_2 > 0 before, alpha_1 >= 0
//!      after; and max r_ac, |{r_ac = 1}|.
//!
//! Usage: cargo run --release -- [pgrid] [ntheta]

use std::f64::consts::PI;

fn p2() -> f64 { PI / 2.0 }

/// A cap is its a.c. curvature radius on [0, pi/2], as a piecewise-constant table.
#[derive(Clone)]
struct Cap {
    name: &'static str,
    /// (start, end, value) covering [0, pi/2] left to right, values in [0,1].
    pieces: Vec<(f64, f64, f64)>,
}

impl Cap {
    fn r(&self, th: f64) -> f64 {
        // mirror: r(pi - th) = r(th)
        let t = if th > p2() { PI - th } else { th };
        for &(a, b, v) in &self.pieces {
            if t >= a && t <= b { return v; }
        }
        0.0
    }
    /// int_0^th r cos and int_0^th r sin, exactly (r piecewise constant), th in [0, pi/2].
    fn ab(&self, th: f64) -> (f64, f64) {
        let (mut a, mut b) = (0.0f64, 0.0f64);
        for &(s, e, v) in &self.pieces {
            let lo = s.min(th);
            let hi = e.min(th);
            if hi > lo {
                a += v * (hi.sin() - lo.sin());
                b += v * (lo.cos() - hi.cos());
            }
        }
        (a, b)
    }
    /// H and H' on [0, pi/2] from the ODE; the mirror gives [pi/2, pi].
    fn h_half(&self, th: f64) -> (f64, f64) {
        let (a, b) = self.ab(th);
        let h = th.cos() + 0.5 * th.sin() + th.sin() * a - th.cos() * b;
        let hp = -th.sin() + 0.5 * th.cos() + th.cos() * a + th.sin() * b;
        (h, hp)
    }
    /// H on [0, pi], with H(pi - th) = H(th).
    fn h(&self, th: f64) -> f64 {
        if th <= p2() { self.h_half(th).0 } else { self.h_half(PI - th).0 }
    }
    /// H' on [0, pi]; at pi/2 the LEFT derivative is returned (the atom sits there).
    fn hp_left(&self, th: f64) -> f64 {
        if th <= p2() { self.h_half(th).1 } else { -self.h_half(PI - th).1 }
    }
    /// H' on [0, pi]; at pi/2 the RIGHT derivative.
    fn hp_right(&self, th: f64) -> f64 {
        if th < p2() { self.h_half(th).1 } else { -self.h_half(PI - th).1 }
    }
    fn gauge_defect(&self) -> f64 { self.h(p2()) - 1.0 }
    fn atom(&self) -> f64 { self.hp_right(p2()) - self.hp_left(p2()) }
}

/// Build r = 1 on the given disjoint intervals of [0, pi/2], 0 elsewhere, then scale the LAST
/// interval's right endpoint so that int r cos = 1/2 exactly.  Returns None if impossible.
fn calibrate(name: &'static str, mut iv: Vec<(f64, f64)>) -> Option<Cap> {
    // int over intervals of cos = sum (sin b - sin a); solve for the right end of the last.
    iv.sort_by(|p, q| p.0.partial_cmp(&q.0).unwrap());
    let head: f64 = iv[..iv.len() - 1].iter().map(|&(a, b)| b.sin() - a.sin()).sum();
    let (la, _) = iv[iv.len() - 1];
    let need = 0.5 - head - (-la.sin());   // sin(b) must equal this
    if !(need > la.sin() - 1e-15 && need <= 1.0) { return None; }
    let lb = need.asin();
    if lb > p2() + 1e-12 || lb < la { return None; }
    let n = iv.len();
    iv[n - 1].1 = lb;
    let pieces = iv.iter().map(|&(a, b)| (a, b, 1.0)).collect();
    Some(Cap { name, pieces })
}

/// r = 1 on {th : sin(1/(th - pi/4)) > 0} union [c, pi/2]: infinitely many phases
/// accumulating at pi/4, with c fixed by bisection so that int r cos = 1/2.  r takes only the
/// values 0 and 1, so |{r_ac = 1}| is positive and the phase count is infinite.
fn oscillating(name: &'static str, nres: usize) -> Cap {
    let osc = |th: f64| -> bool {
        let d = th - PI / 4.0;
        if d.abs() < 1e-12 { false } else { (1.0 / d).sin() > 0.0 }
    };
    let build = |c: f64| -> Vec<(f64, f64, f64)> {
        (0..nres).map(|k| {
            let a = k as f64 / nres as f64 * p2();
            let b = (k + 1) as f64 / nres as f64 * p2();
            let m = 0.5 * (a + b);
            (a, b, if m >= c || osc(m) { 1.0 } else { 0.0 })
        }).collect()
    };
    let integ = |pieces: &Vec<(f64, f64, f64)>| -> f64 {
        pieces.iter().map(|&(a, b, v)| v * (b.sin() - a.sin())).sum()
    };
    // integral is decreasing in c
    let (mut lo, mut hi) = (0.0f64, p2());
    for _ in 0..200 {
        let mid = 0.5 * (lo + hi);
        if integ(&build(mid)) > 0.5 { lo = mid; } else { hi = mid; }
    }
    Cap { name, pieces: build(0.5 * (lo + hi)) }
}

/// r = R on [b, pi/2], 0 before, with b fixed by R(1 - sin b) = 1/2.  For R > 1 this is a cap
/// that violates (RC) and nothing else; it is the negative control for the Sturm step.
fn hot_block(name: &'static str, rr: f64) -> Cap {
    let sb = 1.0 - 0.5 / rr;
    let b = sb.asin();
    Cap { name, pieces: vec![(0.0, b, 0.0), (b, p2(), rr)] }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let pg: usize = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(360);
    let nth: usize = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(24001);

    println!("rc_one -- T(p) connectivity for caps in D with r_ac = 1 on a positive-measure set");
    println!("point grid {}^2, theta grid {}\n", pg, nth);

    let mut caps: Vec<Cap> = Vec::new();
    // (A) r = 1 next to theta = 0, away from the atom.  Exactly r = 1_{[0,pi/6]}.
    caps.push(calibrate("A  r=1 on [0,pi/6]            ", vec![(0.0, p2())]).unwrap());
    // (B) r = 1 running up to the atom.  Extremal: |{r=1}| = pi/3, the largest possible.
    caps.push(Cap { name: "B  r=1 on [pi/6,pi/2] (atom)  ",
                    pieces: vec![(0.0, PI / 6.0, 0.0), (PI / 6.0, p2(), 1.0)] });
    // (C) two blocks, one at each end.
    caps.push(calibrate("C  r=1 on [0,0.3] u [b,pi/2]  ", vec![(0.0, 0.3), (0.9, p2())]).unwrap());
    // (D) many blocks: 40 alternating slabs.
    {
        let mut iv = Vec::new();
        for k in 0..40 {
            let a = k as f64 / 40.0 * p2();
            iv.push((a, a + p2() / 80.0));
        }
        // calibrate by trimming from the right: keep adding blocks until the integral hits 1/2
        let mut acc = 0.0;
        let mut kept: Vec<(f64, f64)> = Vec::new();
        for &(s, e) in &iv {
            let c = e.sin() - s.sin();
            if acc + c >= 0.5 {
                let b = (0.5 - acc + s.sin()).asin();
                kept.push((s, b));
                acc = 0.5;
                break;
            }
            kept.push((s, e));
            acc += c;
        }
        if (acc - 0.5).abs() > 1e-12 { panic!("D: 40 slabs give only {}", acc); }
        caps.push(Cap { name: "D  r=1 on 40 alternating slabs",
                        pieces: kept.iter().map(|&(a, b)| (a, b, 1.0)).collect() });
    }
    // (E) infinitely many phases accumulating at pi/4.
    caps.push(oscillating("E  r=1 on osc set (inf phases)", 200000));
    // (F) control: r = 1/2 constant off the atom (the stadium), which has r < 1 strictly.
    caps.push(Cap { name: "F  r=1/2 const (stadium ctrl) ",
                    pieces: vec![(0.0, p2(), 0.5)] });
    // (G,H,I) NEGATIVE CONTROLS: r = R > 1 on a block.  (RC) fails and nothing else does.
    caps.push(hot_block("G  r=1.05 block (NEG CONTROL) ", 1.05));
    caps.push(hot_block("H  r=3 block   (NEG CONTROL)  ", 3.0));
    caps.push(hot_block("I  r=8 block   (NEG CONTROL)  ", 8.0));

    for cap in &caps {
        run(cap, pg, nth);
    }
}

/// THE DECISIVE TEST.  `{W > 0}` is order-connected on a window for EVERY p exactly when, for
/// every triple th1 < th2 < th3 in the window,
///     Delta = g2 sin(th3-th1) - g1 sin(th3-th2) - g3 sin(th2-th1) >= 0,   g = H - 1,
/// because p enters W only through the span of {cos, sin}, and Delta * (a positive factor) is
/// the value of W at th2 for the unique p that puts W(th1) = W(th3) = 0.  Delta < 0 at one
/// triple produces, after an arbitrarily small perturbation of that p, a genuine dip:
/// W > 0 at th1 and th3 and W < 0 at th2.  So this is not sampling -- it quantifies over all p.
/// The Sturm claim is exactly Delta >= 0, and Delta >= 0 is what r <= 1 buys.
fn min_delta(cap: &Cap, lo: f64, hi: f64, n: usize) -> (f64, f64, f64, f64) {
    let h = (hi - lo) / (n - 1) as f64;
    let g: Vec<f64> = (0..n).map(|k| cap.h(lo + k as f64 * h) - 1.0).collect();
    let sn: Vec<f64> = (0..n).map(|d| (d as f64 * h).sin()).collect();
    let mut best = f64::MAX;
    let mut arg = (0usize, 0usize, 0usize);
    for i in 0..n {
        for k in (i + 2)..n {
            let s13 = sn[k - i];
            let (gi, gk) = (g[i], g[k]);
            for j in (i + 1)..k {
                let d = g[j] * s13 - gi * sn[k - j] - gk * sn[j - i];
                if d < best { best = d; arg = (i, j, k); }
            }
        }
    }
    (best, lo + arg.0 as f64 * h, lo + arg.1 as f64 * h, lo + arg.2 as f64 * h)
}

fn run(cap: &Cap, pg: usize, nth: usize) {
    println!("=== {} ===", cap.name);
    // calibration and class-D checks
    let gd = cap.gauge_defect();
    let atom = cap.atom();
    let mut rmax = 0.0f64;
    let mut meas_one = 0.0f64;
    let m = 400000usize;
    for k in 0..m {
        let th = (k as f64 + 0.5) / m as f64 * p2();
        let r = cap.r(th);
        if r > rmax { rmax = r; }
        if r >= 1.0 - 1e-12 { meas_one += p2() / m as f64; }
    }
    println!("  gauge H(pi/2)-1 {:+.2e}   atom mass {:.6}   max r_ac {:.6}   |{{r_ac=1}}| {:.6}",
             gd, atom, rmax, meas_one);

    // arms, sigma, c_y on [0, pi/2]
    let nt = 4001usize;
    let mut a1v = vec![0.0f64; nt];
    let mut a2v = vec![0.0f64; nt];
    let mut cyv = vec![0.0f64; nt];
    for q in 0..nt {
        let t = q as f64 / (nt - 1) as f64 * p2();
        let f = cap.h(t);
        let g = cap.h(t + p2());
        let fp = cap.hp_left(t);
        let gp = cap.hp_right(t + p2());
        a1v[q] = g - 1.0 - fp;
        a2v[q] = f - 1.0 + gp;
        cyv[q] = (f - 1.0) * t.sin() + (g - 1.0) * t.cos();
    }
    let cymax = cyv.iter().cloned().fold(f64::MIN, f64::max);
    // (d): largest t with alpha_2 > 0 throughout [0,t]; smallest t with alpha_1 >= 0 on [t,pi/2]
    let mut t_a2 = p2();
    for q in 0..nt {
        if a2v[q] <= 0.0 { t_a2 = q as f64 / (nt - 1) as f64 * p2(); break; }
    }
    let mut t_a1 = 0.0f64;
    for q in (0..nt).rev() {
        if a1v[q] < 0.0 { t_a1 = q as f64 / (nt - 1) as f64 * p2(); break; }
    }
    println!("  (c) max c_y {:.6} (need <= 0.5)   (d) alpha_2>0 up to {:.5}, alpha_1>=0 from {:.5}  -> {}",
             cymax, t_a2, t_a1,
             if t_a1 < t_a2 && cymax <= 0.5 { "in D" } else { "NOT in D" });

    // IS THE WRONSKIAN STRICTLY ANTITONE, OR ONLY ANTITONE?  G_x(th) = W' sin(th-x) - W cos(th-x)
    // has G_x' = (r-1) sin(th-x), so where r_ac = 1 it is flat.  `wronskian_strictAntiOn` in
    // Anchor.lean demands StrictAntiOn and therefore does not instantiate; the claim under test
    // is that AntitoneOn is all `pos_between_of_strictAnti` actually consumes.  W is taken with
    // p = 0, which changes G by a multiple of a solution of the homogeneous equation and so
    // changes neither the sign nor the flatness of G'.
    {
        let ng = 200001usize;
        let x = 0.2f64;                      // anchor inside [0, pi/2)
        let hstep = (p2() - x) / (ng - 1) as f64;
        let gval = |th: f64| -> f64 {
            let (h, hp) = cap.h_half(th);
            (hp) * (th - x).sin() - (h - 1.0) * (th - x).cos()
        };
        let (mut worst_up, mut flat) = (f64::MIN, 0.0f64);
        let mut prev = gval(x);
        for k in 1..ng {
            let th = x + k as f64 * hstep;
            let g = gval(th);
            let d = g - prev;
            if d > worst_up { worst_up = d; }
            if d.abs() < 1e-14 * (1.0 + g.abs()) { flat += hstep; }
            prev = g;
        }
        println!("  Wronskian at x=0.2: max forward increment {:+.2e}, flat on {:.4} of {:.4}",
                 worst_up, flat, p2() - x);
    }

    // the decisive three-point test, on each side of the atom and then straddling it
    let nd: usize = std::env::args().nth(3).and_then(|s| s.parse().ok()).unwrap_or(500);
    let (d1, a1, b1, c1) = min_delta(cap, 0.0, p2(), nd);
    let (d2, a2, b2, c2) = min_delta(cap, p2(), PI, nd);
    let (d3, _, _, _) = min_delta(cap, 0.0, PI, nd);
    println!("  min Delta on [0,pi/2]   {:+.3e}  at ({:.4},{:.4},{:.4})", d1, a1, b1, c1);
    println!("  min Delta on [pi/2,pi]  {:+.3e}  at ({:.4},{:.4},{:.4})", d2, a2, b2, c2);
    println!("  min Delta on [0,pi] (straddles the atom; expected negative) {:+.3e}", d3);
    println!("  => {{W>0}} order-connected on each half for EVERY p: {}",
             if d1 >= -1e-12 && d2 >= -1e-12 { "YES" } else { "NO" });

    // W on a fine theta grid, shared across points except for the linear point part.
    let dth = PI / (nth - 1) as f64;
    let hv: Vec<f64> = (0..nth).map(|k| cap.h(k as f64 * dth) - 1.0).collect();
    let cs: Vec<f64> = (0..nth).map(|k| (k as f64 * dth).cos()).collect();
    let sn: Vec<f64> = (0..nth).map(|k| (k as f64 * dth).sin()).collect();
    // index of pi/2 (nth odd => exact)
    let khalf = (nth - 1) / 2;

    // support-function membership test for C_2 (the body is rho-invariant, so C_2 = C)
    let ncap = 721usize;
    let sup: Vec<(f64, f64, f64)> = (0..ncap).map(|k| {
        let th = k as f64 / (ncap - 1) as f64 * PI;
        (th.cos(), th.sin(), cap.h(th))
    }).collect();

    let (lo, hi) = (-2.2f64, 2.2f64);
    let (ylo, yhi) = (-0.1f64, 1.1f64);
    let mut hist = [0usize; 9];
    let mut ehist = [0usize; 9];
    let mut lohist = [0usize; 9];
    let mut hihist = [0usize; 9];
    let mut ncell = 0usize;
    let mut worst_watom = f64::MIN;

    for jy in 0..pg {
        let py = ylo + (jy as f64 + 0.5) / pg as f64 * (yhi - ylo);
        for ix in 0..pg {
            let px = lo + (ix as f64 + 0.5) / pg as f64 * (hi - lo);
            if !sup.iter().all(|&(ex, ey, hh)| px * ex + py * ey <= hh
                                            && px * ex + (1.0 - py) * ey <= hh) { continue; }
            // W and the two halves
            let w = |k: usize| hv[k] - (px * cs[k] + py * sn[k]);
            let mut clo = 0usize; let mut plo = false;
            let mut chi = 0usize; let mut phi = false;
            for k in 0..khalf { let b = w(k) > 0.0; if b && !plo { clo += 1; } plo = b; }
            for k in (khalf + 1)..nth { let b = w(k) > 0.0; if b && !phi { chi += 1; } phi = b; }
            // T(p): W(t) > 0 and W(t + pi/2) > 0 for t in [0, pi/2]
            let mut comps = 0usize; let mut prev = false;
            let mut entries = 0usize;
            for k in 0..=khalf {
                let cut = w(k) > 0.0 && w(k + khalf) > 0.0;
                if cut && !prev { comps += 1; if k > 0 { entries += 1; } }
                prev = cut;
            }
            if comps == 0 { continue; }
            ncell += 1;
            hist[comps.min(8)] += 1;
            ehist[entries.min(8)] += 1;
            lohist[clo.min(8)] += 1;
            hihist[chi.min(8)] += 1;
            worst_watom = worst_watom.max(w(khalf) + py);   // W(pi/2) = -p_y exactly
        }
    }

    let show = |lbl: &str, h: &[usize; 9]| {
        let s: String = (0..9).filter(|&k| h[k] > 0)
            .map(|k| format!("{}:{} ", k, h[k])).collect();
        println!("  {:<28} {}", lbl, s);
    };
    println!("  cells with T(p) nonempty: {}", ncell);
    show("#components of T(p)", &hist);
    show("#entries of T(p) (t>0)", &ehist);
    show("#comps {W>0} on [0,pi/2)", &lohist);
    show("#comps {W>0} on (pi/2,pi]", &hihist);
    println!("  max |W(pi/2) + p_y| {:.2e}   (W(pi/2) = -p_y: the atom is never cut)",
             worst_watom.abs());
    let bad: usize = hist[2..].iter().sum();
    if bad > 0 {
        println!("  >>> T(p) IS NOT AN INTERVAL on {} of {} cells", bad, ncell);
    } else {
        println!("  T(p) is an interval on every sampled cell.");
    }
    println!();
}
