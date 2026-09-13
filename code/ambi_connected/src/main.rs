//! ambi_connected — does CONNECTEDNESS force the niche ceiling M < 1/2?
//!
//! Rust migration of algorithm/rigorous/ambi_connected.py (Rule 28: the
//! project's Rust-only instruction overrides the Rule 8 Python carve-out;
//! see private/RETRACTIONS.md R6). Faithful line-for-line port: the Python
//! script uses only `math` and `numpy.linspace`, no mpmath/arb ball
//! arithmetic, so this is plain f64 arithmetic with no interval-arithmetic
//! crate required.
//!
//! Usage: cargo run --release --bin ambi_connected

/// p in Q_t with apex (ax,ay): both frame coordinates negative.
fn in_wedge(px: f64, py: f64, ax: f64, ay: f64, t: f64) -> bool {
    let (c, s) = (t.cos(), t.sin());
    let (dx, dy) = (px - ax, py - ay);
    (dx * c + dy * s < 0.0) && (-dx * s + dy * c < 0.0)
}

/// Does Q_t (apex (0,h)) union rho Q_t (apex (0,1-h)) cover the whole
/// segment {x} x [0,1]? rho(p) = (p_x, 1-p_y), so p in rho Q_t iff
/// rho(p) in Q_t with the SAME apex (0,h).
fn covers_vertical(t: f64, h: f64, x: f64, n: usize) -> (bool, Option<f64>) {
    // np.linspace(0.0, 1.0, n): n points, endpoints included.
    for i in 0..n {
        let y = i as f64 / (n as f64 - 1.0);
        let in_u = in_wedge(x, y, 0.0, h, t);
        let in_r = in_wedge(x, 1.0 - y, 0.0, h, t);
        if !(in_u || in_r) {
            return (false, Some(y));
        }
    }
    (true, None)
}

fn main() {
    println!(
        "Does Q_t u rho Q_t cover a full vertical line when the apex is above \
         y = 1/2?"
    );
    println!("  apex of Q_t at (0,h); apex of rho Q_t at (0,1-h).");
    println!("  For h > 1/2 the down-opening cone sits ABOVE the up-opening one.\n");
    println!("{:>8} {:>7} {:>8}  covers [0,1]?   first gap y", "t", "h", "x");

    let ts = [0.3, 0.6, std::f64::consts::PI / 4.0, 1.0, 1.3];
    let hs = [0.40, 0.50, 0.55, 0.70];
    let xs = [-0.02, -0.1, -0.3, -1.0, -3.0];

    for &t in &ts {
        for &h in &hs {
            let mut hit: Option<f64> = None;
            for &x in &xs {
                let (ok, _gap) = covers_vertical(t, h, x, 4001);
                if ok {
                    hit = Some(x);
                    break;
                }
            }
            if let Some(x) = hit {
                println!("{:8.4} {:7.2} {:8.2}  YES -- cut here", t, h, x);
            } else {
                let (_ok, gap) = covers_vertical(t, h, -0.1, 4001);
                println!(
                    "{:8.4} {:7.2} {:8.2}  no          {:.4}",
                    t,
                    h,
                    -0.1,
                    gap.unwrap()
                );
            }
        }
    }

    println!();
    println!("READING.  A 'YES' row means the two wedges alone remove a full vertical");
    println!("segment at that x, so any body meeting both sides of it is disconnected.");
    println!("If every h > 1/2 gives a YES and every h < 1/2 gives a no, the");
    println!("conjectured lemma holds for a single t, and the general case follows by");
    println!("applying it at the maximising t0.");
}
