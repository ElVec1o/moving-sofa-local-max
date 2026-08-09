//! sofa_dtau — the producer for prop:dstrict's two numerical claims about `D_tau`.
//!
//! WHY THIS EXISTS.  Proposition prop:dstrict ("the diagonal form is definite") prints seven
//! decimals that no shipped program produced.  Two of them are closed forms and five come
//! from a finite-element eigenvalue scan that lived only in a scratchpad.  A constant that no
//! shipped program regenerates cannot carry a label — that is the custody rule, and this
//! crate is what it demands here.  Nothing new is claimed; this is the producer for numbers
//! the note already prints.
//!
//! WHAT IS MEASURED, AND WHY.
//!
//! PART 1 — the range (b) coefficient scan.  The proof of prop:dstrict re-runs range (b) of
//! thm:diag with the term the printed collection discards, `-(3/4) int_0^tau p'^2`, RETAINED,
//! and reads the `a^2` coefficient as `-(4/5) sigma sin^2 sigma` rather than as the
//! nonpositive `(4/5) sigma (cos^2 sigma - 1)`.  Definiteness on the sliver then rests on
//! four coefficient signs, and the scan checks the scalar facts they need on
//! `sigma = pi/2 - tau in (0, 1/18]`:
//!
//!   (i)   7/8 - 3pi/16 >= 2/7                     (the spectral coefficient)
//!   (ii)  25 pi sigma/16 <= 25pi/288 <= 2/7       (the D coefficient stays negative)
//!   (iii) (2 sigma/pi)^2 <= 1/400                 (the short Dirichlet Poincare constant)
//!   (iv)  sin s (cos s - 3 sin s) >= (4/5) s      (the boundary Young step)
//!
//! and prints the two decimals the note quotes from it: the `D` coefficient bound
//! `-2/7 + 25pi/288 = -0.0130...` and the discarded p-energy `-3/4 - 399/400 = -1.7475`,
//! whose rounding to `-174/100` is what turned the `P^2` coefficient `-11/80` into the
//! note's `-13/100`.  (i)-(iv) are the scalar steps Lean carries as `rangeb_spec_coeff`,
//! `rangeb_D_coeff`, `rangeb_short_poincare`, `rangeb_trig` and `rangeb_a_coeff`; the scan is
//! the independent second opinion on them, not their proof.
//!
//! PART 2 — the first eigenvalue of `-D_tau` by P1 finite elements.  This is the cross-check
//! the note runs against the shooting determinant of range (c), and it is deliberately a
//! DIFFERENT decision procedure: the sign is settled by a count of negative pivots in a
//! symmetric factorisation (Sylvester's law of inertia) and never by a Rayleigh quotient, so
//! an unconverged iteration cannot report a positive eigenvalue that is not there.  A power
//! iteration on the same matrices does not converge here at all — it returns 1.48 where the
//! answer is 0.036 — which is exactly why inertia bisection is the method of record.
//!
//! The cell form on `[0, pi/2]`, in the variables `(p,q)` of thm:system, is
//!
//!   B[eta] = int_0^{pi/2}[2p^2 - 2p'^2 + q^2 - q'^2] - int_0^tau (p+q')^2
//!            + int_0^tau (q-p')^2 ,
//!   p(0) = p(pi/2) = 0,   q(0) = 0,   q(pi/2) free,
//!
//! and `lambda_1(-D_tau) > 0` is equivalent to `D_tau` being negative definite.  `tau` is
//! forced to be a mesh node, so the discontinuity of the integrand at `tau` is resolved
//! exactly and the P1 space is conforming on both sides of it.
//!
//! DISCRETISATION.  P1 elements, uniform on `[0,tau]` and on `[tau,pi/2]` separately with the
//! element counts split in proportion to the two lengths, total element count given on the
//! command line.  The generalised eigenvalue `lambda_1` of the pencil `(-B, M)` is bracketed
//! by bisection on `[-50, 50]`, each step deciding the sign by the number of negative pivots
//! of `-B - lambda M`; the bracket is closed to `1e-13`.  The note quotes the `400`-element
//! column and states the digits are stable against `120` and `240`, so all three are run and
//! the ladder is printed: the claim of stability is checked here rather than asserted.
//!
//! DETERMINISM AND SIZE.  Pure `f64`, fixed loop counts, no randomness, no threads, std only.
//! The dense factorisation is `O(dim^3)` with `dim = 2*elements - 1`; the element count is
//! capped at 1200 (`dim = 2399`, one 46 MB working matrix) so that a mistyped argument cannot
//! turn into an out-of-memory run.  At the shipped sizes the whole program is under a second.
//!
//! Usage: cargo run --release -- [elements ...]     (default: 120 240 400)

const PI: f64 = std::f64::consts::PI;

/// Largest element count accepted, so a mistyped argument cannot allocate the machine away.
const MAX_ELEMENTS: usize = 1200;

// ------------------------------------------------------------------ part 1

/// The scalar inequalities behind the four coefficient signs of the sliver collection.
fn part1() {
    println!("=== part 1: range (b) coefficients, sigma = pi/2 - tau in (0, 1/18] ===");
    let smax = 1.0 / 18.0;
    println!("  sigma_max = 1/18            = {:.10}", smax);
    println!("  tau_min   = pi/2 - 1/18     = {:.10}", PI / 2.0 - smax);
    println!("  sliver (1.5153, pi/2) has sigma < {:.10}", PI / 2.0 - 1.5153);

    let spec = 7.0 / 8.0 - 3.0 * PI / 16.0;
    println!(
        "  (i)   7/8 - 3pi/16          = {:.12}  >= 2/7 = {:.12}   {}",
        spec,
        2.0 / 7.0,
        spec >= 2.0 / 7.0
    );

    let dmax = 25.0 * PI / 288.0;
    println!(
        "  (ii)  25pi/288              = {:.12}  <= 2/7 = {:.12}   {}",
        dmax,
        2.0 / 7.0,
        dmax <= 2.0 / 7.0
    );
    // The D coefficient of the sliver collection, at its least favourable sigma = 1/18.
    println!(
        "        D coefficient  -2/7 + 25pi/288        = {:.12}",
        -2.0 / 7.0 + dmax
    );

    let poin = (2.0 * smax / PI) * (2.0 * smax / PI);
    println!(
        "  (iii) (2 sigma/pi)^2        = {:.12}  <= 1/400 = {:.12}   {}",
        poin,
        1.0 / 400.0,
        poin <= 1.0 / 400.0
    );

    // (iv) sin s (cos s - 3 sin s) >= (4/5) s on (0, 1/18], scanned on a fixed uniform grid.
    let n = 200_000usize;
    let mut worst = f64::INFINITY;
    let mut worst_s = 0.0;
    for k in 1..=n {
        let s = smax * (k as f64) / (n as f64);
        let ratio = s.sin() * (s.cos() - 3.0 * s.sin()) / (0.8 * s);
        if ratio < worst {
            worst = ratio;
            worst_s = s;
        }
    }
    println!(
        "  (iv)  min sin s(cos s - 3 sin s)/((4/5)s)   = {:.12} at s = {:.8}   {}",
        worst,
        worst_s,
        worst >= 1.0
    );

    println!();
    println!("  the p-energy the printed collection discards, and what undoing it costs:");
    // -3/4 int_0^{pi/2} p'^2 is replaced by -3/4 P^2 in the printed range (b); keeping the
    // Dirichlet piece is what pins p on [0,tau].  The two constants below are the note's.
    println!(
        "        -3/4 - 399/400                        = {:.12}   (rounded to -174/100)",
        -3.0 / 4.0 - 399.0 / 400.0
    );
    println!(
        "        P^2 coefficient, term retained        = {:.12}   (= -11/80)",
        -3.0 / 4.0 - 399.0 / 400.0 + 5.0 / 4.0 + 9.0 / 25.0
    );
    println!(
        "        P^2 coefficient, as printed           = {:.12}   (= -13/100)",
        -174.0 / 100.0 + 5.0 / 4.0 + 9.0 / 25.0
    );

    println!();
    println!("  a^2 coefficient -(4/5) sigma sin^2 sigma (degenerates like sigma^3):");
    for &s in &[1.0e-3, 1.0e-2, 3.0e-2, 0.0554, smax] {
        println!("        sigma = {:.6}   coeff = {:.6e}", s, -0.8 * s * s.sin() * s.sin());
    }
}

// ------------------------------------------------------------------ part 2

/// Mesh on `[0, pi/2]`, uniform on each side of `tau`, with `tau` itself a node.
struct Mesh {
    x: Vec<f64>,
    n: usize,
    itau: usize,
}

fn mesh(tau: f64, m1: usize, m2: usize) -> Mesh {
    let mut x = Vec::with_capacity(m1 + m2 + 1);
    for i in 0..=m1 {
        x.push(tau * (i as f64) / (m1 as f64));
    }
    for i in 1..=m2 {
        x.push(tau + (PI / 2.0 - tau) * (i as f64) / (m2 as f64));
    }
    Mesh { n: m1 + m2, itau: m1, x }
}

/// Assemble the cell form `B` and the mass matrix `M` in the P1 basis.
///
/// Unknowns are `p_1..p_{n-1}` (Dirichlet at both ends) followed by `q_1..q_n` (Dirichlet at
/// `0`, free at `pi/2`).  On an element of length `h` the P1 mass block is
/// `h/3` on the diagonal and `h/6` off it, and the stiffness block is `1/h` with the sign
/// pattern of a difference; the mixed terms `int p q'` and `int q p'` are exact because `q'`
/// and `p'` are constant on the element.
fn assemble(me: &Mesh) -> (Vec<Vec<f64>>, Vec<Vec<f64>>) {
    let n = me.n;
    let np = n - 1;
    let dim = np + n;
    let mut bb = vec![vec![0.0f64; dim]; dim];
    let mut mm = vec![vec![0.0f64; dim]; dim];
    let pidx = |i: usize| -> Option<usize> { if i == 0 || i == n { None } else { Some(i - 1) } };
    let qidx = |i: usize| -> Option<usize> { if i == 0 { None } else { Some(np + i - 1) } };
    fn add(mat: &mut [Vec<f64>], a: Option<usize>, b: Option<usize>, v: f64) {
        if let (Some(i), Some(j)) = (a, b) {
            mat[i][j] += v;
        }
    }
    for e in 0..n {
        let h = me.x[e + 1] - me.x[e];
        let inside = e < me.itau; // element lies in [0, tau)
        let (p0, p1, q0, q1) = (pidx(e), pidx(e + 1), qidx(e), qidx(e + 1));
        let m00 = h / 3.0;
        let m01 = h / 6.0;
        let s = 1.0 / h;

        for (u0, u1) in [(p0, p1), (q0, q1)] {
            add(&mut mm, u0, u0, m00);
            add(&mut mm, u1, u1, m00);
            add(&mut mm, u0, u1, m01);
            add(&mut mm, u1, u0, m01);
        }

        // 2 p^2 - 2 p'^2
        add(&mut bb, p0, p0, 2.0 * m00);
        add(&mut bb, p1, p1, 2.0 * m00);
        add(&mut bb, p0, p1, 2.0 * m01);
        add(&mut bb, p1, p0, 2.0 * m01);
        add(&mut bb, p0, p0, -2.0 * s);
        add(&mut bb, p1, p1, -2.0 * s);
        add(&mut bb, p0, p1, 2.0 * s);
        add(&mut bb, p1, p0, 2.0 * s);
        // q^2 - q'^2
        add(&mut bb, q0, q0, m00);
        add(&mut bb, q1, q1, m00);
        add(&mut bb, q0, q1, m01);
        add(&mut bb, q1, q0, m01);
        add(&mut bb, q0, q0, -s);
        add(&mut bb, q1, q1, -s);
        add(&mut bb, q0, q1, s);
        add(&mut bb, q1, q0, s);

        if inside {
            // -(p + q')^2
            add(&mut bb, p0, p0, -m00);
            add(&mut bb, p1, p1, -m00);
            add(&mut bb, p0, p1, -m01);
            add(&mut bb, p1, p0, -m01);
            for pu in [p0, p1] {
                add(&mut bb, pu, q1, -0.5);
                add(&mut bb, q1, pu, -0.5);
                add(&mut bb, pu, q0, 0.5);
                add(&mut bb, q0, pu, 0.5);
            }
            add(&mut bb, q0, q0, -s);
            add(&mut bb, q1, q1, -s);
            add(&mut bb, q0, q1, s);
            add(&mut bb, q1, q0, s);
            // +(q - p')^2
            add(&mut bb, q0, q0, m00);
            add(&mut bb, q1, q1, m00);
            add(&mut bb, q0, q1, m01);
            add(&mut bb, q1, q0, m01);
            for qu in [q0, q1] {
                add(&mut bb, qu, p1, -0.5);
                add(&mut bb, p1, qu, -0.5);
                add(&mut bb, qu, p0, 0.5);
                add(&mut bb, p0, qu, 0.5);
            }
            add(&mut bb, p0, p0, s);
            add(&mut bb, p1, p1, s);
            add(&mut bb, p0, p1, -s);
            add(&mut bb, p1, p0, -s);
        }
    }
    (bb, mm)
}

/// Number of negative eigenvalues of `A = (-B) - lambda M`, by the inertia of a symmetric
/// `LDL^T` elimination.  Sylvester's law of inertia makes the count of negative pivots equal
/// to the count of eigenvalues below `lambda`, so the SIGN of `lambda_1` is decided by an
/// integer and never by a residual.  The tiny-pivot guard keeps a structurally zero pivot
/// from producing an infinity; the matrices here are banded and well conditioned.
fn n_neg(bb: &[Vec<f64>], mm: &[Vec<f64>], lam: f64) -> usize {
    let n = bb.len();
    let mut a = vec![vec![0.0f64; n]; n];
    for i in 0..n {
        for j in 0..n {
            a[i][j] = -bb[i][j] - lam * mm[i][j];
        }
    }
    let mut neg = 0usize;
    for k in 0..n {
        let mut d = a[k][k];
        if d.abs() < 1e-300 {
            d = if d < 0.0 { -1e-300 } else { 1e-300 };
        }
        if d < 0.0 {
            neg += 1;
        }
        for i in k + 1..n {
            let f = a[i][k] / d;
            if f == 0.0 {
                continue;
            }
            for j in k + 1..n {
                a[i][j] -= f * a[k][j];
            }
            a[i][k] = 0.0;
        }
    }
    neg
}

/// Smallest generalised eigenvalue of `(-B, M)`, by bisection on the inertia count.
fn lambda1(bb: &[Vec<f64>], mm: &[Vec<f64>]) -> f64 {
    let mut lo = -50.0f64;
    let mut hi = 50.0f64;
    if n_neg(bb, mm, lo) > 0 {
        return f64::NEG_INFINITY; // below the bracket: would mean D_tau is not definite
    }
    for _ in 0..200 {
        let mid = 0.5 * (lo + hi);
        if n_neg(bb, mm, mid) > 0 {
            hi = mid;
        } else {
            lo = mid;
        }
        if (hi - lo).abs() < 1e-13 {
            break;
        }
    }
    0.5 * (lo + hi)
}

/// The note's seven abscissae.  `pi/4` is where the diagonal and mirror families coincide,
/// `1.5153` is the right end of range (c), and `pi/2 - 1e-4` sits inside the sliver where the
/// annihilated mode `(0, sin t)` drives `lambda_1` to zero.
fn taus() -> Vec<f64> {
    vec![PI / 4.0, 1.4137, 1.5140, 1.5153, 1.5400, 1.5600, PI / 2.0 - 1e-4]
}

fn part2(res: usize) {
    println!();
    println!(
        "=== part 2: lambda_1(-D_tau), P1 FEM, {} elements, inertia bisection ===",
        res
    );
    println!("    lambda_1 > 0  <=>  D_tau negative definite");
    for tau in taus() {
        let sigma = PI / 2.0 - tau;
        let frac = tau / (PI / 2.0);
        let m1 = ((res as f64 * frac).round() as usize).max(3);
        let m2 = ((res as f64 * (1.0 - frac)).round() as usize).max(3);
        let me = mesh(tau, m1, m2);
        let (bb, mm) = assemble(&me);
        let lam = lambda1(&bb, &mm);
        println!(
            "    tau = {:.10}   sigma = {:.10}   lambda_1 = {:+.9}   lambda_1/sigma = {:.6}",
            tau,
            sigma,
            lam,
            lam / sigma
        );
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut sizes: Vec<usize> = args
        .iter()
        .filter_map(|a| a.parse::<usize>().ok())
        .filter(|&m| m >= 8 && m <= MAX_ELEMENTS)
        .collect();
    if sizes.is_empty() {
        sizes = vec![120, 240, 400];
    }

    println!("sofa_dtau — prop:dstrict: the range (b) coefficients and lambda_1(-D_tau)");
    println!();
    part1();
    for m in sizes {
        part2(m);
    }
    println!();
    println!("the note quotes the last column above; the earlier ones are the stability ladder.");
}
