// ambi_ordercert.py — an EXACT certificate that Sigma's cap is ordered.
// Rust port. See algorithm/rigorous/ambi_ordercert.py for the full mathematical writeup.
//
// Every step in the original is exact rational arithmetic (Python fractions.Fraction).
// This is NOT the arb/ball-arithmetic case (that is ambi_certbound.py's `flint` import,
// still blocked pending an arb-crate spike) -- this script only needs exact Q arithmetic,
// which num-rational's BigRational (backed by num-bigint) provides directly and exactly,
// with no precision loss anywhere.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

fn r(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

fn pow_r(x: &BigRational, n: u32) -> BigRational {
    let mut result = BigRational::one();
    for _ in 0..n {
        result = result * x;
    }
    result
}

fn s3_hi() -> BigRational {
    r(86602540379, 10i64.pow(11))
}
fn s3_lo() -> BigRational {
    r(86602540378, 10i64.pow(11))
}
fn t_cert() -> BigRational {
    r(723, 1000)
}

fn sin_lo(x: &BigRational) -> BigRational {
    x - pow_r(x, 3) / BigInt::from(6) + pow_r(x, 5) / BigInt::from(120)
        - pow_r(x, 7) / BigInt::from(5040)
}
fn sin_hi(x: &BigRational) -> BigRational {
    sin_lo(x) + pow_r(x, 9) / BigInt::from(362880)
}
fn cos_lo(x: &BigRational) -> BigRational {
    BigRational::one() - pow_r(x, 2) / BigInt::from(2) + pow_r(x, 4) / BigInt::from(24)
        - pow_r(x, 6) / BigInt::from(720)
}

/// Returns (i, i', ii) verdicts and the two slacks, all in exact rationals.
fn certify(
    c_lo: &BigRational,
    t: &BigRational,
    q: &BigRational,
) -> (bool, bool, bool, BigRational, BigRational) {
    let k = c_lo + BigRational::one() - s3_hi(); // < c + 1 - sqrt3/2
    let s1 = &k * cos_lo(t) - sin_hi(t); // (i) > 0 wanted
    let s1b = (c_lo + BigRational::one()) * s3_lo() - r(5, 4); // (i') > 0 wanted
    let w = sin_lo(t) - r(1, 2);
    if w <= BigRational::zero() {
        return (false, false, false, BigRational::zero(), BigRational::zero());
    }
    let sq = (BigRational::one() - pow_r(&w, 2) + q * q) / (BigRational::from(BigInt::from(2)) * q); // >= sqrt(1-w^2)
    let s2 = sin_lo(t) * ((c_lo + BigRational::one()) + cos_lo(t) - sq) - BigRational::one(); // (ii) >= 0 wanted
    (
        s1 > BigRational::zero(),
        s1b > BigRational::zero(),
        s2 >= BigRational::zero(),
        s1,
        s2,
    )
}

/// a_1 > 7/8 by integer arithmetic: the cubic S^3 - 51S - 142 is negative at 33/4.
fn sigma_clears_three_quarters() -> bool {
    let s = r(33, 4);
    let v = pow_r(&s, 3) - BigRational::from(BigInt::from(51)) * &s - BigRational::from(BigInt::from(142));
    v < BigRational::zero()
}

fn to_f64(x: &BigRational) -> f64 {
    // exact enough for display purposes; matches Python's float(Fraction) rounding closely
    x.numer().to_string().parse::<f64>().unwrap_or(f64::NAN)
        / x.denom().to_string().parse::<f64>().unwrap_or(1.0)
}

fn main() {
    let c = r(3, 4);
    let s334 = r(33, 4);
    let v = pow_r(&s334, 3) - BigRational::from(BigInt::from(51)) * &s334 - BigRational::from(BigInt::from(142));
    println!("  threshold c = 3/4");
    println!(
        "  Sigma clears it: (33/4)^3 - 51(33/4) - 142 = {} < 0, so S > 33/4,",
        v
    );
    println!(
        "    a_1 > 7/8, alpha_2(0) = 2a_1 - 1 > 3/4   [{}]",
        if sigma_clears_three_quarters() { "OK" } else { "FAILS" }
    );
    let t = t_cert();
    println!("  witness T = {} = {}\n", t, to_f64(&t));

    let q = r(98685, 100000);
    let (a, b, d, s1, s2) = certify(&c, &t, &q);
    println!(
        "  (i)   tan T < c + 1 - sqrt3/2      slack {:+.9}   {}",
        to_f64(&s1),
        if a { "HOLDS" } else { "FAILS" }
    );
    let ib = (&c + BigRational::one()) * s3_lo() - r(5, 4);
    println!(
        "  (i')  min of the bound on [0,pi/6] {:+.9}   {}",
        to_f64(&ib),
        if b { "HOLDS" } else { "FAILS" }
    );
    println!(
        "  (ii)  alpha_1 bound at T           slack {:+.9}   {}",
        to_f64(&s2),
        if d { "HOLDS" } else { "FAILS" }
    );
    let mut ok = a && b && d;
    ok = ok && sigma_clears_three_quarters();
    println!(
        "\n  -> {}: every cap with (RC), the forced",
        if ok { "CERTIFIED" } else { "NOT CERTIFIED" }
    );
    println!("     boundary data and alpha_2(0) >= 3/4 is ORDERED, hence ANCHORED,");
    println!("     and Sigma clears 3/4 because a_1 > 7/8.");

    println!("\n  NEGATIVE CONTROLS (rule I12): below the LP threshold 0.7484 these must FAIL.");
    let mut bad = false;
    for cv in [r(74, 100), r(70, 100), r(60, 100)] {
        let (aa, bb, dd, _, _) = certify(&cv, &t, &q);
        let acc = aa && bb && dd;
        println!(
            "    c = {:.2}: {}",
            to_f64(&cv),
            if acc { "*** ACCEPTED, CERTIFICATE UNSOUND ***" } else { "rejected" }
        );
        bad |= acc;
    }
    println!(
        "  -> {}",
        if !bad { "controls pass" } else { "A FALSE CLAIM WAS ACCEPTED" }
    );

    std::process::exit(if ok && !bad { 0 } else { 1 });
}
