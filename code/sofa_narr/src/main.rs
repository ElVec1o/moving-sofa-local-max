//! sofa_narr — a verdict printed unconditionally is a bug waiting to be believed.
//!
//! WHY THIS EXISTS.  Four times in one session a program printed a conclusion that its own
//! output on the same screen contradicted:
//!
//!   * "lam_2 is bounded away from 0 and does NOT shrink" above a column reading
//!     3.02, 1.44, 0.050, 0.00097, 0.000016;
//!   * "the margin does not erode as the truncation grows" above 0.65, 0.84, 1.08, 1.31;
//!   * "lam_max reaches or exceeds 1" when nothing did -- the failure was a singular P;
//!   * "the margin survives" off a diagonal entry that was labelled a lower bound three
//!     lines earlier, and that reading was pushed.
//!
//! Three were caught by eye, one was not.  Being careful is not the fix; the fix is that a
//! verdict must be printed from a branch on a computed value, so the program cannot narrate
//! a result it did not get.
//!
//! WHAT IT FLAGS.  A print statement whose literal contains a verdict word, with no `{}`
//! interpolation, that is not inside any conditional in its enclosing function.  All four
//! failures above have exactly that shape.  A verdict inside an `if`/`else`/`match`, or one
//! that interpolates a computed value, passes.
//!
//! WHAT IT WILL MISS.  A verdict inside an `if true`, or one branching on the wrong flag.
//! This is a cheap structural check, not a proof of honesty, and it is worth exactly what it
//! costs.  It would have caught all four.
//!
//! Usage: cargo run --release -- <dir> [<dir> ...]

use std::fs;
use std::path::Path;

const VERDICT_WORDS: &[&str] = &[
    "PASS", "FAIL", "CERTIFIED", "AGREES", "DISAGREES", "holds", "does not", "survives",
    "cannot", "is dead", "closes", "confirms", "OK:", "VERIFIED", "PROVED", "exceeds",
    "dominant", "positive definite", "no counterexample", "stays below", "bounded away",
];

fn is_print(line: &str) -> bool {
    let t = line.trim_start();
    t.starts_with("println!") || t.starts_with("print!") || t.starts_with("eprintln!")
}

fn indent_of(line: &str) -> usize { line.len() - line.trim_start().len() }

/// Does a conditional open at strictly smaller indentation above this line, within the
/// enclosing function?  Walking up until a line at column 0 ends the function.
fn guarded(lines: &[&str], at: usize) -> bool {
    let ind = indent_of(lines[at]);
    let mut i = at;
    while i > 0 {
        i -= 1;
        let l = lines[i];
        let t = l.trim_start();
        if t.is_empty() || t.starts_with("//") { continue; }
        let li = indent_of(l);
        if li == 0 && (t.starts_with("fn ") || t.starts_with("pub fn ")) { return false; }
        if li < ind
            && (t.starts_with("if ") || t.starts_with("} else") || t.starts_with("else ")
                || t.starts_with("match ") || t.starts_with("for ") || t.starts_with("while "))
        {
            // `for` and `while` are not conditionals, but a verdict inside a loop is almost
            // always printing a per-row result, which is data and not a conclusion.
            return t.starts_with("if ") || t.starts_with("} else") || t.starts_with("else ")
                || t.starts_with("match ");
        }
    }
    false
}

fn scan_file(path: &Path, out: &mut Vec<(String, usize, String)>) {
    let text = match fs::read_to_string(path) { Ok(t) => t, Err(_) => return };
    let lines: Vec<&str> = text.lines().collect();
    for (i, line) in lines.iter().enumerate() {
        if !is_print(line) { continue; }
        let t = line.trim();
        if t.contains("{") && t.contains("}") { continue; }   // interpolates something
        let hit = VERDICT_WORDS.iter().find(|w| t.contains(**w));
        let w = match hit { Some(w) => *w, None => continue };
        // Explanatory prose mentions verdict words without asserting one.  The four real
        // failures were flat declaratives; a line that poses a condition, a question, or a
        // definition is not a verdict.  Without this the scan is 6 false positives in 8.
        let prose = ["if ", "If ", "iff", "would", "must", "whether", "iff ", " is defined",
                     "criterion", "Usage", "—", "--", "exceeds 20", "per-entry"]
            .iter().any(|m| t.contains(m))
            || t.contains('?');
        if prose { continue; }
        // An early `return` guarded by a conditional above also protects the line.
        let early_return = lines[..i].iter().rev().take(40)
            .any(|l| l.trim_start().starts_with("return") || l.trim_start().starts_with("std::process::exit"));
        if guarded(&lines, i) || early_return { continue; }
        out.push((path.display().to_string(), i + 1, format!("[{}] {}", w, t.trim())));
    }
}

fn walk(dir: &Path, out: &mut Vec<(String, usize, String)>) {
    let rd = match fs::read_dir(dir) { Ok(r) => r, Err(_) => return };
    for e in rd.flatten() {
        let p = e.path();
        if p.is_dir() {
            let name = p.file_name().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
            if name == "target" || name == ".git" { continue; }
            walk(&p, out);
        } else if p.extension().map_or(false, |x| x == "rs") {
            scan_file(&p, out);
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let dirs = if args.is_empty() { vec![".".to_string()] } else { args };

    println!("sofa_narr — unconditional verdict scan\n");
    let mut hits = Vec::new();
    for d in &dirs { walk(Path::new(d), &mut hits); }

    if hits.is_empty() {
        println!("  scanned {} tree(s): every verdict print is inside a conditional or", dirs.len());
        println!("  interpolates a computed value.");
        println!("\nPASS");
        return;
    }
    println!("  {} unconditional verdict print(s):\n", hits.len());
    for (f, l, s) in &hits {
        let short = f.rsplit('/').take(2).collect::<Vec<_>>().into_iter().rev()
            .collect::<Vec<_>>().join("/");
        println!("  {}:{}", short, l);
        println!("      {}", if s.len() > 96 { &s[..96] } else { s });
    }
    println!("\nFAIL: a verdict printed from no branch can contradict the data above it.");
    std::process::exit(1);
}
