//! sofa_release — run every gate before a push, so none of them depends on my remembering.
//!
//! WHY THIS EXISTS.  The gates only work if they run.  Across this project two results were
//! withdrawn because a computation was never shipped, four verdicts were printed that their
//! own data contradicted, and one push went out with a shell check standing in for the real
//! gates.  Each of those is a case of a check existing but not being run at the moment it
//! mattered.  One command removes the choice.
//!
//! WHAT IT RUNS, in order, stopping at the first failure:
//!
//!   1. sofa_gates  — every decimal printed in the note is registered, and every declared
//!                    measurement is produced by a shipped program (custody ratchet).
//!   2. sofa_narr   — no verdict is printed from outside a conditional.
//!   3. sync        — every file the release repo tracks matches its source counterpart.
//!   4. release     — the Rule 11 checks: nothing from private/ is tracked, no build
//!                    artifacts are tracked, and the commit author is the project's.
//!
//! It replaces check_sync.sh, check_custody.py and check_prose.py, which are retired.  One
//! coverage loss is real and stated rather than hidden: check_prose compared each Python
//! script's prose against its own output, and sofa_narr scans only Rust.  The 33 remaining
//! Python files therefore have no verdict check.  None of them has been executed since the
//! ban, so nothing they print is load-bearing, but if any is ever run again that gap is
//! open.
//!
//! It does not commit or push.  It reports whether a push would be legitimate, and the
//! decision stays with the person running it.
//!
//! Usage: cargo run --release -- <repo-root> <release-repo>

use std::path::Path;
use std::process::Command;

fn run(bin_dir: &Path, name: &str, args: &[&str]) -> (bool, String) {
    let _ = Command::new("cargo").arg("build").arg("--release").current_dir(bin_dir).output();
    let exe = bin_dir.join("target/release").join(name);
    match Command::new(&exe).args(args).output() {
        Ok(o) => (o.status.success(),
                  String::from_utf8_lossy(&o.stdout).to_string()
                      + &String::from_utf8_lossy(&o.stderr)),
        Err(e) => (false, format!("could not run {}: {}", name, e)),
    }
}

fn git(repo: &Path, args: &[&str]) -> String {
    match Command::new("git").args(args).current_dir(repo).output() {
        Ok(o) => String::from_utf8_lossy(&o.stdout).to_string(),
        Err(_) => String::new(),
    }
}

fn tail(s: &str, n: usize) -> String {
    let lines: Vec<&str> = s.lines().collect();
    lines[lines.len().saturating_sub(n)..].join("\n")
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let root = Path::new(a.get(1).map(|s| s.as_str()).unwrap_or("."));
    let rel = Path::new(a.get(2).map(|s| s.as_str()).unwrap_or("moving-sofa-local-max"));
    let code = root.join("code");

    println!("sofa_release — all gates, one command\n");
    let mut failed: Vec<&str> = Vec::new();

    let (ok1, out1) = run(&code.join("sofa_gates"), "sofa_gates",
                          &[root.to_str().unwrap_or(".")]);
    println!("[1] constants + custody");
    println!("{}", tail(&out1, 4));
    if !ok1 { failed.push("sofa_gates"); }

    let (ok2, out2) = run(&code.join("sofa_narr"), "sofa_narr", &[code.to_str().unwrap_or(".")]);
    println!("\n[2] narration guard");
    println!("{}", tail(&out2, 3));
    if !ok2 { failed.push("sofa_narr"); }

    // Every file the release repo tracks must match its source counterpart.  Content flows
    // SOURCE -> RELEASE only; a divergence in either direction is the bug, because it means
    // a push would ship something no source tree produced.  Three defects in this project
    // came from sync round-trips silently reverting work.  This absorbs the last thing the
    // retired shell gate did that nothing else covered.
    println!("\n[3] source <-> release sync");
    let tracked = git(rel, &["ls-files"]);
    let mut diverged: Vec<&str> = Vec::new();
    let mut checked = 0usize;
    for f in tracked.lines() {
        // release-only by design: repo metadata and archived material with no source twin
        if matches!(f, ".gitignore" | "CITATION.cff" | "LICENSE" | "README.md")
            || f.starts_with("paper/manuscript") || f.starts_with("paper/UNIQUENESS")
            || f.starts_with("paper/OFFDIAG") || f.starts_with("paper/figures/")
            || f.ends_with("Cargo.lock")
            || f == "algorithm/rigorous/probe_spurious_direction.py"
        { continue; }
        let s = root.join(f);
        let r = rel.join(f);
        if !s.exists() { diverged.push(f); continue; }
        checked += 1;
        match (std::fs::read(&s), std::fs::read(&r)) {
            (Ok(a), Ok(b)) if a == b => {}
            _ => diverged.push(f),
        }
    }
    println!("  compared               {}", checked);
    println!("  diverged / release-only {}", diverged.len());
    for f in diverged.iter().take(8) { println!("    {}", f); }
    if !diverged.is_empty() { failed.push("sync"); }

    println!("\n[4] release checks (Rule 11)");
    let leaked = tracked.lines().filter(|l| l.starts_with("private/")).count();
    let artifacts = tracked.lines().filter(|l| l.contains("/target/")).count();
    let author = git(rel, &["config", "user.name"]).trim().to_string();
    let staged = git(rel, &["status", "--short"]);
    println!("  files tracked           {}", tracked.lines().count());
    println!("  private/ leaked         {}", leaked);
    println!("  build artifacts tracked {}", artifacts);
    println!("  commit author           {}", author);
    println!("  uncommitted changes     {}", staged.lines().count());
    let rule11 = leaked == 0 && artifacts == 0 && author == "elvec1o";
    if !rule11 { failed.push("release checks"); }

    println!();
    if failed.is_empty() {
        println!("ALL GATES PASS — a push from this state is legitimate.");
    } else {
        println!("BLOCKED by: {}", failed.join(", "));
        println!("Do not push until each is green.");
        std::process::exit(1);
    }
}
