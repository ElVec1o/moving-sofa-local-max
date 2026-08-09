//! sofa_gates — the constants and custody gates, in Rust.  No Python at any point.
//!
//! WHY THIS EXISTS.  Python is banned in this project.  Two of the four release gates did
//! real work that a shell release-check cannot replace:
//!
//!   constants — every decimal printed in the note must be registered, so a new number
//!               cannot enter the paper unnoticed.
//!   custody   — every registered measurement must be PRODUCED by a shipped program, so no
//!               label rests on a computation that can no longer be re-run.  Two results in
//!               this project were withdrawn for exactly that.
//!
//! Both are reimplemented here with the standard library alone: no crates, no network, no
//! interpreter.  The registry lives in constants_registry.py, which is DATA and nothing else
//! -- it was check_constants.py until that gate was retired; this program
//! parses its `"literal": ("key", "V"|"D", "note"),` lines textually and never executes it.
//!
//! CUSTODY AND THE MIGRATION.  Coverage is harvested from the shipped Rust binaries, which
//! are built and run here, plus any files listed in `LEGACY_OUTPUTS` -- captured stdout from
//! programs that have not been ported yet.  A legacy file is a stopgap and is reported as
//! one, so the count of un-ported producers is visible rather than hidden.
//!
//! MIGRATION STATUS, AND IT IS NOT YET EQUIVALENT.  This port is STRICTER than the Python
//! gate it replaces: it flags 26 decimals the old one accepts.  Some are short literals the
//! old scanner skipped, some sit in contexts its wider block matching covered.  Until those
//! 26 are reconciled one by one, this program is a second opinion and not a replacement, and
//! it says so by failing rather than by quietly widening its own tolerance.
//!
//! Custody coverage is likewise incomplete: only the two Rust binaries produce, so the
//! orphan count is far above the Python baseline.  Each ported program moves constants from
//! orphan to produced.  The baseline must not be re-based to hide that -- it is the
//! migration backlog made countable.
//!
//! Usage: cargo run --release -- <repo-root> [--update-baseline]

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Rust programs whose stdout counts as production, with the arguments to run them under.
const RUST_BINS: &[(&str, &[&str])] = &[
    ("sofa_cert", &["1024"]),
    ("tail_schur", &["256", "32"]),
    ("sofa_sweep", &[]),
];

/// Captured stdout of not-yet-ported producers.  Every entry here is migration debt.
const LEGACY_OUTPUTS: &[&str] = &["private/legacy_outputs"];

/// Pull decimal literals out of a string, matching the note scanner exactly:
/// at least FOUR digits after the point, not preceded by a digit or a dot, and not an
/// arXiv identifier.  A first version required only five characters total, which admits
/// 0.001 and 0.884 and over-reported by 26.
fn decimals(s: &str) -> BTreeSet<String> {
    let stripped: String = s
        .lines()
        .filter(|l| !l.trim_start().starts_with('%'))
        .collect::<Vec<_>>()
        .join("\n");
    let s: &str = &stripped;
    let b: Vec<char> = s.chars().collect();
    let mut out = BTreeSet::new();
    let mut i = 0usize;
    while i < b.len() {
        if b[i].is_ascii_digit() {
            let start = i;
            while i < b.len() && b[i].is_ascii_digit() { i += 1; }
            if i < b.len() && b[i] == '.' {
                let dot = i;
                i += 1;
                let frac_start = i;
                while i < b.len() && b[i].is_ascii_digit() { i += 1; }
                let frac = i - frac_start;
                let before_ok = start == 0 || !(b[start - 1] == '.' || b[start - 1].is_ascii_digit());
                let arxiv = {
                    let lo = start.saturating_sub(8);
                    b[lo..start].iter().collect::<String>().contains("arXiv:")
                };
                if frac >= 4 && before_ok && !arxiv {
                    out.insert(b[start..i].iter().collect::<String>());
                }
                if frac == 0 { i = dot + 1; }
            }
        } else {
            i += 1;
        }
    }
    out
}

/// Parse the DECLARED_BLOCKS list: a context substring that exempts nearby decimals.
fn parse_blocks(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut inside = false;
    for line in text.lines() {
        let t = line.trim();
        if t.starts_with("DECLARED_BLOCKS") { inside = true; continue; }
        if inside {
            if t.starts_with(']') { break; }
            if let Some(rest) = t.strip_prefix("(\"") {
                if let Some(end) = rest.find("\",") {
                    out.push(rest[..end].replace("\\\\", "\\"));
                }
            }
        }
    }
    out
}

/// Parse `"literal": ("key", "KIND", "note"),` lines out of the registry file.
fn parse_registry(text: &str) -> Vec<(String, String, String)> {
    let mut out = Vec::new();
    for line in text.lines() {
        let t = line.trim();
        if !t.starts_with('"') { continue; }
        let mut parts = t.splitn(2, "\":");
        let lit = match parts.next() { Some(p) => p.trim_start_matches('"').to_string(), None => continue };
        let rest = match parts.next() { Some(r) => r, None => continue };
        if !lit.contains('.') || !lit.chars().next().map_or(false, |c| c.is_ascii_digit()) { continue; }
        let quoted: Vec<&str> = rest.split('"').collect();
        if quoted.len() < 4 { continue; }
        out.push((lit, quoted[1].to_string(), quoted[3].to_string()));
    }
    out
}

fn run_rust_bin(root: &Path, name: &str, args: &[&str]) -> String {
    let dir = root.join("code").join(name);
    if !dir.join("src/main.rs").exists() { return String::new(); }
    let _ = Command::new("cargo").arg("build").arg("--release").current_dir(&dir).output();
    let exe = dir.join("target/release").join(name);
    match Command::new(&exe).args(args).current_dir(&dir).output() {
        Ok(o) => String::from_utf8_lossy(&o.stdout).to_string(),
        Err(_) => String::new(),
    }
}

fn read_dir_texts(dir: &Path) -> (String, usize) {
    let mut s = String::new();
    let mut n = 0;
    if let Ok(rd) = fs::read_dir(dir) {
        for e in rd.flatten() {
            if let Ok(t) = fs::read_to_string(e.path()) { s.push_str(&t); s.push('\n'); n += 1; }
        }
    }
    (s, n)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let root = PathBuf::from(args.get(1).cloned().unwrap_or_else(|| ".".into()));
    let update = args.iter().any(|a| a == "--update-baseline");

    let note = root.join("paper/niche_separation/note.tex");
    let reg_file = root.join("private/tools/constants_registry.py");
    // A SEPARATE baseline from the Python gate.  That one measures coverage over 19 Python
    // producers; this one measures it over the Rust binaries only, so the two counts are not
    // comparable and sharing a file would silently clobber one with the other.  This number
    // is the migration backlog: it falls as programs are ported and must never be raised.
    let baseline_file = root.join("private/tools/custody_baseline_rust.txt");

    let note_text = fs::read_to_string(&note).unwrap_or_default();
    let reg_text = fs::read_to_string(&reg_file).unwrap_or_default();
    if note_text.is_empty() || reg_text.is_empty() {
        eprintln!("FAIL: could not read the note or the registry under {}", root.display());
        std::process::exit(2);
    }
    let registry = parse_registry(&reg_text);
    let reg_lits: BTreeSet<&str> = registry.iter().map(|(l, _, _)| l.as_str()).collect();

    println!("sofa_gates — constants and custody, in Rust, no interpreter\n");

    // ---- gate 1: every printed decimal is registered ------------------------------------
    let blocks = parse_blocks(&reg_text);
    let printed = decimals(&note_text);
    // A decimal may also be covered by a DECLARED_BLOCK: a context substring registered
    // once for a whole table.  Without this the port over-reports by more than a hundred.
    let exempt = |d: &str| -> bool {
        let mut from = 0usize;
        while let Some(pos) = note_text[from..].find(d) {
            let at = from + pos;
            let lo = at.saturating_sub(240);
            let ctx = &note_text[lo..at];
            if blocks.iter().any(|b| ctx.contains(b.as_str())) { return true; }
            from = at + d.len();
            if from >= note_text.len() { break; }
        }
        false
    };
    let unregistered: Vec<&String> = printed.iter()
        .filter(|d| !reg_lits.contains(d.as_str()) && !exempt(d))
        .collect();
    println!("CONSTANTS");
    println!("  decimals in the note {:>5}", printed.len());
    println!("  registry entries     {:>5}", registry.len());
    println!("  unregistered (>=5 chars) {:>1}", unregistered.len());
    for d in unregistered.iter().take(12) { println!("    {}", d); }

    // ---- gate 2: every declared constant is produced by a shipped program ---------------
    println!("\nCUSTODY");
    let mut corpus: BTreeSet<String> = BTreeSet::new();
    for (name, a) in RUST_BINS {
        let out = run_rust_bin(&root, name, a);
        let d = decimals(&out);
        println!("  {:<22} rust   {:>5} decimals", name, d.len());
        corpus.extend(d);
    }
    let mut legacy_files = 0usize;
    for rel in LEGACY_OUTPUTS {
        let (text, n) = read_dir_texts(&root.join(rel));
        if n > 0 {
            let d = decimals(&text);
            println!("  {:<22} legacy {:>5} decimals from {} captured file(s)", rel, d.len(), n);
            corpus.extend(d);
            legacy_files += n;
        }
    }

    let declared: Vec<&(String, String, String)> =
        registry.iter().filter(|(_, _, k)| k == "D").collect();
    let covered = |c: &str| -> bool {
        corpus.iter().any(|p| p.len() >= 5 && (p == c || p.starts_with(c) || c.starts_with(p.as_str())))
    };
    let orphans: Vec<&&(String, String, String)> =
        declared.iter().filter(|(l, _, _)| !covered(l)).collect();

    let n_dec = declared.len();
    let n_orph = orphans.len();
    println!("\n  declared {}   produced {}   ORPHAN {}   coverage {:.1}%",
             n_dec, n_dec - n_orph, n_orph,
             100.0 * (n_dec - n_orph) as f64 / n_dec.max(1) as f64);
    if legacy_files > 0 {
        println!("  {} legacy capture file(s) still contribute coverage: migration debt,", legacy_files);
        println!("  not production.  Porting their producer to Rust retires them.");
    }

    let base: usize = fs::read_to_string(&baseline_file).ok()
        .and_then(|s| s.trim().parse().ok()).unwrap_or(n_orph);
    if update {
        let _ = fs::write(&baseline_file, format!("{}\n", n_orph));
        println!("  baseline set to {}", n_orph);
        return;
    }
    println!("  baseline {}   current {}", base, n_orph);

    let mut fail = false;
    if !unregistered.is_empty() {
        println!("\nFAIL: a decimal is printed in the note with no registry entry.");
        fail = true;
    }
    if n_orph > base {
        println!("\nFAIL: {} new orphan(s).  A constant no shipped program produces cannot", n_orph - base);
        println!("carry a label.  Ship the program, or remove the constant.");
        for (l, k, note) in orphans.iter().rev().take(10) { println!("    {:<20} {} — {}", l, k, note); }
        fail = true;
    }
    if fail { std::process::exit(1); }
    if n_orph < base { println!("\n  {} orphan(s) retired; re-run with --update-baseline.", base - n_orph); }
    println!("\nPASS: every printed decimal is registered and no new orphans.");
}
