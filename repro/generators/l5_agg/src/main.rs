// l5_agg: aggregation generator for the five-speed spectrum .
// Subcommands:
//   scan <leanroot> <Module>...        import closure (LRSpectrumFull.* only), modules carrying a real `sorry` token, families
//   gen  <leanroot> <aggdir> <outdir>  emit rep-block masters, holes structure, link and final glue (see gen.rs section)
//   status <leanroot> <aggdir>         per depth-1 node: expected, built, holes, what the final still needs
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::Path;

mod gen;

pub fn strip_comments(s: &str) -> String {
    let b: Vec<char> = s.chars().collect();
    let mut out = String::with_capacity(s.len());
    let mut i = 0;
    let mut depth = 0usize;
    let mut in_str = false;
    while i < b.len() {
        let c = b[i];
        if depth > 0 {
            if c == '/' && i + 1 < b.len() && b[i + 1] == '-' { depth += 1; i += 2; continue; }
            if c == '-' && i + 1 < b.len() && b[i + 1] == '/' { depth -= 1; i += 2; continue; }
            if c == '\n' { out.push('\n'); }
            i += 1;
            continue;
        }
        if in_str {
            if c == '\\' { i += 2; continue; }
            if c == '"' { in_str = false; }
            i += 1;
            continue;
        }
        if c == '/' && i + 1 < b.len() && b[i + 1] == '-' { depth = 1; i += 2; continue; }
        if c == '-' && i + 1 < b.len() && b[i + 1] == '-' {
            while i < b.len() && b[i] != '\n' { i += 1; }
            continue;
        }
        if c == '"' { in_str = true; i += 1; continue; }
        out.push(c);
        i += 1;
    }
    out
}

pub fn has_word(s: &str, w: &str) -> bool {
    let bytes = s.as_bytes();
    let mut start = 0;
    while let Some(p) = s[start..].find(w) {
        let a = start + p;
        let e = a + w.len();
        let before = a == 0 || !(bytes[a - 1].is_ascii_alphanumeric() || bytes[a - 1] == b'_' || bytes[a - 1] == b'.');
        let after = e >= bytes.len() || !(bytes[e].is_ascii_alphanumeric() || bytes[e] == b'_');
        if before && after { return true; }
        start = e;
    }
    false
}

pub fn mod_path(root: &str, m: &str) -> String {
    format!("{}/{}.lean", root, m.replace('.', "/"))
}

pub fn imports_of(src: &str) -> Vec<String> {
    let st = strip_comments(src);
    let mut v = vec![];
    for l in st.lines() {
        let t = l.trim();
        if let Some(r) = t.strip_prefix("import ") {
            for m in r.split_whitespace() { v.push(m.to_string()); }
        }
    }
    v
}

pub fn family(m: &str) -> String {
    let mut o = String::new();
    let mut prev_digit = false;
    for c in m.chars() {
        if c.is_ascii_digit() {
            if !prev_digit { o.push('N'); }
            prev_digit = true;
        } else { o.push(c); prev_digit = false; }
    }
    o
}

/// closure over LRSpectrumFull.* modules; returns (modules in discovery order, map module -> has_sorry)
pub fn closure(root: &str, roots: &[String]) -> (Vec<String>, HashMap<String, bool>, BTreeSet<String>) {
    let mut seen: HashMap<String, bool> = HashMap::new();
    let mut order = vec![];
    let mut missing = BTreeSet::new();
    let mut stack: Vec<String> = roots.to_vec();
    while let Some(m) = stack.pop() {
        if seen.contains_key(&m) { continue; }
        if !m.starts_with("LRSpectrumFull.") { continue; }
        let p = mod_path(root, &m);
        let src = match fs::read_to_string(&p) { Ok(s) => s, Err(_) => { missing.insert(m.clone()); seen.insert(m.clone(), false); continue; } };
        let st = strip_comments(&src);
        let hs = has_word(&st, "sorry");
        seen.insert(m.clone(), hs);
        order.push(m.clone());
        for i in imports_of(&src) { stack.push(i); }
    }
    (order, seen, missing)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 { eprintln!("usage: l5_agg scan|gen|status ..."); std::process::exit(2); }
    match args[1].as_str() {
        "scan" => {
            let root = &args[2];
            let roots: Vec<String> = args[3..].to_vec();
            let (order, seen, missing) = closure(root, &roots);
            let mut fam: BTreeMap<String, Vec<String>> = BTreeMap::new();
            for m in &order { if seen[m] { fam.entry(family(m)).or_default().push(m.clone()); } }
            println!("closure: {} LRSpectrumFull modules ({} source files missing)", order.len(), missing.len());
            println!("modules with a real `sorry` token: {}", fam.values().map(|v| v.len()).sum::<usize>());
            for (f, v) in &fam { println!("  family {} : {} module(s){}", f, v.len(), if v.len() <= 3 { format!(" {:?}", v) } else { String::new() }); }
            for m in &missing { println!("  MISSING source {}", m); }
        }
        "closure" => {
            let root = &args[2];
            let roots: Vec<String> = args[3..].to_vec();
            let (order, _, _) = closure(root, &roots);
            for m in order { println!("{}", m); }
        }
        "gen" => gen::run(&args[2..]),
        "pending" => { for m in gen::pending(&args[2]) { println!("{}", m); } }
        "leaves" => gen::leaves(&args[2..]),
        "order" => { for m in gen::order(&args[2]) { println!("{}", m); } }
        "status" => gen::status(&args[2..]),
        _ => { eprintln!("unknown"); std::process::exit(2); }
    }
    let _ = Path::new(".");
}
