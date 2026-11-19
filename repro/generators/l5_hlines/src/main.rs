// l5hlines: the `hlines` mirror of the generated aggregation tree (stage S4V).
// For every generated module AggFive.{Leaf*,Mid*,D*} and AggFive.Top it writes AggFive/Hl/<Name>.lean with
//   structure HLines : the lines hypotheses that remain (one per hole representative, one per built representative without L5Reg.lines<c>, one per child),
//   theorem block_good : Good T5Store.t5 (<Name>.block ..)   (same term shape as the generated `block`, side conditions by unification),
// and for Top `lines_all : forall cl in Top.topTab H, LinesCl T5Store.t5 cl`.
// usage: l5hlines gen          write the mirror modules (only files whose text changed) + state/hl_order.txt + state/hl_manifest.tsv
//        l5hlines status       print the remaining-hypothesis summary from the generated text (no file written)
// Nothing here is trusted: the Lean kernel checks every generated module; a wrong rep / offset is a type error.
use std::collections::{BTreeMap, HashSet};
use std::env;
use std::fmt::Write as FW;
use std::fs;

const LEAN: &str = "/DEV_TREE/lean/LRSpectrumFull";
const BUILD: &str = "/DEV_TREE/lean/.lake/build/lib/lean/LRSpectrumFull";
const STATE: &str = "/DEV_TREE/work/l5_hlines/state";

#[derive(Debug, Clone)]
enum Node { Atom(String), App(Vec<Node>) }

fn tokenize(s: &str) -> Vec<String> {
    let mut v = vec![]; let mut cur = String::new();
    for ch in s.chars() {
        if ch == '(' || ch == ')' { if !cur.is_empty() { v.push(cur.clone()); cur.clear(); } v.push(ch.to_string()); }
        else if ch.is_whitespace() { if !cur.is_empty() { v.push(cur.clone()); cur.clear(); } }
        else { cur.push(ch); }
    }
    if !cur.is_empty() { v.push(cur); }
    v
}
// parse a sequence of items until ')' or end; each item is an atom or a parenthesised group
fn parse_seq(t: &[String], i: &mut usize) -> Vec<Node> {
    let mut out = vec![];
    while *i < t.len() {
        if t[*i] == ")" { return out; }
        if t[*i] == "(" { *i += 1; let inner = parse_seq(t, i); assert!(*i < t.len() && t[*i] == ")", "unbalanced"); *i += 1;
            out.push(if inner.len() == 1 { inner.into_iter().next().unwrap() } else { Node::App(inner) }); }
        else { out.push(Node::Atom(t[*i].clone())); *i += 1; }
    }
    out
}
fn parse_expr(s: &str) -> Node {
    let t = tokenize(s); let mut i = 0; let v = parse_seq(&t, &mut i);
    assert!(i == t.len(), "trailing tokens");
    if v.len() == 1 { v.into_iter().next().unwrap() } else { Node::App(v) }
}

struct Module {
    name: String,          // Leaf0_0, Mid5_1_0, D5, Top
    kind: char,            // 'L' leaf, 'M' mid, 'D' root, 'T' top
    text: String,
    has_holes: bool,
    holes: Vec<String>,    // leaf: h<c> field names
    reps: Vec<usize>,      // leaf: built reps (import GD3O<c>)
}

fn read_module(name: &str) -> Module {
    let text = fs::read_to_string(format!("{}/AggFive/{}.lean", LEAN, name)).unwrap();
    let kind = if name.starts_with("Leaf") { 'L' } else if name.starts_with("Mid") { 'M' } else if name == "Top" { 'T' } else { 'D' };
    let has_holes = text.lines().any(|l| l.trim_end() == "structure Holes where");
    let mut holes = vec![];
    if has_holes && kind == 'L' {
        for l in text.lines() {
            if let Some(r) = l.strip_prefix("  h") { if let Some(p) = r.find(" : ") { let d = &r[..p]; if d.chars().all(|c| c.is_ascii_digit()) && !d.is_empty() { holes.push(format!("h{}", d)); } } }
        }
    }
    let mut reps = vec![];
    if kind == 'L' {
        for l in text.lines() { if let Some(r) = l.strip_prefix("import LRSpectrumFull.L5S4.GD3O") { if let Ok(c) = r.trim().trim_start_matches('A').parse::<usize>() { reps.push(c); } } }
    }
    Module { name: name.to_string(), kind, text, has_holes, holes, reps }
}

fn list_modules() -> Vec<String> {
    let mut v: Vec<String> = fs::read_dir(format!("{}/AggFive", LEAN)).unwrap().filter_map(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().to_string()).filter(|n| n.ends_with(".lean"))
        .map(|n| n.trim_end_matches(".lean").to_string())
        .filter(|n| n.starts_with("Leaf") || n.starts_with("Mid") || n == "Top" || (n.starts_with('D') && n[1..].chars().all(|c| c.is_ascii_digit()) && n.len() > 1)).collect();
    v.sort(); v
}

// rep -> RegFin group number, only for groups whose olean exists
fn regfin_map() -> BTreeMap<usize, String> {
    let mut m = BTreeMap::new();
    let mut files: Vec<String> = fs::read_dir(format!("{}/L5Reg", LEAN)).unwrap().filter_map(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().to_string()).filter(|n| n.starts_with("RegFin") && n.ends_with(".lean")).collect();
    files.sort();
    for f in files {
        let g = f.trim_end_matches(".lean").to_string();
        if fs::metadata(format!("{}/L5Reg/{}.olean", BUILD, g)).is_err() { continue; }
        let s = fs::read_to_string(format!("{}/L5Reg/{}", LEAN, f)).unwrap();
        for l in s.lines() { if let Some(r) = l.strip_prefix("theorem lines") { if let Some(p) = r.find(" :") { if let Ok(c) = r[..p].parse::<usize>() { m.insert(c, g.clone()); } } } }
    }
    m
}

struct Ctx<'a> { mods: &'a BTreeMap<String, Module>, rf: &'a BTreeMap<usize, String> }

// transform the generated `block` expression into the mirror term. `child_idx` counts child modules in text order.
fn xform(n: &Node, cx: &Ctx, m: &Module, child_idx: &mut usize, used_missing: &mut Vec<usize>) -> String {
    match n {
        Node::Atom(a) => {
            if let Some(d) = a.strip_prefix('r') { if let Ok(c) = d.parse::<usize>() { return rep_term(c, cx, used_missing); } }
            if let Some(nm) = a.strip_suffix(".block") { return child_term(nm, None, cx, m, child_idx); }
            panic!("unexpected atom {} in {}", a, m.name);
        }
        Node::App(v) => {
            let head = match &v[0] { Node::Atom(h) => h.clone(), _ => panic!("non-atom head in {}", m.name) };
            if head == "RBlock.append" {
                assert!(v.len() == 4, "append arity");
                format!("(good_append {} {} _)", xform(&v[1], cx, m, child_idx, used_missing), xform(&v[2], cx, m, child_idx, used_missing))
            } else if head == "RepData.blk" {
                let a = match &v[1] { Node::Atom(a) => a.clone(), _ => panic!("blk arg") };
                let h = a.strip_prefix("H.").unwrap_or_else(|| panic!("blk arg {}", a));
                format!("(good_of_tab HL.{})", h)
            } else if let Some(nm) = head.strip_suffix(".block") {
                let a = match v.get(1) { Some(Node::Atom(a)) => a.clone(), _ => panic!("child arg in {}", m.name) };
                child_term(nm, Some(&a), cx, m, child_idx)
            } else { panic!("unexpected head {} in {}", head, m.name) }
        }
    }
}
fn rep_term(c: usize, cx: &Ctx, used_missing: &mut Vec<usize>) -> String {
    if cx.rf.contains_key(&c) { format!("(good_of_tab L5Reg.lines{})", c) } else { used_missing.push(c); format!("(good_of_tab HL.m{})", c) }
}
fn child_term(nm: &str, harg: Option<&str>, cx: &Ctx, m: &Module, child_idx: &mut usize) -> String {
    let i = *child_idx; *child_idx += 1;
    let ch = cx.mods.get(nm).unwrap_or_else(|| panic!("child {} of {} missing", nm, m.name));
    if ch.has_holes {
        let a = harg.unwrap_or_else(|| panic!("child {} has holes but no argument in {}", nm, m.name));
        format!("(Hl.{}.block_good {} HL.k{})", nm, a, i)
    } else { assert!(harg.is_none()); format!("(Hl.{}.block_good HL.k{})", nm, i) }
}

fn block_expr(m: &Module) -> (String, String) {
    // returns (the expression text after `:=`, the header text before)
    for l in m.text.lines() {
        if l.starts_with("noncomputable def block") {
            let p = l.find(":=").expect(":=");
            return (l[p + 2..].trim().to_string(), l[..p].to_string());
        }
    }
    panic!("no block in {}", m.name)
}

fn children_of(m: &Module) -> Vec<String> {
    // child module names in text order of the block expression
    let (e, _) = block_expr(m);
    let mut out = vec![];
    for t in tokenize(&e) { if let Some(nm) = t.strip_suffix(".block") { out.push(nm.to_string()); } }
    out
}

fn gen_module(m: &Module, cx: &Ctx, used_rf_groups: &mut Vec<String>, manifest: &mut String) -> String {
    let mut s = String::new();
    let (e, _) = block_expr(m);
    let ast = parse_expr(&e);
    let mut ci = 0usize; let mut missing: Vec<usize> = vec![];
    let term = xform(&ast, cx, m, &mut ci, &mut missing);
    let kids = children_of(m);
    let mut imports: Vec<String> = vec![format!("LRSpectrumFull.AggFive.{}", m.name), "LRSpectrumFull.L5S5.AggLines".to_string()];
    let mut groups: Vec<String> = vec![];
    if m.kind == 'L' { for &c in &m.reps { if let Some(g) = cx.rf.get(&c) { if !groups.contains(g) { groups.push(g.clone()); } } } }
    groups.sort();
    for g in &groups { imports.push(format!("LRSpectrumFull.L5Reg.{}", g)); used_rf_groups.push(g.clone()); }
    for k in &kids { imports.push(format!("LRSpectrumFull.AggFive.Hl.{}", k)); }
    writeln!(s, "/-\n# AggFive.Hl.{} : the lines clause carried by `{}.block` (generated by l5_hlines)\n\n`HLines` lists the lines hypotheses that remain: one per hole representative (`h<c>`), one per built representative without a `L5Reg.lines<c>` theorem (`m<c>`), one per child (`k<i>`).\nNo `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.\n-/", m.name, m.name).unwrap();
    for i in &imports { writeln!(s, "import {}", i).unwrap(); }
    writeln!(s, "\nset_option maxRecDepth 100000\nnamespace LRSpectrumFull\nnamespace AggFive\nnamespace Hl\nnamespace {}\nopen LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S5 LRSpectrumFull.L5Reg\n", m.name).unwrap();
    let hp = if m.has_holes { format!(" (H : AggFive.{}.Holes)", m.name) } else { String::new() };
    let hl_ty = if m.has_holes { "HLines H" } else { "HLines" };
    writeln!(s, "structure HLines{} : Prop where", hp).unwrap();
    if m.kind == 'L' {
        for h in &m.holes { writeln!(s, "  {} : ∀ cl ∈ (H.{}).tab, LinesCl T5Store.t5 cl", h, h).unwrap(); }
        for &c in &missing { writeln!(s, "  m{} : ∀ cl ∈ N{}.tabO, LinesCl T5Store.t5 cl", c, c).unwrap(); }
    } else {
        // children in text order; field type depends on whether the child has holes (argument `H.c<n>` read from the generated text)
        let toks = tokenize(&e); let mut idx = 0usize;
        let mut t = 0usize;
        while t < toks.len() {
            if let Some(nm) = toks[t].strip_suffix(".block") {
                let ch = &cx.mods[nm];
                if ch.has_holes { let a = toks[t + 1].trim_end_matches(')').to_string(); writeln!(s, "  k{} : Hl.{}.HLines {}", idx, nm, a).unwrap(); }
                else { writeln!(s, "  k{} : Hl.{}.HLines", idx, nm).unwrap(); }
                idx += 1;
            }
            t += 1;
        }
    }
    writeln!(s).unwrap();
    let hargs = if m.has_holes { format!(" (H : AggFive.{}.Holes)", m.name) } else { String::new() };
    let hexpr = if m.has_holes { format!("(AggFive.{}.block H)", m.name) } else { format!("AggFive.{}.block", m.name) };
    writeln!(s, "theorem block_good{} (HL : {}) : Good T5Store.t5 {} :=\n  {}\n", hargs, hl_ty, hexpr, term).unwrap();
    writeln!(s, "#print axioms block_good\n\nend {}\nend Hl\nend AggFive\nend LRSpectrumFull", m.name).unwrap();
    let nh = m.holes.len();
    writeln!(manifest, "{}\t{}\t{}\t{}\t{}\t{}\t{}", m.name, m.kind, m.has_holes, nh, m.reps.len(), missing.len(), kids.len()).unwrap();
    s
}

fn gen_top(m: &Module, cx: &Ctx, manifest: &mut String) -> String {
    // Top: Holes fields d<k>; topTab = (dB<k> H).tab ++ ... ; D<k> with/without holes
    let mut ds: Vec<usize> = vec![];
    for l in m.text.lines() {
        if l.starts_with("noncomputable def topTab") {
            for t in tokenize(l) { if let Some(r) = t.strip_prefix("dB") { if let Ok(k) = r.parse::<usize>() { ds.push(k); } } }
        }
    }
    let mut dh: Vec<(usize, bool)> = vec![];
    for &k in &ds { let nm = format!("D{}", k); dh.push((k, cx.mods[&nm].has_holes)); }
    let mut s = String::new();
    writeln!(s, "/-\n# AggFive.Hl.Top : the lines clause for `Top.topTab` (generated by l5_hlines)\n\n`HLines H` = the lines hypotheses of all depth-1 nodes; `lines_all` is the lines clause of the concatenated local class tables, the hypothesis `hlines` of `FiveSpeedHyps2`.\nNo `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.\n-/").unwrap();
    writeln!(s, "import LRSpectrumFull.AggFive.Top\nimport LRSpectrumFull.L5S5.AggLines").unwrap();
    for &(k, _) in &dh { writeln!(s, "import LRSpectrumFull.AggFive.Hl.D{}", k).unwrap(); }
    writeln!(s, "\nset_option maxRecDepth 100000\nnamespace LRSpectrumFull\nnamespace AggFive\nnamespace Hl\nnamespace Top\nopen LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S5 LRSpectrumFull.L5Reg\n").unwrap();
    writeln!(s, "structure HLines (H : AggFive.Top.Holes) : Prop where").unwrap();
    for &(k, h) in &dh { if h { writeln!(s, "  d{} : Hl.D{}.HLines H.d{}", k, k, k).unwrap(); } else { writeln!(s, "  d{} : Hl.D{}.HLines", k, k).unwrap(); } }
    writeln!(s).unwrap();
    writeln!(s, "/-- the lines clause for every class of the concatenated local tables of the whole tree -/\ntheorem lines_all (H : AggFive.Top.Holes) (HL : HLines H) : ∀ cl ∈ AggFive.Top.topTab H, LinesCl T5Store.t5 cl := by\n  intro cl hcl\n  unfold AggFive.Top.topTab {} at hcl", dh.iter().map(|&(k, _)| format!("AggFive.Top.dB{}", k)).collect::<Vec<_>>().join(" ")).unwrap();
    // topTab is left-nested: ((a0 ++ a1) ++ ...) ++ a(n-1); peel the last summand first
    for (j, &(k, h)) in dh.iter().enumerate().rev() {
        let ex = if h { format!("(Hl.D{}.block_good H.d{} HL.d{}) cl", k, k, k) } else { format!("(Hl.D{}.block_good HL.d{}) cl", k, k) };
        if j == 0 { writeln!(s, "  exact {} hcl", ex).unwrap(); }
        else { writeln!(s, "  rcases List.mem_append.1 hcl with hcl | h\n  swap\n  · exact {} h", ex).unwrap(); }
    }
    writeln!(s, "\n#print axioms lines_all\n\nend Top\nend Hl\nend AggFive\nend LRSpectrumFull").unwrap();
    writeln!(manifest, "Top\tT\ttrue\t0\t0\t0\t{}", dh.len()).unwrap();
    let _ = cx;
    s
}

fn write_if_changed(path: &str, content: &str) -> bool {
    if let Ok(old) = fs::read_to_string(path) { if old == content { return false; } }
    fs::write(path, content).unwrap(); true
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let mode = a.get(1).map(|s| s.as_str()).unwrap_or("");
    let names = list_modules();
    let mut mods: BTreeMap<String, Module> = BTreeMap::new();
    for n in &names { mods.insert(n.clone(), read_module(n)); }
    let rf = regfin_map();
    let cx = Ctx { mods: &mods, rf: &rf };
    if mode == "gen" {
        fs::create_dir_all(format!("{}/AggFive/Hl", LEAN)).unwrap();
        let mut manifest = String::from("module\tkind\thas_holes\tholes\tbuilt_reps\tmissing_reg\tchildren\n");
        let mut changed = 0; let mut total = 0;
        let mut order: Vec<String> = vec![];
        let mut groups_used: Vec<String> = vec![];
        for kind in ['L', 'M', 'D', 'T'] {
            for n in &names {
                let m = &mods[n];
                if m.kind != kind { continue; }
                let s = if kind == 'T' { gen_top(m, &cx, &mut manifest) } else { gen_module(m, &cx, &mut groups_used, &mut manifest) };
                if write_if_changed(&format!("{}/AggFive/Hl/{}.lean", LEAN, n), &s) { changed += 1; }
                total += 1; order.push(n.clone());
            }
        }
        // drop mirror files of modules that no longer exist
        let have: HashSet<String> = order.iter().cloned().collect();
        for e in fs::read_dir(format!("{}/AggFive/Hl", LEAN)).unwrap().filter_map(|e| e.ok()) {
            let n = e.file_name().to_string_lossy().to_string();
            if n.ends_with(".lean") { let b = n.trim_end_matches(".lean").to_string(); if !have.contains(&b) { eprintln!("note: stale mirror file {} (module no longer generated)", n); } }
        }
        fs::write(format!("{}/hl_order.txt", STATE), order.join("\n") + "\n").unwrap();
        fs::write(format!("{}/hl_manifest.tsv", STATE), manifest).unwrap();
        eprintln!("l5hlines: {} mirror modules ({} written/changed); RegFin groups available: {}; reps with lines<c>: {}", total, changed, { let mut g: Vec<&String> = rf.values().collect(); g.sort(); g.dedup(); g.len() }, rf.len());
    } else if mode == "fixtop" {
        // rewrite the `look<k>` proofs of AggFive/Top.lean (split_ifs hits the simp step limit) to an explicit if_neg/if_pos chain; same text as the patched l5_agg generator
        let p = format!("{}/AggFive/Top.lean", LEAN);
        let text = fs::read_to_string(&p).unwrap();
        let mut bounds: Vec<(usize, usize)> = vec![]; // (k, upper bound), in order; the last has none
        for l in text.lines() { if l.starts_with("noncomputable def topIdx") {
            let t = tokenize(l); let mut i = 0;
            while i < t.len() { if t[i] == "if" && t[i + 1] == "c" && t[i + 2] == "<" { let b: usize = t[i + 3].parse().unwrap(); let k: usize = t[i + 6].trim_start_matches("dB").parse().unwrap(); bounds.push((k, b)); i += 7; } else { i += 1; } }
            let lastk: usize = { let pos = t.iter().rposition(|x| x.starts_with("dB")).unwrap(); t[pos].trim_start_matches("dB").parse().unwrap() };
            bounds.push((lastk, usize::MAX));
        } }
        let ls: Vec<&str> = text.lines().collect(); let mut out: Vec<String> = vec![]; let mut i = 0; let mut n = 0;
        while i < ls.len() {
            let l = ls[i];
            if l.starts_with("theorem look") && l.ends_with(":= by") {
                let k: usize = l["theorem look".len()..].split(' ').next().unwrap().parse().unwrap();
                let j = bounds.iter().position(|b| b.0 == k).unwrap();
                let first = if j == 0 { 0 } else { bounds[j - 1].1 };
                let mut rwl: Vec<String> = vec![];
                for (jj, b) in bounds.iter().enumerate() {
                    if jj < j { rwl.push(format!("if_neg (show ¬ ({} + i < {}) by omega)", first, b.1)); }
                    else if jj == j && jj + 1 < bounds.len() { rwl.push(format!("if_pos (show {} + i < {} by omega)", first, b.1)); }
                }
                out.push(l.to_string()); out.push("  unfold topIdx".to_string()); out.push(format!("  rw [{}]", rwl.join(", "))); out.push("  all_goals (congr 1; omega)".to_string());
                i += 3; n += 1; continue;
            }
            if l.starts_with("theorem idx_t3") && ls.get(i + 2).map_or(false, |x| x.trim() == "split_ifs") {
                out.push(l.to_string()); out.push("  unfold topIdx".to_string());
                let mut j = i + 3; let mut exs: Vec<String> = vec![];
                while j < ls.len() && ls[j].starts_with("  · exact ") { exs.push(ls[j]["  · exact ".len()..].to_string()); j += 1; }
                assert!(exs.len() == bounds.len(), "idx_t3 bullets {} vs bounds {}", exs.len(), bounds.len());
                for (jj, ex) in exs.iter().enumerate() {
                    if jj + 1 < exs.len() { out.push(format!("  by_cases h{} : c < {}", jj, bounds[jj].1)); out.push(format!("  · rw [if_pos h{}]; exact {}", jj, ex)); out.push(format!("  rw [if_neg h{}]", jj)); }
                    else { out.push(format!("  exact {}", ex)); }
                }
                i = j; n += 1; continue;
            }
            out.push(l.to_string()); i += 1;
        }
        let mut s = out.join("\n"); s.push('\n');
        fs::write(&p, s).unwrap();
        eprintln!("fixtop: rewrote {} look proofs", n);
    } else if mode == "status" {
        let mut holes_by_node: BTreeMap<String, usize> = BTreeMap::new();
        let (mut nh, mut nbuilt, mut nmiss) = (0, 0, 0);
        for (n, m) in &mods { if m.kind == 'L' {
            let node: String = n.trim_start_matches("Leaf").split('_').next().unwrap().to_string();
            *holes_by_node.entry(node).or_default() += m.holes.len();
            nh += m.holes.len(); nbuilt += m.reps.len(); nmiss += m.reps.iter().filter(|c| !rf.contains_key(c)).count();
        } }
        println!("leaves {} ; hole reps {} ; built reps {} ; built reps without lines<c> {}", mods.values().filter(|m| m.kind == 'L').count(), nh, nbuilt, nmiss);
        for (k, v) in &holes_by_node { if *v > 0 { println!("node {} holes {}", k, v); } }
    } else { eprintln!("usage: l5hlines gen | status"); }
}
