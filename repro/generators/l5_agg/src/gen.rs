// Generator of the five-speed aggregation .  Resumable and incremental: every file is rewritten only if its text changed;
// built representatives (olean of GD3O<c> present and results.tsv DONE/DONE_PRIOR with STD axioms) become real singles, all others
// become fields of the generated `Holes` structures (explicit hypotheses).  Rust is untrusted: the Lean kernel checks every link.
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::Path;

const ENODES: [usize; 4] = [1, 5, 13, 19]; // depth-1 nodes whose t2 final is the v3 family T2E<k> (T2E13 built as comparison by S4S)
const NREP: usize = 1965;

#[derive(Clone, Debug)]
pub struct Node { pub k: usize, pub first: usize, pub size: usize }

// main-module name of rep c.  Reps 1 and 2 collide with the S4O library modules GD3O1, GD3O2; their generated main modules are
// GD3OA1, GD3OA2 (table l5_rollout/modname.tsv, rep TAB name; default GD3O<c>).  The namespace stays N<c>.
fn mname(c: usize) -> String {
    let p = "/DEV_TREE/work/l5_rollout/modname.tsv";
    if let Ok(t) = fs::read_to_string(p) {
        for l in t.lines() {
            let f: Vec<&str> = l.split('\t').collect();
            if f.len() == 2 && f[0].trim().parse::<usize>().ok() == Some(c) { return f[1].trim().to_string(); }
        }
    }
    format!("GD3O{}", c)
}

fn xns(k: usize) -> String { if ENODES.contains(&k) { format!("T2E{}", k) } else { format!("T2D{}", k) } }

pub struct Cfg {
    pub lean: String,   // lean
    pub roll: String,   // results.tsv
    pub rlst: String,   // T2RL_STATUS.tsv (node, clsFirst, size)
    pub nodes: Vec<Node>,
    pub built: BTreeSet<usize>,
    pub results: HashMap<usize, (String, String)>,
}

fn read_cfg(a: &[String]) -> Cfg {
    let lean = a[0].clone();
    let roll = a[1].clone();
    let rlst = a[2].clone();
    let mut nodes = vec![];
    for l in fs::read_to_string(&rlst).unwrap().lines().skip(1) {
        let f: Vec<&str> = l.split('\t').collect();
        if f.len() < 3 { continue; }
        nodes.push(Node { k: f[0].parse().unwrap(), first: f[1].parse().unwrap(), size: f[2].parse().unwrap() });
    }
    assert_eq!(nodes.len(), 26);
    let tot: usize = nodes.iter().map(|n| n.size).sum();
    assert_eq!(tot, NREP, "sizes must sum to 1965");
    let mut results = HashMap::new();
    for l in fs::read_to_string(&roll).unwrap().lines().skip(1) {
        let f: Vec<&str> = l.split('\t').collect();
        if f.len() < 11 { continue; }
        if let Ok(c) = f[0].parse::<usize>() { results.insert(c, (f[1].to_string(), f[10].to_string())); }
    }
    let mut built = BTreeSet::new();
    for c in 0..NREP {
        let ol = format!("{}/.lake/build/lib/lean/LRSpectrumFull/L5S4/{}.olean", lean, mname(c));
        let src = format!("{}/LRSpectrumFull/L5S4/{}.lean", lean, mname(c));
        let ok_res = match results.get(&c) { Some((s, ax)) => (s == "DONE" || s == "DONE_PRIOR") && ax.starts_with("STD"), None => false };
        if ok_res && Path::new(&ol).exists() {
            if let Ok(t) = fs::read_to_string(&src) {
                if t.contains("def tabO") && t.contains("theorem t3_nodeU_of") { built.insert(c); }
            }
        }
    }
    // reps built by other chains (#265, #304 ...) whose axioms were observed during the aggregation: state/extra_built.txt
    if let Ok(t) = fs::read_to_string("/DEV_TREE/work/l5_agg/state/extra_built.txt") {
        for l in t.lines() {
            if let Ok(c) = l.trim().parse::<usize>() {
                let ol = format!("{}/.lake/build/lib/lean/LRSpectrumFull/L5S4/{}.olean", lean, mname(c));
                if Path::new(&ol).exists() { built.insert(c); }
            }
        }
    }
    Cfg { lean, roll, rlst, nodes, built, results }
}

struct Out { dir: String, changed: Vec<String>, all: Vec<(String, String)> } // (dotted module, kind)
impl Out {
    fn put(&mut self, rel: &str, module: &str, kind: &str, text: &str) {
        let p = format!("{}/{}", self.dir, rel);
        if let Some(par) = Path::new(&p).parent() { fs::create_dir_all(par).unwrap(); }
        let old = fs::read_to_string(&p).unwrap_or_default();
        if old != text { fs::write(&p, text).unwrap(); self.changed.push(module.to_string()); }
        self.all.push((module.to_string(), kind.to_string()));
    }
}

fn rep_pos(cfg: &Cfg, c: usize) -> (usize, usize) {
    for n in &cfg.nodes { if n.size > 0 && c >= n.first && c < n.first + n.size { return (n.k, c - n.first); } }
    panic!("class id {} outside all nodes", c);
}

fn note_for(c: usize) -> &'static str {
    match c {
        304 => "critical leaves (kind 0): separate critical-leaf chain, layout-U route, data not emitted yet",
        265 => "big rep (23,228 leaves, 78 chunks): the #265 chain on lane 1 plus a master over its chunks",
        _ => "leaf rollout driver (l5_rollout/rollout.sh, driver.pid) or the big-rep chain if > 2,400 leaves",
    }
}

/// balanced binary append of expressions (all of type X<k>.RB)
fn comb(items: &[String]) -> String {
    if items.len() == 1 { return items[0].clone(); }
    let m = items.len() / 2;
    format!("RBlock.append ({}) ({}) rfl", comb(&items[..m]), comb(&items[m..]))
}

fn clean_text(src: &str, cleanset: &BTreeSet<String>, swap13: bool) -> String {
    let mut dropped: BTreeSet<String> = BTreeSet::new();
    let mut lines: Vec<String> = vec![];
    for l in src.lines() {
        if l.contains("by sorry") {
            let t = l.trim_start();
            if let Some(r) = t.strip_prefix("theorem ") { dropped.insert(r.split_whitespace().next().unwrap().to_string()); }
            continue;
        }
        lines.push(l.to_string());
    }
    let mut out = String::from("-- CLEAN MIRROR (planted `sorry` controls removed), generated by l5_agg from the original module of the same name\n");
    for mut l in lines {
        let t = l.trim().to_string();
        if let Some(r) = t.strip_prefix("#print axioms ") { if dropped.contains(r.trim()) { continue; } }
        if let Some(r) = t.strip_prefix("import LRSpectrumFull.L5S4.") {
            let mut name = r.trim().to_string();
            if swap13 && name == "T2D13Pos" { name = "T2E13Pos".to_string(); }
            if cleanset.contains(&name) { l = format!("import LRSpectrumFull.AggFive.Clean.{}", name); }
            else { l = format!("import LRSpectrumFull.L5S4.{}", name); }
        }
        if swap13 {
            for w in ["repPos", "clsFirst", "t2_block"] { l = l.replace(&format!("T2D13.{}", w), &format!("T2E13.{}", w)); }
        }
        out.push_str(&l); out.push('\n');
    }
    out
}

pub fn run(a: &[String]) {
    let cfg = read_cfg(a);
    let outdir = format!("{}/LRSpectrumFull/AggFive", cfg.lean);
    let mut o = Out { dir: outdir.clone(), changed: vec![], all: vec![] };
    let l4 = format!("{}/LRSpectrumFull/L5S4", cfg.lean);
    o.all.push(("L5S5.AggBlock".into(), "base".into()));
    // ---- clean mirrors ----
    let mut cleanset: BTreeSet<String> = BTreeSet::new();
    cleanset.insert("T2All".into()); cleanset.insert("T2Final".into());
    for k in 0..26 { cleanset.insert(xns(k)); cleanset.insert(format!("{}Pos", xns(k))); }
    for name in cleanset.clone() {
        let src = fs::read_to_string(format!("{}/{}.lean", l4, name)).unwrap_or_else(|_| panic!("missing {}", name));
        let t = clean_text(&src, &cleanset, name == "T2Final");
        o.put(&format!("Clean/{}.lean", name), &format!("AggFive.Clean.{}", name), "clean", &t);
    }
    // ---- per-node link function modules X<k> ----
    for n in &cfg.nodes {
        let k = n.k;
        let t = format!(
"/-
# AggFive.X{k} : the row-link function E of depth-1 node #{k} and the block types (generated by l5_agg)

`E i` is the row set that the `t2` leader record at position `i` of the node demands of the rollout node of class `clsFirst + i`.
No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S5.AggBlock
import LRSpectrumFull.AggFive.Clean.{x}Pos

set_option maxRecDepth 100000

namespace LRSpectrumFull
namespace AggFive
namespace X{k}
open Matrix Finset LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S5

noncomputable def E (i : ℕ) := setRow T2D{k}.nK.rows 1 (cY ((T2D{k}.flatN.map unpackRec).getD ({x}.repPos.getD i 0) []))

abbrev RB := RBlock (fun n : NodeW 2 3 => n.rows) E
abbrev RD (pos : ℕ) := RepData (fun n : NodeW 2 3 => n.rows) E pos

end X{k}
end AggFive
end LRSpectrumFull
", k = k, x = xns(k));
        o.put(&format!("X{}.lean", k), &format!("AggFive.X{}", k), "x", &t);
    }
    // ---- trees of masters per node ----
    #[derive(Clone)]
    struct Mod { name: String, open: bool }
    let mut roots: Vec<Option<Mod>> = vec![None; 26];
    let mut stat: Vec<(usize, usize, usize, Vec<usize>)> = vec![]; // k, size, built, holes
    for n in &cfg.nodes {
        let k = n.k;
        if n.size == 0 { stat.push((k, 0, 0, vec![])); continue; }
        let nb = (n.size + 7) / 8;
        let mut level: Vec<Mod> = vec![];
        let mut holes_k = vec![];
        let mut nbuilt = 0;
        for j in 0..nb {
            let name = format!("Leaf{}_{}", k, j);
            let reps: Vec<usize> = (j * 8..((j + 1) * 8).min(n.size)).map(|i| n.first + i).collect();
            let mut imports = String::new();
            let mut defs = String::new();
            let mut fields = String::new();
            let mut items = vec![];
            let mut anyhole = false;
            for &c in &reps {
                let i = c - n.first;
                if cfg.built.contains(&c) {
                    nbuilt += 1;
                    imports.push_str(&format!("import LRSpectrumFull.L5S4.{}\n", mname(c)));
                    defs.push_str(&format!(
"theorem lk{c} : N{c}.nK.rows = X{k}.E {i} := by decide +kernel
noncomputable def r{c} : X{k}.RB := RBlock.single {i} N{c}.nK N{c}.tabO (fun C h => N{c}.t3_nodeU_of C h) lk{c}
", c = c, k = k, i = i));
                    items.push(format!("r{}", c));
                } else {
                    anyhole = true;
                    holes_k.push(c);
                    fields.push_str(&format!("  /-- class #{c}, position {i} of depth-1 node #{k}: module not built yet.  Discharged by: {nt}. -/\n  h{c} : X{k}.RD {i}\n", c = c, i = i, k = k, nt = note_for(c)));
                    items.push(format!("RepData.blk (H.h{})", c));
                }
            }
            let hs = if anyhole { format!("structure Holes where\n{}\n", fields) } else { String::new() };
            let sig = if anyhole { "(H : Holes) " } else { "" };
            let t = format!(
"/-
# AggFive.{name} : block of the representatives {r0}..{r1} of depth-1 node #{k} (generated by l5_agg; {nh} hole(s))

For every built representative: the row link `lk<c>` (kernel `decide`) and the single block from its `t3_nodeU_of`; every other one is a field of `Holes`.
No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.AggFive.X{k}
{imports}
set_option maxRecDepth 100000

namespace LRSpectrumFull
namespace AggFive
namespace {name}
open Matrix Finset LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S5

{defs}{hs}noncomputable def block {sig}: X{k}.RB := {body}

#print axioms block

end {name}
end AggFive
end LRSpectrumFull
", name = name, r0 = reps[0], r1 = reps[reps.len() - 1], k = k, nh = fields.matches("  h").count(), imports = imports, defs = defs, hs = hs, sig = sig, body = comb(&items));
            o.put(&format!("{}.lean", name), &format!("AggFive.{}", name), "leaf", &t);
            level.push(Mod { name, open: anyhole });
        }
        let mut lvl = 1;
        while level.len() > 1 {
            let mut next = vec![];
            for (j, grp) in level.chunks(8).enumerate() {
                let islast = level.len() <= 8;
                let name = if islast { format!("D{}", k) } else { format!("Mid{}_{}_{}", k, lvl, j) };
                let mut imports = String::new();
                let mut fields = String::new();
                let mut items = vec![];
                let mut anyopen = false;
                for (ci, ch) in grp.iter().enumerate() {
                    imports.push_str(&format!("import LRSpectrumFull.AggFive.{}\n", ch.name));
                    if ch.open {
                        anyopen = true;
                        fields.push_str(&format!("  c{} : {}.Holes\n", ci, ch.name));
                        items.push(format!("{}.block H.c{}", ch.name, ci));
                    } else { items.push(format!("{}.block", ch.name)); }
                }
                let hs = if anyopen { format!("structure Holes where\n{}\n", fields) } else { String::new() };
                let sig = if anyopen { "(H : Holes) " } else { "" };
                let t = format!(
"/-
# AggFive.{name} : master over {n} blocks of depth-1 node #{k} (generated by l5_agg)

`append` of its children in order; every side condition is `rfl` (literal arithmetic).
No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.AggFive.X{k}
{imports}
set_option maxRecDepth 100000
namespace LRSpectrumFull
namespace AggFive
namespace {name}
open LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S5

{hs}noncomputable def block {sig}: X{k}.RB := {body}

#print axioms block

end {name}
end AggFive
end LRSpectrumFull
", name = name, n = grp.len(), k = k, imports = imports, hs = hs, sig = sig, body = comb(&items));
                o.put(&format!("{}.lean", name), &format!("AggFive.{}", name), if islast { "root" } else { "mid" }, &t);
                next.push(Mod { name, open: anyopen });
            }
            level = next;
            lvl += 1;
        }
        // single leaf: rename to D<k>: emit a thin root
        if level.len() == 1 && level[0].name.starts_with("Leaf") {
            let ch = level[0].clone();
            let name = format!("D{}", k);
            let (hs, sig, body, fld) = if ch.open { ("structure Holes where\n  c0 : ".to_string() + &ch.name + ".Holes\n\n", "(H : Holes) ", format!("{}.block H.c0", ch.name), true) } else { (String::new(), "", format!("{}.block", ch.name), false) };
            let _ = fld;
            let t = format!(
"/-
# AggFive.{name} : root block of depth-1 node #{k} (generated by l5_agg; a single leaf master)
No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.AggFive.X{k}
import LRSpectrumFull.AggFive.{ch}
set_option maxRecDepth 100000

namespace LRSpectrumFull
namespace AggFive
namespace {name}
open LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S5

{hs}noncomputable def block {sig}: X{k}.RB := {body}

#print axioms block

end {name}
end AggFive
end LRSpectrumFull
", name = name, k = k, ch = ch.name, hs = hs, sig = sig, body = body);
            o.put(&format!("{}.lean", name), &format!("AggFive.{}", name), "root", &t);
            roots[k] = Some(Mod { name, open: ch.open });
        } else {
            roots[k] = Some(level[0].clone());
        }
        stat.push((k, n.size, nbuilt, holes_k));
    }
    // ---- Top ----
    let ne: Vec<&Node> = cfg.nodes.iter().filter(|n| n.size > 0).collect();
    let mut imp = String::new();
    let mut hfields = String::new();
    let mut bdefs = String::new();
    for n in &ne {
        let k = n.k;
        let r = roots[k].clone().unwrap();
        imp.push_str(&format!("import LRSpectrumFull.AggFive.D{}\n", k));
        if r.open {
            hfields.push_str(&format!("  /-- depth-1 node #{k}: representatives not built yet -/\n  d{k} : D{k}.Holes\n", k = k));
            bdefs.push_str(&format!("noncomputable def dB{k} (H : Holes) : X{k}.RB := D{k}.block H.d{k}\n", k = k));
        } else {
            bdefs.push_str(&format!("noncomputable def dB{k} (_H : Holes) : X{k}.RB := D{k}.block\n", k = k));
        }
    }
    let tab = ne.iter().map(|n| format!("(dB{} H).tab", n.k)).collect::<Vec<_>>().join(" ++ ");
    let mut idx = String::new();
    for (j, n) in ne.iter().enumerate() {
        let k = n.k;
        let arg = if n.first == 0 { "c".to_string() } else { format!("c - {}", n.first) };
        if j + 1 < ne.len() { idx.push_str(&format!("if c < {} then (dB{} H).idx ({}) else ", n.first + n.size, k, arg)); }
        else { idx.push_str(&format!("(dB{} H).idx ({})", k, arg)); }
    }
    let mut lemmas = String::new();
    // regs, sizes, lookups, lk
    for (jn, n) in ne.iter().enumerate() {
        let k = n.k;
        // S4V: explicit `if_neg`/`if_pos` chain instead of `split_ifs` (23 nested ifs: simp step limit)
        let mut rwl: Vec<String> = vec![];
        for (jj, m) in ne.iter().enumerate() {
            if jj < jn { rwl.push(format!("if_neg (show ¬ ({} + i < {}) by omega)", n.first, m.first + m.size)); }
            else if jj == jn && jj + 1 < ne.len() { rwl.push(format!("if_pos (show {} + i < {} by omega)", n.first, m.first + m.size)); }
        }
        let lookproof = format!("  unfold topIdx\n  rw [{}]\n  all_goals (congr 1; omega)\n", rwl.join(", "));
        lemmas.push_str(&format!(
"theorem sz{k} (H : Holes) : (dB{k} H).size = {s} := rfl
theorem pp{k} (H : Holes) : (dB{k} H).pos0 = 0 := rfl
theorem reg{k} {{H : Holes}} {{C : Certificate}} (hC : LocRegistered C (topTab H)) : LocRegistered C (dB{k} H).tab :=
  fun cl hcl => hC cl (by simp [topTab, hcl])
theorem look{k} (H : Holes) (i : ℕ) (hi : i < {s}) : topIdx H ({f} + i) = (dB{k} H).idx i := by
{lp}", k = k, s = n.size, f = n.first, lp = lookproof));
    }
    // t3 over all c
    let sum_expr = ne.iter().map(|n| format!("(dB{} H).size", n.k)).collect::<Vec<_>>().join(" + ");
    let rws = ne.iter().map(|n| format!("sz{} H", n.k)).collect::<Vec<_>>().join(", ");
    let total = format!("theorem total_size (H : Holes) : {} = {} := by rw [{}]\n", sum_expr, NREP, rws);
    let mut t3p = String::new();
    for (j, n) in ne.iter().enumerate() {
        let k = n.k;
        let arg = if n.first == 0 { "c".to_string() } else { format!("c - {}", n.first) };
        // S4V: by_cases chain instead of `split_ifs` (simp step limit)
        let ex = format!("(dB{k} H).ok C (reg{k} hC) ({arg}) (by rw [sz{k}]; omega)", k = k, arg = arg);
        if j + 1 < ne.len() { t3p.push_str(&format!("  by_cases h{j} : c < {b}\n  · rw [if_pos h{j}]; exact {ex}\n  rw [if_neg h{j}]\n", j = j, b = n.first + n.size, ex = ex)); }
        else { t3p.push_str(&format!("  exact {}\n", ex)); }
    }
    let mut lks = String::new();
    for n in &cfg.nodes {
        let k = n.k;
        if n.size == 0 {
            lks.push_str(&format!("theorem lk{k} (H : Holes) : T2Final.Lk{k} (topIdx H) := by\n  intro i hi\n  exfalso\n  have h : {x}.repPos.length = 0 := by decide +kernel\n  omega\n", k = k, x = xns(k)));
        } else {
            lks.push_str(&format!(
"theorem lk{k} (H : Holes) : T2Final.Lk{k} (topIdx H) := by
  intro i hi
  have hl : {x}.repPos.length = {s} := by decide +kernel
  have hi' : i < {s} := by omega
  have e : {x}.clsFirst = {f} := rfl
  rw [e, look{k} H i hi']
  have h := (dB{k} H).lk i (by rw [sz{k}]; exact hi')
  rw [pp{k}, Nat.zero_add] at h
  exact h
", k = k, x = xns(k), s = n.size, f = n.first));
        }
    }
    let lkargs = (0..26).map(|k| format!("(lk{} H)", k)).collect::<Vec<_>>().join(" ");
    let top = format!(
"/-
# AggFive.Top : the top block over the depth-1 nodes, the set R2, `t3` over it and `t2` from the row links (generated by l5_agg)

`topIdx H c` is the rollout node of class id `c`; `R2 H` its range; `top_t3` is the `t3` clause for all of R2 under `LocRegistered C (topTab H)`;
`t2_top` is `T2Final.t2_all` (clean mirror) with the 26 row links proved from the blocks.  `Holes` collects the holes of every node.
No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.AggFive.Clean.T2Final
{imp}
set_option maxRecDepth 100000

namespace LRSpectrumFull
namespace AggFive
namespace Top
open Matrix Finset LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S5

structure Holes where
{hfields}
{bdefs}
noncomputable def topTab (H : Holes) : List T4Rec := {tab}

noncomputable def topIdx (H : Holes) (c : ℕ) : NodeW 2 3 := {idx}

noncomputable def R2 (H : Holes) : Set (NodeW 2 3) := {{n | ∃ c, c < {nrep} ∧ n = topIdx H c}}

{lemmas}{total}
theorem idx_t3 (H : Holes) (C : Certificate) (hC : LocRegistered C (topTab H)) (c : ℕ) (hc : c < {nrep}) : T3At C (topIdx H c) := by
  unfold topIdx
{t3p}
theorem top_t3 (H : Holes) (C : Certificate) (hC : LocRegistered C (topTab H)) : ∀ n ∈ R2 H, T3At C n := by
  rintro n ⟨c, hc, rfl⟩
  exact idx_t3 H C hC c hc

{lks}
theorem t2_top (H : Holes) : ∀ n ∈ R1d1, T2Stmt n (R2 H) :=
  T2Final.t2_all (R2 H) (topIdx H) (fun c hc => ⟨c, hc, rfl⟩) {lkargs}

#print axioms top_t3
#print axioms t2_top

end Top
end AggFive
end LRSpectrumFull
", imp = imp, hfields = hfields, bdefs = bdefs, tab = tab, idx = idx, nrep = NREP, lemmas = lemmas, total = total, t3p = t3p, lks = lks, lkargs = lkargs);
    o.put("Top.lean", "AggFive.Top", "top", &top);
    // ---- Final ----
    let nholes: usize = stat.iter().map(|s| s.3.len()).sum();
    let fin = format!(
"/-
# L5S5.FiveSpeedFinal : `five_speed_spectrum` assembled from the generated aggregation (generated by l5_agg)

`FiveSpeedHyps` is the EXPLICIT LIST of what is still assumed: the {nholes} representatives without a built module (named fields of `holes`,
each tied to the driver that discharges it), the registration of the local class tables in the final class table `C.t4`, the `lines` clause
for `C` (discharged by `Lin.lines_clause_all` once `LinRAll` is built and `ht5` holds) and `ResOK` of the stored residual tuples.
`t1` is `d1_t1`, `t2` is `Top.t2_top` (row links from the blocks), `t3` is `Top.top_t3`.
No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.AggFive.Top
import LRSpectrumFull.L5S4.CheckT1
import LRSpectrumFull.L5S4.LinRCov

namespace LRSpectrumFull
namespace L5S5
open LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S4.Lin LRSpectrumFull.AggFive

structure FiveSpeedHyps where
  /-- H6/H7: the {nholes} depth-2 representatives whose module is not built (leaf rollout driver; #304 critical-leaf chain; #265 big-rep chain) -/
  holes : Top.Holes
  /-- the final certificate (H9: `Lin.lineCert LinRAll.blobs t5` once the lines driver has built `LinRAll`) -/
  C : Certificate
  /-- H8/H2: every local class table is registered in `C.t4` (rows `l` equal, ranges covered): lines/registration chain -/
  reg : LocRegistered C (Top.topTab holes)
  /-- H9: the `lines` clause for `C` (lines driver; `Lin.lines_clause_all` with `ht5`) -/
  lines : ∀ cl ∈ C.t4, ∀ u : V5, Primitive u → (∀ i, u i ≠ 0) → (∀ i j, i ≠ j → |u i| ≠ |u j|) →
    InClass cl u → (∃ r ∈ C.t5, ∃ g : SP, g.act u = r.v) ∨ 1 / 5 ≤ ML u
  /-- H3: the stored residual tuples are within the box (`ResOK`): T5 stage -/
  hres : ∀ r ∈ C.t5, ResOK r.v

/-- **The five-speed spectrum, conditional on `FiveSpeedHyps`.** -/
theorem five_speed_spectrum (hy : FiveSpeedHyps) (v : Fin 5 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hlt : ML v < 1 / 5) : ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1) :=
  five_speed_spectrum_of_clauses (R1 := R1d1) (R2 := Top.R2 hy.holes) d1_t1 (fun n hn => Top.t2_top hy.holes n hn)
    (Top.top_t3 hy.holes hy.C hy.reg) hy.lines hy.hres v hpos hinj hlt

/-- The same with the `lines` clause replaced by what the lines driver produces: the chunk theorem `LinRAll.ok` for `blobs`
(`Lin.lines_clause_tab`, no hypothesis on the class table).  Instantiating `blobs := LinRAll.blobs`, `hok := LinRAll.ok` is the last step
once the lines driver has built `LinRAll`. -/
structure FiveSpeedHypsL where
  /-- H6/H7: representatives without a built module (see `FiveSpeedHyps.holes`) -/
  holes : Top.Holes
  /-- the class table of the lines stage (`LinRAll.blobs`, in class-id order = concatenation of the local tables) -/
  blobs : List (ℕ × ℕ)
  /-- H9: the chunk theorem for `blobs` (`LinRAll.ok`; lines driver) -/
  hok : (blobs.all fun p => classLinesR (L5S4.dg p.1) p.2) = true
  /-- the residual tuples of the T5 stage -/
  t5 : List T5Rec
  /-- H3: the 25 residual tuples `T5V` are among the stored records (`ht5_of_incl` with `T5Store`; T5 stage) -/
  ht5 : ∀ r ∈ T5V, ∃ r' ∈ t5, r'.v = T5Vec r
  /-- H3: `ResOK` of the stored residual tuples -/
  hres : ∀ r ∈ t5, ResOK r.v
  /-- H8: registration of every local class table in `linTab blobs` (lines/registration chain) -/
  reg : LocRegistered (lineCert blobs t5) (Top.topTab holes)

theorem five_speed_spectrum_lines (hy : FiveSpeedHypsL) (v : Fin 5 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hlt : ML v < 1 / 5) : ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1) :=
  five_speed_spectrum ⟨hy.holes, lineCert hy.blobs hy.t5, hy.reg, lines_clause_tab hy.blobs hy.t5 hy.hok hy.ht5, hy.hres⟩
    v hpos hinj hlt

#print axioms five_speed_spectrum
#print axioms five_speed_spectrum_lines

end L5S5
end LRSpectrumFull
", nholes = nholes);
    {
        let p = format!("{}/LRSpectrumFull/L5S5/FiveSpeedFinal.lean", cfg.lean);
        let old = fs::read_to_string(&p).unwrap_or_default();
        if old != fin { fs::write(&p, &fin).unwrap(); o.changed.push("L5S5.FiveSpeedFinal".into()); }
        o.all.push(("L5S5.FiveSpeedFinal".into(), "final".into()));
    }
    // ---- aggregation controls (separate module, never imported by the final) ----
    {
        let mut pick: Option<(usize, usize, usize, usize, String)> = None; // k, c1, p1, c2, leafname
        'o: for n in &cfg.nodes {
            for c in n.first..n.first + n.size {
                if cfg.built.contains(&c) && cfg.built.contains(&(c + 1)) && c + 1 < n.first + n.size && (c - n.first) / 8 == (c + 1 - n.first) / 8 {
                    pick = Some((n.k, c, c - n.first, c + 1, format!("Leaf{}_{}", n.k, (c - n.first) / 8)));
                    break 'o;
                }
            }
        }
        if let Some((k, c1, p1, c2, leaf)) = pick {
            let t = format!(
"/-
# AggFive.Ctl : planted corruption controls at the aggregation level (generated by l5_agg; imported by NOTHING)

Real representatives #{c1} and #{c2} (adjacent positions {p1},{p2} of depth-1 node #{k}).  The true side conditions hold by `rfl`; a wrong offset, a missing
representative and a swapped link are rejected by `decide`; a planted `sorry` prints [sorryAx].  This module carries the only `sorry` of the aggregation.
-/
import LRSpectrumFull.AggFive.{leaf}

namespace LRSpectrumFull
namespace AggFive
namespace Ctl
open LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S5

theorem ok_offset : ({leaf}.r{c2}).pos0 = ({leaf}.r{c1}).pos0 + ({leaf}.r{c1}).size := rfl
theorem ctl_wrong_offset : ¬ (({leaf}.r{c2}).pos0 = ({leaf}.r{c1}).pos0 + ({leaf}.r{c1}).size + 1) := by decide
theorem ok_pair_size : (RBlock.append ({leaf}.r{c1}) ({leaf}.r{c2}) rfl).size = 2 := rfl
theorem ctl_missing_rep : ¬ ((RBlock.append ({leaf}.r{c1}) ({leaf}.r{c2}) rfl).size = 3) := by decide
theorem ctl_missing_rep2 : ¬ (({leaf}.r{c1}).size = 2) := by decide
theorem ok_link : N{c1}.nK.rows = X{k}.E {p1} := by decide +kernel
theorem ctl_swapped_link : ¬ (N{c1}.nK.rows = X{k}.E {p2}) := by decide +kernel
theorem ctl_swapped_link2 : ¬ (N{c2}.nK.rows = X{k}.E {p1}) := by decide +kernel
theorem ctl_sorry : (1 : ℕ) = 2 := by sorry

#print axioms ok_offset
#print axioms ctl_wrong_offset
#print axioms ctl_missing_rep
#print axioms ok_link
#print axioms ctl_swapped_link
#print axioms ctl_sorry

end Ctl
end AggFive
end LRSpectrumFull
", c1 = c1, c2 = c2, p1 = p1, p2 = p1 + 1, k = k, leaf = leaf);
            o.put("Ctl.lean", "AggFive.Ctl", "ctl", &t);
        }
    }
    // ---- manifest ----
    let sd = "/DEV_TREE/work/l5_agg/state";
    fs::create_dir_all(sd).unwrap();
    let mut m = String::from("module\tkind\n");
    for (a, b) in &o.all { m.push_str(&format!("{}\t{}\n", a, b)); }
    fs::write(format!("{}/modules.tsv", sd), m).unwrap();
    let mut h = String::from("node\tsize\tbuilt\tholes\n");
    for (k, s, b, hs) in &stat { h.push_str(&format!("{}\t{}\t{}\t{}\n", k, s, b, hs.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))); }
    fs::write(format!("{}/nodes.tsv", sd), h).unwrap();
    fs::write(format!("{}/changed.txt", sd), o.changed.join("\n") + "\n").unwrap();
    println!("generated {} modules, {} changed; built reps {} of {}; holes {}", o.all.len(), o.changed.len(), cfg.built.len(), NREP, nholes);
}

/// module order for building: clean, X, leaves, mids, roots, top, final, ctl
pub fn order(lean: &str) -> Vec<String> {
    let sd = "/DEV_TREE/work/l5_agg/state";
    let t = fs::read_to_string(format!("{}/modules.tsv", sd)).unwrap_or_default();
    let mut v: Vec<(usize, usize, String)> = vec![];
    for l in t.lines().skip(1) {
        let f: Vec<&str> = l.split('\t').collect();
        let (m, kind) = (f[0].to_string(), f[1]);
        let r = match kind { "base" => 0, "clean" => if m.ends_with("Pos") { 2 } else if m.ends_with("T2Final") { 3 } else { 1 }, "x" => 4, "leaf" => 5, "mid" => 6, "root" => 7, "top" => 8, "final" => 9, _ => 10 };
        // mids: by level so that lower levels first
        let sub = if kind == "mid" { m.split('_').nth(1).and_then(|x| x.parse().ok()).unwrap_or(0) } else { 0 };
        v.push((r, sub, m));
    }
    v.sort();
    let _ = lean;
    v.into_iter().map(|x| x.2).collect()
}

fn mtime(p: &str) -> Option<std::time::SystemTime> { fs::metadata(p).ok().and_then(|m| m.modified().ok()) }

/// modules whose olean is missing or older than the source / than an imported generated module
pub fn pending(lean: &str) -> Vec<String> {
    let ord = order(lean);
    let mut stale: BTreeSet<String> = BTreeSet::new();
    let mut out = vec![];
    for m in ord {
        let src = if m.starts_with("L5S5.") { format!("{}/LRSpectrumFull/{}.lean", lean, m.replace('.', "/")) } else { format!("{}/LRSpectrumFull/{}.lean", lean, m.replace('.', "/")) };
        let ol = format!("{}/.lake/build/lib/lean/LRSpectrumFull/{}.olean", lean, m.replace('.', "/"));
        let text = fs::read_to_string(&src).unwrap_or_default();
        let mut need = match (mtime(&src), mtime(&ol)) { (Some(s), Some(o)) => s > o, (_, None) => true, _ => true };
        for l in text.lines() {
            if let Some(r) = l.strip_prefix("import LRSpectrumFull.") {
                let im = r.trim();
                if stale.contains(im) { need = true; }
                let io = format!("{}/.lake/build/lib/lean/LRSpectrumFull/{}.olean", lean, im.replace('.', "/"));
                if let (Some(a), Some(b)) = (mtime(&ol), mtime(&io)) { if b > a && (im.starts_with("AggFive") || im.starts_with("L5S5")) { need = true; } }
            }
        }
        if need { stale.insert(m.clone()); out.push(m); }
    }
    out
}

pub fn status(a: &[String]) {
    // status <leanroot> <results.tsv> <rlstatus.tsv>
    let cfg = read_cfg(a);
    let mut tot_b = 0; let mut tot_e = 0;
    println!("node\texpected\tbuilt\tholes\tfirst_holes");
    for n in &cfg.nodes {
        let holes: Vec<usize> = (n.first..n.first + n.size).filter(|c| !cfg.built.contains(c)).collect();
        let b = n.size - holes.len();
        tot_b += b; tot_e += n.size;
        let hl: Vec<String> = holes.iter().take(6).map(|x| x.to_string()).collect();
        println!("{}\t{}\t{}\t{}\t{}{}", n.k, n.size, b, holes.len(), hl.join(","), if holes.len() > 6 { ",..." } else { "" });
    }
    println!("TOTAL\t{}\t{}\t{}", tot_e, tot_b, tot_e - tot_b);
    let mut by: BTreeMap<String, usize> = BTreeMap::new();
    for (_, (s, _)) in &cfg.results { *by.entry(s.clone()).or_default() += 1; }
    println!("rollout results.tsv statuses: {:?}", by);
    let p = pending(&cfg.lean);
    println!("generated modules pending a build (olean missing or stale): {}", p.len());
    for m in p.iter().take(12) { println!("  pending {}", m); }
}

/// leaves (module names) in node order until at least `n` built reps are covered
pub fn leaves(a: &[String]) {
    let cfg = read_cfg(&a[..3]);
    let n: usize = a[3].parse().unwrap();
    let mut cum = 0;
    for nd in &cfg.nodes {
        if nd.size == 0 { continue; }
        for j in 0..(nd.size + 7) / 8 {
            let reps = (j * 8..((j + 1) * 8).min(nd.size)).map(|i| nd.first + i);
            let b = reps.filter(|c| cfg.built.contains(c)).count();
            if b == 0 { continue; }
            cum += b;
            println!("AggFive.Leaf{}_{}", nd.k, j);
            if cum >= n { return; }
        }
    }
}
