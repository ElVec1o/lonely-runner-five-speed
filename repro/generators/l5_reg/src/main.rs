// l5reg: registration modules (H8) of the per-rep local class tables in the lines class table.
// usage: l5reg gen REP...        write L5Reg/Reg<REP>.lean for the given reps (advice (chunk, index) per local class, checked here too)
//        l5reg genbuilt          every rep whose GD3O<c>.olean exists and Reg<c>.lean is absent (or older flag FORCE=1)
//        l5reg mem               write L5Reg/Mem.lean (chunk j subset of LinRAll.blobs, all chunks of the plan)
//        l5reg table             print rep, nT, chunks, min gid, max gid, contiguous (no files written)
// Nothing here is trusted: the Lean kernel re-checks every row/range comparison (L5Reg.Base.regChk).
use std::collections::HashMap;
use std::env;
use std::fmt::Write as FW;
use std::fs;

const LEAN: &str = "/DEV_TREE/lean/LRSpectrumFull";
const BUILD: &str = "/DEV_TREE/lean/.lake/build/lib/lean/LRSpectrumFull";
const PLAN: &str = "/DEV_TREE/work/l5_lines_driver/plan.tsv";

fn digits(h: &str, upto: usize) -> Vec<i64> {
    // hex string without 0x ; digit k = chars [len-8(k+1), len-8k) ; bias 2^31
    let b = h.as_bytes(); let n = b.len(); let mut v = Vec::with_capacity(upto);
    for k in 0..upto {
        let end = n as i64 - 8 * k as i64;
        let raw: i64 = if end <= 0 { 0 } else {
            let s = (end - 8).max(0) as usize; let e = end as usize;
            i64::from_str_radix(std::str::from_utf8(&b[s..e]).unwrap(), 16).unwrap()
        };
        v.push(raw - 2147483648);
    }
    v
}

struct Chunk { first: usize, n: usize, name: String }

fn load_plan() -> Vec<Chunk> {
    let s = fs::read_to_string(PLAN).unwrap(); let mut v = vec![];
    for l in s.lines() {
        let f: Vec<&str> = l.split('\t').collect();
        let ids = f[6];
        let first: usize = ids.split(',').next().unwrap().parse().unwrap();
        let n: usize = f[3].parse().unwrap();
        v.push(Chunk { first, n, name: f[0].to_string() });
    }
    v
}

// record digits of a chunk: Vec<Vec<i64>> (digits 0..=60 and 61, ranges)
fn load_chunk(name: &str) -> Vec<Vec<i64>> {
    let p = format!("{}/L5S4/{}.lean", LEAN, name);
    let s = fs::read_to_string(&p).unwrap_or_else(|_| panic!("missing {}", p));
    let mut out = vec![];
    for l in s.lines() {
        if let Some(r) = l.strip_prefix("(0x") {
            let h: &str = r.split(',').next().unwrap();
            let d0 = digits(h, 64);
            let nr = d0[61].max(0) as usize;
            out.push(digits(h, 62 + 2 * nr + 2));
        }
    }
    out
}

struct Rep { tt: String, nt: usize, st: usize }

fn parse_rep(rep: usize) -> Rep {
    let p = format!("{}/L5S4/GD3O{}T.lean", LEAN, rep);
    let s = fs::read_to_string(&p).unwrap_or_else(|_| panic!("missing {}", p));
    let mut tt = String::new(); let mut nt = 0; let mut st = 0;
    for l in s.lines() {
        if let Some(r) = l.strip_prefix("def TT : ℕ := ") { let r = r.trim(); tt = if let Some(h) = r.strip_prefix("0x") { h.to_string() } else { assert!(r == "0"); String::new() }; }
        if let Some(r) = l.strip_prefix("def nT : ℕ := ") { nt = r.trim().parse().unwrap(); }
        if let Some(r) = l.strip_prefix("def ST : ℕ := ") { st = r.trim().parse().unwrap(); }
    }
    Rep { tt, nt, st }
}

// local id -> global id from the leaf records of the rep
fn rep_map(rep: usize) -> HashMap<i64, i64> {
    let mut m: HashMap<i64, i64> = HashMap::new();
    let mut files: Vec<String> = fs::read_dir(format!("{}/L5S4", LEAN)).unwrap()
        .filter_map(|e| e.ok()).map(|e| e.file_name().to_string_lossy().to_string())
        .filter(|n| n.starts_with(&format!("GD3O{}R", rep)) && n.ends_with(".lean") && n[format!("GD3O{}R", rep).len()..].chars().next().map_or(false, |c| c == 'c')).collect();
    files.sort();
    for f in files {
        let s = fs::read_to_string(format!("{}/L5S4/{}", LEAN, f)).unwrap();
        for l in s.lines() {
            let t = l.trim().trim_end_matches(',');
            if let Some(h) = t.strip_prefix("0x") {
                let d = digits(h, 98);
                if d[49] != 2 { continue; }
                assert!(d[96] == 0, "steps nonempty rep {}", rep);
                let loc = d[97]; let glob = d[50];
                if let Some(&g0) = m.get(&loc) { assert!(g0 == glob, "rep {} local {} maps to {} and {}", rep, loc, g0, glob); } else { m.insert(loc, glob); }
            }
        }
    }
    m
}

fn chunk_of(plan: &[Chunk], gid: usize) -> usize {
    // plan is in table order, ids contiguous
    let mut lo = 0; let mut hi = plan.len();
    while hi - lo > 1 { let mid = (lo + hi) / 2; if plan[mid].first <= gid { lo = mid } else { hi = mid } }
    lo
}

fn cname_idx(name: &str) -> usize { name.trim_start_matches("LinRQSC").parse().unwrap() }

fn rep_check(rp: &Rep, c: usize, rec: &[i64]) -> bool {
    let tg = digits(&rp.tt, rp.st * (c + 1) + 2);
    for k in 0..15 { if tg[rp.st * c + k] != rec[11 + k] { return false; } }
    let nl = tg[rp.st * c + 15].max(0) as usize; let ng = rec[61].max(0) as usize;
    for t in 0..nl {
        let lo = tg[rp.st * c + 16 + 2 * t]; let hi = tg[rp.st * c + 17 + 2 * t];
        let mut ok = false;
        for j in 0..ng { if rec[62 + 2 * j] <= lo && hi <= rec[63 + 2 * j] { ok = true; break; } }
        if !ok { return false; }
    }
    true
}

// rows of the lines record (digits 11..25) mapped by G (gp digits 1..5, ge digits 6..10): (G x)_a = e_a x_{p_a}; then row-HNF
fn glrows_raw(rec: &[i64]) -> Option<Vec<[i64; 5]>> {
    if rec.len() < 64 { return None; }
    let mut out = vec![];
    for i in 0..3 {
        let mut row = [0i64; 5];
        for a in 0..5 { let p = (rec[1 + a].rem_euclid(5)) as usize; row[a] = rec[6 + a] * rec[11 + 5 * i + p]; }
        out.push(row);
    }
    Some(out)
}
fn glrows(rec: &[i64]) -> Option<Vec<[i64; 5]>> {
    let raw = glrows_raw(rec)?; let h = hnf3(&raw); if h.is_empty() { None } else { Some(h) }
}
// M (row-major 3x3) with G l_i = sum_k M_ik rp_k, rp the local rows (15 digits); None if not in the lattice
fn solve_m(rp: &[i64], rec: &[i64]) -> Option<Vec<i64>> {
    let raw = glrows_raw(rec)?;
    let rows: Vec<[i64; 5]> = (0..3).map(|k| [rp[5 * k], rp[5 * k + 1], rp[5 * k + 2], rp[5 * k + 3], rp[5 * k + 4]]).collect();
    let pcs: Vec<usize> = rows.iter().map(|r| (0..5).find(|&c| r[c] != 0)).collect::<Option<Vec<_>>>()?;
    let mut m = vec![];
    for i in 0..3 {
        let mut x = raw[i]; let mut cs = [0i64; 3];
        for k in 0..3 {
            let piv = rows[k][pcs[k]];
            if x[pcs[k]] % piv != 0 { return None; }
            let c = x[pcs[k]] / piv; cs[k] = c;
            for a in 0..5 { x[a] -= c * rows[k][a]; }
        }
        if x.iter().any(|&v| v != 0) { return None; }
        m.extend_from_slice(&cs);
    }
    Some(m)
}

fn rep_check_rng(rp: &Rep, c: usize, rec: &[i64]) -> bool {
    let tg = digits(&rp.tt, rp.st * (c + 1) + 2);
    let nl = tg[rp.st * c + 15].max(0) as usize; let ng = rec[61].max(0) as usize;
    for t in 0..nl {
        let lo = tg[rp.st * c + 16 + 2 * t]; let hi = tg[rp.st * c + 17 + 2 * t];
        if !(0..ng).any(|j| rec[62 + 2 * j] <= lo && hi <= rec[63 + 2 * j]) { return false; }
    }
    true
}

struct Cache { plan: Vec<Chunk>, recs: Vec<Vec<i64>>, byrows: HashMap<Vec<i64>, Vec<usize>> }
impl Cache {
    fn load(&mut self) {
        if !self.recs.is_empty() { return; }
        let total: usize = self.plan.iter().map(|c| c.n).sum();
        self.recs = vec![vec![0; 128]; total];
        for ci in 0..self.plan.len() {
            if fs::metadata(format!("{}/L5S4/{}.lean", LEAN, self.plan[ci].name)).is_err() { eprintln!("chunk {} not emitted yet (skipped)", self.plan[ci].name); continue; }
            let r = load_chunk(&self.plan[ci].name);
            assert!(r.len() == self.plan[ci].n, "chunk {} has {} records, plan says {}", self.plan[ci].name, r.len(), self.plan[ci].n);
            for (k, rec) in r.into_iter().enumerate() {
                let g = self.plan[ci].first + k;
                assert!(rec[0] == g as i64, "chunk record cid {} != {}", rec[0], g);
                if let Some(h) = glrows(&rec) { self.byrows.entry(h.iter().flat_map(|x| x.iter().cloned()).collect()).or_default().push(g); }
                self.recs[g] = rec;
            }
        }
        eprintln!("loaded {} global records, {} distinct row triples", total, self.byrows.len());
    }
}

struct Adv { adv: Vec<(usize, usize, Vec<i64>)>, nt: usize, gmin: i64, gmax: i64, bad: usize }

fn advice(rep: usize, cache: &mut Cache) -> Adv {
    cache.load();
    let rp = parse_rep(rep);
    let mut adv = vec![]; let mut bad = 0; let mut gmin = i64::MAX; let mut gmax = -1;
    let tg = digits(&rp.tt, rp.st * rp.nt + 2);
    for c in 0..rp.nt {
        let key: Vec<i64> = tg[rp.st * c..rp.st * c + 15].to_vec();
        let mut found: Option<(usize, Vec<i64>)> = None;
        if let Some(cands) = cache.byrows.get(&key) { for &g in cands { if rep_check_rng(&rp, c, &cache.recs[g]) { if let Some(m) = solve_m(&tg[rp.st * c..rp.st * c + 15], &cache.recs[g]) { found = Some((g, m)); break; } } } }
        let (g, m) = match found { Some(x) => x, None => { bad += 1; (0, vec![0; 9]) } };
        gmin = gmin.min(g as i64); gmax = gmax.max(g as i64);
        let ci = chunk_of(&cache.plan, g); let k = g - cache.plan[ci].first;
        adv.push((cname_idx(&cache.plan[ci].name), k, m));
    }
    Adv { adv, nt: rp.nt, gmin, gmax, bad }
}

fn emit(rep: usize, a: &Adv) {
    let mut chunks: Vec<usize> = a.adv.iter().map(|x| x.0).collect(); chunks.sort(); chunks.dedup();
    let mut s = String::new();
    writeln!(s, "/-\n# L5Reg.Reg{rep} : the lines clause for every class of the local table of rep #{rep} (generated by l5reg)\n\nEvery local class `i < nT` of rep #{rep} ({} classes) is matched to the lines record `(chunk, index)` of `adv` with a 3x3 integer matrix `M` (UNTRUSTED advice): the kernel checks\n`G l'_i = sum_k M_ik l_k` (G from digits 1..10 of the record), the signed-permutation property of G, and that every local range lies in a record range (`L5Reg.Equiv.eqChk`).\nThe theorem takes, for each chunk used, the lines clause of the chunk's records (from `Lin.lines_clause_tab` via `L5Reg.Mem`).\nNo `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.\n-/", a.nt).unwrap();
    writeln!(s, "import LRSpectrumFull.L5Reg.Equiv\nimport LRSpectrumFull.L5S4.GD3O{rep}T").unwrap();
    for c in &chunks { writeln!(s, "import LRSpectrumFull.L5S4.LinRQSC{}", c).unwrap(); }
    writeln!(s, "\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5Reg\nnamespace R{rep}\nopen LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S4.Lin\n").unwrap();
    let bl: Vec<String> = chunks.iter().map(|c| format!("({}, LinRQSC{}.blobs)", c, c)).collect();
    writeln!(s, "def bls : List (ℕ × List (ℕ × ℕ)) := [{}]", bl.join(", ")).unwrap();
    let ad: Vec<String> = a.adv.iter().map(|x| format!("({}, {}, [{}])", x.0, x.1, x.2.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", "))).collect();
    writeln!(s, "def adv : List (ℕ × ℕ × List ℤ) := [{}]\n", ad.join(", ")).unwrap();
    writeln!(s, "theorem advOk : eqAll (LRSpectrumFull.L5S4.dg N{rep}.TT) N{rep}.ST (assoc bls) 0 adv = true := by decide +kernel\n").unwrap();
    writeln!(s, "theorem adv_len : adv.length = N{rep}.nT := by decide +kernel\n").unwrap();
    let hyps: Vec<String> = chunks.iter().map(|c| format!("(h{c} : ∀ p ∈ LinRQSC{c}.blobs, LinesCl t5 (t4OfRec p.1))")).collect();
    let hs = if chunks.is_empty() { "  intro e he; simp [bls] at he\n".to_string() } else {
        let pat: Vec<&str> = chunks.iter().map(|_| "rfl").collect();
        let mut t = String::from("  intro e he p hp\n  simp only [bls, List.mem_cons, List.mem_nil_iff, or_false] at he\n");
        if chunks.len() == 1 { writeln!(t, "  rcases he with rfl\n  exact h{} p hp", chunks[0]).unwrap(); }
        else {
            writeln!(t, "  rcases he with {}", pat.join(" | ")).unwrap();
            for c in &chunks { writeln!(t, "  · exact h{c} p hp").unwrap(); }
        }
        t
    };
    writeln!(s, "/-- the lines clause for every class of the local table of rep #{rep}. -/\ntheorem lines (t5 : List T5Rec) {}\n    : ∀ cl ∈ (List.range N{rep}.nT).map (t4At (LRSpectrumFull.L5S4.dg N{rep}.TT) N{rep}.ST), LinesCl t5 cl :=\n  linesLoc_of_adv t5 _ _ _ bls adv adv_len advOk (by\n{})\n", hyps.join(" "), hs).unwrap();
    writeln!(s, "#print axioms lines\n\nend R{rep}\nend L5Reg\nend LRSpectrumFull").unwrap();
    fs::create_dir_all(format!("{}/L5Reg", LEAN)).unwrap();
    fs::write(format!("{}/L5Reg/Reg{}.lean", LEAN, rep), s).unwrap();
}

// chunked emission (S4V): classes [i0, i0+len) of rep `rep` as module `RegP<rep>_<k>`, and the assembling module `Reg<rep>` (same statement `R<rep>.lines` as emit)
fn emit_chunked(rep: usize, a: &Adv, size: usize) {
    let parts: Vec<(usize, usize)> = (0..a.nt).step_by(size).map(|i0| (i0, size.min(a.nt - i0))).collect();
    let mut all_chunks: Vec<usize> = a.adv.iter().map(|x| x.0).collect(); all_chunks.sort(); all_chunks.dedup();
    for (k, &(i0, len)) in parts.iter().enumerate() {
        let sub = &a.adv[i0..i0 + len];
        let mut chunks: Vec<usize> = sub.iter().map(|x| x.0).collect(); chunks.sort(); chunks.dedup();
        let mut s = String::new();
        writeln!(s, "/-\n# L5Reg.RegP{rep}_{k} : part {k} of the lines clause of rep #{rep}: local classes {i0}..{} (generated by l5reg `genchunk`)\n\nSame check as `Reg<c>` (`L5Reg.Equiv.eqAll`, UNTRUSTED advice, kernel-checked) on a sub-range of classes, so that the kernel check stays small.\nNo `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.\n-/", i0 + len - 1).unwrap();
        writeln!(s, "import LRSpectrumFull.L5Reg.Equiv\nimport LRSpectrumFull.L5S4.GD3O{rep}T").unwrap();
        for c in &chunks { writeln!(s, "import LRSpectrumFull.L5S4.LinRQSC{}", c).unwrap(); }
        writeln!(s, "\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5Reg\nnamespace P{rep}_{k}\nopen LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S4.Lin\n").unwrap();
        let bl: Vec<String> = chunks.iter().map(|c| format!("({}, LinRQSC{}.blobs)", c, c)).collect();
        writeln!(s, "def bls : List (ℕ × List (ℕ × ℕ)) := [{}]", bl.join(", ")).unwrap();
        let ad: Vec<String> = sub.iter().map(|x| format!("({}, {}, [{}])", x.0, x.1, x.2.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", "))).collect();
        writeln!(s, "def adv : List (ℕ × ℕ × List ℤ) := [{}]\n", ad.join(", ")).unwrap();
        writeln!(s, "theorem advOk : eqAll (LRSpectrumFull.L5S4.dg N{rep}.TT) N{rep}.ST (assoc bls) {i0} adv = true := by decide +kernel\n").unwrap();
        writeln!(s, "theorem adv_len : adv.length = {len} := by decide +kernel\n").unwrap();
        let hyps: Vec<String> = chunks.iter().map(|c| format!("(h{c} : ∀ p ∈ LinRQSC{c}.blobs, LinesCl t5 (t4OfRec p.1))")).collect();
        let pat: Vec<&str> = chunks.iter().map(|_| "rfl").collect();
        let mut t = String::from("  have hbl : ∀ j, ∀ p ∈ assoc bls j, LinesCl t5 (t4OfRec p.1) := by\n    intro j p hp\n    obtain ⟨e, he, hpe⟩ := assoc_mem hp\n    simp only [bls, List.mem_cons, List.mem_nil_iff, or_false] at he\n");
        if chunks.len() == 1 { writeln!(t, "    rcases he with rfl\n    exact h{} p hpe", chunks[0]).unwrap(); }
        else {
            writeln!(t, "    rcases he with {}", pat.join(" | ")).unwrap();
            for c in &chunks { writeln!(t, "    · exact h{c} p hpe").unwrap(); }
        }
        writeln!(s, "/-- the lines clause for local classes {i0}..{} of rep #{rep}. -/\ntheorem lines (t5 : List T5Rec) {}\n    : ∀ c, {i0} ≤ c → c < {i0} + {len} → LinesCl t5 (t4At (LRSpectrumFull.L5S4.dg N{rep}.TT) N{rep}.ST c) := by\n  intro c h1 h2\n{}  refine eqAll_sound t5 _ _ (assoc bls) hbl adv {i0} advOk c h1 ?_\n  rw [adv_len]; exact h2\n", i0 + len - 1, hyps.join(" "), t).unwrap();
        writeln!(s, "#print axioms lines\n\nend P{rep}_{k}\nend L5Reg\nend LRSpectrumFull").unwrap();
        fs::write(format!("{}/L5Reg/RegP{}_{}.lean", LEAN, rep, k), s).unwrap();
    }
    // assembly
    let mut s = String::new();
    writeln!(s, "/-\n# L5Reg.Reg{rep} : the lines clause for every class of the local table of rep #{rep} (generated by l5reg `genchunk`, {} parts of at most {size} classes)\n\nAssembles `RegP{rep}_<k>`.  Same statement as the unchunked `Reg<c>`.\nNo `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.\n-/", parts.len()).unwrap();
    writeln!(s, "import LRSpectrumFull.L5Reg.Equiv\nimport LRSpectrumFull.L5S4.GD3O{rep}T").unwrap();
    for c in &all_chunks { writeln!(s, "import LRSpectrumFull.L5S4.LinRQSC{}", c).unwrap(); }
    for k in 0..parts.len() { writeln!(s, "import LRSpectrumFull.L5Reg.RegP{rep}_{k}").unwrap(); }
    writeln!(s, "\nnamespace LRSpectrumFull\nnamespace L5Reg\nnamespace R{rep}\nopen LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S4.Lin\n").unwrap();
    let hyps: Vec<String> = all_chunks.iter().map(|c| format!("(h{c} : ∀ p ∈ LinRQSC{c}.blobs, LinesCl t5 (t4OfRec p.1))")).collect();
    let mut t = String::new();
    let disj: Vec<String> = parts.iter().map(|&(i0, len)| format!("({i0} ≤ c ∧ c < {})", i0 + len)).collect();
    writeln!(t, "  intro cl hcl\n  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hcl\n  have hc' : c < N{rep}.nT := List.mem_range.1 hc\n  have hn : N{rep}.nT = {} := rfl\n  have hcase : {} := by omega\n  rcases hcase with {}", a.nt, disj.join(" ∨ "), vec!["h"; parts.len()].join(" | ")).unwrap();
    for (k, &(i0, len)) in parts.iter().enumerate() {
        let mut chunks: Vec<usize> = a.adv[i0..i0 + len].iter().map(|x| x.0).collect(); chunks.sort(); chunks.dedup();
        let args: Vec<String> = chunks.iter().map(|c| format!("h{c}")).collect();
        writeln!(t, "  · exact P{rep}_{k}.lines t5 {} c h.1 (by omega)", args.join(" ")).unwrap();
    }
    writeln!(s, "/-- the lines clause for every class of the local table of rep #{rep}. -/\ntheorem lines (t5 : List T5Rec) {}\n    : ∀ cl ∈ (List.range N{rep}.nT).map (t4At (LRSpectrumFull.L5S4.dg N{rep}.TT) N{rep}.ST), LinesCl t5 cl := by\n{}\n#print axioms lines\n\nend R{rep}\nend L5Reg\nend LRSpectrumFull", hyps.join(" "), t).unwrap();
    fs::write(format!("{}/L5Reg/Reg{}.lean", LEAN, rep), s).unwrap();
    println!("rep {} chunked: {} parts, {} classes, {} record chunks", rep, parts.len(), a.nt, all_chunks.len());
}

fn built_reps() -> Vec<usize> {
    let mut v: Vec<usize> = fs::read_dir(format!("{}/L5S4", BUILD)).unwrap().filter_map(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().to_string())
        .filter(|n| n.starts_with("GD3O") && n.ends_with(".olean"))
        .filter_map(|n| n["GD3O".len()..n.len() - 6].trim_start_matches('A').parse::<usize>().ok()).collect();
    v.sort(); v
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let mode = a.get(1).map(|s| s.as_str()).unwrap_or("");
    let mut cache = Cache { plan: load_plan(), recs: vec![], byrows: HashMap::new() };
    match mode {
        "gen" | "table" | "genbuilt" => {
            let reps: Vec<usize> = if mode == "genbuilt" { built_reps() } else { a[2..].iter().map(|x| x.parse().unwrap()).collect() };
            let force = env::var("FORCE").is_ok();
            let (mut ok, mut skipped, mut badreps, mut classes, mut contiguous) = (0, 0, 0, 0usize, 0);
            for r in reps {
                if mode == "genbuilt" && !force && fs::metadata(format!("{}/L5Reg/Reg{}.lean", LEAN, r)).is_ok() { skipped += 1; continue; }
                if fs::metadata(format!("{}/L5S4/GD3O{}T.lean", LEAN, r)).is_err() { eprintln!("rep {}: no GD3O{}T.lean (skipped)", r, r); continue; }
                let ad = advice(r, &mut cache);
                let gs: Vec<usize> = ad.adv.iter().map(|x| cache.plan[x.0].first + x.1).collect();
                let contig = gs.windows(2).all(|w| w[1] == w[0] + 1);
                if contig { contiguous += 1; }
                let nch = { let mut c: Vec<usize> = ad.adv.iter().map(|x| x.0).collect(); c.sort(); c.dedup(); c.len() };
                println!("rep\t{}\tnT\t{}\tchunks\t{}\tgmin\t{}\tgmax\t{}\tcontig\t{}\tbad\t{}", r, ad.nt, nch, if ad.nt == 0 { -1 } else { ad.gmin }, ad.gmax, contig, ad.bad);
                classes += ad.nt;
                if ad.bad > 0 { badreps += 1; eprintln!("rep {}: {} local classes FAIL the Rust row/range check (no module written)", r, ad.bad); continue; }
                if mode != "table" { emit(r, &ad); }
                ok += 1;
            }
            eprintln!("reps ok {} skipped {} bad {} ; local classes {} ; contiguous reps {}", ok, skipped, badreps, classes, contiguous);
        }
        "genchunk" => {
            // l5reg genchunk SIZE REP... : chunked Reg<REP> (parts RegP<REP>_<k> + assembly)
            let size: usize = a[2].parse().unwrap();
            for rs in &a[3..] {
                let r: usize = rs.parse().unwrap();
                let ad = advice(r, &mut cache);
                if ad.bad > 0 { eprintln!("rep {}: {} local classes FAIL the Rust check, nothing written", r, ad.bad); continue; }
                emit_chunked(r, &ad, size);
            }
        }
        "fin" => {
            // RegFin<g>: instantiate Reg<c>.lines with the global lines clause, for the reps listed in a.[3..] (group number a[2])
            let g: usize = a[2].parse().unwrap();
            let reps: Vec<usize> = a[3..].iter().map(|x| x.parse().unwrap()).collect();
            let mut s = String::new();
            writeln!(s, "/-\n# L5Reg.RegFin{g} : the lines clause for the local class tables of {} reps, from the global lines clause (generated by l5reg `fin`)\n\n`lines<c>` instantiates `L5Reg.R<c>.lines` with `FinalGlue.glines` (lines clause of every record of `LinRAll.blobs`) through `L5Reg.Mem`.\nNo `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.\n-/\nimport LRSpectrumFull.L5Reg.Mem\nimport LRSpectrumFull.L5S5.FinalGlue", reps.len()).unwrap();
            for r in &reps { writeln!(s, "import LRSpectrumFull.L5Reg.Reg{}", r).unwrap(); }
            writeln!(s, "\nnamespace LRSpectrumFull\nnamespace L5Reg\nopen LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S5\n").unwrap();
            for r in &reps {
                let src = fs::read_to_string(format!("{}/L5Reg/Reg{}.lean", LEAN, r)).unwrap();
                let chunks: Vec<String> = src.lines().filter_map(|l| l.strip_prefix("import LRSpectrumFull.L5S4.LinRQSC").map(|x| x.to_string())).collect();
                let args: Vec<String> = chunks.iter().map(|c| format!("(fun p hp => FinalGlue.glines p (mem{} p hp))", c)).collect();
                writeln!(s, "theorem lines{r} : ∀ cl ∈ (List.range N{r}.nT).map (t4At (LRSpectrumFull.L5S4.dg N{r}.TT) N{r}.ST), LinesCl T5Store.t5 cl :=\n  R{r}.lines T5Store.t5 {}\n", args.join(" ")).unwrap();
            }
            writeln!(s, "#print axioms lines{}\n\nend L5Reg\nend LRSpectrumFull", reps[0]).unwrap();
            fs::write(format!("{}/L5Reg/RegFin{}.lean", LEAN, g), s).unwrap();
        }
        "hnftest" => {
            cache.load();
            let mut idx: HashMap<Vec<i64>, Vec<usize>> = HashMap::new();
            for (g, r) in cache.recs.iter().enumerate() {
                if r.len() < 64 || r[0] != g as i64 { continue; }
                let rows: Vec<[i64; 5]> = (0..3).map(|i| [r[11 + 5 * i], r[12 + 5 * i], r[13 + 5 * i], r[14 + 5 * i], r[15 + 5 * i]]).collect();
                let h = hnf3(&rows);
                if h.is_empty() { continue; }
                idx.entry(h.iter().flat_map(|x| x.iter().cloned()).collect()).or_default().push(g);
            }
            eprintln!("hnf index: {} keys", idx.len());
            for rs in &a[2..] {
                let rep: usize = rs.parse().unwrap(); let rp = parse_rep(rep);
                let tg = digits(&rp.tt, rp.st * rp.nt + 2);
                let (mut hit, mut cov) = (0, 0);
                for c in 0..rp.nt {
                    let key: Vec<i64> = tg[rp.st * c..rp.st * c + 15].to_vec();
                    if let Some(cs) = idx.get(&key) { hit += 1; if cs.iter().any(|&g| rep_check_rng(&rp, c, &cache.recs[g])) { cov += 1; } }
                }
                println!("rep {} nT {} hnf-match {} range-covered {}", rep, rp.nt, hit, cov);
            }
        }
        "rec" => {
            cache.load();
            for s in &a[2..] { let g: usize = s.parse().unwrap(); let r = &cache.recs[g]; println!("cid {} gp {:?} ge {:?} l {:?} k {:?} nr {} lo {} hi {}", g, &r[1..6], &r[6..11], &r[11..26], &r[26..36], r[61], r[62], r[63]); }
        }
        "find" => {
            cache.load();
            let lo: i64 = a[2].parse().unwrap(); let hi: i64 = a[3].parse().unwrap();
            for (g, r) in cache.recs.iter().enumerate() {
                if r.len() < 64 { continue; }
                let nr = r[61].max(0) as usize;
                for j in 0..nr { if r.len() > 63 + 2 * j && r[62 + 2 * j] <= lo && hi <= r[63 + 2 * j] { println!("cid {} rows {:?} range {}:{} nr {}", g, &r[11..26], r[62 + 2 * j], r[63 + 2 * j], nr); break; } }
            }
        }
        "dbg" => {
            let rep: usize = a[2].parse().unwrap();
            let f = format!("{}/L5S4/GD3O{}Rc0.lean", LEAN, rep);
            let s = fs::read_to_string(&f).unwrap();
            for l in s.lines().take(400) {
                let t = l.trim().trim_end_matches(',');
                if let Some(h) = t.strip_prefix("0x") { let d = digits(h, 98); println!("kind {} d50 {} d51 {} d52 {} d96 {} d97 {}", d[49], d[50], d[51], d[52], d[96], d[97]); }
            }
        }
        "mem" => {
            let plan = &cache.plan; let n = plan.len(); let gsz = 32;
            let ng = (n + gsz - 1) / gsz;
            let mut s = String::new();
            writeln!(s, "/-\n# L5Reg.Mem : every chunk of the lines certificate is contained in `LinRAll.blobs` (generated by l5reg `mem`)\n\n`mem<j> : ∀ p ∈ LinRQSC<j>.blobs, p ∈ LinRAll.blobs`: chunk -> group (`LinRQSG<g>.blobs`, right-nested `++`) -> top (`LinRQSA.blobs`, right-nested `++`).\nNo `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.\n-/\nimport LRSpectrumFull.L5S4.LinRAll\n\nnamespace LRSpectrumFull\nnamespace L5Reg\nopen LRSpectrumFull.L5S4\n").unwrap();
            for g in 0..ng {
                let mut u = String::from("hp");
                if g < ng - 1 { u = format!("List.mem_append_left _ ({})", u); }
                for _ in 0..g { u = format!("List.mem_append_right _ ({})", u); }
                writeln!(s, "theorem memG{g} : ∀ p ∈ LinRQSG{g}.blobs, p ∈ LinRAll.blobs := fun p hp => by\n  unfold LinRAll.blobs LinRQSA.blobs\n  exact {}\n", u).unwrap();
            }
            for j in 0..n {
                let ci = cname_idx(&plan[j].name); let g = ci / gsz; let k = ci % gsz;
                let gn = if g == ng - 1 { n - gsz * g } else { gsz };
                let mut t = String::from("hp");
                if k < gn - 1 { t = format!("List.mem_append_left _ ({})", t); }
                for _ in 0..k { t = format!("List.mem_append_right _ ({})", t); }
                writeln!(s, "theorem mem{ci} : ∀ p ∈ LinRQSC{ci}.blobs, p ∈ LinRAll.blobs := fun p hp =>\n  memG{g} p (by unfold LinRQSG{g}.blobs; exact {})\n", t).unwrap();
            }
            writeln!(s, "#print axioms mem0\n#print axioms mem{}\n\nend L5Reg\nend LRSpectrumFull", n - 1).unwrap();
            fs::create_dir_all(format!("{}/L5Reg", LEAN)).unwrap();
            fs::write(format!("{}/L5Reg/Mem.lean", LEAN), s).unwrap();
            eprintln!("wrote Mem.lean for {} chunks, {} groups", n, ng);
        }
        _ => eprintln!("usage: l5reg gen REP.. | genbuilt | table REP.. | mem"),
    }
}

// canonical reduced row echelon (Hermite) form of 3 independent rows in Z^5 (copy of l5s4o::hnf3)
fn hnf3(rows: &[[i64; 5]]) -> Vec<[i64; 5]> {
    let mut m: Vec<[i64; 5]> = rows.to_vec();
    let mut r = 0usize; let mut pcs: Vec<usize> = vec![];
    for c in 0..5 {
        if r == 3 { break; }
        loop {
            let nz: Vec<usize> = (r..3).filter(|&i| m[i][c] != 0).collect();
            if nz.len() <= 1 { break; }
            let mut p = nz[0]; for &i in &nz { if m[i][c].abs() < m[p][c].abs() { p = i; } }
            for &i in &nz { if i != p { let q = m[i][c] / m[p][c]; let mp = m[p]; for k in 0..5 { m[i][k] -= q * mp[k]; } } }
        }
        let nz: Vec<usize> = (r..3).filter(|&i| m[i][c] != 0).collect();
        if nz.len() == 1 {
            m.swap(r, nz[0]);
            if m[r][c] < 0 { for k in 0..5 { m[r][k] = -m[r][k]; } }
            pcs.push(c); r += 1;
        }
    }
    if r < 3 { return vec![]; }
    for i in 0..3 { let pc = pcs[i]; let piv = m[i][pc]; for j in 0..i { let q = m[j][pc].div_euclid(piv); let mi = m[i]; for k in 0..5 { m[j][k] -= q * mi[k]; } } }
    m
}
