// l5s4o: class merging of the flat leaf records (S4O).  Reads flat per-record blob modules (GD3F2L<rep>R<j>.lean, def blobsF_<tag>),
// computes for every kind-2 record the signed-permutation class of its leaf lattice (wp0a::canon on qmat(b, adj)),
// the canonical class representative rows (row-HNF of G*cl, unique per lattice), the maps U, U' (integer, verified here),
// rewrites digits 53..95 of the record (gp, U, U', cl) and appends the class id as digit 97 (steps are empty, digit 96 = 0),
// and emits Lean data modules: table module GD3O<rep>T, chunk modules GD3O<rep>R<tag>, main module GD3O<rep>.
// usage: l5s4o REP OUTLEAN TSVDIR tag=path [tag=path ...]
use std::collections::HashMap;
use std::env;
use std::fmt::Write as FW;
use std::fs;
use wp0a::*;

fn right_inverse(h: &[V5]) -> Option<Vec<V5>> {
    let r = h.len(); let mut hm: Vec<Vec<I>> = h.iter().map(|x| x.to_vec()).collect();
    let mut u = ident(5);
    for i in 0..r {
        loop {
            let mut piv = usize::MAX;
            for c in i..5 { if hm[i][c] != 0 && (piv == usize::MAX || hm[i][c].abs() < hm[i][piv].abs()) { piv = c; } }
            if piv == usize::MAX { return None; }
            let mut any = false;
            for c in i..5 { if c != piv && hm[i][c] != 0 { let q = hm[i][c] / hm[i][piv]; for rr in 0..r { let v = hm[rr][piv]; hm[rr][c] -= q * v; } for rr in 0..5 { let v = u[rr][piv]; u[rr][c] -= q * v; } if hm[i][c] != 0 { any = true; } } }
            if !any { for rr in 0..r { hm[rr].swap(i, piv); } for rr in 0..5 { u[rr].swap(i, piv); } break; }
        }
        if hm[i][i].abs() != 1 { return None; }
    }
    let mut tinv = vec![vec![0 as I; r]; r];
    for col in 0..r { for i in 0..r { let mut s = if i == col { 1 } else { 0 }; for k in 0..i { s -= hm[i][k] * tinv[k][col]; } tinv[i][col] = s * hm[i][i]; } }
    let mut p: Vec<V5> = vec![];
    for j in 0..r { let mut col = [0 as I; 5]; for k in 0..r { for rr in 0..5 { col[rr] += u[rr][k] * tinv[k][j]; } } p.push(col); }
    for j in 0..r { for i in 0..r { if dot(&h[i], &p[j]) != if i == j { 1 } else { 0 } { return None; } } }
    Some(p)
}

// canonical reduced row echelon (Hermite) form of 3 independent rows in Z^5
fn hnf3(rows: &[V5]) -> Vec<V5> {
    let mut m: Vec<V5> = rows.to_vec();
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
    assert!(r == 3, "rank < 3");
    for i in 0..3 { let pc = pcs[i]; let piv = m[i][pc]; for j in 0..i { let q = m[j][pc].div_euclid(piv); let mi = m[i]; for k in 0..5 { m[j][k] -= q * mi[k]; } } }
    m
}

fn parse_blobs(path: &str, tag: &str) -> Vec<Vec<I>> {
    let src = fs::read_to_string(path).unwrap();
    let key = format!("def blobsF_{} : List ℕ := [", tag);
    let k = src.find(&key).expect("no blobs def");
    let rest = &src[k + key.len()..];
    let end = rest.find("\n]").expect("no end");
    let body = &rest[..end];
    let mut out = vec![];
    for line in body.lines() {
        let l = line.trim().trim_end_matches(',');
        if l.is_empty() { continue; }
        let h = l.trim_start_matches("0x");
        assert!(h.len() % 8 == 0);
        let len = h.len() / 8;
        let mut d = vec![0 as I; len];
        for i in 0..len { let a = (len - 1 - i) * 8; d[i] = i64::from_str_radix(&h[a..a + 8], 16).unwrap() as I - (1 << 31); }
        out.push(d);
    }
    out
}

fn hex_of(d: &[I]) -> String {
    if d.is_empty() { return "0".to_string(); }   // rollout fix: empty table (rep without kind-2 leaves) must not print the invalid literal `0x`
    let mut s = String::from("0x");
    for i in (0..d.len()).rev() { let v = d[i] + (1 << 31); assert!(v >= 0 && v < (1 << 32), "digit overflow {}", d[i]); write!(s, "{:08x}", v).unwrap(); }
    s
}
fn v5d(d: &[I], o: usize) -> V5 { [d[o], d[o + 1], d[o + 2], d[o + 3], d[o + 4]] }

// main-module name of a rep: the table l5_rollout/modname.tsv (rep TAB name) overrides the default GD3O<rep>.
// Only the MAIN module is renamed; the table module GD3O<rep>T and the chunk modules GD3O<rep>R<tag> keep their names (no collision).
fn main_name(rep: usize) -> String {
    let p = "/DEV_TREE/work/l5_rollout/modname.tsv";
    if let Ok(t) = fs::read_to_string(p) {
        for l in t.lines() {
            let f: Vec<&str> = l.split('\t').collect();
            if f.len() == 2 && f[0].trim().parse::<usize>().ok() == Some(rep) { return f[1].trim().to_string(); }
        }
    }
    format!("GD3O{}", rep)
}

struct Cls { rep: Vec<V5>, ranges: Vec<(I, I)>, members: usize }

fn main() {
    let a: Vec<String> = env::args().collect();
    let rep: usize = a[1].parse().unwrap();
    let outl = &a[2]; let tsvdir = &a[3];
    let perms = all_perms();
    let mut cls: Vec<Cls> = vec![]; let mut cmap: HashMap<Vec<V5>, usize> = HashMap::new();
    let mut keymap: HashMap<Vec<i64>, Vec<V5>> = HashMap::new();
    let mut chunks: Vec<(String, Vec<Vec<I>>)> = vec![];
    let (mut nk2, mut nk1, mut nother) = (0usize, 0usize, 0usize);
    for ta in &a[4..] {
        let (tag, path) = ta.split_once('=').unwrap();
        let mut recs = parse_blobs(path, tag);
        for d in recs.iter_mut() {
            assert!(d[96] == 0, "steps nonempty");
            assert!(d.len() == 97, "unexpected record length");
            let kind = d[49];
            if kind == 2 {
                nk2 += 1;
                let b0 = v5d(d, 8); let b1 = v5d(d, 13);
                let bb = vec![b0, b1];
                let gm = gram(&bb); let adj = adjm(&gm); let q = qmat(&bb, &adj);
                let (key, g) = canon(&[&q], &perms);
                let cl: Vec<V5> = (0..3).map(|i| v5d(d, 81 + 5 * i)).collect();
                let t: Vec<V5> = cl.iter().map(|x| g.apply(x)).collect();
                let rp = hnf3(&t);
                let srep = right_inverse(&rp).expect("rep not saturated");
                let st = right_inverse(&t).expect("t not saturated");
                let mut u = [[0 as I; 3]; 3]; let mut u2 = [[0 as I; 3]; 3];
                for i in 0..3 { for k in 0..3 { u[i][k] = dot(&t[i], &srep[k]); u2[i][k] = dot(&rp[i], &st[k]); } }
                for i in 0..3 { for c in 0..5 {
                    let mut s1 = 0; let mut s2 = 0;
                    for k in 0..3 { s1 += u[i][k] * rp[k][c]; s2 += u2[i][k] * t[k][c]; }
                    assert!(s1 == t[i][c] && s2 == rp[i][c], "map check failed");
                } }
                // key consistency: same canonical key must give same representative lattice
                match keymap.get(&key) { Some(r0) => assert!(*r0 == rp, "key -> lattice not injective/consistent"), None => { keymap.insert(key, rp.clone()); } }
                let (rlo, rhi) = (d[51], d[52]);
                assert!(rlo <= rhi, "kind 2 with empty range");
                let cid = match cmap.get(&rp) { Some(&c) => c, None => { let c = cls.len(); cmap.insert(rp.clone(), c); cls.push(Cls { rep: rp.clone(), ranges: vec![], members: 0 }); c } };
                cls[cid].ranges.push((rlo, rhi)); cls[cid].members += 1;
                for i in 0..5 { d[53 + i] = g.p[i] as I; d[58 + i] = g.e[i] as I; }
                for i in 0..3 { for k in 0..3 { d[63 + 3 * i + k] = u[i][k]; d[72 + 3 * i + k] = u2[i][k]; } }
                for i in 0..3 { for c in 0..5 { d[81 + 5 * i + c] = rp[i][c]; } }
                d.push(cid as I);
            } else if kind == 1 { nk1 += 1; d.push(0); } else { nother += 1; d.push(0); }
        }
        chunks.push((tag.to_string(), recs));
    }
    assert!(nother == 0, "kind 0 records present");
    assert!(keymap.len() == cls.len(), "canon key count {} != rep-lattice class count {}", keymap.len(), cls.len());
    // merge ranges
    let mut rmax = 1usize;
    for c in cls.iter_mut() {
        c.ranges.sort(); let mut m: Vec<(I, I)> = vec![];
        for &(lo, hi) in &c.ranges { if let Some(l) = m.last_mut() { if lo <= l.1 + 1 { if hi > l.1 { l.1 = hi; } continue; } } m.push((lo, hi)); }
        c.ranges = m; if c.ranges.len() > rmax { rmax = c.ranges.len(); }
    }
    let s = 16 + 2 * rmax;
    let mut tab: Vec<I> = vec![0; s * cls.len()];
    for (ci, c) in cls.iter().enumerate() {
        for i in 0..3 { for k in 0..5 { tab[s * ci + 5 * i + k] = c.rep[i][k]; } }
        tab[s * ci + 15] = c.ranges.len() as I;
        for (t, r) in c.ranges.iter().enumerate() { tab[s * ci + 16 + 2 * t] = r.0; tab[s * ci + 17 + 2 * t] = r.1; }
    }
    eprintln!("rep {}: records k2={} k1={} ; local classes {} ; max merged ranges {} ; stride {} ; table digits {}", rep, nk2, nk1, cls.len(), rmax, s, tab.len());
    // TSV of classes (rep rows, members, ranges)
    let mut tsv = String::new();
    for (ci, c) in cls.iter().enumerate() {
        let rows: Vec<String> = c.rep.iter().flat_map(|r| r.iter().map(|x| x.to_string())).collect();
        let rg: Vec<String> = c.ranges.iter().map(|r| format!("{}:{}", r.0, r.1)).collect();
        writeln!(tsv, "{}\t{}\t{}\t{}\t{}", rep, ci, c.members, rows.join(","), rg.join(";")).unwrap();
    }
    fs::write(format!("{}/classes_{}.tsv", tsvdir, rep), tsv).unwrap();
    let hdr = |name: &str, doc: &str, imps: &str| format!("/-\n# L5S4.{} : {} (S4O)\n\nNo `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.\n-/\n{}\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace N{}\nopen Matrix Finset LRSpectrumFull.L5S3\n\n", name, doc, imps, rep);
    let foot = "\nend N".to_string() + &rep.to_string() + "\nend L5S4\nend LRSpectrumFull\n";
    // table module (pads to at least one entry so that nT >= 1)
    let tname = format!("GD3O{}T", rep);
    let mut ts = hdr(&tname, &format!("local class table of rep #{} ({} classes, stride {})", rep, cls.len(), s), "import LRSpectrumFull.L5S4.GD3O1");
    writeln!(ts, "def TT : ℕ := {}\ndef nT : ℕ := {}\ndef ST : ℕ := {}\n", hex_of(&tab), cls.len(), s).unwrap();
    ts.push_str(&foot);
    fs::write(format!("{}/{}.lean", outl, tname), ts).unwrap();
    // chunk modules
    for (tag, recs) in &chunks {
        let name = format!("GD3O{}R{}", rep, tag);
        let mut cs = hdr(&name, &format!("class-mapped leaf records (chunk {}) with the T4 cover check of rep #{}", tag, rep), &format!("import LRSpectrumFull.L5S4.GD3F2N{}\nimport LRSpectrumFull.L5S4.GD3O{}T", rep, rep));
        writeln!(cs, "def blobsO_{} : List ℕ := [", tag).unwrap();
        for (i, d) in recs.iter().enumerate() { cs.push_str(&hex_of(d)); cs.push_str(if i + 1 < recs.len() { ",\n" } else { "\n" }); }
        cs.push_str("]\n\n");
        writeln!(cs, "theorem okO_{} : (blobsO_{}.all fun N => leafOkF (dg NN) (dg N) && t4F (dg TT) ST nT (dg N)) = true := by decide +kernel", tag, tag).unwrap();
        // leaf-only twin for pricing
        writeln!(cs, "\ntheorem okOL_{} : (blobsO_{}.all fun N => leafOkF (dg NN) (dg N)) = true := by decide +kernel", tag, tag).unwrap();
        cs.push_str(&foot);
        fs::write(format!("{}/{}.lean", outl, name), cs).unwrap();
    }
    // main module
    let name = main_name(rep);   // main-module name table (reps 1, 2 collide with S4O library modules GD3O1, GD3O2)
    let mut imps: String = chunks.iter().map(|(t, _)| format!("import LRSpectrumFull.L5S4.GD3O{}R{}\n", rep, t)).collect();
    // rollout fix: the main module always imports the node accessor, the local table, and (for node-split reps) the assembly GD3N<rep>Z
    imps.push_str(&format!("import LRSpectrumFull.L5S4.GD3F2N{}\nimport LRSpectrumFull.L5S4.GD3O{}T\n", rep, rep));
    if std::path::Path::new(&format!("{}/GD3N{}Z.lean", outl, rep)).exists() { imps.push_str(&format!("import LRSpectrumFull.L5S4.GD3N{}Z\n", rep)); }
    let mut ms = hdr(&name, &format!("`StreamHyp'.t3` for rep #{} with NO hypothesis: flat leaf checker + class-table cover (T4Cover) discharged for the local table", rep), &imps);
    let mut blobs_expr = chunks.iter().map(|(t, _)| format!("blobsO_{}", t)).collect::<Vec<_>>().join(" ++ ");
    if chunks.is_empty() { blobs_expr = "[]".to_string(); }
    let n = chunks.len();
    let mut rc = String::new();
    // case split over the appended lists (left-nested ++): (((a ++ b) ++ c) ++ d)
    let mut pat = String::from("h"); // build rcases pattern for left-nested mem_append
    if n == 1 { rc.push_str("  · exact (okcase_0 N hN)\n"); }
    else {
        pat = String::from("h0");
        for i in 1..n { pat = format!("({} | h{})", pat, i); }
        // outermost is ((h0 | h1) | h2) ...
        pat = pat.trim().to_string();
    }
    let mut cases = String::new();
    for (i, (t, _)) in chunks.iter().enumerate() { writeln!(cases, "  · have := List.all_eq_true.1 okO_{} N h{}; simpa [Bool.and_eq_true] using this", t, if n == 1 { 0 } else { i }).unwrap(); }
    let _ = rc;
    writeln!(ms, "def blobsO : List ℕ := {}\ndef recsO : List LeafRec := blobsO.map fun N => recOf (dg N)\n", blobs_expr).unwrap();
    writeln!(ms, "theorem alignO : storedOf cks = recsO.map LeafRec.t := by decide +kernel\n").unwrap();
    writeln!(ms, "theorem blobsO_ok : ∀ N ∈ blobsO, leafOkF (dg NN) (dg N) = true ∧ t4F (dg TT) ST nT (dg N) = true := by\n  intro N hN\n  simp only [blobsO, List.mem_append] at hN").unwrap();
    if n == 0 { writeln!(ms, "  simp [blobsO] at hN").unwrap(); }
    else if n == 1 { writeln!(ms, "  have h0 := hN").unwrap(); writeln!(ms, "  have := List.all_eq_true.1 okO_{} N h0\n  simpa [Bool.and_eq_true] using this", chunks[0].0).unwrap(); }
    else { writeln!(ms, "  rcases hN with {}", pat).unwrap(); ms.push_str(&cases); }
    writeln!(ms, "\ntheorem recsO_ok : ∀ r ∈ recsO, leafOk nK r = true := by\n  intro r hr\n  obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hr\n  exact leafOkF_sound nK (dg NN) (dg N) ag (blobsO_ok N hN).1\n").unwrap();
    writeln!(ms, "def tabO : List T4Rec := (List.range nT).map (t4At (dg TT) ST)\ndef Crep : Certificate := ⟨[], [], [], [], tabO, []⟩\n").unwrap();
    writeln!(ms, "theorem t4coverO : T4Cover Crep recsO := by\n  intro r hr hk0 hk1\n  obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hr\n  exact t4F_sound (dg TT) ST nT (dg N) (blobsO_ok N hN).2 hk0 hk1\n").unwrap();
    writeln!(ms, "/-- `StreamHyp'.t3` for rep #{} with NO hypothesis, for the local certificate `Crep`. -/\ntheorem t3_nodeU :\n    ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n3 : LeafW), (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧\n      n3.rows = setRow nK.rows 2 y' ∧ LeafRelW Crep n3 :=\n  fun y hy => t3_leaves Crep nK bn bd (by norm_num [bd]) hrad cks (by rw [fc_eq]; exact cov) (by rw [fc_eq]; exact allok)\n    recsO alignO recsO_ok t4coverO y hy\n", rep).unwrap();
    writeln!(ms, "/-- Lifting to any certificate whose table registers every local class (same rows, ranges covered). -/\ntheorem t3_nodeU_of (C : Certificate) (hsub : LocRegistered C tabO) :\n    ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n3 : LeafW), (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧\n      n3.rows = setRow nK.rows 2 y' ∧ LeafRelW C n3 := by\n  intro y hy\n  obtain ⟨y', n3, h1, h2, h3⟩ := t3_nodeU y hy\n  exact ⟨y', n3, h1, h2, leafRelW_of_registered hsub h3⟩\n\n#print axioms t3_nodeU\n#print axioms t3_nodeU_of").unwrap();
    ms.push_str(&foot);
    fs::write(format!("{}/{}.lean", outl, name), ms).unwrap();
}
