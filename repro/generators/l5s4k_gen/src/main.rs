// l5probe4: translate real chunks of the cert-v2 prototype (lean5_wp0a) into Lean packed-blob data modules.
// Exact i128 arithmetic only; reuses wp0a::* (lattice library) for the tree objects; everything that goes into Lean is
// an integer digit.  Mirror asserts (b_i.y = t_i, H P = I, G3 = t^T adj t, U/U' maps) run at generation time.
use std::collections::HashMap;
use std::fmt::Write as FW;
use std::fs;
use wp0a::*;

const OUT_LEAN: &str = "/DEV_TREE/lean/LRSpectrumFull/L5Probe4";
const OUT_DIR: &str = "/DEV_TREE/work/l5probe4/out";

fn mred(l: &[V5]) -> Vec<V5> { let mut v = l.to_vec(); pair_reduce(&mut v, None); v }

// ---- copied from lean5_wp0a/src/cert.rs (private there)
fn check_u(t: &[V5], b: &[V5], u: &Vec<Vec<I>>) -> bool {
    let r = t.len();
    for i in 0..r { for c in 0..5 { let mut s = 0; for k in 0..r { s += u[i][k] * b[k][c]; } if s != t[i][c] { return false; } } }
    true
}
fn solve_u(t: &[V5], b: &[V5]) -> Option<Vec<Vec<I>>> {
    let r = t.len();
    let gm: Vec<Vec<I>> = (0..r).map(|i| (0..r).map(|j| dot(&b[i], &b[j])).collect()).collect();
    let mx: Vec<Vec<I>> = (0..r).map(|i| (0..r).map(|j| dot(&t[i], &b[j])).collect()).collect();
    let d = det(&gm); let ad = adjm(&gm);
    let mut u = vec![vec![0 as I; r]; r];
    for i in 0..r { for j in 0..r { let mut s = 0; for k in 0..r { s += mx[i][k] * ad[k][j]; } if s % d != 0 { return None; } u[i][j] = s / d; } }
    if check_u(t, b, &u) { Some(u) } else { None }
}
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
fn d1_list() -> Vec<(V5, Node)> {
    let m0 = fr(3, 10); let b1 = fr(175, 27).div(fi(4).mul(m0).mul(m0)); let mut d1 = vec![];
    for a0 in 0..=4 { for a1 in a0..=4 { for a2 in a1..=4 { for a3 in a2..=4 { for a4 in a3..=4 {
        let h: V5 = [a0, a1, a2, a3, a4]; let ss: I = h.iter().map(|x| x * x).sum();
        if ss <= 1 { continue; } let mut g = 0; for &x in h.iter() { g = gcd(g, x); } if g != 1 { continue; }
        if !fi(ss).lt(b1) { continue; }
        d1.push((h, child(&root(), &h.to_vec())));
    } } } } }
    d1
}
fn d2_bound(n1: &Node, c1: Fr) -> Fr {
    let ms = [fr(3, 10), m_of(c1)]; let inv = [fi(0), fr(n1.gs[0], n1.gs[1])];
    radius_bound(&ms, &inv, 2, fr(37, 9), &[0, 1]).unwrap()
}
fn d3_bound(n2: &Node, c1: Fr, c2: Fr) -> Fr {
    let ms = [fr(3, 10), m_of(c1), m_of(c2)]; let inv = [fi(0), fr(n2.gs[0], n2.gs[1]), fr(n2.gs[1], n2.gs[2])];
    radius_bound(&ms, &inv, 3, fr(7, 3), &[0, 1, 2]).unwrap()
}
fn leaf_info(c: [Fr; 3], n3: &Node, c3: Fr, rho: Fr) -> (bool, Option<(I, I)>, bool) {
    let m3 = m_of(c3); let crit = m3.eq(fi(0));
    let ms = [fr(3, 10), m_of(c[0]), m_of(c[1]), m3];
    let w = leaf_window(&ms, &n3.gs, rho); let g3 = n3.gs[3];
    let ne = match w.hi { None => true, Some(h) => w.lo.lt(h) };
    if crit || !ne { return (ne, None, crit); }
    let hi = w.hi.unwrap();
    let (a, b) = (cdiv(w.lo.n * g3, w.lo.d), cdiv(hi.n * g3, hi.d) - 1);
    (ne, if a <= b { Some((a, b)) } else { None }, crit)
}
// own copy of the box iteration (rec_box is private in wp0a)
fn rec_box(i: usize, d: usize, tmax: &[I], t: &mut Vec<I>, started: bool, f: &mut dyn FnMut(&Vec<I>)) {
    if i == d { if started { f(t); } return; }
    let lo = if started { -tmax[i] } else { 0 };
    for v in lo..=tmax[i] { t[i] = v; rec_box(i + 1, d, tmax, t, started || v != 0, f); }
    t[i] = 0;
}

// ---- packing: digits of width 32 (biased by 2^31) or 64 (biased by 2^63)
#[derive(Clone)]
struct Dg { w: u32, v: Vec<u64> }
impl Dg {
    fn new(w: u32) -> Dg { Dg { w, v: vec![] } }
    fn put(&mut self, x: I) {
        let bias: I = 1 << (self.w - 1);
        assert!(x > -bias && x < bias, "digit overflow {} for width {}", x, self.w);
        self.v.push((x + bias) as u64);
    }
    fn v5(&mut self, v: &V5) { for i in 0..5 { self.put(v[i]); } }
    fn mat(&mut self, m: &Vec<Vec<I>>) { for r in m { for &x in r { self.put(x); } } }
    fn g(&mut self, g: &G) { for i in 0..5 { self.put(g.p[i] as I); } for i in 0..5 { self.put(g.e[i] as I); } }
}
fn hex_of(d: &[u64], w: u32) -> String {
    let nib = (w / 4) as usize; let mut s = String::new();
    for x in d.iter().rev() { write!(s, "{:0width$x}", x, width = nib).unwrap(); }
    let t = s.trim_start_matches('0'); if t.is_empty() { "0".into() } else { t.to_string() }
}
// concatenate records (each fixed length) into one blob number (record 0 = low digits)
fn blob(recs: &[Vec<u64>], w: u32) -> String { let mut all: Vec<u64> = vec![]; for r in recs { all.extend_from_slice(r); } hex_of(&all, w) }

struct Cls { crep: Vec<V5>, lo: I, hi: I, has: bool }
struct RepOut { hdr: Vec<u64>, recs: Vec<Vec<u64>> }

fn pad_rec(len: usize, w: u32, kind_digit: I) -> Vec<u64> { let mut d = Dg::new(w); d.put(kind_digit); for _ in 1..len { d.put(0); } d.v }
fn emit_rep_list(name: &str, reps: &Vec<RepOut>, rlen: usize, per_blob: usize, w: u32) -> String {
    let mut s = String::new();
    write!(s, "noncomputable def {} : List (Nat × List Nat) := [\n", name).unwrap();
    for (ri, r) in reps.iter().enumerate() {
        write!(s, "(0x{}, [", hex_of(&r.hdr, w)).unwrap();
        let mut first = true;
        for ch in r.recs.chunks(per_blob) {
            let mut v: Vec<Vec<u64>> = ch.to_vec(); while v.len() < per_blob { v.push(pad_rec(rlen, w, 3)); }
            if !first { s.push_str(", "); } first = false;
            write!(s, "0x{}", blob(&v, w)).unwrap();
        }
        s.push_str("])"); if ri + 1 < reps.len() { s.push_str(",\n"); }
    }
    s.push_str("\n]\n"); s
}
fn emit_tbl(name: &str, ents: &Vec<Vec<u64>>, per: usize, w: u32) -> String {
    let mut s = String::new(); write!(s, "noncomputable def {} : List Nat := [\n", name).unwrap();
    let nb = (ents.len() + per - 1) / per;
    for (bi, ch) in ents.chunks(per).enumerate() {
        write!(s, "0x{}", blob(ch, w)).unwrap(); if bi + 1 < nb { s.push_str(",\n"); }
    }
    s.push_str("\n]\n"); s
}
fn lean_file(path: &str, doc: &str, imports: &[&str], body: &str) {
    let mut s = String::new();
    write!(s, "/-\n{}\n-/\n", doc).unwrap();
    for i in imports { write!(s, "import {}\n", i).unwrap(); }
    s.push_str("\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace L5P4\n\n");
    s.push_str(body); s.push_str("\nend L5P4\n");
    fs::write(path, s).unwrap();
}

struct S2 { t: Vec<I>, n2: Node, x: V5, w: I, cls: usize, gn: G, c2: Fr }
struct C2 { hi: usize, n2: Node, g: G, c2: Fr, x: V5, w: I }

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let perms = all_perms(); let rho = fr(3, 4);
    let mut log = String::new();
    macro_rules! say { ($($a:tt)*) => {{ let l = format!($($a)*); println!("{}", l); log.push_str(&l); log.push('\n'); }} }
    let d1 = d1_list();
    // T1 witnesses
    let mut c1s: Vec<Fr> = vec![]; let mut w1: Vec<(V5, I)> = vec![];
    for (h, _) in &d1 { let (_, w) = mlat(&[*h], true); let w = w.unwrap(); c1s.push(witness_ok(&[*h], &w.x, w.w).unwrap()); w1.push((w.x, w.w)); }
    // T2 survivors and classes
    let mut cmap: HashMap<Vec<i64>, usize> = HashMap::new();
    let mut cls2: Vec<C2> = vec![]; let mut surv: Vec<Vec<S2>> = vec![]; let mut st2 = Funnel::default();
    for (hi, (h, n1)) in d1.iter().enumerate() {
        let mut q1 = [[0 as I; 5]; 5]; for i in 0..5 { for j in 0..5 { q1[i][j] = h[i] * h[j]; } }
        let bound = d2_bound(n1, c1s[hi]);
        let ts = children(n1, bound, &mut st2);
        let mut v = vec![];
        for t in ts {
            let n2 = child(n1, &t);
            let (_, w) = mlat(&mred(&n2.l), true); let w = w.unwrap(); let c2 = witness_ok(&n2.l, &w.x, w.w).unwrap();
            let q2 = qmat(&n2.b, &n2.adj); let (key, gn) = canon(&[&q1, &q2], &perms);
            let ci = match cmap.get(&key) { Some(&c) => c, None => { let c = cls2.len(); cmap.insert(key, c); cls2.push(C2 { hi, n2: n2.clone(), g: gn, c2, x: w.x, w: w.w }); c } };
            v.push(S2 { t, n2, x: w.x, w: w.w, cls: ci, gn, c2 });
        }
        surv.push(v);
    }
    say!("T1 {} reps; T2 survivors {} ; classes {}", d1.len(), surv.iter().map(|v| v.len()).sum::<usize>(), cls2.len());
    // ================= l5s4k: all-node depth-3 data pipeline
    // usage: l5s4k MODE REPS CHUNKPTS      MODE = stats | emit | rowsonly ; REPS = sel | comma list of class-rep ids ; CHUNKPTS = module budget (ball points)
    let nrep = cls2.len();
    let selected: Vec<usize> = (0..nrep).filter(|&ci| { let rp = &cls2[ci]; let n1 = &d1[rp.hi].1; fr(rp.n2.gs[2], rp.n2.gs[1]).lt(d2_bound(n1, c1s[rp.hi])) }).collect();
    say!("surviving class reps {} (expected 1965)", selected.len());
    let mode = args.get(1).cloned().unwrap_or("stats".to_string());
    let reps: Vec<usize> = match args.get(2).map(|s| s.as_str()) {
        None | Some("sel") => selected.clone(),
        Some(s) => s.split(',').filter(|x| !x.is_empty()).map(|x| x.parse().unwrap()).collect() };
    let chunk_pts: u64 = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(1700);
    let lean_dir = "/DEV_TREE/lean/LRSpectrumFull/L5S4";
    let ii = |x: I| if x < 0 { format!("({})", x) } else { format!("{}", x) };
    struct Row { t0: I, t1: I, lo: I, hi: I, pl: Vec<I>, ball: u64, kk: [u64; 4] }
    struct Ch { t0: I, t1s: I, nrows: usize, data: Vec<I>, ball: u64 }
    let mut tsv = String::from("ci\td1idx\tball\tcand\tpass\tgcdrej\tei\tgreedyrej\trows\tgroups\tmaxgroupball\tmods\tmaxmodball\n");
    let mut tot = [0u64; 8];
    for &ci in &reps {
        let rp = &cls2[ci]; let nd = &rp.n2; let bound = d3_bound(nd, c1s[rp.hi], rp.c2);
        let tmax: Vec<I> = (0..3).map(|i| isqrt(fdiv(bound.n * nd.a[i][i], bound.d))).collect();
        let g = nd.g(); let adj = &nd.adj;
        let fval = |t0: I, t1: I, t2: I| -> I { let t = [t0, t1, t2]; let mut qq = 0; for i in 0..3 { let mut s = 0; for j in 0..3 { s += adj[i][j] * t[j]; } qq += t[i] * s; } bound.n * g - bound.d * qq };
        let ps = |t0: I, t1: I, t2: I| -> I { // 0 pass, 1 gcd, 2 ei, 3 greedy
            let t = [t0, t1, t2]; let mut gg = 0; for &x in t.iter() { gg = gcd(gg, x); }
            if gg != 1 { 1 } else if ei_bad(nd, &t) { 2 } else if !greedy_ok(nd, &t) { 3 } else { 0 } };
        let mut rows: Vec<Row> = vec![];
        for t0 in 0..=tmax[0] {
            let t1lo = if t0 == 0 { 0 } else { -tmax[1] };
            for t1 in t1lo..=tmax[1] {
                let (flo, fhi) = if t0 == 0 && t1 == 0 { (1, tmax[2]) } else { (-tmax[2], tmax[2]) };
                let mut lo: Option<I> = None; let mut hi: Option<I> = None;
                for t2 in flo..=fhi { if fval(t0, t1, t2) > 0 { if lo.is_none() { lo = Some(t2); } hi = Some(t2); } }
                let mut pl: Vec<I> = vec![]; let mut kk = [0u64; 4]; let mut bl = 0u64;
                let (rlo, rhi) = match (lo, hi) {
                    (Some(a), Some(b)) => {
                        for t2 in a..=b { assert!(fval(t0, t1, t2) > 0); } assert!(fval(t0, t1, b + 1) <= 0); if !(t0 == 0 && t1 == 0) { assert!(fval(t0, t1, a - 1) <= 0); }
                        if t0 == 0 && t1 == 0 { assert_eq!(a, 1); }
                        if mode != "rowsonly" { for t2 in a..=b { bl += 1; let k = ps(t0, t1, t2) as usize; kk[k] += 1; if k == 0 { pl.push(t2); } } } else { bl = (b - a + 1) as u64; }
                        (a, b) }
                    _ => {
                        assert!(!(t0 == 0 && t1 == 0));
                        let mut m = 0 as I; let mut fm = fval(t0, t1, 0);
                        loop { let up = fval(t0, t1, m + 1); let dn = fval(t0, t1, m - 1); if up > fm { m += 1; fm = up; } else if dn > fm { m -= 1; fm = dn; } else { break; } }
                        assert!(fm <= 0);
                        (m, m - 1) }
                };
                rows.push(Row { t0, t1, lo: rlo, hi: rhi, pl, ball: bl, kk });
            }
        }
        let mut k4 = [0u64; 4]; let mut ball = 0u64; let mut groupball = vec![0u64; (tmax[0] + 1) as usize];
        for r in &rows { for z in 0..4 { k4[z] += r.kk[z]; } ball += r.ball; groupball[r.t0 as usize] += r.ball; }
        let maxg = *groupball.iter().max().unwrap();
        // modules of at most chunk_pts ball points (rows are never split), each a list of chunks (one t0 per chunk)
        let mut mods: Vec<Vec<Ch>> = vec![vec![]]; let mut modball = 0u64; let mut maxmod = 0u64;
        for r in &rows {
            if modball > 0 && modball + r.ball > chunk_pts { mods.push(vec![]); modball = 0; }
            let m = mods.last_mut().unwrap();
            let newch = match m.last() { Some(c) => c.t0 != r.t0, None => true };
            if newch { m.push(Ch { t0: r.t0, t1s: r.t1, nrows: 0, data: vec![], ball: 0 }); }
            let c = m.last_mut().unwrap();
            c.nrows += 1; c.ball += r.ball; c.data.push(r.t1); c.data.push(r.lo); c.data.push(r.hi); c.data.push(r.pl.len() as I);
            for &x in &r.pl { c.data.push(x); }
            modball += r.ball; if modball > maxmod { maxmod = modball; }
        }
        let nmods = mods.len();
        tsv.push_str(&format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n", ci, rp.hi, ball, k4[0] + k4[3], k4[0], k4[1], k4[2], k4[3], rows.len(), tmax[0] + 1, maxg, nmods, maxmod));
        tot[0] += ball; tot[1] += k4[0] + k4[3]; tot[2] += k4[0]; tot[3] += rows.len() as u64; tot[4] += nmods as u64; tot[5] += 1;
        if mode == "leaves" {
            let rho = fr(3, 4);
            let c1 = c1s[rp.hi]; let c2 = rp.c2;
            let mut stream: Vec<I> = vec![]; let mut cnt = 0usize; let mut kinds = [0usize; 3];
            for r in &rows { for &t2 in &r.pl {
                let t = vec![r.t0, r.t1, t2];
                let n3 = child(nd, &t); let y = lift(nd, &t);
                assert_eq!(n3.l[2], y);
                let (_, w) = mlat(&mred(&n3.l), true); let w = w.unwrap();
                let c3 = witness_ok(&n3.l, &w.x, w.w).unwrap();
                let m3 = m_of(c3); let crit = m3.eq(fi(0));
                assert!(!crit, "critical leaf at node {}: not supported by this generator", ci);
                let ms = [fr(3, 10), m_of(c1), m_of(c2), m3];
                let wn = leaf_window(&ms, &n3.gs, rho); let g3 = n3.gs[3];
                let hi = wn.hi.unwrap();
                let e = cdiv(hi.n * g3, hi.d); let a = cdiv(wn.lo.n * g3, wn.lo.d);
                let (kind, rlo, rhi): (usize, I, I) = if a > e - 1 { (1, e, e - 1) } else { (2, a, e - 1) };
                kinds[kind] += 1; cnt += 1;
                let s = right_inverse(&n3.l).expect("saturation functionals");
                assert_eq!(n3.b.len(), 2); assert_eq!(n3.r.len(), 2); assert_eq!(s.len(), 3);
                stream.extend_from_slice(&t); stream.extend_from_slice(&y);
                for v in &n3.b { stream.extend_from_slice(v); } for v in &n3.r { stream.extend_from_slice(v); }
                for v in &s { stream.extend_from_slice(v); }
                stream.extend_from_slice(&w.x); stream.push(w.w); stream.push(kind as I); stream.push(0); stream.push(rlo); stream.push(rhi);
                for i in 0..5 { stream.push(i as I); } for _ in 0..5 { stream.push(1); }
                for _ in 0..2 { stream.extend_from_slice(&[1, 0, 0, 0, 1, 0, 0, 0, 1]); }
                for v in &n3.l { stream.extend_from_slice(v); }
                stream.push(0);
            } }
            let mxabs = stream.iter().map(|x| x.abs()).max().unwrap_or(0);
            let dgw: u32 = if mxabs < 32767 { 16 } else { 32 };
            let (unp, imp2) = if dgw == 16 { ("unpackL", "") } else { ("unpackL32", "\nimport LRSpectrumFull.L5S4.GD3K6") };
            let mut dg = Dg::new(dgw); for &x in &stream { dg.put(x); }
            let single = nmods == 1;
            let top = if single { format!("LRSpectrumFull.L5S4.GD3N{}", ci) } else { format!("LRSpectrumFull.L5S4.GD3N{}Z", ci) };
            let s = format!("/-\n# L5S4.GD3L{ci} : leaf records of the depth-3 children of rep #{ci} and the `t3` clause of the node (stage S4 block 11)\nGenerated by l5s4k_gen leaves.  {cnt} leaves (kind 1 empty window {k1}, kind 2 window with SELF class (identity map, class rows = own rows; the stored class table is not part of this block) {k2}).\n-/\nimport {top}\nimport LRSpectrumFull.L5S4.GD3K4\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace N{ci}\nopen Matrix Finset LRSpectrumFull.L5S3\n\ndef leafData : List ℤ := unpackL 0x{hex} {len}\ndef recs : List LeafRec := parseAll {cnt} leafData\n\ntheorem align : storedOf cks = recs.map LeafRec.t := by decide +kernel\n\ntheorem recs_ok : ∀ r ∈ recs, leafOk nK r = true := by decide +kernel\n\n/-- `StreamHyp'.t3` for rep #{ci}: conditional only on the class-table obligation `T4Cover`. -/\ntheorem t3_node (C : Certificate) (hT4 : T4Cover C recs) :\n    ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n3 : LeafW), (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧\n      n3.rows = setRow nK.rows 2 y' ∧ LeafRelW C n3 :=\n  fun y hy => t3_leaves C nK bn bd (by norm_num [bd]) hrad cks (by rw [fc_eq]; exact cov) (by rw [fc_eq]; exact allok)\n    recs align recs_ok hT4 y hy\n\nend N{ci}\nend L5S4\nend LRSpectrumFull\n", ci = ci, cnt = cnt, k1 = kinds[1], k2 = kinds[2], top = top, hex = hex_of(&dg.v, 16), len = dg.v.len());
            let _ = s;
            if args.get(4).map(|s| s.as_str()) == Some("v2") {
                // layout v2: per-chunk data blobs (no quadratic unpack), R_j (data + check), A (recs := concat, align), main (recs_ok, t3_node)
                let rl = 97usize; let pr: usize = args.get(5).map(|s| s.parse().unwrap()).unwrap_or(64); let nch = (cnt + pr - 1) / pr;
                assert_eq!(stream.len(), cnt * rl);
                let hdr2 = |name: &str, doc: &str, imps: &str| format!("/-\n# L5S4.{name} : {doc} (rep #{ci}; generated by l5s4k_gen leaves v2, S4 block 13)\n-/\n{imps}\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace N{ci}\nopen Matrix Finset LRSpectrumFull.L5S3\n\n", name = name, doc = doc, imps = imps, ci = ci);
                let ftr2 = format!("\nend N{}\nend L5S4\nend LRSpectrumFull\n", ci);
                let wr2 = |name: &str, body: String| fs::write(format!("{}/{}.lean", lean_dir, name), body).unwrap();
                for j in 0..nch {
                    let lo = j * pr * rl; let hi = ((j + 1) * pr * rl).min(stream.len());
                    let mut dj = Dg::new(dgw); for &x in &stream[lo..hi] { dj.put(x); }
                    let nj = (hi - lo) / rl;
                    let nm = format!("GD3L{}R{}", ci, j);
                    wr2(&nm, format!("{}def blob_{j} : List ℤ := {unp} 0x{hx} {ln}\ndef recsC_{j} : List LeafRec := parseAll {nj} blob_{j}\n\ntheorem rec_chunk_{j} : ∀ r ∈ recsC_{j}, leafOk nK r = true := by decide +kernel\n{ftr}", hdr2(&nm, "one chunk of leaf records (data and check)", &format!("import {}\nimport LRSpectrumFull.L5S4.GD3K4\nimport LRSpectrumFull.L5S4.GD3K6", top)), j = j, unp = unp, hx = hex_of(&dj.v, dgw), ln = dj.v.len(), nj = nj, ftr = ftr2));
                }
                let mut ia = String::new(); for j in 0..nch { ia.push_str(&format!("import LRSpectrumFull.L5S4.GD3L{}R{}\n", ci, j)); }
                if nch == 0 { ia = format!("import {}\nimport LRSpectrumFull.L5S4.GD3K4\n", top); }
                let mut cat = String::new(); for j in 0..nch { cat.push_str(&format!("recsC_{} ++ ", j)); } cat.push_str("[]");
                let nmA = format!("GD3L{}A", ci);
                wr2(&nmA, format!("{}def recs : List LeafRec := {}\n\ntheorem align : storedOf cks = recs.map LeafRec.t := by decide +kernel\n{}", hdr2(&nmA, "concatenated records and alignment with the chunk list", &ia), cat, ftr2));
                let mut pat: Vec<String> = vec![]; for _ in 0..nch { pat.push("h".to_string()); } pat.push("h".to_string());
                let mut cases = String::new(); for j in 0..nch { cases.push_str(&format!("  · exact rec_chunk_{} r h\n", j)); }
                let nmM = format!("GD3L{}", ci);
                wr2(&nmM, format!("{}theorem recs_ok : ∀ r ∈ recs, leafOk nK r = true := by\n{}\n/-- `StreamHyp'.t3` for rep #{}: conditional only on the class-table obligation `T4Cover`. -/\ntheorem t3_node (C : Certificate) (hT4 : T4Cover C recs) :\n    ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n3 : LeafW), (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧\n      n3.rows = setRow nK.rows 2 y' ∧ LeafRelW C n3 :=\n  fun y hy => t3_leaves C nK bn bd (by norm_num [bd]) hrad cks (by rw [fc_eq]; exact cov) (by rw [fc_eq]; exact allok)\n    recs align recs_ok hT4 y hy\n{}", hdr2(&nmM, "leaf records of the depth-3 children and the `t3` clause of the node", &format!("import LRSpectrumFull.L5S4.GD3L{}A", ci)), if nch == 0 { "  intro r hr\n  simp [recs] at hr".to_string() } else if nch == 1 { "  intro r hr\n  simp only [recs, List.mem_append, List.not_mem_nil, or_false] at hr\n  exact rec_chunk_0 r hr".to_string() } else { format!("  intro r hr\n  simp only [recs, List.mem_append, List.not_mem_nil, or_false] at hr\n  rcases hr with {}\n{}", { let mut p = "h".to_string(); for _ in 1..nch { p = format!("({} | h)", p); } p }, cases) }, ci, ftr2));
                say!("LEAVES v2 rep {} count {} kind1 {} kind2 {} chunks {} width {}", ci, cnt, kinds[1], kinds[2], nch, dgw);
                continue;
            }
            // S4 block 13 layout: D (data) / A (align) / R_j (64 records each) / main (t3_node); width-adaptive digits
            let pr = 64usize; let nch = (cnt + pr - 1) / pr;
            let hdr = |name: &str, doc: &str, imps: &str| format!("/-\n# L5S4.{name} : {doc} (rep #{ci}; generated by l5s4k_gen leaves, S4 block 13)\n-/\n{imps}\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace N{ci}\nopen Matrix Finset LRSpectrumFull.L5S3\n\n", name = name, doc = doc, imps = imps, ci = ci);
            let ftr = format!("\nend N{}\nend L5S4\nend LRSpectrumFull\n", ci);
            let wr = |name: &str, body: String| fs::write(format!("{}/{}.lean", lean_dir, name), body).unwrap();
            wr(&format!("GD3L{}D", ci), format!("{}def leafData : List ℤ := {} 0x{} {}\ndef recs : List LeafRec := parseAll {} leafData\n{}", hdr(&format!("GD3L{}D", ci), "leaf record data", &format!("import {}\nimport LRSpectrumFull.L5S4.GD3K4{}\nimport LRSpectrumFull.L5S4.GD3K6", top, imp2)), unp, hex_of(&dg.v, dgw), dg.v.len(), cnt, ftr));
            wr(&format!("GD3L{}A", ci), format!("{}theorem align : storedOf cks = recs.map LeafRec.t := by decide +kernel\n{}", hdr(&format!("GD3L{}A", ci), "alignment of the stored list with the chunk list", &format!("import LRSpectrumFull.L5S4.GD3L{}D", ci)), ftr));
            for j in 0..nch { wr(&format!("GD3L{}R{}", ci, j), format!("{}theorem rec_chunk_{} : ∀ r ∈ (recs.drop ({} * {})).take {}, leafOk nK r = true := by decide +kernel\n{}", hdr(&format!("GD3L{}R{}", ci, j), "one chunk of leaf records", &format!("import LRSpectrumFull.L5S4.GD3L{}D", ci)), j, j, pr, pr, ftr)); }
            let mut imps = format!("import LRSpectrumFull.L5S4.GD3L{}A", ci); for j in 0..nch { imps.push_str(&format!("\nimport LRSpectrumFull.L5S4.GD3L{}R{}", ci, j)); }
            let mut cases = String::new(); for j in 0..nch { cases.push_str(&format!("  · exact rec_chunk_{}\n", j)); }
            let body = format!("{}theorem recs_ok : ∀ r ∈ recs, leafOk nK r = true := by\n  refine forall_of_chunks _ recs {} {} (by norm_num) (by unfold recs; rw [parseAll_length]; omega) ?_\n  intro j hj\n  interval_cases j\n{}\n/-- `StreamHyp'.t3` for rep #{}: conditional only on the class-table obligation `T4Cover`. -/\ntheorem t3_node (C : Certificate) (hT4 : T4Cover C recs) :\n    ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n3 : LeafW), (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧\n      n3.rows = setRow nK.rows 2 y' ∧ LeafRelW C n3 :=\n  fun y hy => t3_leaves C nK bn bd (by norm_num [bd]) hrad cks (by rw [fc_eq]; exact cov) (by rw [fc_eq]; exact allok)\n    recs align recs_ok hT4 y hy\n{}", hdr(&format!("GD3L{}", ci), "leaf records of the depth-3 children and the `t3` clause of the node", &imps), pr, nch, cases, ci, ftr);
            wr(&format!("GD3L{}", ci), body);
            say!("LEAVES rep {} count {} kind1 {} kind2 {} digits {}", ci, cnt, kinds[1], kinds[2], dg.v.len());
            continue;
        }
        if mode != "emit" { continue; }
        // ---- emit Lean modules
        let mut flds: Vec<I> = vec![]; flds.extend_from_slice(&nd.l[0]); flds.extend_from_slice(&nd.l[1]);
        for i in 0..3 { flds.extend_from_slice(&nd.b[i]); } for i in 0..3 { flds.extend_from_slice(&nd.r[i]); }
        flds.extend_from_slice(&[adj[0][0], adj[0][1], adj[0][2], adj[1][1], adj[1][2], adj[2][2], g, bound.n, bound.d, tmax[0], tmax[1], tmax[2]]);
        let fc = format!("⟨{}⟩", flds.iter().map(|&x| ii(x)).collect::<Vec<_>>().join(", "));
        let n1 = &d1[rp.hi].1; let _ = n1;
        let t: Vec<I> = (0..4).map(|i| dot(&d1[rp.hi].1.b[i], &nd.l[1])).collect();
        let mut f: Vec<I> = vec![]; f.extend(t.iter()); f.extend(nd.l[1].iter());
        for k in 0..3 { f.extend(nd.b[k].iter()); } for k in 0..3 { f.extend(nd.r[k].iter()); }
        f.extend(rp.x.iter()); f.push(rp.w);
        assert_eq!(f.len(), 45);
        let recl = f.iter().map(|&x| ii(x)).collect::<Vec<_>>().join(", ");
        let hdr = |name: &str, doc: &str, imp: &str| format!("/-\n# L5S4.{} : {}\nGenerated by l5s4k_gen (stage S4 block 11).  Rep #{} of 1965, depth-1 index {}, ball {} pass {} candidates {}.\n-/\nimport {}\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace N{}\nopen Matrix Finset LRSpectrumFull.L5S3\n\n", name, doc, ci, rp.hi, ball, k4[0], k4[0] + k4[3], imp, ci);
        let foot = "\nend N{}\nend L5S4\nend LRSpectrumFull\n";
        let chunk_text = |m: usize, mm: &Vec<Ch>| -> String {
            let mut s = String::new();
            for (j, c) in mm.iter().enumerate() {
                let mut dg = Dg::new(16); for &x in &c.data { dg.put(x); }
                s.push_str(&format!("def ck_{}_{} : Chunk := ({}, {}, {}, unpackL 0x{} {})\n", m, j, ii(c.t0), ii(c.t1s), c.nrows, hex_of(&dg.v, 16), dg.v.len()));
                s.push_str(&format!("theorem ok_{}_{} : rowsOk fc ck_{}_{}.1 ck_{}_{}.2.2.1 ck_{}_{}.2.1 ck_{}_{}.2.2.2 = true := by decide +kernel\n\n", m, j, m, j, m, j, m, j, m, j));
            }
            s };
        let assembly = || -> String {
            let mut s = String::new();
            let names: Vec<String> = mods.iter().enumerate().flat_map(|(m, mm)| (0..mm.len()).map(move |j| format!("ck_{}_{}", m, j))).collect();
            s.push_str(&format!("abbrev cks : List Chunk := [{}]\n\n", names.join(", ")));
            s.push_str("theorem cov : coverOk fc cks = true := by decide +kernel\n\n");
            let oks: Vec<String> = names.iter().map(|n| n.replace("ck_", "ok_")).collect();
            s.push_str(&format!("theorem allok : AllOk fc cks := ⟨{}, trivial⟩\n\n", oks.join(", ")));
            s.push_str("theorem t3 : ∀ y : V5, ChildPass nK y → ∃ e ∈ storedOf cks, e = (tvec nK.b y 0, tvec nK.b y 1, tvec nK.b y 2) :=\n  fun y hy => child_list_complete3k nK bn bd (by norm_num [bd]) hrad cks (by rw [fc_eq]; exact cov) (by rw [fc_eq]; exact allok) y hy\n");
            s };
        // module 0: node data, chunks of module 0, and (single-module node) the assembly
        let mut s0 = hdr(&format!("GD3N{}", ci), "node data and the depth-3 child list of one representative", "LRSpectrumFull.L5S4.GD3K2");
        s0.push_str(&format!("def recd : List ℤ := [{}]\ndef r1 : D1Raw := d1Data.getD {} badB.default_d1\ntheorem r1_ok : r1.ok := by decide +kernel\nnoncomputable def nD : NodeW 1 4 := nodeOfRaw r1 r1_ok\ntheorem rec_facts : RecFacts nD recd := by decide +kernel\nnoncomputable def nK : NodeW 2 3 := nodeOf2 nD recd rec_facts\ndef bn : ℤ := {}\ndef bd : ℤ := {}\ndef fc : FC3 := {}\ntheorem fc_eq : FC3.ofNode nK bn bd = fc := by decide +kernel\ntheorem hrad : radFrac (Cq (2 + 1)) nK.wit nK.rows 2 nK.rk = (bn : ℚ) / bd :=\n  hrad_of_ok nK bn bd (by decide +kernel)\n\n", recl, rp.hi, ii(bound.n), ii(bound.d), fc));
        s0.push_str(&chunk_text(0, &mods[0]));
        if nmods == 1 { s0.push_str(&assembly()); }
        s0.push_str(&foot.replace("{}", &ci.to_string()));
        fs::write(format!("{}/GD3N{}.lean", lean_dir, ci), s0).unwrap();
        if nmods > 1 {
            for m in 1..nmods {
                let mut s = hdr(&format!("GD3N{}M{}", ci, m), &format!("chunk module {}", m), &format!("LRSpectrumFull.L5S4.GD3N{}", ci));
                s.push_str(&chunk_text(m, &mods[m]));
                s.push_str(&foot.replace("{}", &ci.to_string()));
                fs::write(format!("{}/GD3N{}M{}.lean", lean_dir, ci, m), s).unwrap();
            }
            let imps: Vec<String> = (1..nmods).map(|m| format!("LRSpectrumFull.L5S4.GD3N{}M{}", ci, m)).collect();
            let mut s = hdr(&format!("GD3N{}Z", ci), "assembly of the chunks", &imps.join("\nimport "));
            s.push_str(&assembly());
            s.push_str(&foot.replace("{}", &ci.to_string()));
            fs::write(format!("{}/GD3N{}Z.lean", lean_dir, ci), s).unwrap();
        }
        say!("EMITTED rep {} d1idx {} ball {} pass {} mods {}", ci, rp.hi, ball, k4[0], nmods);
    }
    say!("TOTAL reps {} ball {} greedy-cand {} pass {} rows {} modules {}", tot[5], tot[0], tot[1], tot[2], tot[3], tot[4]);
    fs::write(format!("/DEV_TREE/logs/l5s4k/stats_{}.tsv", mode), &tsv).unwrap();
    fs::write("/DEV_TREE/logs/l5s4k/gen.log", &log).unwrap();
}
