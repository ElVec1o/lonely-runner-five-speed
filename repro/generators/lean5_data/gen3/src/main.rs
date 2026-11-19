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
    let old_mode = std::env::var("L5D_OLD").is_ok();
    if old_mode { radius_bound(&ms, &inv, 3, fr(7, 3), &[2]).unwrap() } else { radius_bound(&ms, &inv, 3, fr(7, 3), &[0, 1, 2]).unwrap() }
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


// ---- v3 helpers
fn wmin_v(x: &V5, w: I) -> I { x.iter().map(|&c| { let r = c.rem_euclid(w); r.min(w - r) }).min().unwrap() }
fn dec_of_u32(d: &[u32]) -> String {
    let mut a: Vec<u32> = d.to_vec(); let mut out: Vec<u32> = vec![];
    while a.iter().any(|&x| x != 0) {
        let mut rem: u64 = 0;
        for x in a.iter_mut().rev() { let cur = (rem << 32) | (*x as u64); *x = (cur / 1_000_000_000) as u32; rem = cur % 1_000_000_000; }
        out.push(rem as u32);
    }
    if out.is_empty() { return "0".to_string(); }
    let mut s = format!("{}", out[out.len() - 1]);
    for k in (0..out.len() - 1).rev() { s.push_str(&format!("{:09}", out[k])); }
    s
}
fn gmap_v(gn: &G, gr: &G, rows: &[V5]) -> Vec<V5> { rows.iter().map(|r| gr.apply_inv(&gn.apply(r))).collect() }
// composition c(x) = gr^{-1}(gn(x)) as a G in apply form: c.p[pr[i]] = pn[i], c.e[pr[i]] = er[i]*en[i]
fn compose_g(gn: &G, gr: &G) -> G { let mut c = G { p: [0; 5], e: [1; 5] }; for i in 0..5 { let j = gr.p[i] as usize; c.p[j] = gn.p[i]; c.e[j] = gr.e[i] * gn.e[i]; } c }
// pair_reduce with the elementary steps logged: row i -= q * row j (same loop as wp0a::pair_reduce)
fn pair_reduce_steps(b: &mut Vec<V5>) -> Vec<(usize, usize, I)> {
    let k = b.len(); let mut st = vec![];
    loop { let mut imp = false;
        for i in 0..k { for j in 0..k { if i == j { continue; }
            let nj = dot(&b[j], &b[j]); if nj == 0 { continue; }
            let q = rdiv(dot(&b[i], &b[j]), nj);
            if q != 0 { let mut nw = b[i]; for c in 0..5 { nw[c] -= q * b[j][c]; }
                if dot(&nw, &nw) < dot(&b[i], &b[i]) { b[i] = nw; imp = true; st.push((i, j, q)); } }
        } }
        if !imp { break; } }
    st
}
fn merge_ranges_v(mut r: Vec<(I, I)>) -> Vec<(I, I)> {
    r.sort(); let mut un: Vec<(I, I)> = vec![];
    for (a, b) in r { if let Some(l) = un.last_mut() { if a <= l.1 + 1 { if b > l.1 { l.1 = b; } continue; } } un.push((a, b)); }
    un
}
// line enumeration statistics of one class (copy of wp0a cert.rs lines_enum without the witness search): [rows, box, ellipse, in-range, primitive, lines checked]
fn lines_stats(kb: &Vec<V5>, un: &Vec<(I, I)>) -> [u64; 6] {
    let mut s = [0u64; 6]; if un.is_empty() { return s; }
    let mut b = kb.clone(); pair_reduce(&mut b, None);
    let (a, bb, cc) = (dot(&b[0], &b[0]), dot(&b[0], &b[1]), dot(&b[1], &b[1])); let dt = a * cc - bb * bb;
    let nmax = un.last().unwrap().1;
    let xmax = isqrt(fdiv(nmax * cc, dt)); let ymax = isqrt(fdiv(nmax * a, dt));
    s[0] += (2 * xmax + 1) as u64;
    for y in 0..=ymax { for x in -xmax..=xmax {
        s[1] += 1; if y == 0 && x <= 0 { continue; }
        let n = a * x * x + 2 * bb * x * y + cc * y * y;
        if n <= nmax { s[2] += 1; }
        if n < un[0].0 || n > nmax || !un.iter().any(|&(lo, hi)| n >= lo && n <= hi) { continue; }
        s[3] += 1; if gcd(x.abs(), y) != 1 { continue; } s[4] += 1;
        let mut v = [0 as I; 5]; for i in 0..5 { v[i] = x * b[0][i] + y * b[1][i]; }
        if v.iter().any(|&e| e == 0) { continue; }
        let mut av = [v[0].abs(), v[1].abs(), v[2].abs(), v[3].abs(), v[4].abs()]; av.sort();
        if av[0] == av[1] || av[1] == av[2] || av[2] == av[3] || av[3] == av[4] { continue; }
        s[5] += 1;
    } }
    s
}
struct Cl3 { g: G, l: Vec<V5>, k: Vec<V5>, ranges: Vec<(I, I)>, first_hi: usize, first_rep: usize, members: u64 }
fn bitlen(x: I) -> u64 { 128 - (x.unsigned_abs() as u128).leading_zeros() as u64 }
fn rec_hex(rec: &[I], w: u32) -> String {
    let bias: I = 1 << (w - 1); let nib = (w / 4) as usize; let mut s = String::from("0x");
    for d in (0..rec.len()).rev() { let v = rec[d] + bias; assert!(v >= 0 && v < (1 << w), "digit overflow"); s.push_str(&format!("{:0width$x}", v, width = nib)); }
    s
}
fn alt_pat(n: usize) -> String { // left-nested rcases pattern for n alternatives: n=1 "h", n=2 "h | h", n=3 "(h | h) | h"
    let mut p = "h".to_string(); for _ in 1..n { p = if p.contains('|') { format!("({}) | h", p) } else { format!("{} | h", p) }; } p }

struct S2 { t: Vec<I>, n2: Node, x: V5, w: I, cls: usize, gn: G, c2: Fr }
struct C2 { hi: usize, n2: Node, g: G, c2: Fr, x: V5, w: I }
struct LC { b: Vec<V5>, g3: I, ranges: Vec<(I, I)>, real_ne: bool, crit: bool, first_hi: usize, first_ci: usize, members: u64 }

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
    // ---- inv mode: per depth-1 aggregates (columns: d2old, d2surv, reps, ball, cand, pass, gcdrej, ei, greedyrej, rows, leaves, crit, nonempty-noncrit leaves, t4classes, lines, box, inwin, prim)
    let mut d1agg: Vec<[u64; 20]> = vec![[0u64; 20]; d1.len()];
    let mut lcm: HashMap<Vec<i64>, LC> = HashMap::new();
    let mut reptsv = String::from("ci\td1\tball\tcand\tpass\tgcdrej\tei\tgreedyrej\trows\tleaves\tcrit\tnonempty\tk_empty\tk_window\n");
    if args.get(1).map(|x| x.as_str()) == Some("inv") {
        let m0 = fr(3, 10); let c2k = fr(37, 9);
        for (hi, (h, n1)) in d1.iter().enumerate() {
            let (mm1, _) = mlat(&[*h], false); let m1 = m_of(mm1);
            let ms = [m0, m1]; let inv = [fi(0), fr(n1.gs[0], n1.gs[1])];
            let bold = radius_bound(&ms, &inv, 2, c2k, &[1]).unwrap();
            let mut f2 = Funnel::default(); let _ = children(n1, bold, &mut f2);
            d1agg[hi][0] = f2.pass; d1agg[hi][1] = surv[hi].len() as u64;
        }
    }
    let nrep = cls2.len();
    let selected: Vec<usize> = (0..nrep).filter(|&ci| { let rp = &cls2[ci]; let n1 = &d1[rp.hi].1; fr(rp.n2.gs[2], rp.n2.gs[1]).lt(d2_bound(n1, c1s[rp.hi])) }).collect();
    say!("surviving class reps {} (expected 1965)", selected.len());
    let mode = args.get(1).cloned().unwrap_or("stats".to_string());
    let reps: Vec<usize> = match args.get(2).map(|s| s.as_str()) {
        None | Some("sel") => selected.clone(),
        Some(s) => s.split(',').filter(|x| !x.is_empty()).map(|x| x.parse().unwrap()).collect() };
    let real = std::env::var("L5V3_REAL").map(|s| s == "1").unwrap_or(false) && mode == "v3";
    let d1set: Vec<usize> = std::env::var("L5V3_D1").unwrap_or("".to_string()).split(',').filter(|x| !x.is_empty()).map(|x| x.parse().unwrap()).collect();
    let emit_set: Vec<usize> = reps.clone();
    let reps: Vec<usize> = if real { selected.clone() } else { reps };
    let mut cls3: Vec<Cl3> = vec![]; let mut c3map: HashMap<Vec<i64>, usize> = HashMap::new();
    let chunk_pts: u64 = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(1700);
    let lean_dir_s = std::env::var("L5D_SRC").unwrap_or("/DEV_TREE/work/lean5_data/src".to_string()); let lean_dir: &str = &lean_dir_s;
    let log_dir = std::env::var("L5D_LOG").unwrap_or("/DEV_TREE/work/lean5_data/logs".to_string()); fs::create_dir_all(&log_dir).unwrap(); fs::create_dir_all(lean_dir).unwrap();
    let counting = mode == "count" || mode == "countleaves" || mode == "v3count"; let mut nbytes = 0u64; let mut nfiles = 0u64; let mut nmodtot = 0u64; let mut wide = 0u64;
    macro_rules! wr { ($p:expr, $c:expr) => {{ let c: String = $c; nbytes += c.len() as u64; nfiles += 1; if !counting { fs::write($p, c).unwrap(); } }} }
    let ii = |x: I| if x < 0 { format!("({})", x) } else { format!("{}", x) };
    struct Row { t0: I, t1: I, lo: I, hi: I, pl: Vec<I>, ball: u64, kk: [u64; 4] }
    struct Ch { t0: I, t1s: I, nrows: usize, data: Vec<I>, ball: u64 }
    let mut dump = String::new();
    let mut v3tsv = String::from("ci\td1\tleaves\tk1\tk2\tcrit\tchunks\trec16\tchunks16\tmaxabs\tnodemods\tbits_k1\tbits_k2\tbytes32\tbytesU\n"); let mut v3crit = String::from("ci\tpos\tt0\tt1\tt2\tleaves\n");
    let mut tsv = String::from("ci\td1idx\tball\tcand\tpass\tgcdrej\tei\tgreedyrej\trows\tgroups\tmaxgroupball\tmods\tmaxmodball\n");
    let mut tot = [0u64; 8];
    for &ci in &reps {
        let rp = &cls2[ci]; let nd = &rp.n2; let bound = d3_bound(nd, c1s[rp.hi], rp.c2);
        let tmax: Vec<I> = (0..3).map(|i| isqrt(fdiv(bound.n * nd.a[i][i], bound.d))).collect();
        let g = nd.g(); let adj = &nd.adj;
        if mode == "dumpnode" { dump.push_str(&format!("REP {} {}\nL0 {:?}\nL1 {:?}\nB {:?} {:?} {:?}\nRAD {} {}\nTMAX {:?}\n", ci, rp.hi, nd.l[0], nd.l[1], nd.b[0], nd.b[1], nd.b[2], bound.n, bound.d, tmax)); }
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
                        if mode != "rowsonly" { for t2 in a..=b { bl += 1; let k = ps(t0, t1, t2) as usize; kk[k] += 1; if k == 0 { pl.push(t2); } if mode == "dumpnode" { dump.push_str(&format!("P {} {} {} {}\n", t0, t1, t2, k)); } } } else { bl = (b - a + 1) as u64; }
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
        let mut mods: Vec<Vec<Ch>> = vec![vec![]]; let mut modball = 0u64; let mut maxmod = 0u64; let mut row_mod: Vec<usize> = vec![];
        for r in &rows {
            if modball > 0 && modball + r.ball > chunk_pts { mods.push(vec![]); modball = 0; }
            let m = mods.last_mut().unwrap();
            let newch = match m.last() { Some(c) => c.t0 != r.t0, None => true };
            if newch { m.push(Ch { t0: r.t0, t1s: r.t1, nrows: 0, data: vec![], ball: 0 }); }
            let c = m.last_mut().unwrap();
            c.nrows += 1; c.ball += r.ball; c.data.push(r.t1); c.data.push(r.lo); c.data.push(r.hi); c.data.push(r.pl.len() as I);
            for &x in &r.pl { c.data.push(x); }
            modball += r.ball; if modball > maxmod { maxmod = modball; }
            row_mod.push(mods.len() - 1);
        }
        let nmods = mods.len();
        tsv.push_str(&format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n", ci, rp.hi, ball, k4[0] + k4[3], k4[0], k4[1], k4[2], k4[3], rows.len(), tmax[0] + 1, maxg, nmods, maxmod));
        { let da = &mut d1agg[rp.hi]; da[2] += 1; da[3] += ball; da[4] += k4[0] + k4[3]; da[5] += k4[0]; da[6] += k4[1]; da[7] += k4[2]; da[8] += k4[3]; da[9] += rows.len() as u64; }
        tot[0] += ball; tot[1] += k4[0] + k4[3]; tot[2] += k4[0]; tot[3] += rows.len() as u64; tot[4] += nmods as u64; tot[5] += 1;
        if mode == "inv" {
            let c1 = c1s[rp.hi]; let c2 = rp.c2;
            let (mut nleaf, mut ncrit, mut nne, mut ke, mut kw) = (0u64, 0u64, 0u64, 0u64, 0u64);
            for r in &rows { for &t2 in &r.pl {
                let t = vec![r.t0, r.t1, t2];
                let n3 = child(nd, &t);
                let (_, w) = mlat(&mred(&n3.l), true); let w = w.unwrap();
                let c3 = witness_ok(&n3.l, &w.x, w.w).unwrap();
                let m3 = m_of(c3); let is_crit = m3.eq(fi(0));
                let msv = [fr(3, 10), m_of(c1), m_of(c2), m3];
                let win = leaf_window(&msv, &n3.gs, fr(3, 4));
                let nonempty = match win.hi { None => true, Some(hi) => win.lo.lt(hi) };
                let g3 = n3.gs[3];
                nleaf += 1; if is_crit { ncrit += 1; }
                if nonempty { if is_crit { } else { nne += 1; } } 
                let q3 = qmat(&n3.b, &n3.adj); let (key, _) = canon(&[&q3], &perms);
                let e = lcm.entry(key).or_insert_with(|| LC { b: n3.b.clone(), g3, ranges: vec![], real_ne: false, crit: is_crit, first_hi: rp.hi, first_ci: ci, members: 0 });
                e.members += 1;
                if nonempty && !is_crit {
                    e.real_ne = true; let hi = win.hi.expect("noncrit infinite window");
                    let (a, b) = (cdiv(win.lo.n * g3, win.lo.d), cdiv(hi.n * g3, hi.d) - 1);
                    if a <= b { e.ranges.push((a, b)); kw += 1; } else { ke += 1; }
                } else if !is_crit { ke += 1; }
            } }
            let da = &mut d1agg[rp.hi]; da[10] += nleaf; da[11] += ncrit; da[12] += nne;
            reptsv.push_str(&format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n", ci, rp.hi, ball, k4[0] + k4[3], k4[0], k4[1], k4[2], k4[3], rows.len(), nleaf, ncrit, nne, ke, kw));
            continue;
        }
        if mode == "v3" || mode == "v3count" {
            // ===== v3: flat per-record layout (one natural per record), node accessor, per-chunk independent modules
            let pr: usize = std::env::var("L5V3_PR").ok().and_then(|s| s.parse().ok()).unwrap_or(64);
            let layout_u = std::env::var("L5V3_LAYOUT").map(|s| s == "U").unwrap_or(false);
            let w16 = std::env::var("L5V3_W16").map(|s| s == "1").unwrap_or(false);
            let c1 = c1s[rp.hi]; let c2 = rp.c2;
            let mut recs: Vec<Vec<I>> = vec![]; let mut kinds = [0usize; 3]; let mut crit_pos: Vec<(usize, Vec<I>)> = vec![];
            let mut bits = [0u64; 3]; let mut ndig = [0u64; 3];
            for r in &rows { for &t2 in &r.pl {
                let t = vec![r.t0, r.t1, t2];
                let n3 = child(nd, &t); let y = lift(nd, &t);
                assert_eq!(n3.l[2], y);
                let (_, w) = mlat(&mred(&n3.l), true); let w = w.unwrap();
                let c3 = witness_ok(&n3.l, &w.x, w.w).unwrap();
                let m3 = m_of(c3); let crit = m3.eq(fi(0));
                let ms = [fr(3, 10), m_of(c1), m_of(c2), m3];
                let (kind, rlo, rhi): (usize, I, I) = if crit { (0, 0, -1) } else {
                    let wn = leaf_window(&ms, &n3.gs, rho); let g3 = n3.gs[3];
                    let hi = wn.hi.unwrap();
                    let e = cdiv(hi.n * g3, hi.d); let a = cdiv(wn.lo.n * g3, wn.lo.d);
                    if a > e - 1 { (1, e, e - 1) } else { (2, a, e - 1) } };
                kinds[kind] += 1;
                let s = right_inverse(&n3.l).expect("saturation functionals");
                assert_eq!(n3.b.len(), 2); assert_eq!(n3.r.len(), 2); assert_eq!(s.len(), 3);
                let mut st: Vec<I> = vec![];
                st.extend_from_slice(&t); st.extend_from_slice(&y);
                for v in &n3.b { st.extend_from_slice(v); } for v in &n3.r { st.extend_from_slice(v); }
                for v in &s { st.extend_from_slice(v); }
                st.extend_from_slice(&w.x); st.push(w.w); st.push(kind as I); st.push(0); st.push(rlo); st.push(rhi);
                for i in 0..5 { st.push(i as I); } for _ in 0..5 { st.push(1); }
                for _ in 0..2 { st.extend_from_slice(&[1, 0, 0, 0, 1, 0, 0, 0, 1]); }
                for v in &n3.l { st.extend_from_slice(v); }
                st.push(0);
                if real && kind == 2 {
                    let mut red = n3.l.clone(); let steps = pair_reduce_steps(&mut red);
                    assert_eq!(red, mred(&n3.l));
                    let q3 = qmat(&n3.b, &n3.adj); let (key, gl) = canon(&[&q3], &perms);
                    let cid = match c3map.get(&key) { Some(&c) => c, None => { let c = cls3.len(); c3map.insert(key, c);
                        let mut kb = n3.b.clone(); pair_reduce(&mut kb, None);
                        cls3.push(Cl3 { g: gl, l: red.clone(), k: kb, ranges: vec![], first_hi: rp.hi, first_rep: ci, members: 0 }); c } };
                    cls3[cid].members += 1; cls3[cid].ranges.push((rlo, rhi));
                    let rc_g = cls3[cid].g; let rc_l = cls3[cid].l.clone();
                    let hh = gmap_v(&gl, &rc_g, &red);
                    let u = solve_u(&hh, &rc_l).expect("leaf map U"); let u2 = solve_u(&rc_l, &hh).expect("leaf map U'");
                    let gp = compose_g(&gl, &rc_g);
                    for i in 0..3 { assert_eq!(gp.apply(&red[i]), hh[i]); }
                    st[50] = cid as I;
                    for i in 0..5 { st[53 + i] = gp.p[i] as I; st[58 + i] = gp.e[i] as I; }
                    for i in 0..3 { for j in 0..3 { st[63 + 3 * i + j] = u[i][j]; st[72 + 3 * i + j] = u2[i][j]; } }
                    for i in 0..3 { for c in 0..5 { st[81 + 5 * i + c] = rc_l[i][c]; } }
                    st[96] = steps.len() as I;
                    for &(i, j, q) in &steps { st.push(i as I); st.push(j as I); st.push(q); }
                } else { assert_eq!(st.len(), 97); }
                for &x in &st { bits[kind] += bitlen(x); ndig[kind] += 1; }
                if crit { crit_pos.push((recs.len(), t.clone())); }
                recs.push(st);
            } }
            if real && !emit_set.contains(&ci) { continue; }
            let cnt = recs.len(); let nch = (cnt + pr - 1) / pr;
            let is16 = |rr: &[Vec<I>]| rr.iter().all(|r| r.iter().all(|&x| x.abs() <= 32767));
            let nrec16 = recs.iter().filter(|r| r.iter().all(|&x| x.abs() <= 32767)).count();
            let mxabs = recs.iter().flat_map(|r| r.iter()).map(|x| x.abs()).max().unwrap_or(0);
            let mut chunk16 = 0usize; for j in 0..nch { if is16(&recs[j * pr..((j + 1) * pr).min(cnt)]) { chunk16 += 1; } }
            let mut bytes32 = 0u64; // hex source bytes of the all-32-bit layout (records only)
            for r in &recs { bytes32 += (2 + 8 * r.len() + 2) as u64; }
            let mut bytesu = 0u64; // layout with per-chunk 16-bit where possible
            for j in 0..nch { let sl = &recs[j * pr..((j + 1) * pr).min(cnt)]; let wd = if is16(sl) { 4 } else { 8 }; for r in sl { bytesu += (2 + wd * r.len() + 2) as u64; } }
            let bavg = |k: usize| if ndig[k] > 0 { bits[k] as f64 / ndig[k] as f64 } else { 0.0 };
            v3tsv.push_str(&format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.3}\t{:.3}\t{}\t{}\n", ci, rp.hi, cnt, kinds[1], kinds[2], kinds[0], nch, nrec16, chunk16, mxabs, nmods, bavg(1), bavg(2), bytes32, bytesu));
            if !crit_pos.is_empty() {
                for (p, t) in &crit_pos { v3crit.push_str(&format!("{}\t{}\t{}\t{}\t{}\t{}\n", ci, p, t[0], t[1], t[2], cnt)); }
                say!("V3 rep {} count {} CRITICAL {}: flat modules NOT emitted (route: see report)", ci, cnt, crit_pos.len());
                continue;
            }
            if mode == "v3count" { say!("V3COUNT rep {} count {} chunks {} chunks16 {} bytes32 {} bytesU {}", ci, cnt, nch, chunk16, bytes32, bytesu); continue; }
            // node accessor literal (34 integers; layout of GD3F1.NodeAg)
            let (x1, w1v) = w1[rp.hi];
            let e00 = dot(&nd.l[0], &nd.l[0]); let e01 = dot(&nd.l[0], &nd.l[1]); let e11 = dot(&nd.l[1], &nd.l[1]);
            let mut ng: Vec<I> = vec![]; ng.extend_from_slice(&nd.l[0]); ng.extend_from_slice(&nd.l[1]); for k in 0..3 { ng.extend_from_slice(&nd.b[k]); }
            ng.extend_from_slice(&[wmin_v(&x1, w1v), w1v, wmin_v(&rp.x, rp.w), rp.w, e00, e00 * e11 - e01 * e01, e00, e01, e11]);
            assert_eq!(ng.len(), 34);
            let nn_digits: Vec<u32> = ng.iter().map(|&x| { let v = x + (1i128 << 31); assert!(v >= 0 && v < (1i128 << 32)); v as u32 }).collect();
            let nn = dec_of_u32(&nn_digits);
            let rep = ci;
            let nodetop = if nmods == 1 { format!("LRSpectrumFull.L5S4.GD3N{}", rep) } else { format!("LRSpectrumFull.L5S4.GD3N{}Z", rep) };
            let nodefile = format!("/-\n# L5S4.GD3F2N{rep} : flat node accessor of rep #{rep} and its agreement with `nK` (S4N)\n-/\nimport LRSpectrumFull.L5S4.GD3F1\nimport LRSpectrumFull.L5S4.GD3N{rep}\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace N{rep}\nopen Matrix Finset LRSpectrumFull.L5S3\n\ndef NN : ℕ := {nn}\n\ntheorem ag : NodeAg nK (dg NN) := by\n  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel\n\nend N{rep}\nend L5S4\nend LRSpectrumFull\n", rep = rep, nn = nn);
            wr!(format!("{}/GD3F2N{}.lean", lean_dir, rep), nodefile);
            let tag = |j: usize| format!("c{}", j);
            for j in 0..nch {
                let sl = &recs[j * pr..((j + 1) * pr).min(cnt)];
                let wd: u32 = if layout_u && w16 && is16(sl) { 16 } else { 32 };
                let acc = if wd == 16 { "dg16" } else { "dg" };
                let mut body = String::new();
                for (k, r) in sl.iter().enumerate() { body.push_str(&rec_hex(r, wd)); body.push_str(if k + 1 < sl.len() { ",\n" } else { "\n" }); }
                let tg = tag(j);
                let head = format!("/-\n# N{rep}.{tg} : flat per-record leaf blobs, chunk {tg} (S4N layout, written by l5v3)\n-/\nimport LRSpectrumFull.L5S4.GD3F1\n{extra}import LRSpectrumFull.L5S4.GD3F2N{rep}\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace N{rep}\n\n", rep = rep, tg = tg, extra = if wd == 16 { "import LRSpectrumFull.L5S4.GD3F4\n" } else { "" });
                let foot = format!("end N{}\nend L5S4\nend LRSpectrumFull\n", rep);
                let txt = if !layout_u {
                    format!("{head}def blobsF_{tg} : List ℕ := [\n{body}]\n\ntheorem okF_{tg} : (blobsF_{tg}.all fun N => leafOkF (dg NN) (dg N)) = true := by decide +kernel\n\n{foot}", head = head, tg = tg, body = body, foot = foot)
                } else {
                    format!("{head}def blobsU_{tg} : List ℕ := [\n{body}]\n\ndef recsU_{tg} : List LeafRec := blobsU_{tg}.map fun N => recOf ({acc} N)\n\ntheorem okU_{tg} : (blobsU_{tg}.all fun N => leafOkF (dg NN) ({acc} N)) = true := by decide +kernel\n\ntheorem recsU_ok_{tg} : ∀ r ∈ recsU_{tg}, leafOk nK r = true := by\n  intro r hr\n  obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hr\n  exact leafOkF_sound nK (dg NN) ({acc} N) ag (List.all_eq_true.1 okU_{tg} N hN)\n\n{foot}", head = head, tg = tg, body = body, acc = acc, foot = foot)
                };
                wr!(format!("{}/GD3F2L{}R{}.lean", lean_dir, rep, j), txt);
            }
            // rep-level assembly
            let mut imps = String::new(); for j in 0..nch { imps.push_str(&format!("import LRSpectrumFull.L5S4.GD3F2L{}R{}\n", rep, j)); }
            if nch == 0 { imps.push_str(&format!("import LRSpectrumFull.L5S4.GD3F2N{}\n", rep)); }
            if nmods > 1 { imps.push_str(&format!("import {}\n", nodetop)); }
            let asm_head = format!("/-\n# L5S4.GD3F2L{rep} : `StreamHyp'.t3` for rep #{rep} from the FLAT leaf checker (S4N)\n\n`recsF` is the record list read from the per-record naturals; `recsF_ok` is `leafOkF_sound` on every record; the `t3` clause\nis `t3_leaves` exactly as in `GD3L{rep}.t3_node`, conditional only on the class-table obligation `T4Cover`.\n\nNo `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.\n-/\n{imps}\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace N{rep}\nopen Matrix Finset LRSpectrumFull.L5S3\n\n", rep = rep, imps = imps);
            let t3tail = format!("/-- `StreamHyp'.t3` for rep #{rep} from the flat checker: conditional only on `T4Cover`. -/\ntheorem t3_nodeF (C : Certificate) (hT4 : T4Cover C recsF) :\n    ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n3 : LeafW), (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧\n      n3.rows = setRow nK.rows 2 y' ∧ LeafRelW C n3 :=\n  fun y hy => t3_leaves C nK bn bd (by norm_num [bd]) hrad cks (by rw [fc_eq]; exact cov) (by rw [fc_eq]; exact allok)\n    recsF alignF recsF_ok hT4 y hy\n\n#print axioms t3_nodeF\n\nend N{rep}\nend L5S4\nend LRSpectrumFull\n", rep = rep);
            let mut mid = String::new();
            if !layout_u {
                let cat = if nch == 0 { "[]".to_string() } else { (0..nch).map(|j| format!("blobsF_c{}", j)).collect::<Vec<_>>().join(" ++ ") };
                mid.push_str(&format!("def blobsF : List ℕ := {}\ndef recsF : List LeafRec := blobsF.map fun N => recOf (dg N)\n\ntheorem alignF : storedOf cks = recsF.map LeafRec.t := by decide +kernel\n\ntheorem blobsF_ok : ∀ N ∈ blobsF, leafOkF (dg NN) (dg N) = true := by\n  intro N hN\n", cat));
                if nch == 0 { mid.push_str("  simp [blobsF] at hN\n"); }
                else { mid.push_str("  simp only [blobsF, List.mem_append] at hN\n"); if nch > 1 { mid.push_str(&format!("  rcases hN with {}\n", alt_pat(nch))); } }
                if nch >= 1 { if nch == 1 { mid.push_str("  exact List.all_eq_true.1 okF_c0 N hN\n"); } else { for j in 0..nch { mid.push_str(&format!("  · exact List.all_eq_true.1 okF_c{} N h\n", j)); } } }
                mid.push_str("\ntheorem recsF_ok : ∀ r ∈ recsF, leafOk nK r = true := by\n  intro r hr\n  obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hr\n  exact leafOkF_sound nK (dg NN) (dg N) ag (blobsF_ok N hN)\n\n");
            } else {
                let cat = if nch == 0 { "[]".to_string() } else { (0..nch).map(|j| format!("recsU_c{}", j)).collect::<Vec<_>>().join(" ++ ") };
                mid.push_str(&format!("def recsF : List LeafRec := {}\n\ntheorem alignF : storedOf cks = recsF.map LeafRec.t := by decide +kernel\n\ntheorem recsF_ok : ∀ r ∈ recsF, leafOk nK r = true := by\n  intro r hr\n", cat));
                if nch == 0 { mid.push_str("  simp [recsF] at hr\n"); }
                else { mid.push_str("  simp only [recsF, List.mem_append] at hr\n"); if nch > 1 { mid.push_str(&format!("  rcases hr with {}\n", alt_pat(nch))); }
                    if nch == 1 { mid.push_str("  exact recsU_ok_c0 r hr\n"); } else { for j in 0..nch { mid.push_str(&format!("  · exact recsU_ok_c{} r h\n", j)); } } }
                mid.push_str("\n");
            }
            wr!(format!("{}/GD3F2L{}.lean", lean_dir, rep), format!("{}{}{}", asm_head, mid, t3tail));
            say!("V3 rep {} count {} k1 {} k2 {} chunks {} (16-bit chunks {}) nodemods {}", rep, cnt, kinds[1], kinds[2], nch, chunk16, nmods);
            continue;
        }
        if mode == "leaves" || mode == "countleaves" {
            let rho = fr(3, 4);
            let c1 = c1s[rp.hi]; let c2 = rp.c2;
            let nm = mods.len(); let mut streams: Vec<Vec<I>> = vec![vec![]; nm]; let mut cnts = vec![0usize; nm]; let mut kindsm = vec![[0usize; 3]; nm];
            for (ri, r) in rows.iter().enumerate() { let mi = row_mod[ri]; for &t2 in &r.pl {
                let t = vec![r.t0, r.t1, t2];
                let n3 = child(nd, &t); let y = lift(nd, &t);
                assert_eq!(n3.l[2], y);
                let (_, w) = mlat(&mred(&n3.l), true); let w = w.unwrap();
                let c3 = witness_ok(&n3.l, &w.x, w.w).unwrap();
                let m3 = m_of(c3); let crit = m3.eq(fi(0));
                let ms = [fr(3, 10), m_of(c1), m_of(c2), m3];
                let (kind, rlo, rhi): (usize, I, I) = if crit { (0, 0, -1) } else {
                    let wn = leaf_window(&ms, &n3.gs, rho); let g3 = n3.gs[3];
                    let hi = wn.hi.unwrap();
                    let e = cdiv(hi.n * g3, hi.d); let a = cdiv(wn.lo.n * g3, wn.lo.d);
                    if a > e - 1 { (1, e, e - 1) } else { (2, a, e - 1) } };
                kindsm[mi][kind] += 1; cnts[mi] += 1;
                let s = right_inverse(&n3.l).expect("saturation functionals");
                assert_eq!(n3.b.len(), 2); assert_eq!(n3.r.len(), 2); assert_eq!(s.len(), 3);
                let stream = &mut streams[mi];
                stream.extend_from_slice(&t); stream.extend_from_slice(&y);
                for v in &n3.b { stream.extend_from_slice(v); } for v in &n3.r { stream.extend_from_slice(v); }
                for v in &s { stream.extend_from_slice(v); }
                stream.extend_from_slice(&w.x); stream.push(w.w); stream.push(kind as I); stream.push(0); stream.push(rlo); stream.push(rhi);
                for i in 0..5 { stream.push(i as I); } for _ in 0..5 { stream.push(1); }
                for _ in 0..2 { stream.extend_from_slice(&[1, 0, 0, 0, 1, 0, 0, 0, 1]); }
                for v in &n3.l { stream.extend_from_slice(v); }
                stream.push(0);
            } }
            let single = nmods == 1;
            let mut lnames: Vec<String> = vec![]; let mut totcnt = 0usize;
            for m in 0..nm {
                if cnts[m] == 0 { continue; }
                let mx = streams[m].iter().map(|x| x.abs()).max().unwrap_or(0); let wd: u32 = if mx < 32767 { 16 } else if mx < 2147483647 { 32 } else { 64 }; if wd > 16 { wide += 1; } let mut dg = Dg::new(wd); for &x in &streams[m] { dg.put(x); }
                let top = if m == 0 { format!("LRSpectrumFull.L5S4.GD3N{}", ci) } else { format!("LRSpectrumFull.L5S4.GD3N{}M{}", ci, m) };
                let cks: Vec<String> = (0..mods[m].len()).map(|j| format!("ck_{}_{}", m, j)).collect();
                let s = format!("/-\n# L5S4.GD3L{ci}M{m} : leaf records of the depth-3 children in chunk module {m} of rep #{ci} (stage S4 data generator l5d)\nGenerated by l5d leaves.  {cnt} leaves (kind 1 empty window {k1}, kind 2 window with SELF class {k2}).  Imports only its own node chunk module: independent of every other chunk.\n-/\nimport {top}\nimport LRSpectrumFull.L5S4.GD3K4\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace N{ci}\nopen Matrix Finset LRSpectrumFull.L5S3\n\ndef leafData_{m} : List ℤ := unpackL{sfx} 0x{hex} {len}\ndef recs_{m} : List LeafRec := parseAll {cnt} leafData_{m}\n\ntheorem align_{m} : storedOf [{cks}] = recs_{m}.map LeafRec.t := by decide +kernel\n\ntheorem recs_ok_{m} : ∀ r ∈ recs_{m}, leafOk nK r = true := by decide +kernel\n\nend N{ci}\nend L5S4\nend LRSpectrumFull\n", ci = ci, m = m, cnt = cnts[m], k1 = kindsm[m][1], k2 = kindsm[m][2], top = top, cks = cks.join(", "), hex = hex_of(&dg.v, wd), len = dg.v.len(), sfx = if wd == 16 { "".to_string() } else { format!("{}", wd) });
                wr!(format!("{}/GD3L{}M{}.lean", lean_dir, ci, m), s);
                lnames.push(format!("LRSpectrumFull.L5S4.GD3L{}M{}", ci, m)); totcnt += cnts[m];
            }
            let _ = single;
            if !lnames.is_empty() {
                let recsx: Vec<String> = (0..nm).filter(|&m| cnts[m] > 0).map(|m| format!("recs_{}", m)).collect();
                let imps = lnames.join("\nimport ");
                let zn = if nmods == 1 { format!("LRSpectrumFull.L5S4.GD3N{}", ci) } else { format!("LRSpectrumFull.L5S4.GD3N{}Z", ci) };
                let s = format!("/-\n# L5S4.GD3L{ci}Z : assembly of the leaf chunks of rep #{ci}\nGenerated by l5d leaves.  {tc} leaves in {n} chunk modules.  TEMPLATE, NOT BUILT: `align` needs the generic lemma `storedOf_append` (storedOf of a concatenation of chunk lists), to be supplied on the Lean side; the per-chunk `align_m` and `recs_ok_m` are the checked statements.\n-/\nimport {zn}\nimport {imps}\n\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace N{ci}\nopen Matrix Finset LRSpectrumFull.L5S3\n\nabbrev recs : List LeafRec := {rx}\n\ntheorem recs_ok : ∀ r ∈ recs, leafOk nK r = true := by\n  intro r hr\n  simp only [recs, List.mem_append, or_assoc] at hr\n  {proof}\n\nend N{ci}\nend L5S4\nend LRSpectrumFull\n", ci = ci, tc = totcnt, n = lnames.len(), zn = zn, imps = imps, rx = if recsx.is_empty() { "[]".to_string() } else { recsx.join(" ++ ") }, proof = { let ids: Vec<usize> = (0..nm).filter(|&m| cnts[m] > 0).collect(); if ids.len() == 1 { format!("exact recs_ok_{} r hr", ids[0]) } else { let pats: Vec<String> = (0..ids.len()).map(|k| format!("h{}", k)).collect(); let ex: Vec<String> = ids.iter().enumerate().map(|(k, m)| format!("recs_ok_{} r h{}", m, k)).collect(); format!("rcases hr with {}\n  exacts [{}]", pats.join(" | "), ex.join(", ")) } });
                wr!(format!("{}/GD3L{}Z.lean", lean_dir, ci), s);
            }
            say!("LEAVES rep {} count {} modules {}", ci, totcnt, lnames.len());
            continue;
        }
        if mode == "dumpnode" { dump.push_str(&format!("CNT {} {} {} {} {}\n", ball, k4[1], k4[2], k4[3], k4[0])); continue; }
        if mode != "emit" && mode != "count" { continue; }
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
        wr!(format!("{}/GD3N{}.lean", lean_dir, ci), s0);
        if nmods > 1 {
            for m in 1..nmods {
                let mut s = hdr(&format!("GD3N{}M{}", ci, m), &format!("chunk module {}", m), &format!("LRSpectrumFull.L5S4.GD3N{}", ci));
                s.push_str(&chunk_text(m, &mods[m]));
                s.push_str(&foot.replace("{}", &ci.to_string()));
                wr!(format!("{}/GD3N{}M{}.lean", lean_dir, ci, m), s);
            }
            let imps: Vec<String> = (1..nmods).map(|m| format!("LRSpectrumFull.L5S4.GD3N{}M{}", ci, m)).collect();
            let mut s = hdr(&format!("GD3N{}Z", ci), "assembly of the chunks", &imps.join("\nimport "));
            s.push_str(&assembly());
            s.push_str(&foot.replace("{}", &ci.to_string()));
            wr!(format!("{}/GD3N{}Z.lean", lean_dir, ci), s);
        }
        say!("EMITTED rep {} d1idx {} ball {} pass {} mods {} files {} cumbytes {}", ci, rp.hi, ball, k4[0], nmods, nfiles, nbytes);
    }
    if mode == "inv" {
        // lines per class (no witness search)
        let mut ctsv = String::from("class\tfirst_hi\tfirst_ci\tg3\tmembers\tnranges\tmerged\tbox\tinwin\tprim\tnonzero\tlines\n");
        let (mut t_box, mut t_in, mut t_prim, mut t_nz, mut t_nzd) = (0u64, 0u64, 0u64, 0u64, 0u64);
        let (mut ncls, mut ncrit_cls, mut nreal, mut nint) = (0u64, 0u64, 0u64, 0u64);
        let mut keys: Vec<&Vec<i64>> = lcm.keys().collect(); keys.sort();
        for (idx, k) in keys.iter().enumerate() {
            let c = &lcm[*k]; ncls += 1; if c.crit { ncrit_cls += 1; } if c.real_ne { nreal += 1; }
            if c.crit || c.ranges.is_empty() { continue; }
            nint += 1;
            let mut rg = c.ranges.clone(); rg.sort();
            let mut un: Vec<(I, I)> = vec![];
            for (a, b) in rg { if let Some(l) = un.last_mut() { if a <= l.1 + 1 { if b > l.1 { l.1 = b; } continue; } } un.push((a, b)); }
            let mut b = c.b.clone(); pair_reduce(&mut b, None);
            let (a, bb, cc) = (dot(&b[0], &b[0]), dot(&b[0], &b[1]), dot(&b[1], &b[1]));
            let dt = a * cc - bb * bb; let nmax = un.last().unwrap().1;
            let xmax = isqrt(fdiv(nmax * cc, dt)); let ymax = isqrt(fdiv(nmax * a, dt));
            let (mut cbox, mut cin, mut cprim, mut cnz, mut cnzd) = (0u64, 0u64, 0u64, 0u64, 0u64);
            for y in 0..=ymax { for x in -xmax..=xmax {
                if y == 0 && x <= 0 { continue; }
                cbox += 1;
                let n = a * x * x + 2 * bb * x * y + cc * y * y;
                if n < un[0].0 || n > nmax { continue; }
                if !un.iter().any(|&(lo, hi)| n >= lo && n <= hi) { continue; }
                cin += 1;
                if gcd(x.abs(), y) != 1 { continue; }
                cprim += 1;
                let mut v = [0 as I; 5]; for i in 0..5 { v[i] = x * b[0][i] + y * b[1][i]; }
                if v.iter().any(|&e| e == 0) { continue; }
                cnz += 1;
                let mut av = [v[0].abs(), v[1].abs(), v[2].abs(), v[3].abs(), v[4].abs()]; av.sort();
                if av[0] == av[1] || av[1] == av[2] || av[2] == av[3] || av[3] == av[4] { continue; }
                cnzd += 1;
            } }
            t_box += cbox; t_in += cin; t_prim += cprim; t_nz += cnz; t_nzd += cnzd;
            let da = &mut d1agg[c.first_hi]; da[13] += 1; da[14] += cnzd; da[15] += cbox; da[16] += cin; da[17] += cprim;
            ctsv.push_str(&format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n", idx, c.first_hi, c.first_ci, c.g3, c.members, c.ranges.len(), un.len(), cbox, cin, cprim, cnz, cnzd));
        }
        say!("LEAF CLASSES {} | critical classes {} | classes with real nonempty window {} | with nonempty integer range {}", ncls, ncrit_cls, nreal, nint);
        say!("LINES box {} inwindow {} primitive {} nonzero {} nonzero+distinct (lines checked) {}", t_box, t_in, t_prim, t_nz, t_nzd);
        let mut dtsv = String::from("d1\td2_old\td2_surv\treps\tball\tcand\tpass\tgcdrej\tei\tgreedyrej\trows\tleaves\tcrit\tnonempty_noncrit\tt4classes\tlines\tbox\tinwin\tprim\n");
        for (hi, a) in d1agg.iter().enumerate() { dtsv.push_str(&format!("{}\t{}\n", hi, a[0..18].iter().map(|x| x.to_string()).collect::<Vec<_>>().join("\t"))); }
        fs::write(format!("{}/inv_d1.tsv", log_dir), dtsv).unwrap();
        fs::write(format!("{}/inv_reps.tsv", log_dir), reptsv).unwrap();
        fs::write(format!("{}/inv_classes.tsv", log_dir), ctsv).unwrap();
    }
    if real {
        // ===== T4 class tables for the classes whose first leaf lies under a depth-1 node in L5V3_D1 (global class ids = first-occurrence order over ALL reps)
        let pt4: usize = std::env::var("L5V3_PT4").ok().and_then(|s| s.parse().ok()).unwrap_or(100);
        let mut t4tsv = String::from("cid\tfirst_hi\tfirst_rep\tmembers\tnranges\trows\tbox\tell\tinrange\tprim\tlines\n");
        let mut tot = [0u64; 6]; let mut ncls_all = [0u64; 26]; let mut mine: Vec<(usize, Vec<I>)> = vec![]; let mut nr_tot = 0usize;
        for (cid, c) in cls3.iter().enumerate() {
            ncls_all[c.first_hi] += 1;
            if !d1set.contains(&c.first_hi) { continue; }
            let rg = merge_ranges_v(c.ranges.clone()); let ls = lines_stats(&c.k, &rg);
            for z in 0..6 { tot[z] += ls[z]; }
            t4tsv.push_str(&format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n", cid, c.first_hi, c.first_rep, c.members, rg.len(), ls[0], ls[1], ls[2], ls[3], ls[4], ls[5]));
            let p = right_inverse(&c.l).expect("right inverse"); let a = gram(&c.k); let gd = det(&a); let ad = adjm(&a);
            let mut q = vec![vec![0 as I; 5]; 2];
            for i in 0..2 { for col in 0..5 {
                let mut xv = [0 as I; 5]; xv[col] = 1; for j in 0..3 { let hj = c.l[j][col]; for r in 0..5 { xv[r] -= p[j][r] * hj; } }
                let w2: Vec<I> = c.k.iter().map(|b| dot(b, &xv)).collect(); let mut s = 0; for k in 0..2 { s += ad[i][k] * w2[k]; }
                assert!(s % gd == 0, "Q not integral"); q[i][col] = s / gd; } }
            // mirror asserts: H B = 0 and B Q + P H = I
            for h in &c.l { for b in &c.k { assert_eq!(dot(h, b), 0); } }
            for i in 0..5 { for j in 0..5 { let mut s = 0; for a2 in 0..2 { s += c.k[a2][i] * q[a2][j]; } for a2 in 0..3 { s += p[a2][i] * c.l[a2][j]; } assert_eq!(s, if i == j { 1 } else { 0 }); } }
            let mut d: Vec<I> = vec![cid as I];
            for i in 0..5 { d.push(c.g.p[i] as I); } for i in 0..5 { d.push(c.g.e[i] as I); }
            for r in &c.l { d.extend_from_slice(r); } for r in &c.k { d.extend_from_slice(r); }
            for r in &q { d.extend_from_slice(r); } for r in &p { d.extend_from_slice(r); }
            d.push(rg.len() as I); for &(x, y) in &rg { d.push(x); d.push(y); }
            nr_tot += rg.len(); mine.push((cid, d));
        }
        let d1tag = d1set.iter().map(|x| x.to_string()).collect::<Vec<_>>().join("_");
        let nmod = (mine.len() + pt4 - 1) / pt4;
        for j in 0..nmod {
            let sl = &mine[j * pt4..((j + 1) * pt4).min(mine.len())];
            let mut body = String::new();
            for (k, (_, d)) in sl.iter().enumerate() { body.push_str(&rec_hex(d, 32)); body.push_str(if k + 1 < sl.len() { ",\n" } else { "\n" }); }
            let txt = format!("/-\n# L5S4.GD3T{d1}C{j} : flat T4 class records (depth-1 node(s) {d1}), module {j}; classes with global ids {lo}..{hi} among the listed (WRITTEN-UNCHECKED, format of FORMAT_NOTES.md section T4)\n-/\nimport LRSpectrumFull.L5S4.GD3F1\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace T4D{d1}\n\ndef t4blobs_{j} : List ℕ := [\n{body}]\n\n-- `t4OkF` is the class-record check specified in FORMAT_NOTES.md (not yet in Lean)\ntheorem t4ok_{j} : (t4blobs_{j}.all fun N => t4OkF (dg N)) = true := by decide +kernel\n\nend T4D{d1}\nend L5S4\nend LRSpectrumFull\n", d1 = d1tag, j = j, lo = sl[0].0, hi = sl[sl.len() - 1].0, body = body);
            wr!(format!("{}/GD3T{}C{}.lean", lean_dir, d1tag, j), txt);
        }
        fs::write(format!("{}/t4_classes_d1_{}.tsv", log_dir, d1tag), &t4tsv).unwrap();
        say!("T4 global classes {} (per first depth-1 node {:?}); emitted {} classes of d1 {} in {} modules, ranges {}, lines stats rows {} box {} ellipse {} inrange {} prim {} lines {}", cls3.len(), ncls_all, mine.len(), d1tag, nmod, nr_tot, tot[0], tot[1], tot[2], tot[3], tot[4], tot[5]);
    }
    if mode == "v3" || mode == "v3count" { fs::write(format!("{}/v3_{}.tsv", log_dir, mode), &v3tsv).unwrap(); fs::write(format!("{}/v3_crit_{}.tsv", log_dir, mode), &v3crit).unwrap(); }
    if mode == "dumpnode" { fs::write(format!("{}/dump.txt", log_dir), &dump).unwrap(); }
    say!("TOTAL reps {} ball {} greedy-cand {} pass {} rows {} modules {} files {} bytes {} wide-leaf-modules {}", tot[5], tot[0], tot[1], tot[2], tot[3], tot[4], nfiles, nbytes, wide);
    fs::write(format!("{}/stats_{}.tsv", log_dir, mode), &tsv).unwrap();
    fs::write(format!("{}/gen_{}.log", log_dir, mode), &log).unwrap();
}
