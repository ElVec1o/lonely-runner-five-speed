// cert-v2 prototype: generator and checker for the pruned five-speed tree (exact integer/rational arithmetic only).
use super::*;
use std::collections::{HashMap, HashSet};
use std::fs;

pub struct Wr(pub Vec<u8>);
impl Wr {
    fn u8(&mut self, x: u8) { self.0.push(x); }
    fn u32(&mut self, x: u32) { self.0.extend_from_slice(&x.to_le_bytes()); }
    fn i32(&mut self, x: i32) { self.0.extend_from_slice(&x.to_le_bytes()); }
    fn g(&mut self, g: &G) { for i in 0..5 { self.u8(g.p[i]); } for i in 0..5 { self.u8(g.e[i] as u8); } }
    fn v5(&mut self, v: &V5) { for i in 0..5 { self.i32(v[i] as i32); } }
    fn mat(&mut self, m: &Vec<Vec<I>>) { for r in m { for &x in r { self.i32(x as i32); } } }
}
pub struct Rd<'a>(pub &'a [u8], pub usize);
impl<'a> Rd<'a> {
    fn u8(&mut self) -> u8 { let x = self.0[self.1]; self.1 += 1; x }
    fn u32(&mut self) -> u32 { let x = u32::from_le_bytes(self.0[self.1..self.1 + 4].try_into().unwrap()); self.1 += 4; x }
    fn i32(&mut self) -> i32 { self.u32() as i32 }
    fn g(&mut self) -> G { let mut p = [0u8; 5]; let mut e = [0i8; 5]; for i in 0..5 { p[i] = self.u8(); } for i in 0..5 { e[i] = self.u8() as i8; } G { p, e } }
    fn v5(&mut self) -> V5 { let mut v = [0 as I; 5]; for i in 0..5 { v[i] = self.i32() as I; } v }
    fn mat(&mut self, r: usize, c: usize) -> Vec<Vec<I>> { (0..r).map(|_| (0..c).map(|_| self.i32() as I).collect()).collect() }
    fn done(&self) -> bool { self.1 == self.0.len() }
}
pub fn fnv(b: &[u8]) -> u64 { let mut h: u64 = 0xcbf29ce484222325; for &x in b { h ^= x as u64; h = h.wrapping_mul(0x100000001b3); } h }

fn solve_u(t: &[V5], b: &[V5]) -> Option<Vec<Vec<I>>> {
    let r = t.len();
    let gm: Vec<Vec<I>> = (0..r).map(|i| (0..r).map(|j| dot(&b[i], &b[j])).collect()).collect();
    let mx: Vec<Vec<I>> = (0..r).map(|i| (0..r).map(|j| dot(&t[i], &b[j])).collect()).collect();
    let d = det(&gm); let ad = adjm(&gm);
    let mut u = vec![vec![0 as I; r]; r];
    for i in 0..r { for j in 0..r { let mut s = 0; for k in 0..r { s += mx[i][k] * ad[k][j]; } if s % d != 0 { return None; } u[i][j] = s / d; } }
    if check_u(t, b, &u) { Some(u) } else { None }
}
fn check_u(t: &[V5], b: &[V5], u: &Vec<Vec<I>>) -> bool {
    let r = t.len();
    for i in 0..r { for c in 0..5 { let mut s = 0; for k in 0..r { s += u[i][k] * b[k][c]; } if s != t[i][c] { return false; } } }
    true
}
// lattice equality proof: U and U' with t = U b and b = U' t
fn leq_ok(t: &[V5], b: &[V5], u: &Vec<Vec<I>>, u2: &Vec<Vec<I>>) -> bool { check_u(t, b, u) && check_u(b, t, u2) }
fn gmap(gn: &G, gr: &G, rows: &[V5]) -> Vec<V5> { rows.iter().map(|r| gr.apply_inv(&gn.apply(r))).collect() }

// ---- shared enumeration pieces
pub fn d1_list() -> Vec<(V5, Node)> {
    let m0 = fr(3, 10); let b1 = fr(175, 27).div(fi(4).mul(m0).mul(m0)); let mut d1 = vec![];
    for a0 in 0..=4 { for a1 in a0..=4 { for a2 in a1..=4 { for a3 in a2..=4 { for a4 in a3..=4 {
        let h: V5 = [a0, a1, a2, a3, a4]; let ss: I = h.iter().map(|x| x * x).sum();
        if ss <= 1 { continue; } let mut g = 0; for &x in h.iter() { g = gcd(g, x); } if g != 1 { continue; }
        if !fi(ss).lt(b1) { continue; }
        d1.push((h, child(&root(), &h.to_vec())));
    } } } } }
    d1
}
pub fn d2_surv(n1: &Node, c1: Fr, st: &mut Funnel) -> Vec<(Vec<I>, Node)> {
    let ms = [fr(3, 10), m_of(c1)]; let inv = [fi(0), fr(n1.gs[0], n1.gs[1])];
    let b = radius_bound(&ms, &inv, 2, fr(37, 9), &[0, 1]).unwrap();
    children(n1, b, st).into_iter().map(|t| { let n = child(n1, &t); (t, n) }).collect()
}
pub fn d3_leaves(n2: &Node, c1: Fr, c2: Fr, st: &mut Funnel) -> Vec<(Vec<I>, Node)> {
    let ms = [fr(3, 10), m_of(c1), m_of(c2)]; let inv = [fi(0), fr(n2.gs[0], n2.gs[1]), fr(n2.gs[1], n2.gs[2])];
    let b = radius_bound(&ms, &inv, 3, fr(7, 3), &[0, 1, 2]).unwrap();
    children(n2, b, st).into_iter().map(|t| { let n = child(n2, &t); (t, n) }).collect()
}
// returns (real_nonempty, integer range (lo,hi) inclusive or None, is_crit)
pub fn leaf_info(c: [Fr; 3], n3: &Node, c3: Fr, rho: Fr) -> (bool, Option<(I, I)>, bool) {
    let m3 = m_of(c3); let crit = m3.eq(fi(0));
    let ms = [fr(3, 10), m_of(c[0]), m_of(c[1]), m3];
    let w = leaf_window(&ms, &n3.gs, rho); let g3 = n3.gs[3];
    let ne = match w.hi { None => true, Some(h) => w.lo.lt(h) };
    if crit || !ne { return (ne, None, crit); }
    let hi = w.hi.unwrap();
    let (a, b) = (cdiv(w.lo.n * g3, w.lo.d), cdiv(hi.n * g3, hi.d) - 1);
    (ne, if a <= b { Some((a, b)) } else { None }, crit)
}
pub fn merge_ranges(mut r: Vec<(I, I)>) -> Vec<(I, I)> {
    r.sort(); let mut un: Vec<(I, I)> = vec![];
    for (a, b) in r { if let Some(l) = un.last_mut() { if a <= l.1 + 1 { if b > l.1 { l.1 = b; } continue; } } un.push((a, b)); }
    un
}
pub fn times() -> Vec<(I, I)> { let mut t = vec![]; for q in 5..=60 { for a in 1..=q / 2 { if gcd(a, q) == 1 { t.push((a, q)); } } } t }
#[derive(Default, Clone, Debug)]
pub struct LineStats { pub ell: u64, pub rows: u64, pub box_pts: u64, pub in_range: u64, pub prim: u64, pub lines: u64, pub modops: u64, pub unwit: u64, pub maxlines_class: u64 }
// enumerate lines of class (K basis, merged ranges); callback gets sorted abs tuple and a witness flag
pub fn lines_enum(kb: &Vec<V5>, un: &Vec<(I, I)>, tms: &Vec<(I, I)>, st: &mut LineStats, unw: &mut HashSet<[I; 5]>) {
    if un.is_empty() { return; }
    let mut b = kb.clone(); pair_reduce(&mut b, None);
    let (a, bb, cc) = (dot(&b[0], &b[0]), dot(&b[0], &b[1]), dot(&b[1], &b[1])); let dt = a * cc - bb * bb;
    let nmax = un.last().unwrap().1;
    let xmax = isqrt(fdiv(nmax * cc, dt)); let ymax = isqrt(fdiv(nmax * a, dt));
    let mut cl = 0u64; st.rows += (2 * xmax + 1) as u64;
    for y in 0..=ymax { for x in -xmax..=xmax {
        st.box_pts += 1;
        if y == 0 && x <= 0 { continue; }
        let n = a * x * x + 2 * bb * x * y + cc * y * y;
        if n <= nmax { st.ell += 1; }
        if n < un[0].0 || n > nmax || !un.iter().any(|&(lo, hi)| n >= lo && n <= hi) { continue; }
        st.in_range += 1;
        if gcd(x.abs(), y) != 1 { continue; }
        st.prim += 1;
        let mut v = [0 as I; 5]; for i in 0..5 { v[i] = x * b[0][i] + y * b[1][i]; }
        if v.iter().any(|&e| e == 0) { continue; }
        let mut av = [v[0].abs(), v[1].abs(), v[2].abs(), v[3].abs(), v[4].abs()]; av.sort();
        if av[0] == av[1] || av[1] == av[2] || av[2] == av[3] || av[3] == av[4] { continue; }
        st.lines += 1; cl += 1;
        let mut found = false;
        'tm: for &(ta, tq) in tms { for i in 0..5 { st.modops += 1; let r = (av[i] * ta) % tq; if tq > 5 * r.min(tq - r) { continue 'tm; } } found = true; break; }
        if !found { st.unwit += 1; unw.insert(av); }
    } }
    if cl > st.maxlines_class { st.maxlines_class = cl; }
}
fn ml_time(v: &V5) -> (Fr, I, I) { // best time a/q (q = v_i+v_j) and ML
    let mut best = (fr(0, 1), 0, 1);
    for i in 0..5 { for j in i..5 { let l = v[i] + v[j]; for k in 0..l {
        let mut mn = l; for q in 0..5 { let r = (v[q] * k).rem_euclid(l); mn = mn.min(r.min(l - r)); }
        let c = fr(mn, l); if best.0.lt(c) { best = (c, k, l); }
    } } }
    best
}
// upper bound ML <= c by interval cover of [0,1]
fn cover_ok(v: &V5, c: Fr) -> bool {
    let mut iv: Vec<(Fr, Fr)> = vec![];
    for i in 0..5 { for m in 0..=v[i] {
        let l = fr(m, v[i]).sub(c.div(fi(v[i]))); let r = fr(m, v[i]).add(c.div(fi(v[i])));
        iv.push((l, r));
    } }
    iv.sort_by(|a, b| if a.0.lt(b.0) { std::cmp::Ordering::Less } else if b.0.lt(a.0) { std::cmp::Ordering::Greater } else { std::cmp::Ordering::Equal });
    let mut cur = fi(0); let one = fi(1);
    for (l, r) in iv { if cur.lt(l) { return false; } if cur.lt(r) { cur = r; } if one.le(cur) { return true; } }
    one.le(cur)
}
// integer right inverse of a saturated 3x5 H: columns p_j with H p_j = e_j
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
    // T = hm[:, :r] lower triangular unit diag; P = U[:, :r] T^{-1}
    let mut tinv = vec![vec![0 as I; r]; r];
    for col in 0..r { for i in 0..r { let mut s = if i == col { 1 } else { 0 }; for k in 0..i { s -= hm[i][k] * tinv[k][col]; } tinv[i][col] = s * hm[i][i]; } }
    let mut p: Vec<V5> = vec![];
    for j in 0..r { let mut col = [0 as I; 5]; for k in 0..r { for rr in 0..5 { col[rr] += u[rr][k] * tinv[k][j]; } } p.push(col); }
    for j in 0..r { for i in 0..r { if dot(&h[i], &p[j]) != if i == j { 1 } else { 0 } { return None; } } }
    Some(p)
}
struct Cls { g: G, l: Vec<V5>, k: Vec<V5>, ranges: Vec<(I, I)>, q: Vec<Vec<I>>, p: Vec<V5> }
struct LeafR { x: V5, w: I, flag: u8, cls: u32, gl: G, u: Vec<Vec<I>>, u2: Vec<Vec<I>>, ck: u8 }
fn crit_basis(kind: u8) -> Vec<V5> { if kind == 0 { vec![[1, 2, 3, 4, 0], [0, 0, 0, 0, 1]] } else { vec![[1, 3, 4, 7, 0], [0, 0, 0, 0, 1]] } }

pub fn gen(dir: &str, rho: Fr) {
    fs::create_dir_all(dir).unwrap();
    let perms = all_perms(); let tms = times();
    let mut man = String::new(); let mut total = 0usize;
    let mut save = |name: &str, w: &Wr, man: &mut String, total: &mut usize| { fs::write(format!("{}/{}", dir, name), &w.0).unwrap(); man.push_str(&format!("{} {} {:016x}\n", name, w.0.len(), fnv(&w.0))); *total += w.0.len(); };
    let d1 = d1_list();
    // ---- T1
    let mut t1 = Wr(vec![]); t1.u32(d1.len() as u32);
    let mut c1s: Vec<Fr> = vec![];
    for (h, _) in &d1 { let (_, w) = mlat(&[*h], true); let w = w.unwrap(); t1.v5(h); t1.v5(&w.x); t1.u32(w.w as u32); c1s.push(witness_ok(&[*h], &w.x, w.w).unwrap()); }
    save("t1.bin", &t1, &mut man, &mut total);
    // ---- T2 (survivors) and classes
    struct S2 { hi: usize, t: Vec<I>, x: V5, w: I, cls: u32, gn: G, u: Vec<Vec<I>>, u2: Vec<Vec<I>>, c2: Fr }
    let mut surv: Vec<S2> = vec![]; let mut cmap: HashMap<Vec<i64>, u32> = HashMap::new();
    struct C2 { hi: usize, t: Vec<I>, g: G, l: Vec<V5>, node: Node, c2: Fr }
    let mut cls2: Vec<C2> = vec![]; let mut st2 = Funnel::default();
    for (hi, (h, n1)) in d1.iter().enumerate() {
        let mut q1 = [[0 as I; 5]; 5]; for i in 0..5 { for j in 0..5 { q1[i][j] = h[i] * h[j]; } }
        for (t, n2) in d2_surv(n1, c1s[hi], &mut st2) {
            let (_, w) = mlat(&mred(&n2.l), true); let w = w.unwrap(); let c2 = witness_ok(&n2.l, &w.x, w.w).unwrap();
            let q2 = qmat(&n2.b, &n2.adj); let (key, gn) = canon(&[&q1, &q2], &perms);
            let ci = match cmap.get(&key) { Some(&c) => c, None => { let c = cls2.len() as u32; cmap.insert(key, c); cls2.push(C2 { hi, t: t.clone(), g: gn, l: n2.l.clone(), node: n2.clone(), c2 }); c } };
            let rc = &cls2[ci as usize];
            let hh = gmap(&gn, &rc.g, &n2.l);
            let u = solve_u(&hh, &rc.l).expect("depth2 class map U"); let u2 = solve_u(&rc.l, &hh).expect("depth2 class map U'");
            surv.push(S2 { hi, t, x: w.x, w: w.w, cls: ci, gn, u, u2, c2 });
        }
    }
    println!("gen: T1 {} survivors {} classes {}", d1.len(), surv.len(), cls2.len());
    for hi in 0..d1.len() {
        let mut w = Wr(vec![]); let rs: Vec<&S2> = surv.iter().filter(|s| s.hi == hi).collect(); w.u32(rs.len() as u32);
        for s in rs { w.v5(&s.x); w.u32(s.w as u32); w.u32(s.cls); w.g(&s.gn); w.mat(&s.u); w.mat(&s.u2); }
        save(&format!("t2_{:02}.bin", hi), &w, &mut man, &mut total);
    }
    let mut w = Wr(vec![]); w.u32(cls2.len() as u32);
    for c in &cls2 { w.u32(c.hi as u32); for &x in c.t.iter() { w.i32(x as i32); } w.g(&c.g); }
    save("t2c.bin", &w, &mut man, &mut total);
    // ---- T3 leaves
    let mut lcm: HashMap<Vec<i64>, u32> = HashMap::new(); let mut lc: Vec<Cls> = vec![];
    let mut leaves: Vec<Vec<LeafR>> = vec![]; let mut st3 = Funnel::default(); let mut nleaf = 0u64; let mut ncrit = 0u64;
    for c in &cls2 {
        let n1 = &d1[c.hi].1; let mut v: Vec<LeafR> = vec![];
        for (_, n3) in d3_leaves(&c.node, c1s[c.hi], c.c2, &mut st3) {
            let (_, w) = mlat(&mred(&n3.l), true); let w = w.unwrap(); let c3 = witness_ok(&n3.l, &w.x, w.w).unwrap();
            let (ne, rng, crit) = leaf_info([c1s[c.hi], c.c2, c3].map(|x| x), &n3, c3, rho);
            let _ = n1; nleaf += 1;
            let mut lr = LeafR { x: w.x, w: w.w, flag: 0, cls: 0, gl: G { p: [0; 5], e: [1; 5] }, u: vec![], u2: vec![], ck: 0 };
            let q3 = qmat(&n3.b, &n3.adj); let (key, gl) = canon(&[&q3], &perms);
            if crit {
                ncrit += 1; lr.flag = 1; lr.gl = gl;
                let kk = if n3.gs[3] == 30 { 0 } else { 1 }; lr.ck = kk;
                let kb: Vec<V5> = n3.b.clone(); let cb = crit_basis(kk); let mut found = false;
                'fg: for p in perms.iter() { for m in 0..32u32 {
                    let g = G { p: [p[0] as u8, p[1] as u8, p[2] as u8, p[3] as u8, p[4] as u8], e: [0, 1, 2, 3, 4].map(|i| if (m >> i) & 1 == 1 { -1i8 } else { 1i8 }) };
                    let tb: Vec<V5> = kb.iter().map(|b| g.apply(b)).collect();
                    if let (Some(u), Some(u2)) = (solve_u(&tb, &cb), solve_u(&cb, &tb)) { lr.gl = g; lr.u = u; lr.u2 = u2; found = true; break 'fg; }
                } }
                assert!(found, "no g maps critical leaf onto critical basis");
            } else if ne {
                lr.flag = 2; lr.gl = gl;
                let ci = match lcm.get(&key) { Some(&c) => c, None => { let c = lc.len() as u32; lcm.insert(key, c);
                    let lrep = mred(&n3.l); let mut kb = n3.b.clone(); pair_reduce(&mut kb, None);
                    lc.push(Cls { g: gl, l: lrep, k: kb, ranges: vec![], q: vec![], p: vec![] }); c } };
                lr.cls = ci; let rc = &lc[ci as usize];
                let hh = gmap(&gl, &rc.g, &mred(&n3.l));
                lr.u = solve_u(&hh, &rc.l).expect("leaf map U"); lr.u2 = solve_u(&rc.l, &hh).expect("leaf map U'");
                if let Some(r) = rng { lc[ci as usize].ranges.push(r); }
            }
            v.push(lr);
        }
        leaves.push(v);
    }
    println!("gen: leaves {} crit {} classes(real nonempty) {}", nleaf, ncrit, lc.len());
    // class certificate matrices
    for c in lc.iter_mut() {
        c.ranges = merge_ranges(c.ranges.clone());
        let p = right_inverse(&c.l).expect("right inverse"); let a = gram(&c.k); let g = det(&a); let ad = adjm(&a);
        let mut q = vec![vec![0 as I; 5]; 2];
        for i in 0..2 { for col in 0..5 {
            // Q = A^-1 B^T (I - P H) ; (I-PH) e_col = e_col - sum_j p_j (H e_col)_j
            let mut xv = [0 as I; 5]; xv[col] = 1; for j in 0..3 { let hj = c.l[j][col]; for r in 0..5 { xv[r] -= p[j][r] * hj; } }
            let w2: Vec<I> = c.k.iter().map(|b| dot(b, &xv)).collect(); let mut s = 0; for k in 0..2 { s += ad[i][k] * w2[k]; }
            assert!(s % g == 0, "Q not integral"); q[i][col] = s / g;
        } }
        c.q = q; c.p = p;
    }
    // write T3 chunks (100 reps each)
    let mut nchunk = 0;
    for chunk in leaves.chunks(100) {
        let mut w = Wr(vec![]); w.u32(chunk.iter().map(|v| v.len()).sum::<usize>() as u32);
        for v in chunk { for lr in v { w.v5(&lr.x); w.u32(lr.w as u32); w.u8(lr.flag);
            if lr.flag == 2 { w.u32(lr.cls); w.g(&lr.gl); w.mat(&lr.u); w.mat(&lr.u2); }
            if lr.flag == 1 { w.u8(lr.ck); w.g(&lr.gl); w.mat(&lr.u); w.mat(&lr.u2); } } }
        save(&format!("t3_{:03}.bin", nchunk), &w, &mut man, &mut total); nchunk += 1;
    }
    // T4 (classes) chunks of 2000
    let mut ncl = 0;
    let mut unw: HashSet<[I; 5]> = HashSet::new(); let mut ls = LineStats::default();
    for ch in lc.chunks(2000) {
        let mut w = Wr(vec![]); w.u32(ch.len() as u32);
        for c in ch { w.g(&c.g); for r in &c.l { w.v5(r); } for r in &c.k { w.v5(r); } w.mat(&c.q); for p in &c.p { w.v5(p); }
            w.u32(c.ranges.len() as u32); for &(a, b) in &c.ranges { w.u32(a as u32); w.u32(b as u32); }
            lines_enum(&c.k, &c.ranges, &tms, &mut ls, &mut unw); }
        save(&format!("t4_{:03}.bin", ncl), &w, &mut man, &mut total); ncl += 1;
    }
    println!("gen: lines {} modops {} unwit {} distinct unwit {}", ls.lines, ls.modops, ls.unwit, unw.len());
    // T5
    let mut u5: Vec<[I; 5]> = unw.into_iter().collect(); u5.sort();
    let mut w = Wr(vec![]); w.u32(u5.len() as u32);
    for v in &u5 {
        let (ml, a, q) = ml_time(v); w.v5(v);
        if ml.lt(th()) { assert!(cover_ok(v, ml)); w.u8(1); } else { w.u8(0); }
        w.u32(a as u32); w.u32(q as u32); w.u32(ml.n as u32); w.u32(ml.d as u32);
    }
    save("t5.bin", &w, &mut man, &mut total);
    let hdr = format!("cert-v2-prototype rho={}/{} files {} bytes {}\n", rho.n, rho.d, man.lines().count(), total);
    fs::write(format!("{}/manifest.txt", dir), format!("{}{}", hdr, man)).unwrap();
    println!("gen: wrote {} files, {} bytes to {}", man.lines().count() + 1, total, dir);
}

#[derive(Default, Debug)]
pub struct Ops { pub per_class: Vec<(u64, u64, u64)>, pub per_rep: Vec<(u64, u64, u64)>, pub t4_max_ranges: usize, pub box2: u64, pub box3: u64, pub greedy_it: u64, pub ball2: u64, pub prim2: u64, pub ball3: u64, pub prim3: u64, pub rec_t1: u64, pub rec_t2: u64, pub rec_t3: u64, pub rec_crit: u64, pub rec_t3map: u64, pub rec_t4: u64, pub rec_t5: u64, pub lines: LineStats }

// ---- l5s4e taps: emit Lean data lines (bounded output)
fn compose_g(gn: &G, gr: &G) -> ([u8; 5], [I; 5]) { let mut p = [0u8; 5]; let mut e = [0 as I; 5]; for k in 0..5 { let j = gr.p[k] as usize; p[j] = gn.p[k]; e[j] = gr.e[k] as I * gn.e[k] as I; } (p, e) }
fn l_v5(v: &V5) -> String { format!("![{}, {}, {}, {}, {}]", v[0], v[1], v[2], v[3], v[4]) }
fn l_g(p: &[u8; 5], e: &[I; 5]) -> String { format!("(![{}, {}, {}, {}, {}], ![{}, {}, {}, {}, {}])", p[0], p[1], p[2], p[3], p[4], e[0], e[1], e[2], e[3], e[4]) }
fn l_mat(m: &Vec<Vec<I>>) -> String { let rows: Vec<String> = m.iter().map(|r| format!("[{}]", r.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "))).collect(); format!("[{}]", rows.join(", ")) }
fn l_rows(l: &[V5]) -> String { format!("[{}]", l.iter().map(|v| l_v5(v)).collect::<Vec<_>>().join(", ")) }
fn pair_reduce_steps(b: &mut Vec<V5>) -> Vec<(usize, usize, I)> {
    let mut steps = vec![]; let k = b.len();
    loop { let mut imp = false;
        for i in 0..k { for j in 0..k { if i == j { continue; }
            let nj = dot(&b[j], &b[j]); if nj == 0 { continue; }
            let q = rdiv(dot(&b[i], &b[j]), nj);
            if q != 0 { let mut nw = b[i]; for c in 0..5 { nw[c] -= q * b[j][c]; }
                if dot(&nw, &nw) < dot(&b[i], &b[i]) { b[i] = nw; imp = true; steps.push((i, j, q)); } } } }
        if !imp { break; } }
    steps
}
fn emit(f: &str, s: &str) { use std::io::Write; let mut fh = std::fs::OpenOptions::new().create(true).append(true).open(format!("/DEV_TREE/work/l5s4e_gen2/out2/{}", f)).unwrap(); writeln!(fh, "{}", s).unwrap(); }

include!("genchild.rs");

pub fn check(dir: &str, plant: u32, rho: Fr, flipbyte: bool) -> Result<Ops, String> {
    let perms = all_perms(); let _ = perms; let tms = times();
    let man = fs::read_to_string(format!("{}/manifest.txt", dir)).map_err(|e| e.to_string())?;
    let mut files: HashMap<String, Vec<u8>> = HashMap::new();
    for l in man.lines().skip(1) {
        let p: Vec<&str> = l.split(' ').collect();
        let mut b = fs::read(format!("{}/{}", dir, p[0])).map_err(|e| format!("{}: {}", p[0], e))?;
        if flipbyte && p[0] == "t3_000.bin" { let n = b.len() / 2; b[n] ^= 1; }
        if b.len().to_string() != p[1] || format!("{:016x}", fnv(&b)) != p[2] { return Err(format!("checksum/size mismatch in {}", p[0])); }
        files.insert(p[0].to_string(), b);
    }
    let mut ops = Ops::default();
    // ---- T1
    let d1 = d1_list(); let b1 = files.get("t1.bin").ok_or("no t1")?; let mut r = Rd(b1, 0);
    if r.u32() as usize != d1.len() { return Err("T1 count".into()); }
    let mut c1s = vec![]; let mut t1w: Vec<(V5, I)> = vec![];
    for (h, _) in &d1 {
        let hh = r.v5(); let x = r.v5(); let w = r.u32() as I;
        if hh != *h { return Err("T1 vector mismatch".into()); }
        let mut x = x; if plant == 8 && c1s.is_empty() { x[0] += 1; }
        let c = witness_ok(&[*h], &x, w).ok_or("T1 witness")?; if c.lt(th()) { return Err("T1 c1<theta".into()); }
        c1s.push(c); t1w.push((x, w)); ops.rec_t1 += 1;
    }
    // ---- T2c
    let b = files.get("t2c.bin").ok_or("no t2c")?; let mut r = Rd(b, 0); let nc = r.u32() as usize;
    struct Rep { hi: usize, t: Vec<I>, g: G, seen: bool, c2: Fr, node: Option<Node>, rx: V5, rw: I }
    let mut reps: Vec<Rep> = vec![];
    for _ in 0..nc { let hi = r.u32() as usize; let t: Vec<I> = (0..4).map(|_| r.i32() as I).collect(); let g = r.g(); reps.push(Rep { hi, t, g, seen: false, c2: fi(0), node: None, rx: [0; 5], rw: 0 }); }
    // ---- T2
    let mut st2 = Funnel::default(); let mut nsurv = 0; let mut emit_cnt2 = 0usize; let mut emit_cnt3 = 0usize;
    for (hi, (_, n1)) in d1.iter().enumerate() {
        let b = files.get(&format!("t2_{:02}.bin", hi)).ok_or("no t2")?; let mut r = Rd(b, 0); let cnt = r.u32() as usize;
        let sv = d2_surv(n1, c1s[hi], &mut st2);
        if sv.len() != cnt { return Err(format!("T2 stream length mismatch at depth-1 rep {}: loop {} records {}", hi, sv.len(), cnt)); }
        for (t, n2) in sv {
            let mut x = r.v5(); let w = r.u32() as I; let cls = r.u32() as usize; let gn = r.g(); let mut u = r.mat(2, 2); let u2 = r.mat(2, 2);
            if plant == 1 && nsurv == 5 { x[1] += 1; } if plant == 3 && nsurv == 7 { u[0][0] += 1; }
            let c2 = witness_ok(&n2.l, &x, w).ok_or("T2 witness invalid")?; if c2.lt(th()) { return Err("T2 c2<theta".into()); }
            if cls >= reps.len() { return Err("T2 class id".into()); }
            let rp = &mut reps[cls]; if rp.hi != hi { return Err("T2 class depth-1 rep".into()); }
            if rp.t == t { rp.seen = true; rp.c2 = c2; rp.node = Some(n2.clone()); rp.rx = x; rp.rw = w; }
            let rl = if let Some(n) = &rp.node { n.l.clone() } else { // rep not seen yet (rep is first of class so it must be seen first)
                return Err("T2 class rep not yet seen (rep must be first member)".into()); };
            let hh = gmap(&gn, &rp.g, &n2.l);
            if hh[0] != rl[0] && hh[0].iter().zip(rl[0].iter()).any(|(a, b)| *a != -*b) { return Err("T2 chain L1 not preserved".into()); }
            if !leq_ok(&hh, &rl, &u, &u2) { return Err("T2 symmetry map invalid".into()); }
            if hi == 4 && emit_cnt2 < 100 { emit_cnt2 += 1; let (cp, ce) = compose_g(&gn, &rp.g); emit("d2.txt", &format!("  {{ n2 := {}, rep := {}, gp := {}, u := {}, u' := {} }},", l_rows(&n2.l), l_rows(&rl), l_g(&cp, &ce), l_mat(&u), l_mat(&u2))); }
            nsurv += 1; ops.rec_t2 += 1;
        }
        if !r.done() { return Err("T2 leftover records".into()); }
    }
    if reps.iter().any(|r| !r.seen) { return Err("T2c rep not found among survivors".into()); }
    ops.ball2 = st2.ball; ops.prim2 = st2.prim; ops.box2 = st2.box_iters;
    // ---- T4 (class table)
    struct C4 { g: G, l: Vec<V5>, k: Vec<V5>, ranges: Vec<(I, I)> }
    let mut c4: Vec<C4> = vec![]; let mut idx = 0;
    while let Some(b) = files.get(&format!("t4_{:03}.bin", idx)) {
        let mut r = Rd(b, 0); let n = r.u32() as usize;
        for _ in 0..n {
            let g = r.g(); let l: Vec<V5> = (0..3).map(|_| r.v5()).collect(); let k: Vec<V5> = (0..2).map(|_| r.v5()).collect();
            let q = r.mat(2, 5); let p: Vec<V5> = (0..3).map(|_| r.v5()).collect();
            let nr = r.u32() as usize; let mut rg: Vec<(I, I)> = (0..nr).map(|_| { let a = r.u32() as I; let b = r.u32() as I; (a, b) }).collect();
            if plant == 5 && c4.len() < 50 && !rg.is_empty() { let last = rg.len() - 1; rg[last].1 -= 1; }
            // completeness / saturation certificate: H B = 0 and B Q + P H = I
            for hr in &l { for bk in &k { if dot(hr, bk) != 0 { return Err("T4 H B != 0".into()); } } }
            for i in 0..5 { for j in 0..5 { let mut s = 0; for a in 0..2 { s += k[a][i] * q[a][j]; } for a in 0..3 { s += p[a][i] * l[a][j]; } if s != if i == j { 1 } else { 0 } { return Err("T4 B Q + P H != I".into()); } } }
            ops.rec_t4 += 1; c4.push(C4 { g, l, k, ranges: rg });
        }
        idx += 1;
    }
    // ---- T3
    let mut st3 = Funnel::default(); let mut crit_kinds = [0u64; 2]; let mut nleaf = 0u64; let mut cur_chunk = 0usize;
    let mut rd: Option<Rd> = None; let mut remaining = 0u32;
    for (ci, rp) in reps.iter().enumerate() {
        if ci % 100 == 0 {
            if let Some(rr) = &rd { if remaining != 0 || !rr.done() { return Err("T3 chunk leftover records".into()); } }
            let b = files.get(&format!("t3_{:03}.bin", cur_chunk)).ok_or("no t3 chunk")?; cur_chunk += 1;
            let mut r = Rd(b, 0); remaining = r.u32(); rd = Some(r);
        }
        let r = rd.as_mut().unwrap();
        let n2 = rp.node.as_ref().unwrap();
        let (bx0, gr0) = (st3.box_iters, C_GREEDY.load(Ordering::Relaxed));
        let lv = d3_leaves(n2, c1s[rp.hi], rp.c2, &mut st3);
        ops.per_rep.push((st3.box_iters - bx0, lv.len() as u64, C_GREEDY.load(Ordering::Relaxed) - gr0));
        for (_, n3) in lv {
            if remaining == 0 { return Err("T3 stream too short (record dropped)".into()); }
            remaining -= 1; nleaf += 1; ops.rec_t3 += 1;
            let mut x = r.v5(); let w = r.u32() as I; let flag = r.u8();
            if plant == 2 && nleaf == 100 { x[2] += 1; }
            let c3 = witness_ok(&n3.l, &x, w).ok_or_else(|| format!("T3 witness invalid at leaf {}", nleaf))?;
            if c3.lt(th()) { return Err("T3 c3<theta (fault)".into()); }
            let (ne, rng, crit) = leaf_info([c1s[rp.hi], rp.c2, c3], &n3, c3, rho);
            if crit {
                if flag != 1 { return Err("T3 crit flag missing".into()); }
                let ck = r.u8(); let gl = r.g(); let u = r.mat(2, 2); let u2 = r.mat(2, 2);
                let tb: Vec<V5> = n3.b.iter().map(|b| gl.apply(b)).collect(); let cb = crit_basis(ck);
                if !leq_ok(&tb, &cb, &u, &u2) { return Err("T3 critical identification invalid".into()); }
                let ge: [I; 5] = [gl.e[0] as I, gl.e[1] as I, gl.e[2] as I, gl.e[3] as I, gl.e[4] as I];
                let mut sv: Vec<V5> = vec![];
                for k in 0..3 { 'f: for a in -6..=6i128 { for b2 in -6..=6i128 { for c in -6..=6i128 { for d in -6..=6i128 { for e in -6..=6i128 {
                    let s = [a, b2, c, d, e]; let mut okk = true; for i in 0..3 { if dot(&n3.l[i], &s) != if i == k { 1 } else { 0 } { okk = false; break; } }
                    if okk { sv.push(s); break 'f; } } } } } } }
                let (c1x, c1w) = t1w[rp.hi];
                emit("d3crit.txt", &format!("  {{ rows := {}, b := {}, r := {}, s := {}, x1 := {}, w1 := {}, x2 := {}, w2 := {}, x3 := {}, w3 := {}, ck := {}, gp := {}, u := {}, u' := {} }},", l_rows(&n3.l), l_rows(&n3.b), l_rows(&n3.r), l_rows(&sv), l_v5(&c1x), c1w, l_v5(&rp.rx), rp.rw, l_v5(&x), w, ck, l_g(&gl.p, &ge), l_mat(&u), l_mat(&u2)));
                crit_kinds[ck as usize] += 1; ops.rec_crit += 1;
            } else if ne {
                if flag != 2 { return Err("T3 class map missing for nonempty window".into()); }
                let cls = r.u32() as usize; let mut gl = r.g(); let mut u = r.mat(3, 3); let u2 = r.mat(3, 3);
                if plant == 4 && nleaf == 200 { gl.e[0] = -gl.e[0]; } if plant == 6 && nleaf == 300 { u[1][1] += 1; }
                if cls >= c4.len() { return Err("T3 class id".into()); }
                let hh = gmap(&gl, &c4[cls].g, &mred(&n3.l));
                if !leq_ok(&hh, &c4[cls].l, &u, &u2) { return Err(format!("T3 leaf-to-class map invalid at leaf {}", nleaf)); }
                if let Some((a, b)) = rng { if !c4[cls].ranges.iter().any(|&(lo, hi)| a >= lo && b <= hi) { return Err(format!("T3 leaf window not inside class window at leaf {}", nleaf)); } }
                let mut mm = n3.l.to_vec(); let steps = pair_reduce_steps(&mut mm); if emit_cnt3 < 100 && (!steps.is_empty() || nleaf % 997 == 0) { emit_cnt3 += 1; let (cp, ce) = compose_g(&gl, &c4[cls].g);
                    emit("d3map.txt", &format!("  {{ rows := {}, steps := [{}], gp := {}, cl := {}, u := {}, u' := {} }},", l_rows(&n3.l), steps.iter().map(|(i, j, q)| format!("({}, {}, {})", i, j, q)).collect::<Vec<_>>().join(", "), l_g(&cp, &ce), l_rows(&c4[cls].l), l_mat(&u), l_mat(&u2))); }
                ops.rec_t3map += 1;
            } else if flag != 0 { return Err("T3 spurious flag".into()); }
        }
    }
    if remaining != 0 { return Err("T3 leftover in last chunk".into()); }
    if let Some(rr) = &rd { if !rr.done() { return Err("T3 last chunk leftover bytes".into()); } }
    if crit_kinds[0] + crit_kinds[1] != 8 { return Err(format!("T3 critical leaf count {:?}", crit_kinds)); }
    ops.ball3 = st3.ball; ops.prim3 = st3.prim; ops.box3 = st3.box_iters; ops.greedy_it = C_GREEDY.load(Ordering::Relaxed);
    // ---- lines + T5
    let mut unw: HashSet<[I; 5]> = HashSet::new(); let mut ls = LineStats::default();
    for c in &c4 { let (l0, b0, e0) = (ls.lines, ls.box_pts, ls.ell); lines_enum(&c.k, &c.ranges, &tms, &mut ls, &mut unw); ops.per_class.push((ls.lines - l0, ls.box_pts - b0, ls.ell - e0)); if c.ranges.len() > ops.t4_max_ranges { ops.t4_max_ranges = c.ranges.len(); } }
    let b = files.get("t5.bin").ok_or("no t5")?; let mut r = Rd(b, 0); let n5 = r.u32() as usize; let mut t5: HashSet<[I; 5]> = HashSet::new();
    for _ in 0..n5 {
        let v = r.v5(); let kind = r.u8(); let a = r.u32() as I; let q = r.u32() as I; let cn = r.u32() as I; let cd = r.u32() as I;
        let mut mn = q; for i in 0..5 { let rr = (v[i] * a).rem_euclid(q); mn = mn.min(rr.min(q - rr)); }
        let cmin = fr(mn, q);
        if kind == 0 { if cmin.lt(th()) { return Err("T5 extra witness time invalid".into()); } }
        else { let c = fr(cn, cd); if !cmin.eq(c) || !c.lt(th()) || !cover_ok(&v, c) { return Err("T5 residual ML certificate invalid".into()); } }
        t5.insert(v); ops.rec_t5 += 1;
    }
    let mut missing = unw.iter().filter(|v| !t5.contains(*v)).count();
    if plant == 7 { missing += 1; }
    if missing > 0 { return Err(format!("{} unwitnessed line tuples not covered by T5", missing)); }
    ops.lines = ls;
    Ok(ops)
}

fn rewrite_manifest(dir: &str) {
    let old = fs::read_to_string(format!("{}/manifest.txt", dir)).unwrap(); let mut out = String::new();
    let mut first = true;
    for l in old.lines() {
        if first { out.push_str(l); out.push('\n'); first = false; continue; }
        let name = l.split(' ').next().unwrap(); let b = fs::read(format!("{}/{}", dir, name)).unwrap();
        out.push_str(&format!("{} {} {:016x}\n", name, b.len(), fnv(&b)));
    }
    fs::write(format!("{}/manifest.txt", dir), out).unwrap();
}
pub fn mutate(src: &str, dst: &str, kind: &str) {
    let _ = fs::remove_dir_all(dst); fs::create_dir_all(dst).unwrap();
    for e in fs::read_dir(src).unwrap() { let e = e.unwrap(); fs::copy(e.path(), format!("{}/{}", dst, e.file_name().to_str().unwrap())).unwrap(); }
    let rw = |name: &str, f: &dyn Fn(&mut Vec<u8>)| { let p = format!("{}/{}", dst, name); let mut b = fs::read(&p).unwrap(); f(&mut b); fs::write(&p, b).unwrap(); };
    match kind {
        "drop_t2" => rw("t2_05.bin", &|b| { let c = u32::from_le_bytes(b[0..4].try_into().unwrap()) - 1; b[0..4].copy_from_slice(&c.to_le_bytes()); let n = b.len(); b.truncate(n - 70); }),
        "drop_t3" => rw("t3_007.bin", &|b| {
            let cnt = u32::from_le_bytes(b[0..4].try_into().unwrap()); let mut pos = 4usize; let mut last = 4usize;
            for _ in 0..cnt { last = pos; let flag = b[pos + 24]; pos += 25 + if flag == 2 { 86 } else if flag == 1 { 43 } else { 0 }; }
            b.truncate(last); b[0..4].copy_from_slice(&(cnt - 1).to_le_bytes()); }),
        "t3_witness" => rw("t3_003.bin", &|b| { b[4] ^= 1; }),
        "t4_range" => rw("t4_000.bin", &|b| {
            // class 0: g(10) + 15*4 (L) + 10*4 (K) + 10*4 (Q) + 15*4 (P) = 10+60+40+40+60 = 210 ; then nranges u32, then (lo,hi)
            let nr = u32::from_le_bytes(b[4 + 210..4 + 214].try_into().unwrap()); assert!(nr > 0);
            let off = 4 + 214; let lo = u32::from_le_bytes(b[off..off + 4].try_into().unwrap()) + 1; b[off..off + 4].copy_from_slice(&lo.to_le_bytes());
            let off2 = 4 + 214 + 4; let hi = u32::from_le_bytes(b[off2..off2 + 4].try_into().unwrap()); if hi >= 1 { b[off2..off2 + 4].copy_from_slice(&(hi - 1).to_le_bytes()); } }),
        "t5_drop" => rw("t5.bin", &|b| { let c = u32::from_le_bytes(b[0..4].try_into().unwrap()) - 1; b[0..4].copy_from_slice(&c.to_le_bytes()); let n = b.len(); b.truncate(n - 37); }),
        "t2c_swap" => rw("t2c.bin", &|b| { b[4] ^= 0; let o = 4 + 4 + 16 + 10; /* second class entry t[0] */ b[o] ^= 1; }),
        "t1_h" => rw("t1.bin", &|b| { b[4] ^= 1; }),
        _ => panic!("kind"),
    }
    rewrite_manifest(dst);
}

pub fn model(o: &Ops, dir: &str) {
    let mut sizes: HashMap<String, u64> = HashMap::new();
    for e in fs::read_dir(dir).unwrap() { let e = e.unwrap(); let n = e.file_name().to_str().unwrap().to_string(); let sz = e.metadata().unwrap().len(); let k = if n.starts_with("t2c") { "t2c".to_string() } else { n[..2].to_string() }; *sizes.entry(k).or_default() += sz; }
    let l = &o.lines;
    // primitive integer op counts per row (formulas in the report, section 2)
    let rows: Vec<(&str, u64, u64)> = vec![
        ("T1 depth-1 reps (126 candidates tested, 26 records)", 26, 126 * 20 + 26 * 120),
        ("depth-2 ball loop (box iterations x35)", o.box2, o.box2 * 35),
        ("depth-2 candidate filters (gcd x72, e_i x90, greedy setup x100)", o.ball2, o.ball2 * 72 + o.prim2 * 190),
        ("depth-2 survivor records (witness 44 + node tests 120 + symOk 120 + lift 66)", o.rec_t2, o.rec_t2 * 350),
        ("depth-2 class reps (bounds + node build, 900)", 1965, 1965 * 900),
        ("depth-3 ball loop (box iterations x21)", o.box3, o.box3 * 21),
        ("depth-3 candidate filters (gcd x54, e_i x45, greedy setup x100)", o.ball3, o.ball3 * 54 + o.prim3 * 145),
        ("shortest-vector (greedy) inner iterations x12 (depth 2+3)", o.greedy_it, o.greedy_it * 12),
        ("leaf records (witness 56 + lift 60 + window/tests 320 = 436)", o.rec_t3, o.rec_t3 * 436),
        ("leaf-to-class maps (symOk r=3 240 + subset 20)", o.rec_t3map, o.rec_t3map * 260),
        ("critical leaf identifications", o.rec_crit, o.rec_crit * 400),
        ("class records T4 (H B = 0, B Q + P H = I: 280)", o.rec_t4, o.rec_t4 * 280),
        ("line loops: rows x60 + ellipse points x9 + window-range hits x20 + primitive x80", l.ell, l.rows * 60 + l.ell * 9 + l.in_range * 20 + l.prim * 80 + l.lines * 10),
        ("T5 residual / extra-time tuples (cover check ~10k each)", o.rec_t5, o.rec_t5 * 10_000),
    ];
    let mut tot: u64 = 0;
    println!("KERNEL WORK MODEL (primitive integer ops; 1 mod-op = mul+mod+compare = 3 primitive ops)");
    for (n, c, p) in &rows { println!("  {:<92} count {:>12}  prim ops {:>14}", n, c, p); tot += p; }
    let units = l.modops as f64 + tot as f64 / 3.0;
    println!("  witness mod-ops on lines (fixed list a/q, q<=60, early exit): {} ({:.2} per line over {} lines)", l.modops, l.modops as f64 / l.lines as f64, l.lines);
    println!("  TOTAL primitive ops other than witness mod-ops: {}  ; mod-op-equivalent units = mod-ops + prim/3 = {:.4e}", tot, units);
    for (name, us) in [("mask tables 20 us/unit", 20.0), ("56 us/unit", 56.0), ("92 us/unit", 92.0)] {
        println!("  est kernel time @ {:<24}: {:.2} h total ; lines only {:.2} h ; tree+records {:.2} h", name, units * us / 3.6e9, (l.modops as f64 + (rows[12].2 as f64) / 3.0) * us / 3.6e9, (tot as f64 - rows[12].2 as f64) / 3.0 * us / 3.6e9);
    }
    // chunking: theorems with at most 1e4 lines and at most 2e5 ellipse/box iterations
    let (mut th_l, mut cl, mut ce, mut over) = (0u64, 0u64, 0u64, 0u64); let mut open = false;
    for &(ln, _bx, el) in &o.per_class { if ln > 10_000 { over += 1; }
        if !open || cl + ln > 10_000 || ce + el > 200_000 { th_l += 1; cl = 0; ce = 0; open = true; } cl += ln; ce += el; }
    let (mut th_t, mut cb, mut cleaf, mut open2) = (0u64, 0u64, 0u64, false);
    for &(bx, lv, _) in &o.per_rep { if !open2 || cb + bx > 200_000 || cleaf + lv > 20_000 { th_t += 1; cb = 0; cleaf = 0; open2 = true; } cb += bx; cleaf += lv; }
    let max_cl = o.per_class.iter().map(|x| x.0).max().unwrap_or(0); let max_ce = o.per_class.iter().map(|x| x.2).max().unwrap_or(0);
    let max_rb = o.per_rep.iter().map(|x| x.0).max().unwrap_or(0); let max_rl = o.per_rep.iter().map(|x| x.1).max().unwrap_or(0);
    println!("  CHUNKING: line theorems (<=1e4 lines, <=2e5 ellipse points): {} -> {} modules of 8 ; classes alone above 1e4 lines: {} ; largest class: {} lines, {} ellipse points (rectangular box {})", th_l, (th_l + 7) / 8, over, max_cl, max_ce, o.per_class.iter().map(|x| x.1).max().unwrap_or(0));
    println!("  CHUNKING: depth-3 tree theorems (<=2e5 box iterations, <=2e4 leaf records): {} -> {} modules ; largest rep: {} box iterations, {} leaves ; depth-2: {} box iterations in 26 reps -> {} theorems at 2e5", th_t, (th_t + 7) / 8, max_rb, max_rl, o.box2, (o.box2 + 199_999) / 200_000);
    let blobs = (o.rec_t2 + 99) / 100 + (o.rec_t3 + 99) / 100 + (o.rec_t4 + 99) / 100 + 1;
    println!("  BLOB DATA bytes (binary cert, Lean Nat-blob size ~ same): t1 {} t2 {} t2c {} t3 {} t4 {} t5 {} ; total {} ; ~{} blobs of 100 records", sizes.get("t1").unwrap_or(&0), sizes.get("t2").unwrap_or(&0), sizes.get("t2c").unwrap_or(&0), sizes.get("t3").unwrap_or(&0), sizes.get("t4").unwrap_or(&0), sizes.get("t5").unwrap_or(&0), sizes.values().sum::<u64>(), blobs);
    println!("  LARGEST RECORDS: T4 class record with most ranges: {} ranges = {} bytes ; T3 leaf record max 111 bytes ; T2 survivor 70 bytes ; heaviest single kernel unit: class with {} lines / {} ellipse points; rep with {} box iterations / {} leaves", o.t4_max_ranges, 214 + 8 * o.t4_max_ranges, max_cl, max_ce, max_rb, max_rl);
}
