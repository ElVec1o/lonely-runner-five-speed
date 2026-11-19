// WP0a core library: exact integer / rational lattice arithmetic for the pruned five-speed tree.
// No f32/f64 on any decision path (f64 appears only as a seed inside isqrt, corrected exactly).
use std::sync::atomic::{AtomicU64, Ordering};
pub type I = i128;
pub type V5 = [I; 5];

pub static C_BOX: AtomicU64 = AtomicU64::new(0); // ball-box iterations
pub static C_GREEDY: AtomicU64 = AtomicU64::new(0); // inner iterations of shortest-vector checks
pub fn cinc(c: &AtomicU64, k: u64) { c.fetch_add(k, Ordering::Relaxed); }

pub fn gcd(a: I, b: I) -> I { let (mut a, mut b) = (a.abs(), b.abs()); while b != 0 { let t = a % b; a = b; b = t; } a }
pub fn fdiv(a: I, b: I) -> I { a.div_euclid(b) } // b>0
pub fn cdiv(a: I, b: I) -> I { -fdiv(-a, b) }
pub fn rdiv(a: I, b: I) -> I { fdiv(2 * a + b, 2 * b) }
pub fn isqrt(n: I) -> I {
    if n <= 0 { return 0; }
    let mut x = (n as f64).sqrt() as I;
    while x * x > n { x -= 1; }
    while (x + 1) * (x + 1) <= n { x += 1; }
    x
}

#[derive(Clone, Copy, Debug)]
pub struct Fr { pub n: I, pub d: I }
pub fn fr(n: I, d: I) -> Fr { let g = gcd(n, d); let (mut n, mut d) = (n / g, d / g); if d < 0 { n = -n; d = -d; } Fr { n, d } }
pub fn fi(n: I) -> Fr { Fr { n, d: 1 } }
impl Fr {
    pub fn add(self, o: Fr) -> Fr { fr(self.n * o.d + o.n * self.d, self.d * o.d) }
    pub fn sub(self, o: Fr) -> Fr { fr(self.n * o.d - o.n * self.d, self.d * o.d) }
    pub fn mul(self, o: Fr) -> Fr { fr(self.n * o.n, self.d * o.d) }
    pub fn div(self, o: Fr) -> Fr { fr(self.n * o.d, self.d * o.n) }
    pub fn lt(self, o: Fr) -> bool { self.n * o.d < o.n * self.d }
    pub fn le(self, o: Fr) -> bool { self.n * o.d <= o.n * self.d }
    pub fn eq(self, o: Fr) -> bool { self.n * o.d == o.n * self.d }
    pub fn gtz(self) -> bool { self.n > 0 }
    pub fn fmin(self, o: Fr) -> Fr { if o.lt(self) { o } else { self } }
    pub fn fmax(self, o: Fr) -> Fr { if self.lt(o) { o } else { self } }
}

pub fn dot(a: &V5, b: &V5) -> I { let mut s = 0; for i in 0..5 { s += a[i] * b[i]; } s }
pub fn gram(b: &[V5]) -> Vec<Vec<I>> { let k = b.len(); let mut g = vec![vec![0; k]; k]; for i in 0..k { for j in 0..k { g[i][j] = dot(&b[i], &b[j]); } } g }
pub fn minor(m: &Vec<Vec<I>>, r: usize, c: usize) -> Vec<Vec<I>> {
    let n = m.len(); let mut o = Vec::with_capacity(n - 1);
    for i in 0..n { if i == r { continue; } let mut row = Vec::with_capacity(n - 1); for j in 0..n { if j != c { row.push(m[i][j]); } } o.push(row); }
    o
}
pub fn det(m: &Vec<Vec<I>>) -> I {
    let n = m.len();
    match n {
        0 => 1, 1 => m[0][0],
        2 => m[0][0] * m[1][1] - m[0][1] * m[1][0],
        _ => { let mut s = 0; for c in 0..n { if m[0][c] == 0 { continue; } let v = m[0][c] * det(&minor(m, 0, c)); if c % 2 == 0 { s += v } else { s -= v } } s }
    }
}
pub fn adjm(m: &Vec<Vec<I>>) -> Vec<Vec<I>> {
    let n = m.len(); if n == 1 { return vec![vec![1]]; }
    let mut a = vec![vec![0; n]; n];
    for i in 0..n { for j in 0..n { let v = det(&minor(m, i, j)); a[j][i] = if (i + j) % 2 == 0 { v } else { -v }; } }
    a
}
pub fn ident(d: usize) -> Vec<Vec<I>> { let mut m = vec![vec![0; d]; d]; for i in 0..d { m[i][i] = 1; } m }

// ---------------------------------------------------------------- nodes
#[derive(Clone)]
pub struct Node {
    pub j: usize,            // rank of L_j
    pub b: Vec<V5>,          // basis of K_j = L_j^perp cap Z^5   (5-j vectors)
    pub r: Vec<V5>,          // right inverse columns: b_i . r_k = delta
    pub a: Vec<Vec<I>>,      // Gram of b
    pub adj: Vec<Vec<I>>,    // adjugate of a
    pub gs: Vec<I>,          // G_0=1, G_1..G_j  (Gram det of L_i = Gram det of K_i)
    pub l: Vec<V5>,          // chain basis h_1..h_j of L_j
}
impl Node { pub fn d(&self) -> usize { 5 - self.j } pub fn g(&self) -> I { *self.gs.last().unwrap() } }
pub fn root() -> Node {
    let mut b = vec![]; for i in 0..5 { let mut e = [0; 5]; e[i] = 1; b.push(e); }
    Node { j: 0, r: b.clone(), b, a: ident(5), adj: ident(5), gs: vec![1], l: vec![] }
}

pub fn pair_reduce(b: &mut Vec<V5>, mut r: Option<&mut Vec<V5>>) {
    let k = b.len();
    loop {
        let mut imp = false;
        for i in 0..k { for j in 0..k {
            if i == j { continue; }
            let nj = dot(&b[j], &b[j]); if nj == 0 { continue; }
            let q = rdiv(dot(&b[i], &b[j]), nj);
            if q != 0 {
                let mut nw = b[i]; for c in 0..5 { nw[c] -= q * b[j][c]; }
                if dot(&nw, &nw) < dot(&b[i], &b[i]) {
                    b[i] = nw; imp = true;
                    if let Some(rr) = r.as_mut() { let ri = rr[i]; for c in 0..5 { rr[j][c] += q * ri[c]; } }
                }
            }
        } }
        if !imp { break; }
    }
}

pub fn lift(nd: &Node, t: &[I]) -> V5 {
    let mut y = [0; 5];
    for i in 0..nd.d() { for c in 0..5 { y[c] += t[i] * nd.r[i][c]; } }
    for _ in 0..2 { for i in (0..nd.j).rev() {
        let n = dot(&nd.l[i], &nd.l[i]); let q = rdiv(dot(&y, &nd.l[i]), n);
        if q != 0 { for c in 0..5 { y[c] -= q * nd.l[i][c]; } }
    } }
    y
}

pub fn child(nd: &Node, t: &Vec<I>) -> Node {
    let d = nd.d();
    let mut p = ident(d); let mut pinv = ident(d); let mut tt = t.clone();
    let mut piv;
    loop {
        piv = usize::MAX;
        for i in 0..d { if tt[i] != 0 && (piv == usize::MAX || tt[i].abs() < tt[piv].abs()) { piv = i; } }
        let mut any = false;
        for i in 0..d {
            if i != piv && tt[i] != 0 {
                let q = tt[i] / tt[piv]; tt[i] -= q * tt[piv];
                for c in 0..d { let v = p[piv][c]; p[i][c] -= q * v; }
                for rr in 0..d { let v = pinv[rr][i]; pinv[rr][piv] += q * v; }
                if tt[i] != 0 { any = true; }
            }
        }
        if !any { break; }
    }
    assert!(tt[piv].abs() == 1, "t not primitive");
    if piv != 0 { p.swap(0, piv); for rr in 0..d { pinv[rr].swap(0, piv); } tt.swap(0, piv); }
    if tt[0] == -1 { for c in 0..d { p[0][c] = -p[0][c]; } for rr in 0..d { pinv[rr][0] = -pinv[rr][0]; } }
    let mut nb: Vec<V5> = vec![]; let mut nr: Vec<V5> = vec![];
    for k in 0..d - 1 {
        let mut bv = [0; 5]; let mut rv = [0; 5];
        for i in 0..d { let nik = p[k + 1][i]; let mik = pinv[i][k + 1];
            for c in 0..5 { bv[c] += nik * nd.b[i][c]; rv[c] += mik * nd.r[i][c]; } }
        nb.push(bv); nr.push(rv);
    }
    pair_reduce(&mut nb, Some(&mut nr));
    let a = gram(&nb); let g = det(&a); let adj = adjm(&a);
    let y = lift(nd, t);
    let mut l = nd.l.clone(); l.push(y);
    let mut gs = nd.gs.clone(); gs.push(g);
    Node { j: nd.j + 1, b: nb, r: nr, a, adj, gs, l }
}

pub fn exists_shorter(g: &Vec<Vec<I>>, bound: I) -> bool {
    let k = g.len(); let dt = det(g); let ad = adjm(g);
    let mut mx = vec![0 as I; k];
    for i in 0..k { mx[i] = isqrt(((bound - 1).max(0) * ad[i][i]) / dt); }
    let mut c: Vec<I> = mx.iter().map(|m| -m).collect();
    let mut it = 0u64;
    loop {
        it += 1;
        if c.iter().any(|&x| x != 0) {
            let mut q = 0; for i in 0..k { for j in 0..k { q += g[i][j] * c[i] * c[j]; } }
            if q < bound { cinc(&C_GREEDY, it); return true; }
        }
        let mut i = 0;
        loop { if i == k { cinc(&C_GREEDY, it); return false; } if c[i] < mx[i] { c[i] += 1; break; } else { c[i] = -mx[i]; i += 1; } }
    }
}

// necessary greedy conditions of the chain L_1 < ... < L_{j+1} (the new lattice is nd.l + [y]); j+1 = 2 or 3
pub fn greedy_ok(nd: &Node, t: &[I]) -> bool {
    if nd.j == 0 { return true; }
    let y = lift(nd, t);
    let mut l = nd.l.clone(); l.push(y);
    let g = gram(&l);
    let a = g[0][0];
    if exists_shorter(&g, a) { return false; }
    if nd.j == 2 {
        let s = vec![vec![a * g[1][1] - g[0][1] * g[0][1], a * g[1][2] - g[0][1] * g[0][2]],
                     vec![a * g[1][2] - g[0][1] * g[0][2], a * g[2][2] - g[0][2] * g[0][2]]];
        if exists_shorter(&s, s[0][0]) { return false; }
    }
    true
}
pub fn ei_bad(nd: &Node, t: &[I]) -> bool {
    let d = nd.d();
    for i in 0..5 {
        let row: Vec<I> = (0..d).map(|k| nd.b[k][i]).collect();
        let mut par = true;
        'o: for a in 0..d { for b in a + 1..d { if row[a] * t[b] != row[b] * t[a] { par = false; break 'o; } } }
        if par { return true; }
    }
    false
}

#[derive(Default, Clone, Debug)]
pub struct Funnel { pub box_iters: u64, pub ball: u64, pub prim: u64, pub ei: u64, pub greedy: u64, pub pass: u64 }

fn rec_box(i: usize, d: usize, tmax: &[I], t: &mut Vec<I>, started: bool, f: &mut dyn FnMut(&Vec<I>)) {
    if i == d { if started { f(t); } return; }
    let lo = if started { -tmax[i] } else { 0 };
    for v in lo..=tmax[i] { t[i] = v; rec_box(i + 1, d, tmax, t, started || v != 0, f); }
    t[i] = 0;
}
// children t (first nonzero positive, primitive, no e_i, greedy) with mu^2 < bound (bound = rational > 0)
pub fn children(nd: &Node, bound: Fr, st: &mut Funnel) -> Vec<Vec<I>> {
    let d = nd.d(); let g = nd.g();
    let tmax: Vec<I> = (0..d).map(|i| isqrt(fdiv(bound.n * nd.a[i][i], bound.d))).collect();
    let mut out = vec![]; let mut t = vec![0 as I; d];
    let adj = nd.adj.clone();
    let mut iters = 0u64;
    {
        let mut f = |t: &Vec<I>| {
            iters += 1;
            let mut q = 0; for i in 0..d { let mut s = 0; for j in 0..d { s += adj[i][j] * t[j]; } q += t[i] * s; }
            if q * bound.d >= bound.n * g { return; }
            st.ball += 1;
            let mut gg = 0; for &x in t.iter() { gg = gcd(gg, x); }
            if gg != 1 { return; }
            st.prim += 1;
            if ei_bad(nd, t) { st.ei += 1; return; }
            if !greedy_ok(nd, t) { st.greedy += 1; return; }
            st.pass += 1; out.push(t.clone());
        };
        rec_box(0, d, &tmax, &mut t, false, &mut f);
    }
    st.box_iters += iters; cinc(&C_BOX, iters);
    out
}

// ---------------------------------------------------------------- M(L): exact, zonotope gauge
pub struct Wit { pub x: V5, pub w: I }
pub fn mlat(h: &[V5], wit: bool) -> (Fr, Option<Wit>) {
    let r = h.len();
    if r == 0 { return (fr(1, 2), if wit { Some(Wit { x: [1; 5], w: 2 }) } else { None }); }
    let cols: Vec<Vec<I>> = (0..5).map(|i| (0..r).map(|j| h[j][i]).collect()).collect();
    let mut normals: Vec<Vec<I>> = vec![];
    match r {
        1 => normals.push(vec![1]),
        2 => { for c in &cols { if c[0] != 0 || c[1] != 0 { normals.push(vec![-c[1], c[0]]); } } }
        3 => { for i in 0..5 { for j in i + 1..5 { let a = &cols[i]; let b = &cols[j];
            let n = vec![a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
            if n.iter().any(|&x| x != 0) { normals.push(n); } } } }
        _ => panic!("rank"),
    }
    for n in normals.iter_mut() {
        let mut g = 0; for &x in n.iter() { g = gcd(g, x); }
        for x in n.iter_mut() { *x /= g; }
        let first = n.iter().find(|&&x| x != 0).copied().unwrap();
        if first < 0 { for x in n.iter_mut() { *x = -*x; } }
    }
    normals.sort(); normals.dedup();
    let hn: Vec<I> = normals.iter().map(|n| cols.iter().map(|c| { let mut s = 0; for k in 0..r { s += c[k] * n[k]; } s.abs() }).sum()).collect();
    let s: Vec<I> = (0..r).map(|j| h[j].iter().sum()).collect();
    let rl: Vec<I> = (0..r).map(|j| h[j].iter().map(|x| x.abs()).sum()).collect();
    let zlo: Vec<I> = (0..r).map(|j| cdiv(s[j] - rl[j], 2)).collect();
    let zhi: Vec<I> = (0..r).map(|j| fdiv(s[j] + rl[j], 2)).collect();
    let mut z = zlo.clone();
    let (mut bn, mut bd) = (1 as I, 1 as I); let mut bz = z.clone(); let mut have = false;
    loop {
        let p2: Vec<I> = (0..r).map(|j| 2 * z[j] - s[j]).collect();
        let (mut mn, mut md) = (0 as I, 1 as I); let mut worse = false;
        for (ni, n) in normals.iter().enumerate() {
            let mut v = 0; for k in 0..r { v += p2[k] * n[k]; } let v = v.abs(); let dd = 2 * hn[ni];
            if v * md > mn * dd { mn = v; md = dd;
                if have && mn * bd >= bn * md { worse = true; break; } }
        }
        if !worse && (!have || mn * bd < bn * md) { bn = mn; bd = md; bz = z.clone(); have = true; }
        let mut i = 0;
        loop { if i == r { break; } if z[i] < zhi[i] { z[i] += 1; break; } else { z[i] = zlo[i]; i += 1; } }
        if i == r { break; }
    }
    let m = fr(bd - 2 * bn, 2 * bd);
    if !wit { return (m, None); }
    // witness: vertex search
    let p2: Vec<I> = (0..r).map(|j| 2 * bz[j] - s[j]).collect();
    let mut subsets: Vec<Vec<usize>> = vec![];
    fn comb(start: usize, k: usize, cur: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) { if cur.len() == k { out.push(cur.clone()); return; } for i in start..5 { cur.push(i); comb(i + 1, k, cur, out); cur.pop(); } }
    comb(0, r, &mut vec![], &mut subsets);
    for sub in subsets {
        let hs: Vec<Vec<I>> = (0..r).map(|row| sub.iter().map(|&c| h[row][c]).collect()).collect();
        let dt = det(&hs); if dt == 0 { continue; }
        let ad = adjm(&hs);
        let others: Vec<usize> = (0..5).filter(|c| !sub.contains(c)).collect();
        for sm in 0..(1u32 << others.len()) {
            let sg: Vec<I> = (0..others.len()).map(|k| if (sm >> k) & 1 == 1 { -1 } else { 1 }).collect();
            let mut rhs = vec![0 as I; r];
            for row in 0..r { let mut v = bd * p2[row]; for (k, &c) in others.iter().enumerate() { v -= sg[k] * 2 * bn * h[row][c]; } rhs[row] = v; }
            // y_S = adj * rhs / (det * 2bd)
            let mut yn = vec![0 as I; r]; let mut ok = true;
            for i in 0..r { let mut v = 0; for k in 0..r { v += ad[i][k] * rhs[k]; } yn[i] = v; if v.abs() > 2 * bn * dt.abs() { ok = false; } }
            if !ok { continue; }
            let den = 2 * bd * dt.abs(); let sgnd = if dt < 0 { -1 } else { 1 };
            let mut ynum = [0 as I; 5];
            for (i, &c) in sub.iter().enumerate() { ynum[c] = yn[i] * sgnd; }
            for (k, &c) in others.iter().enumerate() { ynum[c] = sg[k] * 2 * bn * dt.abs(); }
            // x = 1/2 + y = (den + 2 ynum) / (2 den)
            let mut xn = [0 as I; 5]; let mut w = 2 * den; let mut g = w;
            for c in 0..5 { xn[c] = den + 2 * ynum[c]; g = gcd(g, xn[c]); }
            for c in 0..5 { xn[c] /= g; } w /= g;
            if let Some(cv) = witness_ok(h, &xn, w) { if cv.eq(m) { return (m, Some(Wit { x: xn, w })); } }
        }
    }
    panic!("no witness found for lattice {:?} M={:?}", h, m);
}
// H x = 0 mod W and all x_i integers mod W; returns c = min_i ||x_i/W||
pub fn witness_ok(h: &[V5], x: &V5, w: I) -> Option<Fr> {
    if w <= 0 { return None; }
    for row in h { let mut s = 0; for i in 0..5 { s += row[i] * x[i]; } if s.rem_euclid(w) != 0 { return None; } }
    let mut mn = w; for i in 0..5 { let xi = x[i].rem_euclid(w); mn = mn.min(xi.min(w - xi)); }
    Some(fr(mn, w))
}

// ---------------------------------------------------------------- signed permutations and canonical keys
pub fn all_perms() -> Vec<[usize; 5]> {
    let mut out = vec![]; let mut p = [0, 1, 2, 3, 4];
    fn rec(k: usize, p: &mut [usize; 5], out: &mut Vec<[usize; 5]>) { if k == 5 { out.push(*p); return; } for i in k..5 { p.swap(k, i); rec(k + 1, p, out); p.swap(k, i); } }
    rec(0, &mut p, &mut out); out.sort(); out
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct G { pub p: [u8; 5], pub e: [i8; 5] }
impl G {
    pub fn apply(&self, x: &V5) -> V5 { let mut y = [0; 5]; for i in 0..5 { y[i] = self.e[i] as I * x[self.p[i] as usize]; } y }
    pub fn apply_inv(&self, x: &V5) -> V5 { let mut y = [0; 5]; for i in 0..5 { y[self.p[i] as usize] = self.e[i] as I * x[i]; } y }
}
pub type Q5 = [[I; 5]; 5];
pub fn qmat(b: &[V5], adj: &Vec<Vec<I>>) -> Q5 {
    let k = b.len(); let mut q = [[0; 5]; 5];
    for i in 0..5 { for j in 0..5 { let mut s = 0; for a in 0..k { for c in 0..k { s += b[a][i] * adj[a][c] * b[c][j]; } } q[i][j] = s; } }
    q
}
pub fn canon(qs: &[&Q5], perms: &Vec<[usize; 5]>) -> (Vec<i64>, G) {
    let nq = qs.len();
    let mut best_abs: Vec<i64> = vec![]; let mut tied: Vec<usize> = vec![];
    let mut v: Vec<i64> = Vec::with_capacity(15 * nq);
    for (pi, p) in perms.iter().enumerate() {
        v.clear();
        for q in qs { for i in 0..5 { for j in i..5 { v.push(q[p[i]][p[j]].abs() as i64); } } }
        if pi == 0 || v < best_abs { best_abs = v.clone(); tied.clear(); tied.push(pi); } else if v == best_abs { tied.push(pi); }
    }
    let mut best: Vec<i64> = vec![]; let mut bg = G { p: [0; 5], e: [1; 5] };
    for &pi in &tied {
        let p = perms[pi];
        for mask in 0..16u32 {
            let eps: [i64; 5] = [1, if mask & 1 == 1 { -1 } else { 1 }, if mask & 2 == 2 { -1 } else { 1 }, if mask & 4 == 4 { -1 } else { 1 }, if mask & 8 == 8 { -1 } else { 1 }];
            v.clear();
            for q in qs { for i in 0..5 { for j in i..5 { v.push(eps[i] * eps[j] * q[p[i]][p[j]] as i64); } } }
            if best.is_empty() || v < best { best = v.clone(); bg = G { p: [p[0] as u8, p[1] as u8, p[2] as u8, p[3] as u8, p[4] as u8], e: [eps[0] as i8, eps[1] as i8, eps[2] as i8, eps[3] as i8, eps[4] as i8] }; }
        }
    }
    (best, bg)
}

// ---------------------------------------------------------------- tests, radii, windows
pub fn th() -> Fr { fr(1, 5) }
pub fn m_of(m: Fr) -> Fr { m.sub(th()) }
// strict upper bound on mu_r^2 from tests k=0..r-1 (ks = list of k to use); ms[k]=m_k ; inv[i]=mu_i^{-2} for i=1..; c = tail constant
pub fn radius_bound(ms: &[Fr], inv: &[Fr], r: usize, c: Fr, ks: &[usize]) -> Option<Fr> {
    let mut best: Option<Fr> = None;
    for &k in ks {
        let mut den = fi(4).mul(ms[k]).mul(ms[k]);
        for i in k + 1..r { den = den.sub(inv[i]); } // inv indexed by i (inv[0] unused)
        if den.gtz() { let cand = c.div(den); best = Some(match best { None => cand, Some(b) => b.fmin(cand) }); }
    }
    best
}
pub struct Window { pub lo: Fr, pub hi: Option<Fr> }
pub fn leaf_window(ms: &[Fr; 4], gs: &[I], rho: Fr) -> Window {
    let mu2 = |i: usize| fr(gs[i], gs[i - 1]); // i=1..3
    let inv = |i: usize| fr(gs[i - 1], gs[i]);
    let mut hi: Option<Fr> = None;
    for k in 0..4 {
        let mut den = fi(4).mul(ms[k]).mul(ms[k]);
        for i in k + 1..=3 { den = den.sub(inv(i)); }
        if den.gtz() { let c = fi(1).div(den); hi = Some(match hi { None => c, Some(h) => h.fmin(c) }); }
    }
    let q = fr(1, 4);
    let l2 = rho.mul(mu2(3));
    let l1 = rho.mul(mu2(2)).sub(q.mul(mu2(3)));
    let l0 = rho.mul(mu2(1)).sub(q.mul(mu2(2).add(mu2(3))));
    Window { lo: l2.fmax(l1).fmax(l0), hi }
}
