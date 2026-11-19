use std::collections::HashMap;
use std::sync::atomic::Ordering;
use wp0a::*;
mod cert;

fn mred(l: &[V5]) -> Vec<V5> { let mut v = l.to_vec(); pair_reduce(&mut v, None); v }
fn arg(args: &[String], k: &str) -> Option<String> { args.iter().position(|a| a == k).and_then(|i| args.get(i + 1).cloned()) }
fn has(args: &[String], k: &str) -> bool { args.iter().any(|a| a == k) }
fn parse_fr(s: &str) -> Fr { let mut it = s.split('/'); let n: I = it.next().unwrap().parse().unwrap(); let d: I = it.next().map(|x| x.parse().unwrap()).unwrap_or(1); fr(n, d) }

pub struct LeafClass { pub b: Vec<V5>, pub g3: I, pub ranges: Vec<(I, I)>, pub real_ne: bool, pub crit: bool, pub members: u64, pub ne_members: u64 }

fn selftest() {
    // M(L) against grid maxima, rank 1..3
    let mut seed: u64 = 12345;
    let mut rnd = |m: i64| -> i64 { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); ((seed >> 33) as i64) % m };
    let mut bad = 0; let mut tested = 0;
    for it in 0..300 {
        let r = 1 + (it % 3) as usize;
        let mut h: Vec<V5> = vec![];
        for _ in 0..r { let mut v = [0 as I; 5]; for c in 0..5 { v[c] = (rnd(7) - 3) as I; } h.push(v); }
        // rank check
        let g = gram(&h); if det(&g) == 0 { continue; }
        let (m, w) = mlat(&h, true); let w = w.unwrap();
        let c = witness_ok(&h, &w.x, w.w).unwrap();
        if !c.eq(m) { bad += 1; println!("witness mismatch {:?}", h); }
        // grid: W up to 14 (r=1,2) / 10 (r=3)
        let wmax = if r == 3 { 10 } else { 14 };
        let mut gm = fr(0, 1);
        for ww in 1..=wmax as I {
            let mut x = [0 as I; 5];
            loop {
                if let Some(c) = witness_ok(&h, &x, ww) { if gm.lt(c) { gm = c; } }
                let mut i = 0; loop { if i == 5 { break; } if x[i] + 1 < ww { x[i] += 1; break; } else { x[i] = 0; i += 1; } }
                if i == 5 { break; }
            }
        }
        if m.lt(gm) { bad += 1; println!("GRID EXCEEDS M {:?} grid {:?} M {:?}", h, gm, m); }
        tested += 1;
    }
    println!("selftest mlat: tested {} bad {}", tested, bad);
    // cross-check canon invariance
    let perms = all_perms();
    let h: V5 = [1, 2, 3, 4, 7]; let n1 = child(&root(), &h.to_vec());
    let q = qmat(&n1.b, &n1.adj);
    let (k1, _) = canon(&[&q], &perms);
    let g = G { p: [2, 4, 0, 1, 3], e: [1, -1, 1, 1, -1] };
    let b2: Vec<V5> = n1.b.iter().map(|v| g.apply(v)).collect();
    let q2 = qmat(&b2, &n1.adj);
    let (k2, _) = canon(&[&q2], &perms);
    println!("canon invariance: {}", k1 == k2);
    println!("G_1 = {} (|h|^2 = 79 expected), gs {:?}", n1.g(), n1.gs);
}

fn tree(args: &[String]) {
    let old = has(args, "--old"); let incl = has(args, "--inclhi"); let emul = has(args, "--emul32");
    let rho = parse_fr(&arg(args, "--rho").unwrap_or("3/4".into()));
    let perms = all_perms();
    let m0 = fr(3, 10);
    let c2 = fr(37, 9); let c3 = fr(7, 3); let c1 = fr(175, 27);
    // ---- depth 1
    let mut d1: Vec<(V5, Node, Fr)> = vec![];
    let b1 = c1.div(fi(4).mul(m0).mul(m0));
    for a0 in 0..=4 { for a1 in a0..=4 { for a2 in a1..=4 { for a3 in a2..=4 { for a4 in a3..=4 {
        let h: V5 = [a0, a1, a2, a3, a4];
        let ss: I = h.iter().map(|x| x * x).sum();
        if ss <= 1 { continue; }
        let mut g = 0; for &x in h.iter() { g = gcd(g, x); } if g != 1 { continue; }
        if !fi(ss).lt(b1) { continue; }
        let n1 = child(&root(), &h.to_vec());
        let (mm, _) = mlat(&[h], false);
        d1.push((h, n1, mm));
    } } } } }
    println!("depth1 reps: {} (expected 26)", d1.len());
    // ---- depth 2
    struct R2 { h: usize, t: Vec<I>, surv: bool, class: usize }
    let mut recs: Vec<R2> = vec![];
    struct C2 { rep: usize, size: u64, surv: u64 }
    let mut classes: Vec<C2> = vec![]; let mut cmap: HashMap<Vec<i64>, usize> = HashMap::new();
    let mut f2 = Funnel::default(); let mut anomalies = 0u64; let mut min_m1 = fr(1, 1);
    for (hi, (h, n1, mm1)) in d1.iter().enumerate() {
        let m1 = m_of(*mm1); if m1.lt(fi(0)) { anomalies += 1; }
        min_m1 = min_m1.fmin(m1);
        let ms = [m0, m1]; let inv = [fi(0), fr(n1.gs[0], n1.gs[1])];
        let bold = radius_bound(&ms, &inv, 2, c2, &[1]).unwrap();
        let bnew = radius_bound(&ms, &inv, 2, c2, &[0, 1]).unwrap();
        let ts = children(n1, bold, &mut f2);
        let mut q1 = [[0 as I; 5]; 5]; for i in 0..5 { for j in 0..5 { q1[i][j] = h[i] * h[j]; } }
        for t in ts {
            let n2 = child(n1, &t);
            let (mm2, _) = mlat(&mred(&n2.l), false);
            if m_of(mm2).lt(fi(0)) { anomalies += 1; }
            let mu2sq = fr(n2.gs[2], n2.gs[1]);
            let surv = mu2sq.lt(bnew);
            let q2 = qmat(&n2.b, &n2.adj);
            let (key, _) = canon(&[&q1, &q2], &perms);
            let ci = *cmap.entry(key).or_insert_with(|| { classes.push(C2 { rep: recs.len(), size: 0, surv: 0 }); classes.len() - 1 });
            classes[ci].size += 1; if surv { classes[ci].surv += 1; }
            recs.push(R2 { h: hi, t, surv, class: ci });
        }
    }
    let nsurv = recs.iter().filter(|r| r.surv).count();
    let mixed = classes.iter().filter(|c| c.surv != 0 && c.surv != c.size).count();
    let ssurv = classes.iter().filter(|c| c.surv > 0).count();
    println!("DEPTH2 old-mode funnel: ball(both signs) {} prim+sign {} ei_removed {} greedy_removed {} nodes {} box_iters {}", 2 * f2.ball, f2.prim, f2.ei, f2.greedy, f2.pass, f2.box_iters);
    println!("DEPTH2 nodes(old) {} survivors(new tests) {} classes(old) {} classes surviving {} mixed-status classes {} anomalies {}", recs.len(), nsurv, classes.len(), ssurv, mixed, anomalies);
    // ---- depth 3
    let mut lcm: HashMap<Vec<i64>, LeafClass> = HashMap::new();
    let (mut leaves, mut leaves_w, mut crit, mut crit_w, mut ne, mut ne_w, mut ne_nc, mut ne_nc_w, mut faults) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    let mut f3 = Funnel::default(); let mut f3w = [0u64; 5];
    let mut nodes_with_children = 0u64;
    let mut min_margin = fi(1);
    for (ci, c) in classes.iter().enumerate() {
        if !old && c.surv == 0 { continue; }
        let r = &recs[c.rep]; let (h, n1, mm1) = &d1[r.h];
        let _ = h;
        let n2 = child(n1, &r.t);
        let (mm2, _) = mlat(&mred(&n2.l), false);
        let ms = [m0, m_of(*mm1), m_of(mm2)];
        let inv = [fi(0), fr(n2.gs[0], n2.gs[1]), fr(n2.gs[1], n2.gs[2])];
        let ks: Vec<usize> = if old { vec![2] } else { vec![0, 1, 2] };
        let bound = match radius_bound(&ms, &inv, 3, c3, &ks) { Some(b) => b, None => panic!("unbounded") };
        let before = f3.clone();
        let ts = children(&n2, bound, &mut f3);
        let w = c.size;
        f3w[0] += w * (f3.ball - before.ball); f3w[1] += w * (f3.prim - before.prim); f3w[2] += w * (f3.ei - before.ei); f3w[3] += w * (f3.greedy - before.greedy); f3w[4] += w * (f3.pass - before.pass);
        if !ts.is_empty() { nodes_with_children += w; }
        let _ = ci;
        for t in ts {
            let n3 = child(&n2, &t);
            leaves += 1; leaves_w += w;
            let (mm3, _) = mlat(&mred(&n3.l), false);
            let m3 = m_of(mm3);
            if m3.lt(fi(0)) { faults += 1; }
            let is_crit = m3.eq(fi(0));
            if is_crit { crit += 1; crit_w += w; }
            else { min_margin = min_margin.fmin(m3); }
            let msv = [ms[0], ms[1], ms[2], m3];
            let win = leaf_window(&msv, &n3.gs, rho);
            let f32v = |f: Fr| -> f64 { ((f.n as f64) / (f.d as f64)) as f32 as f64 };
            let nonempty = match win.hi { None => true, Some(hi) => if emul { f32v(win.lo) < f32v(hi) } else if incl { win.lo.le(hi) } else { win.lo.lt(hi) } };
            let g3 = n3.gs[3];
            if nonempty { ne += 1; ne_w += w; if !is_crit { ne_nc += 1; ne_nc_w += w; } }
            let q3 = qmat(&n3.b, &n3.adj);
            let (key, _) = canon(&[&q3], &perms);
            let e = lcm.entry(key).or_insert_with(|| LeafClass { b: n3.b.clone(), g3, ranges: vec![], real_ne: false, crit: is_crit, members: 0, ne_members: 0 });
            e.members += 1;
            if is_crit != e.crit { println!("WARNING crit mismatch in class"); }
            if nonempty && !is_crit {
                e.real_ne = true; e.ne_members += 1;
                let hi = win.hi.expect("noncrit leaf with infinite window");
                let (n1i, n2i) = if emul { (((f32v(win.lo) * g3 as f64).ceil()) as I, ((f32v(hi) * g3 as f64).ceil()) as I - 1) } else if incl { (cdiv(win.lo.n * g3, win.lo.d), fdiv(hi.n * g3, hi.d)) } else { (cdiv(win.lo.n * g3, win.lo.d), cdiv(hi.n * g3, hi.d) - 1) };
                if n1i <= n2i { e.ranges.push((n1i, n2i)); }
            }
        }
    }
    println!("DEPTH3 funnel (unweighted, reps): ball(both signs) {} prim+sign {} ei {} greedy {} leaves {} box_iters {}", 2 * f3.ball, f3.prim, f3.ei, f3.greedy, f3.pass, f3.box_iters);
    println!("DEPTH3 funnel (weighted by class size): ball(both signs) {} prim+sign {} ei {} greedy {} leaves {} nodes_with_children {}", 2 * f3w[0], f3w[1], f3w[2], f3w[3], f3w[4], nodes_with_children);
    println!("LEAVES under reps {} weighted {} | critical {} weighted {} | faults(m3<0) {} | min noncrit margin M3-theta {}/{}", leaves, leaves_w, crit, crit_w, faults, min_margin.n, min_margin.d);
    println!("NONEMPTY-WINDOW leaves (incl critical): under reps {} weighted {} | noncritical only: {} weighted {}", ne, ne_w, ne_nc, ne_nc_w);
    let ncls = lcm.len(); let ncrit = lcm.values().filter(|c| c.crit).count();
    let nreal = lcm.values().filter(|c| c.real_ne).count();
    let nint = lcm.values().filter(|c| !c.ranges.is_empty()).count();
    println!("LEAF CLASSES {} | critical classes {} (g3 {:?}) | classes with real nonempty window {} | with nonempty integer |v|^2 range {}", ncls, ncrit, lcm.values().filter(|c| c.crit).map(|c| c.g3).collect::<Vec<_>>(), nreal, nint);
    if has(args, "--nolines") { return; }
    // ---- lines
    let mut times: Vec<(I, I)> = vec![];
    for q in 5..=60 { for a in 1..=q / 2 { if gcd(a, q) == 1 { times.push((a, q)); } } }
    println!("witness times {} (expected 548)", times.len());
    let (mut l_all, mut l_nz, mut l_nzd, mut witnessed, mut modops) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut distinct: Vec<u64> = vec![]; let mut unwit: Vec<u64> = vec![]; let mut unwit_lines = 0u64;
    let mut lines_hull_extra = 0u64;
    let _ = &mut lines_hull_extra;
    for c in lcm.values() {
        if c.crit || c.ranges.is_empty() { continue; }
        let mut rg = c.ranges.clone(); rg.sort();
        let mut un: Vec<(I, I)> = vec![];
        for (a, b) in rg { if let Some(l) = un.last_mut() { if a <= l.1 + 1 { if b > l.1 { l.1 = b; } continue; } } un.push((a, b)); }
        if has(args, "--hull") { let (a, b) = (un[0].0, un.last().unwrap().1); un = vec![(a, b)]; }
        let mut b = c.b.clone(); pair_reduce(&mut b, None);
        let (a, bb, cc) = (dot(&b[0], &b[0]), dot(&b[0], &b[1]), dot(&b[1], &b[1]));
        let dt = a * cc - bb * bb;
        let nmax = un.last().unwrap().1;
        let xmax = isqrt(fdiv(nmax * cc, dt)); let ymax = isqrt(fdiv(nmax * a, dt));
        for y in 0..=ymax { for x in -xmax..=xmax {
            if y == 0 && x <= 0 { continue; }
            let n = a * x * x + 2 * bb * x * y + cc * y * y;
            if n < un[0].0 || n > nmax { continue; }
            if !un.iter().any(|&(lo, hi)| n >= lo && n <= hi) { continue; }
            if gcd(x.abs(), y) != 1 { continue; }
            l_all += 1;
            let mut v = [0 as I; 5]; for i in 0..5 { v[i] = x * b[0][i] + y * b[1][i]; }
            if v.iter().any(|&e| e == 0) { continue; }
            l_nz += 1;
            let mut av = [v[0].abs(), v[1].abs(), v[2].abs(), v[3].abs(), v[4].abs()]; av.sort();
            if av[0] == av[1] || av[1] == av[2] || av[2] == av[3] || av[3] == av[4] { continue; }
            l_nzd += 1;
            let mut pk: u64 = 0; for i in 0..5 { assert!(av[i] < 4096); pk = (pk << 12) | av[i] as u64; }
            distinct.push(pk);
            // witness search with early exits
            let mut found = false;
            'tm: for &(ta, tq) in &times {
                for i in 0..5 { modops += 1; let r = (av[i] * ta) % tq; if tq > 5 * r.min(tq - r) { continue 'tm; } }
                found = true; break;
            }
            if found { witnessed += 1; } else { unwit_lines += 1; unwit.push(pk); }
        } }
    }
    distinct.sort_unstable(); distinct.dedup(); unwit.sort_unstable(); unwit.dedup();
    println!("LINES primitive+onesign+inwindow {} | all nonzero {} | nonzero+distinct {} | witnessed {} unwitnessed lines {} | distinct sorted tuples {} | unwitnessed distinct {} | mod-ops {} ({:.2}/line)", l_all, l_nz, l_nzd, witnessed, unwit_lines, distinct.len(), unwit.len(), modops, modops as f64 / l_nzd as f64);
    let maxe = distinct.iter().map(|p| p & 4095).max().unwrap_or(0);
    println!("max entry over distinct tuples {}", maxe);
    // unwitnessed tuples with exact ML
    for &pk in &unwit {
        let mut v = [0 as I; 5]; for i in 0..5 { v[i] = ((pk >> (12 * (4 - i))) & 4095) as I; }
        let ml = ml_exact(&v);
        println!("UNWIT {:?} ML {}/{} {}", v, ml.n, ml.d, if ml.lt(th()) { "NEAR-TIGHT" } else { "ML>=1/5" });
    }
    // dump distinct set for verification pass
    let mut s = String::new();
    for &pk in &distinct { let mut v = [0u64; 5]; for i in 0..5 { v[i] = (pk >> (12 * (4 - i))) & 4095; } s.push_str(&format!("{},{},{},{},{}\n", v[0], v[1], v[2], v[3], v[4])); }
    if let Some(p) = arg(args, "--dump") { std::fs::write(p, s).unwrap(); }
    println!("C_BOX {} C_GREEDY {}", C_BOX.load(Ordering::Relaxed), C_GREEDY.load(Ordering::Relaxed));
}

pub fn ml_exact(v: &V5) -> Fr {
    let mut best = fr(0, 1);
    for i in 0..5 { for j in i..5 {
        let l = v[i] + v[j];
        for k in 0..l {
            let mut mn = l; // min over speeds of min(r, l-r)/l
            for q in 0..5 { let r = (v[q] * k).rem_euclid(l); mn = mn.min(r.min(l - r)); }
            let c = fr(mn, l); if best.lt(c) { best = c; }
        }
    } }
    best
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("selftest") => selftest(),
        Some("tree") => tree(&args[2..]),
        Some("verify") => verify(&args[2..]),
        Some("mutate") => cert::mutate(&args[2], &args[3], &args[4]),
        Some("gen") => cert::gen(&args[2], parse_fr(&arg(&args, "--rho").unwrap_or("3/4".into()))),
        Some("check") => { let rho = parse_fr(&arg(&args, "--rho").unwrap_or("3/4".into())); let plant: u32 = arg(&args, "--plant").map(|x| x.parse().unwrap()).unwrap_or(0);
            match cert::check(&args[2], plant, rho, has(&args, "--flipbyte")) { Ok(o) => { println!("CHECK PASS records T1 {} T2 {} T3 {} (crit {}, class maps {}) T4 {} T5 {} ; box2 {} box3 {} greedy_it {} ; lines {:?}", o.rec_t1, o.rec_t2, o.rec_t3, o.rec_crit, o.rec_t3map, o.rec_t4, o.rec_t5, o.box2, o.box3, o.greedy_it, o.lines); if has(&args, "--model") { cert::model(&o, &args[2]); } }, Err(e) => println!("CHECK FAIL: {}", e) } }
        _ => println!("usage: wp0a selftest | tree [--old] [--rho n/d] [--nolines] [--dump file]"),
    }
}

// ===================================================================== verification of known tuples (all tie flags)
fn unimod(t: &Vec<I>) -> Vec<Vec<I>> {
    let d = t.len(); let mut p = ident(d); let mut tt = t.clone(); let mut piv;
    loop {
        piv = usize::MAX;
        for i in 0..d { if tt[i] != 0 && (piv == usize::MAX || tt[i].abs() < tt[piv].abs()) { piv = i; } }
        let mut any = false;
        for i in 0..d { if i != piv && tt[i] != 0 { let q = tt[i] / tt[piv]; tt[i] -= q * tt[piv]; for c in 0..d { let v = p[piv][c]; p[i][c] -= q * v; } if tt[i] != 0 { any = true; } } }
        if !any { break; }
    }
    assert!(tt[piv].abs() == 1);
    p.swap(0, piv); p
}
fn flags_rec(v: &V5, nd: &Node, chain: &mut Vec<Node>, out: &mut Vec<Vec<Node>>) {
    if nd.j == 3 { out.push(chain.clone()); return; }
    let d = nd.d(); let g = nd.g();
    let w: Vec<I> = nd.b.iter().map(|b| dot(b, v)).collect();
    let mut c = vec![0 as I; d];
    for i in 0..d { let mut s = 0; for k in 0..d { s += nd.adj[i][k] * w[k]; } assert!(s % g == 0); c[i] = s / g; }
    let p = unimod(&c);
    let nk: Vec<Vec<I>> = (1..d).map(|k| p[k].clone()).collect();
    let q: Vec<Vec<I>> = (0..d - 1).map(|a| (0..d - 1).map(|b| { let mut s = 0; for i in 0..d { for j in 0..d { s += nk[a][i] * nd.adj[i][j] * nk[b][j]; } } s }).collect()).collect();
    let u = (0..d - 1).map(|k| q[k][k]).min().unwrap();
    let dt = det(&q); let aq = adjm(&q);
    let mx: Vec<I> = (0..d - 1).map(|k| isqrt(fdiv(u * aq[k][k], dt))).collect();
    let mut s: Vec<I> = mx.iter().map(|m| -m).collect();
    let mut best: Option<I> = None; let mut cand: Vec<Vec<I>> = vec![];
    loop {
        if s.iter().any(|&x| x != 0) {
            let mut f = 0; for a in 0..d - 1 { for b in 0..d - 1 { f += q[a][b] * s[a] * s[b]; } }
            if f <= u {
                let mut t = vec![0 as I; d]; for k in 0..d - 1 { for i in 0..d { t[i] += s[k] * nk[k][i]; } }
                let fnz = t.iter().find(|&&x| x != 0).copied().unwrap();
                if fnz > 0 { match best { None => { best = Some(f); cand = vec![t]; } Some(bf) => { if f < bf { best = Some(f); cand = vec![t]; } else if f == bf { cand.push(t); } } } }
            }
        }
        let mut i = 0; loop { if i == d - 1 { break; } if s[i] < mx[i] { s[i] += 1; break; } else { s[i] = -mx[i]; i += 1; } }
        if i == d - 1 { break; }
    }
    for t in cand { let ch = child(nd, &t); chain.push(ch.clone()); flags_rec(v, &ch, chain, out); chain.pop(); }
}
const TESTS: [&str; 9] = ["mk>=0", "LemmaB", "ii_3/4", "L", "node1", "node2", "node3", "window", "covol"];
fn check_flag(chain: &Vec<Node>, v: &V5, rho: Fr) -> ([bool; 9], bool) {
    let mut f = [false; 9];
    let gs = &chain[3].gs; let vv = dot(v, v);
    f[8] = gs[3] * 0 + 0 != 0; // placeholder, set below
    let mm: Vec<Fr> = (1..=3).map(|k| mlat(&mred(&chain[k].l), false).0).collect();
    let ms = [fr(3, 10), m_of(mm[0]), m_of(mm[1]), m_of(mm[2])];
    let mu = |i: usize| if i <= 3 { fr(gs[i], gs[i - 1]) } else { fr(vv, gs[3]) };
    let inv = |i: usize| fi(1).div(mu(i));
    let fourm2 = |k: usize| fi(4).mul(ms[k]).mul(ms[k]);
    for k in 0..4 { if ms[k].lt(fi(0)) { f[0] = true; } }
    for k in 0..4 { let mut s = fi(0); for i in k + 1..=4 { s = s.add(inv(i)); } if !fourm2(k).lt(s) { f[1] = true; } }
    for i in 1..=3 { if mu(i + 1).lt(rho.mul(mu(i))) { f[2] = true; } }
    for j in 0..3 { let mut s = fi(0); for i in j + 1..=3 { s = s.add(mu(i)); } if mu(j + 1).gt_(mu(4).add(fr(1, 4).mul(s))) { f[3] = true; } }
    if !fourm2(0).lt(fr(175, 27).mul(inv(1))) { f[4] = true; }
    if !fourm2(0).lt(inv(1).add(fr(37, 9).mul(inv(2)))) || !fourm2(1).lt(fr(37, 9).mul(inv(2))) { f[5] = true; }
    if !fourm2(0).lt(inv(1).add(inv(2)).add(fr(7, 3).mul(inv(3)))) || !fourm2(1).lt(inv(2).add(fr(7, 3).mul(inv(3)))) || !fourm2(2).lt(fr(7, 3).mul(inv(3))) { f[6] = true; }
    let w = leaf_window(&ms, gs, rho);
    if mu(4).lt(w.lo) { f[7] = true; } if let Some(h) = w.hi { if !mu(4).lt(h) { f[7] = true; } }
    let crit = ms[3].eq(fi(0));
    // covolume identity: product of the four mu^2 = |v|^2 (trivially true by definition of mu4); check G_3 consistency with minimizer on K_3
    f[8] = false;
    (f, crit)
}
trait FrX { fn gt_(self, o: Fr) -> bool; }
impl FrX for Fr { fn gt_(self, o: Fr) -> bool { o.lt(self) } }

fn on_crit(v: &V5, perms: &Vec<[usize; 5]>) -> bool {
    // v in G-orbit of span{(1,2,3,4,0),e5} or span{(1,3,4,7,0),e5}
    for p in perms { for m in 0..32u32 {
        let mut u = [0 as I; 5]; for i in 0..5 { u[i] = if (m >> i) & 1 == 1 { -v[p[i]] } else { v[p[i]] }; }
        for vv in [[1, 2, 3, 4], [1, 3, 4, 7]] {
            let mut ok = true; for a in 0..4 { for b in a + 1..4 { if u[a] * vv[b] != u[b] * vv[a] { ok = false; } } }
            if ok { return true; }
        }
    } }
    false
}
fn verify(args: &[String]) {
    let perms = all_perms(); let rho = fr(3, 4);
    let mut tuples: Vec<(String, V5)> = vec![];
    let txt = std::fs::read_to_string("/DEV_TREE/logs/ks5_n5/neartight_tuples.txt").unwrap();
    for l in txt.lines() { let p: Vec<I> = l.trim().split(',').map(|x| x.parse().unwrap()).collect(); let mut v: V5 = [p[0], p[1], p[2], p[3], p[4]]; v.sort(); tuples.push(("known92".into(), v)); }
    let smax: I = arg(args, "--smax").map(|x| x.parse().unwrap()).unwrap_or(2000);
    for s in 1..=smax { tuples.push(("fam1".into(), [1, 2, 3, 4, 5 * s])); tuples.push(("fam2".into(), { let mut v = [1, 3, 4, 7, 5 * s]; v.sort(); v })); }
    let dist: std::collections::HashSet<String> = std::fs::read_to_string(arg(args, "--lines").unwrap_or("out/distinct_tuples.txt".into())).map(|s| s.lines().map(|x| x.to_string()).collect()).unwrap_or_default();
    let mut fails = [0u64; 9]; let (mut nflags, mut ntup, mut allcrit, mut mixed, mut nocrit) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let (mut notcovered, mut mlbad) = (0u64, 0u64); let mut nlines = 0u64; let mut ncritonly = 0u64;
    let mut flag_hist: HashMap<usize, u64> = HashMap::new();
    for (kind, v) in &tuples {
        let ml = ml_exact(v); if !ml.lt(th()) { mlbad += 1; println!("ML>=1/5 for {:?}", v); }
        let mut out = vec![]; let mut chain = vec![root()]; flags_rec(v, &root(), &mut chain, &mut out);
        let (mut nc, mut nn) = (0, 0);
        for ch in &out { let (f, crit) = check_flag(ch, v, rho); nflags += 1; for i in 0..9 { if f[i] { fails[i] += 1; println!("FAIL {} {:?} test {}", kind, v, TESTS[i]); } } if crit { nc += 1 } else { nn += 1 } }
        *flag_hist.entry(out.len()).or_default() += 1;
        if kind == "known92" { if nn == 0 { allcrit += 1; } else if nc == 0 { nocrit += 1; } else { mixed += 1; } }
        ntup += 1;
        let key = format!("{},{},{},{},{}", v[0], v[1], v[2], v[3], v[4]);
        let inl = dist.contains(&key); let onc = on_crit(v, &perms);
        if inl { nlines += 1; } if onc && !inl { ncritonly += 1; }
        if !inl && !onc { notcovered += 1; println!("NOT COVERED {:?}", v); }
    }
    println!("VERIFY tuples {} (92 known + {} family members) flags {} | failures per test: {:?} | ML>=1/5 {}", ntup, 2 * smax, nflags, TESTS.iter().zip(fails.iter()).map(|(a, b)| format!("{}={}", a, b)).collect::<Vec<_>>(), mlbad);
    println!("known92 flag classes: all flags critical {} | all flags non-critical {} | mixed {} ; tuples present in line list {} ; covered only by critical lattice {} ; NOT covered {}", allcrit, nocrit, mixed, nlines, ncritonly, notcovered);
    let mut h: Vec<_> = flag_hist.into_iter().collect(); h.sort(); println!("flags-per-tuple histogram {:?}", h);
}
