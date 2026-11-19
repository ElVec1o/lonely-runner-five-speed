// l5emit: certificate EMITTER for the Lean row-interval lines checker `classLinesR` (LinRCore.lean), stage S4Q, 2026-11-17.
// Generator code (rows, hints, class reduction) is taken from the idea prototype l5lines_idea (l5li); the new parts are the exact
// Lean record/stream packing, an independent interpreter `lean_check` written from the TEXT of LinRCore.lean (it decodes the record and
// the stream from the emitted hex, not from the generator structures), the Lean module writer and the planted-corruption control writer.
// Exact i128 arithmetic, overflow checks on.
//   emit TDIR TSV LINTL D1LIST|all OUTDIR TAG MAXPTS     write LinR<TAG>C<j>.lean chunks (<= MAXPTS visited points each), self-check every class
//   ctl  TDIR TSV LINTL D1LIST OUTFILE                    write the planted-corruption control module for one real class
//   env ORACLE=1 : also compare the visited set with a brute-force scan of the old box (independent oracle)
use std::collections::{HashMap, HashSet};
use std::fs;

type I = i128;

fn parse_hex_digits(h: &str) -> Vec<I> {
    let b = h.as_bytes();
    assert!(b.len() % 8 == 0, "hex length not a multiple of 8");
    let n = b.len() / 8;
    (0..n).map(|j| { let s = &h[b.len() - 8 * (j + 1)..b.len() - 8 * j]; u32::from_str_radix(s, 16).unwrap() as I - 2147483648 }).collect()
}

fn load(dir: &str) -> Vec<Vec<I>> {
    let mut fl: Vec<String> = fs::read_dir(dir).unwrap().map(|e| e.unwrap().file_name().to_string_lossy().to_string())
        .filter(|f| f.starts_with("GD3T") && f.ends_with(".lean")).collect();
    // numeric order of the chunk index (a plain string sort puts C10 before C2): file name ...C<j>.lean
    let ckey = |f: &String| -> (String, u64) { let s = f.trim_end_matches(".lean"); let i = s.rfind('C').unwrap(); (s[..i].to_string(), s[i + 1..].parse::<u64>().unwrap()) };
    fl.sort_by_key(|f| ckey(f));
    let mut v = vec![];
    for f in fl {
        let s = fs::read_to_string(format!("{}/{}", dir, f)).unwrap();
        for l in s.lines() {
            let l = l.trim();
            if let Some(h) = l.strip_prefix("0x") { v.push(parse_hex_digits(h.trim_end_matches(|c| c == ',' || c == ']' || c == ' '))); }
        }
    }
    v
}

fn load_tl(path: &str) -> (Vec<(I, I)>, Vec<[I; 5]>) {
    let s = fs::read_to_string(path).unwrap();
    let (mut tl, mut t5) = (vec![], vec![]);
    let mut mode = 0;
    for l in s.lines() {
        let l = l.trim();
        if l.starts_with("def TL5") { mode = 1; continue; }
        if l.starts_with("def T5V") { mode = 2; continue; }
        if mode == 1 && l.starts_with('(') {
            let t: Vec<I> = l.trim_matches(|c| c == '(' || c == ')' || c == ',' || c == ']').split(',').map(|x| x.trim().parse().unwrap()).collect();
            tl.push((t[0], t[1]));
        }
        if mode == 2 && l.starts_with('[') && l.len() > 1 {
            let t: Vec<I> = l.trim_matches(|c| c == '[' || c == ']' || c == ',').split(',').map(|x| x.trim().parse().unwrap()).collect();
            t5.push([t[0], t[1], t[2], t[3], t[4]]);
        }
    }
    (tl, t5)
}

fn dot(a: &[I; 5], b: &[I; 5]) -> I { (0..5).map(|i| a[i] * b[i]).sum() }
fn gcd(a: I, b: I) -> I { let (mut a, mut b) = (a.abs(), b.abs()); while b != 0 { let t = a % b; a = b; b = t; } a }
fn fdiv(a: I, b: I) -> I { assert!(b > 0); let q = a / b; if a % b != 0 && a < 0 { q - 1 } else { q } }
fn isqrt(n: I) -> I { if n <= 0 { return 0; } let mut x = (n as f64).sqrt() as I; while x * x > n { x -= 1; } while (x + 1) * (x + 1) <= n { x += 1; } x }

#[derive(Clone)]
struct Cls { cid: I, k: [[I; 5]; 2], lo: I, hi: I, a: I, b: I, c: I, dd: I, rec: Vec<I> }

// reduce k (Lagrange), update q contragrediently, rebuild the 65-digit Lean record (X dropped, Y appended at digit 64)
fn prep(d: &Vec<I>) -> Cls {
    let g = |i: usize| d[i];
    let mut k = [[0; 5]; 2]; let mut q = [[0; 5]; 2]; let mut l = [[0; 5]; 3]; let mut p = [[0; 5]; 3];
    for a in 0..2 { for i in 0..5 { k[a][i] = g(26 + 5 * a + i); q[a][i] = g(36 + 5 * a + i); } }
    for a in 0..3 { for i in 0..5 { l[a][i] = g(11 + 5 * a + i); p[a][i] = g(46 + 5 * a + i); } }
    let ident = |k: &[[I; 5]; 2], q: &[[I; 5]; 2]| -> bool {
        for r in 0..3 { for a in 0..2 { if dot(&l[r], &k[a]) != 0 { return false; } } }
        for i in 0..5 { for j in 0..5 {
            let mut s = 0; for a in 0..2 { s += k[a][i] * q[a][j]; } for a in 0..3 { s += p[a][i] * l[a][j]; }
            if s != (i == j) as I { return false; } } }
        true };
    assert!(ident(&k, &q), "identity fails before reduction");
    loop {
        if dot(&k[1], &k[1]) < dot(&k[0], &k[0]) { k.swap(0, 1); q.swap(0, 1); continue; }
        let n0 = dot(&k[0], &k[0]); let b = dot(&k[0], &k[1]);
        let mu = fdiv(2 * b + n0, 2 * n0);
        if mu == 0 { break; }
        for i in 0..5 { k[1][i] -= mu * k[0][i]; q[0][i] += mu * q[1][i]; }
    }
    assert!(ident(&k, &q), "identity fails after reduction");
    assert_eq!(g(61), 1, "nr != 1");
    let (lo, hi) = (g(62), g(63));
    let (a, b, c) = (dot(&k[0], &k[0]), dot(&k[0], &k[1]), dot(&k[1], &k[1]));
    let dd = a * c - b * b; assert!(dd > 0 && a > 0);
    assert!(a <= c && 2 * b.abs() <= a, "k not Lagrange-reduced with a <= c");
    let mut rec: Vec<I> = d[0..64].to_vec();
    for a_ in 0..2 { for i in 0..5 { rec[26 + 5 * a_ + i] = k[a_][i]; rec[36 + 5 * a_ + i] = q[a_][i]; } }
    Cls { cid: g(0), k, lo, hi, a, b, c, dd, rec }
}

#[derive(Clone, Copy, Debug)]
struct Row { p: I, g1: I, g2: I, r: I }

fn ymax(c: &Cls) -> I {
    let mut y = isqrt(fdiv(c.a * c.hi, c.dd)); while c.dd * y * y > c.a * c.hi { y -= 1; } while c.dd * (y + 1) * (y + 1) <= c.a * c.hi { y += 1; } y }

fn gen_row(c: &Cls, y: I) -> Row {
    let bb = c.b * y; let dy = c.dd * y * y; let t = c.a * c.hi - dy; let s = c.a * c.lo - dy;
    let z = |x: I| c.a * x + bb;
    let xv = fdiv(-bb, c.a); assert!(z(xv) <= 0 && z(xv + 1) > 0);
    let mut p = xv; while z(p) * z(p) <= t { p -= 1; }
    let mut r = xv + 1; while z(r) * z(r) <= t { r += 1; }
    let hole: Vec<I> = ((p + 1)..r).filter(|&x| z(x) * z(x) < s).collect();
    if hole.is_empty() { Row { p, g1: xv + 1, g2: xv, r } } else {
        let (g1, g2) = (hole[0], *hole.last().unwrap());
        assert_eq!(hole.len() as I, g2 - g1 + 1, "hole not contiguous");
        Row { p, g1, g2, r } }
}

#[derive(Clone, Copy, PartialEq, Debug)]
struct Hint { a: I, q: I }
const PAIRS: [(usize, usize); 10] = [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)];

fn entries(c: &Cls, x: I, y: I) -> [I; 5] { let mut u = [0; 5]; for i in 0..5 { u[i] = x * c.k[0][i] + y * c.k[1][i]; } u }
fn n_of(c: &Cls, x: I, y: I) -> I { c.a * x * x + 2 * c.b * x * y + c.c * y * y }
fn ok_time(u: &[I; 5], a: I, q: I) -> bool { q > 0 && u.iter().all(|&e| { let r = (e.abs() * a) % q; q <= 5 * r && 5 * r <= 4 * q }) }

#[derive(Default, Clone)]
struct Stats { classes: u64, rows: u64, pts: u64, lines: u64, k_np: u64, k_zero: u64, k_eq: u64, k_time: u64, k_t5: u64, k_out: u64, k_fail: u64, bits: u64 }

fn gen_hint(c: &Cls, x: I, y: I, tl: &[(I, I)], t5: &[[I; 5]], st: &mut Stats) -> Hint {
    let n = n_of(c, x, y);
    if n < c.lo || n > c.hi { st.k_out += 1; return Hint { a: 0, q: 4 }; }
    if gcd(x, y) != 1 { st.k_np += 1; return Hint { a: 0, q: 0 }; }
    let u = entries(c, x, y);
    if let Some(i) = (0..5).find(|&i| u[i] == 0) { st.k_zero += 1; return Hint { a: i as I, q: 1 }; }
    if let Some(j) = (0..10).find(|&j| u[PAIRS[j].0].abs() == u[PAIRS[j].1].abs()) { st.k_eq += 1; return Hint { a: j as I, q: 2 }; }
    st.lines += 1;
    for &(a, q) in tl.iter() { if ok_time(&u, a, q) { st.k_time += 1; return Hint { a, q }; } }
    let mut av = [u[0].abs(), u[1].abs(), u[2].abs(), u[3].abs(), u[4].abs()]; av.sort();
    if let Some(j) = t5.iter().position(|r| *r == av) { st.k_t5 += 1; return Hint { a: j as I, q: 3 }; }
    st.k_fail += 1; Hint { a: 0, q: 63 }
}

#[derive(Clone)]
struct Cert { y: I, rows: Vec<Row>, hints: Vec<Hint> }

fn make_cert(c: &Cls, tl: &[(I, I)], t5: &[[I; 5]], st: &mut Stats) -> Cert {
    let y = ymax(c);
    let rows: Vec<Row> = (1..=y).map(|yy| gen_row(c, yy)).collect();
    let mut hints = vec![gen_hint(c, 1, 0, tl, t5, st)];
    for (j, rw) in rows.iter().enumerate() { let yy = j as I + 1;
        for x in (rw.p + 1)..rw.g1 { hints.push(gen_hint(c, x, yy, tl, t5, st)); }
        for x in (rw.g2 + 1)..rw.r { hints.push(gen_hint(c, x, yy, tl, t5, st)); } }
    st.rows += y as u64;
    Cert { y, rows, hints }
}

// ---------- packing: the Lean record hex and the stream W ----------
fn hint_code(h: Hint) -> u64 { assert!(h.a >= 0 && h.a < 32 && h.q >= 0 && h.q < 64, "hint field out of range"); (h.a as u64) * 64 + h.q as u64 }

fn push_bits(bits: &mut Vec<bool>, width: u32, v: u64) { for i in 0..width { bits.push((v >> i) & 1 == 1); } }
fn f16(v: I) -> u64 { assert!(v >= -32768 && v <= 32767, "row field out of 16-bit range"); (v + 32768) as u64 }

// stream bits (LSB first): hint(1,0); per row: p g1 g2 r (16 bit, bias 2^15), then the hints of the two walks
fn pack(rows: &[Row], hints: &[Hint]) -> Vec<bool> {
    let mut bits = vec![];
    push_bits(&mut bits, 11, hint_code(hints[0]));
    let mut hi = 1;
    for rw in rows {
        for v in [rw.p, rw.g1, rw.g2, rw.r] { push_bits(&mut bits, 16, f16(v)); }
        let c1 = std::cmp::max(0, rw.g1 - 1 - rw.p) as usize; let c2 = std::cmp::max(0, rw.r - 1 - rw.g2) as usize;
        for _ in 0..(c1 + c2) { push_bits(&mut bits, 11, hints.get(hi).map_or(0, |h| hint_code(*h))); hi += 1; }
    }
    bits
}

fn bits_hex(bits: &[bool]) -> String {
    let nn = (bits.len() + 3) / 4;
    let mut s = String::new();
    for j in (0..nn).rev() { let mut v = 0u32; for t in 0..4 { let ix = 4 * j + t; if ix < bits.len() && bits[ix] { v |= 1 << t; } } s.push(std::char::from_digit(v, 16).unwrap()); }
    let t = s.trim_start_matches('0').to_string(); if t.is_empty() { "0".into() } else { t }
}
fn hex_bits(h: &str) -> Vec<bool> {
    let b = h.as_bytes(); let mut bits = vec![];
    for j in (0..b.len()).rev() { let v = (b[j] as char).to_digit(16).unwrap(); for t in 0..4 { bits.push((v >> t) & 1 == 1); } }
    bits
}
fn rec_hex(rec: &[I]) -> String { let mut s = String::new(); for k in (0..rec.len()).rev() { s.push_str(&format!("{:08x}", (rec[k] + 2147483648) as u32)); } s }

// ---------- the independent interpreter of the Lean text (decodes record and stream from hex) ----------
fn rd(bits: &[bool], pos: usize, w: usize) -> u64 { let mut v = 0u64; for i in 0..w { if pos + i < bits.len() && bits[pos + i] { v |= 1 << i; } } v }

struct Em<'a> { g: Vec<I>, t5: &'a [[I; 5]], a: I, b: I, c: I, visited: Vec<(I, I, u64)> }

impl<'a> Em<'a> {
    fn g(&self, i: usize) -> I { self.g[i] }
    fn dt(&self, o: usize, p: usize) -> I { (0..5).map(|i| self.g(o + i) * self.g(p + i)).sum() }
    fn struct_r(&self) -> bool {
        let g = |i| self.g(i);
        let (a, b, c) = (self.dt(26, 26), self.dt(26, 31), self.dt(31, 31)); let dd = a * c - b * b; let y = g(64);
        if !(self.dt(11, 26) == 0 && self.dt(11, 31) == 0 && self.dt(16, 26) == 0 && self.dt(16, 31) == 0 && self.dt(21, 26) == 0 && self.dt(21, 31) == 0) { return false; }
        for i in 0..5 { for j in 0..5 {
            if g(26 + i) * g(36 + j) + g(31 + i) * g(41 + j) + g(46 + i) * g(11 + j) + g(51 + i) * g(16 + j) + g(56 + i) * g(21 + j) != (i == j) as I { return false; } } }
        g(61) == 1 && 0 < dd && 0 <= y && g(63) * a < dd * ((y + 1) * (y + 1))
    }
    fn pt(&mut self, x: I, y: I, h: u64) -> bool {
        self.visited.push((x, y, h));
        let (q, t) = ((h % 64) as I, (h / 64) as I);
        let e = |i: usize| x * self.g[26 + i] + y * self.g[31 + i];
        let n = self.a * x * x + 2 * self.b * x * y + self.c * y * y;
        if q >= 5 { (0..5).all(|i| { let s = e(i).abs(); let r = (s * t) % q; q <= 5 * r && 5 * r <= 4 * q }) }
        else if q == 0 { gcd(x, y) != 1 }
        else if q == 1 { t < 5 && e(t as usize) == 0 }
        else if q == 2 { t < 10 && e(PAIRS[t as usize].0).abs() == e(PAIRS[t as usize].1).abs() }
        else if q == 3 { t < 25 && self.t5[t as usize].iter().all(|&v| (0..5).any(|i| e(i).abs() == v)) }
        else { n < self.g[62] || self.g[63] < n }
    }
    fn row_chk(&self, y: I, p: I, g1: I, g2: I, r: I) -> bool {
        let (a, b, c) = (self.a, self.b, self.c); let dd = a * c - b * b; let hi = self.g[63]; let lo = self.g[62];
        let tt = a * hi - dd * y * y; let ss = a * lo - dd * y * y;
        let zp = a * p + b * y; let zr = a * r + b * y; let z1 = a * g1 + b * y; let z2 = a * g2 + b * y;
        zp <= 0 && tt < zp * zp && 0 <= zr && tt < zr * zr && (g2 < g1 || (z1 * z1 < ss && z2 * z2 < ss))
    }
}

fn dec16(bits: &[bool], pos: usize) -> I { rd(bits, pos, 16) as I - 32768 }

fn lean_check(rec: &[I], bits: &[bool], t5: &[[I; 5]]) -> (bool, Vec<(I, I, u64)>) {
    let mut em = Em { g: rec.to_vec(), t5, a: 0, b: 0, c: 0, visited: vec![] };
    if rec.len() < 65 { return (false, vec![]); }
    if !em.struct_r() { return (false, vec![]); }
    em.a = em.dt(26, 26); em.b = em.dt(26, 31); em.c = em.dt(31, 31);
    if !em.pt(1, 0, rd(bits, 0, 11)) { return (false, em.visited); }
    let fuel = std::cmp::max(0, em.g[64]) as usize;
    let mut pos = 11usize;
    for yy in 1..=fuel {
        let y = yy as I;
        let (p, g1, g2, r) = (dec16(bits, pos), dec16(bits, pos + 16), dec16(bits, pos + 32), dec16(bits, pos + 48));
        let c1 = std::cmp::max(0, g1 - 1 - p) as usize; let c2 = std::cmp::max(0, r - 1 - g2) as usize;
        if !em.row_chk(y, p, g1, g2, r) { return (false, em.visited); }
        let mut hp = pos + 64;
        for i in 0..c1 { let h = rd(bits, hp, 11); hp += 11; if !em.pt(p + 1 + i as I, y, h) { return (false, em.visited); } }
        for i in 0..c2 { let h = rd(bits, hp, 11); hp += 11; if !em.pt(g2 + 1 + i as I, y, h) { return (false, em.visited); } }
        pos += 64 + 11 * (c1 + c2);
    }
    (true, em.visited)
}

// ---------- brute-force oracle over the old box ----------
fn oldbox(c: &Cls) -> (I, I) { let x = isqrt(fdiv(c.hi * c.c, c.dd)) + 1; let y = isqrt(fdiv(c.hi * c.a, c.dd)) + 1; (x, y) }
fn nd5(e: I, a: I, q: I) -> bool { let m = ((e * a) % q + q) % q; 5 * std::cmp::min(m, q - m) >= q }
fn oracle(c: &Cls, vis: &[(I, I, u64)], t5: &[[I; 5]]) -> (u64, u64, u64) {
    let (bx, by) = oldbox(c);
    let vset: HashMap<(I, I), u64> = vis.iter().map(|&(x, y, h)| ((x, y), h)).collect();
    let (mut inr, mut missed, mut bad) = (0u64, 0u64, 0u64);
    for y in 0..=by { let xs: Vec<I> = if y == 0 { vec![1] } else { (-bx..=bx).collect() };
        for x in xs { let n = n_of(c, x, y); if n < c.lo || n > c.hi { continue; } inr += 1;
            let u = entries(c, x, y);
            let line = gcd(x, y) == 1 && u.iter().all(|&e| e != 0) && PAIRS.iter().all(|&(i, j)| u[i].abs() != u[j].abs());
            match vset.get(&(x, y)) { None => { missed += 1; }
                Some(&h) => if line { let (q, t) = ((h % 64) as I, (h / 64) as I);
                    let ok = if q >= 5 { u.iter().all(|&e| nd5(e, t, q)) } else if q == 3 && (t as usize) < t5.len() {
                        let mut av: Vec<I> = u.iter().map(|e| e.abs()).collect(); av.sort(); av == t5[t as usize].to_vec() } else { false };
                    if !ok { bad += 1; } } } } }
    (inr, missed, bad)
}

fn setup(args: &[String]) -> (Vec<Cls>, Vec<(I, I)>, Vec<[I; 5]>, HashMap<I, I>) {
    let recs = load(&args[2]);
    let tsv = fs::read_to_string(&args[3]).unwrap();
    let d1of: HashMap<I, I> = tsv.lines().skip(1).map(|l| { let f: Vec<&str> = l.split('\t').collect(); (f[0].parse().unwrap(), f[1].parse().unwrap()) }).collect();
    let (tl, t5) = load_tl(&args[4]);
    assert_eq!(tl.len(), 548); assert_eq!(t5.len(), 25);
    let sel: Option<HashSet<I>> = if args[5] == "all" { None } else { Some(args[5].split(',').map(|s| s.parse().unwrap()).collect()) };
    let cls: Vec<Cls> = recs.iter().map(prep).filter(|c| sel.as_ref().map_or(true, |s| s.contains(&d1of[&c.cid]))).collect();
    eprintln!("records {} selected classes {}", recs.len(), cls.len());
    (cls, tl, t5, d1of)
}

fn lean_header(name: &str, doc: &str) -> String {
    format!("/-\n# L5S4.{name} : {doc}\n-/\nimport LRSpectrumFull.L5S4.LinRCore\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace {name}\n\nopen LRSpectrumFull.L5S4.Lin\n\n")
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args[1].as_str();
    let (cls, tl, t5, _d1) = setup(&args);
    let oracle_on = std::env::var("ORACLE").is_ok();
    if mode == "emit" {
        let outdir = &args[6]; let tag = &args[7]; let maxpts: u64 = args[8].parse().unwrap();
        fs::create_dir_all(outdir).unwrap();
        let mut st = Stats::default();
        let (mut chunk, mut cpts, mut cn, mut files) = (String::new(), 0u64, 0usize, 0usize);
        let (mut tot_inr, mut tot_missed, mut tot_bad, mut rejected, mut maxbits) = (0u64, 0u64, 0u64, 0u64, 0u64);
        let flush = |chunk: &mut String, cpts: &mut u64, cn: &mut usize, files: &mut usize| {
            if *cn == 0 { return; }
            let name = format!("LinR{}C{}", tag, *files);
            let mut s = lean_header(&name, &format!("row-interval lines records (T4 layout minus X, Y at digit 64) + streams W, {} classes, {} visited points (WRITTEN-UNCHECKED)", cn, cpts));
            s.push_str("def blobs : List (Nat × Nat) := [\n"); s.push_str(chunk); s.push_str("]\n\n");
            s.push_str("theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by decide +kernel\n\n");
            s.push_str(&format!("end {}\nend L5S4\nend LRSpectrumFull\n", name));
            fs::write(format!("{}/{}.lean", outdir, name), s).unwrap();
            println!("chunk {} classes {} visited points {}", name, cn, cpts);
            chunk.clear(); *cpts = 0; *cn = 0; *files += 1; };
        // optional TOPN=n: emit only the n classes with the most visited points (the heaviest records), in decreasing size
        let order: Vec<usize> = if let Ok(tn) = std::env::var("TOPN") {
            let tn: usize = tn.parse().unwrap();
            let mut sz: Vec<(usize, usize)> = cls.iter().enumerate().map(|(i, c)| { let mut s = Stats::default(); (make_cert(c, &tl, &t5, &mut s).hints.len(), i) }).map(|(n, i)| (n, i)).collect();
            sz.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
            sz.iter().take(tn).map(|x| x.1).collect()
        } else if let (Ok(f), Ok(t)) = (std::env::var("CLS_FROM"), std::env::var("CLS_TO")) {
            (f.parse::<usize>().unwrap()..std::cmp::min(t.parse::<usize>().unwrap(), cls.len())).collect()
        } else { (0..cls.len()).collect() };
        let total = order.len();
        for (ci, &cidx) in order.iter().enumerate() {
            let c = &cls[cidx];
            let mut cs = Stats::default();
            let ce = make_cert(c, &tl, &t5, &mut cs);
            assert_eq!(cs.k_fail, 0, "class {} has a line without time or residual tuple", c.cid);
            let bits = pack(&ce.rows, &ce.hints);
            let rec = c.rec.clone() ; let mut rec = rec; rec.push(ce.y);
            // round trip of the packing, then the independent interpreter of the Lean text
            let rh = rec_hex(&rec); let wh = bits_hex(&bits);
            let rec2 = parse_hex_digits(&rh); assert_eq!(rec2, rec);
            let bits2 = hex_bits(&wh);
            let (ok, vis) = lean_check(&rec2, &bits2, &t5);
            if !ok { rejected += 1; eprintln!("class {} REJECTED by the interpreter", c.cid); }
            assert_eq!(vis.len(), ce.hints.len(), "visited count differs from the hint count");
            if oracle_on { let (inr, missed, bad) = oracle(c, &vis, &t5); tot_inr += inr; tot_missed += missed; tot_bad += bad; }
            st.classes += 1; st.rows += 0; st.pts += vis.len() as u64; st.lines += cs.lines; st.k_np += cs.k_np; st.k_out += cs.k_out; st.k_time += cs.k_time; st.k_eq += cs.k_eq; st.k_zero += cs.k_zero; st.k_t5 += cs.k_t5;
            st.bits += bits.len() as u64; maxbits = maxbits.max(bits.len() as u64);
            let rows_total = ce.rows.len() as u64;
            if cpts + vis.len() as u64 > maxpts && cn > 0 { flush(&mut chunk, &mut cpts, &mut cn, &mut files); }
            chunk.push_str(&format!("(0x{}, 0x{}){}\n", rh, wh, if false { "" } else { "," }));
            cpts += vis.len() as u64; cn += 1; let _ = rows_total;
            if ci + 1 == total {}
        }
        // the last record must not carry a trailing comma issue: Lean accepts a trailing comma in list literals? no: fix below
        flush(&mut chunk, &mut cpts, &mut cn, &mut files);
        // repair trailing commas in every written chunk (Lean list literals reject a final comma before ']')
        for j in 0..files { let path = format!("{}/LinR{}C{}.lean", outdir, tag, j); let s = fs::read_to_string(&path).unwrap(); let s2 = s.replace(",\n]\n", "\n]\n"); fs::write(&path, s2).unwrap(); }
        println!("emitted classes {} chunks {} | visited points {} lines {} | kinds: time {} T5 {} nonprim {} zero {} eqabs {} out {} | stream bytes {:.0} (max class {} bits) | interpreter rejected {}",
            st.classes, files, st.pts, st.lines, st.k_time, st.k_t5, st.k_np, st.k_zero, st.k_eq, st.k_out, st.bits as f64 / 8.0, maxbits, rejected);
        if oracle_on { println!("oracle: in-range points {} missed {} bad {}", tot_inr, tot_missed, tot_bad); }
    } else if mode == "plan" {
        // plan TDIR TSV LINTL all PLANFILE MAXPTS : deterministic chunk plan, nodes by ascending total points (node 5 last), chunks by ascending points inside a node
        let planfile = &args[6]; let maxpts: u64 = args[7].parse().unwrap();
        let mut per: Vec<(I, I, u64)> = vec![]; // (node, cid, points)
        for c in cls.iter() {
            let mut s = Stats::default(); let ce = make_cert(c, &tl, &t5, &mut s);
            assert_eq!(s.k_fail, 0, "class {} has an uncertified line", c.cid);
            per.push((_d1[&c.cid], c.cid, ce.hints.len() as u64));
        }
        if std::env::var("PLAN_CID").is_ok() {
            // CID MODE : chunks are consecutive runs of class ids (= rep order, first-occurrence ids), pseudo node "S",
            // so that the concatenation of the chunk lists in plan order is the class table in cid order.
            let mut per2 = per.clone(); per2.sort_by_key(|p| p.1);
            for (i, p) in per2.iter().enumerate() { assert_eq!(p.1, i as I, "class ids are not contiguous"); }
            let mut out = String::new(); let (mut cp, mut cc): (u64, Vec<I>) = (0, vec![]); let mut j = 0usize; let mut allpts = 0u64;
            let mut flush = |cp: &mut u64, cc: &mut Vec<I>, out: &mut String, j: &mut usize| { if cc.is_empty() { return; }
                out.push_str(&format!("LinRQSC{}\tS\t{}\t{}\t{}\t{}\t{}\n", j, j, cc.len(), cp, j, cc.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))); *j += 1; *cp = 0; cc.clear(); };
            for p in per2.iter() { if cp + p.2 > maxpts && !cc.is_empty() { flush(&mut cp, &mut cc, &mut out, &mut j); } cp += p.2; allpts += p.2; cc.push(p.1); }
            flush(&mut cp, &mut cc, &mut out, &mut j);
            fs::write(planfile, out).unwrap();
            println!("plan (cid mode): classes {} chunks {} visited points {}", per.len(), j, allpts);
            return;
        }
        let mut tot: HashMap<I, u64> = HashMap::new();
        for p in &per { *tot.entry(p.0).or_insert(0) += p.2; }
        let mut nodes: Vec<(u64, I)> = tot.iter().map(|(n, t)| (*t, *n)).collect(); nodes.sort();
        let mut out = String::new(); let mut nchunks = 0usize; let mut allpts = 0u64;
        for (_t, node) in nodes.iter() {
            let mut cl: Vec<&(I, I, u64)> = per.iter().filter(|p| p.0 == *node).collect(); cl.sort_by_key(|p| p.1);
            let mut chunks: Vec<(u64, Vec<I>)> = vec![]; let (mut cp, mut cc): (u64, Vec<I>) = (0, vec![]);
            for p in cl { if cp + p.2 > maxpts && !cc.is_empty() { chunks.push((cp, std::mem::take(&mut cc))); cp = 0; } cp += p.2; cc.push(p.1); }
            if !cc.is_empty() { chunks.push((cp, cc)); }
            chunks.sort_by(|a, b| a.0.cmp(&b.0).then(a.1[0].cmp(&b.1[0])));
            for (j, (pp, ids)) in chunks.iter().enumerate() {
                out.push_str(&format!("LinRQ{}C{}\t{}\t{}\t{}\t{}\t{}\t{}\n", node, j, node, j, ids.len(), pp, nchunks, ids.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")));
                nchunks += 1; allpts += pp; } }
        fs::write(planfile, out).unwrap();
        println!("plan: classes {} nodes {} chunks {} visited points {} (maxpts {})", per.len(), nodes.len(), nchunks, allpts, maxpts);
    } else if mode == "asm" {
        // asm TDIR TSV LINTL all PLANFILE OUTDIR : assembly modules (no data): LinRQ<node>G<g> (32 chunks each, only for nodes with > 32 chunks),
        // LinRQ<node>A (node assembly), LinRAll (all nodes, plan order); also writes asm_order.txt (build order of the assembly modules)
        let plan = fs::read_to_string(&args[6]).unwrap(); let outdir = &args[7];
        fs::create_dir_all(outdir).unwrap();
        let mut nodes: Vec<String> = vec![]; let mut chunks: HashMap<String, Vec<String>> = HashMap::new();
        for line in plan.lines() { let f: Vec<&str> = line.split('\t').collect();
            if !chunks.contains_key(f[1]) { nodes.push(f[1].to_string()); }
            chunks.entry(f[1].to_string()).or_default().push(f[0].to_string()); }
        let write_asm = |name: &str, imps: &Vec<String>, doc: &str| {
            let mut s = format!("/-\n# L5S4.{} : {}\n-/\nimport LRSpectrumFull.L5S4.LinRGlue\n", name, doc);
            for i in imps { s.push_str(&format!("import LRSpectrumFull.L5S4.{}\n", i)); }
            s.push_str(&format!("\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace {}\n\nopen LRSpectrumFull.L5S4.Lin\n\n", name));
            let mut bl = format!("{}.blobs", imps[imps.len() - 1]);
            let mut ok = format!("{}.ok", imps[imps.len() - 1]);
            for i in (0..imps.len() - 1).rev() { bl = format!("{}.blobs ++ ({})", imps[i], bl); ok = format!("chunksR_ok_append {}.ok ({})", imps[i], ok); }
            s.push_str(&format!("def blobs : List (Nat × Nat) := {}\n\ntheorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by\n  unfold blobs\n  exact {}\n\n#print axioms ok\n\nend {}\nend L5S4\nend LRSpectrumFull\n", bl, ok, name));
            fs::write(format!("{}/{}.lean", outdir, name), s).unwrap(); };
        let mut order = String::new();
        for node in &nodes {
            let ch = &chunks[node];
            if ch.len() <= 32 { let a = format!("LinRQ{}A", node); write_asm(&a, ch, &format!("node {} assembly of {} chunks", node, ch.len())); order.push_str(&format!("{}\t{}\n", node, a)); }
            else {
                let mut gs: Vec<String> = vec![];
                for (g, part) in ch.chunks(32).enumerate() { let gn = format!("LinRQ{}G{}", node, g); write_asm(&gn, &part.to_vec(), &format!("node {} group {} ({} chunks)", node, g, part.len())); order.push_str(&format!("{}\t{}\n", node, gn)); gs.push(gn); }
                let a = format!("LinRQ{}A", node); write_asm(&a, &gs, &format!("node {} assembly of {} groups", node, gs.len())); order.push_str(&format!("{}\t{}\n", node, a)); }
        }
        let anodes: Vec<String> = nodes.iter().map(|n| format!("LinRQ{}A", n)).collect();
        write_asm("LinRAll", &anodes, "all 81,436 classes: the lines certificate chunk theorems glued (`allBlobs` = blobs, `ok`)");
        order.push_str("all\tLinRAll\n");
        fs::write(format!("{}/asm_order.txt", outdir), order).unwrap();
        println!("asm: nodes {} (written to {})", nodes.len(), outdir);
    } else if mode == "emitc" {
        // emitc TDIR TSV LINTL all PLANFILE OUTDIR FROM TO : write plan lines FROM..TO (0-based, half open) as modules LinRQ<node>C<j>.lean, interpreter-checked
        // plan columns: 0 name, 1 node, 2 j, 3 ncls, 4 points, 5 global chunk index, 6 comma-separated cids
        let plan = fs::read_to_string(&args[6]).unwrap(); let outdir = &args[7];
        let from: usize = args[8].parse().unwrap(); let to: usize = args[9].parse().unwrap();
        fs::create_dir_all(outdir).unwrap();
        let byc: HashMap<I, usize> = cls.iter().enumerate().map(|(i, c)| (c.cid, i)).collect();
        let (mut nrej, mut tp, mut tc) = (0u64, 0u64, 0u64);
        for (li, line) in plan.lines().enumerate() {
            if li < from || li >= to { continue; }
            let f: Vec<&str> = line.split('\t').collect();
            let name = f[0]; let ids: Vec<I> = f[6].split(',').map(|x| x.parse().unwrap()).collect();
            let mut body = String::new(); let mut pts = 0u64;
            for (n, cid) in ids.iter().enumerate() {
                let c = &cls[byc[cid]]; let mut cs = Stats::default(); let ce = make_cert(c, &tl, &t5, &mut cs);
                assert_eq!(cs.k_fail, 0);
                let bits = pack(&ce.rows, &ce.hints); let mut rec = c.rec.clone(); rec.push(ce.y);
                let rh = rec_hex(&rec); let wh = bits_hex(&bits);
                assert_eq!(parse_hex_digits(&rh), rec);
                let (ok, vis) = lean_check(&parse_hex_digits(&rh), &hex_bits(&wh), &t5);
                if !ok { nrej += 1; eprintln!("class {} REJECTED by the interpreter", cid); }
                assert_eq!(vis.len(), ce.hints.len());
                if oracle_on { let (_i, m, b) = oracle(c, &vis, &t5); assert!(m == 0 && b == 0, "oracle: class {} missed {} bad {}", cid, m, b); }
                pts += vis.len() as u64;
                body.push_str(&format!("(0x{}, 0x{}){}\n", rh, wh, if n + 1 == ids.len() { "" } else { "," }));
            }
            assert_eq!(pts.to_string(), f[4], "plan/emit point count mismatch for {}", name);
            let mut s = lean_header(name, &format!("row-interval lines records + streams W, node {}, {} classes, {} visited points (all-tree lines certificate, generated by l5qemit)", f[1], ids.len(), pts));
            s.push_str("def blobs : List (Nat × Nat) := [\n"); s.push_str(&body); s.push_str("]\n\n");
            s.push_str("theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by decide +kernel\n\n#print axioms ok\n\n");
            if f[1] == "S" { // cid mode: the chunk is the run of class ids first .. first+n-1 (position in the table = class id)
                s.push_str(&format!("def firstCid : Nat := {}\n\ntheorem cids : blobs.map (fun p => (dg p.1 0).toNat) = List.range' firstCid {} := by decide +kernel\n\n#print axioms cids\n\n", ids[0], ids.len()));
                for (n, cid) in ids.iter().enumerate() { assert_eq!(*cid, ids[0] + n as I, "chunk cids not consecutive"); } }
            s.push_str(&format!("end {}\nend L5S4\nend LRSpectrumFull\n", name));
            fs::write(format!("{}/{}.lean.tmp", outdir, name), &s).unwrap();
            fs::rename(format!("{}/{}.lean.tmp", outdir, name), format!("{}/{}.lean", outdir, name)).unwrap();
            println!("{}\t{}\t{}\t{}", name, ids.len(), pts, s.len());
            tp += pts; tc += ids.len() as u64;
        }
        eprintln!("emitc: classes {} points {} interpreter rejected {}", tc, tp, nrej);
        if nrej > 0 { std::process::exit(7); }
    } else if mode == "ctl" {
        let outfile = &args[6];
        // pick the control class: has a hole row, >= 3 time hints, fewest visited points
        let mut best: Option<(usize, Cert, usize)> = None;
        for (ci, c) in cls.iter().enumerate() {
            let mut s = Stats::default(); let ce = make_cert(c, &tl, &t5, &mut s);
            let holes = ce.rows.iter().filter(|r| r.g1 <= r.g2).count();
            let has_seg1 = ce.rows.iter().any(|r| r.g1 - 1 - r.p > 0); let has_seg2 = ce.rows.iter().any(|r| r.r - 1 - r.g2 > 0);
            if holes >= 1 && s.k_time >= 6 && ce.hints.len() >= 12 && has_seg1 && has_seg2 {
                let np = ce.hints.len(); if best.as_ref().map_or(true, |b| np < b.1.hints.len()) { best = Some((ci, ce, holes)); } }
        }
        let (ci, ce, holes) = best.expect("no control class");
        let c = &cls[ci];
        println!("control class index {} cid {} rows {} holes {} points {}", ci, c.cid, ce.rows.len(), holes, ce.hints.len());
        let mut rec = c.rec.clone(); rec.push(ce.y);
        let base_bits = pack(&ce.rows, &ce.hints);
        let (ok0, _) = lean_check(&rec, &base_bits, &t5); assert!(ok0, "base class not accepted");
        // hint index of the first point of row j: 1 + sum of previous (c1 + c2)
        let cnts: Vec<(usize, usize)> = ce.rows.iter().map(|r| (std::cmp::max(0, r.g1 - 1 - r.p) as usize, std::cmp::max(0, r.r - 1 - r.g2) as usize)).collect();
        let start: Vec<usize> = { let mut s = vec![]; let mut acc = 1; for &(a, b) in &cnts { s.push(acc); acc += a + b; } s };
        let jseg1 = (0..ce.rows.len()).find(|&j| cnts[j].0 > 0).unwrap();
        let jseg2 = (0..ce.rows.len()).find(|&j| cnts[j].1 > 0).unwrap();
        let jhole = (0..ce.rows.len()).find(|&j| ce.rows[j].g1 <= ce.rows[j].g2).unwrap();
        let ti = (0..ce.hints.len()).find(|&i| ce.hints[i].q >= 5).unwrap();     // first time hint (a line point)
        let mut muts: Vec<(String, String, Vec<I>, Vec<bool>)> = vec![]; // (name, doc, record, stream)
        let cl = |ce: &Cert| (ce.rows.clone(), ce.hints.clone());
        let mk = |rows: &Vec<Row>, hints: &Vec<Hint>| pack(rows, hints);
        { let (mut r, h) = cl(&ce); r[jseg1].p += 1; muts.push(("rowp".into(), "row bound p raised by one (lower bound shrunk, first walk point dropped)".into(), rec.clone(), mk(&r, &h))); }
        { let (mut r, h) = cl(&ce); r[jseg2].r -= 1; muts.push(("rowr".into(), "row bound r lowered by one (upper bound shrunk)".into(), rec.clone(), mk(&r, &h))); }
        { let (mut r, h) = cl(&ce); let t = r[jhole].g1; r[jhole].g1 = r[jhole].g2; r[jhole].g2 = t; muts.push(("swap".into(), "hole ends g1 and g2 swapped in one row".into(), rec.clone(), mk(&r, &h))); }
        { let (mut r, h) = cl(&ce); r[jhole].g1 -= 1; muts.push(("g1m".into(), "hole start g1 lowered by one (hole too large)".into(), rec.clone(), mk(&r, &h))); }
        { let (mut r, h) = cl(&ce); r[jhole].g2 += 1; muts.push(("g2p".into(), "hole end g2 raised by one (hole too large)".into(), rec.clone(), mk(&r, &h))); }
        { let (mut r, h) = cl(&ce); r[jhole].g1 = r[jhole].g2 + 2; muts.push(("noflag".into(), "hole flag removed (g1 > g2) in a hole row".into(), rec.clone(), mk(&r, &h))); }
        for (nm, doc, hh) in [("hq0", "the hint of a time line point replaced by q = 0 (claims non-primitive): the dropped time hint", Hint { a: 0, q: 0 }),
            ("hq1", "the hint of a time line point replaced by q = 1 (zero entry 0)", Hint { a: 0, q: 1 }),
            ("hq2", "the hint of a time line point replaced by q = 2 (equal absolute entries, pair 0)", Hint { a: 0, q: 2 }),
            ("hq3", "the hint of a time line point replaced by q = 3 (residual tuple 0)", Hint { a: 0, q: 3 }),
            ("hq4", "the hint of a time line point replaced by q = 4 (out of range)", Hint { a: 0, q: 4 }),
            ("hq3a25", "residual index a = 25 (explicit bound a < 25)", Hint { a: 25, q: 3 }),
            ("hq3a31", "residual index a = 31", Hint { a: 31, q: 3 }),
            ("hq5a1", "time 1/5 (fails for entries divisible by 5)", Hint { a: 1, q: 5 }),
            ("hq2a10", "pair index a = 10", Hint { a: 10, q: 2 }),
            ("hq1a5", "zero-entry index a = 5", Hint { a: 5, q: 1 })] {
            let (r, mut h) = cl(&ce); h[ti] = hh; muts.push((nm.into(), doc.into(), rec.clone(), mk(&r, &h))); }
        { let (r, mut h) = cl(&ce); h[ti].a += 1; muts.push(("hta".into(), "time a+1".into(), rec.clone(), mk(&r, &h))); }
        { let (r, mut h) = cl(&ce); h[ti].q += 1; muts.push(("htq".into(), "time denominator q+1".into(), rec.clone(), mk(&r, &h))); }
        { let (r, mut h) = cl(&ce); h[0] = Hint { a: 0, q: 0 }; let _ = &r; muts.push(("hq0pt0".into(), "the hint of the point (1, 0) replaced by q = 0".into(), rec.clone(), mk(&r, &h))); }
        { let (mut r, h) = cl(&ce); r.pop(); muts.push(("rowdrop".into(), "last row dropped from the stream (Y unchanged)".into(), rec.clone(), mk(&r, &h[..h.len() - (cnts[cnts.len() - 1].0 + cnts[cnts.len() - 1].1)].to_vec()))); }
        { let mut b = base_bits.clone(); let n = b.len(); b.truncate(n - 40); muts.push(("trunc".into(), "stream truncated by 40 bits".into(), rec.clone(), b)); }
        { let mut b = base_bits.clone(); b.truncate(11 + 64 * 0 + 16); muts.push(("trunc2".into(), "stream cut after the first row field".into(), rec.clone(), b)); }
        let _ = start;
        let mut rm = |nm: &str, doc: &str, f: &dyn Fn(&mut Vec<I>)| { let mut r2 = rec.clone(); f(&mut r2); muts.push((nm.into(), doc.into(), r2, base_bits.clone())); };
        rm("nr2", "nr := 2 (record has one range)", &|r| r[61] = 2);
        rm("nr0", "nr := 0", &|r| r[61] = 0);
        rm("y0", "Y := 0", &|r| r[64] = 0);
        rm("ym1", "Y := Y - 1 (box bound D (Y+1)^2 > a hi fails)", &|r| r[64] -= 1);
        rm("yneg", "Y := -1", &|r| r[64] = -1);
        rm("kp", "digit k[0][0] + 1", &|r| r[26] += 1);
        rm("qp", "digit q[0][1] + 1", &|r| r[37] += 1);
        rm("pp", "digit p[0][1] + 1", &|r| r[47] += 1);
        rm("lp", "digit l[0][1] + 1", &|r| r[12] += 1);
        rm("hip", "hi := hi + 2 percent (more points in range, rows no longer certified)", &|r| r[63] += r[63] / 50 + 1);
        rm("lom", "lo := lo - 2 percent", &|r| r[62] -= r[62] / 50 + 1);
        let mut out = lean_header("LinRCtl", "planted-corruption controls for the row-interval five-speed lines checker (stage S4Q; MATHLIB-FREE)");
        out.push_str(&format!("def NR0 : Nat := 0x{}\n\ndef WR0 : Nat := 0x{}\n\n", rec_hex(&rec), bits_hex(&base_bits)));
        out.push_str("def bumpR (g : Nat → Int) (k : Nat) (d : Int) : Nat → Int := fun i => if i = k then g i + d else g i\ndef setdR (g : Nat → Int) (k : Nat) (v : Int) : Nat → Int := fun i => if i = k then v else g i\n\n");
        out.push_str("theorem ctlR_pos : classLinesR (dg NR0) WR0 = true := by decide +kernel\n");
        let mut accepted = vec![]; let mut nrej = 0;
        for (nm, doc, r2, b2) in &muts {
            let (ok, _) = lean_check(r2, b2, &t5);
            if ok { accepted.push(nm.clone()); println!("mutant {} ACCEPTED by the interpreter: {}", nm, doc); continue; }
            nrej += 1;
            // record mutations are expressed through the accessor (so the control is a one-digit change of the real record)
            let diffs: Vec<usize> = (0..r2.len()).filter(|&i| r2[i] != rec[i]).collect();
            let same_stream = *b2 == base_bits;
            if same_stream {
                assert_eq!(diffs.len(), 1, "record mutation changes one digit");
                let i = diffs[0]; let d = r2[i] - rec[i];
                if nm == "hip" || nm == "lom" || nm == "ym1" || nm == "y0" || nm == "yneg" || nm == "nr2" || nm == "nr0" {
                    out.push_str(&format!("-- {}\ntheorem ctlR_{} : classLinesR (setdR (dg NR0) {} ({})) WR0 = false := by decide +kernel\n", doc, nm, i, r2[i]));
                } else {
                    out.push_str(&format!("-- {}\ntheorem ctlR_{} : classLinesR (bumpR (dg NR0) {} ({})) WR0 = false := by decide +kernel\n", doc, nm, i, d));
                }
            } else {
                out.push_str(&format!("-- {}\ntheorem ctlR_{} : classLinesR (dg NR0) 0x{} = false := by decide +kernel\n", doc, nm, bits_hex(b2)));
            }
        }
        out.push_str("\nend LinRCtl\nend L5S4\nend LRSpectrumFull\n");
        fs::write(outfile, out).unwrap();
        println!("controls written {} (interpreter-rejected {}, accepted {:?})", outfile, nrej, accepted);
    }
}
