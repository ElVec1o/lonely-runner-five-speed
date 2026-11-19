// WP1 box theorem generator (untrusted; Lean re-checks everything it emits).
// usage:  gen selftest
//         gen scan B                      (counts, witness-failing tuples, near-tight list; no files)
//         gen emit B LIM OUTDIR           (writes Lean modules into OUTDIR)
// Brute-force gate: abstraction attempted: none applies (finite box enumeration; the Lean side proves completeness
// of the enumeration itself); serves atom KS5-LEAN stage WP1; symmetry quotient: increasing order (index 120) and primitivity.
use std::env;
use std::fs;
use std::io::Write;

fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn lcm(a: u64, b: u64) -> u64 { a / gcd(a, b) * b }

fn ok_at(a: u64, q: u64, v: u64) -> bool { let r = (v * a) % q; q <= 5 * r.min(q - r) }

fn times() -> Vec<(u64, u64)> {
    let mut t = Vec::new();
    for q in 5..=60u64 { for a in 1..=q / 2 { if gcd(a, q) == 1 { t.push((a, q)); } } }
    t
}

fn times_ext() -> Vec<(u64, u64)> {
    let mut t = Vec::new();
    for q in 2..=60u64 { for a in 1..=q / 2 { if gcd(a, q) == 1 { t.push((a, q)); } } }
    t
}

fn witness(v: &[u64; 5], ts: &Vec<(u64, u64)>) -> bool {
    ts.iter().any(|&(a, q)| v.iter().all(|&x| ok_at(a, q, x)))
}

/// exact ML as (g, L, k): gap value g/L attained at t = k/L; candidates t=k/L, L = v_i+v_j (i<=j), every k (ml_standard rule)
fn ml(v: &[u64; 5]) -> (u64, u64, u64) {
    let mut best = (0u64, 1u64, 0u64);
    for i in 0..5 { for j in i..5 {
        let l = v[i] + v[j];
        for k in 0..l {
            let mut g = l;
            for &x in v.iter() { let r = (x * k) % l; g = g.min(r.min(l - r)); }
            if (g as u128) * (best.1 as u128) > (best.0 as u128) * (l as u128) { best = (g, l, k); }
        }
    }}
    best
}

fn reduce(n: u64, d: u64) -> (u64, u64) { let g = gcd(n, d); (n / g, d / g) }

fn selftest() {
    let c: Vec<([u64; 5], (u64, u64))> = vec![
        ([1, 2, 3, 4, 5], (1, 6)), ([1, 3, 4, 7, 5], (2, 11)), ([1, 2, 3, 4, 10], (2, 11)),
        ([1, 2, 3, 4, 30], (6, 31)), ([1, 3, 4, 7, 10], (2, 11)), ([1, 3, 4, 5, 27], (6, 31)),
        ([1, 2, 13, 14, 15], (1, 4)),
    ];
    for (v, (n, d)) in c {
        let (g, l, _) = ml(&v);
        let r = reduce(g, l);
        println!("selftest {:?} ML={}/{} expect {}/{} {}", v, r.0, r.1, n, d, if r == (n, d) { "OK" } else { "FAIL" });
        assert!(r == (n, d));
    }
    // negative control for the witness predicate: (1,2,3,4,5) has ML 1/6 so no time may pass
    assert!(!witness(&[1, 2, 3, 4, 5], &times_ext()));
    assert!(witness(&[1, 2, 13, 14, 15], &times_ext()));
    assert_eq!(times().len(), 548);
    println!("selftest witness controls OK (548 times)");
}

struct Scan { prim: u64, fail: Vec<([u64; 5], (u64, u64), u64, u64, u64)> } // tuple, ML reduced, x, q (argmax reduced time), nonprimitive skipped

fn scan(b: u64) -> (Scan, u64) {
    let ts = times_ext();
    let mut prim = 0u64; let mut all = 0u64;
    let mut fail = Vec::new();
    for a in 1..=b { for bb in a + 1..=b { for c in bb + 1..=b { for d in c + 1..=b { for e in d + 1..=b {
        all += 1;
        let v = [a, bb, c, d, e];
        if gcd(gcd(gcd(gcd(a, bb), c), d), e) != 1 { continue; }
        prim += 1;
        if witness(&v, &ts) { continue; }
        let (g, l, k) = ml(&v);
        let r = reduce(g, l);
        let (x, q) = reduce(k, l);
        let x = if x == 0 { 0 } else { x };
        fail.push((v, r, x, q, g * 5 < l)); // placeholder replaced below
    }}}}}
    // rebuild with correct type
    let fail2 = fail.into_iter().map(|(v, r, x, q, nt)| (v, r, x, q, if nt { 1u64 } else { 0u64 })).collect();
    (Scan { prim, fail: fail2 }, all)
}

fn lean_list(v: &[u64]) -> String { format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")) }

fn main() {
    let args: Vec<String> = env::args().collect();
    match args[1].as_str() {
        "selftest" => selftest(),
        "scan" => {
            let b: u64 = args[2].parse().unwrap();
            let (s, all) = scan(b);
            let nt: Vec<_> = s.fail.iter().filter(|f| f.4 == 1).collect();
            let ex: Vec<_> = s.fail.iter().filter(|f| f.4 == 0).collect();
            println!("B={} increasing tuples {} primitive {} witness-failing {} near-tight {} extra(ML>=1/5, no q<=60 time) {}", b, all, s.prim, s.fail.len(), nt.len(), ex.len());
            for f in &nt { println!("NT {:?} ML {}/{}", f.0, f.1 .0, f.1 .1); }
            for f in &ex { println!("EX {:?} ML {}/{} time {}/{}", f.0, f.1 .0, f.1 .1, f.2, f.3); }
        }
        "emit" => {
            let b: u64 = args[2].parse().unwrap();
            let lim: u64 = args[3].parse().unwrap();
            let out = args[4].clone();
            fs::create_dir_all(&out).unwrap();
            let (s, _all) = scan(b);
            let nt: Vec<_> = s.fail.iter().filter(|f| f.4 == 1).cloned().collect();
            let ex: Vec<_> = s.fail.iter().filter(|f| f.4 == 0).cloned().collect();
            // every near-tight tuple must have ML = s/(5s+1)
            for f in &nt { assert!(f.1 .1 == 5 * f.1 .0 + 1, "ML not of the form s/(5s+1): {:?}", f); }
            // extra times must be valid
            for f in &ex { assert!(f.0.iter().all(|&x| ok_at(f.2, f.3, x)), "bad extra time {:?}", f); }
            // ---- data module
            let mut d = String::new();
            d.push_str(&format!("/- WP1 box data for B={} (generated by lean5_wp1/src/gen.rs; untrusted, re-checked by the kernel).\n  nt: witness-failing primitive increasing tuples with ML < 1/5; ex: tuples with ML >= 1/5 without a q<=60 time, plus one time (x,q). -/\nnamespace L5W\n\n", b));
            d.push_str(&format!("def nt{} : List (List Nat) := [\n", b));
            d.push_str(&nt.iter().map(|f| format!("  {}", lean_list(&f.0))).collect::<Vec<_>>().join(",\n"));
            d.push_str("]\n\n");
            d.push_str(&format!("def ex{} : List (List Nat × Nat × Nat) := [\n", b));
            d.push_str(&ex.iter().map(|f| format!("  ({}, {}, {})", lean_list(&f.0), f.2, f.3)).collect::<Vec<_>>().join(",\n"));
            d.push_str("]\n\nend L5W\n");
            fs::write(format!("{}/BoxData{}.lean", out, b), d).unwrap();
            // ---- chunk packing over pairs (a,b) in lexicographic order
            let cnt = |bb: u64| -> u64 { let m = b - bb; m * (m - 1) * (m.saturating_sub(2)) / 6 };
            let mut chunks: Vec<Vec<(u64, u64)>> = Vec::new();
            let mut cur: Vec<(u64, u64)> = Vec::new(); let mut cur_n = 0u64; let mut total = 0u64;
            for a in 1..=b - 4 { for bb in a + 1..=b - 3 {
                let n = cnt(bb);
                if !cur.is_empty() && cur_n + n > lim { chunks.push(std::mem::take(&mut cur)); cur_n = 0; }
                cur.push((a, bb)); cur_n += n; total += n;
            }}
            if !cur.is_empty() { chunks.push(cur); }
            let chunk_sizes: Vec<u64> = chunks.iter().map(|c| c.iter().map(|p| cnt(p.1)).sum()).collect();
            for (k, c) in chunks.iter().enumerate() {
                let k1 = k + 1;
                let lst = format!("[{}]", c.iter().map(|p| format!("({},{})", p.0, p.1)).collect::<Vec<_>>().join(","));
                let mut m = String::new();
                m.push_str(&format!("import LRSpectrumFull.L5WP1.BoxCore\nimport LRSpectrumFull.L5WP1.BoxData{}\n\nset_option Elab.async false\nset_option maxHeartbeats 0\n\nnamespace L5W\n\n/-- chunk {} of {}: {} pairs (a,b), {} tuples -/\ntheorem chunk{}_{} : chunkP {} nt{} ex{} {} = true := by decide +kernel\n\nend L5W\n",
                    b, k1, chunks.len(), c.len(), chunk_sizes[k], b, k1, b, b, b, lst));
                fs::write(format!("{}/BoxC{}_{}.lean", out, b, k1), m).unwrap();
            }
            // ---- master module
            let mut m = String::new();
            for k in 0..chunks.len() { m.push_str(&format!("import LRSpectrumFull.L5WP1.BoxC{}_{}\n", b, k + 1)); }
            m.push_str(&format!("import LRSpectrumFull.L5WP1.BoxCore\nimport LRSpectrumFull.L5WP1.BoxData{}\n\nset_option maxHeartbeats 0\n\nnamespace L5W\n\n", b));
            m.push_str(&format!("def chunks{} : List (List (Nat × Nat)) := [\n", b));
            m.push_str(&chunks.iter().map(|c| format!("  [{}]", c.iter().map(|p| format!("({},{})", p.0, p.1)).collect::<Vec<_>>().join(","))).collect::<Vec<_>>().join(",\n"));
            m.push_str("]\n\n");
            m.push_str(&format!("theorem allChunks{} : ∀ ps ∈ chunks{}, chunkP {} nt{} ex{} ps = true := by\n  intro ps hps\n  simp only [chunks{}, List.mem_cons, List.not_mem_nil, or_false] at hps\n  rcases hps with {}\n", b, b, b, b, b, b,
                (0..chunks.len()).map(|_| "rfl").collect::<Vec<_>>().join(" | ")));
            for k in 0..chunks.len() { m.push_str(&format!("  · exact chunk{}_{}\n", b, k + 1)); }
            m.push_str(&format!("\ntheorem flat{} : (chunks{}).flatten = allPairs {} := by decide +kernel\n\nend L5W\n", b, b, b));
            fs::write(format!("{}/BoxMaster{}.lean", out, b), m).unwrap();
            // ---- near-tight value module
            let mut v = String::new();
            v.push_str(&format!("import LRSpectrumFull.L5WP1.BoxNT\nimport LRSpectrumFull.L5WP1.BoxData{}\n\nset_option maxHeartbeats 0\n\nnamespace L5W\nopen LRSpectrumFull\n\n", b));
            let mut cases: Vec<String> = Vec::new();
            let mut idx = 0;
            for f in &nt {
                let t = f.0; let s = f.1 .0;
                let fam1 = t[0] == 1 && t[1] == 2 && t[2] == 3 && t[3] == 4 && t[4] % 5 == 0;
                let fam2 = t[0] == 1 && t[1] == 3 && t[2] == 4 && t[3] == 7 && t[4] % 5 == 0 && t[4] / 5 >= 2;
                if fam1 { assert!(t[4] == 5 * s); cases.push(format!("exact ⟨{}, by norm_num, val_fam1 {} {} (by norm_num) (by norm_num)⟩", s, s, t[4])); }
                else if fam2 { assert!(t[4] == 5 * s); cases.push(format!("exact ⟨{}, by norm_num, val_fam2 {} {} (by norm_num) (by norm_num)⟩", s, s, t[4])); }
                else {
                    idx += 1;
                    let (g, l, k) = ml(&t);
                    let (x, q) = reduce(k, l);
                    let (pn, pd) = (f.1 .0, f.1 .1);
                    assert_eq!(reduce(g, l), (pn, pd));
                    assert!(t.iter().all(|&w| { let r = (w * x) % q; pd * r.min(q - r) >= pn * q }));
                    let mut ll = 1u64; for &w in t.iter() { ll = lcm(ll, w); }
                    let rr = pd * ll;
                    let mut ivs: Vec<(u64, u64, u64, u64)> = Vec::new();
                    for &w in t.iter() { let kk = ll / w; for m in 0..=w { let lo = (m * pd).saturating_sub(pn) * kk; let hi = (m * pd + pn) * kk; ivs.push((lo, hi, w, m)); } }
                    let mut reach = 0u64; let mut chain: Vec<(u64, u64)> = Vec::new();
                    while reach < rr {
                        let mut bestc: Option<(u64, u64, u64, u64)> = None;
                        for &iv in ivs.iter() { if iv.0 <= reach && iv.1 > reach { if bestc.map_or(true, |bb| iv.1 > bb.1) { bestc = Some(iv); } } }
                        let iv = bestc.expect("cover chain stuck: value not an upper bound");
                        chain.push((iv.2, iv.3)); reach = iv.1.max(reach);
                    }
                    let chs = format!("[{}]", chain.iter().map(|c| format!("({},{})", c.0, c.1)).collect::<Vec<_>>().join(","));
                    v.push_str(&format!("/-- exact value of a sporadic near-tight tuple: lower bound by the time {}/{}, upper bound by a cover chain of {} intervals -/\ntheorem spor{}_{} : ML (vecL {}) = (({}:ℕ):ℝ) / (5 * ({}:ℕ) + 1) := by\n  rw [ml_eq_of_data {} {} {} {} {} {} {} {} {} {} {} (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]\n  norm_num\n\n",
                        x, q, chain.len(), b, idx, lean_list(&t), s, s, t[0], t[1], t[2], t[3], t[4], pn, pd, x, q, ll, chs));
                    cases.push(format!("exact ⟨{}, by norm_num, spor{}_{}⟩", s, b, idx));
                }
            }
            v.push_str(&format!("theorem ntvals{} : ∀ l ∈ nt{}, ∃ s : ℕ, 1 ≤ s ∧ ML (vecL l) = (s : ℝ) / (5 * s + 1) := by\n  intro l hl\n  simp only [nt{}, List.mem_cons, List.not_mem_nil, or_false] at hl\n  rcases hl with {}\n", b, b, b, (0..cases.len()).map(|_| "rfl").collect::<Vec<_>>().join(" | ")));
            for c in &cases { v.push_str(&format!("  · {}\n", c)); }
            v.push_str("\nend L5W\n");
            fs::write(format!("{}/BoxNTV{}.lean", out, b), v).unwrap();
            println!("B={} pairs chunks {} (sizes min {} max {} total {})", b, chunks.len(), chunk_sizes.iter().min().unwrap(), chunk_sizes.iter().max().unwrap(), total);
            println!("nt {} ex {}", nt.len(), ex.len());
        }
        _ => panic!("usage"),
    }
    std::io::stdout().flush().unwrap();
}
