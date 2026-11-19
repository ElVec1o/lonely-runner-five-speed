// l5s4s: independent cross-check of the literal `lead` of a T2E<k>Lead module against the packed data module T2D<k>Data.
// usage: chk_lead <T2D<k>Data.lean> <T2E<k>Lead.lean>
// Reads every 16-hex-digit-per-integer packed record (0x... literals inside `def G<i> : List Nat`), takes digit 45 (bias 32768), and checks
// that the set of digit-45 values equals the set of numbers in `def lead : List Nat := [...]`.
use std::collections::BTreeSet;
use std::fs;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let data = fs::read_to_string(&a[1]).unwrap();
    let lead = fs::read_to_string(&a[2]).unwrap();
    let mut digs: BTreeSet<i64> = BTreeSet::new(); let mut nrec = 0usize;
    for line in data.lines() {
        let t = line.trim().trim_end_matches(',').trim_end_matches(']');
        if let Some(h) = t.strip_prefix("0x") {
            if !h.chars().all(|c| c.is_ascii_hexdigit()) { continue; }
            assert_eq!(h.len(), 64 * 4, "record must have 64 digits of 4 hex chars");
            // most significant digit first: digit k (least significant = digit 0) is the k-th 4-hex-char group from the right
            let k = 45usize; let end = h.len() - 4 * k; let s = &h[end - 4..end];
            let v = i64::from_str_radix(s, 16).unwrap() - 32768;
            digs.insert(v); nrec += 1;
        }
    }
    let l = lead.lines().find(|l| l.starts_with("def lead")).expect("no lead line");
    let inner = &l[l.find('[').unwrap() + 1..l.rfind(']').unwrap()];
    let ls: BTreeSet<i64> = inner.split(',').filter(|x| !x.trim().is_empty()).map(|x| x.trim().parse().unwrap()).collect();
    println!("records {} distinct digit-45 values {} lead entries {} equal {}", nrec, digs.len(), ls.len(), digs == ls);
    if digs != ls { std::process::exit(1); }
}
