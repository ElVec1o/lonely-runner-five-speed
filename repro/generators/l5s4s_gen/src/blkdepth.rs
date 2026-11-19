// l5s4s: per block of B records of a T2D<k>Data module: max and mean of digit 45 (class representative position = depth of the `L.getD` walk in recN)
// usage: blk_depth <T2D<k>Data.lean> <B>
use std::fs;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let data = fs::read_to_string(&a[1]).unwrap(); let b: usize = a[2].parse().unwrap();
    let mut d45: Vec<i64> = vec![];
    for line in data.lines() {
        let t = line.trim().trim_end_matches(',').trim_end_matches(']');
        if let Some(h) = t.strip_prefix("0x") {
            if !h.chars().all(|c| c.is_ascii_hexdigit()) { continue; }
            let k = 45usize; let end = h.len() - 4 * k; let s = &h[end - 4..end];
            d45.push(i64::from_str_radix(s, 16).unwrap() - 32768);
        }
    }
    for (j, c) in d45.chunks(b).enumerate() {
        let mx = c.iter().max().unwrap(); let mean = c.iter().sum::<i64>() as f64 / c.len() as f64;
        let nlead = c.iter().filter(|&&x| x as usize >= j * b && (x as usize) < (j + 1) * b).count();
        println!("block {} records {} max45 {} mean45 {:.0} self-block reps {}", j, c.len(), mx, mean, nlead);
    }
}
