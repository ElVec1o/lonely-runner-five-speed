// l5s4f: emit the child-list data of ONE depth-1 node for the Lean child enumeration checker (CheckChild*).
// Output: Lean data module (groups by t0, 64-integer flat records), plus per-node funnel counts on stdout.
// Record layout (64 ints): t(4) y(5) b0 b1 b2 (15) r0 r1 r2 (15) x(5) w repIdx p(5) e(5) u(4) u'(4).

pub fn genr(dir: &str, kk: usize, outd: &str, maxpts: usize, maxrec: usize, v2: bool) -> Result<(), String> {
    let d1 = d1_list();
    let b1 = fs::read(format!("{}/t1.bin", dir)).map_err(|e| e.to_string())?; let mut r = Rd(&b1, 0);
    if r.u32() as usize != d1.len() { return Err("T1 count".into()); }
    let mut c1s = vec![]; let mut xws: Vec<(V5, I)> = vec![];
    for (h, _) in &d1 { let hh = r.v5(); let x = r.v5(); let w = r.u32() as I;
        if hh != *h { return Err("T1 vector mismatch".into()); }
        xws.push((x, w)); c1s.push(witness_ok(&[*h], &x, w).ok_or("T1 witness")?); }

    let (h, n1) = &d1[kk];
    let ms = [fr(3, 10), m_of(c1s[kk])]; let inv = [fi(0), fr(n1.gs[0], n1.gs[1])];
    let bnd = radius_bound(&ms, &inv, 2, fr(37, 9), &[0, 1]).unwrap();
    let mut st = Funnel::default(); let sv = d2_surv(n1, c1s[kk], &mut st);
    // T2 class representatives
    let b = fs::read(format!("{}/t2c.bin", dir)).map_err(|e| e.to_string())?; let mut rr = Rd(&b, 0); let nc = rr.u32() as usize;
    let mut rep_t: Vec<Vec<I>> = vec![]; let mut rep_g: Vec<G> = vec![]; let mut rep_hi: Vec<usize> = vec![];
    for _ in 0..nc { let hi = rr.u32() as usize; let t: Vec<I> = (0..4).map(|_| rr.i32() as I).collect(); let g = rr.g(); rep_hi.push(hi); rep_t.push(t); rep_g.push(g); }
    let b2 = fs::read(format!("{}/t2_{:02}.bin", dir, kk)).map_err(|e| e.to_string())?; let mut r2 = Rd(&b2, 0); let cnt = r2.u32() as usize;
    if cnt != sv.len() { return Err("T2 length".into()); }
    let mut rep_idx: HashMap<usize, usize> = HashMap::new(); let mut rep_y: HashMap<usize, V5> = HashMap::new();
    let mut recs: Vec<(I, Vec<I>)> = vec![];
    for (i, (t, n2)) in sv.iter().enumerate() {
        let x = r2.v5(); let w = r2.u32() as I; let cls = r2.u32() as usize; let gn = r2.g(); let u = r2.mat(2, 2); let u2 = r2.mat(2, 2);
        if rep_hi[cls] != kk { return Err("class belongs to another depth-1 node".into()); }
        if rep_t[cls] == *t { rep_idx.insert(cls, i); rep_y.insert(cls, n2.l[1]); }
        let ri = *rep_idx.get(&cls).ok_or("rep not seen first")?; let ry = rep_y[&cls];
        let (cp, ce) = compose_g(&gn, &rep_g[cls]);
        // self-check of the class map in Rust (the same test the Rust checker applies)
        let rl = vec![n2.l[0], ry]; let hh = gmap(&gn, &rep_g[cls], &n2.l);
        if !leq_ok(&hh, &rl, &u, &u2) { return Err("class map fails".into()); }
        let mut f: Vec<I> = vec![];
        f.extend(t.iter()); f.extend(n2.l[1].iter());
        for k in 0..3 { f.extend(n2.b[k].iter()); } for k in 0..3 { f.extend(n2.r[k].iter()); }
        f.extend(x.iter()); f.push(w); f.push(ri as I);
        for k in 0..5 { f.push(cp[k] as I); } for k in 0..5 { f.push(ce[k]); }
        for rw in &u { for &z in rw { f.push(z); } } for rw in &u2 { for &z in rw { f.push(z); } }
        assert_eq!(f.len(), 64);
        recs.push((t[0], f));
    }
    // ---- l5s4r tail: per-node module set for the leaders-only t2 ----
    let d = n1.d(); let tmax: Vec<I> = (0..d).map(|i| isqrt(fdiv(bnd.n * n1.a[i][i], bnd.d))).collect();
    let mut groups: BTreeMap<I, Vec<usize>> = BTreeMap::new();
    for t0 in -tmax[0]..=tmax[0] { groups.insert(t0, vec![]); }
    for (i, (t0, _)) in recs.iter().enumerate() { groups.get_mut(t0).ok_or("t0 outside box")?.push(i); }
    let mut order: Vec<usize> = vec![]; for (_, v) in groups.iter() { for &i in v { order.push(i); } }
    let mut pos = vec![0usize; recs.len()]; for (p, &i) in order.iter().enumerate() { pos[i] = p; }
    let ng = groups.len(); let nrec = recs.len();
    let mut reps: std::collections::BTreeSet<usize> = Default::default();
    let mut hexg: Vec<Vec<String>> = vec![];
    for (_, v) in groups.iter() { let mut hv = vec![]; for &i in v { let mut f = recs[i].1.clone(); let ridx = f[45] as usize; f[45] = pos[ridx] as I; reps.insert(pos[ridx]);
        for &x in f.iter() { assert!(x > -32768 && x < 32767); }
        hv.push(f.iter().rev().map(|x| format!("{:04x}", (x + 32768) as u32)).collect::<String>()); } hexg.push(hv); }
    // node facts and the radius case
    let (xv, w) = xws[kk].clone(); let g1 = n1.gs[1];
    let mm = |z: I| -> I { let r = z.rem_euclid(w); r.min(w - r) };
    let mn: I = xv.iter().map(|&z| mm(z)).min().unwrap();
    let (v0n, v0d) = (9 * g1 - 25, 25 * g1); let (v1n, v1d) = (4 * (5 * mn - w) * (5 * mn - w), 25 * w * w);
    assert!(v1n > 0);
    let case0 = v0n > 0 && v0n * v1d >= v1n * v0d;
    let (vn, vd) = if case0 { (v0n, v0d) } else { (v1n, v1d) };
    let val = fr(37 * vd, 9 * vn);
    if val.n != bnd.n || val.d != bnd.d { return Err(format!("radius mismatch: bound {}/{} value {}/{}", bnd.n, bnd.d, val.n, val.d)); }
    let (t1m, t2m, t3m) = (tmax[1], tmax[2], tmax[3]);
    let pts = ((2 * t1m + 1) * (2 * t2m + 1) * (2 * t3m + 1)) as usize;
    let cch: usize = 300; let nchunk = (nrec + cch - 1) / cch;
    let m = format!("T2D{}", kk);
    let head = |modn: &str, doc: &str, imps: &[String]| -> String {
        let mut s = format!("/-\n# L5S4.{} : {}\n\nGenerated by l5s4r_gen (stage S4R), depth-1 node #{}.  No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.\n-/\n", modn, doc, kk);
        for i in imps { s.push_str(&format!("import LRSpectrumFull.L5S4.{}\n", i)); }
        s.push_str(&format!("\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace LRSpectrumFull\nnamespace L5S4\nnamespace {}\nopen Matrix Finset LRSpectrumFull.L5S3\n\n", m)); s };
    let foot = format!("\nend {}\nend L5S4\nend LRSpectrumFull\n", m);
    let wr = |modn: &str, body: String| -> Result<(), String> { fs::write(format!("{}/{}.lean", outd, modn), body).map_err(|e| e.to_string()) };
    let mut mods: Vec<String> = vec![];
    // data
    let mut s = head(&format!("{}Data", m), "data of the child list of one depth-1 node (packed 16-bit records)", &["T2Gen".to_string()]);
    s.push_str(&format!("def Bn : ℤ := {}\ndef Bd : ℤ := {}\n\n", bnd.n, bnd.d));
    for (gi, hv) in hexg.iter().enumerate() {
        s.push_str(&format!("def G{} : List ℕ := [", gi));
        for (ri, hx) in hv.iter().enumerate() { s.push_str(&format!("{}0x{}", if ri == 0 { "\n    " } else { ",\n    " }, hx)); }
        s.push_str("]\n\n");
    }
    s.push_str("def P : List (ℤ × List ℕ) := [\n");
    for (gi, (t0, _)) in groups.iter().enumerate() { s.push_str(&format!("  ({}, G{}){}\n", t0, gi, if gi + 1 == ng { "" } else { "," })); }
    s.push_str("]\n\ndef Gl : List (ℤ × List (List ℤ)) := P.map fun g => (g.1, g.2.map unpackRec)\n\ndef flatN : List ℕ := P.flatMap Prod.snd\n");
    s.push_str(&foot); wr(&format!("{}Data", m), s)?; mods.push(format!("{}Data", m));
    // node
    let mut s = head(&format!("{}Node", m), "the node, its radius, the box bounds, the group keys", &[format!("{}Data", m)]);
    s.push_str(&format!("def r : D1Raw := d1Data.getD {} badB.default_d1\ntheorem r_ok : r.ok := by decide +kernel\ntheorem r_G : dot r.h r.h = {} := by decide +kernel\ntheorem r_m : wMin r.x {} = {} := by decide +kernel\ntheorem r_w : r.w = {} := by decide +kernel\n\nnoncomputable def nK : NodeW 1 4 := nodeOfRaw r r_ok\n\n", kk, g1, w, mn, w));
    if case0 {
        s.push_str("theorem hrad : radFrac (Cq (1 + 1)) nK.wit nK.rows 1 nK.rk = (Bn : ℚ) / Bd := by\n  refine hrad1_of r r_ok ((Bn : ℚ) / Bd) (Or.inl ⟨?_, ?_, fun _ => ?_⟩) <;>\n    simp only [r_G, r_m, r_w, Bn, Bd] <;> norm_num\n\n");
    } else if v0n > 0 {
        s.push_str("theorem hrad : radFrac (Cq (1 + 1)) nK.wit nK.rows 1 nK.rk = (Bn : ℚ) / Bd := by\n  refine hrad1_of r r_ok ((Bn : ℚ) / Bd) (Or.inr ⟨?_, ?_, fun _ => ?_⟩) <;>\n    simp only [r_G, r_m, r_w, Bn, Bd] <;> norm_num\n\n");
    } else {
        s.push_str("theorem hrad : radFrac (Cq (1 + 1)) nK.wit nK.rows 1 nK.rk = (Bn : ℚ) / Bd := by\n  refine hrad1_of r r_ok ((Bn : ℚ) / Bd) (Or.inr ⟨?_, ?_, fun h => ?_⟩)\n  · simp only [r_G, r_m, r_w, Bn, Bd]; norm_num\n  · simp only [r_G, r_m, r_w, Bn, Bd]; norm_num\n  · simp only [r_G] at h; norm_num at h\n\n");
    }
    s.push_str("noncomputable def ckC : Ctx := ctxOf nK Bn Bd\n\n");
    for i in 0..4 { if i > 0 { s.push_str(&format!("theorem t_{} : tmaxOf ckC {} = {} := by decide +kernel\n", i, i, tmax[i])); } }
    s.push_str(&format!("theorem keys : Gl.map Prod.fst = rngI (tmaxOf ckC 0) := by decide +kernel\ntheorem gl_length : Gl.length = {} := by decide +kernel\n", ng));
    s.push_str(&foot); wr(&format!("{}Node", m), s)?; mods.push(format!("{}Node", m));
    // scan modules
    let mut sm: Vec<Vec<usize>> = vec![]; { let mut cur: Vec<usize> = vec![]; let mut acc = 0usize;
        for gi in 0..ng { if !cur.is_empty() && acc + pts > maxpts { sm.push(std::mem::take(&mut cur)); acc = 0; } cur.push(gi); acc += pts; }
        if !cur.is_empty() { sm.push(cur); } }
    for (j, gs) in sm.iter().enumerate() {
        let modn = format!("{}S{}", m, j);
        let mut s = head(&modn, "box scan: the slices of the groups (flat filters, list equality)", &[format!("{}Node", m)]);
        for &gi in gs { s.push_str(&format!("theorem sc_{} : (rngI {}).all (fun t1 => sliceF (FC.ofCtx ckC) {} {} (Gl.getD {} (0, [])) t1) = true := by decide +kernel\n", gi, t1m, t2m, t3m, gi)); }
        s.push_str(&foot); wr(&modn, s)?; mods.push(modn);
    }
    // record modules
    let per = std::cmp::max(1, maxrec / cch); let nrm = (nchunk + per - 1) / per;
    for j in 0..nrm {
        let modn = format!("{}R{}", m, j);
        let mut s = head(&modn, "record check: facts and class map of a block of stored records (packed Nat)", &[format!("{}Node", m)]);
        for k in (j * per)..std::cmp::min(nchunk, (j + 1) * per) { s.push_str(&format!("theorem rc_{} : ((flatN.drop ({} * {})).take {}).all (recN (FC.ofCtx ckC) flatN) = true := by decide +kernel\n", k, k, cch, cch)); }
        s.push_str(&foot); wr(&modn, s)?; mods.push(modn);
    }
    // assembly
    let mut imps = vec![format!("{}Node", m), "T2Glue".to_string()];
    for j in 0..sm.len() { imps.push(format!("{}S{}", m, j)); } for j in 0..nrm { imps.push(format!("{}R{}", m, j)); }
    let mut s = head(&m, "`StreamHyp'.t2` for the depth-1 node with the representative set restricted to the class leaders", &imps);
    s.push_str(&format!("theorem ft_slices : ∀ g ∈ Gl, ∀ t1 ∈ rngI (tmaxOf ckC 1), sliceF (FC.ofCtx ckC) {} {} g t1 = true := by\n  refine forall_getD Gl (0, []) (fun i hi => ?_)\n  rw [gl_length] at hi\n  rw [t_1]\n  intro t1 ht1\n", t2m, t3m));
    s.push_str("  interval_cases i\n");
    for gi in 0..ng { s.push_str(&format!("  · exact List.all_eq_true.1 sc_{} t1 ht1\n", gi)); }
    s.push_str(&format!("\ntheorem hcomp : ∀ y : V5, ChildPass nK y → ∃ g ∈ Gl, ∃ r ∈ g.2, recT r = tvec nK.b y :=\n  fun y hy => child_list_completeF nK Bn Bd (by decide) hrad Gl keys {} {} t_2 t_3 ft_slices y hy\n\n", t2m, t3m));
    if nchunk == 0 {
        s.push_str("theorem hrec : ∀ N ∈ flatN, recN (FC.ofCtx ckC) flatN N = true := by\n  intro N hN\n  have h0 : flatN = [] := by decide +kernel\n  rw [h0] at hN\n  simp at hN\n\n");
    } else {
        s.push_str(&format!("theorem hrec : ∀ N ∈ flatN, recN (FC.ofCtx ckC) flatN N = true := by\n  refine all_of_chunks flatN {} (by norm_num) _ (fun k hk => ?_)\n  have hl : (flatN.length + {} - 1) / {} = {} := by decide +kernel\n  rw [hl] at hk\n  interval_cases k\n", cch, cch, cch, nchunk));
        for k in 0..nchunk { s.push_str(&format!("  · exact rc_{}\n", k)); }
        s.push_str("\n");
    }
    if v2 { let leadv: Vec<usize> = reps.iter().cloned().collect(); s.push_str(&format!("def lead : List ℕ := {:?}\n\n", leadv)); } else { s.push_str("def lead : List ℕ := (flatN.map fun N => cRep (unpackRec N)).dedup\n\n"); }
    s.push_str(&format!("theorem lead_length : lead.length = {} := by decide +kernel\n\ntheorem flat_length : flatN.length = {} := by decide +kernel\n\n", reps.len(), nrec));
    if v2 { s.push_str("theorem hlead : ∀ N ∈ P.flatMap Prod.snd, cRep (unpackRec N) ∈ lead := by decide +kernel\n\n"); } else { s.push_str("theorem hlead : ∀ N ∈ P.flatMap Prod.snd, cRep (unpackRec N) ∈ lead := fun N hN =>\n  List.mem_dedup.2 (List.mem_map.2 ⟨N, hN, rfl⟩)\n\n"); }
    s.push_str("/-- `StreamHyp'.t2` for this depth-1 node, representatives from `R2Lead` (the class leaders only). -/\ntheorem t2 : ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n2 : NodeW 2 3),\n    (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧ n2.rows = setRow nK.rows 1 y' ∧\n    ∃ rep ∈ R2Lead nK (flatN.map unpackRec) lead, ∃ (g : SP) (U U' : ℕ → ℕ → ℤ),\n      Chain2Rel g n2.rows rep.rows U U' :=\n  t2_lead nK Bn Bd P hcomp hrec lead hlead\n\n");
    // controls
    s.push_str("/-! controls -/\n\n");
    if nrec > 0 {
        s.push_str("theorem ctl_rec : recN (FC.ofCtx ckC) flatN ((flatN.getD 0 0) + 65536 ^ 56) = false := by decide +kernel\n");
        s.push_str("theorem ctl_lead : (flatN.all fun N => (lead.drop 1).contains (cRep (unpackRec N))) = false := by decide +kernel\n");
        let gmax = (0..ng).max_by_key(|&gi| hexg[gi].len()).unwrap();
        s.push_str(&format!("theorem ctl_box : ((rngI {}).all fun t1 => sliceF (FC.ofCtx ckC) 0 {} (Gl.getD {} (0, [])) t1) = false := by decide +kernel\n", t1m, t3m, gmax));
    }
    s.push_str("theorem ctl_sorry : (1 : ℕ) = 2 := by sorry\n\n#print axioms hrad\n#print axioms hcomp\n#print axioms hrec\n#print axioms lead_length\n#print axioms t2\n");
    if nrec > 0 { s.push_str("#print axioms ctl_rec\n#print axioms ctl_lead\n#print axioms ctl_box\n"); }
    s.push_str("#print axioms ctl_sorry\n");
    s.push_str(&foot); wr(&m, s)?; mods.push(m.clone());
    // the position module: leader flat index of every class of this node, in global class-id order (the rollout block order)
    let clsids: Vec<usize> = (0..nc).filter(|&c| rep_hi[c] == kk).collect();
    let rp: Vec<usize> = clsids.iter().map(|c| pos[rep_idx[c]]).collect();
    { let mut tsv = String::new(); for c in clsids.iter() { let f = &recs[rep_idx[c]].1; tsv.push_str(&format!("{}", c)); for k in 0..45 { tsv.push_str(&format!(" {}", f[k])); } tsv.push('\n'); } fs::write(format!("{}/recd_{}.tsv", outd, kk), tsv).map_err(|e| e.to_string())?; }
    let mut s = head(&format!("{}Pos", m), "class ids and leader positions: the interface to the rollout block", &[m.clone(), "T2Link".to_string()]);
    s.push_str(&format!("def clsFirst : ℕ := {}\n\ndef repPos : List ℕ := {:?}\n\ntheorem repPos_length : repPos.length = {} := by decide +kernel\n\ntheorem lead_sub : ∀ j ∈ lead, j ∈ repPos := by decide +kernel\n\ntheorem repPos_nodup : repPos.Nodup := by decide +kernel\n\n/-- the interface to the rollout block: `idx i` is the node of class `clsFirst + i`. -/\ntheorem t2_block (idx : ℕ → NodeW 2 3)\n    (hrows : ∀ i, i < repPos.length → (idx i).rows = setRow nK.rows 1 (cY ((flatN.map unpackRec).getD (repPos.getD i 0) []))) :\n    ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n2 : NodeW 2 3),\n      (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧ n2.rows = setRow nK.rows 1 y' ∧\n      ∃ rep ∈ ({{a | ∃ i, i < repPos.length ∧ a = idx i}} : Set (NodeW 2 3)), ∃ (g : SP) (U U' : ℕ → ℕ → ℤ),\n        Chain2Rel g n2.rows rep.rows U U' :=\n  t2_of_link nK Bn Bd P hcomp hrec lead hlead _ (hlink_of_block nK (flatN.map unpackRec) lead repPos lead_sub idx hrows)\n\n#print axioms t2_block\n", clsids.first().cloned().unwrap_or(0), rp, rp.len()));
    s.push_str(&foot); wr(&format!("{}Pos", m), s)?; mods.push(format!("{}Pos", m));
    fs::write(format!("{}/{}.mods", outd, m), mods.join("\n") + "\n").map_err(|e| e.to_string())?;
    println!("NODE {} : {} children, {} groups, {} leaders, tmax {:?}, bn/bd {}/{}, case0={}, scan modules {}, record chunks {} in {} modules, mods {}", kk, nrec, ng, reps.len(), tmax, bnd.n, bnd.d, case0, sm.len(), nchunk, nrm, mods.len());
    Ok(())
}
