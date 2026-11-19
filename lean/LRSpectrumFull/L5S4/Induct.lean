/-
# L5S4.Induct : the T1 -> T2 -> T3 induction (completeness of the tree) and `tree_complete_unconditional`

Case-tree certificate, part 4.  `StreamHyp` replaces the single hypothesis `TreeHyp.leaf` of
`Records.lean` by the three per-depth statements the S4 checkers must establish (what the kernel loops verify about the
streams); `leaf_cover` PROVES the induction from them with `child_step`, `chain1_rep_flag`, `chain2_rep_flag`,
`prefixEq_child`, `accepted_prefix`, `depth1_cover`, `leaf_lo_sound`, `leaf_hi_sound`, `crit_link`.

* `t1` : every sorted depth-1 vector `T1Ok h` is the first row of a stored depth-1 node.
* `t2` : every candidate row that passes `ChildPass` at a depth-1 node is represented (same coordinates `t`) by an
  enumerated depth-2 node, together with a class map `Chain2Rel` to a stored depth-2 class representative.
* `t3` : likewise at depth-2 representatives, ending in a leaf relation `LeafRel` (critical identification, or a stored
  leaf class whose range contains the integer window).
* `lines` : the T4/T5 line stage (named hypothesis, WP7).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.ChildStep

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## 1. Leaf data -/

def padL3 (l : Fin 3 → V5) : Fin 4 → V5 := fun i => if h : i.val < 3 then l ⟨i.val, h⟩ else fun _ => 0
def padB2 (b : Fin 2 → V5) : Fin 4 → V5 := fun i => if h : i.val < 2 then b ⟨i.val, h⟩ else fun _ => 0

/-- `V_0 = (1,2,3,4)`, `V_1 = (1,3,4,7)`. -/
def critV (ck : Fin 2) : Fin 4 → ℤ := if ck = 0 then ![1, 2, 3, 4] else ![1, 3, 4, 7]

/-- `crit_basis` of `cert.rs`: rows `(V_ck, 0)` and `e_5`. -/
def critBasis (ck : Fin 2) : Fin 4 → V5 := fun i a =>
  if i.val = 0 then (if h : a.val < 4 then critV ck ⟨a.val, h⟩ else 0)
  else if i.val = 1 then (if a.val = 4 then 1 else 0) else 0

/-- The integers `n = |v|²` of the leaf window `lo ≤ n/G_3 < hi` of `leaf_info`
(`lo` = three lower bounds at `ρ = 3/4`, `hi = min_{den_k > 0} 1/den_k`; the integer range of the generator is
`[⌈lo G_3⌉, ⌈hi G_3⌉ - 1]`, `range_iff`). -/
def LeafWinMem (n3 : NodeW 3 2) (n : ℤ) : Prop :=
  (3 / 4 : ℚ) * ((Gm n3.rows 3 : ℚ) / (Gm n3.rows 2 : ℚ)) ≤ (n : ℚ) / (Gm n3.rows 3 : ℚ) ∧
  (3 / 4 : ℚ) * ((Gm n3.rows 2 : ℚ) / (Gm n3.rows 1 : ℚ)) - (1 / 4) * ((Gm n3.rows 3 : ℚ) / (Gm n3.rows 2 : ℚ))
    ≤ (n : ℚ) / (Gm n3.rows 3 : ℚ) ∧
  (3 / 4 : ℚ) * ((Gm n3.rows 1 : ℚ) / (Gm n3.rows 0 : ℚ))
    - (1 / 4) * ((Gm n3.rows 2 : ℚ) / (Gm n3.rows 1 : ℚ) + (Gm n3.rows 3 : ℚ) / (Gm n3.rows 2 : ℚ))
    ≤ (n : ℚ) / (Gm n3.rows 3 : ℚ) ∧
  ∀ k < 4, 0 < denK (fun i => Gm n3.rows i) (cOf (n3.wit k) - 1 / 5) k →
    (n : ℚ) / (Gm n3.rows 3 : ℚ) < 1 / denK (fun i => Gm n3.rows i) (cOf (n3.wit k) - 1 / 5) k

/-- What the checker verifies at a leaf (`T3` check): `c_3 = 1/5` (critical leaf) needs an identification of `K_3` with
the critical lattice (`leq_ok`); otherwise, when the integer window is nonempty, a stored leaf class `cl` with a lattice
map (`Leaf3Rel`) and one merged range containing the whole window. -/
def LeafRel (C : Certificate) (n3 : NodeW 3 2) : Prop :=
  (cOf (n3.wit 3) = 1 / 5 → ∃ (ck : Fin 2) (g : SP) (U U' : ℕ → ℕ → ℤ),
      LeqOkN 2 (fun i => g.act (padB2 n3.b i)) (critBasis ck) U U') ∧
  (cOf (n3.wit 3) ≠ 1 / 5 → (∃ n, LeafWinMem n3 n) →
    ∃ cl ∈ C.t4, (∃ (g : SP) (U U' : ℕ → ℕ → ℤ), Leaf3Rel g n3.rows (padL3 cl.l) U U') ∧
      ∃ r ∈ cl.ranges, ∀ n, LeafWinMem n3 n → r.1 ≤ n ∧ n ≤ r.2)

/-- The per-depth statements the S4 checkers must establish; none is proved here except through `leaf_cover`. -/
structure StreamHyp (C : Certificate) (R1 : Set (NodeW 1 4)) (R2 : Set (NodeW 2 3)) : Prop where
  t1 : ∀ h : V5, T1Ok h → ∃ n ∈ R1, hN n.rows 0 = h
  t2 : ∀ n ∈ R1, ∀ y : V5, ChildPass n y →
    ∃ (y' : V5) (n2 : NodeW 2 3), (∀ i, dot (n.b i) y' = dot (n.b i) y) ∧ n2.rows = setRow n.rows 1 y' ∧
      ∃ rep ∈ R2, ∃ (g : SP) (U U' : ℕ → ℕ → ℤ), Chain2Rel g n2.rows rep.rows U U'
  t3 : ∀ n ∈ R2, ∀ y : V5, ChildPass n y →
    ∃ (y' : V5) (n3 : NodeW 3 2), (∀ i, dot (n.b i) y' = dot (n.b i) y) ∧ n3.rows = setRow n.rows 2 y' ∧
      LeafRel C n3
  lines : ∀ cl ∈ C.t4, ∀ u : V5, Primitive u → (∀ i, u i ≠ 0) → (∀ i j, i ≠ j → |u i| ≠ |u j|) →
    InClass cl u → (∃ r ∈ C.t5, ∃ g : SP, g.act u = r.v) ∨ 1 / 5 ≤ ML u

/-! ## 2. Congruences for relations -/

theorem hN_eq_of_rows {d : ℕ} (hd : d ≤ 4) (F r : Fin 4 → V5) (h : ∀ i : Fin 4, i.val < d → F i = r i)
    (m : ℕ) (hm : m < d) : hN F m = hN r m := by
  have h4 : m < 4 := by omega
  simp [hN, h4, h ⟨m, h4⟩ hm]

theorem leqOkN_congr {d : ℕ} {t t' b : Fin 4 → V5} {U U' : ℕ → ℕ → ℤ}
    (h : ∀ i < d, hN t i = hN t' i) (hl : LeqOkN d t b U U') : LeqOkN d t' b U U' := by
  refine ⟨fun i hi c => ?_, fun i hi c => ?_⟩
  · rw [← h i hi]; exact hl.1 i hi c
  · rw [hl.2 i hi c]
    exact Finset.sum_congr rfl (fun k hk => by rw [h k (Finset.mem_range.1 hk)])

theorem leqOkN_act_congr {d : ℕ} (hd : d ≤ 4) {g : SP} {r r' b : Fin 4 → V5} {U U' : ℕ → ℕ → ℤ}
    (h : ∀ i : Fin 4, i.val < d → r i = r' i) (hl : LeqOkN d (fun i => g.act (r i)) b U U') :
    LeqOkN d (fun i => g.act (r' i)) b U U' :=
  leqOkN_congr (fun i hi => by
    rw [hN_act r g i, hN_act r' g i, hN_eq_of_rows hd r r' h i hi]) hl

theorem chain2Rel_congr {g : SP} {r r' rep : Fin 4 → V5} {U U' : ℕ → ℕ → ℤ}
    (h : ∀ i : Fin 4, i.val < 2 → r i = r' i) (hr : Chain2Rel g r rep U U') : Chain2Rel g r' rep U U' := by
  obtain ⟨h1, h2⟩ := hr
  refine ⟨?_, leqOkN_act_congr (by norm_num) h h2⟩
  unfold Chain1Rel at h1 ⊢
  rw [← hN_eq_of_rows (by norm_num) r r' h 0 (by norm_num)]
  exact h1

/-! ## 3. Critical leaves: identification of `K_3` with the critical lattice -/

theorem crit_link {v' : V5} (n3 : NodeW 3 2)
    (hv' : ∀ i : Fin 4, i.val < 3 → dot (n3.rows i) v' = 0) (ck : Fin 2) (g : SP) (U U' : ℕ → ℕ → ℤ)
    (hle : LeqOkN 2 (fun i => g.act (padB2 n3.b i)) (critBasis ck) U U') : CritTorus ck (g.act v') := by
  have hu : ∀ k : Fin 3, dot ((fun i : Fin 3 => hN n3.rows i.val) k) v' = 0 := by
    intro k
    have h4 : k.val < 4 := by omega
    have := hv' ⟨k.val, h4⟩ k.2
    simpa [hN, h4] using this
  have hexp := lat_of_orth_dual (by norm_num : 3 + 2 = 5) n3.id v' hu
  set ρ : Fin 2 → ℤ := fun i => dot (n3.r i) v' with hρ
  have hact : ∀ a, g.act v' a = ∑ i : Fin 2, ρ i * g.act (n3.b i) a := by
    intro a
    simp only [SP.act]
    rw [hexp (g.σ a), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hb : ∀ (i : Fin 2) a, g.act (n3.b i) a
      = U i.val 0 * hN (critBasis ck) 0 a + U i.val 1 * hN (critBasis ck) 1 a := by
    intro i a
    have h1 := hle.1 i.val i.2 a
    have h2 : hN (fun i => g.act (padB2 n3.b i)) i.val a = g.act (n3.b i) a := by
      have h4 : i.val < 4 := by omega
      simp [hN, h4, padB2, i.2]
    rw [← h2, h1]
    simp [Finset.sum_range_succ]
  have hc0 : ∀ a : Fin 5, hN (critBasis ck) 0 a = if h : a.val < 4 then critV ck ⟨a.val, h⟩ else 0 := by
    intro a; simp [hN, critBasis]
  have hc1 : ∀ a : Fin 5, hN (critBasis ck) 1 a = if a.val = 4 then 1 else 0 := by
    intro a; simp [hN, critBasis]
  refine ⟨∑ i : Fin 2, ρ i * U i.val 0, ∑ i : Fin 2, ρ i * U i.val 1, ?_, ?_⟩
  · intro i
    have hlt : i.val < 4 := i.2
    have hne : i.val ≠ 4 := by have := i.2; omega
    have e : g.act v' i.castSucc = (∑ x : Fin 2, ρ x * U x.val 0) * hN (critBasis ck) 0 i.castSucc
        + (∑ x : Fin 2, ρ x * U x.val 1) * hN (critBasis ck) 1 i.castSucc := by
      rw [hact]
      simp only [hb, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [e, hc0, hc1]
    simp [hne, hlt, critV]
  · have e : g.act v' 4 = (∑ x : Fin 2, ρ x * U x.val 0) * hN (critBasis ck) 0 4
        + (∑ x : Fin 2, ρ x * U x.val 1) * hN (critBasis ck) 1 4 := by
      rw [hact]
      simp only [hb, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [e, hc0, hc1]
    simp

/-! ## 4. Leaf window: the real flag lies in the window of the enumerated leaf -/

theorem leaf_window_mem {v : V5} (hv : Primitive v) (F : FlagData v) (hacc : Accepted F) (n3 : NodeW 3 2)
    (hrows : ∀ i : Fin 4, i.val < 3 → F.h i = n3.rows i) : LeafWinMem n3 (dot v v) := by
  have hFN : ∀ m < 3, hN F.h m = hN n3.rows m := fun m hm => hN_eq_of_rows (by norm_num) F.h n3.rows hrows m hm
  have hGm : ∀ i, i ≤ 3 → leadMinor (gram F) i = Gm n3.rows i := by
    intro i hi
    rw [leadMinor_eq_gF F i (by omega)]
    unfold Gm
    congr 1
    funext m
    exact hFN m.val (by omega)
  have hlo := leaf_lo_sound F hacc.reduced
  have D0 : F.Dq 0 = (leadMinor (gram F) 1 : ℚ) / (leadMinor (gram F) 0 : ℚ) := Dq_minors_thm v F 0
  have D1 : F.Dq 1 = (leadMinor (gram F) 2 : ℚ) / (leadMinor (gram F) 1 : ℚ) := Dq_minors_thm v F 1
  have D2 : F.Dq 2 = (leadMinor (gram F) 3 : ℚ) / (leadMinor (gram F) 2 : ℚ) := Dq_minors_thm v F 2
  have D3 := Dq3_eq F hv
  rw [hGm 0 (by norm_num), hGm 1 (by norm_num)] at D0
  rw [hGm 1 (by norm_num), hGm 2 (by norm_num)] at D1
  rw [hGm 2 (by norm_num), hGm 3 (by norm_num)] at D2
  rw [hGm 3 (by norm_num)] at D3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← D3, ← D2]; exact hlo.1
  · rw [← D3, ← D2, ← D1]; exact hlo.2.1
  · rw [← D3, ← D2, ← D1, ← D0]; exact hlo.2.2
  · intro k hk hden
    obtain ⟨hW, hdiv⟩ := n3.wok k (by omega)
    have hok : WitnessOk F k (n3.wit k).1 (n3.wit k).2 :=
      ⟨hW, fun i hi => by rw [hrows i (by omega)]; exact hdiv i hi⟩
    have hdenG : denK (fun n => leadMinor (gram F) n) (cOf (n3.wit k) - 1 / 5) k
        = denK (fun i => Gm n3.rows i) (cOf (n3.wit k) - 1 / 5) k := by
      unfold denK
      congr 1
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' := Finset.mem_range.1 hi
      dsimp only
      rw [hGm i (by omega), hGm (i + 1) (by omega)]
    rw [← hdenG] at hden ⊢
    have := leaf_hi_sound F hacc k hk (n3.wit k).1 (n3.wit k).2 hok (cOf (n3.wit k)) rfl (n3.wge k (by omega)) hden
    rw [← D3]
    exact this

/-! ## 5. The induction -/

theorem leaf_cover {C : Certificate} {R1 : Set (NodeW 1 4)} {R2 : Set (NodeW 2 3)}
    (H : StreamHyp C R1 R2) (v : V5) (hnt : NearTight v) :
    (∃ (k : Fin 2) (g : SP), CritTorus k (g.act v)) ∨ ∃ cl ∈ C.t4, ∃ g : SP, InClass cl (g.act v) := by
  obtain ⟨hv, hnz, hlt⟩ := hnt
  obtain ⟨F, hacc⟩ := exists_flag_accepted v hv hnz hlt
  -- depth 1: the sorted representative
  obtain ⟨g1, hg1⟩ := depth1_cover (F.h 0) (accepted_h0_primitive F hacc) (accepted_two_le hnz F hacc) hacc.first_le
  obtain ⟨n1, hn1, hn1h⟩ := H.t1 _ hg1
  have hv1 : Primitive (g1.act v) := primitive_act hv g1
  have hnz1 := nz_act hnz g1
  have hlt1 : ML (g1.act v) < 1 / 5 := by rw [ML_act]; exact hlt
  obtain ⟨F1, hacc1, hF1⟩ := chain1_rep_flag hv hnz hlt F hacc g1 n1.rows
    (Or.inl (by rw [hn1h]; simp [hN]))
  have hrows1 : ∀ i : Fin 4, i.val < 1 → F1.h i = n1.rows i := by
    intro i hi
    have : i = 0 := by ext; simp; omega
    rw [this]; exact hF1
  -- depth 2
  obtain ⟨F1s, hacc1s, hrows1s, hpass1⟩ :=
    child_step_signed hv1 hnz1 hlt1 F1 hacc1 (by norm_num : 1 + 4 = 5) le_rfl (by norm_num) n1 hrows1
  obtain ⟨y', n2, hy', hn2, rep, hrep, g2, U, U', hrel⟩ := H.t2 n1 hn1 _ hpass1
  have hP : PrefixEq F1s n2.rows 2 := by
    rw [hn2]; exact prefixEq_child F1s (by norm_num : 1 + 4 = 5) (by norm_num) n1 hrows1s y' hy'
  obtain ⟨F2, hacc2, -, hF2rows⟩ := accepted_prefix hv1 hnz1 hlt1 F1s hacc1s.greedy n2.rows 2 (by norm_num) hP
  have hrel2 : Chain2Rel g2 F2.h rep.rows U U' := chain2Rel_congr (fun i hi => (hF2rows i hi).symm) hrel
  obtain ⟨F3, hacc3, hF30, hF31⟩ := chain2_rep_flag hv1 hnz1 hlt1 F2 hacc2 g2 rep.rows U U' hrel2
  have hv2 : Primitive (g2.act (g1.act v)) := primitive_act hv1 g2
  have hnz2 := nz_act hnz1 g2
  have hlt2 : ML (g2.act (g1.act v)) < 1 / 5 := by rw [ML_act]; exact hlt1
  have hrows3 : ∀ i : Fin 4, i.val < 2 → F3.h i = rep.rows i := by
    intro i hi
    have hi' : i.val = 0 ∨ i.val = 1 := by omega
    rcases hi' with h | h
    · have : i = 0 := Fin.ext h
      rw [this]; exact hF30
    · have : i = 1 := Fin.ext h
      rw [this]; exact hF31
  -- depth 3
  obtain ⟨F3s, hacc3s, hrows3s, hpass3⟩ :=
    child_step_signed hv2 hnz2 hlt2 F3 hacc3 (by norm_num : 2 + 3 = 5) (by norm_num) le_rfl rep hrows3
  obtain ⟨y'', n3, hy'', hn3, hleaf⟩ := H.t3 rep hrep _ hpass3
  have hP3 : PrefixEq F3s n3.rows 3 := by
    rw [hn3]; exact prefixEq_child F3s (by norm_num : 2 + 3 = 5) (by norm_num) rep hrows3s y'' hy''
  obtain ⟨F4, hacc4, -, hF4rows⟩ := accepted_prefix hv2 hnz2 hlt2 F3s hacc3s.greedy n3.rows 3 (by norm_num) hP3
  have hperp : ∀ i : Fin 4, i.val < 3 → dot (n3.rows i) (g2.act (g1.act v)) = 0 := by
    intro i hi
    rw [← hF4rows i hi]; exact F4.hv i
  by_cases hc3 : cOf (n3.wit 3) = 1 / 5
  · obtain ⟨ck, g, Uc, Uc', hle⟩ := hleaf.1 hc3
    left
    refine ⟨ck, g.mul (g2.mul g1), ?_⟩
    rw [act_mul, act_mul]
    exact crit_link n3 hperp ck g Uc Uc' hle
  · have hmem : LeafWinMem n3 (dot (g2.act (g1.act v)) (g2.act (g1.act v))) :=
      leaf_window_mem hv2 F4 hacc4 n3 hF4rows
    obtain ⟨cl, hcl, ⟨g, Ul, Ul', hl3⟩, r, hr, hrng⟩ := hleaf.2 hc3 ⟨_, hmem⟩
    right
    refine ⟨cl, hcl, g.mul (g2.mul g1), ?_, r, hr, ?_⟩
    · intro i
      have hl3' : Leaf3Rel g F4.h (padL3 cl.l) Ul Ul' := leqOkN_act_congr (by norm_num) (fun i hi => (hF4rows i hi).symm) hl3
      have := leaf_orth F4 g (padL3 cl.l) Ul Ul' hl3' i.val i.2
      have h4 : i.val < 4 := by omega
      rw [act_mul, act_mul]
      simpa [hN, h4, padL3, i.2] using this
    · rw [act_mul, act_mul, dot_act, dot_act, dot_act]
      have := hrng _ hmem
      rw [dot_act, dot_act] at this
      exact this

/-- **The tree theorem, from the per-depth statements.**  Every near-tight `v` with pairwise distinct absolute entries lies,
up to a signed permutation, on a critical torus, or is a stored residual tuple. -/
theorem tree_complete_unconditional {C : Certificate} {R1 : Set (NodeW 1 4)} {R2 : Set (NodeW 2 3)}
    (H : StreamHyp C R1 R2) (v : V5) (hnt : NearTight v) (hdist : ∀ i j, i ≠ j → |v i| ≠ |v j|) :
    (∃ (k : Fin 2) (g : SP), CritTorus k (g.act v)) ∨ (∃ r ∈ C.t5, ∃ g : SP, g.act v = r.v) := by
  rcases leaf_cover H v hnt with hc | ⟨cl, hcl, g, hu⟩
  · exact Or.inl hc
  · obtain ⟨hv, hnz, hlt⟩ := hnt
    have hd : ∀ i j, i ≠ j → |g.act v i| ≠ |g.act v j| := by
      intro i j hij
      simp only [SP.act, abs_mul]
      rcases g.hε i with a | a <;> rcases g.hε j with b | b <;> simp [a, b] <;>
        exact hdist _ _ (fun h => hij (g.σ.injective h))
    rcases H.lines cl hcl (g.act v) (primitive_act hv g) (nz_act hnz g) hd hu with ⟨r, hr, g2, hg2⟩ | hge
    · refine Or.inr ⟨r, hr, g2.mul g, ?_⟩
      rw [act_mul]; exact hg2
    · exact absurd (by rw [ML_act] at hge; exact hge) (not_le.2 hlt)

end L5S4
end LRSpectrumFull
