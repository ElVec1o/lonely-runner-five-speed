/-
# L5S3.Accepted : a flag of every near-tight `v` accepted by every filter of the five-speed tree

The generator (`lean5_wp0a`: `children`, `greedy_ok`, `ei_bad`, `radius_bound`, `d1_list`) keeps a child
`t` of a node (new row `h_d`, new lattice `L_d = ℤ h_0 + … + ℤ h_{d-1}`, `d = 1, 2, 3`) iff

  (a) `t` is primitive in `ℤ^{5-d+1}`              <->  `L_d` saturated in `ℤ⁵`            : `PrimChild`
  (b) first nonzero coordinate of `t` positive       <->  sign of `h_{d-1}`                   : `flip` (below)
  (c) `ei_bad` false                                 <->  no `e_i` in `ℚ L_d`                 : `NoCoord`
  (d) `greedy_ok`: no vector of `L_d` shorter than `h_0` (`d = 2, 3`), and for `d = 3` no vector of the
      projected lattice shorter than `π h_1`                                                  : `ShortestFirst`, `ShortestSecond`
  (e) `μ_d² < radius_bound(..)`  = the node test `4 (M(L_k) - 1/5)² < ∑_{k<i<d} μ_i^{-2} + C_d μ_d^{-2}`
      for every `k < d` (`C_1 = 175/27`, `C_2 = 37/9`, `C_3 = 7/3`)                          : `NodeBound`
  (f) depth 1 only: `|h_0|² ≤ 18` (the integer form of (e) at `d = 1, k = 0`)                 : `first_le`

`Accepted F` is the conjunction.  `accepted_of_greedy` : a `Greedy` flag of a primitive `v` with all
`v_i ≠ 0` and `ML v < 1/5` is accepted; `exists_flag_accepted` combines this with `greedyBasis_exists`.
All filters are invariant under `h_i ↦ ± h_i` (they only see lattices, Gram forms and `Dq`): `Greedy` is
shown sign-invariant in `GreedyFlip` (so the sign normalisation (b) can be imposed afterwards).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S3.GreedyFinal
import LRSpectrumFull.L5S3.Reduced34

namespace LRSpectrumFull
namespace L5S3

open Finset

/-! ## Definitions of the filters -/

/-- (a) `L_d` is saturated: integer functionals `ρ_b` with `ρ_b (h_a) = δ_ab` (equivalent to `t` primitive). -/
def PrimChild {v : V5} (F : FlagData v) : Prop :=
  ∀ d : ℕ, d ≤ 4 → ∃ ρ : Fin 5 → ℕ → ℤ, ∀ a < d, ∀ b < d,
    ∑ k, hN F.h a k * ρ k b = if a = b then 1 else 0

/-- The coordinate vector `e_i`. -/
def eVec (i : Fin 5) : V5 := fun k => if k = i then 1 else 0

/-- (c) no coordinate vector lies in the rational span of `L_d` (`ei_bad` is false). -/
def NoCoord {v : V5} (F : FlagData v) : Prop :=
  ∀ (i : Fin 5) (d : ℕ), d ≤ 4 → ¬ InQN d F.h (eVec i)

/-- Quadratic form of the Gram matrix of the first `d` rows (`q = ∑ g_ij c_i c_j` in the generator). -/
def gramQ {v : V5} (F : FlagData v) (d : ℕ) (c : ℕ → ℤ) : ℤ :=
  ∑ i ∈ range d, ∑ j ∈ range d, c i * c j * dot (hN F.h i) (hN F.h j)

/-- (d1) `exists_shorter(g, g_00)` is false: `h_0` is a shortest nonzero vector of `L_d`. -/
def ShortestFirst {v : V5} (F : FlagData v) (d : ℕ) : Prop :=
  ∀ c : ℕ → ℤ, (∃ i < d, c i ≠ 0) → dot (hN F.h 0) (hN F.h 0) ≤ gramQ F d c

/-- Entry of the matrix `s_ij = g_00 g_ij - g_0i g_0j` of the generator (`nd.j == 2`). -/
def sgm {v : V5} (F : FlagData v) (i j : ℕ) : ℤ :=
  dot (hN F.h 0) (hN F.h 0) * dot (hN F.h i) (hN F.h j)
    - dot (hN F.h 0) (hN F.h i) * dot (hN F.h 0) (hN F.h j)

/-- (d2) `exists_shorter(s, s_00)` is false (`d = 3`): `π h_1` is shortest in the projected lattice. -/
def ShortestSecond {v : V5} (F : FlagData v) : Prop :=
  ∀ c1 c2 : ℤ, (c1 ≠ 0 ∨ c2 ≠ 0) →
    sgm F 1 1 ≤ c1 * c1 * sgm F 1 1 + 2 * c1 * c2 * sgm F 1 2 + c2 * c2 * sgm F 2 2

/-- `μ²_{i+1} = Dq i`, extended by `Dq 3` for `i ≥ 3` (a bookkeeping extension to all of `ℕ`). -/
noncomputable def Dext {v : V5} (F : FlagData v) (i : ℕ) : ℝ := ((F.Dq ⟨min i 3, by omega⟩ : ℚ) : ℝ)

/-- `C_d = ∑_{s < 5-d} (4/3)^s` (`175/27, 37/9, 7/3, 1` for `d = 1..4`). -/
noncomputable def Cnode (d : ℕ) : ℝ := ∑ s ∈ range (5 - d), (4 / 3 : ℝ) ^ s

/-- Right-hand side of the node test `k` at depth `d`: `∑_{k ≤ i < d-1} μ_{i+1}^{-2} + C_d μ_d^{-2}`. -/
noncomputable def nodeRHS {v : V5} (F : FlagData v) (d k : ℕ) : ℝ :=
  (∑ i ∈ range (d - 1), if k ≤ i then 1 / Dext F i else 0) + Cnode d * (1 / Dext F (d - 1))

/-- (e) node tests: for every stage `k < d`, every stage witness `x` with `f x ≥ c ≥ 1/5`. -/
def NodeBound {v : V5} (F : FlagData v) (d : ℕ) : Prop :=
  ∀ k < d, ∀ (x : Fin 5 → ℝ) (c : ℝ), StageWitness F k x → 1 / 5 ≤ c → c ≤ fmin x →
    4 * (c - 1 / 5) ^ 2 < nodeRHS F d k

/-- All filters of the depth-1, 2, 3 (and 4) nodes, for one flag. -/
structure Accepted {v : V5} (F : FlagData v) : Prop where
  greedy : Greedy v F.h
  prim : PrimChild F
  noCoord : NoCoord F
  short1 : ∀ d, d ≤ 4 → ShortestFirst F d
  short2 : ShortestSecond F
  reduced : Reduced34 F
  node : ∀ d, 1 ≤ d → d ≤ 4 → NodeBound F d
  first_le : dot (F.h 0) (F.h 0) ≤ 18

/-! ## Proofs -/

theorem Dext_pos {v : V5} (F : FlagData v) (i : ℕ) : 0 < Dext F i := by
  unfold Dext
  exact_mod_cast F.hDpos _

theorem Dext_lt {v : V5} (F : FlagData v) (i : Fin 4) : Dext F i.val = ((F.Dq i : ℚ) : ℝ) := by
  unfold Dext
  have : min i.val 3 = i.val := by have := i.2; omega
  simp only [this]

theorem Dext_step {v : V5} (F : FlagData v) (hr : Reduced34 F) (i : ℕ) :
    3 / 4 * Dext F i ≤ Dext F (i + 1) := by
  by_cases hi : i < 3
  · have h := hr ⟨i, hi⟩
    have e1 : (Fin.castSucc (⟨i, hi⟩ : Fin 3)) = (⟨i, by omega⟩ : Fin 4) := rfl
    have e2 : (Fin.succ (⟨i, hi⟩ : Fin 3)) = (⟨i + 1, by omega⟩ : Fin 4) := rfl
    rw [e1, e2] at h
    have h' : (3 / 4 : ℝ) * ((F.Dq ⟨i, by omega⟩ : ℚ) : ℝ) ≤ ((F.Dq ⟨i + 1, by omega⟩ : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 h
      push_cast at this
      exact this
    have a := Dext_lt F ⟨i, by omega⟩
    have b := Dext_lt F ⟨i + 1, by omega⟩
    simp only at a b
    rw [a, b]; exact h'
  · have h1 : min i 3 = 3 := by omega
    have h2 : min (i + 1) 3 = 3 := by omega
    unfold Dext
    simp only [h1, h2]
    have := F.hDpos ⟨3, by omega⟩
    have h3 : (0 : ℝ) < ((F.Dq ⟨3, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast this
    linarith

theorem Sk_eq_range {v : V5} (F : FlagData v) (k : ℕ) :
    Sk F k = ∑ i ∈ range 4, if k ≤ i then 1 / Dext F i else 0 := by
  unfold Sk
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => if k ≤ i then 1 / Dext F i else 0) 4]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Dext_lt F i]

theorem Cnode_eq (d : ℕ) (hd : 1 ≤ d) (hd4 : d ≤ 4) :
    Cnode d = ∑ s ∈ range (5 - d), (4 / 3 : ℝ) ^ s := rfl

theorem node_of_stage {v : V5} (F : FlagData v) (hv : Primitive v) (hlt : ML v < 1 / 5)
    (hr : Reduced34 F) (d : ℕ) (hd : 1 ≤ d) (hd4 : d ≤ 4) : NodeBound F d := by
  intro k hk x c hx hc hfc
  have hS := stage_prune_free v F k x hv hx hlt c hc hfc
  have hpos : ∀ i, 0 < Dext F i := Dext_pos F
  have hstep : ∀ i, 3 / 4 * Dext F i ≤ Dext F (i + 1) := Dext_step F hr
  have e4 : (4 : ℕ) = (d - 1) + (5 - d) := by omega
  have hsplit : Sk F k = (∑ i ∈ range (d - 1), if k ≤ i then 1 / Dext F i else 0)
      + ∑ s ∈ range (5 - d), 1 / Dext F (d - 1 + s) := by
    rw [Sk_eq_range, e4, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have : k ≤ d - 1 + s := by omega
    simp [this]
  have htail := tail_sum (Dext F) hpos hstep (d - 1) (5 - d)
  have : Sk F k ≤ nodeRHS F d k := by
    rw [hsplit]
    unfold nodeRHS Cnode
    have := htail
    linarith
  linarith

theorem accepted_noCoord {v : V5} (F : FlagData v) (hnz : ∀ i, v i ≠ 0) : NoCoord F := by
  rintro i d hd ⟨a, ha⟩
  apply hnz i
  have h1 : ((v i : ℤ) : ℚ) = ∑ n ∈ range d, a n * ((dot (hN F.h n) v : ℤ) : ℚ) := by
    have e : ((v i : ℤ) : ℚ) = ∑ k : Fin 5, ((eVec i k : ℤ) : ℚ) * (v k : ℚ) := by
      simp [eVec, Finset.sum_ite_eq]
    rw [e]
    simp only [ha, dot]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  have h2 : ∀ n ∈ range d, dot (hN F.h n) v = 0 := by
    intro n hn
    have hn4 : n < 4 := by have := Finset.mem_range.mp hn; omega
    have := F.hv ⟨n, hn4⟩
    simpa [hN, hn4] using this
  have h3 : ((v i : ℤ) : ℚ) = 0 := by
    rw [h1]
    exact Finset.sum_eq_zero (fun n hn => by rw [h2 n hn]; simp)
  exact_mod_cast h3

theorem accepted_prim {v : V5} (F : FlagData v) : PrimChild F := by
  intro d hd
  refine ⟨fun k b => if hb : b < 4 then F.R k ⟨b, hb⟩ else 0, ?_⟩
  intro a ha b hb
  have ha4 : a < 4 := by omega
  have hb4 : b < 4 := by omega
  have := F.hR ⟨a, ha4⟩ ⟨b, hb4⟩
  simp only [hN, ha4, hb4, dite_true]
  rw [this]
  simp [Fin.ext_iff]

theorem dot_sum_sum (d : ℕ) (c : ℕ → ℤ) (x : ℕ → V5) :
    dot (fun k => ∑ i ∈ range d, c i * x i k) (fun k => ∑ i ∈ range d, c i * x i k)
      = ∑ i ∈ range d, ∑ j ∈ range d, c i * c j * dot (x i) (x j) := by
  unfold dot
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem accepted_short1 {v : V5} (F : FlagData v) (hg : Greedy v F.h) (d : ℕ) (hd : d ≤ 4) :
    ShortestFirst F d := by
  intro c ⟨i0, hi0, hc0⟩
  set u : V5 := fun k => ∑ i ∈ range d, c i * hN F.h i k with hu
  have hdv : dot u v = 0 := by
    unfold dot
    have : ∀ k, u k * v k = ∑ i ∈ range d, c i * (hN F.h i k * v k) := by
      intro k; simp only [hu, Finset.sum_mul]; refine Finset.sum_congr rfl (fun i _ => by ring)
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [← Finset.mul_sum]
    have hi4 : i < 4 := by have := Finset.mem_range.mp hi; omega
    have := F.hv ⟨i, hi4⟩
    simp only [dot, hN, hi4, dite_true] at this ⊢
    rw [this]; simp
  have hnq : ¬ InQSpanPrefix F.h 0 u := by
    rintro ⟨c', hc'⟩
    have hz : ∀ k : Fin 5, ∑ m : Fin 4, (if m.val < d then (c m.val : ℚ) else 0) * (F.h m k : ℚ) = 0 := by
      intro k
      have h1 : (u k : ℚ) = 0 := by simpa using hc' k
      have h2 : (u k : ℚ) = ∑ m : Fin 4, (if m.val < d then (c m.val : ℚ) else 0) * (F.h m k : ℚ) := by
        simp only [hu]
        push_cast
        have := prefix_sum_key F.h d hd (fun n => (c n : ℚ)) k
        rw [← this]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        by_cases hm : m.val < d <;> simp [hm, hN_lt]
      rw [← h2]; exact h1
    have := rows_indep F (fun m => if m.val < d then (c m.val : ℚ) else 0) hz ⟨i0, by omega⟩
    simp only [hi0] at this
    exact hc0 (by exact_mod_cast this)
  have := hg 0 (by norm_num) u hdv hnq
  simp only [List.ofFn_succ, List.take_succ_cons, List.take_zero, List.nil_append] at this
  rw [gdl1, gdl1] at this
  have e : dot u u = gramQ F d c := by
    unfold gramQ; exact dot_sum_sum d c (hN F.h)
  have h0 : hN F.h 0 = F.h 0 := by simp [hN]
  rw [← e, h0]
  exact this

theorem accepted_short2 {v : V5} (F : FlagData v) (hg : Greedy v F.h) : ShortestSecond F := by
  intro c1 c2 hc
  set u : V5 := fun k => c1 * F.h 1 k + c2 * F.h 2 k with hu
  have hdv : dot u v = 0 := by
    have h1 := F.hv 1
    have h2 := F.hv 2
    simp only [hu, dot, Fin.sum_univ_five] at h1 h2 ⊢
    linear_combination c1 * h1 + c2 * h2
  have hnq : ¬ InQSpanPrefix F.h 1 u := by
    rintro ⟨c', hc'⟩
    have hz : ∀ k : Fin 5, ∑ m : Fin 4, (![-c' 0, (c1 : ℚ), (c2 : ℚ), 0] : Fin 4 → ℚ) m * (F.h m k : ℚ) = 0 := by
      intro k
      have h1 := hc' k
      simp only [hu, Fin.sum_univ_four] at h1 ⊢
      simp at h1
      simp
      push_cast at h1
      linarith
    have := rows_indep F _ hz
    have a1 := this 1
    have a2 := this 2
    simp at a1 a2
    rcases hc with h | h
    · exact h (by exact_mod_cast a1)
    · exact h (by exact_mod_cast a2)
  have hgl := hg 1 (by norm_num) u hdv hnq
  rw [take_succ_eq 1 (by norm_num), take_append_eq 1 (by norm_num), gramDetList_ofFn,
    gramDetList_ofFn] at hgl
  have e0 : hN F.h 0 = F.h 0 := by simp [hN]
  have e1 : hN F.h 1 = F.h 1 := by simp [hN]
  have e2 : hN F.h 2 = F.h 2 := by simp [hN]
  have hexp : ∀ w : V5, gF (Ef 1 F.h w) = dot (F.h 0) (F.h 0) * dot w w - dot (F.h 0) w * dot w (F.h 0) := by
    intro w
    have e : gF (Ef 1 F.h w)
        = (Matrix.of fun a b : Fin 2 => dot (Ef 1 F.h w a) (Ef 1 F.h w b)).det := rfl
    rw [e, Matrix.det_fin_two]
    simp [Ef, hN, dot_comm' w (F.h 0)]
  rw [hexp, hexp] at hgl
  simp only [Fin.mk_one] at hgl
  have hd1 : dot (F.h 1) (F.h 1) = dot (F.h 1) (F.h 1) := rfl
  have c11 : dot u u = c1 * c1 * dot (F.h 1) (F.h 1) + 2 * c1 * c2 * dot (F.h 1) (F.h 2)
      + c2 * c2 * dot (F.h 2) (F.h 2) := by
    simp only [hu, dot, Fin.sum_univ_five]; ring
  have c01 : dot (F.h 0) u = c1 * dot (F.h 0) (F.h 1) + c2 * dot (F.h 0) (F.h 2) := by
    simp only [hu, dot, Fin.sum_univ_five]; ring
  have c10 : dot u (F.h 0) = c1 * dot (F.h 0) (F.h 1) + c2 * dot (F.h 0) (F.h 2) := by
    simp only [hu, dot, Fin.sum_univ_five]; ring
  have c21 : dot (F.h 1) (F.h 0) = dot (F.h 0) (F.h 1) := dot_comm' _ _
  rw [c11, c01, c10, c21] at hgl
  simp only [sgm, e0, e1, e2]
  nlinarith [hgl]

theorem Dq0_eq {v : V5} (F : FlagData v) : F.Dq 0 = (dot (F.h 0) (F.h 0) : ℚ) := by
  have h := F.hLDL 0 0
  have l01 : F.Lq 0 1 = 0 := F.hLlow 0 1 (by decide)
  have l02 : F.Lq 0 2 = 0 := F.hLlow 0 2 (by decide)
  have l03 : F.Lq 0 3 = 0 := F.hLlow 0 3 (by decide)
  have u0 := F.hLunit 0
  simp only [Fin.sum_univ_four, l01, l02, l03, u0] at h
  linarith

theorem accepted_first_le {v : V5} (F : FlagData v) (hv : Primitive v) (hlt : ML v < 1 / 5)
    (hr : Reduced34 F) : dot (F.h 0) (F.h 0) ≤ 18 := by
  have hnb := node_of_stage F hv hlt hr 1 le_rfl (by norm_num) 0 (by norm_num) (fun _ => 1 / 2) (1 / 2)
    (fun i hi => absurd hi (Nat.not_lt_zero _)) (by norm_num) (by
      unfold fmin
      refine Finset.le_inf' _ _ (fun i _ => ?_)
      exact nearestIntDist_ge (by norm_num) (by norm_num) (le_refl _) (by norm_num))
  have hD : Dext F 0 = ((dot (F.h 0) (F.h 0) : ℤ) : ℝ) := by
    have := Dext_lt F 0
    simp only [Fin.val_zero] at this
    rw [this, Dq0_eq]
    push_cast; rfl
  have hpos : (0 : ℝ) < ((dot (F.h 0) (F.h 0) : ℤ) : ℝ) := by rw [← hD]; exact Dext_pos F 0
  unfold nodeRHS at hnb
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.sub_self] at hnb
  have hC : Cnode 1 = 175 / 27 := by
    unfold Cnode; exact node_constants.1
  rw [hC, hD] at hnb
  by_contra hn
  have h19 : (19 : ℝ) ≤ ((dot (F.h 0) (F.h 0) : ℤ) : ℝ) := by
    have : (19 : ℤ) ≤ dot (F.h 0) (F.h 0) := by omega
    exact_mod_cast this
  rw [mul_one_div, lt_div_iff₀ hpos] at hnb
  nlinarith

theorem accepted_of_greedy {v : V5} (F : FlagData v) (hv : Primitive v) (hnz : ∀ i, v i ≠ 0)
    (hlt : ML v < 1 / 5) (hg : Greedy v F.h) : Accepted F := by
  have hr : Reduced34 F := fun i => ratio34_thm F hg i
  exact ⟨hg, accepted_prim F, accepted_noCoord F hnz, fun d hd => accepted_short1 F hg d hd,
    accepted_short2 F hg, hr, fun d h1 h2 => node_of_stage F hv hlt hr d h1 h2,
    accepted_first_le F hv hlt hr⟩

/-- Every primitive `v` with all entries nonzero and `ML v < 1/5` has a flag accepted by every filter. -/
theorem exists_flag_accepted (v : V5) (hv : Primitive v) (hnz : ∀ i, v i ≠ 0)
    (hlt : ML v < 1 / 5) : ∃ F : FlagData v, Accepted F := by
  obtain ⟨F, hg⟩ := flag_exists v hv
  exact ⟨F, accepted_of_greedy F hv hnz hlt hg⟩

end L5S3
end LRSpectrumFull
