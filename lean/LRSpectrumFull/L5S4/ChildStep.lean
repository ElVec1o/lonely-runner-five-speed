/-
# L5S4.ChildStep : the child-step lemma of the five-speed tree

Case-tree certificate, part 4.  Tree nodes are data `NodeW j d` (rows `l`, a basis `b` of `L^⊥`
with right inverse `r`, saturation functionals `s`, stage witnesses `(X_k, W_k)` of `M(L_k)`, `k ≤ j`).

* `ChildPass n y` : the conjunction of the filters of `lib.rs::children` for the candidate row `y` (primitive `t`, first
  nonzero coordinate positive, `ei_bad` false, `greedy_ok` for the node level, the radius test `q·bd < bn·g`); the box
  `|t_i| ≤ tmax_i` is a CONSEQUENCE (`childPass_box`), so the loop's list is the set of `t` passing exactly these tests.
* `child_step` : if `F` is an accepted flag whose first `j` rows are the rows of the node, and `t = tvec b (h_j)` has its first
  nonzero coordinate positive, then `ChildPass n h_j`.  `child_step_signed` removes the sign hypothesis (`h_j ↦ -h_j`).
* `prefixEq_child` : any row `y'` with the same coordinates `t` gives rows of the same chain (`PrefixEq`), so the flag whose
  first rows are the ENUMERATED child rows exists (`accepted_prefix`).
* `accepted_two_le`, `accepted_h0_primitive` : the depth-1 row is primitive with `2 ≤ |h_0|²`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.Records
import LRSpectrumFull.L5S4.Link
import LRSpectrumFull.L5S4.Prim
import LRSpectrumFull.L5S4.Short
import LRSpectrumFull.L5S4.Short2
import LRSpectrumFull.L5S4.EiBad
import LRSpectrumFull.L5S4.Radius
import LRSpectrumFull.L5S4.LeafWin

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## 1. Row families, witnesses, node data -/

/-- Replace row `j` of a (padded) row family by `y` (the child row). -/
def setRow (rows : Fin 4 → V5) (j : ℕ) (y : V5) : Fin 4 → V5 := fun i => if i.val = j then y else rows i

theorem hN_setRow_lt (rows : Fin 4 → V5) (j : ℕ) (y : V5) (m : ℕ) (hm : m < j) :
    hN (setRow rows j y) m = hN rows m := by
  by_cases h4 : m < 4
  · simp [hN, h4, setRow, Nat.ne_of_lt hm]
  · simp [hN, h4]

theorem hN_setRow_eq (rows : Fin 4 → V5) (j : ℕ) (y : V5) (hj : j < 4) :
    hN (setRow rows j y) j = y := by
  simp [hN, hj, setRow]

/-- The first `d` rows of a padded family as a `Fin d`-family. -/
def rowsR (rw : Fin 4 → V5) (d : ℕ) : Fin d → V5 := fun i => hN rw i.val

/-- Leading Gram minor `G_i` of a padded row family. -/
def Gm (rw : Fin 4 → V5) (i : ℕ) : ℤ := gF (rowsR rw i)

def sgmR (rw : Fin 4 → V5) (i j : ℕ) : ℤ :=
  dot (hN rw 0) (hN rw 0) * dot (hN rw i) (hN rw j) - dot (hN rw 0) (hN rw i) * dot (hN rw 0) (hN rw j)

/-- The matrix `s` of `lib.rs::greedy_ok` for `nd.j = 2`. -/
def sMatR (rw : Fin 4 → V5) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![sgmR rw 1 1, sgmR rw 1 2; sgmR rw 1 2, sgmR rw 2 2]

theorem rowsR_congr {rw rw' : Fin 4 → V5} {d : ℕ} (h : ∀ m < d, hN rw m = hN rw' m) :
    rowsR rw d = rowsR rw' d := by
  funext i; exact h i.val i.2

theorem sMatR_congr {rw rw' : Fin 4 → V5} (h : ∀ m < 3, hN rw m = hN rw' m) :
    sMatR rw = sMatR rw' ∧ sgmR rw 1 1 = sgmR rw' 1 1 := by
  have e : ∀ i j, i < 3 → j < 3 → sgmR rw i j = sgmR rw' i j := by
    intro i j hi hj
    unfold sgmR
    rw [h 0 (by norm_num), h i hi, h j hj]
  refine ⟨?_, e 1 1 (by norm_num) (by norm_num)⟩
  unfold sMatR
  rw [e 1 1 (by norm_num) (by norm_num), e 1 2 (by norm_num) (by norm_num), e 2 2 (by norm_num) (by norm_num)]

/-- The value `c = min_i ‖X_i / W‖` of a witness (`witness_ok`). -/
def cOf (w : V5 × ℤ) : ℚ := ((wMin w.1 w.2 : ℤ) : ℚ) / ((w.2 : ℤ) : ℚ)

/-- `S_k = ∑_{k ≤ i < j} G_i / G_{i+1}` of the radius test at a node of level `j`. -/
def SArr (rw : Fin 4 → V5) (j k : ℕ) : ℚ :=
  ∑ i ∈ range j, if k ≤ i then (Gm rw i : ℚ) / (Gm rw (i + 1) : ℚ) else 0

/-- The stages `k ≤ j` with `den_k > 0` (those over which `radius_bound` takes its minimum). -/
def radSet (wit : ℕ → V5 × ℤ) (rw : Fin 4 → V5) (j : ℕ) : Finset ℕ :=
  (range (j + 1)).filter (fun k => 0 < 4 * (cOf (wit k) - 1 / 5) ^ 2 - SArr rw j k)

/-- `bn / bd = radius_bound(ms, inv, j+1, C, [0..j])` (the unwrap succeeds iff `radSet` is nonempty). -/
noncomputable def radFrac (C : ℚ) (wit : ℕ → V5 × ℤ) (rw : Fin 4 → V5) (j : ℕ)
    (hK : (radSet wit rw j).Nonempty) : ℚ :=
  (radSet wit rw j).inf' hK (fun k => C / (4 * (cOf (wit k) - 1 / 5) ^ 2 - SArr rw j k))

/-- A node of the tree at level `j` (`d = 5 - j`), with the data the generator stores or recomputes. -/
structure NodeW (j d : ℕ) where
  rows : Fin 4 → V5
  b : Fin d → V5
  s : Fin j → V5
  r : Fin d → V5
  id : NodeId (fun i : Fin j => hN rows i.val) b s r
  wit : ℕ → V5 × ℤ
  w0 : wit 0 = (fun _ => 1, 2)
  wok : ∀ k ≤ j, 0 < (wit k).2 ∧ ∀ i : Fin 4, i.val < k → (wit k).2 ∣ dot (rows i) (wit k).1
  wge : ∀ k ≤ j, (1 : ℚ) / 5 ≤ cOf (wit k)
  rk : (radSet wit rows j).Nonempty

/-- First nonzero coordinate positive (`rec_box`: `lo = 0` before the first nonzero coordinate). -/
def FirstPos {d : ℕ} (t : Fin d → ℤ) : Prop := ∃ m : Fin d, 0 < t m ∧ ∀ i : Fin d, i < m → t i = 0

/-- The filters of `lib.rs::children` (candidate row `y` of the child of the node `n`, level `j ∈ {1, 2}`):
primitive `t`, sign, `ei_bad`, `greedy_ok` (`exists_shorter` on the Gram matrix of `l ++ [y]`, and for `j = 2` on `s`),
and the radius test `q·bd < bn·g`. -/
def ChildPass {j d : ℕ} (n : NodeW j d) (y : V5) : Prop :=
  GcdOne (tvec n.b y) ∧ FirstPos (tvec n.b y) ∧ ¬ eiBad n.b (tvec n.b y) ∧
  ¬ existsShorter (gramM (rowsR (setRow n.rows j y) (j + 1))) (dot (hN n.rows 0) (hN n.rows 0)) ∧
  (j = 2 → ¬ existsShorter (sMatR (setRow n.rows j y)) (sgmR (setRow n.rows j y) 1 1)) ∧
  qform n.b y * ((radFrac (Cq (j + 1)) n.wit n.rows j n.rk).den : ℤ)
    < (radFrac (Cq (j + 1)) n.wit n.rows j n.rk).num * (gramK n.b).det

/-- The box of the generator is implied by the radius test. -/
theorem childPass_box {j d : ℕ} (hjd : j + d = 5) (n : NodeW j d) (y : V5) (hp : ChildPass n y) (i : Fin d) :
    |tvec n.b y i| ≤ isqrtI ((radFrac (Cq (j + 1)) n.wit n.rows j n.rk).num * gramK n.b i i
      / ((radFrac (Cq (j + 1)) n.wit n.rows j n.rk).den : ℤ)) :=
  box_covers hjd n.id y i _ _ (by exact_mod_cast Rat.den_pos _) hp.2.2.2.2.2

/-! ## 2. Small lemmas: signs, primitive depth-1 row -/

theorem tvec_neg {d : ℕ} (b : Fin d → V5) (y : V5) :
    tvec b (fun c => - y c) = fun i => - tvec b y i := by
  funext i; simp [tvec, dot, Finset.sum_neg_distrib]

theorem exists_firstpos {d : ℕ} (t : Fin d → ℤ) (h : ∃ m, t m ≠ 0) :
    FirstPos t ∨ FirstPos (fun i => - t i) := by
  classical
  obtain ⟨a, ha⟩ := h
  set S := (Finset.univ : Finset (Fin d)).filter (fun m => t m ≠ 0) with hS
  have hne : S.Nonempty := ⟨a, by simp [hS, ha]⟩
  set m := S.min' hne with hm
  have hmS : t m ≠ 0 := by
    have := Finset.min'_mem S hne
    simpa [hS] using this
  have hbefore : ∀ i : Fin d, i < m → t i = 0 := by
    intro i hi
    by_contra hti
    have : i ∈ S := by simp [hS, hti]
    exact absurd (Finset.min'_le S i this) (not_le.2 hi)
  rcases lt_or_gt_of_ne hmS with h1 | h1
  · right; exact ⟨m, by simpa using h1, fun i hi => by simp [hbefore i hi]⟩
  · left; exact ⟨m, h1, hbefore⟩

theorem accepted_h0_primitive {v : V5} (F : FlagData v) (hacc : Accepted F) : Primitive (F.h 0) := by
  intro d hd
  obtain ⟨ρ, hρ⟩ := hacc.prim 1 (by norm_num)
  have h1 := hρ 0 (by norm_num) 0 (by norm_num)
  have h2 : ∑ k, F.h 0 k * ρ k 0 = 1 := by simpa [hN] using h1
  have : d ∣ 1 := by
    rw [← h2]; exact Finset.dvd_sum (fun k _ => Dvd.dvd.mul_right (hd k) _)
  exact Int.isUnit_iff.1 (isUnit_of_dvd_one this)

theorem accepted_two_le {v : V5} (hnz : ∀ i, v i ≠ 0) (F : FlagData v) (hacc : Accepted F) :
    2 ≤ dot (F.h 0) (F.h 0) := by
  have hpos : 0 < dot (F.h 0) (F.h 0) := by
    have := gF_rows_pos F 1 (by norm_num)
    simpa [gF_eq_det, gramM, rowsF, Matrix.det_unique, hN] using this
  by_contra hcon
  have h1 : dot (F.h 0) (F.h 0) = 1 := by omega
  have hv0 := F.hv 0
  have hex : ∃ k0, F.h 0 k0 ≠ 0 := by
    by_contra hh
    push_neg at hh
    have : dot (F.h 0) (F.h 0) = 0 := by simp [dot, hh]
    omega
  obtain ⟨k0, hk0⟩ := hex
  have hsq : ∀ k, F.h 0 k * F.h 0 k ≤ 1 := fun k => by
    have := sq_le_dot (F.h 0) k; omega
  have hk0sq : 1 ≤ F.h 0 k0 * F.h 0 k0 := by
    have : 0 < F.h 0 k0 * F.h 0 k0 := mul_self_pos.2 hk0
    omega
  have hzero : ∀ k, k ≠ k0 → F.h 0 k = 0 := by
    intro k hk
    have hpair : F.h 0 k0 * F.h 0 k0 + F.h 0 k * F.h 0 k ≤ 1 := by
      rw [← h1, ← Finset.sum_pair (f := fun x => F.h 0 x * F.h 0 x) (Ne.symm hk)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => mul_self_nonneg _)
    nlinarith [mul_self_nonneg (F.h 0 k)]
  have : dot (F.h 0) v = F.h 0 k0 * v k0 := by
    unfold dot
    rw [Finset.sum_eq_single k0]
    intro k _ hk; rw [hzero k hk]; ring
    intro hh; exact absurd (Finset.mem_univ _) hh
  rw [this] at hv0
  rcases mul_eq_zero.1 hv0 with h | h
  · exact hk0 h
  · exact hnz k0 h

/-! ## 3. The child-step lemma -/

theorem inQN_of_ext {v : V5} (F : FlagData v) {j : ℕ} (u : V5)
    (h : InQExt (fun i : Fin j => hN F.h i.val) (hN F.h j) u) : InQN (j + 1) F.h u := by
  obtain ⟨c, c0, hc⟩ := h
  refine ⟨fun m => if hm : m < j then c ⟨m, hm⟩ else c0, fun k => ?_⟩
  rw [hc k, Finset.sum_range_succ]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun m => (if hm : m < j then c ⟨m, hm⟩ else c0) * (hN F.h m k : ℚ)) j]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [i.2]
  · simp

theorem nodeF_of_rows {v : V5} (F : FlagData v) {j d : ℕ} (hj : j ≤ 4) (n : NodeW j d)
    (hrows : ∀ i : Fin 4, i.val < j → F.h i = n.rows i) :
    NodeId (fun i : Fin j => hN F.h i.val) n.b n.s n.r := by
  have : (fun i : Fin j => hN F.h i.val) = (fun i : Fin j => hN n.rows i.val) := by
    funext i
    have hi4 : i.val < 4 := by omega
    simp [hN, hi4, hrows ⟨i.val, hi4⟩ i.2]
  rw [this]; exact n.id

theorem hN_rows_eq {v : V5} (F : FlagData v) {j d : ℕ} (hj : j ≤ 4) (n : NodeW j d)
    (hrows : ∀ i : Fin 4, i.val < j → F.h i = n.rows i) (m : ℕ) (hm : m < j) :
    hN F.h m = hN n.rows m := by
  have h4 : m < 4 := by omega
  simp [hN, h4, hrows ⟨m, h4⟩ hm]

/-- **Child step.**  An accepted flag `F` whose first `j` rows are the rows of the node `n` (`1 ≤ j ≤ 2`) and whose next
row has `t = tvec b h_j` with first nonzero coordinate positive passes every filter of the generator at `n`. -/
theorem child_step {v : V5} (F : FlagData v) (hacc : Accepted F) {j d : ℕ} (hjd : j + d = 5)
    (hj1 : 1 ≤ j) (hj2 : j ≤ 2) (n : NodeW j d)
    (hrows : ∀ i : Fin 4, i.val < j → F.h i = n.rows i)
    (hpos : FirstPos (tvec n.b (hN F.h j))) : ChildPass n (hN F.h j) := by
  have hj4 : j < 4 := by omega
  have hy : hN F.h j = F.h ⟨j, hj4⟩ := by simp [hN, hj4]
  have hnodeF := nodeF_of_rows F (by omega) n hrows
  have hFN := hN_rows_eq F (by omega) n hrows
  have hrw : ∀ m < j + 1, hN (setRow n.rows j (hN F.h j)) m = hN F.h m := by
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | h
    · rw [hN_setRow_lt _ _ _ _ h, hFN m h]
    · rw [h, hN_setRow_eq _ _ _ hj4]
  have h0 : hN n.rows 0 = hN F.h 0 := (hFN 0 (by omega)).symm
  have hgcd : GcdOne (tvec n.b (hN F.h j)) := by
    rw [hy]; exact gcd_of_primChild F hjd hj4 hnodeF hacc.prim
  have hex : ∃ m, tvec n.b (hN F.h j) m ≠ 0 := by
    by_contra hh
    push_neg at hh
    have : Finset.univ.gcd (tvec n.b (hN F.h j)) = 0 := by
      rw [Finset.gcd_eq_zero_iff]; intro x _; exact hh x
    exact absurd (hgcd.symm.trans this) one_ne_zero
  have hnoei : ¬ eiBad n.b (tvec n.b (hN F.h j)) := by
    intro h
    rw [eiBad_iff hjd hnodeF _ hex] at h
    obtain ⟨i, hi⟩ := h
    exact hacc.noCoord i (j + 1) (by omega) (inQN_of_ext F _ hi)
  have g1 : ¬ existsShorter (gramM (rowsF F (j + 1))) (dot (hN F.h 0) (hN F.h 0)) :=
    (shortestFirst_iff F (j + 1) (by omega)).1 (hacc.short1 (j + 1) (by omega))
  have hrowsEq : rowsR (setRow n.rows j (hN F.h j)) (j + 1) = rowsF F (j + 1) :=
    rowsR_congr (fun m hm => hrw m hm)
  have g1' : ¬ existsShorter (gramM (rowsR (setRow n.rows j (hN F.h j)) (j + 1)))
      (dot (hN n.rows 0) (hN n.rows 0)) := by
    rw [hrowsEq, h0]; exact g1
  have g2' : j = 2 → ¬ existsShorter (sMatR (setRow n.rows j (hN F.h j)))
      (sgmR (setRow n.rows j (hN F.h j)) 1 1) := by
    intro hj
    have hs := (shortestSecond_iff F).1 hacc.short2
    have hc := sMatR_congr (rw := setRow n.rows j (hN F.h j)) (rw' := F.h) (fun m hm => hrw m (by omega))
    rw [hc.1, hc.2]
    exact hs
  -- radius test
  have hGj : leadMinor (gram F) j = gF n.b := (flag_minor_node F hjd hj4 hnodeF).1
  have hGq : leadMinor (gram F) (j + 1) = qform n.b (hN F.h j) := by
    rw [hy]; exact (flag_minor_node F hjd hj4 hnodeF).2.1
  have hgpos : 0 < (gramK n.b).det := by
    have := leadMinor_pos' F j; rw [hGj] at this; exact this
  have hqpos : 0 < qform n.b (hN F.h j) := by
    have := leadMinor_pos' F (j + 1); rw [hGq] at this; exact this
  have hGm : ∀ i, i ≤ j → leadMinor (gram F) i = Gm n.rows i := by
    intro i hi
    rw [leadMinor_eq_gF F i (by omega)]
    unfold Gm
    congr 1
    funext m
    exact hFN m.val (by omega)
  have hC : 0 < Cq (j + 1) := by
    unfold Cq
    exact Finset.sum_pos (fun s _ => by positivity) ⟨0, Finset.mem_range.2 (by omega)⟩
  have hall : ∀ k < j + 1, 4 * (cOf (n.wit k) - 1 / 5) ^ 2 < SArr n.rows j k
      + Cq (j + 1) * (1 / (((qform n.b (hN F.h j) : ℤ) : ℚ) / (((gramK n.b).det : ℤ) : ℚ))) := by
    intro k hk
    obtain ⟨hW, hdiv⟩ := n.wok k (by omega)
    have hok : WitnessOk F k (n.wit k).1 (n.wit k).2 :=
      ⟨hW, fun i hi => by rw [hrows i (by omega)]; exact hdiv i hi⟩
    have hb := nodeBound_to_rat F (j + 1) (by omega) (by omega) (hacc.node (j + 1) (by omega) (by omega))
      k hk (n.wit k).1 (n.wit k).2 hok (cOf (n.wit k)) rfl (n.wge k (by omega))
    simp only [ratRHS, Nat.add_sub_cancel] at hb
    have e1 : (∑ i ∈ range j, if k ≤ i then ((leadMinor (gram F) i : ℤ) : ℚ)
        / ((leadMinor (gram F) (i + 1) : ℤ) : ℚ) else 0) = SArr n.rows j k := by
      unfold SArr
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' := Finset.mem_range.1 hi
      rw [hGm i (by omega), hGm (i + 1) (by omega)]
    have e2 : ((leadMinor (gram F) j : ℤ) : ℚ) / ((leadMinor (gram F) (j + 1) : ℤ) : ℚ)
        = 1 / (((qform n.b (hN F.h j) : ℤ) : ℚ) / (((gramK n.b).det : ℤ) : ℚ)) := by
      rw [one_div_div, hGj, hGq]; rfl
    rw [e1, e2] at hb
    exact hb
  have hrad : qform n.b (hN F.h j) * ((radFrac (Cq (j + 1)) n.wit n.rows j n.rk).den : ℤ)
      < (radFrac (Cq (j + 1)) n.wit n.rows j n.rk).num * (gramK n.b).det := by
    unfold radFrac
    exact (accept_iff (j + 1) (fun k => cOf (n.wit k) - 1 / 5) (fun k => SArr n.rows j k) (Cq (j + 1)) hC
      (qform n.b (hN F.h j)) ((gramK n.b).det) hgpos hqpos n.rk).2 hall
  exact ⟨hgcd, hpos, hnoei, g1', g2', hrad⟩

/-- The sign of `h_j` can be chosen so that `t` has first nonzero coordinate positive. -/
theorem child_step_signed {v : V5} (hv : Primitive v) (hnz : ∀ i, v i ≠ 0) (hlt : ML v < 1 / 5)
    (F : FlagData v) (hacc : Accepted F) {j d : ℕ} (hjd : j + d = 5) (hj1 : 1 ≤ j) (hj2 : j ≤ 2)
    (n : NodeW j d) (hrows : ∀ i : Fin 4, i.val < j → F.h i = n.rows i) :
    ∃ F' : FlagData v, Accepted F' ∧ (∀ i : Fin 4, i.val < j → F'.h i = n.rows i) ∧
      ChildPass n (hN F'.h j) := by
  have hj4 : j < 4 := by omega
  have hy : hN F.h j = F.h ⟨j, hj4⟩ := by simp [hN, hj4]
  have hnodeF := nodeF_of_rows F (by omega) n hrows
  have hgcd : GcdOne (tvec n.b (hN F.h j)) := by
    rw [hy]; exact gcd_of_primChild F hjd hj4 hnodeF hacc.prim
  have hex : ∃ m, tvec n.b (hN F.h j) m ≠ 0 := by
    by_contra hh
    push_neg at hh
    have : Finset.univ.gcd (tvec n.b (hN F.h j)) = 0 := by
      rw [Finset.gcd_eq_zero_iff]; intro x _; exact hh x
    exact absurd (hgcd.symm.trans this) one_ne_zero
  rcases exists_firstpos _ hex with hp | hp
  · exact ⟨F, hacc, hrows, child_step F hacc hjd hj1 hj2 n hrows hp⟩
  · let ε : Fin 4 → ℤ := fun i => if i = ⟨j, hj4⟩ then -1 else 1
    have hε : ∀ i, ε i = 1 ∨ ε i = -1 := fun i => by
      by_cases h : i = ⟨j, hj4⟩ <;> simp [ε, h]
    have hacc' : Accepted (F.flip ε hε) :=
      accepted_of_greedy _ hv hnz hlt (greedy_flip F hacc.greedy ε hε)
    have hrows' : ∀ i : Fin 4, i.val < j → (F.flip ε hε).h i = n.rows i := by
      intro i hi
      have hne : i ≠ ⟨j, hj4⟩ := fun h => by rw [h] at hi; exact lt_irrefl _ hi
      rw [← hrows i hi]
      funext k
      simp [FlagData.flip, ε, hne]
    have hrowj : hN (F.flip ε hε).h j = fun c => - hN F.h j c := by
      funext c
      simp [hN, hj4, FlagData.flip, ε]
    refine ⟨F.flip ε hε, hacc', hrows', child_step _ hacc' hjd hj1 hj2 n hrows' ?_⟩
    rw [hrowj, tvec_neg]
    exact hp

/-! ## 4. The row `y'` of the enumerated child: same chain -/

theorem latRows_self (r : Fin 4 → V5) (i : ℕ) : LatRows r (i + 1) (hN r i) := by
  refine ⟨fun m => if m = i then 1 else 0, fun a => ?_⟩
  simp [Finset.sum_ite_eq']

theorem prefixEq_child {v : V5} (F : FlagData v) {j d : ℕ} (hjd : j + d = 5) (hj : j < 4) (n : NodeW j d)
    (hrows : ∀ i : Fin 4, i.val < j → F.h i = n.rows i) (y' : V5)
    (hy : ∀ i, dot (n.b i) y' = dot (n.b i) (hN F.h j)) :
    PrefixEq F (setRow n.rows j y') (j + 1) := by
  have hnodeF := nodeF_of_rows F (by omega) n hrows
  have hFN := hN_rows_eq F (by omega) n hrows
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hij | hij
  · have e : hN (setRow n.rows j y') i = hN F.h i := by
      rw [hN_setRow_lt _ _ _ _ hij, hFN i hij]
    rw [e]
    exact ⟨latRows_self F.h i, by have := latRows_self (setRow n.rows j y') i; rwa [e] at this⟩
  · have key : LatRows F.h (j + 1) (hN (setRow n.rows j y') j) ∧ LatRows (setRow n.rows j y') (j + 1) (hN F.h j) := by
      have hd := lat_of_same_coords hjd hnodeF (hN F.h j) y' (fun i => (hy i).symm)
      set β : ℕ → ℤ := fun m => if hm : m < j then dot (n.s ⟨m, hm⟩) (fun c => y' c - hN F.h j c) else 0 with hβ
      have hsum : ∀ a, ∑ k : Fin j, dot (n.s k) (fun c => y' c - hN F.h j c) * hN F.h k.val a
          = ∑ m ∈ range j, β m * hN F.h m a := by
        intro a
        rw [← Fin.sum_univ_eq_sum_range (fun m => β m * hN F.h m a) j]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp [hβ, k.2]
      have hy'a : ∀ a, y' a = hN F.h j a + ∑ m ∈ range j, β m * hN F.h m a := by
        intro a
        rw [← hsum a]
        exact hd a
      rw [hN_setRow_eq _ _ _ hj]
      refine ⟨⟨fun m => if m < j then β m else 1, fun a => ?_⟩, ⟨fun m => if m < j then - β m else 1, fun a => ?_⟩⟩
      · rw [Finset.sum_range_succ, hy'a a]
        have : ∑ m ∈ range j, (if m < j then β m else 1) * hN F.h m a = ∑ m ∈ range j, β m * hN F.h m a :=
          Finset.sum_congr rfl (fun m hm => by simp [Finset.mem_range.1 hm])
        rw [this]; simp; ring
      · rw [Finset.sum_range_succ, hN_setRow_eq _ _ _ hj]
        have : ∑ m ∈ range j, (if m < j then - β m else 1) * hN (setRow n.rows j y') m a
            = - ∑ m ∈ range j, β m * hN F.h m a := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl (fun m hm => ?_)
          have hm' := Finset.mem_range.1 hm
          rw [hN_setRow_lt _ _ _ _ hm', ← hFN m hm']
          simp [hm']
        rw [this, hy'a a]; simp
    rw [hij]; exact key

end L5S4
end LRSpectrumFull
