/-
# L5S4.GD3K3 : the LEAF GLUE of the depth-3 child step (stage S4 block 11)

For a depth-2 node `n` and a stored child (the coordinates `t` of a chunk row) the leaf record `LeafRec` carries the
representative `y'` (so no lookup is needed), the leaf node data (`K_3` basis `b`, right inverse `r`, saturation `s`, the stage-3
witness `x3/w3`) and the class data.  `leafOf` builds the `LeafW` (the `NodeW 3 2` without `rk`, repair F1) from the record;
the witnesses of stages 1, 2 are inherited from `n`.

* `leafOk n r` : the Boolean of one record (facts, `c_3 = 1/5` critical or `c_3 > 1/5`; for `c_3 > 1/5` the integer window of
  the leaf is contained in `[rlo, rhi]` (`winOk`: a closed-form integer test of the three lower terms and of the four upper
  terms of `leaf_info`, `rho = 3/4`), and for kind 2 the class map on the reduced rows);
* `leaf_sound` : a checked record gives a `LeafW` with `rows = setRow n.rows 2 y'` and `LeafRelW C` (the class and its range
  enter as the hypothesis `hT4`: the stored class table `C.t4` is NOT part of this block);
* `t3_leaves` : with the chunk completeness of `GD3K2` and an alignment `storedOf cks = recs.map t`, every `y` with
  `ChildPass n y` has a stored `y'` and a leaf `n3 : LeafW` with `LeafRelW C n3`: the `StreamHyp'.t3` clause of the node.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GD3K2

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

structure LeafRec where
  t : ℤ × ℤ × ℤ
  y : V5
  b : List V5
  r : List V5
  s : List V5
  x3 : V5
  w3 : ℤ
  kind : ℕ
  ck : Fin 2
  rlo : ℤ
  rhi : ℤ
  gp : GR
  u : List (List ℤ)
  u' : List (List ℤ)
  cl : List V5
  steps : List (ℕ × ℕ × ℤ)

def LeafRec.facts (n : NodeW 2 3) (r : LeafRec) : Prop :=
  (dot (n.b 0) r.y = r.t.1 ∧ dot (n.b 1) r.y = r.t.2.1 ∧ dot (n.b 2) r.y = r.t.2.2) ∧
  (∀ (i : Fin 2) (k : Fin 3), dot (bL r.b i) (hN (setRow n.rows 2 r.y) k.val) = 0) ∧
  (∀ i k : Fin 3, dot (hN (setRow n.rows 2 r.y) i.val) (sL r.s k) = if i = k then 1 else 0) ∧
  (∀ i k : Fin 2, dot (bL r.b i) (bL r.r k) = if i = k then 1 else 0) ∧
  (0 < r.w3 ∧ r.w3 ∣ dot (n.rows 0) r.x3 ∧ r.w3 ∣ dot (n.rows 1) r.x3 ∧ r.w3 ∣ dot r.y r.x3 ∧
    r.w3 ≤ 5 * wMin r.x3 r.w3)

instance (n : NodeW 2 3) (r : LeafRec) : Decidable (r.facts n) := by unfold LeafRec.facts; infer_instance

theorem setRow2_lt (n : NodeW 2 3) (y : V5) (i : Fin 4) (hi : i.val < 2) : setRow n.rows 2 y i = n.rows i := by
  simp only [setRow]
  rw [if_neg (by omega)]

def leafOf (n : NodeW 2 3) (r : LeafRec) (hf : r.facts n) : LeafW where
  rows := setRow n.rows 2 r.y
  b := bL r.b
  s := sL r.s
  r := bL r.r
  id := ⟨hf.2.1, hf.2.2.1, hf.2.2.2.1⟩
  wit := fun k => if k ≤ 2 then n.wit k else (r.x3, r.w3)
  w0 := by simpa using n.w0
  wok := by
    intro k hk
    by_cases hk2 : k ≤ 2
    · simp only [hk2, if_true]
      refine ⟨(n.wok k hk2).1, fun i hi => ?_⟩
      rw [setRow2_lt n r.y i (by omega)]
      exact (n.wok k hk2).2 i hi
    · have hk3 : k = 3 := by omega
      subst hk3
      simp only [show ¬ (3 ≤ 2) by norm_num, if_false]
      obtain ⟨hw, d0, d1, d2, -⟩ := hf.2.2.2.2
      refine ⟨hw, fun i hi => ?_⟩
      have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
      rcases this with h0 | h1 | h2
      · rw [setRow2_lt n r.y i (by omega)]
        have : i = ⟨0, by norm_num⟩ := Fin.ext h0
        subst this; exact d0
      · rw [setRow2_lt n r.y i (by omega)]
        have : i = ⟨1, by norm_num⟩ := Fin.ext h1
        subst this; exact d1
      · have e : setRow n.rows 2 r.y i = r.y := by simp [setRow, h2]
        rw [e]; exact d2
  wge := by
    intro k hk
    by_cases hk2 : k ≤ 2
    · simp only [hk2, if_true]; exact n.wge k hk2
    · simp only [hk2, if_false]
      exact cOf_ge hf.2.2.2.2.1 hf.2.2.2.2.2.2.2.2

/-! ## Window arithmetic -/

def hiK (N D G3 rhi : ℤ) : Bool := decide (0 < N) && decide (G3 * D ≤ (rhi + 1) * N)

def winOk (G1 G2 G3 M1 W1 M2 W2 M3 W3 rlo rhi : ℤ) : Bool :=
  decide (0 < G1) && decide (0 < G2) && decide (0 < G3) && decide (0 < W1) && decide (0 < W2) && decide (0 < W3) &&
  (decide ((rlo - 1) * (4 * G2) < 3 * G3 * G3) ||
    decide ((rlo - 1) * (4 * G1 * G2) < 3 * G2 * G2 * G3 - G1 * G3 * G3) ||
    decide ((rlo - 1) * (4 * G1 * G2) < 3 * G1 * G1 * G2 * G3 - G3 * (G2 * G2 + G3 * G1))) &&
  (hiK (radN 1 2 (G2 * G3 + G1 * G1 * G3 + G1 * G2 * G2) (G1 * G2 * G3)) (radD 2 (G1 * G2 * G3)) G3 rhi ||
    hiK (radN M1 W1 (G1 * G3 + G2 * G2) (G2 * G3)) (radD W1 (G2 * G3)) G3 rhi ||
    hiK (radN M2 W2 G2 G3) (radD W2 G3) G3 rhi || hiK (radN M3 W3 0 1) (radD W3 1) G3 rhi)

theorem lo_step (x : ℚ) (n rlo : ℤ) (hx : (rlo : ℚ) - 1 < x) (hn : x ≤ n) : rlo ≤ n := by
  have h1 : (rlo : ℚ) - 1 < n := lt_of_lt_of_le hx hn
  have h2 : rlo - 1 < n := by exact_mod_cast h1
  omega

theorem hi_step (N D G3 rhi n : ℤ) (hN : 0 < N) (hD : 0 < D) (hG3 : 0 < G3) (hle : G3 * D ≤ (rhi + 1) * N)
    (h : (n : ℚ) / G3 < 1 / ((N : ℚ) / D)) : n ≤ rhi := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hGq : (0 : ℚ) < G3 := by exact_mod_cast hG3
  rw [div_lt_iff₀ hGq] at h
  have e : 1 / ((N : ℚ) / D) * G3 = D * G3 / N := by field_simp
  rw [e, lt_div_iff₀ hNq] at h
  have h2 : n * N < D * G3 := by exact_mod_cast h
  by_contra hc
  push_neg at hc
  have h3 : (rhi + 1) * N ≤ n * N := Int.mul_le_mul_of_nonneg_right (by omega) hN.le
  nlinarith

theorem gram3_eq (rw : Fin 4 → V5) :
    Gm rw 3 = dot (hN rw 0) (hN rw 0) * (dot (hN rw 1) (hN rw 1) * dot (hN rw 2) (hN rw 2) - dot (hN rw 1) (hN rw 2) * dot (hN rw 2) (hN rw 1))
      - dot (hN rw 0) (hN rw 1) * (dot (hN rw 1) (hN rw 0) * dot (hN rw 2) (hN rw 2) - dot (hN rw 1) (hN rw 2) * dot (hN rw 2) (hN rw 0))
      + dot (hN rw 0) (hN rw 2) * (dot (hN rw 1) (hN rw 0) * dot (hN rw 2) (hN rw 1) - dot (hN rw 1) (hN rw 1) * dot (hN rw 2) (hN rw 0)) := by
  unfold Gm gF
  simp [Matrix.det_fin_three, rowsR]
  ring

theorem denK_zero (n3 : LeafW) (G1 G2 G3 : ℤ) (h1 : Gm n3.rows 1 = G1) (h2 : Gm n3.rows 2 = G2) (h3 : Gm n3.rows 3 = G3)
    (p1 : 0 < G1) (p2 : 0 < G2) (p3 : 0 < G3) (m : ℚ) :
    denK (fun i => Gm n3.rows i) m 0 =
      4 * m ^ 2 - (((G2 * G3 + G1 * G1 * G3 + G1 * G2 * G2 : ℤ) : ℚ) / ((G1 * G2 * G3 : ℤ) : ℚ)) := by
  have q1 : (G1 : ℚ) ≠ 0 := by exact_mod_cast p1.ne'
  have q2 : (G2 : ℚ) ≠ 0 := by exact_mod_cast p2.ne'
  have q3 : (G3 : ℚ) ≠ 0 := by exact_mod_cast p3.ne'
  unfold denK
  norm_num [Finset.sum_range_succ, Gm_zero, h1, h2, h3]
  push_cast
  field_simp <;> ring

theorem denK_one (n3 : LeafW) (G1 G2 G3 : ℤ) (h1 : Gm n3.rows 1 = G1) (h2 : Gm n3.rows 2 = G2) (h3 : Gm n3.rows 3 = G3)
    (p2 : 0 < G2) (p3 : 0 < G3) (m : ℚ) :
    denK (fun i => Gm n3.rows i) m 1 =
      4 * m ^ 2 - (((G1 * G3 + G2 * G2 : ℤ) : ℚ) / ((G2 * G3 : ℤ) : ℚ)) := by
  have q2 : (G2 : ℚ) ≠ 0 := by exact_mod_cast p2.ne'
  have q3 : (G3 : ℚ) ≠ 0 := by exact_mod_cast p3.ne'
  unfold denK
  norm_num [Finset.sum_range_succ, h1, h2, h3]
  push_cast
  field_simp <;> ring

theorem denK_two (n3 : LeafW) (G2 G3 : ℤ) (h2 : Gm n3.rows 2 = G2) (h3 : Gm n3.rows 3 = G3) (m : ℚ) :
    denK (fun i => Gm n3.rows i) m 2 = 4 * m ^ 2 - (((G2 : ℤ) : ℚ) / ((G3 : ℤ) : ℚ)) := by
  unfold denK
  norm_num [Finset.sum_range_succ, h2, h3]

theorem denK_three (n3 : LeafW) (m : ℚ) :
    denK (fun i => Gm n3.rows i) m 3 = 4 * m ^ 2 - (((0 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)) := by
  unfold denK
  norm_num [Finset.sum_range_succ]

theorem winOk_sound (n3 : LeafW) (G1 G2 G3 M1 W1 M2 W2 M3 W3 rlo rhi : ℤ)
    (hG1 : Gm n3.rows 1 = G1) (hG2 : Gm n3.rows 2 = G2) (hG3 : Gm n3.rows 3 = G3)
    (hc0 : cOf (n3.wit 0) = ((1 : ℤ) : ℚ) / ((2 : ℤ) : ℚ))
    (hc1 : cOf (n3.wit 1) = (M1 : ℚ) / W1) (hc2 : cOf (n3.wit 2) = (M2 : ℚ) / W2)
    (hc3 : cOf (n3.wit 3) = (M3 : ℚ) / W3)
    (h : winOk G1 G2 G3 M1 W1 M2 W2 M3 W3 rlo rhi = true) (n : ℤ) (hn : LeafWinMemW n3 n) :
    rlo ≤ n ∧ n ≤ rhi := by
  unfold winOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, w1⟩, w2⟩, w3⟩, hlo⟩, hhi⟩ := h
  have q1 : (G1 : ℚ) ≠ 0 := by exact_mod_cast p1.ne'
  have q2 : (G2 : ℚ) ≠ 0 := by exact_mod_cast p2.ne'
  have q3 : (G3 : ℚ) ≠ 0 := by exact_mod_cast p3.ne'
  have p1q : (0 : ℚ) < G1 := by exact_mod_cast p1
  have p2q : (0 : ℚ) < G2 := by exact_mod_cast p2
  have p3q : (0 : ℚ) < G3 := by exact_mod_cast p3
  unfold LeafWinMemW at hn
  obtain ⟨hA, hB, hC, hD⟩ := hn
  simp only [Gm_zero, hG1, hG2, hG3] at hA hB hC
  constructor
  · have hA' := (le_div_iff₀ p3q).1 hA
    have hB' := (le_div_iff₀ p3q).1 hB
    have hC' := (le_div_iff₀ p3q).1 hC
    rcases hlo with (hl | hl) | hl
    · refine lo_step _ n rlo ?_ hA'
      have e : (3 / 4 : ℚ) * ((G3 : ℚ) / G2) * G3 = 3 * G3 * G3 / (4 * G2) := by field_simp
      rw [e, lt_div_iff₀ (by positivity)]
      exact_mod_cast hl
    · refine lo_step _ n rlo ?_ hB'
      have e : ((3 / 4 : ℚ) * ((G2 : ℚ) / G1) - (1 / 4) * ((G3 : ℚ) / G2)) * G3 =
          (3 * G2 * G2 * G3 - G1 * G3 * G3) / (4 * G1 * G2) := by field_simp
      rw [e, lt_div_iff₀ (by positivity)]
      exact_mod_cast hl
    · refine lo_step _ n rlo ?_ hC'
      have e : ((3 / 4 : ℚ) * ((G1 : ℚ) / ((1 : ℤ) : ℚ)) - (1 / 4) * ((G2 : ℚ) / G1 + (G3 : ℚ) / G2)) * G3 =
          (3 * G1 * G1 * G2 * G3 - G3 * (G2 * G2 + G3 * G1)) / (4 * G1 * G2) := by
        field_simp <;> (push_cast; ring)
      rw [e, lt_div_iff₀ (by positivity)]
      exact_mod_cast hl
  · simp only [hG3] at hD
    have key : ∀ (k : ℕ) (hk : k < 4) (N D : ℤ) (hN : 0 < N) (hD0 : 0 < D) (hle : G3 * D ≤ (rhi + 1) * N)
        (hdk : denK (fun i => Gm n3.rows i) (cOf (n3.wit k) - 1 / 5) k = (N : ℚ) / D), n ≤ rhi := by
      intro k hk N D hN hD0 hle hdk
      have h1 := hD k hk
      rw [hdk] at h1
      exact hi_step N D G3 rhi n hN hD0 p3 hle (h1 (div_pos (by exact_mod_cast hN) (by exact_mod_cast hD0)))
    have b0 : 0 < G1 * G2 * G3 := mul_pos (mul_pos p1 p2) p3
    have b1 : 0 < G2 * G3 := mul_pos p2 p3
    rcases hhi with ((hh | hh) | hh) | hh
    · unfold hiK at hh
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
      obtain ⟨hN, hle⟩ := hh
      refine key 0 (by norm_num) _ _ hN (radD_pos 2 _ (by norm_num) b0) hle ?_
      rw [denK_zero n3 G1 G2 G3 hG1 hG2 hG3 p1 p2 p3, hc0]
      exact den_eq 1 2 _ _ (by norm_num) b0
    · unfold hiK at hh
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
      obtain ⟨hN, hle⟩ := hh
      refine key 1 (by norm_num) _ _ hN (radD_pos W1 _ w1 b1) hle ?_
      rw [denK_one n3 G1 G2 G3 hG1 hG2 hG3 p2 p3, hc1]
      exact den_eq M1 W1 _ _ w1 b1
    · unfold hiK at hh
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
      obtain ⟨hN, hle⟩ := hh
      refine key 2 (by norm_num) _ _ hN (radD_pos W2 _ w2 p3) hle ?_
      rw [denK_two n3 G2 G3 hG2 hG3, hc2]
      exact den_eq M2 W2 _ _ w2 p3
    · unfold hiK at hh
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
      obtain ⟨hN, hle⟩ := hh
      refine key 3 (by norm_num) _ _ hN (radD_pos W3 _ w3 (by norm_num)) hle ?_
      rw [denK_three n3, hc3]
      exact den_eq M3 W3 _ _ w3 (by norm_num)

/-! ## The record checker -/

/-- critical leaf: `w3 = 5 wMin` and the identification of `K_3` with the critical lattice. -/
noncomputable def critOk (r : LeafRec) : Bool :=
  if h : gOk r.gp then
    decide (LeqOkN 2 (fun i => (gSP r.gp h).act (padB2 (bL r.b) i)) (critBasis r.ck) (matL r.u) (matL r.u'))
  else false

/-- class map on the pair-reduced rows of the leaf. -/
noncomputable def mapOk (n : NodeW 2 3) (r : LeafRec) : Bool :=
  if h : gOk r.gp then
    stepsValid 3 r.steps &&
    decide (LeqOkN 3 (fun i => (gSP r.gp h).act (applySteps r.steps (setRow n.rows 2 r.y) i)) (rowsL r.cl)
      (matL r.u) (matL r.u'))
  else false

def leafG1 (n : NodeW 2 3) : ℤ := dot (hN n.rows 0) (hN n.rows 0)
def leafG2 (n : NodeW 2 3) : ℤ :=
  dot (hN n.rows 0) (hN n.rows 0) * dot (hN n.rows 1) (hN n.rows 1) - dot (hN n.rows 0) (hN n.rows 1) * dot (hN n.rows 1) (hN n.rows 0)
def leafG3 (n : NodeW 2 3) (y : V5) : ℤ :=
  dot (hN n.rows 0) (hN n.rows 0) * (dot (hN n.rows 1) (hN n.rows 1) * dot y y - dot (hN n.rows 1) y * dot y (hN n.rows 1))
    - dot (hN n.rows 0) (hN n.rows 1) * (dot (hN n.rows 1) (hN n.rows 0) * dot y y - dot (hN n.rows 1) y * dot y (hN n.rows 0))
    + dot (hN n.rows 0) y * (dot (hN n.rows 1) (hN n.rows 0) * dot y (hN n.rows 1) - dot (hN n.rows 1) (hN n.rows 1) * dot y (hN n.rows 0))

/-- window test of a record (`rhi = rlo - 1` for kind 1: an empty window). -/
def leafWin (n : NodeW 2 3) (r : LeafRec) : Bool :=
  winOk (leafG1 n) (leafG2 n) (leafG3 n r.y) (wMin (n.wit 1).1 (n.wit 1).2) (n.wit 1).2 (wMin (n.wit 2).1 (n.wit 2).2)
    (n.wit 2).2 (wMin r.x3 r.w3) r.w3 r.rlo (if r.kind = 1 then r.rlo - 1 else r.rhi)

noncomputable def leafOk (n : NodeW 2 3) (r : LeafRec) : Bool :=
  decide (r.facts n) &&
  (if r.kind = 0 then decide (r.w3 = 5 * wMin r.x3 r.w3) && critOk r
   else decide (r.w3 < 5 * wMin r.x3 r.w3) && leafWin n r && (decide (r.kind = 1) || mapOk n r))

theorem leafOf_rows (n : NodeW 2 3) (r : LeafRec) (hf : r.facts n) : (leafOf n r hf).rows = setRow n.rows 2 r.y := rfl

theorem leaf_gm (n : NodeW 2 3) (r : LeafRec) (hf : r.facts n) :
    Gm (leafOf n r hf).rows 1 = leafG1 n ∧ Gm (leafOf n r hf).rows 2 = leafG2 n ∧
    Gm (leafOf n r hf).rows 3 = leafG3 n r.y := by
  have e0 : hN (setRow n.rows 2 r.y) 0 = hN n.rows 0 := hN_setRow_lt n.rows 2 r.y 0 (by norm_num)
  have e1 : hN (setRow n.rows 2 r.y) 1 = hN n.rows 1 := hN_setRow_lt n.rows 2 r.y 1 (by norm_num)
  have e2 : hN (setRow n.rows 2 r.y) 2 = r.y := hN_setRow_eq n.rows 2 r.y (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [leafOf_rows, Gm_one, e0]; rfl
  · rw [leafOf_rows, Gm_two', e0, e1]; rfl
  · rw [leafOf_rows, gram3_eq, e0, e1, e2]; rfl

theorem leaf_sound (C : Certificate) (n : NodeW 2 3) (r : LeafRec) (h : leafOk n r = true)
    (hT4 : r.kind ≠ 0 → r.kind ≠ 1 → ∃ cl ∈ C.t4, (∀ i : Fin 4, i.val < 3 → padL3 cl.l i = rowsL r.cl i) ∧
      ∃ rg ∈ cl.ranges, rg.1 ≤ r.rlo ∧ r.rhi ≤ rg.2) :
    ∃ (hf : r.facts n), LeafRelW C (leafOf n r hf) := by
  unfold leafOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hf, hrest⟩ := h
  refine ⟨hf, ?_⟩
  have hw := hf.2.2.2.2.1
  have hc3 : (leafOf n r hf).wit 3 = (r.x3, r.w3) := by simp [leafOf]
  by_cases hk0 : r.kind = 0
  · rw [if_pos hk0] at hrest
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
    obtain ⟨hcrit, hok⟩ := hrest
    have hceq : cOf ((leafOf n r hf).wit 3) = 1 / 5 := by rw [hc3]; exact cOf_eq_fifth hw hcrit
    refine ⟨fun _ => ?_, fun hne => absurd hceq hne⟩
    unfold critOk at hok
    split at hok
    · rename_i hg
      exact ⟨r.ck, gSP r.gp hg, matL r.u, matL r.u', of_decide_eq_true hok⟩
    · exact absurd hok (by simp)
  · rw [if_neg hk0] at hrest
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hrest
    obtain ⟨⟨hlt, hwin⟩, hmap⟩ := hrest
    have hgt : (1 : ℚ) / 5 < cOf ((leafOf n r hf).wit 3) := by rw [hc3]; exact cOf_gt hw hlt
    obtain ⟨g1, g2, g3⟩ := leaf_gm n r hf
    unfold leafWin at hwin
    have hbox : ∀ m, LeafWinMemW (leafOf n r hf) m → r.rlo ≤ m ∧ m ≤ (if r.kind = 1 then r.rlo - 1 else r.rhi) :=
      fun m hm => winOk_sound (leafOf n r hf) (leafG1 n) (leafG2 n) (leafG3 n r.y) _ _ _ _ _ _ r.rlo
        (if r.kind = 1 then r.rlo - 1 else r.rhi) g1 g2 g3
        (by have := (leafOf n r hf).w0; rw [this]; simp [cOf, wMin])
        rfl rfl (by rw [hc3]; rfl) hwin m hm
    refine ⟨fun hc => absurd hc (ne_of_gt hgt), fun _ hex => ?_⟩
    by_cases hk1 : r.kind = 1
    · obtain ⟨m, hm⟩ := hex
      have := hbox m hm
      rw [if_pos hk1] at this
      omega
    · rcases hmap with h1 | hm2
      · exact absurd h1 hk1
      · obtain ⟨cl, hcl, hrows, rg, hrg, hlo, hhi⟩ := hT4 hk0 hk1
        refine ⟨cl, hcl, ?_, rg, hrg, fun m hm => ?_⟩
        · unfold mapOk at hm2
          split at hm2
          · rename_i hg
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hm2
            obtain ⟨hv, hk⟩ := hm2
            have hk' := leqOkN_congr_b (b' := padL3 cl.l) (d := 3)
              (hN_eq_of_rows (by norm_num : 3 ≤ 4) (rowsL r.cl) (padL3 cl.l) (fun i hi => (hrows i hi).symm)) hk
            obtain ⟨V, V', hl⟩ := leaf3Rel_of_mred (pairReach_applySteps (by norm_num) (setRow n.rows 2 r.y) r.steps hv) hk'
            exact ⟨gSP r.gp hg, V, V', hl⟩
          · exact absurd hm2 (by simp)
        · have := hbox m hm
          rw [if_neg hk1] at this
          exact ⟨le_trans hlo this.1, le_trans this.2 hhi⟩

/-- **The `StreamHyp'.t3` clause of one depth-2 node** from the chunked list and the leaf records. -/
theorem t3_leaves (C : Certificate) (n : NodeW 2 3) (bn bd : ℤ) (hbd : 0 < bd)
    (hrad : radFrac (Cq (2 + 1)) n.wit n.rows 2 n.rk = (bn : ℚ) / bd) (cks : List Chunk)
    (hcov : coverOk (FC3.ofNode n bn bd) cks = true) (hall : AllOk (FC3.ofNode n bn bd) cks)
    (recs : List LeafRec) (halign : storedOf cks = recs.map LeafRec.t)
    (hrecs : ∀ r ∈ recs, leafOk n r = true)
    (hT4 : ∀ r ∈ recs, r.kind ≠ 0 → r.kind ≠ 1 → ∃ cl ∈ C.t4, (∀ i : Fin 4, i.val < 3 → padL3 cl.l i = rowsL r.cl i) ∧
      ∃ rg ∈ cl.ranges, rg.1 ≤ r.rlo ∧ r.rhi ≤ rg.2)
    (y : V5) (hp : ChildPass n y) :
    ∃ (y' : V5) (n3 : LeafW), (∀ i, dot (n.b i) y' = dot (n.b i) y) ∧ n3.rows = setRow n.rows 2 y' ∧ LeafRelW C n3 := by
  obtain ⟨e, he, hee⟩ := child_list_complete3k n bn bd hbd hrad cks hcov hall y hp
  rw [halign, List.mem_map] at he
  obtain ⟨r, hr, rfl⟩ := he
  obtain ⟨hf, hrel⟩ := leaf_sound C n r (hrecs r hr) (hT4 r hr)
  have h0 := congrArg Prod.fst hee
  have h1 := congrArg (fun p => p.2.1) hee
  have h2 := congrArg (fun p => p.2.2) hee
  refine ⟨r.y, leafOf n r hf, fun i => ?_, leafOf_rows n r hf, hrel⟩
  fin_cases i
  · exact hf.1.1.trans h0
  · exact hf.1.2.1.trans h1
  · exact hf.1.2.2.trans h2

end L5S4
end LRSpectrumFull
