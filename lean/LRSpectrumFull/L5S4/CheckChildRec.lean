/-
# L5S4.CheckChildRec : child records of a depth-1 node, their node data, and `StreamHyp'.t2` for the node

Case-tree certificate, part 6.  A child record is a flat list of 64 integers
`t(4) y(5) b'(15) r'(15) x(5) w rep p(5) e(5) u(4) u'(4)` (`l5s4f_gen`).  `RecFacts n r` are the integer facts of a
depth-2 node: `b·y = t`, `gcd t = 1`, `b'·(h, y) = 0`, `b'·r' = I`, and the witness `x/w` of `M(L_2)`
(`w | h·x`, `w | y·x`, `c_2 > 1/5`); `nodeOf2` is the resulting `NodeW 2 3` (the `s` functionals come from `child_nodeId`).
`recOkB` adds the class map of the record to the stored representative (`d2Ok`).

`t2_node` : for the depth-1 node `nK4` (the 5th stored node of `D1Data`, `h = (0,0,0,2,3)`) every `y` with
`ChildPass nK4 y` has a stored record, hence a node `n2` with the same coordinates and a class map to a stored
representative node; the two kernel checks are `ck4_box` (list completeness, `CheckChildFilt.boxOk`) and `ck4_recs`
(record facts and class maps).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.CheckChildFilt
import LRSpectrumFull.L5S4.CheckChain
import LRSpectrumFull.L5S4.CheckT1
import LRSpectrumFull.L5S4.ChildDataK4

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## 1. Record decoding -/

def cv (r : List ℤ) (o : ℕ) : V5 := fun i => r.getD (o + i.val) 0
def cY (r : List ℤ) : V5 := cv r 4
def cB (r : List ℤ) : Fin 3 → V5 := fun k => cv r (9 + 5 * k.val)
def cR (r : List ℤ) : Fin 3 → V5 := fun k => cv r (24 + 5 * k.val)
def cX (r : List ℤ) : V5 := cv r 39
def cW (r : List ℤ) : ℤ := r.getD 44 0
def cRep (r : List ℤ) : ℕ := (r.getD 45 0).toNat

/-- The integer facts of a depth-2 child record. -/
def RecFacts (n : NodeW 1 4) (r : List ℤ) : Prop :=
  (∀ i : Fin 4, dot (n.b i) (cY r) = recT r i) ∧ GcdOne (recT r) ∧
  (∀ i : Fin 3, dot (cB r i) (hN n.rows 0) = 0 ∧ dot (cB r i) (cY r) = 0) ∧
  (∀ i k : Fin 3, dot (cB r i) (cR r k) = if i = k then 1 else 0) ∧
  (0 < cW r ∧ cW r ∣ dot (hN n.rows 0) (cX r) ∧ cW r ∣ dot (cY r) (cX r) ∧ cW r < 5 * wMin (cX r) (cW r))

instance (n : NodeW 1 4) (r : List ℤ) : Decidable (RecFacts n r) := by unfold RecFacts; infer_instance

/-! ## 2. The node of a record -/

theorem tvec_cY (n : NodeW 1 4) (r : List ℤ) (h : RecFacts n r) : tvec n.b (cY r) = recT r := funext h.1

theorem rec_nodeId (n : NodeW 1 4) (r : List ℤ) (h : RecFacts n r) :
    ∃ s' : Fin 2 → V5, NodeId (fun i : Fin 2 => hN (setRow n.rows 1 (cY r)) i.val) (cB r) s' (cR r) := by
  have hg : GcdOne (tvec n.b (cY r)) := by rw [tvec_cY n r h]; exact h.2.1
  have hbl : ∀ i k, dot (cB r i) (Fin.snoc (α := fun _ => V5) (fun i : Fin 1 => hN n.rows i.val) (cY r) k) = 0 := by
    intro i k
    fin_cases k
    · simpa [Fin.snoc] using (h.2.2.1 i).1
    · simpa [Fin.snoc] using (h.2.2.1 i).2
  obtain ⟨s', hs'⟩ := child_nodeId n.id (cY r) hg (cB r) (cR r) hbl h.2.2.2.1
  refine ⟨s', ?_⟩
  have e := snoc_rows n (cY r)
  unfold rowsR at e
  rw [e]; exact hs'

theorem hN_setRow_zero (n : NodeW 1 4) (y : V5) : hN (setRow n.rows 1 y) 0 = hN n.rows 0 := by
  simp [hN, setRow]

theorem cOf_gt {x : V5} {w : ℤ} (hw : 0 < w) (h : w < 5 * wMin x w) : (1 : ℚ) / 5 < cOf (x, w) := by
  unfold cOf
  have hwq : (0 : ℚ) < (w : ℚ) := by exact_mod_cast hw
  have hmq : (w : ℚ) < 5 * (wMin x w : ℚ) := by exact_mod_cast h
  show (1 : ℚ) / 5 < ((wMin x w : ℤ) : ℚ) / ((w : ℤ) : ℚ)
  rw [lt_div_iff₀ hwq]
  linarith

noncomputable def nodeOf2 (n : NodeW 1 4) (r : List ℤ) (h : RecFacts n r) : NodeW 2 3 where
  rows := setRow n.rows 1 (cY r)
  b := cB r
  s := Classical.choose (rec_nodeId n r h)
  r := cR r
  id := Classical.choose_spec (rec_nodeId n r h)
  wit := fun k => if k ≤ 1 then n.wit k else (cX r, cW r)
  w0 := by simpa using n.w0
  wok := by
    intro k hk
    by_cases hk1 : k ≤ 1
    · simp only [hk1, if_true]
      refine ⟨(n.wok k hk1).1, fun i hi => ?_⟩
      have hi0 : i.val < 1 := by omega
      have e : setRow n.rows 1 (cY r) i = n.rows i := by
        simp [setRow]; intro h1; omega
      rw [e]; exact (n.wok k hk1).2 i hi
    · have hk2 : k = 2 := by omega
      subst hk2
      simp only [show ¬ (2 ≤ 1) by norm_num, if_false]
      refine ⟨h.2.2.2.2.1, fun i hi => ?_⟩
      have hi2 : i.val = 0 ∨ i.val = 1 := by omega
      rcases hi2 with h0 | h1
      · have e : setRow n.rows 1 (cY r) i = hN n.rows 0 := by
          have : i = ⟨0, by norm_num⟩ := Fin.ext h0
          subst this; simp [setRow, hN]
        rw [e]; exact h.2.2.2.2.2.1
      · have e : setRow n.rows 1 (cY r) i = cY r := by simp [setRow, h1]
        rw [e]; exact h.2.2.2.2.2.2.1
  wge := by
    intro k hk
    by_cases hk1 : k ≤ 1
    · simp only [hk1, if_true]; exact n.wge k hk1
    · simp only [hk1, if_false]; exact (cOf_gt h.2.2.2.2.1 h.2.2.2.2.2.2.2).le
  rk := ⟨2, by
    have hc := cOf_gt h.2.2.2.2.1 h.2.2.2.2.2.2.2
    simp only [radSet, Finset.mem_filter, Finset.mem_range, SArr, show ¬ (2 ≤ 1) by norm_num, if_false]
    refine ⟨by norm_num, ?_⟩
    have : ∑ i ∈ range 2, (if 2 ≤ i then (Gm (setRow n.rows 1 (cY r)) i : ℚ) / (Gm (setRow n.rows 1 (cY r)) (i + 1) : ℚ) else 0) = 0 := by
      simp [Finset.sum_range_succ]
    rw [this]
    have hp : 0 < cOf (cX r, cW r) - 1 / 5 := by linarith
    nlinarith⟩

theorem nodeOf2_rows (n : NodeW 1 4) (r : List ℤ) (h : RecFacts n r) : (nodeOf2 n r h).rows = setRow n.rows 1 (cY r) := rfl

/-! ## 3. Class maps of the records -/

abbrev GRaw := (Fin 5 → Fin 5) × (Fin 5 → ℤ)

def gpOf (r : List ℤ) : GRaw :=
  (fun i => ⟨(r.getD (46 + i.val) 0).toNat % 5, Nat.mod_lt _ (by norm_num)⟩, fun i => r.getD (51 + i.val) 0)

def mat2 (r : List ℤ) (o : ℕ) : List (List ℤ) := [[r.getD o 0, r.getD (o + 1) 0], [r.getD (o + 2) 0, r.getD (o + 3) 0]]

def classRaw (h : V5) (L : List (List ℤ)) (r : List ℤ) : D2Rec :=
  ⟨[h, cY r], [h, cY (L.getD (cRep r) [])], gpOf r, mat2 r 56, mat2 r 60⟩

noncomputable def recOkB (n : NodeW 1 4) (L : List (List ℤ)) (r : List ℤ) : Bool :=
  decide (RecFacts n r) && decide (cRep r < L.length) && d2Ok (classRaw (hN n.rows 0) L r)

theorem rowsL_pair (h y : V5) (i : Fin 4) (hi : i.val < 2) :
    rowsL [h, y] i = if i.val = 0 then h else y := by
  have : i.val = 0 ∨ i.val = 1 := by omega
  rcases this with h0 | h1
  · simp [rowsL, h0]
  · simp [rowsL, h1]

theorem setRow_pair (n : NodeW 1 4) (y : V5) (i : Fin 4) (hi : i.val < 2) :
    setRow n.rows 1 y i = rowsL [hN n.rows 0, y] i := by
  rw [rowsL_pair _ _ i hi]
  have : i.val = 0 ∨ i.val = 1 := by omega
  rcases this with h0 | h1
  · have : i = ⟨0, by norm_num⟩ := Fin.ext h0
    subst this; simp [setRow, hN]
  · simp [setRow, h1]

/-- A checked record: facts, a stored representative index, and the class map. -/
theorem recOk_sound (n : NodeW 1 4) (L : List (List ℤ)) (r : List ℤ) (h : recOkB n L r = true) :
    RecFacts n r ∧ cRep r < L.length ∧
      ∃ (g : SP) (U U' : ℕ → ℕ → ℤ),
        Chain2Rel g (setRow n.rows 1 (cY r)) (setRow n.rows 1 (cY (L.getD (cRep r) []))) U U' := by
  unfold recOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hf, hl⟩, hd⟩ := h
  exact ⟨hf, hl, d2_chain2_of_ok (classRaw (hN n.rows 0) L r) hd _ _
    (fun i hi => setRow_pair n _ i hi) (fun i hi => setRow_pair n _ i hi)⟩

/-! ## 4. Radius of the node -/

theorem radFrac_eq_of {C : ℚ} {wit : ℕ → V5 × ℤ} {rw : Fin 4 → V5} {j : ℕ} (hK : (radSet wit rw j).Nonempty) (q : ℚ)
    (h1 : ∃ k ∈ radSet wit rw j, C / (4 * (cOf (wit k) - 1 / 5) ^ 2 - SArr rw j k) = q)
    (h2 : ∀ k ∈ radSet wit rw j, q ≤ C / (4 * (cOf (wit k) - 1 / 5) ^ 2 - SArr rw j k)) :
    radFrac C wit rw j hK = q := by
  unfold radFrac
  apply le_antisymm
  · obtain ⟨k, hk, e⟩ := h1
    rw [← e]; exact Finset.inf'_le _ hk
  · exact Finset.le_inf' _ _ h2

theorem Gm_zero (rw : Fin 4 → V5) : Gm rw 0 = 1 := by simp [Gm, gF, rowsR]

theorem Gm_one (rw : Fin 4 → V5) : Gm rw 1 = dot (hN rw 0) (hN rw 0) := by
  unfold Gm gF; rw [Matrix.det_unique]; simp [rowsR]

/-! ## 5. The depth-1 node #4 and `t2` for it -/

def r4 : D1Raw := d1Data.getD 4 badB.default_d1

theorem r4_ok : r4.ok := by decide +kernel
theorem r4_h : r4.h = ![0, 0, 0, 2, 3] := by decide +kernel
theorem r4_w : r4.w = 5 := by decide +kernel
theorem r4_wmin : wMin r4.x r4.w = 2 := by decide +kernel
theorem r4_G : dot r4.h r4.h = 13 := by decide +kernel

noncomputable def nK : NodeW 1 4 := nodeOfRaw r4 r4_ok

theorem hrad_nK : radFrac (Cq (1 + 1)) nK.wit nK.rows 1 nK.rk = (ck4Bn : ℚ) / ck4Bd := by
  have hw0 : cOf (nK.wit 0) = 1 / 2 := by simp [nK, nodeOfRaw, d1Wit, cOf, wMin]
  have hw1 : cOf (nK.wit 1) = 2 / 5 := by
    simp only [nK, nodeOfRaw, d1Wit, show (1 : ℕ) ≠ 0 by norm_num, if_false, cOf]
    rw [r4_wmin, r4_w]; norm_num
  have hS0 : SArr nK.rows 1 0 = 1 / 13 := by
    have : hN nK.rows 0 = r4.h := nodeOfRaw_row0 r4 r4_ok
    simp [SArr, Gm_zero, Gm_one, this, r4_G]
  have hS1 : SArr nK.rows 1 1 = 0 := by simp [SArr]
  have hC : Cq (1 + 1) = 37 / 9 := by norm_num [Cq, Finset.sum_range_succ]
  have hq : (ck4Bn : ℚ) / ck4Bd = 12025 / 828 := by norm_num [ck4Bn, ck4Bd]
  rw [hq, hC]
  apply radFrac_eq_of
  · refine ⟨0, ?_, ?_⟩
    · simp only [radSet, Finset.mem_filter, Finset.mem_range, hw0, hS0]
      norm_num
    · rw [hw0, hS0]; norm_num
  · intro k hk
    simp only [radSet, Finset.mem_filter, Finset.mem_range] at hk
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · rw [hw0, hS0]; norm_num
    · rw [hw1, hS1]; norm_num

def flatL : List (List ℤ) := ck4Groups.flatMap Prod.snd

/-- The stored representative nodes. -/
def R2K : Set (NodeW 2 3) := {m | ∃ r ∈ flatL, ∃ h : RecFacts nK r, m = nodeOf2 nK r h}

noncomputable def ckC : Ctx := ctxOf nK ck4Bn ck4Bd

theorem ck4_keys : ck4Groups.map Prod.fst = rngI (tmaxOf ckC 0) := by decide +kernel

/-- Kernel checks 1: the slices `(t0, t1)` of the box (box points passing the filters are stored). -/
theorem ck4_slice_0_0 : sliceOk ckC (ck4Groups.getD 0 (0, [])) (-3) = true := by decide +kernel
theorem ck4_slice_0_1 : sliceOk ckC (ck4Groups.getD 0 (0, [])) (-2) = true := by decide +kernel
theorem ck4_slice_0_2 : sliceOk ckC (ck4Groups.getD 0 (0, [])) (-1) = true := by decide +kernel
theorem ck4_slice_0_3 : sliceOk ckC (ck4Groups.getD 0 (0, [])) (0) = true := by decide +kernel
theorem ck4_slice_0_4 : sliceOk ckC (ck4Groups.getD 0 (0, [])) (1) = true := by decide +kernel
theorem ck4_slice_0_5 : sliceOk ckC (ck4Groups.getD 0 (0, [])) (2) = true := by decide +kernel
theorem ck4_slice_0_6 : sliceOk ckC (ck4Groups.getD 0 (0, [])) (3) = true := by decide +kernel
theorem ck4_slice_1_0 : sliceOk ckC (ck4Groups.getD 1 (0, [])) (-3) = true := by decide +kernel
theorem ck4_slice_1_1 : sliceOk ckC (ck4Groups.getD 1 (0, [])) (-2) = true := by decide +kernel
theorem ck4_slice_1_2 : sliceOk ckC (ck4Groups.getD 1 (0, [])) (-1) = true := by decide +kernel
theorem ck4_slice_1_3 : sliceOk ckC (ck4Groups.getD 1 (0, [])) (0) = true := by decide +kernel
theorem ck4_slice_1_4 : sliceOk ckC (ck4Groups.getD 1 (0, [])) (1) = true := by decide +kernel
theorem ck4_slice_1_5 : sliceOk ckC (ck4Groups.getD 1 (0, [])) (2) = true := by decide +kernel
theorem ck4_slice_1_6 : sliceOk ckC (ck4Groups.getD 1 (0, [])) (3) = true := by decide +kernel
theorem ck4_slice_2_0 : sliceOk ckC (ck4Groups.getD 2 (0, [])) (-3) = true := by decide +kernel
theorem ck4_slice_2_1 : sliceOk ckC (ck4Groups.getD 2 (0, [])) (-2) = true := by decide +kernel
theorem ck4_slice_2_2 : sliceOk ckC (ck4Groups.getD 2 (0, [])) (-1) = true := by decide +kernel
theorem ck4_slice_2_3 : sliceOk ckC (ck4Groups.getD 2 (0, [])) (0) = true := by decide +kernel
theorem ck4_slice_2_4 : sliceOk ckC (ck4Groups.getD 2 (0, [])) (1) = true := by decide +kernel
theorem ck4_slice_2_5 : sliceOk ckC (ck4Groups.getD 2 (0, [])) (2) = true := by decide +kernel
theorem ck4_slice_2_6 : sliceOk ckC (ck4Groups.getD 2 (0, [])) (3) = true := by decide +kernel
theorem ck4_slice_3_0 : sliceOk ckC (ck4Groups.getD 3 (0, [])) (-3) = true := by decide +kernel
theorem ck4_slice_3_1 : sliceOk ckC (ck4Groups.getD 3 (0, [])) (-2) = true := by decide +kernel
theorem ck4_slice_3_2 : sliceOk ckC (ck4Groups.getD 3 (0, [])) (-1) = true := by decide +kernel
theorem ck4_slice_3_3 : sliceOk ckC (ck4Groups.getD 3 (0, [])) (0) = true := by decide +kernel
theorem ck4_slice_3_4 : sliceOk ckC (ck4Groups.getD 3 (0, [])) (1) = true := by decide +kernel
theorem ck4_slice_3_5 : sliceOk ckC (ck4Groups.getD 3 (0, [])) (2) = true := by decide +kernel
theorem ck4_slice_3_6 : sliceOk ckC (ck4Groups.getD 3 (0, [])) (3) = true := by decide +kernel
theorem ck4_slice_4_0 : sliceOk ckC (ck4Groups.getD 4 (0, [])) (-3) = true := by decide +kernel
theorem ck4_slice_4_1 : sliceOk ckC (ck4Groups.getD 4 (0, [])) (-2) = true := by decide +kernel
theorem ck4_slice_4_2 : sliceOk ckC (ck4Groups.getD 4 (0, [])) (-1) = true := by decide +kernel
theorem ck4_slice_4_3 : sliceOk ckC (ck4Groups.getD 4 (0, [])) (0) = true := by decide +kernel
theorem ck4_slice_4_4 : sliceOk ckC (ck4Groups.getD 4 (0, [])) (1) = true := by decide +kernel
theorem ck4_slice_4_5 : sliceOk ckC (ck4Groups.getD 4 (0, [])) (2) = true := by decide +kernel
theorem ck4_slice_4_6 : sliceOk ckC (ck4Groups.getD 4 (0, [])) (3) = true := by decide +kernel
theorem ck4_slice_5_0 : sliceOk ckC (ck4Groups.getD 5 (0, [])) (-3) = true := by decide +kernel
theorem ck4_slice_5_1 : sliceOk ckC (ck4Groups.getD 5 (0, [])) (-2) = true := by decide +kernel
theorem ck4_slice_5_2 : sliceOk ckC (ck4Groups.getD 5 (0, [])) (-1) = true := by decide +kernel
theorem ck4_slice_5_3 : sliceOk ckC (ck4Groups.getD 5 (0, [])) (0) = true := by decide +kernel
theorem ck4_slice_5_4 : sliceOk ckC (ck4Groups.getD 5 (0, [])) (1) = true := by decide +kernel
theorem ck4_slice_5_5 : sliceOk ckC (ck4Groups.getD 5 (0, [])) (2) = true := by decide +kernel
theorem ck4_slice_5_6 : sliceOk ckC (ck4Groups.getD 5 (0, [])) (3) = true := by decide +kernel
theorem ck4_slice_6_0 : sliceOk ckC (ck4Groups.getD 6 (0, [])) (-3) = true := by decide +kernel
theorem ck4_slice_6_1 : sliceOk ckC (ck4Groups.getD 6 (0, [])) (-2) = true := by decide +kernel
theorem ck4_slice_6_2 : sliceOk ckC (ck4Groups.getD 6 (0, [])) (-1) = true := by decide +kernel
theorem ck4_slice_6_3 : sliceOk ckC (ck4Groups.getD 6 (0, [])) (0) = true := by decide +kernel
theorem ck4_slice_6_4 : sliceOk ckC (ck4Groups.getD 6 (0, [])) (1) = true := by decide +kernel
theorem ck4_slice_6_5 : sliceOk ckC (ck4Groups.getD 6 (0, [])) (2) = true := by decide +kernel
theorem ck4_slice_6_6 : sliceOk ckC (ck4Groups.getD 6 (0, [])) (3) = true := by decide +kernel

theorem ck4_slices : ∀ g ∈ ck4Groups, ∀ t1 ∈ rngI (tmaxOf ckC 1), sliceOk ckC g t1 = true := by
  intro g hg t1 ht1
  have hT : tmaxOf ckC 1 = 3 := by decide +kernel
  rw [hT] at ht1
  have hr : rngI 3 = [-3, -2, -1, 0, 1, 2, 3] := by decide +kernel
  rw [hr] at ht1
  have hl : ck4Groups.length = 7 := by decide +kernel
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
  have hi7 : i < 7 := by omega
  have e : g = ck4Groups.getD i (0, []) := by
    rw [← hgi]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [e]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht1
  interval_cases i <;> rcases ht1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ck4_slice_0_0
  · exact ck4_slice_0_1
  · exact ck4_slice_0_2
  · exact ck4_slice_0_3
  · exact ck4_slice_0_4
  · exact ck4_slice_0_5
  · exact ck4_slice_0_6
  · exact ck4_slice_1_0
  · exact ck4_slice_1_1
  · exact ck4_slice_1_2
  · exact ck4_slice_1_3
  · exact ck4_slice_1_4
  · exact ck4_slice_1_5
  · exact ck4_slice_1_6
  · exact ck4_slice_2_0
  · exact ck4_slice_2_1
  · exact ck4_slice_2_2
  · exact ck4_slice_2_3
  · exact ck4_slice_2_4
  · exact ck4_slice_2_5
  · exact ck4_slice_2_6
  · exact ck4_slice_3_0
  · exact ck4_slice_3_1
  · exact ck4_slice_3_2
  · exact ck4_slice_3_3
  · exact ck4_slice_3_4
  · exact ck4_slice_3_5
  · exact ck4_slice_3_6
  · exact ck4_slice_4_0
  · exact ck4_slice_4_1
  · exact ck4_slice_4_2
  · exact ck4_slice_4_3
  · exact ck4_slice_4_4
  · exact ck4_slice_4_5
  · exact ck4_slice_4_6
  · exact ck4_slice_5_0
  · exact ck4_slice_5_1
  · exact ck4_slice_5_2
  · exact ck4_slice_5_3
  · exact ck4_slice_5_4
  · exact ck4_slice_5_5
  · exact ck4_slice_5_6
  · exact ck4_slice_6_0
  · exact ck4_slice_6_1
  · exact ck4_slice_6_2
  · exact ck4_slice_6_3
  · exact ck4_slice_6_4
  · exact ck4_slice_6_5
  · exact ck4_slice_6_6

/-- Kernel checks 2: every stored record has its node facts and its class map (per group). -/
theorem ck4_recs_0 : (ck4Groups.getD 0 (0, [])).2.all (recOkB nK flatL) = true := by decide +kernel
theorem ck4_recs_1 : (ck4Groups.getD 1 (0, [])).2.all (recOkB nK flatL) = true := by decide +kernel
theorem ck4_recs_2 : (ck4Groups.getD 2 (0, [])).2.all (recOkB nK flatL) = true := by decide +kernel
theorem ck4_recs_3 : (ck4Groups.getD 3 (0, [])).2.all (recOkB nK flatL) = true := by decide +kernel
theorem ck4_recs_4 : (ck4Groups.getD 4 (0, [])).2.all (recOkB nK flatL) = true := by decide +kernel
theorem ck4_recs_5 : (ck4Groups.getD 5 (0, [])).2.all (recOkB nK flatL) = true := by decide +kernel
theorem ck4_recs_6 : (ck4Groups.getD 6 (0, [])).2.all (recOkB nK flatL) = true := by decide +kernel

theorem ck4_all : ∀ r ∈ flatL, recOkB nK flatL r = true := by
  intro r hr
  obtain ⟨g, hg, hrg⟩ := List.mem_flatMap.1 hr
  have hl : ck4Groups.length = 7 := by decide +kernel
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
  have hi7 : i < 7 := by omega
  have e : g = ck4Groups.getD i (0, []) := by
    rw [← hgi]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [e] at hrg
  interval_cases i
  exacts [List.all_eq_true.1 ck4_recs_0 r hrg, List.all_eq_true.1 ck4_recs_1 r hrg, List.all_eq_true.1 ck4_recs_2 r hrg, List.all_eq_true.1 ck4_recs_3 r hrg, List.all_eq_true.1 ck4_recs_4 r hrg, List.all_eq_true.1 ck4_recs_5 r hrg, List.all_eq_true.1 ck4_recs_6 r hrg]

/-- **`StreamHyp'.t2` for the depth-1 node `nK`** (`h = (0,0,0,2,3)`): every child row has a stored record, hence a depth-2
node with the same coordinates and a class map to a stored representative. -/
theorem t2_nK : ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n2 : NodeW 2 3),
    (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧ n2.rows = setRow nK.rows 1 y' ∧
    ∃ rep ∈ R2K, ∃ (g : SP) (U U' : ℕ → ℕ → ℤ), Chain2Rel g n2.rows rep.rows U U' := by
  intro y hy
  have hbd : (0 : ℤ) < ck4Bd := by decide
  obtain ⟨g, hg, r, hr, hrt⟩ := child_list_complete nK ck4Bn ck4Bd hbd hrad_nK ck4Groups ck4_keys ck4_slices y hy
  have hrL : r ∈ flatL := List.mem_flatMap.2 ⟨g, hg, hr⟩
  obtain ⟨hf, hlen, g', U, U', hch⟩ := recOk_sound nK flatL r (ck4_all r hrL)
  have hrp : flatL.getD (cRep r) [] ∈ flatL := by
    have : flatL.getD (cRep r) [] = flatL[cRep r] := by simp [List.getD_eq_getElem?_getD, hlen]
    rw [this]; exact List.getElem_mem hlen
  obtain ⟨hfp, -, -⟩ := recOk_sound nK flatL _ (ck4_all _ hrp)
  refine ⟨cY r, nodeOf2 nK r hf, fun i => ?_, rfl, nodeOf2 nK _ hfp, ⟨_, hrp, hfp, rfl⟩, g', U, U', hch⟩
  have h1 := hf.1 i
  have h2 := congrFun hrt i
  rw [h1]; simpa [tvec] using h2

end L5S4
end LRSpectrumFull
