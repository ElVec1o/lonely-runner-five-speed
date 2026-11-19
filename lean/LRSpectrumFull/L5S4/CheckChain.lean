/-
# L5S4.CheckChain : class-map, critical-leaf and mapped-leaf checkers, tested on real certificate chunks

Case-tree certificate, part 5.  Boolean checkers (decidable predicates evaluated by the kernel) for the
records of the depth-2 and depth-3 streams, each with a soundness theorem to the Lean relations of `Records`/`Induct2`:

* `d2Ok` : `Chain2Rel` for a depth-2 class-map record (first row up to sign, `LeqOkN 2`); `d2Ok_sound`, `d2_chain2_of_ok`
  (the clause of `StreamHyp'.t2` that provides the representative and the map).
* `d3CritOk` : a critical leaf: all node fields of `LeafW` (identities `b.l = 0`, `l.s = I`, `b.r = I`, three witnesses,
  divisibility, `c_k >= 1/5`) and `c_3 = 1/5` exactly, plus the identification `LeqOkN 2` with the critical lattice;
  `d3CritOk_sound` builds the `LeafW`; `d3Crit_leafRel` : `LeafRelW C` holds for it for EVERY certificate `C` (no class, no radius set).
* `d3MapOk` : a mapped leaf: `mred` as a list of pair-reduction steps, the class map on the reduced rows;
  `d3MapOk_sound` : `Leaf3Rel g rows cl` on the node rows (uses `Mred.leaf3Rel_of_mred`).

Real data: `D2Data` (100 depth-2 records), `D3Data` (the 8 critical leaves and 100 mapped leaves).  Controls: planted
corruptions are rejected by the kernel.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.D2Data
import LRSpectrumFull.L5S4.D3Data
import LRSpectrumFull.L5S4.Mred
import LRSpectrumFull.L5S4.Induct2

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## 1. Raw data to Lean objects -/

abbrev GR := (Fin 5 → Fin 5) × (Fin 5 → ℤ)

def gOk (g : GR) : Prop := Function.Injective g.1 ∧ ∀ i, g.2 i = 1 ∨ g.2 i = -1

instance (g : GR) : Decidable (gOk g) := by unfold gOk; infer_instance

/-- The signed permutation `x ↦ (i ↦ ε_i x_{p_i})` (Rust `G::apply`). -/
noncomputable def gSP (g : GR) (h : gOk g) : SP := ⟨Equiv.ofBijective g.1 (Finite.injective_iff_bijective.1 h.1), g.2, h.2⟩

theorem gSP_act (g : GR) (h : gOk g) (x : V5) : (gSP g h).act x = fun i => g.2 i * x (g.1 i) := rfl

def rowsL (l : List V5) : Fin 4 → V5 := fun i => l.getD i.val (fun _ => 0)
def bL (l : List V5) : Fin 2 → V5 := fun i => l.getD i.val (fun _ => 0)
def sL (l : List V5) : Fin 3 → V5 := fun i => l.getD i.val (fun _ => 0)
def matL (m : List (List ℤ)) : ℕ → ℕ → ℤ := fun i k => (m.getD i []).getD k 0

instance (g : SP) (rows rep : Fin 4 → V5) : Decidable (Chain1Rel g rows rep) := by unfold Chain1Rel; infer_instance
instance (d : ℕ) (t b : Fin 4 → V5) (U U' : ℕ → ℕ → ℤ) : Decidable (LeqOkN d t b U U') := by
  unfold LeqOkN; infer_instance
instance (g : SP) (rows rep : Fin 4 → V5) (U U' : ℕ → ℕ → ℤ) : Decidable (Chain2Rel g rows rep U U') := by
  unfold Chain2Rel; infer_instance

/-! ## 2. Depth-2 class maps -/

noncomputable def d2Ok (r : D2Rec) : Bool :=
  if h : gOk r.gp then decide (Chain2Rel (gSP r.gp h) (rowsL r.n2) (rowsL r.rep) (matL r.u) (matL r.u')) else false

theorem d2Ok_sound (r : D2Rec) (h : d2Ok r = true) :
    ∃ g : SP, Chain2Rel g (rowsL r.n2) (rowsL r.rep) (matL r.u) (matL r.u') := by
  unfold d2Ok at h
  split at h
  · exact ⟨_, of_decide_eq_true h⟩
  · exact absurd h (by simp)

theorem leqOkN_congr_b {d : ℕ} {t b b' : Fin 4 → V5} {U U' : ℕ → ℕ → ℤ} (h : ∀ i < d, hN b i = hN b' i)
    (hl : LeqOkN d t b U U') : LeqOkN d t b' U U' := by
  refine ⟨fun i hi c => ?_, fun i hi c => ?_⟩
  · rw [hl.1 i hi c]
    exact Finset.sum_congr rfl (fun k hk => by rw [h k (Finset.mem_range.1 hk)])
  · rw [← h i hi]; exact hl.2 i hi c

theorem chain2Rel_congr_rep {g : SP} {r rep rep' : Fin 4 → V5} {U U' : ℕ → ℕ → ℤ}
    (h : ∀ i : Fin 4, i.val < 2 → rep i = rep' i) (hr : Chain2Rel g r rep U U') : Chain2Rel g r rep' U U' := by
  obtain ⟨h1, h2⟩ := hr
  have hh : ∀ i < 2, hN rep i = hN rep' i := fun i hi => hN_eq_of_rows (by norm_num) rep rep' h i hi
  refine ⟨?_, leqOkN_congr_b hh h2⟩
  unfold Chain1Rel at h1 ⊢
  rw [← hh 0 (by norm_num)]
  exact h1

/-- The clause of `StreamHyp'.t2`: a checked record gives the class map between ANY node with those first two rows and ANY
representative node with those first two rows. -/
theorem d2_chain2_of_ok (r : D2Rec) (h : d2Ok r = true) (n2 rep : Fin 4 → V5)
    (h2 : ∀ i : Fin 4, i.val < 2 → n2 i = rowsL r.n2 i) (hr : ∀ i : Fin 4, i.val < 2 → rep i = rowsL r.rep i) :
    ∃ (g : SP) (U U' : ℕ → ℕ → ℤ), Chain2Rel g n2 rep U U' := by
  obtain ⟨g, hg⟩ := d2Ok_sound r h
  exact ⟨g, _, _, chain2Rel_congr_rep (fun i hi => (hr i hi).symm)
    (chain2Rel_congr (fun i hi => (h2 i hi).symm) hg)⟩

theorem d2_chunk_ok : d2Data.all d2Ok = true := by decide +kernel

theorem d2_chunk_length : d2Data.length = 100 := by decide +kernel

/-! ## 3. Critical leaves: the full `LeafW` -/

theorem cOf_ge {x : V5} {w : ℤ} (hw : 0 < w) (h : w ≤ 5 * wMin x w) : (1 : ℚ) / 5 ≤ cOf (x, w) := by
  unfold cOf
  have hwq : (0 : ℚ) < (w : ℚ) := by exact_mod_cast hw
  have hmq : (w : ℚ) ≤ 5 * (wMin x w : ℚ) := by exact_mod_cast h
  show (1 : ℚ) / 5 ≤ ((wMin x w : ℤ) : ℚ) / ((w : ℤ) : ℚ)
  rw [le_div_iff₀ hwq]
  linarith

theorem cOf_eq_fifth {x : V5} {w : ℤ} (hw : 0 < w) (h : w = 5 * wMin x w) : cOf (x, w) = 1 / 5 := by
  unfold cOf
  have hwq : (0 : ℚ) < (w : ℚ) := by exact_mod_cast hw
  have hmq : (w : ℚ) = 5 * (wMin x w : ℚ) := by exact_mod_cast h
  show ((wMin x w : ℤ) : ℚ) / ((w : ℤ) : ℚ) = 1 / 5
  rw [div_eq_iff hwq.ne']
  linarith

def critWit (r : D3Crit) : ℕ → V5 × ℤ := fun k =>
  if k = 0 then ((fun _ => 1), 2) else if k = 1 then (r.x1, r.w1) else if k = 2 then (r.x2, r.w2) else (r.x3, r.w3)

/-- The node facts of a critical leaf record (all integer, decidable). -/
def D3Crit.facts (r : D3Crit) : Prop :=
  (∀ (i : Fin 2) (k : Fin 3), dot (bL r.b i) (hN (rowsL r.rows) k.val) = 0) ∧
  (∀ i k : Fin 3, dot (hN (rowsL r.rows) i.val) (sL r.s k) = if i = k then 1 else 0) ∧
  (∀ i k : Fin 2, dot (bL r.b i) (bL r.r k) = if i = k then 1 else 0) ∧
  (0 < r.w1 ∧ r.w1 ∣ dot (rowsL r.rows 0) r.x1 ∧ r.w1 ≤ 5 * wMin r.x1 r.w1) ∧
  (0 < r.w2 ∧ r.w2 ∣ dot (rowsL r.rows 0) r.x2 ∧ r.w2 ∣ dot (rowsL r.rows 1) r.x2 ∧ r.w2 ≤ 5 * wMin r.x2 r.w2) ∧
  (0 < r.w3 ∧ r.w3 ∣ dot (rowsL r.rows 0) r.x3 ∧ r.w3 ∣ dot (rowsL r.rows 1) r.x3 ∧ r.w3 ∣ dot (rowsL r.rows 2) r.x3 ∧
    r.w3 = 5 * wMin r.x3 r.w3)

instance (r : D3Crit) : Decidable r.facts := by unfold D3Crit.facts; infer_instance

/-- The leaf node of a checked critical record: a `LeafW`, i.e. a `NodeW 3 2` without the radius field. -/
def critLeaf (r : D3Crit) (hf : r.facts) : LeafW where
  rows := rowsL r.rows
  b := bL r.b
  s := sL r.s
  r := bL r.r
  id := ⟨hf.1, hf.2.1, hf.2.2.1⟩
  wit := critWit r
  w0 := by simp [critWit]
  wok := by
    obtain ⟨-, -, -, ⟨a1, a2, a3⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3, c4, c5⟩⟩ := hf
    intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl | rfl
    · exact ⟨by simp [critWit], fun i hi => by omega⟩
    · refine ⟨by simpa [critWit] using a1, fun i hi => ?_⟩
      have : i = 0 := Fin.ext (by omega)
      subst this; simpa [critWit] using a2
    · refine ⟨by simpa [critWit] using b1, fun i hi => ?_⟩
      have : i = 0 ∨ i = 1 := by
        rcases i with ⟨i, hi4⟩; simp only [Fin.mk.injEq, Fin.ext_iff] at *; omega
      rcases this with rfl | rfl
      · simpa [critWit] using b2
      · simpa [critWit] using b3
    · refine ⟨by simpa [critWit] using c1, fun i hi => ?_⟩
      have : i = 0 ∨ i = 1 ∨ i = 2 := by
        rcases i with ⟨i, hi4⟩; simp only [Fin.mk.injEq, Fin.ext_iff] at *; omega
      rcases this with rfl | rfl | rfl
      · simpa [critWit] using c2
      · simpa [critWit] using c3
      · simpa [critWit] using c4
  wge := by
    obtain ⟨-, -, -, ⟨a1, a2, a3⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3, c4, c5⟩⟩ := hf
    intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl | rfl
    · have : cOf (critWit r 0) = 1 / 2 := by simp [critWit, cOf, wMin]
      rw [this]; norm_num
    · simpa [critWit] using cOf_ge a1 a3
    · simpa [critWit] using cOf_ge b1 b4
    · simpa [critWit] using cOf_ge c1 c5.le

theorem critLeaf_c3 (r : D3Crit) (hf : r.facts) : cOf ((critLeaf r hf).wit 3) = 1 / 5 := by
  have := cOf_eq_fifth hf.2.2.2.2.2.1 hf.2.2.2.2.2.2.2.2.2
  simpa [critLeaf, critWit] using this

noncomputable def d3CritOk (r : D3Crit) : Bool :=
  if h : gOk r.gp then
    decide (r.facts ∧ LeqOkN 2 (fun i => (gSP r.gp h).act (padB2 (bL r.b) i)) (critBasis r.ck) (matL r.u) (matL r.u'))
  else false

/-- Soundness: a checked critical record gives a `LeafW` with `c_3 = 1/5` and the identification with the critical lattice. -/
theorem d3CritOk_sound (r : D3Crit) (h : d3CritOk r = true) :
    ∃ n3 : LeafW, n3.rows = rowsL r.rows ∧ cOf (n3.wit 3) = 1 / 5 ∧
      ∃ (g : SP) (U U' : ℕ → ℕ → ℤ), LeqOkN 2 (fun i => g.act (padB2 n3.b i)) (critBasis r.ck) U U' := by
  unfold d3CritOk at h
  split at h
  · have hh := of_decide_eq_true h
    exact ⟨critLeaf r hh.1, rfl, critLeaf_c3 r hh.1, _, _, _, hh.2⟩
  · exact absurd h (by simp)

/-- For every certificate `C`, a checked critical record is a leaf that satisfies `LeafRelW C` with no class and no radius set. -/
theorem d3Crit_leafRel (r : D3Crit) (h : d3CritOk r = true) (C : Certificate) :
    ∃ n3 : LeafW, n3.rows = rowsL r.rows ∧ cOf (n3.wit 3) = 1 / 5 ∧ LeafRelW C n3 := by
  obtain ⟨n3, h1, h2, g, U, U', hl⟩ := d3CritOk_sound r h
  exact ⟨n3, h1, h2, (leafRelW_crit C n3 h2).2 ⟨r.ck, g, U, U', hl⟩⟩

theorem d3_crit_ok : d3Crit.all d3CritOk = true := by decide +kernel

theorem d3_crit_length : d3Crit.length = 8 := by decide +kernel

/-! ## 4. Mapped leaves and the `mred` bridge on real data -/

noncomputable def d3MapOk (r : D3Map) : Bool :=
  if h : gOk r.gp then
    stepsValid 3 r.steps &&
    decide (LeqOkN 3 (fun i => (gSP r.gp h).act (applySteps r.steps (rowsL r.rows) i)) (rowsL r.cl) (matL r.u) (matL r.u'))
  else false

/-- Soundness: the class map checked on the pair-reduced rows is a class map on the node rows. -/
theorem d3MapOk_sound (r : D3Map) (h : d3MapOk r = true) :
    ∃ (g : SP) (V V' : ℕ → ℕ → ℤ), Leaf3Rel g (rowsL r.rows) (rowsL r.cl) V V' := by
  unfold d3MapOk at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hv, hk⟩ := h
    obtain ⟨V, V', hl⟩ := leaf3Rel_of_mred (pairReach_applySteps (by norm_num) (rowsL r.rows) r.steps hv) hk
    exact ⟨_, V, V', hl⟩
  · exact absurd h (by simp)

theorem d3_map_ok : d3Map.all d3MapOk = true := by decide +kernel

theorem d3_map_length : d3Map.length = 100 := by decide +kernel

/-! ## 5. Planted corruptions -/

def dummyD2 : D2Rec := { n2 := [], rep := [], gp := (id, fun _ => 1), u := [], u' := [] }
def dummyCrit : D3Crit := { rows := [], b := [], r := [], s := [], x1 := 0, w1 := 1, x2 := 0, w2 := 1, x3 := 0, w3 := 1, ck := 0, gp := (id, fun _ => 1), u := [], u' := [] }
def dummyMap : D3Map := { rows := [], steps := [], gp := (id, fun _ => 1), cl := [], u := [], u' := [] }

/-- First depth-2 record with `u_00` changed. -/
def badD2 : D2Rec := match d2Data with
  | r :: _ => { r with u := [[1000, 0], [0, 1]] }
  | [] => dummyD2

theorem ctl_badD2 : d2Ok badD2 = false := by decide +kernel

/-- First depth-2 record with the sign vector changed (`eps_0 := 2` is not a sign). -/
def badG : D2Rec := match d2Data with
  | r :: _ => { r with gp := (r.gp.1, fun i => if i = 0 then 2 else r.gp.2 i) }
  | [] => dummyD2

theorem ctl_badG : d2Ok badG = false := by decide +kernel

/-- First critical leaf with the third witness changed (`c_3 != 1/5`). -/
def badCrit : D3Crit := match d3Crit with
  | r :: _ => { r with w3 := 7 }
  | [] => dummyCrit

theorem ctl_badCrit : d3CritOk badCrit = false := by decide +kernel

/-- First critical leaf with `ck` swapped (identification with the wrong critical lattice). -/
def badCk : D3Crit := match d3Crit with
  | r :: _ => { r with ck := 1 }
  | [] => dummyCrit

theorem ctl_badCk : d3CritOk badCk = false := by decide +kernel

/-- Every real mapped record with a nonempty `mred` step list, with one step dropped, is rejected. -/
def dropStep (r : D3Map) : D3Map := { r with steps := r.steps.drop 1 }

theorem ctl_dropStep : (d3Map.filter (fun r => !r.steps.isEmpty)).all (fun r => !d3MapOk (dropStep r)) = true := by
  decide +kernel

theorem d3_map_with_steps : ((d3Map.filter (fun r => !r.steps.isEmpty)).length > 0) = true := by decide +kernel

end L5S4
end LRSpectrumFull
