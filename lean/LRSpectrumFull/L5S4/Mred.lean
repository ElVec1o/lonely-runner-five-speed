/-
# L5S4.Mred : the `mred` bridge (pair reduction is a unimodular lattice equality) and the class-map composite

Case-tree certificate, part 5.

The Rust leaf check applies `leq_ok` to `gmap(gn, gr, mred(l))`, where `mred` is `pair_reduce` of `lib.rs` (repeated
replacements `b_i := b_i - q b_j`, `i ≠ j`), and `gmap = gr^{-1} ∘ gn`; Lean's `Leaf3Rel g rows rep` is stated on the node
rows themselves with one signed permutation.  This module proves the bridge:

* `elemRow i j q A` : the elementary step `A_i := A_i - q A_j`; `leqOkN_elem` : it preserves the lattice (`LeqOkN` with
  explicit unimodular `U, U'`).
* `PairReach d A B` : `B` arises from `A` by finitely many elementary steps among the first `d` rows (this is what
  `pair_reduce` does, step by step); `leqOkN_of_pairReach` : then `LeqOkN d A B U U'` for some `U, U'`.
* `applySteps`, `stepsValid`, `pairReach_applySteps` : the checker form (a list of triples `(i, j, q)`, a Boolean validity
  test, soundness).
* `leaf3Rel_of_mred` : `LeqOkN 3 (g mred) rep` and `PairReach 3 rows mred` give `Leaf3Rel g rows rep`.
* `leaf3Rel_of_gmap` : the composite of Rust's `gmap` (`gr^{-1}` after `gn`) is a single signed permutation.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.NodeEx

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## 1. One elementary step -/

/-- `A_i := A_i - q A_j` (a step of `pair_reduce`), other rows unchanged. -/
def elemRow (i j : ℕ) (q : ℤ) (A : Fin 4 → V5) : Fin 4 → V5 :=
  fun k => if k.val = i then fun c => A k c - q * hN A j c else A k

theorem hN_elemRow (i j : ℕ) (q : ℤ) (A : Fin 4 → V5) (m : ℕ) (hm : m < 4) (c : Fin 5) :
    hN (elemRow i j q A) m c = if m = i then hN A m c - q * hN A j c else hN A m c := by
  simp only [hN, hm, dif_pos, elemRow]
  by_cases h : m = i <;> simp [h]

theorem leqOkN_refl (d : ℕ) (A : Fin 4 → V5) : LeqOkN d A A idN idN := by
  refine ⟨fun i hi c => ?_, fun i hi c => ?_⟩ <;>
  · simp only [idN]
    simp [Finset.sum_ite_eq, hi]

/-- The matrices of an elementary step. -/
def elemU (i j : ℕ) (q : ℤ) : ℕ → ℕ → ℤ := fun m k => idN m k - (if m = i ∧ k = j then q else 0)
def elemU' (i j : ℕ) (q : ℤ) : ℕ → ℕ → ℤ := fun m k => idN m k + (if m = i ∧ k = j then q else 0)

theorem leqOkN_elem {d : ℕ} (hd : d ≤ 4) {i j : ℕ} (hi : i < d) (hj : j < d) (hij : i ≠ j) (q : ℤ)
    (A : Fin 4 → V5) : LeqOkN d (elemRow i j q A) A (elemU i j q) (elemU' i j q) := by
  have hj4 : j < 4 := by omega
  refine ⟨fun m hm c => ?_, fun m hm c => ?_⟩
  · have hm4 : m < 4 := by omega
    rw [hN_elemRow i j q A m hm4 c]
    simp only [elemU, idN, sub_mul, Finset.sum_sub_distrib]
    have e1 : ∑ k ∈ range d, (if m = k then (1 : ℤ) else 0) * hN A k c = hN A m c := by
      simp [Finset.sum_ite_eq, hm]
    have e2 : ∑ k ∈ range d, (if m = i ∧ k = j then q else 0) * hN A k c
        = if m = i then q * hN A j c else 0 := by
      by_cases h : m = i
      · subst h
        simp [hj, Finset.sum_ite_eq']
      · simp [h]
    rw [e1, e2]
    by_cases h : m = i <;> simp [h]
  · have hm4 : m < 4 := by omega
    simp only [elemU', idN, add_mul, Finset.sum_add_distrib]
    have e1 : ∑ k ∈ range d, (if m = k then (1 : ℤ) else 0) * hN (elemRow i j q A) k c
        = hN (elemRow i j q A) m c := by
      simp [Finset.sum_ite_eq, hm]
    have e2 : ∑ k ∈ range d, (if m = i ∧ k = j then q else 0) * hN (elemRow i j q A) k c
        = if m = i then q * hN (elemRow i j q A) j c else 0 := by
      by_cases h : m = i
      · subst h
        simp [hj, Finset.sum_ite_eq']
      · simp [h]
    rw [e1, e2, hN_elemRow i j q A m hm4 c, hN_elemRow i j q A j hj4 c]
    by_cases h : m = i
    · have hji : j ≠ i := fun e => hij e.symm
      simp [h, hji]
    · simp [h]

/-! ## 2. Reachability by elementary steps -/

/-- `B` is obtained from `A` by elementary steps among the first `d` rows. -/
inductive PairReach (d : ℕ) : (Fin 4 → V5) → (Fin 4 → V5) → Prop
  | refl (A : Fin 4 → V5) : PairReach d A A
  | step {A B : Fin 4 → V5} (i j : ℕ) (q : ℤ) (hd : d ≤ 4) (hi : i < d) (hj : j < d) (hij : i ≠ j) :
      PairReach d A B → PairReach d A (elemRow i j q B)

theorem leqOkN_of_pairReach {d : ℕ} {A B : Fin 4 → V5} (h : PairReach d A B) :
    ∃ U U' : ℕ → ℕ → ℤ, LeqOkN d A B U U' := by
  induction h with
  | refl => exact ⟨idN, idN, leqOkN_refl d _⟩
  | step i j q hd hi hj hij _ ih =>
    obtain ⟨U, U', h1⟩ := ih
    exact ⟨_, _, leqOkN_trans h1 (leqOkN_symm (leqOkN_elem hd hi hj hij q _))⟩

/-! ## 3. The checker form: a list of steps -/

/-- Apply a list of steps `(i, j, q)` in order. -/
def applySteps : List (ℕ × ℕ × ℤ) → (Fin 4 → V5) → (Fin 4 → V5)
  | [], A => A
  | (i, j, q) :: l, A => applySteps l (elemRow i j q A)

/-- Boolean validity of a list of steps among the first `d` rows. -/
def stepsValid (d : ℕ) : List (ℕ × ℕ × ℤ) → Bool
  | [] => true
  | (i, j, _) :: l => decide (i < d) && decide (j < d) && decide (i ≠ j) && stepsValid d l

theorem pairReach_trans_elem {d : ℕ} {A B : Fin 4 → V5} (hAB : PairReach d A B) :
    ∀ (l : List (ℕ × ℕ × ℤ)), d ≤ 4 → stepsValid d l = true → PairReach d A (applySteps l B) := by
  intro l
  induction l generalizing B with
  | nil => intro _ _; simpa [applySteps] using hAB
  | cons s l ih =>
    obtain ⟨i, j, q⟩ := s
    intro hd hv
    simp only [stepsValid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨⟨hi, hj⟩, hij⟩, hl⟩ := hv
    exact ih (PairReach.step i j q hd hi hj hij hAB) hd (by simpa [stepsValid] using hl)

/-- Soundness: a valid list of steps gives a unimodular lattice equality. -/
theorem pairReach_applySteps {d : ℕ} (hd : d ≤ 4) (A : Fin 4 → V5) (l : List (ℕ × ℕ × ℤ))
    (hv : stepsValid d l = true) : PairReach d A (applySteps l A) :=
  pairReach_trans_elem (PairReach.refl A) l hd hv

/-! ## 4. The bridge and the class-map composite -/

/-- **The `mred` bridge.**  A class map checked on the pair-reduced rows `m` (Rust: `leq_ok(gmap(.., mred l), c4.l)`)
is a class map on the node rows. -/
theorem leaf3Rel_of_mred {rows m rep : Fin 4 → V5} (hm : PairReach 3 rows m) {g : SP} {U U' : ℕ → ℕ → ℤ}
    (hk : LeqOkN 3 (fun i => g.act (m i)) rep U U') : ∃ V V' : ℕ → ℕ → ℤ, Leaf3Rel g rows rep V V' := by
  obtain ⟨U0, U0', h0⟩ := leqOkN_of_pairReach hm
  exact ⟨_, _, leqOkN_trans (leqOkN_act g h0) hk⟩

/-- The same at depth 2 (the `T2` class map is also checked on reduced rows in some variants). -/
theorem leqOkN2_of_mred {rows m rep : Fin 4 → V5} (hm : PairReach 2 rows m) {g : SP} {U U' : ℕ → ℕ → ℤ}
    (hk : LeqOkN 2 (fun i => g.act (m i)) rep U U') : ∃ V V' : ℕ → ℕ → ℤ, LeqOkN 2 (fun i => g.act (rows i)) rep V V' := by
  obtain ⟨U0, U0', h0⟩ := leqOkN_of_pairReach hm
  exact ⟨_, _, leqOkN_trans (leqOkN_act g h0) hk⟩

/-- Rust `gmap(gn, gr, rows) = gr.apply_inv(gn.apply(rows))` is the single signed permutation `gr^{-1} ∘ gn`. -/
theorem gmap_eq (gn gr : SP) (x : V5) : gr.inv.act (gn.act x) = (gr.inv.mul gn).act x :=
  (act_mul gr.inv gn x).symm

theorem leaf3Rel_of_gmap {rows m rep : Fin 4 → V5} (hm : PairReach 3 rows m) {gn gr : SP} {U U' : ℕ → ℕ → ℤ}
    (hk : LeqOkN 3 (fun i => gr.inv.act (gn.act (m i))) rep U U') :
    ∃ V V' : ℕ → ℕ → ℤ, Leaf3Rel (gr.inv.mul gn) rows rep V V' :=
  leaf3Rel_of_mred hm (g := gr.inv.mul gn) (by simpa [gmap_eq] using hk)

end L5S4
end LRSpectrumFull
