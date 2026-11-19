/-
# L5S5.AggSketch : the aggregation scheme for the 1,965 depth-2 representatives (sketch, compiles)

Problem: `StreamHyp'.t3` quantifies over a SET `R2` of depth-2 nodes, while the per-representative theorems
(`N<rep>.t3_nodeU`, one module each, about 1,965 of them) live in separate modules.  A final module must (i) name `R2`,
(ii) prove `∀ n ∈ R2, T3At C n`, (iii) let the depth-2 closure (`t2`) point at members of `R2` by an index, without a
lookup whose cost grows with the number of representatives.

Scheme: a `Block` is a size, an index function `at : ℕ → α` and a proof `∀ i < size, P (at i)`.  `Block.single` wraps one
representative (its module supplies `T3At`).  `Block.append` is the only combinator; its index function is
`if i < size₁ then at₁ i else at₂ (i - size₁)`, so a lookup in a tree of `d` binary levels costs `d` comparisons (constant
fuel: no list walk, no `List.getD`, no growing literal).  A master module imports at most 8 blocks and appends them; the
counts of the master are literals added by the kernel.  The set `R2` is `Block.set`; `forall_set` is the t3 clause for ALL
members, and `at_mem` gives `rep ∈ R2` for an index, which is all the depth-2 closure needs.  Per depth-1 node `d` a block
`R2_d` (33, 159, 27, ..., 492, ... reps); the top master is `append` over the 26 depth-1 blocks (26 -> 4 -> 1).

`streamHyp'_of_block`: the field-by-field assembly of `StreamHyp'` from `t1`, `t2` (pointing into the block), the block and
`lines`.  `five_speed_spectrum_of_block`: the final theorem from those hypotheses and the residual check.

Import cost of the proposed layout: about 1,000 real modules in one lean process
need 2.85 GB and 3 s, the same as the 2.77 GB Mathlib floor.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S5.FiveSpeedOfTree

namespace LRSpectrumFull
namespace L5S5

open LRSpectrumFull.L5S3 LRSpectrumFull.L5S4

/-! ## 1. Generic blocks -/

structure Block (α : Type) (P : α → Prop) where
  size : ℕ
  idx : ℕ → α
  ok : ∀ i, i < size → P (idx i)

namespace Block

variable {α : Type} {P : α → Prop}

def single (a : α) (h : P a) : Block α P := ⟨1, fun _ => a, fun _ _ => h⟩

def append (B1 B2 : Block α P) : Block α P where
  size := B1.size + B2.size
  idx := fun i => if i < B1.size then B1.idx i else B2.idx (i - B1.size)
  ok := by
    intro i hi
    by_cases h : i < B1.size
    · simp only [h, if_true]; exact B1.ok i h
    · simp only [h, if_false]; exact B2.ok _ (by omega)

/-- the set of members (this is `R2`) -/
def set (B : Block α P) : Set α := {a | ∃ i, i < B.size ∧ a = B.idx i}

theorem forall_set (B : Block α P) : ∀ a ∈ B.set, P a := by
  rintro a ⟨i, hi, rfl⟩
  exact B.ok i hi

theorem at_mem (B : Block α P) (i : ℕ) (hi : i < B.size) : B.idx i ∈ B.set := ⟨i, hi, rfl⟩

theorem idx_append_left (B1 B2 : Block α P) (i : ℕ) (hi : i < B1.size) : (append B1 B2).idx i = B1.idx i := by
  simp [append, hi]

theorem idx_append_right (B1 B2 : Block α P) (i : ℕ) : (append B1 B2).idx (B1.size + i) = B2.idx i := by
  simp [append]

theorem set_append (B1 B2 : Block α P) : (append B1 B2).set = B1.set ∪ B2.set := by
  ext a
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h : i < B1.size
    · exact Or.inl ⟨i, h, (idx_append_left B1 B2 i h).symm ▸ rfl⟩
    · refine Or.inr ⟨i - B1.size, by simp [append] at hi; omega, ?_⟩
      have : i = B1.size + (i - B1.size) := by omega
      rw [this, idx_append_right, ← this]
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, by simp [append]; omega, (idx_append_left B1 B2 i hi).symm⟩
    · exact ⟨B1.size + i, by simp [append]; omega, (idx_append_right B1 B2 i).symm⟩

end Block

/-! ## 2. The `t3` property and the assembly of `StreamHyp'` -/

/-- the `t3` clause of `StreamHyp'` at one node -/
def T3At (C : Certificate) (n : NodeW 2 3) : Prop :=
  ∀ y : V5, ChildPass n y →
    ∃ (y' : V5) (n3 : LeafW), (∀ i, dot (n.b i) y' = dot (n.b i) y) ∧ n3.rows = setRow n.rows 2 y' ∧ LeafRelW C n3

abbrev RepBlock (C : Certificate) := Block (NodeW 2 3) (T3At C)

theorem streamHyp'_of_block {C : Certificate} {R1 : Set (NodeW 1 4)} (B : RepBlock C)
    (t1 : ∀ h : V5, T1Ok h → ∃ n ∈ R1, hN n.rows 0 = h)
    (t2 : ∀ n ∈ R1, ∀ y : V5, ChildPass n y →
      ∃ (y' : V5) (n2 : NodeW 2 3), (∀ i, dot (n.b i) y' = dot (n.b i) y) ∧ n2.rows = setRow n.rows 1 y' ∧
        ∃ rep ∈ B.set, ∃ (g : SP) (U U' : ℕ → ℕ → ℤ), Chain2Rel g n2.rows rep.rows U U')
    (lines : ∀ cl ∈ C.t4, ∀ u : V5, Primitive u → (∀ i, u i ≠ 0) → (∀ i j, i ≠ j → |u i| ≠ |u j|) →
      InClass cl u → (∃ r ∈ C.t5, ∃ g : SP, g.act u = r.v) ∨ 1 / 5 ≤ ML u) :
    StreamHyp' C R1 B.set :=
  ⟨t1, t2, fun n hn y hy => B.forall_set n hn y hy, lines⟩

/-- **The final theorem, from the four stream clauses, the residual check and the block.** -/
theorem five_speed_spectrum_of_block {C : Certificate} {R1 : Set (NodeW 1 4)} (B : RepBlock C)
    (t1 : ∀ h : V5, T1Ok h → ∃ n ∈ R1, hN n.rows 0 = h)
    (t2 : ∀ n ∈ R1, ∀ y : V5, ChildPass n y →
      ∃ (y' : V5) (n2 : NodeW 2 3), (∀ i, dot (n.b i) y' = dot (n.b i) y) ∧ n2.rows = setRow n.rows 1 y' ∧
        ∃ rep ∈ B.set, ∃ (g : SP) (U U' : ℕ → ℕ → ℤ), Chain2Rel g n2.rows rep.rows U U')
    (lines : ∀ cl ∈ C.t4, ∀ u : V5, Primitive u → (∀ i, u i ≠ 0) → (∀ i j, i ≠ j → |u i| ≠ |u j|) →
      InClass cl u → (∃ r ∈ C.t5, ∃ g : SP, g.act u = r.v) ∨ 1 / 5 ≤ ML u)
    (hres : ∀ r ∈ C.t5, ResOK r.v)
    (v : Fin 5 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) (hlt : ML v < 1 / 5) :
    ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1) :=
  five_speed_spectrum_of_stream (streamHyp'_of_block B t1 t2 lines) hres v hpos hinj hlt

/-! ## 3. Non-vacuity and a lookup test of the scheme (constant depth) -/

def demoA : Block ℕ (fun n => n < 100) := Block.single 3 (by norm_num)
def demoB : Block ℕ (fun n => n < 100) := Block.single 5 (by norm_num)
def demoC : Block ℕ (fun n => n < 100) := Block.single 7 (by norm_num)
def demo8 : Block ℕ (fun n => n < 100) :=
  ((demoA.append demoB).append (demoC.append demoA)).append ((demoB.append demoC).append (demoA.append demoB))

example : demo8.size = 8 := rfl
example : demo8.idx 0 = 3 := rfl
example : demo8.idx 3 = 3 := rfl
example : demo8.idx 5 = 7 := rfl
example : demo8.idx 7 = 5 := rfl
example : demo8.idx 5 ∈ demo8.set := demo8.at_mem 5 (by decide)
/-- a negative control: the lookup does NOT return the wrong member -/
example : demo8.idx 1 ≠ 3 := by decide

end L5S5
end LRSpectrumFull
