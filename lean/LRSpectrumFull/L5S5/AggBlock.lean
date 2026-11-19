/-
# L5S5.AggBlock : generic blocks of depth-2 representatives with local class tables and row links

An `RBlock` is the statement-level record of a run of representatives of ONE depth-1 node: size, index function, the
concatenation of their local class tables, the `t3` clause under `LocRegistered`, and the row link
`rows (idx i) = E (pos0 + i)` (the rows that the `t2` leader record at position `pos0 + i` of the depth-1 node demands).
`append` is the only combinator (constant fuel: `idx i = if i < size1 then idx1 i else idx2 (i - size1)`, no list walk);
its two side conditions are literal-arithmetic facts discharged by `rfl`.  `RepData` is the data of one representative whose
module is not built yet: the generated `Holes` structures consist of such fields, so every missing representative is an
explicit named hypothesis.  `five_speed_spectrum_of_clauses` is the final assembly from the four stream clauses.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S5.AggSketch
import LRSpectrumFull.L5S4.GD3O1

namespace LRSpectrumFull
namespace L5S5

open LRSpectrumFull.L5S3 LRSpectrumFull.L5S4

theorem locReg_left' {C : Certificate} {a b : List T4Rec} (h : LocRegistered C (a ++ b)) : LocRegistered C a :=
  fun cl hcl => h cl (List.mem_append_left _ hcl)

theorem locReg_right' {C : Certificate} {a b : List T4Rec} (h : LocRegistered C (a ++ b)) : LocRegistered C b :=
  fun cl hcl => h cl (List.mem_append_right _ hcl)

structure RBlock {ρ : Type} (rowsOf : NodeW 2 3 → ρ) (E : ℕ → ρ) where
  pos0 : ℕ
  size : ℕ
  idx : ℕ → NodeW 2 3
  tab : List T4Rec
  ok : ∀ C : Certificate, LocRegistered C tab → ∀ i, i < size → T3At C (idx i)
  lk : ∀ i, i < size → rowsOf (idx i) = E (pos0 + i)

namespace RBlock

variable {ρ : Type} {rowsOf : NodeW 2 3 → ρ} {E : ℕ → ρ}

def single (pos : ℕ) (n : NodeW 2 3) (tab : List T4Rec)
    (h : ∀ C : Certificate, LocRegistered C tab → T3At C n) (hl : rowsOf n = E pos) : RBlock rowsOf E where
  pos0 := pos
  size := 1
  idx := fun _ => n
  tab := tab
  ok := fun C hC _ _ => h C hC
  lk := by
    intro i hi
    have : i = 0 := by omega
    subst this
    simpa using hl

def append (B1 B2 : RBlock rowsOf E) (hp : B2.pos0 = B1.pos0 + B1.size) : RBlock rowsOf E where
  pos0 := B1.pos0
  size := B1.size + B2.size
  idx := fun i => if i < B1.size then B1.idx i else B2.idx (i - B1.size)
  tab := B1.tab ++ B2.tab
  ok := by
    intro C hC i hi
    by_cases h : i < B1.size
    · simp only [h, if_true]; exact B1.ok C (locReg_left' hC) i h
    · simp only [h, if_false]; exact B2.ok C (locReg_right' hC) _ (by omega)
  lk := by
    intro i hi
    by_cases h : i < B1.size
    · simp only [h, if_true]; exact B1.lk i h
    · simp only [h, if_false]
      rw [B2.lk (i - B1.size) (by omega), hp]
      congr 1
      omega

end RBlock

/-- the data of one representative (node, local table, `t3`, row link): a field of a generated `Holes` structure -/
structure RepData {ρ : Type} (rowsOf : NodeW 2 3 → ρ) (E : ℕ → ρ) (pos : ℕ) where
  node : NodeW 2 3
  tab : List T4Rec
  ok : ∀ C : Certificate, LocRegistered C tab → T3At C node
  lk : rowsOf node = E pos

def RepData.blk {ρ : Type} {rowsOf : NodeW 2 3 → ρ} {E : ℕ → ρ} {pos : ℕ} (r : RepData rowsOf E pos) : RBlock rowsOf E :=
  RBlock.single pos r.node r.tab r.ok r.lk

/-- **The final assembly from the four stream clauses** (generic in the aggregation). -/
theorem five_speed_spectrum_of_clauses {C : Certificate} {R1 : Set (NodeW 1 4)} {R2 : Set (NodeW 2 3)}
    (t1 : ∀ h : V5, T1Ok h → ∃ n ∈ R1, hN n.rows 0 = h)
    (t2 : ∀ n ∈ R1, ∀ y : V5, ChildPass n y →
      ∃ (y' : V5) (n2 : NodeW 2 3), (∀ i, dot (n.b i) y' = dot (n.b i) y) ∧ n2.rows = setRow n.rows 1 y' ∧
        ∃ rep ∈ R2, ∃ (g : SP) (U U' : ℕ → ℕ → ℤ), Chain2Rel g n2.rows rep.rows U U')
    (t3 : ∀ n ∈ R2, T3At C n)
    (lines : ∀ cl ∈ C.t4, ∀ u : V5, Primitive u → (∀ i, u i ≠ 0) → (∀ i j, i ≠ j → |u i| ≠ |u j|) →
      InClass cl u → (∃ r ∈ C.t5, ∃ g : SP, g.act u = r.v) ∨ 1 / 5 ≤ ML u)
    (hres : ∀ r ∈ C.t5, ResOK r.v)
    (v : Fin 5 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) (hlt : ML v < 1 / 5) :
    ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1) :=
  five_speed_spectrum_of_stream (H := (⟨t1, t2, fun n hn y hy => t3 n hn y hy, lines⟩ : StreamHyp' C R1 R2)) hres v hpos hinj hlt

#print axioms RBlock.single
#print axioms RBlock.append
#print axioms RepData.blk
#print axioms five_speed_spectrum_of_clauses

end L5S5
end LRSpectrumFull
