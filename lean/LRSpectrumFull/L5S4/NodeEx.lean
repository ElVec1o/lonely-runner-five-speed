/-
# L5S4.NodeEx : non-vacuity of `NodeW`, and lattice-equality algebra for the leaf relation

Case-tree certificate, part 4.

* `exNode : NodeW 1 4` : the depth-1 node of `h = (1,1,0,0,0)` (`K = (1,-1,0,0,0), e_3, e_4, e_5`, witness `x = (1,..,1)/2`);
  shows the structure is inhabited (the hypotheses `StreamHyp.t1` etc. are not about an empty type).
* `leqOkN_trans`, `leqOkN_act`, `leqOkN_symm` : `LeqOkN` composes (matrices `U₁ U₂`, `U₂' U₁'`), is invariant under
  the signed permutations, and is symmetric.  With these, a lattice map checked on the rows `mred(l)` (the Rust applies
  `leq_ok` to the pair-reduced rows) transfers to the node rows `l`, once `LeqOkN 3 l (mred l)` is certified.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.Induct

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## 1. Non-vacuity of `NodeW` -/

def exH : V5 := ![1, 1, 0, 0, 0]
def exRows : Fin 4 → V5 := fun i => if i.val = 0 then exH else fun _ => 0
def exBb : Fin 4 → V5 := ![![1, -1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]
def exRr : Fin 4 → V5 := ![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]
def exSs : Fin 1 → V5 := fun _ => ![1, 0, 0, 0, 0]
def exWit : ℕ → V5 × ℤ := fun _ => ((fun _ => 1), 2)

theorem exId : NodeId (fun i : Fin 1 => hN exRows i.val) exBb exSs exRr := by
  refine ⟨?_, ?_, ?_⟩ <;> intro i k <;> revert i k <;> decide

theorem exWit_c (k : ℕ) : cOf (exWit k) = 1 / 2 := by
  simp [cOf, exWit, wMin]

/-- A depth-1 node (`h = (1,1,0,0,0)`): the structure `NodeW` is inhabited. -/
def exNode : NodeW 1 4 where
  rows := exRows
  b := exBb
  s := exSs
  r := exRr
  id := exId
  wit := exWit
  w0 := rfl
  wok := by
    intro k hk
    refine ⟨by simp [exWit], fun i hi => ?_⟩
    have : i.val = 0 ∨ k = 0 := by omega
    rcases this with h | h
    · have hi0 : i = 0 := Fin.ext h
      subst hi0
      simp [exWit, exRows, exH, dot, Fin.sum_univ_five]
    · omega
  wge := by intro k _; rw [exWit_c]; norm_num
  rk := ⟨1, by simp [radSet, SArr, exWit_c]; norm_num⟩

/-! ## 2. Algebra of `LeqOkN` -/

theorem leqOkN_symm {d : ℕ} {t b : Fin 4 → V5} {U U' : ℕ → ℕ → ℤ} (h : LeqOkN d t b U U') :
    LeqOkN d b t U' U := ⟨h.2, h.1⟩

theorem leqOkN_trans {d : ℕ} {A B C : Fin 4 → V5} {U1 U1' U2 U2' : ℕ → ℕ → ℤ}
    (h1 : LeqOkN d A B U1 U1') (h2 : LeqOkN d B C U2 U2') :
    LeqOkN d A C (fun i k => ∑ m ∈ range d, U1 i m * U2 m k) (fun i k => ∑ m ∈ range d, U2' i m * U1' m k) := by
  refine ⟨fun i hi c => ?_, fun i hi c => ?_⟩
  · rw [h1.1 i hi c]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [h2.1 m (Finset.mem_range.1 hm) c, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  · rw [h2.2 i hi c]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [h1.2 m (Finset.mem_range.1 hm) c, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => by ring)

theorem leqOkN_act {d : ℕ} {A B : Fin 4 → V5} {U U' : ℕ → ℕ → ℤ} (g : SP) (h : LeqOkN d A B U U') :
    LeqOkN d (fun i => g.act (A i)) (fun i => g.act (B i)) U U' := by
  have key : ∀ (X Y : Fin 4 → V5) (i : ℕ) (n : ℕ) (c : ℕ → ℤ),
      (∀ a, hN X i a = ∑ k ∈ range n, c k * hN Y k a) →
      ∀ a, g.act (hN X i) a = ∑ k ∈ range n, c k * g.act (hN Y k) a := by
    intro X Y i n c e a
    simp only [SP.act]
    rw [e (g.σ a), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  refine ⟨fun i hi c => ?_, fun i hi c => ?_⟩
  · simp only [hN_act]
    exact key A B i d (U i) (fun a => h.1 i hi a) c
  · simp only [hN_act]
    exact key B A i d (U' i) (fun a => h.2 i hi a) c

end L5S4
end LRSpectrumFull
