/-
# L5S4.Link : node data and the flag (E2 + E3 + E4 together), plus a non-vacuity instance

Stage S4 block 1.  For a flag `F` of `v` and a node `(l, b, s, r)` whose chain rows `l` are the first `j` rows of
`F` (`NodeId (fun i : Fin j => hN F.h i) b s r`):

* `flag_minor_node` : `G_j = leadMinor (gram F) j = gF b` (the generator's `gs[j]`),
                      `G_{j+1} = qform b (h_j) = t^T adj(a) t` with `t_i = b_i · h_j`,
                      `μ_{j+1}² = Dq_j = (t^T adj(a) t) / G_j` (the integer norm formula, E4).
* `node_minor_chain`: the same `G_j` for any flag with the same chain level `j` (E1 + E2).
* `tvec_of_lat`    : `t = B y` is unchanged when `y` moves by an integer combination of the rows `l`.
* `nodeId_example`  : a concrete inhabited `NodeId` (`j = 1`, `l = e_1`), with the formula evaluated on one `y`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.Dict
import LRSpectrumFull.L5S4.Chain
import LRSpectrumFull.L5S3.Minors

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

theorem snoc_eq_hN {v : V5} (F : FlagData v) (j : ℕ) (hj : j < 4) :
    (Fin.snoc (α := fun _ => V5) (fun i : Fin j => hN F.h i.val) (F.h ⟨j, hj⟩) : Fin (j + 1) → V5)
      = fun i : Fin (j + 1) => hN F.h i.val := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [hN, hj]
  · simp [Fin.snoc_castSucc]

theorem flag_minor_node {v : V5} (F : FlagData v) {j d : ℕ} (hjd : j + d = 5) (hj : j < 4)
    {b : Fin d → V5} {s : Fin j → V5} {r : Fin d → V5}
    (hnode : NodeId (fun i : Fin j => hN F.h i.val) b s r) :
    leadMinor (gram F) j = gF b ∧
    leadMinor (gram F) (j + 1) = qform b (F.h ⟨j, hj⟩) ∧
    F.Dq ⟨j, hj⟩ = (qform b (F.h ⟨j, hj⟩) : ℚ) / (gF b : ℚ) := by
  have h1 : leadMinor (gram F) j = gF b := by
    rw [leadMinor_eq_gF F j (by omega), gF_compl hjd hnode]
  have h2 : leadMinor (gram F) (j + 1) = qform b (F.h ⟨j, hj⟩) := by
    rw [leadMinor_eq_gF F (j + 1) (by omega), ← snoc_eq_hN F j hj, gF_snoc hjd hnode]
  refine ⟨h1, h2, ?_⟩
  rw [Dq_minors_thm v F ⟨j, hj⟩]
  simp only [h1, h2]

theorem node_minor_chain {v : V5} (F F' : FlagData v) {j d : ℕ} (hjd : j + d = 5) (hj : j < 4)
    (hc : SameChain F F' j) {b : Fin d → V5} {s : Fin j → V5} {r : Fin d → V5}
    (hnode : NodeId (fun i : Fin j => hN F'.h i.val) b s r) :
    leadMinor (gram F) j = gF b := by
  rw [← leadMinor_chain F F' j (by omega) hc]
  exact (flag_minor_node F' hjd hj hnode).1

theorem tvec_of_lat {j d : ℕ} {l : Fin j → V5} {b : Fin d → V5} {s : Fin j → V5} {r : Fin d → V5}
    (hnode : NodeId l b s r) (y : V5) (c : Fin j → ℤ) :
    tvec b (fun a => y a + ∑ k, c k * l k a) = tvec b y := by
  funext i
  unfold tvec dot
  have : ∀ a, b i a * (y a + ∑ k, c k * l k a) = b i a * y a + ∑ k, c k * (b i a * l k a) := by
    intro a; rw [mul_add, Finset.mul_sum]
    congr 1; exact Finset.sum_congr rfl (fun k _ => by ring)
  simp only [this, Finset.sum_add_distrib]
  have h2 : ∑ a, ∑ k, c k * (b i a * l k a) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero; intro k _
    rw [← Finset.mul_sum]
    have := hnode.bl i k
    unfold dot at this
    rw [this, mul_zero]
  rw [h2, add_zero]

/-! ## Non-vacuity: `j = 1`, `l = e_0`, `K = span e_1..e_4` -/

def exL : Fin 1 → V5 := fun _ k => if k = 0 then 1 else 0
def exB : Fin 4 → V5 := fun i k => if k.val = i.val + 1 then 1 else 0
def exS : Fin 1 → V5 := exL

theorem nodeId_example : NodeId exL exB exS exB := by
  refine ⟨?_, ?_, ?_⟩ <;> intro i k <;> revert i k <;> decide

/-- A test vector `y = (3, 1, 2, 3, 4)`: `t = (1,2,3,4)`, `a = I`, `G_2 = |y|² - y_0² = 30`. -/
def exY : V5 := ![3, 1, 2, 3, 4]

theorem example_gF : gF (Fin.snoc (α := fun _ => V5) exL exY : Fin 2 → V5) = 30 := by
  unfold gF
  rw [Matrix.det_fin_two]
  simp [dot, Fin.sum_univ_five, exL, exY, Fin.snoc]

theorem example_gramK : gramK exB = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [gramK, dot, Fin.sum_univ_five, exB]

theorem example_q : qform exB exY = 30 := by
  unfold qform
  rw [example_gramK, Matrix.adjugate_one]
  simp [tvec, dot, Fin.sum_univ_five, exB, exY, dotProduct, Fin.sum_univ_four]

/-- The two sides of `gF_snoc` agree on the example (independent evaluation, not just the theorem). -/
theorem example_agree :
    gF (Fin.snoc (α := fun _ => V5) exL exY : Fin 2 → V5) = qform exB exY := by
  rw [example_gF, example_q]

end L5S4
end LRSpectrumFull
