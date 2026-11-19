/-
# L5S4.GD3OA1 : `StreamHyp'.t3` for rep #1 with NO hypothesis: flat leaf checker + class-table cover (T4Cover) discharged for the local table (S4O)

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GD3O1Rc0
import LRSpectrumFull.L5S4.GD3F2N1
import LRSpectrumFull.L5S4.GD3O1T

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace LRSpectrumFull
namespace L5S4
namespace N1
open Matrix Finset LRSpectrumFull.L5S3

def blobsO : List ℕ := blobsO_c0
def recsO : List LeafRec := blobsO.map fun N => recOf (dg N)

theorem alignO : storedOf cks = recsO.map LeafRec.t := by decide +kernel

theorem blobsO_ok : ∀ N ∈ blobsO, leafOkF (dg NN) (dg N) = true ∧ t4F (dg TT) ST nT (dg N) = true := by
  intro N hN
  simp only [blobsO, List.mem_append] at hN
  have h0 := hN
  have := List.all_eq_true.1 okO_c0 N h0
  simpa [Bool.and_eq_true] using this

theorem recsO_ok : ∀ r ∈ recsO, leafOk nK r = true := by
  intro r hr
  obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hr
  exact leafOkF_sound nK (dg NN) (dg N) ag (blobsO_ok N hN).1

def tabO : List T4Rec := (List.range nT).map (t4At (dg TT) ST)
def Crep : Certificate := ⟨[], [], [], [], tabO, []⟩

theorem t4coverO : T4Cover Crep recsO := by
  intro r hr hk0 hk1
  obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hr
  exact t4F_sound (dg TT) ST nT (dg N) (blobsO_ok N hN).2 hk0 hk1

/-- `StreamHyp'.t3` for rep #1 with NO hypothesis, for the local certificate `Crep`. -/
theorem t3_nodeU :
    ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n3 : LeafW), (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧
      n3.rows = setRow nK.rows 2 y' ∧ LeafRelW Crep n3 :=
  fun y hy => t3_leaves Crep nK bn bd (by norm_num [bd]) hrad cks (by rw [fc_eq]; exact cov) (by rw [fc_eq]; exact allok)
    recsO alignO recsO_ok t4coverO y hy

/-- Lifting to any certificate whose table registers every local class (same rows, ranges covered). -/
theorem t3_nodeU_of (C : Certificate) (hsub : LocRegistered C tabO) :
    ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n3 : LeafW), (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧
      n3.rows = setRow nK.rows 2 y' ∧ LeafRelW C n3 := by
  intro y hy
  obtain ⟨y', n3, h1, h2, h3⟩ := t3_nodeU y hy
  exact ⟨y', n3, h1, h2, leafRelW_of_registered hsub h3⟩

#print axioms t3_nodeU
#print axioms t3_nodeU_of

end N1
end L5S4
end LRSpectrumFull
