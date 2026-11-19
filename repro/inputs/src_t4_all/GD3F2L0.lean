/-
# L5S4.GD3F2L0 : `StreamHyp'.t3` for rep #0 from the FLAT leaf checker (S4N)

`recsF` is the record list read from the per-record naturals; `recsF_ok` is `leafOkF_sound` on every record; the `t3` clause
is `t3_leaves` exactly as in `GD3L0.t3_node`, conditional only on the class-table obligation `T4Cover`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GD3F2L0R0

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace LRSpectrumFull
namespace L5S4
namespace N0
open Matrix Finset LRSpectrumFull.L5S3

def blobsF : List ℕ := blobsF_c0
def recsF : List LeafRec := blobsF.map fun N => recOf (dg N)

theorem alignF : storedOf cks = recsF.map LeafRec.t := by decide +kernel

theorem blobsF_ok : ∀ N ∈ blobsF, leafOkF (dg NN) (dg N) = true := by
  intro N hN
  simp only [blobsF, List.mem_append] at hN
  exact List.all_eq_true.1 okF_c0 N hN

theorem recsF_ok : ∀ r ∈ recsF, leafOk nK r = true := by
  intro r hr
  obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hr
  exact leafOkF_sound nK (dg NN) (dg N) ag (blobsF_ok N hN)

/-- `StreamHyp'.t3` for rep #0 from the flat checker: conditional only on `T4Cover`. -/
theorem t3_nodeF (C : Certificate) (hT4 : T4Cover C recsF) :
    ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n3 : LeafW), (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧
      n3.rows = setRow nK.rows 2 y' ∧ LeafRelW C n3 :=
  fun y hy => t3_leaves C nK bn bd (by norm_num [bd]) hrad cks (by rw [fc_eq]; exact cov) (by rw [fc_eq]; exact allok)
    recsF alignF recsF_ok hT4 y hy

#print axioms t3_nodeF

end N0
end L5S4
end LRSpectrumFull
