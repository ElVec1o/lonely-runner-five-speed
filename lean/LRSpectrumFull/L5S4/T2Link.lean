/-
# L5S4.T2Link : from the leaders of a node to the rollout block (stage S4R)

`hlink_of_block` : if the block `idx` (the nodes `N<rep>.nK` of the rollout, in global class-id order) satisfies
`(idx i).rows = setRow n.rows 1 (cY L[repPos i])` for `i < repPos.length`, and every leader position `j ∈ lead` occurs in `repPos`,
then every leader has a node of the block with the same rows.  Only `rep.rows` enters `Chain2Rel`, so this is all `t2` needs
from the `t3` side; `t2_of_link` (T2Gen) turns it into the `rep ∈ R2` clause of `StreamHyp'.t2`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.T2Gen

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

theorem hlink_of_block (n : NodeW 1 4) (L : List (List ℤ)) (lead repPos : List ℕ)
    (hsub : ∀ j ∈ lead, j ∈ repPos) (idx : ℕ → NodeW 2 3)
    (hrows : ∀ i, i < repPos.length → (idx i).rows = setRow n.rows 1 (cY (L.getD (repPos.getD i 0) []))) :
    ∀ j ∈ lead, ∃ m ∈ ({a | ∃ i, i < repPos.length ∧ a = idx i} : Set (NodeW 2 3)),
      m.rows = setRow n.rows 1 (cY (L.getD j [])) := by
  intro j hj
  obtain ⟨i, hi, hij⟩ := List.getElem_of_mem (hsub j hj)
  refine ⟨idx i, ⟨i, hi, rfl⟩, ?_⟩
  have := hrows i hi
  have e : repPos.getD i 0 = j := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; simpa using hij
  rw [e] at this; exact this

end L5S4
end LRSpectrumFull
