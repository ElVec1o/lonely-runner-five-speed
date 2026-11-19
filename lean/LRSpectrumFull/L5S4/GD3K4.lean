/-
# L5S4.GD3K4 : stream parser of the leaf records and the class-table obligation (stage S4 block 11)

`parseAll k z` reads `k` records of the flat integer layout written by `l5s4k_gen leaves` (97 fixed integers plus 3 per
pair-reduction step).  The parser needs no soundness: `leafOk` is evaluated on the parsed record itself.
`T4Cover C recs` is the only obligation of `t3_leaves` that is not a kernel computation here: for every record of the class
kind (not critical, not an empty window) the stored table `C.t4` has a class whose rows are the record's class rows and a
range containing the record's window range.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GD3K3

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

def v5At (z : List ℤ) (o : ℕ) : V5 := fun i => z.getD (o + i.val) 0

def parseLeaf (z : List ℤ) : LeafRec where
  t := (z.getD 0 0, z.getD 1 0, z.getD 2 0)
  y := v5At z 3
  b := [v5At z 8, v5At z 13]
  r := [v5At z 18, v5At z 23]
  s := [v5At z 28, v5At z 33, v5At z 38]
  x3 := v5At z 43
  w3 := z.getD 48 0
  kind := (z.getD 49 0).toNat
  ck := if z.getD 50 0 = 0 then 0 else 1
  rlo := z.getD 51 0
  rhi := z.getD 52 0
  gp := (fun i => ⟨(z.getD (53 + i.val) 0).toNat % 5, Nat.mod_lt _ (by norm_num)⟩, fun i => z.getD (58 + i.val) 0)
  u := [[z.getD 63 0, z.getD 64 0, z.getD 65 0], [z.getD 66 0, z.getD 67 0, z.getD 68 0],
    [z.getD 69 0, z.getD 70 0, z.getD 71 0]]
  u' := [[z.getD 72 0, z.getD 73 0, z.getD 74 0], [z.getD 75 0, z.getD 76 0, z.getD 77 0],
    [z.getD 78 0, z.getD 79 0, z.getD 80 0]]
  cl := [v5At z 81, v5At z 86, v5At z 91]
  steps := (List.range (z.getD 96 0).toNat).map fun k =>
    ((z.getD (97 + 3 * k) 0).toNat, (z.getD (98 + 3 * k) 0).toNat, z.getD (99 + 3 * k) 0)

def parseAll : ℕ → List ℤ → List LeafRec
  | 0, _ => []
  | k + 1, z => parseLeaf z :: parseAll k (z.drop (97 + 3 * (z.getD 96 0).toNat))

/-- The class-table obligation of the class-kind records (discharged by the T4 stage, not here). -/
def T4Cover (C : Certificate) (recs : List LeafRec) : Prop :=
  ∀ r ∈ recs, r.kind ≠ 0 → r.kind ≠ 1 → ∃ cl ∈ C.t4, (∀ i : Fin 4, i.val < 3 → padL3 cl.l i = rowsL r.cl i) ∧
    ∃ rg ∈ cl.ranges, rg.1 ≤ r.rlo ∧ r.rhi ≤ rg.2

end L5S4
end LRSpectrumFull
