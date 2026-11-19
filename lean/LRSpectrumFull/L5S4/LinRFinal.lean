/-
# L5S4.LinRFinal : the `lines` clause for the whole class table (81,436 classes), assembled from the 1,063 chunk theorems (stage S4 block 18)

`LinRAll.ok` is the glued chunk theorem for `LinRAll.blobs` (all classes of the certificate, generated, node by node).  `lines_clause_all`
is `lines_clause_tab` for this list: for `lineCert LinRAll.blobs t5` the `lines` clause of `StreamHyp'` / `TreeHyp` holds given only
`ht5` (the 25 residual tuples are among the stored `T5` records).  `lines_count` states that the table has 81,436 entries.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.LinRAll
import LRSpectrumFull.L5S4.LinRCov

namespace LRSpectrumFull
namespace L5S4
namespace Lin

open LRSpectrumFull.L5S3

theorem lines_clause_all (t5 : List T5Rec) (ht5 : ∀ r ∈ T5V, ∃ r' ∈ t5, r'.v = T5Vec r) :
    ∀ cl ∈ (lineCert LinRAll.blobs t5).t4, ∀ u : V5, Primitive u → (∀ i, u i ≠ 0) → (∀ i j, i ≠ j → |u i| ≠ |u j|) →
      InClass cl u → (∃ r ∈ (lineCert LinRAll.blobs t5).t5, ∃ g : SP, g.act u = r.v) ∨ 1 / 5 ≤ ML u :=
  lines_clause_tab LinRAll.blobs t5 LinRAll.ok ht5

theorem lines_count : LinRAll.blobs.length = 81436 := by decide +kernel

#print axioms lines_clause_all
#print axioms lines_count

end Lin
end L5S4
end LRSpectrumFull
