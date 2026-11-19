/-
# L5S4.LinRGlue : from the row-interval chunk theorems to the `lines` clause of `StreamHyp'` / `TreeHyp` (stage S4 block 17)

`lines_clause_R` is `LinGlue.lines_clause` for the record type `ℕ × ℕ` (class record, stream `W`): if every pair `p` of a list `blobs`
passes `classLinesR (dg p.1) p.2` (the generated `LinR<tag>C<j>.ok` theorems, glued by `List.mem_append`), every class `cl` of the
certificate table `C.t4` is read by some record of `blobs` (same three rows `l` and the same range list: the data-inclusion statement,
a pure comparison of table entries), and every tuple of `T5V` is the `v` of a stored `T5` record of `C`, then the `lines` clause holds:

  `∀ cl ∈ C.t4, ∀ u, Primitive u → (∀ i, u i ≠ 0) → (∀ i j, i ≠ j → |u i| ≠ |u j|) →
     InClass cl u → (∃ r ∈ C.t5, ∃ g : SP, g.act u = r.v) ∨ 1/5 ≤ ML u`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.LinRSound

namespace LRSpectrumFull
namespace L5S4
namespace Lin

open LRSpectrumFull.L5S3

theorem chunksR_ok_append {l1 l2 : List (ℕ × ℕ)} (h1 : (l1.all fun p => classLinesR (dg p.1) p.2) = true)
    (h2 : (l2.all fun p => classLinesR (dg p.1) p.2) = true) :
    ((l1 ++ l2).all fun p => classLinesR (dg p.1) p.2) = true := by
  rw [List.all_append, h1, h2]; rfl

theorem lines_clause_R (C : Certificate) (blobs : List (ℕ × ℕ))
    (hok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true)
    (hcov : ∀ cl ∈ C.t4, ∃ p ∈ blobs, (∀ i : Fin 3, cl.l i = fun a : Fin 5 => dg p.1 (11 + 5 * i.val + a.val)) ∧
      cl.ranges = (List.range (dg p.1 61).toNat).map fun j => (dg p.1 (62 + 2 * j), dg p.1 (63 + 2 * j)))
    (ht5 : ∀ r ∈ T5V, ∃ r' ∈ C.t5, r'.v = T5Vec r) :
    ∀ cl ∈ C.t4, ∀ u : V5, Primitive u → (∀ i, u i ≠ 0) → (∀ i j, i ≠ j → |u i| ≠ |u j|) →
      InClass cl u → (∃ r ∈ C.t5, ∃ g : SP, g.act u = r.v) ∨ 1 / 5 ≤ ML u := by
  intro cl hcl u hprim hnz hdist hc
  obtain ⟨p, hp, hl, hrg⟩ := hcov cl hcl
  rw [List.all_eq_true] at hok
  have := classLinesR_inClass (dg p.1) p.2 (hok p hp) cl hl hrg u hprim hnz hdist hc
  rcases this with ⟨r, hr, g, hg⟩ | h
  · obtain ⟨r', hr', hv⟩ := ht5 r hr
    exact Or.inl ⟨r', hr', g, by rw [hv]; exact hg⟩
  · exact Or.inr h

end Lin
end L5S4
end LRSpectrumFull
