/-
# L5S4.LinRCov : the data-inclusion hypotheses `hcov` and `ht5` of `lines_clause_R`, discharged by construction (stage S4 block 18)

`t4OfRec N` reads the class `T4Rec` of a lines record `N` (rows `l`, `k`, `q`, `p`, merged range list, from the digits of the record;
`g` is the identity placeholder, as `t4At`).  `linTab blobs` is the class table whose entries are the records of the chunk list, and
`lineCert blobs t5` is the certificate with exactly that `t4`.  For this table `hcov` is a membership fact (`hcov_linTab`), so
`lines_clause_tab` has NO hypothesis on the class table: it needs only the chunk theorem `blobs.all .. = true` and `ht5`.

`ht5` (the 25 residual tuples `T5V` are among the stored `T5` records): `t5Incl vs = true` (a decidable test on the tuple list `vs`
of the `T5` data) and `t5.map v = vs.map T5Vec` give it (`ht5_of_incl`).

What stays outside (stated, not assumed here): the leaf side must show that every class the tree uses is registered in `linTab`
(`LocRegistered (lineCert ..) tab`, GD3O1), and the `T5` stage must supply the records `t5`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.LinRGlue

namespace LRSpectrumFull
namespace L5S4
namespace Lin

open LRSpectrumFull.L5S3

/-- the class record read from the digits of a lines record (layout of `LinRCore`). -/
def t4OfRec (N : ℕ) : T4Rec where
  g := SP.one
  l := fun i a => dg N (11 + 5 * i.val + a.val)
  k := fun i a => dg N (26 + 5 * i.val + a.val)
  q := fun i a => dg N (36 + 5 * i.val + a.val)
  p := fun i a => dg N (46 + 5 * i.val + a.val)
  ranges := (List.range (dg N 61).toNat).map fun j => (dg N (62 + 2 * j), dg N (63 + 2 * j))

/-- the class table whose entries are the records of the chunk list. -/
def linTab (blobs : List (ℕ × ℕ)) : List T4Rec := blobs.map fun p => t4OfRec p.1

/-- the certificate whose class table is `linTab blobs` (all other streams empty; `t5` supplied by the T5 stage). -/
def lineCert (blobs : List (ℕ × ℕ)) (t5 : List T5Rec) : Certificate := ⟨[], [], [], [], linTab blobs, t5⟩

theorem hcov_linTab (blobs : List (ℕ × ℕ)) :
    ∀ cl ∈ linTab blobs, ∃ p ∈ blobs, (∀ i : Fin 3, cl.l i = fun a : Fin 5 => dg p.1 (11 + 5 * i.val + a.val)) ∧
      cl.ranges = (List.range (dg p.1 61).toNat).map fun j => (dg p.1 (62 + 2 * j), dg p.1 (63 + 2 * j)) := by
  intro cl hcl
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hcl
  exact ⟨p, hp, fun i => rfl, rfl⟩

/-- the `lines` clause for the certificate `lineCert blobs t5`: no hypothesis on the class table. -/
theorem lines_clause_tab (blobs : List (ℕ × ℕ)) (t5 : List T5Rec)
    (hok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true)
    (ht5 : ∀ r ∈ T5V, ∃ r' ∈ t5, r'.v = T5Vec r) :
    ∀ cl ∈ (lineCert blobs t5).t4, ∀ u : V5, Primitive u → (∀ i, u i ≠ 0) → (∀ i j, i ≠ j → |u i| ≠ |u j|) →
      InClass cl u → (∃ r ∈ (lineCert blobs t5).t5, ∃ g : SP, g.act u = r.v) ∨ 1 / 5 ≤ ML u :=
  lines_clause_R (lineCert blobs t5) blobs hok (hcov_linTab blobs) ht5

/-- decidable inclusion test: every residual tuple is a stored tuple of `vs`. -/
def t5Incl (vs : List (List ℕ)) : Bool := T5V.all fun r => vs.any fun s => s == r

theorem ht5_of_incl (t5 : List T5Rec) (vs : List (List ℕ)) (hv : t5.map T5Rec.v = vs.map T5Vec)
    (h : t5Incl vs = true) : ∀ r ∈ T5V, ∃ r' ∈ t5, r'.v = T5Vec r := by
  intro r hr
  unfold t5Incl at h
  rw [List.all_eq_true] at h
  obtain ⟨s, hs, hsr⟩ := List.any_eq_true.1 (h r hr)
  have hsr' : s = r := beq_iff_eq.1 hsr
  subst hsr'
  have hm : T5Vec s ∈ t5.map T5Rec.v := by rw [hv]; exact List.mem_map.2 ⟨s, hs, rfl⟩
  obtain ⟨r', hr', hr'v⟩ := List.mem_map.1 hm
  exact ⟨r', hr', hr'v⟩

#print axioms hcov_linTab
#print axioms lines_clause_tab
#print axioms ht5_of_incl

end Lin
end L5S4
end LRSpectrumFull
