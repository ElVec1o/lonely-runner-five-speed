/-
# L5S5.FinalGlue : the final assembly with the stored tuples, the lines clause on the records, and the class table = the concatenated local tables (stage S4T)

The class table of the final certificate is the concatenation `tab` of the per-rep local tables (the table the tree theorem `t3` is stated against), the residual tuples are
`T5Store.t5`.  Then
* registration of the local tables is definitional (`reg_cert`: `LocRegistered (cert tab) tab`);
* `ht5` and `hres` are theorems (`T5Store`);
* the lines clause for the 81,436 lines records is `glines` (from `Lin.lines_clause_all`, built from `LinRAll.ok`);
* what remains for `tab` is `hlines : forall cl in tab, LinesCl T5Store.t5 cl`, which for every rep with a `L5Reg.Reg<c>` module is a theorem (the local class is a signed-permutation
  image of a lines record, `L5Reg.Equiv`), see `L5Reg.RegFin`.
`five_speed_spectrum_glued` is the generic form: an arbitrary tree (`R2`, `t1`, `t2`, `t3` under registration) with table `tab`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S5.AggBlock
import LRSpectrumFull.L5S5.T5Store
import LRSpectrumFull.L5S4.LinRFinal
import LRSpectrumFull.L5Reg.Equiv

namespace LRSpectrumFull
namespace L5S5
namespace FinalGlue

open LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S4.Lin LRSpectrumFull.L5Reg

/-- the final certificate for the class table `tab` (all streams empty except `t4 = tab`, `t5 = T5Store.t5`). -/
def cert (tab : List T4Rec) : Certificate := ⟨[], [], [], [], tab, T5Store.t5⟩

theorem reg_cert (tab : List T4Rec) : LocRegistered (cert tab) tab :=
  fun cl h => ⟨cl, h, rfl, fun rg hrg => ⟨rg, hrg, le_rfl, le_rfl⟩⟩

/-- the lines clause for every one of the 81,436 lines records. -/
theorem glines : ∀ p ∈ LinRAll.blobs, LinesCl T5Store.t5 (t4OfRec p.1) := by
  intro p hp
  exact Lin.lines_clause_all T5Store.t5 T5Store.ht5 (t4OfRec p.1) (List.mem_map.2 ⟨p, hp, rfl⟩)

theorem five_speed_spectrum_glued {R1 : Set (NodeW 1 4)} {R2 : Set (NodeW 2 3)} (tab : List T4Rec)
    (t1 : ∀ h : V5, T1Ok h → ∃ n ∈ R1, hN n.rows 0 = h)
    (t2 : ∀ n ∈ R1, ∀ y : V5, ChildPass n y →
      ∃ (y' : V5) (n2 : NodeW 2 3), (∀ i, dot (n.b i) y' = dot (n.b i) y) ∧ n2.rows = setRow n.rows 1 y' ∧
        ∃ rep ∈ R2, ∃ (g : SP) (U U' : ℕ → ℕ → ℤ), Chain2Rel g n2.rows rep.rows U U')
    (t3 : ∀ C : Certificate, LocRegistered C tab → ∀ n ∈ R2, T3At C n)
    (hlines : ∀ cl ∈ tab, LinesCl T5Store.t5 cl)
    (v : Fin 5 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) (hlt : ML v < 1 / 5) :
    ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1) :=
  five_speed_spectrum_of_clauses (C := cert tab) t1 t2 (t3 _ (reg_cert tab)) (fun cl h => hlines cl h) T5Store.hres v hpos hinj hlt

#print axioms reg_cert
#print axioms glines
#print axioms five_speed_spectrum_glued

end FinalGlue
end L5S5
end LRSpectrumFull
