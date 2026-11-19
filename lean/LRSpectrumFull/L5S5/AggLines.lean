/-
# L5S5.AggLines : the lines clause carried by the block tree (stage S4V, the `hlines` mirror)

`Good t5 B` says that every class of the concatenated local table `B.tab` of the block `B` has the lines clause.  It is preserved by `RBlock.append` (the table is `B1.tab ++ B2.tab`) and holds for
`RBlock.single` / `RepData.blk` as soon as it holds for the local table.  The generated modules `AggFive.Hl.<Name>` repeat the term shape of each generated `block` with these combinators
(side conditions of `append` are left to unification with the unfolded `block`), so that the lines clause of `Top.topTab` follows from one lines hypothesis per built rep without a `Reg<c>` module
and per hole representative.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S5.AggBlock
import LRSpectrumFull.L5S5.T5Store
import LRSpectrumFull.L5Reg.Equiv

namespace LRSpectrumFull
namespace L5S5

open LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5Reg

/-- every class of the concatenated local table of the block has the lines clause -/
def Good {ρ : Type} {rowsOf : NodeW 2 3 → ρ} {E : ℕ → ρ} (t5 : List T5Rec) (B : RBlock rowsOf E) : Prop :=
  ∀ cl ∈ B.tab, LinesCl t5 cl

/-- a block that is a single representative (or a blk): the lines clause of its table, up to unfolding -/
theorem good_of_tab {ρ : Type} {rowsOf : NodeW 2 3 → ρ} {E : ℕ → ρ} {t5 : List T5Rec} {B : RBlock rowsOf E}
    (hg : ∀ cl ∈ B.tab, LinesCl t5 cl) : Good t5 B := hg

theorem good_single{ρ : Type} {rowsOf : NodeW 2 3 → ρ} {E : ℕ → ρ} {t5 : List T5Rec} {pos : ℕ} {n : NodeW 2 3} {tab : List T4Rec}
    {h : ∀ C : Certificate, LocRegistered C tab → T3At C n} {hl : rowsOf n = E pos}
    (hg : ∀ cl ∈ tab, LinesCl t5 cl) : Good t5 (RBlock.single pos n tab h hl) := hg

theorem good_blk {ρ : Type} {rowsOf : NodeW 2 3 → ρ} {E : ℕ → ρ} {t5 : List T5Rec} {pos : ℕ} {r : RepData rowsOf E pos}
    (hg : ∀ cl ∈ r.tab, LinesCl t5 cl) : Good t5 r.blk := hg

theorem good_append {ρ : Type} {rowsOf : NodeW 2 3 → ρ} {E : ℕ → ρ} {t5 : List T5Rec} {B1 B2 : RBlock rowsOf E}
    (h1 : Good t5 B1) (h2 : Good t5 B2) (hp : B2.pos0 = B1.pos0 + B1.size) : Good t5 (RBlock.append B1 B2 hp) := by
  intro cl hcl
  rcases List.mem_append.1 hcl with h | h
  · exact h1 cl h
  · exact h2 cl h

#print axioms good_single
#print axioms good_blk
#print axioms good_append

end L5S5
end LRSpectrumFull
