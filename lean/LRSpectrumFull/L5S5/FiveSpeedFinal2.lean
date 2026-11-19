/-
# L5S5.FiveSpeedFinal2 : `five_speed_spectrum2`, the five-speed spectrum over the generated aggregation with the reduced hypothesis list (stage S4T)

New module (the generated `FiveSpeedFinal` is untouched).  The hypotheses of `FiveSpeedFinal.FiveSpeedHyps` (`holes`, `C`, `reg`, `lines`, `hres`) shrink to
* `holes : Top.Holes`  the representatives without a built `GD3O<c>` module (each a named field),
* `hlines : forall cl in Top.topTab holes, LinesCl T5Store.t5 cl`  the lines clause for the concatenated local class tables.
`C` is `FinalGlue.cert (Top.topTab holes)`; `reg` is definitional; `hres`, `ht5` are `T5Store` theorems; the lines clause on the 81,436 records is `FinalGlue.glines`.
`hlines` is discharged, per built rep `c`, by `L5Reg.Reg<c>.lines` (instantiated in `L5Reg.RegFin`); the aggregation of these through the block tree (a mirror of `Top.block`) and the
`hlines` of the hole reps remain.

REQUIRES `AggFive.Top` to be built.  No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.AggFive.Top
import LRSpectrumFull.AggFive.Hl.Top
import LRSpectrumFull.L5S4.CheckT1
import LRSpectrumFull.L5S5.FinalGlue

namespace LRSpectrumFull
namespace L5S5

open LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S4.Lin LRSpectrumFull.AggFive LRSpectrumFull.L5Reg

structure FiveSpeedHyps2 where
  /-- H6/H7: the depth-2 representatives whose module is not built (leaf rollout driver; big-rep chain) -/
  holes : Top.Holes
  /-- H8': the lines hypotheses that remain after the tree aggregation `AggFive.Hl.Top` (S4V): one per hole representative and one per built representative without a `L5Reg.lines<c>` theorem -/
  hlines : Hl.Top.HLines holes

/-- **The five-speed spectrum, conditional on `FiveSpeedHyps2`.** -/
theorem five_speed_spectrum2 (hy : FiveSpeedHyps2) (v : Fin 5 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hlt : ML v < 1 / 5) : ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1) :=
  FinalGlue.five_speed_spectrum_glued (R1 := R1d1) (R2 := Top.R2 hy.holes) (Top.topTab hy.holes) d1_t1
    (fun n hn => Top.t2_top hy.holes n hn) (fun C hC => Top.top_t3 hy.holes C hC) (Hl.Top.lines_all hy.holes hy.hlines) v hpos hinj hlt

#print axioms five_speed_spectrum2

end L5S5
end LRSpectrumFull
