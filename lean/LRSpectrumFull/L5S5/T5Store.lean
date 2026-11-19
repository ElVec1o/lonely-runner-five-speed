/-
# L5S5.T5Store : the stored residual tuples (`T5`), `ht5` and `hres` as theorems (stage S4T)

`vs` is the stored tuple list: the 25 sorted residual tuples of the lines certificate (the tuples of `Lin.T5V`, emitted by `l5lines_emit`; `vs_eq` checks
the two copies agree).  `t5` is the stored record list: for every tuple one `T5Rec` with `v = T5Vec s`.  The other fields of a `T5Rec` (`kind, a, q, mln, mld`: extra
time and value of the unwitnessed line in the T5 stage of the Rust checker) are set to the constants `0, 0, 1, 0, 1`: no theorem reads them (`lines_clause_tab`,
`five_speed_spectrum_of_clauses` consume only `r.v`), so they are placeholders and NOT a verification of the T5 stage values.
`ht5` (the 25 tuples of `T5V` are among the stored records) follows from `ht5_of_incl` and the decidable test `t5Incl vs = true`; `hres` (every stored tuple is five distinct positive integers
at most 45) is decided on the 25 tuples.  Controls: a dropped tuple, a changed tuple, a repeated entry and an entry above 45 are rejected.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S5.FiveSpeedOfTree
import LRSpectrumFull.L5S4.LinRCov

namespace LRSpectrumFull
namespace L5S5
namespace T5Store

open LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S4.Lin

/-- the stored tuple list (25 sorted tuples). -/
def vs : List (List ℕ) := [
  [1, 2, 3, 4, 5], [1, 2, 3, 4, 10], [1, 2, 3, 5, 8], [1, 2, 13, 14, 15], [1, 3, 4, 5, 7],
  [1, 3, 4, 5, 9], [1, 3, 4, 5, 11], [1, 3, 4, 5, 18], [1, 3, 4, 5, 27], [1, 3, 4, 7, 10],
  [1, 3, 4, 7, 15], [1, 3, 4, 7, 20], [1, 3, 4, 7, 25], [1, 4, 5, 6, 7], [1, 4, 5, 6, 27],
  [1, 7, 8, 9, 15], [1, 13, 14, 15, 27], [1, 13, 14, 15, 29], [1, 17, 18, 19, 35], [2, 3, 5, 8, 19],
  [2, 5, 7, 8, 9], [3, 5, 8, 9, 13], [3, 5, 8, 11, 13], [3, 7, 10, 13, 23], [5, 13, 18, 23, 31]]

theorem vs_eq : vs = T5V := by decide +kernel

theorem vs_len : vs.length = 25 := by decide +kernel

/-- the stored `T5` records (only `v` is meaningful, see the header). -/
def t5 : List T5Rec := vs.map fun s => ⟨T5Vec s, 0, 0, 1, 0, 1⟩

theorem t5_v : t5.map T5Rec.v = vs.map T5Vec := by
  simp [t5, List.map_map, Function.comp_def]

theorem incl : t5Incl vs = true := by decide +kernel

/-- **H3 (`ht5`) as a theorem**: the 25 residual tuples are among the stored records. -/
theorem ht5 : ∀ r ∈ T5V, ∃ r' ∈ t5, r'.v = T5Vec r := ht5_of_incl t5 vs t5_v incl

theorem resOK_vs : ∀ s ∈ vs, ResOK (T5Vec s) := by
  unfold ResOK
  decide +kernel

/-- **H3 (`hres`) as a theorem**: every stored residual tuple consists of five distinct positive integers at most 45. -/
theorem hres : ∀ r ∈ t5, ResOK r.v := by
  intro r hr
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
  exact resOK_vs s hs

/-! ### controls -/

theorem ctl_drop_first : t5Incl (vs.drop 1) = false := by decide +kernel
theorem ctl_drop_last : t5Incl (vs.take 24) = false := by decide +kernel
theorem ctl_drop_middle : t5Incl (vs.eraseIdx 12) = false := by decide +kernel
theorem ctl_change : t5Incl (vs.map fun s => if s = [1, 3, 4, 5, 27] then [1, 3, 4, 5, 28] else s) = false := by decide +kernel
theorem ctl_dup_entry : ¬ ResOK (T5Vec [1, 1, 2, 3, 4]) := by unfold ResOK; decide +kernel
theorem ctl_big_entry : ¬ ResOK (T5Vec [1, 2, 3, 4, 46]) := by unfold ResOK; decide +kernel
theorem ctl_zero_entry : ¬ ResOK (T5Vec [0, 1, 2, 3, 4]) := by unfold ResOK; decide +kernel

#print axioms vs_eq
#print axioms ht5
#print axioms hres
#print axioms ctl_drop_first
#print axioms ctl_big_entry

end T5Store
end L5S5
end LRSpectrumFull
