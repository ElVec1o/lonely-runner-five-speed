/-
# L5S4.Window : E11, the leaf window as an integer range

`cert.rs::leaf_info` turns the rational window `lo ≤ μ_4² < hi` (`lo` non-strict, `hi` strict) into the integer range
`[⌈lo · G_3⌉, ⌈hi · G_3⌉ − 1]` for `|v|²`, using `|v|² = G_4 = μ_4² G_3`.

* `leadMinor_four`, `Dq3_eq`  `F.Dq 3 = |v|² / G_3` for a flag of a primitive `v`.
* `range_iff`                 `lo ≤ n/G < hi  ↔  ⌈lo G⌉ ≤ n ≤ ⌈hi G⌉ − 1` for `G > 0` (the `cdiv` of `leaf_info`).
* `window_range_iff`          the two combined: the window condition on `μ_4²` is the integer range for `|v|²`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.Chain
import LRSpectrumFull.L5S3.Accepted

namespace LRSpectrumFull
namespace L5S4

open Finset LRSpectrumFull.L5S3

theorem leadMinor_four (M : Matrix (Fin 4) (Fin 4) ℤ) : leadMinor M 4 = M.det := by
  unfold leadMinor
  congr 1
  ext a b
  simp [a.2, b.2]

theorem Dq3_eq {v : V5} (F : FlagData v) (hv : Primitive v) :
    F.Dq 3 = (dot v v : ℚ) / (leadMinor (gram F) 3 : ℚ) := by
  have h : F.Dq 3 = (leadMinor (gram F) 4 : ℚ) / (leadMinor (gram F) 3 : ℚ) := Dq_minors_thm v F 3
  rw [h, leadMinor_four, gram_det_eq_normsq F hv]

theorem range_iff (lo hi : ℚ) (G n : ℤ) (hG : 0 < G) :
    (lo ≤ (n : ℚ) / G ∧ (n : ℚ) / G < hi) ↔ (⌈lo * G⌉ ≤ n ∧ n ≤ ⌈hi * G⌉ - 1) := by
  have hGq : (0 : ℚ) < G := by exact_mod_cast hG
  rw [le_div_iff₀ hGq, div_lt_iff₀ hGq, Int.ceil_le]
  have : n ≤ ⌈hi * G⌉ - 1 ↔ n < ⌈hi * G⌉ := by omega
  rw [this, Int.lt_ceil]

theorem window_range_iff {v : V5} (F : FlagData v) (hv : Primitive v) (lo hi : ℚ) :
    (lo ≤ F.Dq 3 ∧ F.Dq 3 < hi) ↔
      (⌈lo * (leadMinor (gram F) 3 : ℚ)⌉ ≤ dot v v ∧
        dot v v ≤ ⌈hi * (leadMinor (gram F) 3 : ℚ)⌉ - 1) := by
  rw [Dq3_eq F hv]
  exact range_iff lo hi _ _ (leadMinor_pos' F 3)

end L5S4
end LRSpectrumFull
