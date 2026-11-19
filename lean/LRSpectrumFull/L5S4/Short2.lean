/-
# L5S4.Short2 : E8, second greedy test (`nd.j == 2`, `s_ij = g_00 g_ij − g_0i g_0j`, `exists_shorter(s, s_00)`)

`sMat F` is the `2×2` matrix of `lib.rs::greedy_ok` for the rows `h_0, h_1, h_2`; `exists_shorter` is `existsShorter`
of `Short.lean`.  The box inequality for a `2×2` matrix is an exact square identity (no positive-definiteness
hypothesis is needed besides `det > 0` and `s_ii ≥ 0`), and `det (sMat F) = g_00 · G_3 > 0`.

* `det_sMat`             `det (sMat F) = g_00 · gF (h_0, h_1, h_2)`.
* `shortestSecond_iff`   `ShortestSecond F ↔ ¬ existsShorter (sMat F) (s_00)`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.Short

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-- The `2×2` matrix `s` of `greedy_ok` (indices `1, 2` of the Gram matrix of `h_0, h_1, h_2`). -/
def sMat {v : V5} (F : FlagData v) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![sgm F 1 1, sgm F 1 2; sgm F 1 2, sgm F 2 2]

theorem det_sMat {v : V5} (F : FlagData v) :
    (sMat F).det = dot (hN F.h 0) (hN F.h 0) * gF (rowsF F 3) := by
  rw [gF_eq_det]
  have c10 := dot_comm' (hN F.h 1) (hN F.h 0)
  have c20 := dot_comm' (hN F.h 2) (hN F.h 0)
  have c21 := dot_comm' (hN F.h 2) (hN F.h 1)
  simp [Matrix.det_fin_two, Matrix.det_fin_three, sMat, gramM, rowsF, sgm, c10, c20, c21]
  ring

theorem sgm_diag_nonneg {v : V5} (F : FlagData v) (i : ℕ) : 0 ≤ sgm F i i := by
  unfold sgm
  have := dot_cs (hN F.h 0) (hN F.h i)
  nlinarith [dot_self_nonneg (hN F.h 0)]

theorem qf_sMat {v : V5} (F : FlagData v) (c : Fin 2 → ℤ) :
    qf (sMat F) c = c 0 * c 0 * sgm F 1 1 + 2 * c 0 * c 1 * sgm F 1 2 + c 1 * c 1 * sgm F 2 2 := by
  simp [qf, sMat, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem shortestSecond_iff {v : V5} (F : FlagData v) :
    ShortestSecond F ↔ ¬ existsShorter (sMat F) (sgm F 1 1) := by
  have g00 : 0 < dot (hN F.h 0) (hN F.h 0) := by
    have h := gF_rows_pos F 1 (by norm_num)
    simpa [gF_eq_det, gramM, rowsF, Matrix.det_unique] using h
  have hdet : 0 < (sMat F).det := by
    rw [det_sMat]; exact mul_pos g00 (gF_rows_pos F 3 (by norm_num))
  have hadj : ∀ i, 0 ≤ adjugate (sMat F) i i := by
    intro i
    fin_cases i
    · simp [Matrix.adjugate_fin_two, sMat]; exact sgm_diag_nonneg F 2
    · simp [Matrix.adjugate_fin_two, sMat]; exact sgm_diag_nonneg F 1
  have hbox : ∀ (c : Fin 2 → ℤ) (i : Fin 2),
      (c i) ^ 2 * (sMat F).det ≤ adjugate (sMat F) i i * qf (sMat F) c := by
    intro c i
    rw [qf_sMat]
    fin_cases i
    · simp [Matrix.adjugate_fin_two, Matrix.det_fin_two, sMat]
      nlinarith [sq_nonneg (sgm F 1 2 * c 0 + sgm F 2 2 * c 1)]
    · simp [Matrix.adjugate_fin_two, Matrix.det_fin_two, sMat]
      nlinarith [sq_nonneg (sgm F 1 1 * c 0 + sgm F 1 2 * c 1)]
  rw [existsShorter_iff _ _ hdet hadj hbox]
  unfold ShortestSecond
  constructor
  · intro h ⟨c, ⟨i, hi⟩, hlt⟩
    rw [qf_sMat] at hlt
    have := h (c 0) (c 1) (by
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi)
    linarith
  · intro h c1 c2 hc
    by_contra hlt
    push_neg at hlt
    apply h
    refine ⟨![c1, c2], ?_, ?_⟩
    · rcases hc with hc | hc
      · exact ⟨0, by simpa using hc⟩
      · exact ⟨1, by simpa using hc⟩
    · rw [qf_sMat]; simpa using hlt

end L5S4
end LRSpectrumFull
