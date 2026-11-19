/-
# L5S3.Ratio34 : discharge of the `ratio34` field of `FlagGeometry`

For a flag `F : FlagData v` that is `Greedy`, `(3/4) Dq i ≤ Dq (i+1)` for `i = 0, 1, 2`.

Proof (size reduction): put `λ = L_{i+1,i}`, `c = round λ ∈ ℤ`, `u = h_{i+1} - c h_i ∈ Λ`.  The Gram
determinant of `(h_0..h_{i-1}, u)` equals `(D_0 ⋯ D_{i-1}) (D_{i+1} + (λ - c)² D_i)` (polynomial identity
in the LDL data), `u` is not in the rational span of `h_0..h_{i-1}` (independence of the rows, from the
LDL certificate), and `Greedy` compares it with `D_0 ⋯ D_i`.  Hence `D_i ≤ D_{i+1} + (1/4) D_i`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S3.Skeleton
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Round

namespace LRSpectrumFull
namespace L5S3

open Finset

theorem dot_comm' (a b : V5) : dot a b = dot b a := by
  unfold dot; apply Finset.sum_congr rfl; intro i _; ring

theorem dot_sub_smul (x y z : V5) (c : ℤ) :
    dot (fun k => x k - c * y k) z = dot x z - c * dot y z := by
  unfold dot
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]

/-- Rows of a flag with LDL certificate are linearly independent over `ℚ`. -/
theorem rows_indep {v : V5} (F : FlagData v) (α : Fin 4 → ℚ)
    (h : ∀ k : Fin 5, ∑ m, α m * (F.h m k : ℚ) = 0) : ∀ m, α m = 0 := by
  have hq : ∑ k : Fin 5, (∑ m, α m * (F.h m k : ℚ)) ^ 2 = 0 := by
    apply Finset.sum_eq_zero; intro k _; rw [h k]; norm_num
  have hGq : ∀ a b : Fin 4, ((dot (F.h a) (F.h b) : ℤ) : ℚ) = ∑ k, F.Lq a k * F.Dq k * F.Lq b k :=
    F.hLDL
  have l01 : F.Lq 0 1 = 0 := F.hLlow 0 1 (by decide)
  have l02 : F.Lq 0 2 = 0 := F.hLlow 0 2 (by decide)
  have l03 : F.Lq 0 3 = 0 := F.hLlow 0 3 (by decide)
  have l12 : F.Lq 1 2 = 0 := F.hLlow 1 2 (by decide)
  have l13 : F.Lq 1 3 = 0 := F.hLlow 1 3 (by decide)
  have l23 : F.Lq 2 3 = 0 := F.hLlow 2 3 (by decide)
  have u0 := F.hLunit 0
  have u1 := F.hLunit 1
  have u2 := F.hLunit 2
  have u3 := F.hLunit 3
  have hexp : ∑ k : Fin 5, (∑ m, α m * (F.h m k : ℚ)) ^ 2
      = ∑ l : Fin 4, F.Dq l * (∑ m, α m * F.Lq m l) ^ 2 := by
    have e : ∀ a b : Fin 4, ((∑ k : Fin 5, (F.h a k : ℚ) * F.h b k)) = ∑ k, F.Lq a k * F.Dq k * F.Lq b k := by
      intro a b
      have := hGq a b
      simp only [dot] at this
      push_cast at this
      exact this
    simp only [Fin.sum_univ_four] at e ⊢
    simp only [Fin.sum_univ_five] at e ⊢
    have e00 := e 0 0; have e01 := e 0 1; have e02 := e 0 2; have e03 := e 0 3
    have e11 := e 1 1; have e12 := e 1 2; have e13 := e 1 3
    have e22 := e 2 2; have e23 := e 2 3; have e33 := e 3 3
    simp only [Fin.sum_univ_four, Fin.sum_univ_five] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
    simp only [l01, l02, l03, l12, l13, l23, u0, u1, u2, u3] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33 ⊢
    linear_combination (α 0 * α 0) * e00 + (2 * α 0 * α 1) * e01 + (2 * α 0 * α 2) * e02
      + (2 * α 0 * α 3) * e03 + (α 1 * α 1) * e11 + (2 * α 1 * α 2) * e12 + (2 * α 1 * α 3) * e13
      + (α 2 * α 2) * e22 + (2 * α 2 * α 3) * e23 + (α 3 * α 3) * e33
  rw [hexp] at hq
  have hnn : ∀ l ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ F.Dq l * (∑ m, α m * F.Lq m l) ^ 2 :=
    fun l _ => mul_nonneg (F.hDpos l).le (sq_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hq
  have hb : ∀ l, ∑ m, α m * F.Lq m l = 0 := by
    intro l
    have := hz l (Finset.mem_univ l)
    have hD := F.hDpos l
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hD.ne'
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h1
  have b0 := hb 0; have b1 := hb 1; have b2 := hb 2; have b3 := hb 3
  simp only [Fin.sum_univ_four, l01, l02, l03, l12, l13, l23, u0, u1, u2, u3] at b0 b1 b2 b3
  have a3 : α 3 = 0 := by linarith
  have a2 : α 2 = 0 := by rw [a3] at b2; linarith
  have a1 : α 1 = 0 := by rw [a3, a2] at b1; linarith
  have a0 : α 0 = 0 := by rw [a3, a2, a1] at b0; linarith
  intro m
  fin_cases m <;> assumption

theorem dot_sub_smul' (x y z : V5) (c : ℤ) :
    dot x (fun k => y k - c * z k) = dot x y - c * dot x z := by
  rw [dot_comm', dot_sub_smul, dot_comm' y, dot_comm' z]

theorem gdl1 (x : V5) : gramDetList [x] = dot x x := by
  show (Matrix.of fun a b : Fin 1 => dot ([x].get a) ([x].get b)).det = _
  rw [Matrix.det_unique]; simp

theorem gdl2 (x y : V5) :
    gramDetList [x, y] = dot x x * dot y y - dot x y * dot y x := by
  show (Matrix.of fun a b : Fin 2 => dot ([x, y].get a) ([x, y].get b)).det = _
  rw [Matrix.det_fin_two]; simp

theorem gdl3 (x y z : V5) :
    gramDetList [x, y, z] = dot x x * dot y y * dot z z - dot x x * dot y z * dot z y
      - dot x y * dot y x * dot z z + dot x y * dot y z * dot z x
      + dot x z * dot y x * dot z y - dot x z * dot y y * dot z x := by
  show (Matrix.of fun a b : Fin 3 => dot ([x, y, z].get a) ([x, y, z].get b)).det = _
  rw [Matrix.det_fin_three]; simp

theorem dotq_exp {v : V5} (F : FlagData v) (a b : Fin 4) :
    ((dot (F.h a) (F.h b) : ℤ) : ℚ) = ∑ k, F.Lq a k * F.Dq k * F.Lq b k := F.hLDL a b

theorem u_dot_v {v : V5} (F : FlagData v) (a b : Fin 4) (c : ℤ) :
    dot (fun k => F.h a k - c * F.h b k) v = 0 := by
  rw [dot_sub_smul, F.hv a, F.hv b]; ring

theorem round_bd (l : ℚ) : (l - (round l : ℤ)) ^ 2 ≤ 1 / 4 := by
  have h := abs_sub_round l
  have h2 : |l - (round l : ℚ)| ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at h2; linarith

theorem ratio34_thm {v : V5} (F : FlagData v) (hg : Greedy v F.h) (i : Fin 3) :
    (3 / 4 : ℚ) * F.Dq i.castSucc ≤ F.Dq i.succ := by
  have l01 : F.Lq 0 1 = 0 := F.hLlow 0 1 (by decide)
  have l02 : F.Lq 0 2 = 0 := F.hLlow 0 2 (by decide)
  have l03 : F.Lq 0 3 = 0 := F.hLlow 0 3 (by decide)
  have l12 : F.Lq 1 2 = 0 := F.hLlow 1 2 (by decide)
  have l13 : F.Lq 1 3 = 0 := F.hLlow 1 3 (by decide)
  have l23 : F.Lq 2 3 = 0 := F.hLlow 2 3 (by decide)
  have u0 := F.hLunit 0
  have u1 := F.hLunit 1
  have u2 := F.hLunit 2
  have u3 := F.hLunit 3
  have d0 := F.hDpos 0
  have d1 := F.hDpos 1
  have d2 := F.hDpos 2
  have d3 := F.hDpos 3
  fin_cases i
  · -- i = 0 : D0, D1 ; lambda = L10
    set c : ℤ := round (F.Lq 1 0) with hc
    have hcb : (F.Lq 1 0 - c) ^ 2 ≤ 1 / 4 := round_bd _
    have hnot : ¬ InQSpanPrefix F.h 0 (fun k => F.h 1 k - c * F.h 0 k) := by
      rintro ⟨c', hc'⟩
      have := rows_indep F ![-(c : ℚ), 1, 0, 0] (fun k => by
        have h3 := hc' k
        simp [Fin.sum_univ_four] at h3 ⊢
        linarith) 1
      simp at this
    have hG := hg 0 (by norm_num) _ (u_dot_v F 1 0 c) hnot
    have hG' : gramDetList [F.h 0] ≤ gramDetList [fun k => F.h 1 k - c * F.h 0 k] := by
      simpa [List.ofFn_succ] using hG
    rw [gdl1, gdl1] at hG'
    have hG2 : ((dot (F.h 0) (F.h 0) : ℤ) : ℚ) ≤
        ((dot (fun k => F.h 1 k - c * F.h 0 k) (fun k => F.h 1 k - c * F.h 0 k) : ℤ) : ℚ) := by
      exact_mod_cast hG'
    simp only [dot_sub_smul, dot_sub_smul'] at hG2
    push_cast at hG2
    simp only [dotq_exp, Fin.sum_univ_four, l01, l02, l03, l12, l13, l23, u0, u1, u2, u3] at hG2
    show (3 / 4 : ℚ) * F.Dq 0 ≤ F.Dq 1
    nlinarith [mul_nonneg d0.le (sub_nonneg.mpr hcb)]
  · set c : ℤ := round (F.Lq 2 1) with hc
    have hcb : (F.Lq 2 1 - c) ^ 2 ≤ 1 / 4 := round_bd _
    have hnot : ¬ InQSpanPrefix F.h 1 (fun k => F.h 2 k - c * F.h 1 k) := by
      rintro ⟨c', hc'⟩
      have := rows_indep F ![-(c' 0), -(c : ℚ), 1, 0] (fun k => by
        have h3 := hc' k
        simp [Fin.sum_univ_four] at h3 ⊢
        linarith) 2
      simp at this
    have hG := hg 1 (by norm_num) _ (u_dot_v F 2 1 c) hnot
    have hG' : gramDetList [F.h 0, F.h 1] ≤ gramDetList [F.h 0, fun k => F.h 2 k - c * F.h 1 k] := by
      simpa [List.ofFn_succ] using hG
    have hA : ((gramDetList [F.h 0, F.h 1] : ℤ) : ℚ) = F.Dq 0 * F.Dq 1 := by
      rw [gdl2]; push_cast
      simp only [dotq_exp, Fin.sum_univ_four, l01, l02, l03, l12, l13, l23, u0, u1, u2, u3]
      ring
    have hB : ((gramDetList [F.h 0, fun k => F.h 2 k - c * F.h 1 k] : ℤ) : ℚ)
        = F.Dq 0 * (F.Dq 2 + (F.Lq 2 1 - c) ^ 2 * F.Dq 1) := by
      rw [gdl2]; simp only [dot_sub_smul, dot_sub_smul']; push_cast
      simp only [dotq_exp, Fin.sum_univ_four, l01, l02, l03, l12, l13, l23, u0, u1, u2, u3]
      ring
    have hle := (Int.cast_le (R := ℚ)).mpr hG'
    rw [hA, hB] at hle
    show (3 / 4 : ℚ) * F.Dq 1 ≤ F.Dq 2
    have h5 : 0 ≤ F.Dq 0 * (F.Dq 2 - 3 / 4 * F.Dq 1) := by
      nlinarith [mul_nonneg (mul_nonneg d0.le d1.le) (sub_nonneg.mpr hcb)]
    linarith [(mul_nonneg_iff_of_pos_left d0).mp h5]
  · set c : ℤ := round (F.Lq 3 2) with hc
    have hcb : (F.Lq 3 2 - c) ^ 2 ≤ 1 / 4 := round_bd _
    have hnot : ¬ InQSpanPrefix F.h 2 (fun k => F.h 3 k - c * F.h 2 k) := by
      rintro ⟨c', hc'⟩
      have := rows_indep F ![-(c' 0), -(c' 1), -(c : ℚ), 1] (fun k => by
        have h3 := hc' k
        simp [Fin.sum_univ_four] at h3 ⊢
        linarith) 3
      simp at this
    have hG := hg 2 (by norm_num) _ (u_dot_v F 3 2 c) hnot
    have hG' : gramDetList [F.h 0, F.h 1, F.h 2]
        ≤ gramDetList [F.h 0, F.h 1, fun k => F.h 3 k - c * F.h 2 k] := by
      simpa [List.ofFn_succ] using hG
    have hA : ((gramDetList [F.h 0, F.h 1, F.h 2] : ℤ) : ℚ) = F.Dq 0 * F.Dq 1 * F.Dq 2 := by
      rw [gdl3]; push_cast
      simp only [dotq_exp, Fin.sum_univ_four, l01, l02, l03, l12, l13, l23, u0, u1, u2, u3]
      ring
    have hB : ((gramDetList [F.h 0, F.h 1, fun k => F.h 3 k - c * F.h 2 k] : ℤ) : ℚ)
        = F.Dq 0 * F.Dq 1 * (F.Dq 3 + (F.Lq 3 2 - c) ^ 2 * F.Dq 2) := by
      rw [gdl3]; simp only [dot_sub_smul, dot_sub_smul']; push_cast
      simp only [dotq_exp, Fin.sum_univ_four, l01, l02, l03, l12, l13, l23, u0, u1, u2, u3]
      ring
    have hle := (Int.cast_le (R := ℚ)).mpr hG'
    rw [hA, hB] at hle
    show (3 / 4 : ℚ) * F.Dq 2 ≤ F.Dq 3
    have h5 : 0 ≤ F.Dq 0 * F.Dq 1 * (F.Dq 3 - 3 / 4 * F.Dq 2) := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg d0.le d1.le) d2.le) (sub_nonneg.mpr hcb)]
    linarith [(mul_nonneg_iff_of_pos_left (mul_pos d0 d1)).mp h5]

end L5S3
end LRSpectrumFull
