/-
# L5S4.GD3K1 : the two generic lemmas of the depth-3 pipeline (stage S4 block 11)

* `a22_pos`       `0 < (FC3.ofNode n bn bd).a22` for EVERY `n : NodeW 2 3` (the first two vectors of the `K` basis are
                  linearly independent: they have a right inverse, so their Gram determinant is positive);
* `hrad_of_ok`    the radius hypothesis of `child_list_complete3`,
                  `radFrac (Cq 3) n.wit n.rows 2 n.rk = bn / bd`, for EVERY node, from the single Boolean `radOkN n bn bd`
                  (integer cross-multiplications of the three stage values `c_k`, `S_k` and the claimed fraction), which a
                  `decide +kernel` evaluates on the node's own data (witnesses of stages 1, 2 and the first two rows).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GD3S3
import LRSpectrumFull.L5S4.CheckChildRec

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## 1. `a22 > 0` for every node -/

theorem a22_pos (n : NodeW 2 3) (bn bd : ℤ) : 0 < (FC3.ofNode n bn bd).a22 := by
  have h := gF_pos_of_rinv (![n.b 0, n.b 1] : Fin 2 → V5) (![n.r 0, n.r 1] : Fin 2 → V5) (by
    intro i m
    fin_cases i <;> fin_cases m
    · simpa using n.id.br 0 0
    · simpa using n.id.br 0 1
    · simpa using n.id.br 1 0
    · simpa using n.id.br 1 1)
  unfold gF at h
  rw [Matrix.det_fin_two] at h
  have c := dot_comm' (n.b 1) (n.b 0)
  show 0 < gk n 0 0 * gk n 1 1 - gk n 0 1 * gk n 0 1
  simp only [gk]
  simpa [c] using h

/-! ## 2. The generic radius -/

/-- `den = 4 (m/w - 1/5)^2 - A/B` has the sign of `radN m w A B` and equals `radN / radD`. -/
def radN (m w A B : ℤ) : ℤ := 4 * (5 * m - w) ^ 2 * B - 25 * w ^ 2 * A
def radD (w B : ℤ) : ℤ := 25 * w ^ 2 * B

/-- the stage attains the claimed value `bn/bd = (7/3) / (N/D)`. -/
def stEq (N D bn bd : ℤ) : Bool := decide (0 < N) && decide (bn * 3 * N = 7 * D * bd)
/-- the stage is inactive (`N <= 0`) or does not undercut `bn/bd`. -/
def stLe (N D bn bd : ℤ) : Bool := decide (N ≤ 0) || decide (bn * 3 * N ≤ 7 * D * bd)

/-- Stage 0 has `c_0 = 1/2` and `S_0 = 1/G1 + G1/G2`; stage 1 has `S_1 = G1/G2`; stage 2 has `S_2 = 0`. -/
def radOk (m1 w1 m2 w2 G1 G2 bn bd : ℤ) : Bool :=
  decide (0 < bd) && decide (0 < G1) && decide (0 < G2) && decide (0 < w1) && decide (0 < w2) &&
  (stEq (radN 1 2 (G2 + G1 * G1) (G1 * G2)) (radD 2 (G1 * G2)) bn bd ||
    stEq (radN m1 w1 G1 G2) (radD w1 G2) bn bd || stEq (radN m2 w2 0 1) (radD w2 1) bn bd) &&
  stLe (radN 1 2 (G2 + G1 * G1) (G1 * G2)) (radD 2 (G1 * G2)) bn bd &&
  stLe (radN m1 w1 G1 G2) (radD w1 G2) bn bd && stLe (radN m2 w2 0 1) (radD w2 1) bn bd

/-- The Boolean on a node's own data (`G1 = |h_0|^2`, `G2 = Gram det of the first two rows`). -/
def radOkN (n : NodeW 2 3) (bn bd : ℤ) : Bool :=
  radOk (wMin (n.wit 1).1 (n.wit 1).2) (n.wit 1).2 (wMin (n.wit 2).1 (n.wit 2).2) (n.wit 2).2
    (dot (hN n.rows 0) (hN n.rows 0))
    (dot (hN n.rows 0) (hN n.rows 0) * dot (hN n.rows 1) (hN n.rows 1) -
      dot (hN n.rows 0) (hN n.rows 1) * dot (hN n.rows 1) (hN n.rows 0)) bn bd

theorem radD_pos (w B : ℤ) (hw : 0 < w) (hB : 0 < B) : 0 < radD w B := by
  unfold radD; positivity

theorem den_eq (m w A B : ℤ) (hw : 0 < w) (hB : 0 < B) :
    4 * (((m : ℤ) : ℚ) / ((w : ℤ) : ℚ) - 1 / 5) ^ 2 - ((A : ℤ) : ℚ) / ((B : ℤ) : ℚ) =
      ((radN m w A B : ℤ) : ℚ) / ((radD w B : ℤ) : ℚ) := by
  have hw' : (w : ℚ) ≠ 0 := by exact_mod_cast hw.ne'
  have hB' : (B : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  unfold radN radD
  push_cast
  field_simp
  ring

theorem stage_eq (den : ℚ) (N D bn bd : ℤ) (hden : den = (N : ℚ) / D) (hD : 0 < D) (hbd : 0 < bd)
    (h : stEq N D bn bd = true) : 0 < den ∧ (7 / 3 : ℚ) / den = (bn : ℚ) / bd := by
  unfold stEq at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hN, he⟩ := h
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hbq : (0 : ℚ) < bd := by exact_mod_cast hbd
  subst hden
  refine ⟨by positivity, ?_⟩
  have he' : (bn : ℚ) * 3 * N = 7 * D * bd := by exact_mod_cast he
  have hN0 : (N : ℚ) ≠ 0 := hNq.ne'
  have hD0 : (D : ℚ) ≠ 0 := hDq.ne'
  have hb0 : (bd : ℚ) ≠ 0 := hbq.ne'
  field_simp
  linarith

theorem stage_le (den : ℚ) (N D bn bd : ℤ) (hden : den = (N : ℚ) / D) (hD : 0 < D) (hbd : 0 < bd)
    (h : stLe N D bn bd = true) (hpos : 0 < den) : (bn : ℚ) / bd ≤ (7 / 3 : ℚ) / den := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hbq : (0 : ℚ) < bd := by exact_mod_cast hbd
  subst hden
  unfold stLe at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with hN | hle
  · exfalso
    have h1 : (N : ℚ) ≤ 0 := by exact_mod_cast hN
    have := div_nonpos_of_nonpos_of_nonneg h1 hDq.le
    linarith
  · have hNq : (0 : ℚ) < N := by
      by_contra hn
      push_neg at hn
      have := div_nonpos_of_nonpos_of_nonneg hn hDq.le
      linarith
    have hle' : (bn : ℚ) * 3 * N ≤ 7 * D * bd := by exact_mod_cast hle
    have hN0 : (N : ℚ) ≠ 0 := hNq.ne'
    have hD0 : (D : ℚ) ≠ 0 := hDq.ne'
    have key : (7 / 3 : ℚ) / ((N : ℚ) / D) = 7 * D / (3 * N) := by field_simp
    rw [key, div_le_div_iff₀ hbq (by positivity)]
    linarith

theorem Gm_two' (rw : Fin 4 → V5) :
    Gm rw 2 = dot (hN rw 0) (hN rw 0) * dot (hN rw 1) (hN rw 1) -
      dot (hN rw 0) (hN rw 1) * dot (hN rw 1) (hN rw 0) := by
  unfold Gm gF
  simp [Matrix.det_fin_two, rowsR]

/-- Core of the generic radius lemma over abstract integers. -/
theorem hrad_core (n : NodeW 2 3) (bn bd M1 W1 M2 W2 G1 G2 : ℤ)
    (hM1 : wMin (n.wit 1).1 (n.wit 1).2 = M1) (hW1 : (n.wit 1).2 = W1)
    (hM2 : wMin (n.wit 2).1 (n.wit 2).2 = M2) (hW2 : (n.wit 2).2 = W2)
    (hG1 : dot (hN n.rows 0) (hN n.rows 0) = G1)
    (hG2 : dot (hN n.rows 0) (hN n.rows 0) * dot (hN n.rows 1) (hN n.rows 1) -
      dot (hN n.rows 0) (hN n.rows 1) * dot (hN n.rows 1) (hN n.rows 0) = G2)
    (h : radOk M1 W1 M2 W2 G1 G2 bn bd = true) :
    radFrac (Cq (2 + 1)) n.wit n.rows 2 n.rk = (bn : ℚ) / bd := by
  unfold radOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hbd, hG1p⟩, hG2p⟩, hw1⟩, hw2⟩, hmem⟩, hle0⟩, hle1⟩, hle2⟩ := h
  have hGm1 : Gm n.rows 1 = G1 := by rw [Gm_one, hG1]
  have hGm2 : Gm n.rows 2 = G2 := by rw [Gm_two', hG2]
  have hG1q : (G1 : ℚ) ≠ 0 := by exact_mod_cast hG1p.ne'
  have hG2q : (G2 : ℚ) ≠ 0 := by exact_mod_cast hG2p.ne'
  have hc0 : cOf (n.wit 0) = ((1 : ℤ) : ℚ) / ((2 : ℤ) : ℚ) := by
    rw [n.w0]; simp [cOf, wMin]
  have hc1 : cOf (n.wit 1) = ((M1 : ℤ) : ℚ) / ((W1 : ℤ) : ℚ) := by
    unfold cOf; rw [hM1, hW1]
  have hc2 : cOf (n.wit 2) = ((M2 : ℤ) : ℚ) / ((W2 : ℤ) : ℚ) := by
    unfold cOf; rw [hM2, hW2]
  have s0 : SArr n.rows 2 0 = (((G2 + G1 * G1 : ℤ)) : ℚ) / ((G1 * G2 : ℤ) : ℚ) := by
    have : SArr n.rows 2 0 = (Gm n.rows 0 : ℚ) / (Gm n.rows 1 : ℚ) + (Gm n.rows 1 : ℚ) / (Gm n.rows 2 : ℚ) := by
      norm_num [SArr, Finset.sum_range_succ]
    rw [this, Gm_zero, hGm1, hGm2]
    push_cast
    field_simp
  have s1 : SArr n.rows 2 1 = ((G1 : ℤ) : ℚ) / ((G2 : ℤ) : ℚ) := by
    have : SArr n.rows 2 1 = (Gm n.rows 1 : ℚ) / (Gm n.rows 2 : ℚ) := by
      norm_num [SArr, Finset.sum_range_succ]
    rw [this, hGm1, hGm2]
  have s2 : SArr n.rows 2 2 = ((0 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) := by
    norm_num [SArr, Finset.sum_range_succ]
  have hB0 : 0 < G1 * G2 := mul_pos hG1p hG2p
  have d0 := den_eq 1 2 (G2 + G1 * G1) (G1 * G2) (by norm_num) hB0
  have d1 := den_eq M1 W1 G1 G2 hw1 hG2p
  have d2 := den_eq M2 W2 0 1 hw2 (by norm_num)
  rw [← hc0, ← s0] at d0
  rw [← hc1, ← s1] at d1
  rw [← hc2, ← s2] at d2
  have hD0 := radD_pos 2 (G1 * G2) (by norm_num) hB0
  have hD1 := radD_pos W1 G2 hw1 hG2p
  have hD2 := radD_pos W2 1 hw2 (by norm_num)
  have hC : Cq (2 + 1) = 7 / 3 := by norm_num [Cq, Finset.sum_range_succ]
  rw [hC]
  apply radFrac_eq_of
  · rcases hmem with (hm | hm) | hm
    · obtain ⟨hp, he⟩ := stage_eq _ _ _ bn bd d0 hD0 hbd hm
      exact ⟨0, by simp only [radSet, Finset.mem_filter, Finset.mem_range]; exact ⟨by norm_num, hp⟩, he⟩
    · obtain ⟨hp, he⟩ := stage_eq _ _ _ bn bd d1 hD1 hbd hm
      exact ⟨1, by simp only [radSet, Finset.mem_filter, Finset.mem_range]; exact ⟨by norm_num, hp⟩, he⟩
    · obtain ⟨hp, he⟩ := stage_eq _ _ _ bn bd d2 hD2 hbd hm
      exact ⟨2, by simp only [radSet, Finset.mem_filter, Finset.mem_range]; exact ⟨by norm_num, hp⟩, he⟩
  · intro k hk
    simp only [radSet, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hk3, hkp⟩ := hk
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact stage_le _ _ _ bn bd d0 hD0 hbd hle0 hkp
    · exact stage_le _ _ _ bn bd d1 hD1 hbd hle1 hkp
    · exact stage_le _ _ _ bn bd d2 hD2 hbd hle2 hkp

/-- **Generic radius lemma.**  For every node of depth 2, the Boolean `radOkN n bn bd` gives the hypothesis `hrad` of
`child_list_complete3`. -/
theorem hrad_of_ok (n : NodeW 2 3) (bn bd : ℤ) (h : radOkN n bn bd = true) :
    radFrac (Cq (2 + 1)) n.wit n.rows 2 n.rk = (bn : ℚ) / bd :=
  hrad_core n bn bd _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl h

end L5S4
end LRSpectrumFull
