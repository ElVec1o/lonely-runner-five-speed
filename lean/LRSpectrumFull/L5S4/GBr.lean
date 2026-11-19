/-
# L5S4.GBr : soundness bridge of the packed-Nat flat record check (stage S4 block 8)

`recFactsG_sound` : `recFactsG (FC.ofCtx (ctxOf n bn bd)) g = true` and `r.getD k 0 = g k` (`k < 64`) give `RecFacts n r`.
`d2Ok_of_G`       : `recClassG f g z = true` gives `d2Ok` of the class record `[h, y] -> [h, y']` (rows of the record and of
                    the representative; `y'` is read from `z`, the digit function of the representative's row).
Both are for ARBITRARY digit functions, so they serve the old format (representative looked up by index) and the new one.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GBrDef
import LRSpectrumFull.L5S4.CheckChildRec

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

set_option maxRecDepth 100000

theorem recFactsG_eq (f : FC) (r : ℕ) : recFactsN f r = recFactsG f (dgI r) := rfl

/-! ## 1. Small lemmas -/

theorem gcdOne_of_gcdF (t : Fin 4 → ℤ) (h : gcdF (t 0) (t 1) (t 2) (t 3) = true) : GcdOne t := by
  unfold GcdOne
  have hd : ∀ i, Finset.univ.gcd t ∣ t i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
  have hn : ∀ i, (Finset.univ.gcd t).natAbs ∣ (t i).natAbs := fun i => Int.natAbs_dvd_natAbs.2 (hd i)
  unfold gcdF at h
  have hg := Nat.eq_of_beq_eq_true h
  have h1 : (Finset.univ.gcd t).natAbs ∣ 1 := by
    rw [← hg]
    exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (hn 0) (hn 1)) (hn 2)) (hn 3)
  have h2 : (Finset.univ.gcd t).natAbs = 1 := Nat.dvd_one.1 h1
  have h3 : (0 : ℤ) ≤ Finset.univ.gcd t := Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
  omega

theorem wm5N_le (X : V5) (W : ℤ) : wm5N (X 0) (X 1) (X 2) (X 3) (X 4) W ≤ wMin X W := by
  unfold wMin
  apply Finset.le_inf'
  intro a _
  fin_cases a <;> simp [wm5N, mm1N, min_le_iff]

theorem sel5_gen (x : V5) : ∀ (s : ℕ) (hs : s < 5), sel5N (x 0) (x 1) (x 2) (x 3) (x 4) s = x ⟨s, hs⟩
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem sel5_mod (x : V5) (m : ℤ) :
    sel5N (x 0) (x 1) (x 2) (x 3) (x 4) (m.toNat % 5) = x ⟨m.toNat % 5, Nat.mod_lt _ (by norm_num)⟩ :=
  sel5_gen x _ _

theorem sel5_modg (g : ℕ → ℤ) (m : ℤ) : sel5N (g 4) (g 5) (g 6) (g 7) (g 8) (m.toNat % 5) = g (4 + m.toNat % 5) := by
  have := sel5_gen (fun i => g (4 + i.val)) (m.toNat % 5) (Nat.mod_lt _ (by norm_num))
  simpa using this

/-! ## 2. Record facts -/

theorem recFactsG_sound (n : NodeW 1 4) (bn bd : ℤ) (r : List ℤ) (g : ℕ → ℤ)
    (hr : ∀ k, k < 64 → r.getD k 0 = g k)
    (h : recFactsG (FC.ofCtx (ctxOf n bn bd)) g = true) : RecFacts n r := by
  simp only [recFactsG, FC.ofCtx, ctxOf, Bool.and_eq_true, decide_eq_true_eq, and_assoc, d5N] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24⟩ := h
  have hr' := hr
  have hr2 : ∀ k, k < 64 → r[k]?.getD 0 = g k := fun k hk => by rw [← hr k hk]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [dot, Fin.sum_univ_five, cY, cv, recT, hr', hr2]
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · have ht : recT r = ![g 0, g 1, g 2, g 3] := by simp [recT, hr', hr2]
    rw [ht]
    exact gcdOne_of_gcdF _ (by simpa using h5)
  · intro i
    fin_cases i
    · exact ⟨by simp [dot, Fin.sum_univ_five, cB, cv, hr', hr2]; linarith [h6], by simp [dot, Fin.sum_univ_five, cB, cv, cY, hr', hr2]; linarith [h7]⟩
    · exact ⟨by simp [dot, Fin.sum_univ_five, cB, cv, hr', hr2]; linarith [h8], by simp [dot, Fin.sum_univ_five, cB, cv, cY, hr', hr2]; linarith [h9]⟩
    · exact ⟨by simp [dot, Fin.sum_univ_five, cB, cv, hr', hr2]; linarith [h10], by simp [dot, Fin.sum_univ_five, cB, cv, cY, hr', hr2]; linarith [h11]⟩
  · intro i k
    fin_cases i <;> fin_cases k <;> simp [dot, Fin.sum_univ_five, cB, cR, cv, hr', hr2] <;>
      first | linarith [h12] | linarith [h13] | linarith [h14] | linarith [h15] | linarith [h16] |
        linarith [h17] | linarith [h18] | linarith [h19] | linarith [h20]
  · simpa [cW, hr', hr2] using h21
  · simpa [dot, Fin.sum_univ_five, cW, cX, cv, hr', hr2] using h22
  · simpa [dot, Fin.sum_univ_five, cW, cX, cY, cv, hr', hr2] using h23
  · have hw := wm5N_le (cX r) (cW r)
    have ew : cW r = g 44 := by simp [cW, hr', hr2]
    have e0 : cX r 0 = g 39 := by simp [cX, cv, hr', hr2]
    have e1 : cX r 1 = g 40 := by simp [cX, cv, hr', hr2]
    have e2 : cX r 2 = g 41 := by simp [cX, cv, hr', hr2]
    have e3 : cX r 3 = g 42 := by simp [cX, cv, hr', hr2]
    have e4 : cX r 4 = g 43 := by simp [cX, cv, hr', hr2]
    rw [e0, e1, e2, e3, e4] at hw
    rw [ew] at hw ⊢
    linarith [h24, hw]

end L5S4
end LRSpectrumFull
