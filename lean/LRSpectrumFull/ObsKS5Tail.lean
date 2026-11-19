/-
# KS5 tail: lines on the two critical tori at n = 5

Formalisation of Lemma H ("tent plus floor"), Proposition U, Lemma W, Lemmas N and P and
the critical-lines theorem of the accompanying paper (the constant is `D(5/11) = 3/55`).

Loneliness is the project's `ML` of `MaxLoneliness.lean` (`ML v = sSup_t gap v t`,
`gap v t = min_i ‖v_i t‖`), speeds `Fin 5 → ℤ`.  Write `D(t) = dist(t, (1/5)ℤ) = ‖5t‖/5`.

* Lemma H:  for `V = (1,2,3,4)` and `V = (1,3,4,7)`,
  `gap V t ≤ max (1/5 - ‖5t‖/5) p` with `p = 1/7`, resp. `2/11`.
* Prop. U:  `ML (V, 5s) ≤ max (s/(5s+1)) p`.
* Lemma W:  `s/(5s+1) ≤ ML (V, 5s)` (`s ≥ 1`), and `2/11 ≤ ML (1,3,4,7,5)`.
* Lemma N:  `1/5 ≤ ML (v₁..v₄, B)` when `5 ∤ vᵢ`, `5 ∤ B`.
* Lemma P:  `1/5 ≤ ML (A v₁, .., A v₄, B)` when `A ≥ 2`, `IsCoprime A B`, `5 ∤ vᵢ`.
* Theorem 1: assembly.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.DValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Coprime.Basic

namespace LRSpectrumFull
namespace KS5Tail

/-! ## Section 1: Lemma H (tent plus floor) -/

/-- `max (1/5 - D(t)) p` with `D(t) = ‖5t‖/5` the distance from `t` to `(1/5)ℤ`. -/
noncomputable def tentBound (p t : ℝ) : ℝ := max (1 / 5 - nearestIntDist (5 * t) / 5) p

/-- Some one of four runners is within `tentBound p t` of the integers. -/
def HProp (a b c d : ℤ) (p t : ℝ) : Prop :=
  nearestIntDist ((a : ℝ) * t) ≤ tentBound p t ∨ nearestIntDist ((b : ℝ) * t) ≤ tentBound p t ∨
  nearestIntDist ((c : ℝ) * t) ≤ tentBound p t ∨ nearestIntDist ((d : ℝ) * t) ≤ tentBound p t

theorem nd_zmul_add_int (k n : ℤ) (t : ℝ) :
    nearestIntDist ((k : ℝ) * (t + n)) = nearestIntDist ((k : ℝ) * t) := by
  have h : (k : ℝ) * (t + n) = (k : ℝ) * t + ((k * n : ℤ) : ℝ) := by push_cast; ring
  rw [h, nearestIntDist_add_int]

theorem nd_five_add_int (n : ℤ) (t : ℝ) :
    nearestIntDist (5 * (t + n)) = nearestIntDist (5 * t) := by
  have h : (5 : ℝ) * (t + n) = 5 * t + ((5 * n : ℤ) : ℝ) := by push_cast; ring
  rw [h, nearestIntDist_add_int]

theorem HProp_add_int (a b c d : ℤ) (p t : ℝ) (n : ℤ) :
    HProp a b c d p (t + n) ↔ HProp a b c d p t := by
  unfold HProp tentBound
  rw [nd_zmul_add_int a, nd_zmul_add_int b, nd_zmul_add_int c, nd_zmul_add_int d,
    nd_five_add_int]

theorem HProp_neg (a b c d : ℤ) (p t : ℝ) :
    HProp a b c d p (-t) ↔ HProp a b c d p t := by
  unfold HProp tentBound
  simp only [mul_neg, nearestIntDist_neg]

/-- Reduction of a statement for all `t` to `t ∈ [0, 1/2]` (period one and evenness). -/
theorem HProp_all (a b c d : ℤ) (p : ℝ)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → HProp a b c d p t) : ∀ t, HProp a b c d p t := by
  intro t
  have ht : t = Int.fract t + ((⌊t⌋ : ℤ) : ℝ) := by linarith [Int.floor_add_fract t]
  rw [ht, HProp_add_int]
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  rcases le_total (Int.fract t) (1 / 2) with hs | hs
  · exact h _ h0 hs
  · have e : -(Int.fract t) = (1 - Int.fract t) + (((-1 : ℤ)) : ℝ) := by push_cast; ring
    rw [← HProp_neg a b c d p (Int.fract t), e, HProp_add_int]
    exact h _ (by linarith) (by linarith)

/-- Tent case: runner `v` near the integer `n`, with `m/5` the fifth used for `D`. -/
theorem tent_le (t : ℝ) (v n m : ℤ) {p : ℝ}
    (h1 : (v : ℝ) * t - n ≤ 1 / 5 - (5 * t - m) / 5)
    (h2 : (v : ℝ) * t - n ≤ 1 / 5 + (5 * t - m) / 5)
    (h3 : -((v : ℝ) * t - n) ≤ 1 / 5 - (5 * t - m) / 5)
    (h4 : -((v : ℝ) * t - n) ≤ 1 / 5 + (5 * t - m) / 5) :
    nearestIntDist ((v : ℝ) * t) ≤ tentBound p t := by
  have e1 := nearestIntDist_le_dist ((v : ℝ) * t) n
  have e2 := nearestIntDist_le_dist (5 * t) m
  have hs : |(v : ℝ) * t - n| ≤ 1 / 5 - |5 * t - (m : ℝ)| / 5 := by
    rcases abs_cases ((v : ℝ) * t - n) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
    rcases abs_cases (5 * t - (m : ℝ)) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
    rw [ha, hb] <;> linarith
  unfold tentBound
  exact le_trans (le_trans e1 hs) (le_trans (by linarith) (le_max_left _ _))

/-- Floor case: runner `v` within `p` of the integer `n`. -/
theorem floor_le (t : ℝ) (v n : ℤ) {p : ℝ}
    (h1 : (v : ℝ) * t - n ≤ p) (h2 : -((v : ℝ) * t - n) ≤ p) :
    nearestIntDist ((v : ℝ) * t) ≤ tentBound p t := by
  have e1 := nearestIntDist_le_dist ((v : ℝ) * t) n
  unfold tentBound
  exact le_trans (le_trans e1 (abs_le.mpr ⟨by linarith, h1⟩)) (le_max_right _ _)

macro "tent_tac" : tactic => `(tactic| (push_cast; linarith))

/-- The fine case analysis for `V = (1,2,3,4)`, `p = 1/7` (six intervals on `[0,1/2]`
plus the split of the first). -/
theorem HProp_V1 : ∀ t, HProp 1 2 3 4 (1 / 7) t := by
  apply HProp_all
  intro t h0 h1
  unfold HProp
  rcases le_total t (1 / 10) with a | a
  · exact Or.inl (tent_le t 1 0 0 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac))
  rcases le_total t (1 / 5) with b | b
  · exact Or.inl (tent_le t 1 0 1 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac))
  rcases le_total t (1 / 4) with c | c
  · exact Or.inr (Or.inr (Or.inr
      (tent_le t 4 1 1 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac))))
  rcases le_total t (2 / 7) with d | d
  · exact Or.inr (Or.inr (Or.inr (floor_le t 4 1 (by tent_tac) (by tent_tac))))
  rcases le_total t (1 / 3) with e | e
  · exact Or.inr (Or.inr (Or.inl (floor_le t 3 1 (by tent_tac) (by tent_tac))))
  rcases le_total t (2 / 5) with f | f
  · exact Or.inr (Or.inr (Or.inl
      (tent_le t 3 1 2 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac))))
  · exact Or.inr (Or.inl (tent_le t 2 1 2 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac)))

/-- The fine case analysis for `V = (1,3,4,7)`, `p = 2/11`. -/
theorem HProp_V2 : ∀ t, HProp 1 3 4 7 (2 / 11) t := by
  apply HProp_all
  intro t h0 h1
  unfold HProp
  rcases le_total t (1 / 10) with a | a
  · exact Or.inl (tent_le t 1 0 0 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac))
  rcases le_total t (1 / 5) with b | b
  · exact Or.inl (tent_le t 1 0 1 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac))
  rcases le_total t (1 / 4) with c | c
  · exact Or.inr (Or.inr (Or.inl
      (tent_le t 4 1 1 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac))))
  rcases le_total t (7 / 25) with d | d
  · exact Or.inr (Or.inr (Or.inl
      (tent_le t 4 1 1 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac))))
  rcases le_total t (2 / 7) with e | e
  · exact Or.inr (Or.inr (Or.inr
      (tent_le t 7 2 1 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac))))
  rcases le_total t (3 / 10) with f | f
  · exact Or.inr (Or.inr (Or.inr
      (tent_le t 7 2 1 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac))))
  rcases le_total t (1 / 3) with g | g
  · exact Or.inr (Or.inl (tent_le t 3 1 2 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac)))
  rcases le_total t (2 / 5) with i | i
  · exact Or.inr (Or.inl (tent_le t 3 1 2 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac)))
  rcases le_total t (3 / 7) with j | j
  · exact Or.inr (Or.inr (Or.inr
      (tent_le t 7 3 2 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac))))
  rcases le_total t (5 / 11) with k | k
  · exact Or.inr (Or.inr (Or.inr (floor_le t 7 3 (by tent_tac) (by tent_tac))))
  rcases le_total t (7 / 15) with l | l
  · exact Or.inr (Or.inr (Or.inl (floor_le t 4 2 (by tent_tac) (by tent_tac))))
  · exact Or.inr (Or.inr (Or.inl
      (tent_le t 4 2 2 (by tent_tac) (by tent_tac) (by tent_tac) (by tent_tac))))

theorem gap4_le_tent {a b c d : ℤ} {p t : ℝ} (h : HProp a b c d p t) :
    gap (![a, b, c, d] : Fin 4 → ℤ) t ≤ tentBound p t := by
  rcases h with h | h | h | h
  · exact (gap_le (![a, b, c, d] : Fin 4 → ℤ) t 0).trans h
  · exact (gap_le (![a, b, c, d] : Fin 4 → ℤ) t 1).trans h
  · exact (gap_le (![a, b, c, d] : Fin 4 → ℤ) t 2).trans h
  · exact (gap_le (![a, b, c, d] : Fin 4 → ℤ) t 3).trans h

/-- **Lemma H for `V = (1,2,3,4)`**: `min_i ‖t v_i‖ ≤ max (1/5 - dist(t,(1/5)ℤ)) (1/7)`. -/
theorem lemmaH_V1 (t : ℝ) :
    gap (![1, 2, 3, 4] : Fin 4 → ℤ) t ≤ max (1 / 5 - nearestIntDist (5 * t) / 5) (1 / 7) :=
  gap4_le_tent (HProp_V1 t)

/-- **Lemma H for `V = (1,3,4,7)`**: `min_i ‖t v_i‖ ≤ max (1/5 - dist(t,(1/5)ℤ)) (2/11)`. -/
theorem lemmaH_V2 (t : ℝ) :
    gap (![1, 3, 4, 7] : Fin 4 → ℤ) t ≤ max (1 / 5 - nearestIntDist (5 * t) / 5) (2 / 11) :=
  gap4_le_tent (HProp_V2 t)

/-! ## Section 2: Proposition U (upper bound) -/

theorem gap5_le_tent {a b c d e : ℤ} {p t : ℝ} (h : HProp a b c d p t) :
    gap (![a, b, c, d, e] : Fin 5 → ℤ) t ≤ tentBound p t := by
  rcases h with h | h | h | h
  · exact (gap_le (![a, b, c, d, e] : Fin 5 → ℤ) t 0).trans h
  · exact (gap_le (![a, b, c, d, e] : Fin 5 → ℤ) t 1).trans h
  · exact (gap_le (![a, b, c, d, e] : Fin 5 → ℤ) t 2).trans h
  · exact (gap_le (![a, b, c, d, e] : Fin 5 → ℤ) t 3).trans h

/-- `‖s x‖ ≤ s ‖x‖` for a natural number `s`. -/
theorem nd_nat_mul_le (s : ℕ) (x : ℝ) :
    nearestIntDist ((s : ℝ) * x) ≤ s * nearestIntDist x := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hf := Int.floor_add_fract x
  rcases min_choice (Int.fract x) (1 - Int.fract x) with h | h
  · have e : nearestIntDist x = Int.fract x := h
    rw [e]
    have := nearestIntDist_le_dist ((s : ℝ) * x) ((s : ℤ) * ⌊x⌋)
    have h2 : |(s : ℝ) * x - (((s : ℤ) * ⌊x⌋ : ℤ) : ℝ)| = s * Int.fract x := by
      rw [abs_of_nonneg]
      · push_cast; nlinarith [hf]
      · push_cast
        have := Int.fract_nonneg x
        nlinarith [hf]
    linarith
  · have e : nearestIntDist x = 1 - Int.fract x := h
    rw [e]
    have := nearestIntDist_le_dist ((s : ℝ) * x) ((s : ℤ) * (⌊x⌋ + 1))
    have h1 := Int.fract_lt_one x
    have h2 : |(s : ℝ) * x - (((s : ℤ) * (⌊x⌋ + 1) : ℤ) : ℝ)| = s * (1 - Int.fract x) := by
      rw [abs_of_nonpos]
      · push_cast; nlinarith [hf]
      · push_cast
        nlinarith [hf]
    linarith

/-- **Proposition U.**  If `HProp a b c d p` holds for all `t`, then
`ML (a,b,c,d,5s) ≤ max (s/(5s+1)) p`. -/
theorem ML_le_of_tent (a b c d : ℤ) (p : ℝ) (s : ℕ) (hs : 1 ≤ s)
    (hH : ∀ t, HProp a b c d p t) :
    ML (![a, b, c, d, 5 * (s : ℤ)] : Fin 5 → ℤ) ≤ max ((s : ℝ) / (5 * s + 1)) p := by
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hpos : (0 : ℝ) < 5 * s + 1 := by linarith
  unfold ML
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨t, rfl⟩
  have hd1 : (s : ℝ) / (5 * s + 1) ≤ max ((s : ℝ) / (5 * s + 1)) p := le_max_left _ _
  have hd2 : p ≤ max ((s : ℝ) / (5 * s + 1)) p := le_max_right _ _
  have hd1' : (s : ℝ) ≤ max ((s : ℝ) / (5 * s + 1)) p * (5 * s + 1) :=
    (div_le_iff₀ hpos).mp hd1
  set d' := max ((s : ℝ) / (5 * s + 1)) p with hd'
  set u := nearestIntDist (5 * t) with hu
  by_cases hcase : (s : ℝ) * u ≤ d'
  · have h5 : gap (![a, b, c, d, 5 * (s : ℤ)] : Fin 5 → ℤ) t
        ≤ nearestIntDist ((((5 * (s : ℤ) : ℤ)) : ℝ) * t) :=
      gap_le (![a, b, c, d, 5 * (s : ℤ)] : Fin 5 → ℤ) t 4
    have h6 : nearestIntDist ((((5 * (s : ℤ) : ℤ)) : ℝ) * t) ≤ s * u := by
      have := nd_nat_mul_le s (5 * t)
      have e : (((5 * (s : ℤ) : ℤ)) : ℝ) * t = (s : ℝ) * (5 * t) := by push_cast; ring
      rw [e]; exact this
    linarith
  · rw [not_le] at hcase
    have hB : tentBound p t ≤ d' := by
      unfold tentBound
      apply max_le _ hd2
      have key : (s : ℝ) * (1 - u) ≤ (s : ℝ) * (5 * d') := by nlinarith
      have := le_of_mul_le_mul_left key (by linarith)
      linarith
    exact (gap5_le_tent (hH t)).trans hB

/-! ## Section 3: Lemma W (witnesses) -/

theorem nd_ge_shift {x c : ℝ} (n : ℤ) (h0 : 0 ≤ x - n) (h1 : x - n < 1) (hc0 : c ≤ x - n)
    (hc1 : c ≤ 1 - (x - n)) : c ≤ nearestIntDist x := by
  have e : nearestIntDist x = nearestIntDist (x - n) := by
    have := nearestIntDist_add_int (x - n) n
    rwa [sub_add_cancel] at this
  rw [e]
  exact nearestIntDist_ge h0 h1 hc0 hc1

theorem ML_ge_of_witness' {k : ℕ} (v : Fin (k + 1) → ℤ) (t c : ℝ)
    (h : ∀ i, c ≤ nearestIntDist ((v i : ℝ) * t)) : c ≤ ML v :=
  (le_gap v t c h).trans (gap_le_ML v t)

theorem ML_ge_five (a b c d e : ℤ) (t x : ℝ)
    (h0 : x ≤ nearestIntDist ((a : ℝ) * t)) (h1 : x ≤ nearestIntDist ((b : ℝ) * t))
    (h2 : x ≤ nearestIntDist ((c : ℝ) * t)) (h3 : x ≤ nearestIntDist ((d : ℝ) * t))
    (h4 : x ≤ nearestIntDist ((e : ℝ) * t)) :
    x ≤ ML (![a, b, c, d, e] : Fin 5 → ℤ) := by
  apply ML_ge_of_witness' _ t x
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- Facts about `r = s/(5s+1)`. -/
theorem r_facts (s : ℕ) (hs : 1 ≤ s) :
    (1 : ℝ) / 6 ≤ (s : ℝ) / (5 * s + 1) ∧ 5 * ((s : ℝ) / (5 * s + 1)) < 1 ∧
    5 * (s : ℝ) * ((s : ℝ) / (5 * s + 1)) = s - (s : ℝ) / (5 * s + 1) := by
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hpos : (0 : ℝ) < 5 * s + 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by norm_num) hpos]; linarith
  · have : (s : ℝ) / (5 * s + 1) < 1 / 5 := by
      rw [div_lt_div_iff₀ hpos (by norm_num)]; linarith
    linarith
  · field_simp; ring

/-- **Lemma W, common part**: at `t = s/(5s+1)` runners `1,2,3,4` and `5s` stay `≥ s/(5s+1)`
from the integers.  Stated as five separate facts to keep the proofs short. -/
theorem W_one (s : ℕ) (hs : 1 ≤ s) :
    (s : ℝ) / (5 * s + 1) ≤ nearestIntDist (((1 : ℤ) : ℝ) * ((s : ℝ) / (5 * s + 1))) := by
  obtain ⟨h1, h2, h3⟩ := r_facts s hs
  apply nd_ge_shift 0 <;> push_cast <;> linarith

theorem W_two (s : ℕ) (hs : 1 ≤ s) :
    (s : ℝ) / (5 * s + 1) ≤ nearestIntDist (((2 : ℤ) : ℝ) * ((s : ℝ) / (5 * s + 1))) := by
  obtain ⟨h1, h2, h3⟩ := r_facts s hs
  apply nd_ge_shift 0 <;> push_cast <;> linarith

theorem W_three (s : ℕ) (hs : 1 ≤ s) :
    (s : ℝ) / (5 * s + 1) ≤ nearestIntDist (((3 : ℤ) : ℝ) * ((s : ℝ) / (5 * s + 1))) := by
  obtain ⟨h1, h2, h3⟩ := r_facts s hs
  apply nd_ge_shift 0 <;> push_cast <;> linarith

theorem W_four (s : ℕ) (hs : 1 ≤ s) :
    (s : ℝ) / (5 * s + 1) ≤ nearestIntDist (((4 : ℤ) : ℝ) * ((s : ℝ) / (5 * s + 1))) := by
  obtain ⟨h1, h2, h3⟩ := r_facts s hs
  apply nd_ge_shift 0 <;> push_cast <;> linarith

theorem W_seven (s : ℕ) (hs : 1 ≤ s) :
    (s : ℝ) / (5 * s + 1) ≤ nearestIntDist (((7 : ℤ) : ℝ) * ((s : ℝ) / (5 * s + 1))) := by
  obtain ⟨h1, h2, h3⟩ := r_facts s hs
  apply nd_ge_shift 1 <;> push_cast <;> linarith

theorem W_five_s (s : ℕ) (hs : 1 ≤ s) :
    (s : ℝ) / (5 * s + 1) ≤
      nearestIntDist ((((5 * (s : ℤ) : ℤ)) : ℝ) * ((s : ℝ) / (5 * s + 1))) := by
  obtain ⟨h1, h2, h3⟩ := r_facts s hs
  apply nd_ge_shift ((s : ℤ) - 1) <;> push_cast <;> nlinarith

/-- Lower bound for `V = (1,2,3,4)`. -/
theorem ML_ge_V1 (s : ℕ) (hs : 1 ≤ s) :
    (s : ℝ) / (5 * s + 1) ≤ ML (![1, 2, 3, 4, 5 * (s : ℤ)] : Fin 5 → ℤ) :=
  ML_ge_five 1 2 3 4 (5 * (s : ℤ)) ((s : ℝ) / (5 * s + 1)) _ (W_one s hs) (W_two s hs)
    (W_three s hs) (W_four s hs) (W_five_s s hs)

/-- Lower bound for `V = (1,3,4,7)`. -/
theorem ML_ge_V2 (s : ℕ) (hs : 1 ≤ s) :
    (s : ℝ) / (5 * s + 1) ≤ ML (![1, 3, 4, 7, 5 * (s : ℤ)] : Fin 5 → ℤ) :=
  ML_ge_five 1 3 4 7 (5 * (s : ℤ)) ((s : ℝ) / (5 * s + 1)) _ (W_one s hs) (W_three s hs)
    (W_four s hs) (W_seven s hs) (W_five_s s hs)

/-- The exceptional witness `t = 5/11` for `(1,3,4,7,5)`. -/
theorem ML_ge_V2_s1 : (2 / 11 : ℝ) ≤ ML (![1, 3, 4, 7, 5] : Fin 5 → ℤ) := by
  apply ML_ge_five 1 3 4 7 5 (5 / 11) <;> push_cast
  · apply nd_ge_shift 0 <;> push_cast <;> norm_num
  · apply nd_ge_shift 1 <;> push_cast <;> norm_num
  · apply nd_ge_shift 1 <;> push_cast <;> norm_num
  · apply nd_ge_shift 3 <;> push_cast <;> norm_num
  · apply nd_ge_shift 2 <;> push_cast <;> norm_num

/-! ## Section 4: Theorem 1(ii), exact values -/

/-- `ML (1,2,3,4,5s) = s/(5s+1)` for every `s ≥ 1`. -/
theorem ML_V1_eq (s : ℕ) (hs : 1 ≤ s) :
    ML (![1, 2, 3, 4, 5 * (s : ℤ)] : Fin 5 → ℤ) = (s : ℝ) / (5 * s + 1) := by
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hpos : (0 : ℝ) < 5 * s + 1 := by linarith
  have hub := ML_le_of_tent 1 2 3 4 (1 / 7) s hs HProp_V1
  have hmax : max ((s : ℝ) / (5 * s + 1)) (1 / 7) = (s : ℝ) / (5 * s + 1) := by
    apply max_eq_left
    rw [le_div_iff₀ hpos]; linarith
  rw [hmax] at hub
  exact le_antisymm hub (ML_ge_V1 s hs)

/-- `ML (1,3,4,7,5s) = s/(5s+1)` for every `s ≥ 2`. -/
theorem ML_V2_eq (s : ℕ) (hs : 2 ≤ s) :
    ML (![1, 3, 4, 7, 5 * (s : ℤ)] : Fin 5 → ℤ) = (s : ℝ) / (5 * s + 1) := by
  have hs1 : 1 ≤ s := by omega
  have hsr : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hpos : (0 : ℝ) < 5 * s + 1 := by linarith
  have hub := ML_le_of_tent 1 3 4 7 (2 / 11) s hs1 HProp_V2
  have hmax : max ((s : ℝ) / (5 * s + 1)) (2 / 11) = (s : ℝ) / (5 * s + 1) := by
    apply max_eq_left
    rw [le_div_iff₀ hpos]; linarith
  rw [hmax] at hub
  exact le_antisymm hub (ML_ge_V2 s hs1)

/-- The exception: `ML (1,3,4,7,5) = 2/11` (the quintuple `(1,3,4,5,7)` up to order). -/
theorem ML_V2_s1_eq : ML (![1, 3, 4, 7, 5] : Fin 5 → ℤ) = 2 / 11 := by
  have hub := ML_le_of_tent 1 3 4 7 (2 / 11) 1 le_rfl HProp_V2
  have hmax : max (((1 : ℕ) : ℝ) / (5 * ((1 : ℕ) : ℝ) + 1)) (2 / 11) = 2 / 11 := by
    apply max_eq_right; norm_num
  rw [hmax] at hub
  have e : (![1, 3, 4, 7, 5 * ((1 : ℕ) : ℤ)] : Fin 5 → ℤ) = ![1, 3, 4, 7, 5] := by
    simp
  rw [e] at hub
  exact le_antisymm hub ML_ge_V2_s1

/-! ## Section 5: Lemma N and Lemma P (the `ML ≥ 1/5` half) -/

theorem one_fifth_le_nd (n : ℤ) (h : ¬ (5 ∣ n)) :
    (1 / 5 : ℝ) ≤ nearestIntDist ((n : ℝ) * (1 / 5)) := by
  have h0 : n % 5 ≠ 0 := fun hc => h (Int.dvd_of_emod_eq_zero hc)
  have hge : 0 ≤ n % 5 := Int.emod_nonneg n (by norm_num)
  have hlt : n % 5 < 5 := Int.emod_lt_of_pos n (by norm_num)
  have hr1 : (1 : ℝ) ≤ ((n % 5 : ℤ) : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ n % 5)
  have hr2 : ((n % 5 : ℤ) : ℝ) ≤ 4 := by exact_mod_cast (by omega : n % 5 ≤ 4)
  have he : (n : ℝ) = ((n % 5 : ℤ) : ℝ) + 5 * ((n / 5 : ℤ) : ℝ) := by
    have := Int.emod_add_mul_ediv n 5
    exact_mod_cast this.symm
  apply nd_ge_shift (n / 5)
  · rw [he]; linarith
  · rw [he]; linarith
  · rw [he]; linarith
  · rw [he]; linarith

/-- **Lemma N.** `A = 1`, `5 ∤ B`, `5 ∤ vᵢ`: `ML ≥ 1/5`. -/
theorem ML_ge_fifth_N (v1 v2 v3 v4 B : ℤ) (h1 : ¬ 5 ∣ v1) (h2 : ¬ 5 ∣ v2) (h3 : ¬ 5 ∣ v3)
    (h4 : ¬ 5 ∣ v4) (hB : ¬ 5 ∣ B) :
    (1 / 5 : ℝ) ≤ ML (![v1, v2, v3, v4, B] : Fin 5 → ℤ) :=
  ML_ge_five v1 v2 v3 v4 B (1 / 5) _ (one_fifth_le_nd v1 h1) (one_fifth_le_nd v2 h2)
    (one_fifth_le_nd v3 h3) (one_fifth_le_nd v4 h4) (one_fifth_le_nd B hB)

/-- **Lemma P.**  `A ≥ 2`, `A` coprime to `B`, `5 ∤ vᵢ`: `ML (A v₁, .., A v₄, B) ≥ 1/5`. -/
theorem ML_ge_fifth_P (v1 v2 v3 v4 A B : ℤ) (h1 : ¬ 5 ∣ v1) (h2 : ¬ 5 ∣ v2) (h3 : ¬ 5 ∣ v3)
    (h4 : ¬ 5 ∣ v4) (hA : 2 ≤ A) (hcop : IsCoprime A B) :
    (1 / 5 : ℝ) ≤ ML (![A * v1, A * v2, A * v3, A * v4, B] : Fin 5 → ℤ) := by
  obtain ⟨u, w, huw⟩ := hcop
  have hAr : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hA0 : (A : ℝ) ≠ 0 := by linarith
  have huwR : (u : ℝ) * A + w * B = 1 := by exact_mod_cast huw
  -- the integer `j` placing `(B/5 + j)/A` within `1/(2A)` of `1/2`
  set j : ℤ := ⌊(A : ℝ) / 2 - (B : ℝ) / 5 + 1 / 2⌋ with hj
  have hj1 : (j : ℝ) ≤ (A : ℝ) / 2 - (B : ℝ) / 5 + 1 / 2 := Int.floor_le _
  have hj2 : (A : ℝ) / 2 - (B : ℝ) / 5 + 1 / 2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
  set h : ℤ := w * j with hh
  set t : ℝ := (1 / 5 + (h : ℝ)) / A with ht
  have hAt : (A : ℝ) * t = 1 / 5 + (h : ℝ) := by
    rw [ht]; field_simp
  set z : ℝ := ((B : ℝ) / 5 + (j : ℝ)) / A with hz
  have hAz : (A : ℝ) * z = (B : ℝ) / 5 + (j : ℝ) := by
    rw [hz]; field_simp
  have hBt : (B : ℝ) * t = z - ((u * j : ℤ) : ℝ) := by
    apply mul_left_cancel₀ hA0
    have e1 : (A : ℝ) * ((B : ℝ) * t) = (B : ℝ) * ((A : ℝ) * t) := by ring
    rw [e1, hAt]
    push_cast
    rw [mul_sub, hAz]
    have : (h : ℝ) = (w : ℝ) * (j : ℝ) := by rw [hh]; push_cast; ring
    rw [this]
    linear_combination (j : ℝ) * huwR
  -- the B runner
  have hz1 : (1 / 4 : ℝ) ≤ z := by
    by_contra hc
    rw [not_le] at hc
    nlinarith
  have hz2 : z ≤ 3 / 4 := by
    by_contra hc
    rw [not_le] at hc
    nlinarith
  have hB : (1 / 5 : ℝ) ≤ nearestIntDist ((B : ℝ) * t) := by
    rw [hBt, sub_eq_add_neg, ← Int.cast_neg, nearestIntDist_add_int]
    exact nearestIntDist_ge (by linarith) (by linarith) (by linarith) (by linarith)
  -- the A v runners
  have hv : ∀ v : ℤ, ¬ 5 ∣ v →
      (1 / 5 : ℝ) ≤ nearestIntDist ((((A * v : ℤ)) : ℝ) * t) := by
    intro v hv
    have e : (((A * v : ℤ)) : ℝ) * t = (v : ℝ) * (1 / 5) + ((v * h : ℤ) : ℝ) := by
      push_cast
      have : (A : ℝ) * (v : ℝ) * t = (v : ℝ) * ((A : ℝ) * t) := by ring
      rw [this, hAt]; ring
    rw [e, nearestIntDist_add_int]
    exact one_fifth_le_nd v hv
  exact ML_ge_five (A * v1) (A * v2) (A * v3) (A * v4) B t (1 / 5) (hv v1 h1) (hv v2 h2)
    (hv v3 h3) (hv v4 h4) hB

/-! ## Section 6: Theorem 1, assembly -/

/-- **Theorem 1(i), `A ≥ 2`**, for `V = (1,2,3,4)` and `V = (1,3,4,7)`. -/
theorem thm1_i_A_ge_two_V1 (A B : ℤ) (hA : 2 ≤ A) (hcop : IsCoprime A B) :
    (1 / 5 : ℝ) ≤ ML (![A * 1, A * 2, A * 3, A * 4, B] : Fin 5 → ℤ) :=
  ML_ge_fifth_P 1 2 3 4 A B (by omega) (by omega) (by omega) (by omega) hA hcop

theorem thm1_i_A_ge_two_V2 (A B : ℤ) (hA : 2 ≤ A) (hcop : IsCoprime A B) :
    (1 / 5 : ℝ) ≤ ML (![A * 1, A * 3, A * 4, A * 7, B] : Fin 5 → ℤ) :=
  ML_ge_fifth_P 1 3 4 7 A B (by omega) (by omega) (by omega) (by omega) hA hcop

/-- **Theorem 1(i), `A = 1`, `5 ∤ B`.** -/
theorem thm1_i_A_one_V1 (B : ℤ) (hB : ¬ 5 ∣ B) :
    (1 / 5 : ℝ) ≤ ML (![1, 2, 3, 4, B] : Fin 5 → ℤ) :=
  ML_ge_fifth_N 1 2 3 4 B (by omega) (by omega) (by omega) (by omega) hB

theorem thm1_i_A_one_V2 (B : ℤ) (hB : ¬ 5 ∣ B) :
    (1 / 5 : ℝ) ≤ ML (![1, 3, 4, 7, B] : Fin 5 → ℤ) :=
  ML_ge_fifth_N 1 3 4 7 B (by omega) (by omega) (by omega) (by omega) hB

end KS5Tail
end LRSpectrumFull
