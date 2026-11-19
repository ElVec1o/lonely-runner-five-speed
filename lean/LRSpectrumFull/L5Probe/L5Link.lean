/-
# L5 probe: link lemma from the `Nat` witness predicate to the project's `ML`

`witnessOK v = true` (five natural speeds, the fixed time list of `L5Times`) implies `1/5 ≤ ML v`, where `ML` is
`LRSpectrumFull.ML` of `MaxLoneliness.lean` and the speeds are cast to `ℤ`.  The only kernel computation used here
is `times_pos` (every denominator in the list is positive).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5Probe.L5Core
import LRSpectrumFull.MaxLoneliness

namespace L5

open LRSpectrumFull

/-- the spec-level predicate on a five-speed vector -/
def witnessOK (v : Fin 5 → ℕ) : Bool := witnessS (v 0) (v 1) (v 2) (v 3) (v 4)

theorem times_pos : ∀ p ∈ times, 0 < p.2 := by decide +kernel

theorem okAt_real {a q v : ℕ} (hq : 0 < q) (h : okAt a q v = true) :
    (1 : ℝ) / 5 ≤ nearestIntDist ((v : ℝ) * ((a : ℝ) / q)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e : (v : ℝ) * ((a : ℝ) / q) = ((v * a : ℕ) : ℝ) / ((q : ℕ) : ℝ) := by push_cast; ring
  rw [e]
  unfold nearestIntDist
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hrl : v * a % q < q := Nat.mod_lt _ hq
  unfold okAt at h
  have h' : q ≤ 5 * Nat.min (v * a % q) (q - v * a % q) := by
    simpa [Nat.ble_eq] using h
  have h1 : q ≤ 5 * (v * a % q) := le_trans h' (Nat.mul_le_mul_left 5 (Nat.min_le_left _ _))
  have h2 : q ≤ 5 * (q - v * a % q) := le_trans h' (Nat.mul_le_mul_left 5 (Nat.min_le_right _ _))
  generalize v * a % q = r at *
  apply le_min
  · rw [le_div_iff₀ hq']
    have : (q : ℝ) ≤ 5 * r := by exact_mod_cast h1
    linarith
  · have e2 : (1 : ℝ) - (r : ℝ) / q = ((q : ℝ) - r) / q := by field_simp
    rw [e2, le_div_iff₀ hq']
    have : (q : ℝ) ≤ 5 * ((q - r : ℕ) : ℝ) := by exact_mod_cast h2
    rw [Nat.cast_sub hrl.le] at this
    linarith

theorem witnessS_spec {v0 v1 v2 v3 v4 : ℕ} (h : witnessS v0 v1 v2 v3 v4 = true) :
    ∃ a q : ℕ, 0 < q ∧ okAt a q v0 = true ∧ okAt a q v1 = true ∧ okAt a q v2 = true ∧
      okAt a q v3 = true ∧ okAt a q v4 = true := by
  unfold witnessS at h
  rw [List.any_eq_true] at h
  obtain ⟨p, hp, hg⟩ := h
  refine ⟨p.1, p.2, times_pos p hp, ?_⟩
  simpa [good, Bool.and_eq_true, and_assoc] using hg

/-- **Link.**  A witness for the five natural speeds gives the floor `1/5` for the project's `ML`. -/
theorem ML_ge_of_witness (v : Fin 5 → ℕ) (h : witnessOK v = true) :
    (1 : ℝ) / 5 ≤ ML (fun i => (v i : ℤ)) := by
  obtain ⟨a, q, hq, h0, h1, h2, h3, h4⟩ := witnessS_spec h
  have key : ∀ i : Fin 5,
      (1 : ℝ) / 5 ≤ nearestIntDist ((((fun i => (v i : ℤ)) i : ℤ) : ℝ) * ((a : ℝ) / q)) := by
    intro i
    simp only [Int.cast_natCast]
    obtain ⟨j, hj⟩ := i
    have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hj5 with rfl | rfl | rfl | rfl | rfl
    · exact okAt_real hq h0
    · exact okAt_real hq h1
    · exact okAt_real hq h2
    · exact okAt_real hq h3
    · exact okAt_real hq h4
  have hg : (1 : ℝ) / 5 ≤ gap (fun i => (v i : ℤ)) ((a : ℝ) / q) := le_gap _ _ _ key
  exact le_trans hg (le_csSup (bddAbove_range_gap _) ⟨_, rfl⟩)

end L5
