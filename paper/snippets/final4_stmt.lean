theorem five_speed_spectrum_iff_final (x : ℝ) :
    (∃ v : Fin 5 → ℤ, (∀ i, 0 < v i) ∧ Function.Injective v ∧ ML v = x ∧ x < 1 / 5) ↔
      ∃ s : ℕ, 1 ≤ s ∧ x = (s : ℝ) / (5 * s + 1) := by
