theorem five_speed_attained (s : ℕ) (hs : 1 ≤ s) :
    ∃ v : Fin 5 → ℤ, (∀ i, 0 < v i) ∧ Function.Injective v ∧ ML v = (s : ℝ) / (5 * s + 1) := by
