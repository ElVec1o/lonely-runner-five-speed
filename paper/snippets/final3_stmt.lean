theorem five_speed_spectrum_final (v : Fin 5 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hlt : ML v < 1 / 5) : ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1) :=
  five_speed_spectrum2 hyps2_trivial.some v hpos hinj hlt
