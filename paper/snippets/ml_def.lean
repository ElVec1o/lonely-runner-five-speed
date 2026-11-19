noncomputable def ML (v : Fin (k + 1) → ℤ) : ℝ :=
  sSup (Set.range (gap v))
