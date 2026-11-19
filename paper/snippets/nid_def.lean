noncomputable def nearestIntDist (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)
