noncomputable def gap (v : Fin (k + 1) → ℤ) (t : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => nearestIntDist ((v i : ℝ) * t))
