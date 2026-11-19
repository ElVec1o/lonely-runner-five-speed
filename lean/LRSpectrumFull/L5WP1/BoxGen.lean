/-
# WP1 box theorem: the general statement, for any box bound `B`

`box_theorem B nt ex hm hvals`: if the kernel test `tupleOK` holds on all increasing tuples with maximum `<= B`
(`hm`, obtained from the chunk theorems by `master_of_chunks`) and every tuple of `nt` has `ML = s/(5s+1)` (`hvals`), then
for every strictly increasing positive integer five-tuple `v` with `v 4 <= B`:

  `ML v < 1/5`  iff  `v = g * u` with `g >= 1` and `u` on the list `nt`,

and in that case `ML v = s/(5s+1)` for some `s >= 1`.  The near-tight list is therefore a consequence of the kernel
checks (a tuple off the list that is not covered by a witness would make a chunk theorem false), not an input.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5WP1.BoxSound
import LRSpectrumFull.L5WP1.BoxNT

namespace L5W

open LRSpectrumFull

theorem vecL_u (u : Fin 5 → ℕ) : vecL [u 0, u 1, u 2, u 3, u 4] = fun i => (u i : ℤ) := by
  funext i; fin_cases i <;> simp [vecL]

theorem near_tight_value (nt : List (List ℕ))
    (hvals : ∀ l ∈ nt, ∃ s : ℕ, 1 ≤ s ∧ ML (vecL l) = (s : ℝ) / (5 * s + 1))
    (v : Fin 5 → ℤ) (g : ℕ) (u : Fin 5 → ℕ) (hg : 0 < g) (hv : ∀ i, v i = (g : ℤ) * (u i : ℤ))
    (hmem : [u 0, u 1, u 2, u 3, u 4] ∈ nt) :
    ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1) ∧ ML v < 1 / 5 := by
  obtain ⟨s, hs, hml⟩ := hvals _ hmem
  have hvf : v = fun i => (g : ℤ) * (u i : ℤ) := funext hv
  have hML : ML v = (s : ℝ) / (5 * s + 1) := by
    rw [hvf, ML_smul (g : ℤ) (by exact_mod_cast hg) (fun i => (u i : ℤ)), ← vecL_u u]
    exact hml
  refine ⟨s, hs, hML, ?_⟩
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  rw [hML, div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **Box theorem.** -/
theorem box_theorem (B : ℕ) (nt : List (List ℕ)) (ex : List (List ℕ × ℕ × ℕ))
    (hm : ∀ a b c d e : ℕ, 1 ≤ a → a < b → b < c → c < d → d < e → e ≤ B → tupleOK nt ex a b c d e = true)
    (hvals : ∀ l ∈ nt, ∃ s : ℕ, 1 ≤ s ∧ ML (vecL l) = (s : ℝ) / (5 * s + 1))
    (v : Fin 5 → ℤ) (h0 : 0 < v 0) (h01 : v 0 < v 1) (h12 : v 1 < v 2) (h23 : v 2 < v 3) (h34 : v 3 < v 4)
    (hB : v 4 ≤ B) :
    (ML v < 1 / 5 ↔ ∃ (g : ℕ) (u : Fin 5 → ℕ), 0 < g ∧ (∀ i, v i = (g : ℤ) * (u i : ℤ)) ∧
        [u 0, u 1, u 2, u 3, u 4] ∈ nt) ∧
    (ML v < 1 / 5 → ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1)) := by
  have hdich := box_core B nt ex hm v h0 h01 h12 h23 h34 hB
  have hfwd : ML v < 1 / 5 → ∃ (g : ℕ) (u : Fin 5 → ℕ), 0 < g ∧ (∀ i, v i = (g : ℤ) * (u i : ℤ)) ∧
        [u 0, u 1, u 2, u 3, u 4] ∈ nt := by
    intro hlt
    rcases hdich with h | h
    · exact absurd h (not_le.mpr hlt)
    · exact h
  refine ⟨⟨hfwd, ?_⟩, ?_⟩
  · rintro ⟨g, u, hg, hv, hmem⟩
    obtain ⟨s, _, _, hlt⟩ := near_tight_value nt hvals v g u hg hv hmem
    exact hlt
  · intro hlt
    obtain ⟨g, u, hg, hv, hmem⟩ := hfwd hlt
    obtain ⟨s, hs, hML, _⟩ := near_tight_value nt hvals v g u hg hv hmem
    exact ⟨s, hs, hML⟩

end L5W
