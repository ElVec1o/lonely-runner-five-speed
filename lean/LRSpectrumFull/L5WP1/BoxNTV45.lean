import LRSpectrumFull.L5WP1.BoxNT
import LRSpectrumFull.L5WP1.BoxData45

set_option maxHeartbeats 0

namespace L5W
open LRSpectrumFull

/-- exact value of a sporadic near-tight tuple: lower bound by the time 3/11, upper bound by a cover chain of 11 intervals -/
theorem spor45_1 : ML (vecL [1,2,3,5,8]) = ((2:ℕ):ℝ) / (5 * (2:ℕ) + 1) := by
  rw [ml_eq_of_data 1 2 3 5 8 2 11 3 11 120 [(1,0),(5,1),(8,2),(3,1),(5,2),(2,1),(5,3),(3,2),(8,6),(5,4),(1,1)] (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]
  norm_num

/-- exact value of a sporadic near-tight tuple: lower bound by the time 5/11, upper bound by a cover chain of 13 intervals -/
theorem spor45_2 : ML (vecL [1,3,4,5,7]) = ((2:ℕ):ℝ) / (5 * (2:ℕ) + 1) := by
  rw [ml_eq_of_data 1 3 4 5 7 2 11 5 11 420 [(1,0),(5,1),(4,1),(3,1),(5,2),(7,3),(4,2),(7,4),(5,3),(3,2),(4,3),(5,4),(1,1)] (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]
  norm_num

/-- exact value of a sporadic near-tight tuple: lower bound by the time 1/6, upper bound by a cover chain of 13 intervals -/
theorem spor45_3 : ML (vecL [1,3,4,5,9]) = ((1:ℕ):ℝ) / (5 * (1:ℕ) + 1) := by
  rw [ml_eq_of_data 1 3 4 5 9 1 6 1 6 180 [(1,0),(5,1),(4,1),(3,1),(5,2),(9,4),(4,2),(9,5),(5,3),(3,2),(4,3),(5,4),(1,1)] (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]
  norm_num

/-- exact value of a sporadic near-tight tuple: lower bound by the time 7/16, upper bound by a cover chain of 13 intervals -/
theorem spor45_4 : ML (vecL [1,3,4,5,11]) = ((3:ℕ):ℝ) / (5 * (3:ℕ) + 1) := by
  rw [ml_eq_of_data 1 3 4 5 11 3 16 7 16 660 [(1,0),(5,1),(4,1),(3,1),(5,2),(11,5),(4,2),(11,6),(5,3),(3,2),(4,3),(5,4),(1,1)] (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]
  norm_num

/-- exact value of a sporadic near-tight tuple: lower bound by the time 5/11, upper bound by a cover chain of 13 intervals -/
theorem spor45_5 : ML (vecL [1,3,4,5,18]) = ((2:ℕ):ℝ) / (5 * (2:ℕ) + 1) := by
  rw [ml_eq_of_data 1 3 4 5 18 2 11 5 11 180 [(1,0),(5,1),(4,1),(3,1),(5,2),(18,8),(4,2),(18,10),(5,3),(3,2),(4,3),(5,4),(1,1)] (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]
  norm_num

/-- exact value of a sporadic near-tight tuple: lower bound by the time 14/31, upper bound by a cover chain of 13 intervals -/
theorem spor45_6 : ML (vecL [1,3,4,5,27]) = ((6:ℕ):ℝ) / (5 * (6:ℕ) + 1) := by
  rw [ml_eq_of_data 1 3 4 5 27 6 31 14 31 540 [(1,0),(5,1),(4,1),(3,1),(5,2),(27,12),(4,2),(27,15),(5,3),(3,2),(4,3),(5,4),(1,1)] (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]
  norm_num

/-- exact value of a sporadic near-tight tuple: lower bound by the time 4/11, upper bound by a cover chain of 15 intervals -/
theorem spor45_7 : ML (vecL [1,4,5,6,7]) = ((2:ℕ):ℝ) / (5 * (2:ℕ) + 1) := by
  rw [ml_eq_of_data 1 4 5 6 7 2 11 4 11 420 [(1,0),(5,1),(4,1),(7,2),(6,2),(5,2),(7,3),(4,2),(7,4),(5,3),(6,4),(7,5),(4,3),(5,4),(1,1)] (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]
  norm_num

/-- exact value of a sporadic near-tight tuple: lower bound by the time 14/31, upper bound by a cover chain of 15 intervals -/
theorem spor45_8 : ML (vecL [1,4,5,6,27]) = ((6:ℕ):ℝ) / (5 * (6:ℕ) + 1) := by
  rw [ml_eq_of_data 1 4 5 6 27 6 31 14 31 540 [(1,0),(5,1),(4,1),(27,8),(6,2),(5,2),(27,12),(4,2),(27,15),(5,3),(6,4),(27,19),(4,3),(5,4),(1,1)] (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]
  norm_num

/-- exact value of a sporadic near-tight tuple: lower bound by the time 3/16, upper bound by a cover chain of 21 intervals -/
theorem spor45_9 : ML (vecL [1,7,8,9,15]) = ((3:ℕ):ℝ) / (5 * (3:ℕ) + 1) := by
  rw [ml_eq_of_data 1 7 8 9 15 3 16 3 16 2520 [(1,0),(15,3),(9,2),(8,2),(7,2),(9,3),(8,3),(15,6),(7,3),(15,7),(8,4),(15,8),(7,4),(15,9),(8,5),(9,6),(7,5),(8,6),(9,7),(15,12),(1,1)] (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]
  norm_num

/-- exact value of a sporadic near-tight tuple: lower bound by the time 2/21, upper bound by a cover chain of 17 intervals -/
theorem spor45_10 : ML (vecL [2,3,5,8,19]) = ((4:ℕ):ℝ) / (5 * (4:ℕ) + 1) := by
  rw [ml_eq_of_data 2 3 5 8 19 4 21 2 21 2280 [(2,0),(19,2),(8,1),(19,3),(5,1),(8,2),(3,1),(5,2),(2,1),(5,3),(3,2),(8,6),(5,4),(19,16),(8,7),(19,17),(2,2)] (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]
  norm_num

/-- exact value of a sporadic near-tight tuple: lower bound by the time 5/16, upper bound by a cover chain of 19 intervals -/
theorem spor45_11 : ML (vecL [2,5,7,8,9]) = ((3:ℕ):ℝ) / (5 * (3:ℕ) + 1) := by
  rw [ml_eq_of_data 2 5 7 8 9 3 16 5 16 2520 [(2,0),(9,1),(7,1),(5,1),(8,2),(7,2),(9,3),(8,3),(5,2),(2,1),(5,3),(8,5),(9,6),(7,5),(8,6),(5,4),(7,6),(9,8),(2,2)] (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]
  norm_num

/-- exact value of a sporadic near-tight tuple: lower bound by the time 10/21, upper bound by a cover chain of 23 intervals -/
theorem spor45_12 : ML (vecL [3,5,8,9,13]) = ((4:ℕ):ℝ) / (5 * (4:ℕ) + 1) := by
  rw [ml_eq_of_data 3 5 8 9 13 4 21 10 21 4680 [(3,0),(13,1),(9,1),(8,1),(13,2),(5,1),(8,2),(3,1),(5,2),(9,4),(13,6),(8,4),(13,7),(9,5),(5,3),(3,2),(8,6),(5,4),(13,11),(8,7),(9,8),(13,12),(3,3)] (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]
  norm_num

/-- exact value of a sporadic near-tight tuple: lower bound by the time 10/21, upper bound by a cover chain of 23 intervals -/
theorem spor45_13 : ML (vecL [3,5,8,11,13]) = ((4:ℕ):ℝ) / (5 * (4:ℕ) + 1) := by
  rw [ml_eq_of_data 3 5 8 11 13 4 21 10 21 17160 [(3,0),(13,1),(11,1),(8,1),(13,2),(5,1),(8,2),(3,1),(5,2),(11,5),(13,6),(8,4),(13,7),(11,6),(5,3),(3,2),(8,6),(5,4),(13,11),(8,7),(11,10),(13,12),(3,3)] (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)]
  norm_num

theorem ntvals45 : ∀ l ∈ nt45, ∃ s : ℕ, 1 ≤ s ∧ ML (vecL l) = (s : ℝ) / (5 * s + 1) := by
  intro l hl
  simp only [nt45, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by norm_num, val_fam1 1 5 (by norm_num) (by norm_num)⟩
  · exact ⟨2, by norm_num, val_fam1 2 10 (by norm_num) (by norm_num)⟩
  · exact ⟨3, by norm_num, val_fam1 3 15 (by norm_num) (by norm_num)⟩
  · exact ⟨4, by norm_num, val_fam1 4 20 (by norm_num) (by norm_num)⟩
  · exact ⟨5, by norm_num, val_fam1 5 25 (by norm_num) (by norm_num)⟩
  · exact ⟨6, by norm_num, val_fam1 6 30 (by norm_num) (by norm_num)⟩
  · exact ⟨7, by norm_num, val_fam1 7 35 (by norm_num) (by norm_num)⟩
  · exact ⟨8, by norm_num, val_fam1 8 40 (by norm_num) (by norm_num)⟩
  · exact ⟨9, by norm_num, val_fam1 9 45 (by norm_num) (by norm_num)⟩
  · exact ⟨2, by norm_num, spor45_1⟩
  · exact ⟨2, by norm_num, spor45_2⟩
  · exact ⟨1, by norm_num, spor45_3⟩
  · exact ⟨3, by norm_num, spor45_4⟩
  · exact ⟨2, by norm_num, spor45_5⟩
  · exact ⟨6, by norm_num, spor45_6⟩
  · exact ⟨2, by norm_num, val_fam2 2 10 (by norm_num) (by norm_num)⟩
  · exact ⟨3, by norm_num, val_fam2 3 15 (by norm_num) (by norm_num)⟩
  · exact ⟨4, by norm_num, val_fam2 4 20 (by norm_num) (by norm_num)⟩
  · exact ⟨5, by norm_num, val_fam2 5 25 (by norm_num) (by norm_num)⟩
  · exact ⟨6, by norm_num, val_fam2 6 30 (by norm_num) (by norm_num)⟩
  · exact ⟨7, by norm_num, val_fam2 7 35 (by norm_num) (by norm_num)⟩
  · exact ⟨8, by norm_num, val_fam2 8 40 (by norm_num) (by norm_num)⟩
  · exact ⟨9, by norm_num, val_fam2 9 45 (by norm_num) (by norm_num)⟩
  · exact ⟨2, by norm_num, spor45_7⟩
  · exact ⟨6, by norm_num, spor45_8⟩
  · exact ⟨3, by norm_num, spor45_9⟩
  · exact ⟨4, by norm_num, spor45_10⟩
  · exact ⟨3, by norm_num, spor45_11⟩
  · exact ⟨4, by norm_num, spor45_12⟩
  · exact ⟨4, by norm_num, spor45_13⟩

end L5W
