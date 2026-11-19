/-
# WP1 box theorem: unordered and signed corollaries (referee module, new file)

* `gap_perm`, `ML_perm`: `ML (v ∘ σ) = ML v` for a permutation `σ` of the coordinates.
* `gap_signs`, `ML_signs`, `ML_abs`: `ML (ε • v) = ML v` for signs `ε i ∈ {1, -1}`; in particular `ML |v| = ML v`.
* `exists_sort_strictMono`: five pairwise distinct integers can be sorted by a permutation.
* `box_unordered`: the box theorem for five pairwise distinct positive integers `<= B` in any order.
* `box_signed`: the same for five integers with pairwise distinct nonzero absolute values `<= B`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5WP1.BoxGen
import Mathlib.Data.Fin.Tuple.Sort

namespace L5W

open LRSpectrumFull

theorem gap_perm {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (v : Fin (k + 1) → ℤ) (t : ℝ) :
    gap (fun i => v (σ i)) t = gap v t := by
  apply le_antisymm
  · apply le_gap v t
    intro i
    simpa using gap_le (fun i => v (σ i)) t (σ.symm i)
  · apply le_gap (fun i => v (σ i)) t
    intro i
    exact gap_le v t (σ i)

/-- **Permutation invariance of `ML`.** -/
theorem ML_perm {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (v : Fin (k + 1) → ℤ) :
    ML (fun i => v (σ i)) = ML v := by
  have h : gap (fun i => v (σ i)) = gap v := funext (gap_perm σ v)
  simp only [ML, h]

theorem nid_sign (a ε : ℤ) (hε : ε = 1 ∨ ε = -1) (t : ℝ) :
    nearestIntDist (((ε * a : ℤ) : ℝ) * t) = nearestIntDist ((a : ℝ) * t) := by
  rcases hε with rfl | rfl
  · simp
  · have e : (((-1 * a : ℤ) : ℝ)) * t = -((a : ℝ) * t) := by push_cast; ring
    rw [e, nearestIntDist_neg]

theorem gap_signs {k : ℕ} (ε v : Fin (k + 1) → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (t : ℝ) :
    gap (fun i => ε i * v i) t = gap v t := by
  apply le_antisymm
  · apply le_gap v t
    intro i
    have h := gap_le (fun i => ε i * v i) t i
    rwa [nid_sign (v i) (ε i) (hε i) t] at h
  · apply le_gap (fun i => ε i * v i) t
    intro i
    rw [nid_sign (v i) (ε i) (hε i) t]
    exact gap_le v t i

/-- **Sign invariance of `ML`.** -/
theorem ML_signs {k : ℕ} (ε v : Fin (k + 1) → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ML (fun i => ε i * v i) = ML v := by
  have h : gap (fun i => ε i * v i) = gap v := funext (gap_signs ε v hε)
  simp only [ML, h]

/-- `ML` only depends on the absolute values of the speeds. -/
theorem ML_abs {k : ℕ} (v : Fin (k + 1) → ℤ) : ML (fun i => |v i|) = ML v := by
  have hs : ∀ i, (if 0 ≤ v i then (1 : ℤ) else -1) = 1 ∨ (if 0 ≤ v i then (1 : ℤ) else -1) = -1 := by
    intro i; by_cases h : 0 ≤ v i <;> simp [h]
  have e : (fun i => |v i|) = fun i => (if 0 ≤ v i then (1 : ℤ) else -1) * v i := by
    funext i
    by_cases h : 0 ≤ v i
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (not_le.mp h)]
  rw [e]
  exact ML_signs _ v hs

theorem exists_sort_strictMono (v : Fin 5 → ℤ) (hinj : Function.Injective v) :
    ∃ σ : Equiv.Perm (Fin 5), StrictMono (fun i => v (σ i)) := by
  refine ⟨Tuple.sort v, ?_⟩
  have hm : Monotone (v ∘ Tuple.sort v) := Tuple.monotone_sort v
  exact hm.strictMono_of_injective (hinj.comp (Tuple.sort v).injective)

/-- **Box theorem, unordered form.**  Five pairwise distinct positive integers `<= B`, in any order: `ML v < 1/5` exactly
when some rearrangement of `v` is a positive multiple of a tuple of `nt`; then `ML v = s/(5s+1)`. -/
theorem box_unordered (B : ℕ) (nt : List (List ℕ)) (ex : List (List ℕ × ℕ × ℕ))
    (hm : ∀ a b c d e : ℕ, 1 ≤ a → a < b → b < c → c < d → d < e → e ≤ B → tupleOK nt ex a b c d e = true)
    (hvals : ∀ l ∈ nt, ∃ s : ℕ, 1 ≤ s ∧ ML (vecL l) = (s : ℝ) / (5 * s + 1))
    (v : Fin 5 → ℤ) (hinj : Function.Injective v) (hpos : ∀ i, 0 < v i) (hB : ∀ i, v i ≤ B) :
    (ML v < 1 / 5 ↔ ∃ (σ : Equiv.Perm (Fin 5)) (g : ℕ) (u : Fin 5 → ℕ), 0 < g ∧
        (∀ i, v (σ i) = (g : ℤ) * (u i : ℤ)) ∧ [u 0, u 1, u 2, u 3, u 4] ∈ nt) ∧
    (ML v < 1 / 5 → ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1)) := by
  obtain ⟨σ, hσ⟩ := exists_sort_strictMono v hinj
  have hML : ML (fun i => v (σ i)) = ML v := ML_perm σ v
  have hbox := box_theorem B nt ex hm hvals (fun i => v (σ i)) (hpos _)
    (hσ (by decide : (0 : Fin 5) < 1)) (hσ (by decide : (1 : Fin 5) < 2))
    (hσ (by decide : (2 : Fin 5) < 3)) (hσ (by decide : (3 : Fin 5) < 4)) (hB _)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hlt
    rw [← hML] at hlt
    obtain ⟨g, u, hg, hv, hmem⟩ := hbox.1.mp hlt
    exact ⟨σ, g, u, hg, hv, hmem⟩
  · rintro ⟨τ, g, u, hg, hv, hmem⟩
    obtain ⟨s, _, hMLτ, hlt⟩ := near_tight_value nt hvals (fun i => v (τ i)) g u hg hv hmem
    rw [← ML_perm τ v]
    exact hlt
  · intro hlt
    rw [← hML] at hlt ⊢
    exact hbox.2 hlt

/-- **Box theorem, signed form.**  Five integers with pairwise distinct nonzero absolute values `<= B`. -/
theorem box_signed (B : ℕ) (nt : List (List ℕ)) (ex : List (List ℕ × ℕ × ℕ))
    (hm : ∀ a b c d e : ℕ, 1 ≤ a → a < b → b < c → c < d → d < e → e ≤ B → tupleOK nt ex a b c d e = true)
    (hvals : ∀ l ∈ nt, ∃ s : ℕ, 1 ≤ s ∧ ML (vecL l) = (s : ℝ) / (5 * s + 1))
    (v : Fin 5 → ℤ) (hinj : Function.Injective (fun i => |v i|)) (hne : ∀ i, v i ≠ 0) (hB : ∀ i, |v i| ≤ B) :
    (ML v < 1 / 5 ↔ ∃ (σ : Equiv.Perm (Fin 5)) (g : ℕ) (u : Fin 5 → ℕ), 0 < g ∧
        (∀ i, |v (σ i)| = (g : ℤ) * (u i : ℤ)) ∧ [u 0, u 1, u 2, u 3, u 4] ∈ nt) ∧
    (ML v < 1 / 5 → ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1)) := by
  have h := box_unordered B nt ex hm hvals (fun i => |v i|) hinj (fun i => abs_pos.mpr (hne i)) hB
  rw [ML_abs] at h
  exact h

end L5W
