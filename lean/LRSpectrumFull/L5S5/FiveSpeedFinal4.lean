/-
# L5S5.FiveSpeedFinal4 : unconditional characterisation of the five-speed spectrum below 1/5

The set of values below `1/5` of `ML` on five distinct positive integer speeds is exactly `{ s/(5s+1) : s ≥ 1 }`.  "⊆" is `FiveSpeedFinal3.five_speed_spectrum_final`; "⊇" is `five_speed_attained` (witness `(1,2,3,4,5s)`).
No `sorry`, no `native_decide`, no new axiom.
-/
import LRSpectrumFull.L5S5.FiveSpeedFinal3
import LRSpectrumFull.L5S5.FiveSpeedOfTree

namespace LRSpectrumFull
namespace L5S5

/-- **The five-speed spectrum below 1/5, unconditional.** -/
theorem five_speed_spectrum_iff_final (x : ℝ) :
    (∃ v : Fin 5 → ℤ, (∀ i, 0 < v i) ∧ Function.Injective v ∧ ML v = x ∧ x < 1 / 5) ↔
      ∃ s : ℕ, 1 ≤ s ∧ x = (s : ℝ) / (5 * s + 1) := by
  constructor
  · rintro ⟨v, hp, hi, rfl, hx⟩
    exact five_speed_spectrum_final v hp hi hx
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨v, hp, hi, hv⟩ := five_speed_attained s hs
    refine ⟨v, hp, hi, hv, ?_⟩
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

#print axioms five_speed_spectrum_iff_final

end L5S5
end LRSpectrumFull
