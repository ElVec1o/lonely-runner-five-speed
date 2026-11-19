/-
# L5S5.FiveSpeedFinal3 : the five-speed spectrum with NO hypotheses left (all 1,965 representatives built, `Top.Holes` empty)

`five_speed_spectrum2` takes `FiveSpeedHyps2 = {holes : Top.Holes, hlines : Hl.Top.HLines holes}`.  Every representative module is now built, so `Top.Holes` is an empty structure and
`HLines` has no field left for a hole representative or a built representative without a `lines<c>` theorem; this module instantiates the hypothesis and states the result unconditionally.
No `sorry`, no `native_decide`, no new axiom.
-/
import LRSpectrumFull.L5S5.FiveSpeedFinal2

namespace LRSpectrumFull
namespace L5S5

open LRSpectrumFull.AggFive

/-- The only instance of `FiveSpeedHyps2`: no hole representative, so no remaining lines hypothesis. -/
theorem hyps2_trivial : Nonempty FiveSpeedHyps2 :=
  ⟨⟨⟨⟩, by repeat' constructor⟩⟩

/-- **The five-speed spectrum (below 1/5), unconditional.** -/
theorem five_speed_spectrum_final (v : Fin 5 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hlt : ML v < 1 / 5) : ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1) :=
  five_speed_spectrum2 hyps2_trivial.some v hpos hinj hlt

#print axioms five_speed_spectrum_final

end L5S5
end LRSpectrumFull
