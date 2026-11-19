/-
# check_axioms.lean : print the axioms of the headline theorems of the five-speed spectrum.  Builds NOTHING.

Run through `check_axioms.sh` (`lake env lean check_axioms.lean`, which only READS the .olean files of the closure of
`LRSpectrumFull.L5S5.FiveSpeedFinal4`, 17,598 project modules; they must have been built: see build.sh).

Every `#print axioms` below on a real theorem must print exactly [propext, Classical.choice, Quot.sound].  The two planted
controls at the end (a direct and a transitive `sorry`) must print `sorryAx`: they show that a `sorry` anywhere below a
theorem would be visible in this printout.  No `sorry`, no `native_decide`, no axiom is used by this file except in the controls.
-/
import LRSpectrumFull.L5S5.FiveSpeedFinal4

/-! ## The statements, as Lean prints them (read these against the English statement in README.md) -/

#check @LRSpectrumFull.L5S5.five_speed_spectrum_final
#check @LRSpectrumFull.L5S5.five_speed_spectrum_iff_final
#check @LRSpectrumFull.L5S5.five_speed_attained
#check @LRSpectrumFull.L5S5.five_speed_spectrum2
#check @LRSpectrumFull.L5S5.hyps2_trivial
#print LRSpectrumFull.ML
#print LRSpectrumFull.gap
#print LRSpectrumFull.nearestIntDist

/-! ## Axioms: the two headline theorems (and the pieces they cite directly) -/

#print axioms LRSpectrumFull.L5S5.five_speed_spectrum_final
#print axioms LRSpectrumFull.L5S5.five_speed_spectrum_iff_final
#print axioms LRSpectrumFull.L5S5.five_speed_attained
#print axioms LRSpectrumFull.L5S5.five_speed_spectrum2
#print axioms LRSpectrumFull.L5S5.hyps2_trivial

/-! ## NEGATIVE CONTROLS (must print sorryAx; check_axioms.sh requires both) -/

theorem check_axioms_planted_sorry : (1 : Nat) = 2 := by sorry
theorem check_axioms_planted_sorry_user : (2 : Nat) = 3 := by
  have := check_axioms_planted_sorry
  omega

#print axioms check_axioms_planted_sorry
#print axioms check_axioms_planted_sorry_user
