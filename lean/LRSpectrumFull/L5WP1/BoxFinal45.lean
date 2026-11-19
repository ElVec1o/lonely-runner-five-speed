/-
# WP1 box theorem, B = 45 (final assembly)

Five distinct positive integer speeds `v 0 < v 1 < v 2 < v 3 < v 4 <= 45`: `ML v < 1/5` exactly when `v` is a positive
multiple of one of the 30 tuples of `nt45` (nine tuples `(1,2,3,4,5s)`, nine `(1,3,4,7,5s)` sorted, twelve sporadic ones),
and then `ML v = s/(5s+1)`.  The 30-tuple list is exactly the set of primitive tuples of the box on which the kernel
witness test `wit4` fails (`box45_failset`); the extra-time list `ex45` is empty.

* `tupleOK45`: completeness of the enumeration + kernel loops (70 chunk theorems, `flatten = allPairs 45`).
* `box45`: the theorem.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5WP1.BoxMaster45
import LRSpectrumFull.L5WP1.BoxNTV45
import LRSpectrumFull.L5WP1.BoxGen

namespace L5W

open LRSpectrumFull

theorem tupleOK45 : ∀ a b c d e : ℕ, 1 ≤ a → a < b → b < c → c < d → d < e → e ≤ 45 →
    tupleOK nt45 ex45 a b c d e = true :=
  master_of_chunks 45 nt45 ex45 chunks45 allChunks45 flat45

/-- **Box theorem, `B = 45`.** -/
theorem box45 (v : Fin 5 → ℤ) (h0 : 0 < v 0) (h01 : v 0 < v 1) (h12 : v 1 < v 2) (h23 : v 2 < v 3)
    (h34 : v 3 < v 4) (hB : v 4 ≤ 45) :
    (ML v < 1 / 5 ↔ ∃ (g : ℕ) (u : Fin 5 → ℕ), 0 < g ∧ (∀ i, v i = (g : ℤ) * (u i : ℤ)) ∧
        [u 0, u 1, u 2, u 3, u 4] ∈ nt45) ∧
    (ML v < 1 / 5 → ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1)) :=
  box_theorem 45 nt45 ex45 tupleOK45 ntvals45 v h0 h01 h12 h23 h34 hB

/-- the near-tight list, each with its exact value -/
theorem nt45_values : ∀ l ∈ nt45, ∃ s : ℕ, 1 ≤ s ∧ ML (vecL l) = (s : ℝ) / (5 * s + 1) := ntvals45

/-- **The near-tight list is exactly the set of failures of the kernel witness test** (primitive increasing tuples of the
box): `wit4` is false precisely on the 30 tuples of `nt45`. -/
theorem box45_failset (a b c d e : ℕ) (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (he : e ≤ 45) (hprim : G5 a b c d e = 1) : L5.wit4 a b c d e = false ↔ [a, b, c, d, e] ∈ nt45 := by
  constructor
  · intro hw
    have h := tupleOK45 a b c d e ha hab hbc hcd hde he
    unfold tupleOK at h
    have hg : Nat.beq (Nat.gcd (Nat.gcd (Nat.gcd (Nat.gcd a b) c) d) e) 1 = true := by
      have : Nat.gcd (Nat.gcd (Nat.gcd (Nat.gcd a b) c) d) e = 1 := hprim
      rw [this]; rfl
    rw [hg, hw] at h
    have hex : exOK ex45 a b c d e = false := by simp [exOK, ex45]
    rw [hex] at h
    simp only [Bool.not_true, Bool.false_or] at h
    unfold ntMem at h
    rw [List.any_eq_true] at h
    obtain ⟨l, hl, hbeq⟩ := h
    have : l = [a, b, c, d, e] := beq_iff_eq.mp hbeq
    rw [this] at hl
    exact hl
  · intro hmem
    by_contra hw
    have hw' : L5.wit4 a b c d e = true := by simpa using hw
    have h1 : (1 : ℝ) / 5 ≤ ML (fun i => ((![a, b, c, d, e] : Fin 5 → ℕ) i : ℤ)) :=
      L5.ML_ge_of_wit4 ![a, b, c, d, e] hw'
    obtain ⟨s, hs, hml⟩ := ntvals45 _ hmem
    have h2 : vecL [a, b, c, d, e] = fun i => ((![a, b, c, d, e] : Fin 5 → ℕ) i : ℤ) := by
      funext i; fin_cases i <;> simp [vecL]
    rw [h2] at hml
    have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
    rw [hml, div_le_div_iff₀ (by norm_num) (by linarith)] at h1
    linarith

#print axioms box45
#print axioms nt45_values
#print axioms tupleOK45
#print axioms box45_failset

end L5W
