/-
# WP1 box theorem, soundness: from the kernel checks to a statement about `ML`

* `pairLoop_spec`, `chunkP_spec`, `mem_allPairs`, `master_of_chunks`: if the chunks cover `allPairs B` (kernel check
  `flatten = allPairs B`) and every chunk loop is `true`, then `tupleOK` holds for every `1 <= a < b < c < d < e <= B`.
  The completeness of the enumeration is therefore proved here, in Lean; the data only choose the chunk boundaries.
* `tupleOK_spec`: `tupleOK = true` means gcd not `1`, or `1/5 <= ML`, or the tuple is on the list `nt`.
* `box_core`: for every strictly increasing positive integer five-tuple `v` with maximum `<= B`, either `1/5 <= ML v` or
  `v = g * u` with `u` on the list `nt` (scaling `ML (g * u) = ML u` removes the non-primitive tuples).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5Probe.L5Link4
import LRSpectrumFull.Delta2Scaling
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace L5W

open L5 LRSpectrumFull

theorem pairLoop_spec {B : ℕ} {nt : List (List ℕ)} {ex : List (List ℕ × ℕ × ℕ)} {a b : ℕ}
    (h : pairLoop B nt ex a b = true) :
    ∀ c d e, b < c → c < d → d < e → e ≤ B → tupleOK nt ex a b c d e = true := by
  intro c d e hbc hcd hde heB
  unfold pairLoop at h
  rw [List.all_eq_true] at h
  have h1 := h c (List.mem_range'_1.mpr ⟨hbc, by omega⟩)
  rw [List.all_eq_true] at h1
  have h2 := h1 d (List.mem_range'_1.mpr ⟨hcd, by omega⟩)
  rw [List.all_eq_true] at h2
  exact h2 e (List.mem_range'_1.mpr ⟨hde, by omega⟩)

theorem chunkP_spec {B : ℕ} {nt : List (List ℕ)} {ex : List (List ℕ × ℕ × ℕ)} {ps : List (ℕ × ℕ)}
    (h : chunkP B nt ex ps = true) : ∀ p ∈ ps, pairLoop B nt ex p.1 p.2 = true := by
  unfold chunkP at h
  rw [List.all_eq_true] at h
  exact h

theorem mem_allPairs {B a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b + 3 ≤ B) : (a, b) ∈ allPairs B := by
  unfold allPairs
  simp only [List.mem_flatMap, List.mem_map, List.mem_range'_1]
  exact ⟨a, ⟨ha, by omega⟩, b, ⟨by omega, by omega⟩, rfl⟩

/-- **Completeness of the enumeration.**  Chunks that cover `allPairs B` and pass the kernel loops give `tupleOK`
for every increasing tuple with maximum `<= B`. -/
theorem master_of_chunks (B : ℕ) (nt : List (List ℕ)) (ex : List (List ℕ × ℕ × ℕ))
    (chunks : List (List (ℕ × ℕ))) (hall : ∀ ps ∈ chunks, chunkP B nt ex ps = true)
    (hflat : chunks.flatten = allPairs B) :
    ∀ a b c d e : ℕ, 1 ≤ a → a < b → b < c → c < d → d < e → e ≤ B → tupleOK nt ex a b c d e = true := by
  intro a b c d e ha hab hbc hcd hde heB
  have hp : (a, b) ∈ allPairs B := mem_allPairs ha hab (by omega)
  rw [← hflat, List.mem_flatten] at hp
  obtain ⟨ps, hps, hab'⟩ := hp
  exact pairLoop_spec (chunkP_spec (hall ps hps) _ hab') c d e hbc hcd hde heB

theorem tupleOK_spec {nt : List (List ℕ)} {ex : List (List ℕ × ℕ × ℕ)} (w : Fin 5 → ℕ)
    (h : tupleOK nt ex (w 0) (w 1) (w 2) (w 3) (w 4) = true) :
    Nat.gcd (Nat.gcd (Nat.gcd (Nat.gcd (w 0) (w 1)) (w 2)) (w 3)) (w 4) ≠ 1 ∨
      (1 : ℝ) / 5 ≤ ML (fun i => (w i : ℤ)) ∨ [w 0, w 1, w 2, w 3, w 4] ∈ nt := by
  unfold tupleOK at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h1 | h2) | h3) | h4
  · left
    intro hg
    rw [hg] at h1
    exact absurd h1 (by decide)
  · right; left
    exact ML_ge_of_wit4 w h2
  · right; left
    unfold exOK at h3
    rw [List.any_eq_true] at h3
    obtain ⟨r, _, hr⟩ := h3
    simp only [Bool.and_eq_true] at hr
    obtain ⟨⟨⟨⟨⟨⟨_, hq⟩, k0⟩, k1⟩, k2⟩, k3⟩, k4⟩ := hr
    have hq' : 0 < r.2.2 := by
      have := hq
      rw [Nat.blt_eq] at this
      exact this
    exact ML_ge_of_okAt w hq' k0 k1 k2 k3 k4
  · right; right
    unfold ntMem at h4
    rw [List.any_eq_true] at h4
    obtain ⟨l, hl, hbeq⟩ := h4
    have : l = [w 0, w 1, w 2, w 3, w 4] := beq_iff_eq.mp hbeq
    rw [this] at hl
    exact hl

/-! ### the gcd of five naturals -/

def G5 (a b c d e : ℕ) : ℕ := Nat.gcd (Nat.gcd (Nat.gcd (Nat.gcd a b) c) d) e

theorem G5_dvd_a (a b c d e : ℕ) : G5 a b c d e ∣ a :=
  Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_trans (Nat.gcd_dvd_left _ _)
    (Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)))
theorem G5_dvd_b (a b c d e : ℕ) : G5 a b c d e ∣ b :=
  Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_trans (Nat.gcd_dvd_left _ _)
    (Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)))
theorem G5_dvd_c (a b c d e : ℕ) : G5 a b c d e ∣ c :=
  Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))
theorem G5_dvd_d (a b c d e : ℕ) : G5 a b c d e ∣ d :=
  Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
theorem G5_dvd_e (a b c d e : ℕ) : G5 a b c d e ∣ e := Nat.gcd_dvd_right _ _
theorem G5_greatest {k a b c d e : ℕ} (ha : k ∣ a) (hb : k ∣ b) (hc : k ∣ c) (hd : k ∣ d) (he : k ∣ e) :
    k ∣ G5 a b c d e :=
  Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd ha hb) hc) hd) he
theorem G5_pos {a b c d e : ℕ} (ha : 0 < a) : 0 < G5 a b c d e :=
  Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _
    (Nat.gcd_pos_of_pos_left _ ha)))

/-- **Box dichotomy, core form.**  A strictly increasing positive integer five-tuple with maximum at most `B` has
`1/5 <= ML`, or is a positive multiple of a tuple of the list `nt`. -/
theorem box_core (B : ℕ) (nt : List (List ℕ)) (ex : List (List ℕ × ℕ × ℕ))
    (hm : ∀ a b c d e : ℕ, 1 ≤ a → a < b → b < c → c < d → d < e → e ≤ B → tupleOK nt ex a b c d e = true)
    (v : Fin 5 → ℤ) (h0 : 0 < v 0) (h01 : v 0 < v 1) (h12 : v 1 < v 2) (h23 : v 2 < v 3) (h34 : v 3 < v 4)
    (hB : v 4 ≤ B) :
    (1 : ℝ) / 5 ≤ ML v ∨ ∃ (g : ℕ) (u : Fin 5 → ℕ), 0 < g ∧ (∀ i, v i = (g : ℤ) * (u i : ℤ)) ∧
      [u 0, u 1, u 2, u 3, u 4] ∈ nt := by
  -- natural-number version of v
  have hpos : ∀ i, 0 < v i := by
    intro i
    fin_cases i <;> simp <;> omega
  set n : Fin 5 → ℕ := fun i => (v i).toNat with hn
  have hnv : ∀ i, (n i : ℤ) = v i := fun i => Int.toNat_of_nonneg (hpos i).le
  have hn0 : 0 < n 0 := by have := hnv 0; have := hpos 0; omega
  have hn01 : n 0 < n 1 := by have := hnv 0; have := hnv 1; omega
  have hn12 : n 1 < n 2 := by have := hnv 1; have := hnv 2; omega
  have hn23 : n 2 < n 3 := by have := hnv 2; have := hnv 3; omega
  have hn34 : n 3 < n 4 := by have := hnv 3; have := hnv 4; omega
  have hnB : n 4 ≤ B := by have := hnv 4; omega
  set g : ℕ := G5 (n 0) (n 1) (n 2) (n 3) (n 4) with hgdef
  have hg : 0 < g := G5_pos hn0
  have d0 : g ∣ n 0 := G5_dvd_a _ _ _ _ _
  have d1 : g ∣ n 1 := G5_dvd_b _ _ _ _ _
  have d2 : g ∣ n 2 := G5_dvd_c _ _ _ _ _
  have d3 : g ∣ n 3 := G5_dvd_d _ _ _ _ _
  have d4 : g ∣ n 4 := G5_dvd_e _ _ _ _ _
  set u : Fin 5 → ℕ := fun i => n i / g with hu
  have hu0 : n 0 = g * u 0 := (Nat.mul_div_cancel' d0).symm
  have hu1 : n 1 = g * u 1 := (Nat.mul_div_cancel' d1).symm
  have hu2 : n 2 = g * u 2 := (Nat.mul_div_cancel' d2).symm
  have hu3 : n 3 = g * u 3 := (Nat.mul_div_cancel' d3).symm
  have hu4 : n 4 = g * u 4 := (Nat.mul_div_cancel' d4).symm
  have u0pos : 1 ≤ u 0 := by
    rcases Nat.eq_zero_or_pos (u 0) with h | h
    · rw [h] at hu0; omega
    · exact h
  have u01 : u 0 < u 1 := Nat.lt_of_mul_lt_mul_left (a := g) (by rw [← hu0, ← hu1]; exact hn01)
  have u12 : u 1 < u 2 := Nat.lt_of_mul_lt_mul_left (a := g) (by rw [← hu1, ← hu2]; exact hn12)
  have u23 : u 2 < u 3 := Nat.lt_of_mul_lt_mul_left (a := g) (by rw [← hu2, ← hu3]; exact hn23)
  have u34 : u 3 < u 4 := Nat.lt_of_mul_lt_mul_left (a := g) (by rw [← hu3, ← hu4]; exact hn34)
  have u4B : u 4 ≤ B := by
    have : u 4 ≤ g * u 4 := Nat.le_mul_of_pos_left _ hg
    omega
  have hprim : G5 (u 0) (u 1) (u 2) (u 3) (u 4) = 1 := by
    set k := G5 (u 0) (u 1) (u 2) (u 3) (u 4) with hk
    have k0 : k ∣ u 0 := G5_dvd_a _ _ _ _ _
    have k1 : k ∣ u 1 := G5_dvd_b _ _ _ _ _
    have k2 : k ∣ u 2 := G5_dvd_c _ _ _ _ _
    have k3 : k ∣ u 3 := G5_dvd_d _ _ _ _ _
    have k4 : k ∣ u 4 := G5_dvd_e _ _ _ _ _
    have gk : g * k ∣ g := by
      have := G5_greatest (k := g * k) (a := n 0) (b := n 1) (c := n 2) (d := n 3) (e := n 4)
        (by rw [hu0]; exact Nat.mul_dvd_mul_left g k0) (by rw [hu1]; exact Nat.mul_dvd_mul_left g k1)
        (by rw [hu2]; exact Nat.mul_dvd_mul_left g k2) (by rw [hu3]; exact Nat.mul_dvd_mul_left g k3)
        (by rw [hu4]; exact Nat.mul_dvd_mul_left g k4)
      exact this
    have : k ∣ 1 := Nat.dvd_of_mul_dvd_mul_left hg (by rw [Nat.mul_one]; exact gk)
    exact Nat.dvd_one.mp this
  have hok := hm (u 0) (u 1) (u 2) (u 3) (u 4) u0pos u01 u12 u23 u34 u4B
  have hvu : v = fun i => (g : ℤ) * (u i : ℤ) := by
    funext i
    rw [← hnv i]
    have : n i = g * u i := by
      fin_cases i
      · exact hu0
      · exact hu1
      · exact hu2
      · exact hu3
      · exact hu4
    rw [this]; push_cast; ring
  rcases tupleOK_spec u hok with hg1 | hml | hmem
  · exact absurd hprim hg1
  · left
    rw [hvu, ML_smul (g : ℤ) (by exact_mod_cast hg) (fun i => (u i : ℤ))]
    exact hml
  · right
    exact ⟨g, u, hg, fun i => by rw [hvu], hmem⟩

end L5W
