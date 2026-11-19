/-
# L5S5.FiveSpeedOfTree : the five-speed spectrum below `1/5`, from the tree theorem as an explicit hypothesis

`five_speed_spectrum_of_tree` : if the tree theorem `TreeThm5 Res` holds (every near-tight `v` with distinct absolute entries is,
up to a signed permutation, on a critical torus of kind `(1,2,3,4)` or `(1,3,4,7)`, or equals a residual tuple of `Res`) and
every residual tuple consists of pairwise distinct positive integers `<= 45`, then for every five distinct positive integer
speeds `v` with `ML v < 1/5` there is an integer `s ≥ 1` with `ML v = s/(5s+1)`.

`five_speed_spectrum_of_stream` : the same with the tree theorem replaced by the stream hypothesis `StreamHyp'` of
`L5S4.Induct2` (through `tree_complete_unconditional'`); residual tuples are the stored `C.t5` records.

Cases of the proof (mirrors `L4S5.FinalSpectrum`): normalisation `v = d w`, `w` primitive (E11), `ML (d w) = ML w`;
critical torus: `u = (A V, B)` for `V ∈ {(1,2,3,4),(1,3,4,7)}`, signs removed by `nf_ML_signs`, then `A ≥ 2` or `5 ∤ B` give
`1/5 ≤ ML` (`ObsKS5Tail` Lemmas N and P), else `B = 5s` and the exact value is `ML_V1_eq` / `ML_V2_eq` / `ML_V2_s1_eq`;
residual tuple: `L5W.box_unordered 45` (the 25 tuples of `T5V` have entries `<= 35`).

`five_speed_attained`, `five_speed_spectrum_iff`: every `s ≥ 1` occurs, by `(1,2,3,4,5s)`.

Not covered: repeated speeds, zero speeds, non-integer speeds, fewer or more than five speeds.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.Induct2
import LRSpectrumFull.ObsKS5Tail
import LRSpectrumFull.L4Tail.NormalForm
import LRSpectrumFull.L5WP1.BoxPerm
import LRSpectrumFull.L5WP1.BoxFinal45

namespace LRSpectrumFull
namespace L5S5

open LRSpectrumFull.L5S3 LRSpectrumFull.L5S4

/-! ## 1. Statements -/

/-- Residual tuples must be five distinct positive integers `<= 45` (the box of `L5W.box45`). -/
def ResOK (r : V5) : Prop := Function.Injective r ∧ ∀ i, 0 < r i ∧ r i ≤ 45

/-- The tree theorem, as a hypothesis for the development (it is `L5S4.tree_complete_unconditional'` for the stream
hypothesis, see `treeThm5_of_stream`). -/
def TreeThm5 (Res : V5 → Prop) : Prop :=
  ∀ v : V5, NearTight v → (∀ i j, i ≠ j → |v i| ≠ |v j|) →
    (∃ (k : Fin 2) (g : SP), CritTorus k (g.act v)) ∨ (∃ r, Res r ∧ ∃ g : SP, g.act v = r)

theorem treeThm5_of_stream {C : Certificate} {R1 : Set (NodeW 1 4)} {R2 : Set (NodeW 2 3)}
    (H : StreamHyp' C R1 R2) : TreeThm5 (fun r => ∃ r' ∈ C.t5, r'.v = r) := by
  intro v hnt hdist
  rcases tree_complete_unconditional' H v hnt hdist with hc | ⟨r, hr, g, hg⟩
  · exact Or.inl hc
  · exact Or.inr ⟨r.v, ⟨r, hr, rfl⟩, g, hg⟩

/-! ## 2. Normalisation -/

/-- A vector of positive integers is `d ≥ 1` times a primitive vector of positive integers. -/
theorem exists_prim5 (v : V5) (hpos : ∀ i, 0 < v i) :
    ∃ d : ℤ, 1 ≤ d ∧ ∃ w : V5, Primitive w ∧ (∀ i, 0 < w i) ∧ (∀ i, v i = d * w i) := by
  set d : ℤ := Finset.univ.gcd v with hd
  have hdv : ∀ i, d ∣ v i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
  have hd0 : d ≠ 0 := by
    intro h0
    have := (Finset.gcd_eq_zero_iff.1 h0) 0 (Finset.mem_univ _)
    exact (hpos 0).ne' this
  have hdn : 0 ≤ d := Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd)
  have hd1 : 1 ≤ d := by omega
  choose w hw using hdv
  refine ⟨d, hd1, w, ?_, ?_, hw⟩
  · intro e he
    have h1 : ∀ i, d * e ∣ v i := by
      intro i
      rw [hw i]
      exact mul_dvd_mul_left d (he i)
    have h2 : d * e ∣ d := Finset.dvd_gcd (fun i _ => h1 i)
    have h3 : d * e ∣ d * 1 := by simpa using h2
    have h4 : e ∣ 1 := (mul_dvd_mul_iff_left hd0).1 h3
    exact Int.isUnit_iff.mp (isUnit_of_dvd_one h4)
  · intro i
    have := hpos i
    rw [hw i] at this
    by_contra hneg
    have : d * w i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hdn (by omega)
    omega

/-! ## 3. Critical tori -/

/-- Exact value on `(A V, B)` with `V = (1,2,3,4)`, `A, B ≥ 1` coprime, when `ML < 1/5`. -/
theorem crit_core1 (A B : ℤ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hc : IsCoprime A B)
    (hlt : ML (![A * 1, A * 2, A * 3, A * 4, B] : Fin 5 → ℤ) < 1 / 5) :
    ∃ s : ℕ, 1 ≤ s ∧ ML (![A * 1, A * 2, A * 3, A * 4, B] : Fin 5 → ℤ) = (s : ℝ) / (5 * s + 1) := by
  by_cases hA2 : 2 ≤ A
  · exact absurd (KS5Tail.thm1_i_A_ge_two_V1 A B hA2 hc) (not_le.2 hlt)
  · have hA1 : A = 1 := by omega
    subst hA1
    by_cases h5 : (5 : ℤ) ∣ B
    · obtain ⟨s, hs⟩ := h5
      have hs0 : 0 ≤ s := by omega
      lift s to ℕ using hs0
      have hs1 : 1 ≤ s := by omega
      have e : (![1 * 1, 1 * 2, 1 * 3, 1 * 4, B] : Fin 5 → ℤ) = ![1, 2, 3, 4, 5 * (s : ℤ)] := by
        funext i; fin_cases i <;> simp [hs]
      rw [e]
      exact ⟨s, hs1, KS5Tail.ML_V1_eq s hs1⟩
    · have e : (![1 * 1, 1 * 2, 1 * 3, 1 * 4, B] : Fin 5 → ℤ) = ![1, 2, 3, 4, B] := by
        funext i; fin_cases i <;> simp
      rw [e] at hlt
      exact absurd (KS5Tail.thm1_i_A_one_V1 B h5) (not_le.2 hlt)

/-- Exact value on `(A V, B)` with `V = (1,3,4,7)`, `A, B ≥ 1` coprime, when `ML < 1/5`. -/
theorem crit_core2 (A B : ℤ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hc : IsCoprime A B)
    (hlt : ML (![A * 1, A * 3, A * 4, A * 7, B] : Fin 5 → ℤ) < 1 / 5) :
    ∃ s : ℕ, 1 ≤ s ∧ ML (![A * 1, A * 3, A * 4, A * 7, B] : Fin 5 → ℤ) = (s : ℝ) / (5 * s + 1) := by
  by_cases hA2 : 2 ≤ A
  · exact absurd (KS5Tail.thm1_i_A_ge_two_V2 A B hA2 hc) (not_le.2 hlt)
  · have hA1 : A = 1 := by omega
    subst hA1
    by_cases h5 : (5 : ℤ) ∣ B
    · obtain ⟨s, hs⟩ := h5
      have hs0 : 0 ≤ s := by omega
      lift s to ℕ using hs0
      have hs1 : 1 ≤ s := by omega
      by_cases hs2 : 2 ≤ s
      · have e : (![1 * 1, 1 * 3, 1 * 4, 1 * 7, B] : Fin 5 → ℤ) = ![1, 3, 4, 7, 5 * (s : ℤ)] := by
          funext i; fin_cases i <;> simp [hs]
        rw [e]
        exact ⟨s, hs1, KS5Tail.ML_V2_eq s hs2⟩
      · have hs1' : s = 1 := by omega
        subst hs1'
        have e : (![1 * 1, 1 * 3, 1 * 4, 1 * 7, B] : Fin 5 → ℤ) = ![1, 3, 4, 7, 5] := by
          funext i; fin_cases i <;> simp [hs]
        rw [e, KS5Tail.ML_V2_s1_eq]
        refine ⟨2, by norm_num, ?_⟩
        norm_num
    · have e : (![1 * 1, 1 * 3, 1 * 4, 1 * 7, B] : Fin 5 → ℤ) = ![1, 3, 4, 7, B] := by
        funext i; fin_cases i <;> simp
      rw [e] at hlt
      exact absurd (KS5Tail.thm1_i_A_one_V2 B h5) (not_le.2 hlt)

/-- Removing the signs of `A` and `B` from a point of a critical torus. -/
theorem sign_flip (A B : ℤ) (hA : A ≠ 0) (hB : B ≠ 0) (V : Fin 4 → ℤ) (u : V5)
    (hu : ∀ i : Fin 4, u i.castSucc = A * V i) (h4 : u 4 = B) :
    ML u = ML (![|A| * V 0, |A| * V 1, |A| * V 2, |A| * V 3, |B|] : Fin 5 → ℤ) := by
  have hsg : ∀ x : ℤ, x ≠ 0 → (if 0 < x then (1 : ℤ) else -1) * x = |x| := by
    intro x hx
    by_cases h : 0 < x
    · simp [h, abs_of_pos h]
    · have : x < 0 := lt_of_le_of_ne (not_lt.1 h) hx
      simp [h, abs_of_neg this]
  have hpm : ∀ x : ℤ, (if 0 < x then (1 : ℤ) else -1) = 1 ∨ (if 0 < x then (1 : ℤ) else -1) = -1 := by
    intro x; split_ifs <;> simp
  obtain ⟨sa, hsa1, ga⟩ : ∃ sa : ℤ, (sa = 1 ∨ sa = -1) ∧ sa * A = |A| := ⟨_, hpm A, hsg A hA⟩
  obtain ⟨sb, hsb1, gb⟩ : ∃ sb : ℤ, (sb = 1 ∨ sb = -1) ∧ sb * B = |B| := ⟨_, hpm B, hsg B hB⟩
  have hεpm : ∀ i : Fin 5, (![sa, sa, sa, sa, sb] : Fin 5 → ℤ) i = 1 ∨ (![sa, sa, sa, sa, sb] : Fin 5 → ℤ) i = -1 := by
    intro i; fin_cases i
    · simpa using hsa1
    · simpa using hsa1
    · simpa using hsa1
    · simpa using hsa1
    · simpa using hsb1
  have h := L4Tail.nf_ML_signs (![sa, sa, sa, sa, sb] : Fin 5 → ℤ) u hεpm
  rw [← h]
  have e0 : u 0 = A * V 0 := hu 0
  have e1 : u 1 = A * V 1 := hu 1
  have e2 : u 2 = A * V 2 := hu 2
  have e3 : u 3 = A * V 3 := hu 3
  congr 1
  funext i
  fin_cases i
  · show sa * u 0 = |A| * V 0
    rw [e0, ← ga]; ring
  · show sa * u 1 = |A| * V 1
    rw [e1, ← ga]; ring
  · show sa * u 2 = |A| * V 2
    rw [e2, ← ga]; ring
  · show sa * u 3 = |A| * V 3
    rw [e3, ← ga]; ring
  · show sb * u 4 = |B|
    rw [h4, gb]

/-- Primitive point of a critical torus: `A` and `B` are coprime. -/
theorem crit_coprime (A B : ℤ) (V : Fin 4 → ℤ) (u : V5) (hprim : Primitive u)
    (hu : ∀ i : Fin 4, u i.castSucc = A * V i) (h4 : u 4 = B) : IsCoprime A B := by
  have e0 : u 0 = A * V 0 := hu 0
  have e1 : u 1 = A * V 1 := hu 1
  have e2 : u 2 = A * V 2 := hu 2
  have e3 : u 3 = A * V 3 := hu 3
  have hg : Int.gcd A B = 1 := by
    have hdA : ((Int.gcd A B : ℕ) : ℤ) ∣ A := Int.gcd_dvd_left A B
    have hdB : ((Int.gcd A B : ℕ) : ℤ) ∣ B := Int.gcd_dvd_right A B
    have := hprim ((Int.gcd A B : ℕ) : ℤ) (by
      intro i; fin_cases i
      · show _ ∣ u 0; rw [e0]; exact Dvd.dvd.mul_right hdA _
      · show _ ∣ u 1; rw [e1]; exact Dvd.dvd.mul_right hdA _
      · show _ ∣ u 2; rw [e2]; exact Dvd.dvd.mul_right hdA _
      · show _ ∣ u 3; rw [e3]; exact Dvd.dvd.mul_right hdA _
      · show _ ∣ u 4; rw [h4]; exact hdB)
    omega
  exact Int.isCoprime_iff_gcd_eq_one.2 hg

theorem coprime_abs {A B : ℤ} (h : IsCoprime A B) : IsCoprime |A| |B| := by
  have hg : Int.gcd A B = 1 := Int.isCoprime_iff_gcd_eq_one.1 h
  apply Int.isCoprime_iff_gcd_eq_one.2
  rw [Int.gcd_eq_natAbs, Int.natAbs_abs, Int.natAbs_abs, ← Int.gcd_eq_natAbs]
  exact hg

/-- A primitive point `u` of a critical torus with `ML u < 1/5` has `ML u = s/(5s+1)`, `s ≥ 1`. -/
theorem crit_value (k : Fin 2) (u : V5) (hc : CritTorus k u) (hprim : Primitive u) (hnz : ∀ i, u i ≠ 0)
    (hlt : ML u < 1 / 5) : ∃ s : ℕ, 1 ≤ s ∧ ML u = (s : ℝ) / (5 * s + 1) := by
  obtain ⟨A, B, hu, h4⟩ := hc
  have hA : A ≠ 0 := by
    intro h0
    have := hnz (Fin.castSucc 0)
    rw [hu 0, h0] at this
    simp at this
  have hB : B ≠ 0 := by rw [← h4]; exact hnz 4
  have hcop := coprime_abs (crit_coprime A B _ u hprim hu h4)
  have hA1 : 1 ≤ |A| := abs_pos.2 hA
  have hB1 : 1 ≤ |B| := abs_pos.2 hB
  by_cases hk : k = 0
  · have hu' : ∀ i : Fin 4, u i.castSucc = A * (![1, 2, 3, 4] : Fin 4 → ℤ) i := by
      intro i; simpa [hk] using hu i
    rw [sign_flip A B hA hB _ u hu' h4] at hlt ⊢
    simpa using crit_core1 |A| |B| hA1 hB1 hcop (by simpa using hlt)
  · have hu' : ∀ i : Fin 4, u i.castSucc = A * (![1, 3, 4, 7] : Fin 4 → ℤ) i := by
      intro i; simpa [hk] using hu i
    rw [sign_flip A B hA hB _ u hu' h4] at hlt ⊢
    simpa using crit_core2 |A| |B| hA1 hB1 hcop (by simpa using hlt)

/-! ## 4. Residual tuples -/

theorem res_value (r : V5) (hr : ResOK r) (hlt : ML r < 1 / 5) :
    ∃ s : ℕ, 1 ≤ s ∧ ML r = (s : ℝ) / (5 * s + 1) :=
  (L5W.box_unordered 45 L5W.nt45 L5W.ex45 L5W.tupleOK45 L5W.ntvals45 r hr.1 (fun i => (hr.2 i).1)
    (fun i => (hr.2 i).2)).2 hlt

/-! ## 5. The theorem -/

/-- **The five-speed spectrum below `1/5`**, from the tree theorem. -/
theorem five_speed_spectrum_of_tree {Res : V5 → Prop} (hRes : ∀ r, Res r → ResOK r) (hT : TreeThm5 Res)
    (v : Fin 5 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) (hlt : ML v < 1 / 5) :
    ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1) := by
  obtain ⟨d, hd1, w, hprim, hwpos, hvw⟩ := exists_prim5 v hpos
  have hv : v = fun i => d * w i := funext hvw
  have hML : ML v = ML w := by
    rw [hv]; exact L4Tail.nf_ML_smul d (by omega) w
  rw [hML] at hlt ⊢
  have hnz : ∀ i, w i ≠ 0 := fun i => (hwpos i).ne'
  have hdist : ∀ i j, i ≠ j → |w i| ≠ |w j| := by
    intro i j hij h
    rw [abs_of_pos (hwpos i), abs_of_pos (hwpos j)] at h
    apply hij
    apply hinj
    rw [hvw i, hvw j, h]
  rcases hT w ⟨hprim, hnz, hlt⟩ hdist with ⟨k, g, hc⟩ | ⟨r, hr, g, hg⟩
  · have hml : ML (g.act w) = ML w := ML_act g w
    rw [← hml] at hlt ⊢
    exact crit_value k (g.act w) hc (primitive_act hprim g) (nz_act hnz g) hlt
  · have hml : ML w = ML r := by rw [← hg, ML_act]
    rw [hml] at hlt ⊢
    exact res_value r (hRes r hr) hlt

/-- Same, from the stream hypothesis of `L5S4.Induct2`; residual tuples are the stored `C.t5` records. -/
theorem five_speed_spectrum_of_stream {C : Certificate} {R1 : Set (NodeW 1 4)} {R2 : Set (NodeW 2 3)}
    (H : StreamHyp' C R1 R2) (hres : ∀ r ∈ C.t5, ResOK r.v)
    (v : Fin 5 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) (hlt : ML v < 1 / 5) :
    ∃ s : ℕ, 1 ≤ s ∧ ML v = (s : ℝ) / (5 * s + 1) :=
  five_speed_spectrum_of_tree (Res := fun r => ∃ r' ∈ C.t5, r'.v = r)
    (fun r ⟨r', hr', e⟩ => e ▸ hres r' hr') (treeThm5_of_stream H) v hpos hinj hlt

/-- **Attainment**: every `s ≥ 1` occurs, by five distinct positive integer speeds. -/
theorem five_speed_attained (s : ℕ) (hs : 1 ≤ s) :
    ∃ v : Fin 5 → ℤ, (∀ i, 0 < v i) ∧ Function.Injective v ∧ ML v = (s : ℝ) / (5 * s + 1) := by
  have hs' : (1 : ℤ) ≤ s := by exact_mod_cast hs
  refine ⟨![1, 2, 3, 4, 5 * (s : ℤ)], ?_, ?_, KS5Tail.ML_V1_eq s hs⟩
  · intro i; fin_cases i <;> simp <;> omega
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega

/-- The set of values `< 1/5` of `ML` on five distinct positive integer speeds is `{s/(5s+1) : s ≥ 1}`, given the tree. -/
theorem five_speed_spectrum_iff {Res : V5 → Prop} (hRes : ∀ r, Res r → ResOK r) (hT : TreeThm5 Res) (x : ℝ) :
    (∃ v : Fin 5 → ℤ, (∀ i, 0 < v i) ∧ Function.Injective v ∧ ML v = x ∧ x < 1 / 5) ↔
      ∃ s : ℕ, 1 ≤ s ∧ x = (s : ℝ) / (5 * s + 1) := by
  constructor
  · rintro ⟨v, hp, hi, rfl, hx⟩
    exact five_speed_spectrum_of_tree hRes hT v hp hi hx
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨v, h1, h2, h3⟩ := five_speed_attained s hs
    refine ⟨v, h1, h2, h3, ?_⟩
    have hr : (1 : ℝ) ≤ s := by exact_mod_cast hs
    rw [div_lt_iff₀ (by linarith)]
    linarith

/-! ## Controls -/

theorem ctl_not_one_seventh {Res : V5 → Prop} (hRes : ∀ r, Res r → ResOK r) (hT : TreeThm5 Res)
    (v : Fin 5 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) : ML v ≠ 1 / 7 := by
  intro h
  obtain ⟨s, hs, hv⟩ := five_speed_spectrum_of_tree hRes hT v hpos hinj (by rw [h]; norm_num)
  rw [h] at hv
  have hr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  field_simp at hv
  linarith

theorem ctl_not_three_seventeenths {Res : V5 → Prop} (hRes : ∀ r, Res r → ResOK r) (hT : TreeThm5 Res)
    (v : Fin 5 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) : ML v ≠ 3 / 17 := by
  intro h
  obtain ⟨s, hs, hv⟩ := five_speed_spectrum_of_tree hRes hT v hpos hinj (by rw [h]; norm_num)
  rw [h] at hv
  have hr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  field_simp at hv
  have h2 : (2 * (s : ℝ)) = 3 := by linarith
  have h3 : (2 * s : ℕ) = 3 := by exact_mod_cast h2
  omega

end L5S5
end LRSpectrumFull
