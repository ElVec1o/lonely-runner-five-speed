/-
# L5S4.LinSound : soundness of the flat five-speed line checker `classLinesB` (stage S4 block 16)

`classLinesB_sound` : if `classLinesB g = true` for a class record `g` (layout of `LinCore`), then every primitive `u` with nonzero
pairwise distinct absolute entries, orthogonal to the three rows `l` of the record and with `|u|^2` in one of its ranges, is
equal (up to a signed permutation) to a stored residual tuple of `T5V`, or satisfies `1/5 <= ML u`.
`classLinesB_inClass` states this in the form of the `lines` clause of `TreeHyp` (`InClass cl u` for any `T4Rec` whose rows and
ranges are read from the record).

Proof outline (as `L4S5.LinesSound`): (1) `u = x k0 + y k1` with `x = q0 . u`, `y = q1 . u` from `k^T q + p^T l = I`;
(2) `gcd(x, y) = 1` from primitivity; (3) sign: `-u` has the same absolute values, so `y >= 0` and `y = 0 -> x = 1`;
(4) the box: `c n = (c y + b x)^2 + D x^2`, `a n = (a x + b y)^2 + D y^2` with `D > 0` and `n <= nmax` give `|x| <= X`, `|y| <= Y`;
(5) the loop value at `(x, y)` is true and its guard holds, so a time of `TL5` works (`timeOk5_sound`) or a residual tuple matches.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.LinCore
import LRSpectrumFull.L5S4.Records
import LRSpectrumFull.L5S4.Radius

namespace LRSpectrumFull
namespace L5S4
namespace Lin

open Finset LRSpectrumFull.L5S3

noncomputable section

/-! ## 1. The time test and its soundness (five runners, threshold `1/5`) -/

def TimeOk5 (s : V5) (a q : ℤ) : Prop :=
  0 < q ∧ ∀ i, q ≤ 5 * min ((|s i| * a) % q) (q - (|s i| * a) % q)

theorem timeOk5_sound (s : V5) (a q : ℤ) (h : TimeOk5 s a q) : (1 : ℝ) / 5 ≤ ML s := by
  obtain ⟨hq, h⟩ := h
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hgap : (1 : ℝ) / 5 ≤ gap s ((a : ℝ) / q) := by
    apply le_gap
    intro i
    have e : nearestIntDist ((s i : ℝ) * ((a : ℝ) / q)) = nearestIntDist (((|s i| * a : ℤ) : ℝ) / q) := by
      rcases abs_choice (s i) with hh | hh
      · rw [hh]; congr 1; push_cast; ring
      · rw [hh]
        push_cast
        rw [show ((-(s i : ℝ)) * a / q) = -((s i : ℝ) * ((a : ℝ) / q)) by ring, nearestIntDist_neg]
    rw [e, nd_rat _ _ hq, le_div_iff₀ hqr]
    have : (q : ℝ) ≤ 5 * ((min ((|s i| * a) % q) (q - (|s i| * a) % q) : ℤ) : ℝ) := by exact_mod_cast h i
    linarith
  exact hgap.trans (le_csSup (bddAbove_range_gap s) ⟨_, rfl⟩)

/-- Negative control: `s = (1,2,3,4,5)` has no witness at `a/q = 1/5` (`5 · 1 mod 5 = 0`). -/
theorem planted_time5_bad : ¬ TimeOk5 ![1, 2, 3, 4, 5] 1 5 := by
  intro h
  have := h.2 4
  revert this
  decide +kernel

/-- the Bool test on one entry is the integer test. -/
theorem okN_iff (u : ℤ) (a q : ℕ) (hq : 0 < q) :
    okN u.natAbs a q = true ↔ (q : ℤ) ≤ 5 * min ((|u| * a) % q) ((q : ℤ) - (|u| * a) % q) := by
  have h1 : (((u.natAbs * a) % q : ℕ) : ℤ) = (|u| * a) % q := by
    push_cast [Int.natCast_natAbs]; rfl
  have hr0 : 0 ≤ (|u| * (a : ℤ)) % q := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
  have hr1 : (|u| * (a : ℤ)) % q < q := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
  unfold okN
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [← h1] at hr0 hr1 ⊢
  generalize ((u.natAbs * a) % q) = r at *
  constructor
  · rintro ⟨h2, h3⟩
    rw [min_def]; split_ifs <;> omega
  · intro h
    rw [min_def] at h
    split_ifs at h <;> constructor <;> omega

theorem tm_sound (s : V5) (p : ℕ × ℕ) (hq : 0 < p.2)
    (h : tmB (s 0).natAbs (s 1).natAbs (s 2).natAbs (s 3).natAbs (s 4).natAbs p = true) :
    TimeOk5 s (p.1 : ℤ) (p.2 : ℤ) := by
  refine ⟨by exact_mod_cast hq, fun i => ?_⟩
  unfold tmB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  fin_cases i
  · exact (okN_iff _ _ _ hq).1 h0
  · exact (okN_iff _ _ _ hq).1 h1
  · exact (okN_iff _ _ _ hq).1 h2
  · exact (okN_iff _ _ _ hq).1 h3
  · exact (okN_iff _ _ _ hq).1 h4

theorem TL5_pos : ∀ p ∈ TL5, 0 < p.2 := by decide +kernel

theorem t5V_ok : ∀ r ∈ T5V, r.length = 5 ∧ r.Nodup := by decide +kernel

/-! ## 2. A residual tuple gives a signed permutation -/

def T5Vec (r : List ℕ) : V5 := fun j => ((r.getD j.val 0 : ℕ) : ℤ)

theorem getD_zero_eq (r : List ℕ) (j : ℕ) (h : j < r.length) : r.getD j 0 = r[j] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem exists_sp_of_mem (u : V5) (hnz : ∀ i, u i ≠ 0) (r : List ℕ) (hl : r.length = 5) (hnd : r.Nodup)
    (h : ∀ e ∈ r, ∃ i : Fin 5, (u i).natAbs = e) : ∃ s : SP, s.act u = T5Vec r := by
  have hmem : ∀ j : Fin 5, r.getD j.val 0 ∈ r := by
    intro j
    rw [getD_zero_eq _ _ (by omega)]
    exact List.getElem_mem _
  choose f hf using fun j : Fin 5 => h _ (hmem j)
  have hinj : Function.Injective f := by
    intro j j' hjj
    have e : r.getD j.val 0 = r.getD j'.val 0 := by rw [← hf j, ← hf j', hjj]
    rw [getD_zero_eq _ _ (by omega), getD_zero_eq _ _ (by omega)] at e
    have := (List.Nodup.getElem_inj_iff hnd).1 e
    exact Fin.ext this
  let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  refine ⟨⟨σ, fun j => if 0 ≤ u (σ j) then 1 else -1, fun j => by by_cases hh : 0 ≤ u (σ j) <;> simp [hh]⟩, ?_⟩
  funext j
  simp only [SP.act, T5Vec]
  have hj := hf j
  have hs : σ j = f j := rfl
  rw [hs]
  by_cases hh : 0 ≤ u (f j)
  · simp only [hh, if_true, one_mul]
    rw [← hj]; exact (Int.natCast_natAbs _).symm ▸ (abs_of_nonneg hh).symm
  · have : u (f j) < 0 := lt_of_not_ge hh
    simp only [hh, if_false]
    rw [← hj, Int.natCast_natAbs, abs_of_neg this]; ring

/-! ## 3. The witness predicate -/

theorem pb_sound (w : V5) (hnz : ∀ i, w i ≠ 0) (g : Nat → Int) (x y : Int)
    (hw : ∀ i : Fin 5, (x * g (26 + i.val) + y * g (31 + i.val)).natAbs = (w i).natAbs)
    (h : pbB g x y = true) :
    (∃ r ∈ T5V, ∃ s : SP, s.act w = T5Vec r) ∨ (1 : ℝ) / 5 ≤ ML w := by
  have e3' : (x * g 29 + y * g 34).natAbs = (w 3).natAbs := hw 3
  have e4' : (x * g 30 + y * g 35).natAbs = (w 4).natAbs := hw 4
  have e0' : (x * g 26 + y * g 31).natAbs = (w 0).natAbs := hw 0
  have e1' : (x * g 27 + y * g 32).natAbs = (w 1).natAbs := hw 1
  have e2' : (x * g 28 + y * g 33).natAbs = (w 2).natAbs := hw 2
  unfold pbB at h
  rw [e0', e1', e2', e3', e4'] at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · right
    unfold witB at h
    rw [List.any_eq_true] at h
    obtain ⟨p, hp, hpt⟩ := h
    exact timeOk5_sound w p.1 p.2 (tm_sound w p (TL5_pos p hp) hpt)
  · left
    unfold t5B at h
    rw [List.any_eq_true] at h
    obtain ⟨r, hr, hall⟩ := h
    obtain ⟨hl, hnd⟩ := t5V_ok r hr
    refine ⟨r, hr, exists_sp_of_mem w hnz r hl hnd ?_⟩
    intro e he
    rw [List.all_eq_true] at hall
    have := hall e he
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with ((((h0 | h1) | h2) | h3) | h4)
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
    · exact ⟨3, h3⟩
    · exact ⟨4, h4⟩

/-! ## 4. The guard -/

theorem guard_of_facts (g : Nat → Int) (nr : Nat) (a b c x y : Int)
    (hrg : ∃ j < nr, g (62 + 2 * j) ≤ a * x * x + 2 * b * x * y + c * y * y ∧ a * x * x + 2 * b * x * y + c * y * y ≤ g (63 + 2 * j))
    (hgcd : Int.gcd x y = 1)
    (hnz : ∀ i : Fin 5, x * g (26 + i.val) + y * g (31 + i.val) ≠ 0)
    (hd : ∀ i j : Fin 5, i ≠ j → |x * g (26 + i.val) + y * g (31 + i.val)| ≠ |x * g (26 + j.val) + y * g (31 + j.val)|) :
    guardB g nr a b c x y = true := by
  have hd' : ∀ i j : Fin 5, i ≠ j →
      (x * g (26 + i.val) + y * g (31 + i.val)).natAbs ≠ (x * g (26 + j.val) + y * g (31 + j.val)).natAbs := by
    intro i j hij h
    apply hd i j hij
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs, h]
  have n0 : x * g 26 + y * g 31 ≠ 0 := hnz 0
  have n1 : x * g 27 + y * g 32 ≠ 0 := hnz 1
  have n2 : x * g 28 + y * g 33 ≠ 0 := hnz 2
  have n3 : x * g 29 + y * g 34 ≠ 0 := hnz 3
  have n4 : x * g 30 + y * g 35 ≠ 0 := hnz 4
  have d01 : (x * g 26 + y * g 31).natAbs ≠ (x * g 27 + y * g 32).natAbs := hd' 0 1 (by decide)
  have d02 : (x * g 26 + y * g 31).natAbs ≠ (x * g 28 + y * g 33).natAbs := hd' 0 2 (by decide)
  have d03 : (x * g 26 + y * g 31).natAbs ≠ (x * g 29 + y * g 34).natAbs := hd' 0 3 (by decide)
  have d04 : (x * g 26 + y * g 31).natAbs ≠ (x * g 30 + y * g 35).natAbs := hd' 0 4 (by decide)
  have d12 : (x * g 27 + y * g 32).natAbs ≠ (x * g 28 + y * g 33).natAbs := hd' 1 2 (by decide)
  have d13 : (x * g 27 + y * g 32).natAbs ≠ (x * g 29 + y * g 34).natAbs := hd' 1 3 (by decide)
  have d14 : (x * g 27 + y * g 32).natAbs ≠ (x * g 30 + y * g 35).natAbs := hd' 1 4 (by decide)
  have d23 : (x * g 28 + y * g 33).natAbs ≠ (x * g 29 + y * g 34).natAbs := hd' 2 3 (by decide)
  have d24 : (x * g 28 + y * g 33).natAbs ≠ (x * g 30 + y * g 35).natAbs := hd' 2 4 (by decide)
  have d34 : (x * g 29 + y * g 34).natAbs ≠ (x * g 30 + y * g 35).natAbs := hd' 3 4 (by decide)
  have hin : inRangeB g nr (a * x * x + 2 * b * x * y + c * y * y) = true := by
    unfold inRangeB
    rw [List.any_eq_true]
    obtain ⟨j, hj, h1, h2⟩ := hrg
    exact ⟨j, List.mem_range.2 hj, by simp [h1, h2]⟩
  unfold guardB
  simp only [hin, Bool.true_and, true_and, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, and_assoc]
  refine ⟨hgcd, n0, n1, n2, n3, n4, d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩

end

end Lin
end L5S4
end LRSpectrumFull
