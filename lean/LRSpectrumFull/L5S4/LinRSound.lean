/-
# L5S4.LinRSound : soundness of the row-interval five-speed line checker `classLinesR` (case-tree certificate, part 17)

`classLinesR_sound` has the hypotheses and the conclusion of `LinSound2.classLinesB_sound`, with the class record `g` and ONE more
natural `W` (the row data and the per-point hints; layout in `LinRCore`):
every primitive `u` with nonzero pairwise distinct absolute entries, orthogonal to the three rows `l` of the record and with `|u|^2`
in the range of the record is a signed permutation of a residual tuple of `T5V`, or satisfies `1/5 <= ML u`.

Five sub-lemmas:
* W1 `rowsOk_sound`  : induction over the rows `y = 1 .. Y`: every in-range `(x, y)` is a visited point with a hint that passes;
* W2 `segOk_sound`   : induction over the walk of one row (fuel `cnt`): every `x` of the walk is a visited point;
* W3 `rowChk_cover`  : `rowChk = true` forces `p < x < r` and `x` outside the hole `[g1, g2]` for every in-range `(x, y)`
  (`a n = z^2 + D y^2`, `z = a x + b y` increasing);
* W4 (inside W1)     : `p < x < r` and `x` outside `[g1, g2]` gives `x < g1` or `x > g2`, i.e. a point of one of the two walks;
* W5 `ptR_sound`     : a passing hint certifies the point: a time `t/q` (`timeOk5_sound`), a non-primitive point, a zero entry, two equal
  absolute entries, a residual tuple of `T5V`, or an out-of-range point; each excuse contradicts a hypothesis on `u`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.LinSound2
import LRSpectrumFull.L5S4.LinRCore

namespace LRSpectrumFull
namespace L5S4
namespace Lin

open Finset LRSpectrumFull.L5S3

noncomputable section

/-! ## W3: the row boundary check -/

theorem rowChk_cover (g : Nat → Int) (a b c y p g1 g2 r x : Int) (ha : 0 < a)
    (h : rowChk g a b c y p g1 g2 r = true)
    (hlo : g 62 ≤ a * x * x + 2 * b * x * y + c * y * y) (hhi : a * x * x + 2 * b * x * y + c * y * y ≤ g 63) :
    p < x ∧ x < r ∧ ¬ (g1 ≤ x ∧ x ≤ g2) := by
  unfold rowChk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have e : a * (a * x * x + 2 * b * x * y + c * y * y) = (a * x + b * y) ^ 2 + (a * c - b * b) * y * y := by ring
  have hhi' : a * (a * x * x + 2 * b * x * y + c * y * y) ≤ a * g 63 := mul_le_mul_of_nonneg_left hhi ha.le
  have hlo' : a * g 62 ≤ a * (a * x * x + 2 * b * x * y + c * y * y) := mul_le_mul_of_nonneg_left hlo ha.le
  refine ⟨?_, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    have hax : a * x ≤ a * p := mul_le_mul_of_nonneg_left hc ha.le
    have hsq : (a * p + b * y) * (a * p + b * y) ≤ (a * x + b * y) * (a * x + b * y) := by
      nlinarith [mul_nonneg (show 0 ≤ (a * p + b * y) - (a * x + b * y) by linarith)
        (show 0 ≤ -((a * x + b * y) + (a * p + b * y)) by linarith)]
    nlinarith [e, hhi', h2, hsq]
  · by_contra hc
    push_neg at hc
    have hax : a * r ≤ a * x := mul_le_mul_of_nonneg_left hc ha.le
    have hsq : (a * r + b * y) * (a * r + b * y) ≤ (a * x + b * y) * (a * x + b * y) := by
      nlinarith [mul_nonneg (show 0 ≤ (a * x + b * y) - (a * r + b * y) by linarith)
        (show 0 ≤ (a * x + b * y) + (a * r + b * y) by linarith)]
    nlinarith [e, hhi', h4, hsq]
  · rintro ⟨hg1, hg2⟩
    rcases h5 with h5 | ⟨hA, hB⟩
    · omega
    · have hax1 : a * g1 ≤ a * x := mul_le_mul_of_nonneg_left hg1 ha.le
      have hax2 : a * x ≤ a * g2 := mul_le_mul_of_nonneg_left hg2 ha.le
      have hsq : (a * x + b * y) * (a * x + b * y) < a * g 62 - (a * c - b * b) * y * y := by
        rcases le_or_gt 0 (a * x + b * y) with hz | hz
        · nlinarith [mul_nonneg (show 0 ≤ (a * g2 + b * y) - (a * x + b * y) by linarith)
            (show 0 ≤ (a * g2 + b * y) + (a * x + b * y) by linarith)]
        · nlinarith [mul_nonneg (show 0 ≤ (a * x + b * y) - (a * g1 + b * y) by linarith)
            (show 0 ≤ -((a * g1 + b * y) + (a * x + b * y)) by linarith)]
      nlinarith [e, hlo', hsq]

/-! ## W2: one walk -/

theorem segOk_sound (g : Nat → Int) (a b c y : Int) :
    ∀ (cnt : Nat) (x0 : Int) (W : Nat), segOk g a b c y x0 cnt W = true →
      ∀ x : Int, x0 ≤ x → x < x0 + cnt → ∃ h, ptR g a b c x y h = true := by
  intro cnt
  induction cnt with
  | zero => intro x0 W _ x h1 h2; omega
  | succ n ih =>
    intro x0 W h x h1 h2
    simp only [segOk, Bool.and_eq_true] at h
    by_cases hx : x = x0
    · exact ⟨Nat.mod W 2048, by rw [hx]; exact h.1⟩
    · exact ih (x0 + 1) (Nat.shiftRight W 11) h.2 x (by omega) (by omega)

/-! ## W1 (with W4): the rows -/

theorem rowsOk_sound (g : Nat → Int) (a b c : Int) (ha : 0 < a) :
    ∀ (f y0 W : Nat), rowsOk g a b c f y0 W = true →
      ∀ (y : Nat), y0 ≤ y → y < y0 + f → ∀ x : Int,
        g 62 ≤ a * x * x + 2 * b * x * (y : Int) + c * (y : Int) * (y : Int) →
        a * x * x + 2 * b * x * (y : Int) + c * (y : Int) * (y : Int) ≤ g 63 →
        ∃ h, ptR g a b c x (y : Int) h = true := by
  intro f
  induction f with
  | zero => intro y0 W _ y h1 h2; omega
  | succ n ih =>
    intro y0 W h y hy1 hy2 x hlo hhi
    simp only [rowsOk, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hrow, hs1⟩, hs2⟩, hrec⟩ := h
    by_cases hyy : y = y0
    · subst hyy
      obtain ⟨hpx, hxr, hnh⟩ := rowChk_cover g a b c (y : Int) _ _ _ _ x ha hrow hlo hhi
      by_cases hx1 : x < dec16 W 16
      · exact segOk_sound g a b c (y : Int) _ _ _ hs1 x (by omega) (by omega)
      · have hx2 : dec16 W 32 < x := by
          by_contra hcon
          exact hnh ⟨by omega, by omega⟩
        exact segOk_sound g a b c (y : Int) _ _ _ hs2 x (by omega) (by omega)
    · exact ih (y0 + 1) _ hrec y (by omega) (by omega) x hlo hhi

/-! ## W5: one point -/

theorem T5V_getD_mem : ∀ t, t < 25 → T5V.getD t [] ∈ T5V := by decide +kernel

theorem pair_ok : ∀ t, t < 10 → pairA t < 5 ∧ pairB t < 5 ∧ pairA t ≠ pairB t := by decide +kernel

theorem ptR_sound (g : Nat → Int) (a b c x y : Int) (w : V5) (hnz : ∀ i, w i ≠ 0)
    (hdist : ∀ i j, i ≠ j → |w i| ≠ |w j|)
    (hw : ∀ i : Fin 5, (x * g (26 + i.val) + y * g (31 + i.val)).natAbs = (w i).natAbs)
    (hgcd : Int.gcd x y = 1)
    (hlo : g 62 ≤ a * x * x + 2 * b * x * y + c * y * y) (hhi : a * x * x + 2 * b * x * y + c * y * y ≤ g 63)
    (h : Nat) (hp : ptR g a b c x y h = true) :
    (∃ r ∈ T5V, ∃ s : SP, s.act w = T5Vec r) ∨ (1 : ℝ) / 5 ≤ ML w := by
  have e0 : (x * g 26 + y * g 31).natAbs = (w 0).natAbs := hw 0
  have e1 : (x * g 27 + y * g 32).natAbs = (w 1).natAbs := hw 1
  have e2 : (x * g 28 + y * g 33).natAbs = (w 2).natAbs := hw 2
  have e3 : (x * g 29 + y * g 34).natAbs = (w 3).natAbs := hw 3
  have e4 : (x * g 30 + y * g 35).natAbs = (w 4).natAbs := hw 4
  unfold ptR at hp
  by_cases h5 : 5 ≤ h % 64
  · rw [if_pos h5] at hp
    right
    unfold timeR at hp
    rw [e0, e1, e2, e3, e4] at hp
    exact timeOk5_sound w ((h / 64 : ℕ) : ℤ) ((h % 64 : ℕ) : ℤ) (tm_sound w (h / 64, h % 64) (by simp only; omega) hp)
  · rw [if_neg h5] at hp
    by_cases q0 : h % 64 = 0
    · rw [if_pos q0] at hp
      exfalso
      have hg : Nat.gcd x.natAbs y.natAbs = 1 := hgcd
      rw [hg] at hp
      simp at hp
    · rw [if_neg q0] at hp
      by_cases q1 : h % 64 = 1
      · rw [if_pos q1] at hp
        exfalso
        unfold zeroAtR at hp
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
        obtain ⟨ht, hz⟩ := hp
        have hz2 : x * g (26 + h / 64) + y * g (31 + h / 64) = 0 := hz
        have h0 : (x * g (26 + h / 64) + y * g (31 + h / 64)).natAbs = 0 := by rw [hz2]; rfl
        have h00 := (hw ⟨h / 64, ht⟩).symm.trans h0
        exact absurd (Int.natAbs_eq_zero.1 h00) (hnz _)
      · rw [if_neg q1] at hp
        by_cases q2 : h % 64 = 2
        · rw [if_pos q2] at hp
          exfalso
          unfold eqAbsR at hp
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
          obtain ⟨ht, heq⟩ := hp
          obtain ⟨hA, hB, hne⟩ := pair_ok (h / 64) ht
          have hij : (⟨pairA (h / 64), hA⟩ : Fin 5) ≠ ⟨pairB (h / 64), hB⟩ := fun e => hne (congrArg Fin.val e)
          refine hdist _ _ hij ?_
          rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs, ← hw ⟨pairA (h / 64), hA⟩, ← hw ⟨pairB (h / 64), hB⟩]
          exact congrArg (fun n : ℕ => (n : ℤ)) heq
        · rw [if_neg q2] at hp
          by_cases q3 : h % 64 = 3
          · rw [if_pos q3] at hp
            left
            unfold t5R at hp
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
            obtain ⟨ht, hall⟩ := hp
            have hr := T5V_getD_mem (h / 64) ht
            obtain ⟨hl, hnd⟩ := t5V_ok _ hr
            refine ⟨_, hr, exists_sp_of_mem w hnz _ hl hnd ?_⟩
            intro e he
            rw [List.all_eq_true] at hall
            have := hall e he
            simp only [Bool.or_eq_true, beq_iff_eq] at this
            rcases this with ((((h0 | h1) | h2) | h3) | h4)
            · exact ⟨0, (hw 0).symm.trans h0⟩
            · exact ⟨1, (hw 1).symm.trans h1⟩
            · exact ⟨2, (hw 2).symm.trans h2⟩
            · exact ⟨3, (hw 3).symm.trans h3⟩
            · exact ⟨4, (hw 4).symm.trans h4⟩
          · rw [if_neg q3] at hp
            exfalso
            simp only [Bool.or_eq_true, decide_eq_true_eq] at hp
            rcases hp with h1 | h1
            · exact absurd hlo (not_le.2 h1)
            · exact absurd hhi (not_le.2 h1)

/-! ## The structural facts -/

structure StructR (g : Nat → Int) : Prop where
  eq : ∀ i < 5, ∀ j < 5, g (26 + i) * g (36 + j) + g (31 + i) * g (41 + j) + g (46 + i) * g (11 + j) +
      g (51 + i) * g (16 + j) + g (56 + i) * g (21 + j) = if i = j then 1 else 0
  nr1 : g 61 = 1
  D : 0 < dt g 26 26 * dt g 31 31 - dt g 26 31 * dt g 26 31
  Y0 : 0 ≤ g 64
  bY : g 63 * dt g 26 26 <
    (dt g 26 26 * dt g 31 31 - dt g 26 31 * dt g 26 31) * ((g 64 + 1) * (g 64 + 1))

theorem structR_facts (g : Nat → Int) (h : structR g = true) : StructR g := by
  unfold structR at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range, and_assoc] at h
  obtain ⟨_, _, _, _, _, _, h7, h8, h9, h10, h11⟩ := h
  exact ⟨fun i hi j hj => h7 i hi j hj, h8, h9, h10, h11⟩

/-! ## The main theorem -/

theorem classLinesR_sound (g : Nat → Int) (W : Nat) (h : classLinesR g W = true) (u : V5) (hprim : Primitive u)
    (hnz : ∀ i, u i ≠ 0) (hdist : ∀ i j, i ≠ j → |u i| ≠ |u j|)
    (hl0 : ∑ j : Fin 5, g (11 + j.val) * u j = 0) (hl1 : ∑ j : Fin 5, g (16 + j.val) * u j = 0)
    (hl2 : ∑ j : Fin 5, g (21 + j.val) * u j = 0)
    (hr : ∃ j < (g 61).toNat, g (62 + 2 * j) ≤ dot u u ∧ dot u u ≤ g (63 + 2 * j)) :
    (∃ r ∈ T5V, ∃ s : SP, s.act u = T5Vec r) ∨ (1 : ℝ) / 5 ≤ ML u := by
  unfold classLinesR at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hst, hpt0⟩, hrows⟩ := h
  have hS := structR_facts g hst
  have hnr : (g 61).toNat = 1 := by rw [hS.nr1]; rfl
  have hrg0 : g 62 ≤ dot u u ∧ dot u u ≤ g 63 := by
    obtain ⟨j, hj, h1, h2⟩ := hr
    rw [hnr] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact ⟨by simpa using h1, by simpa using h2⟩
  set a := dt g 26 26 with ha
  set b := dt g 26 31 with hb
  set c := dt g 31 31 with hc
  set Y := g 64 with hYd
  -- (1) coordinates
  set x : ℤ := ∑ j : Fin 5, g (36 + j.val) * u j with hx
  set y : ℤ := ∑ j : Fin 5, g (41 + j.val) * u j with hy
  have key : ∀ i : Fin 5, u i = x * g (26 + i.val) + y * g (31 + i.val) := by
    intro i
    have e1 := fun j : Fin 5 => hS.eq i.val i.2 j.val j.2
    calc u i = ∑ j : Fin 5, (if i.val = j.val then (1 : ℤ) else 0) * u j := by
          simp [Fin.val_inj]
      _ = ∑ j : Fin 5, ((g (26 + i.val) * g (36 + j.val) + g (31 + i.val) * g (41 + j.val) + g (46 + i.val) * g (11 + j.val) +
            g (51 + i.val) * g (16 + j.val) + g (56 + i.val) * g (21 + j.val)) * u j) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [e1 j]
      _ = g (26 + i.val) * x + g (31 + i.val) * y + (g (46 + i.val) * ∑ j : Fin 5, g (11 + j.val) * u j +
            g (51 + i.val) * ∑ j : Fin 5, g (16 + j.val) * u j + g (56 + i.val) * ∑ j : Fin 5, g (21 + j.val) * u j) := by
          simp only [hx, hy, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring
      _ = x * g (26 + i.val) + y * g (31 + i.val) := by rw [hl0, hl1, hl2]; ring
  -- (2) coprimality
  have hgcd : Int.gcd x y = 1 := by
    have hdx : ((Int.gcd x y : ℕ) : ℤ) ∣ x := Int.gcd_dvd_left x y
    have hdy : ((Int.gcd x y : ℕ) : ℤ) ∣ y := Int.gcd_dvd_right x y
    have hdu : ∀ i, ((Int.gcd x y : ℕ) : ℤ) ∣ u i := by
      intro i
      rw [key i]
      exact dvd_add (dvd_mul_of_dvd_left hdx _) (dvd_mul_of_dvd_left hdy _)
    rcases hprim _ hdu with h' | h'
    · exact_mod_cast h'
    · have : (0 : ℤ) ≤ ((Int.gcd x y : ℕ) : ℤ) := Int.natCast_nonneg _
      omega
  -- the norm
  have hn : dot u u = a * x * x + 2 * b * x * y + c * y * y := by
    simp only [dot, Fin.sum_univ_five]
    rw [key 0, key 1, key 2, key 3, key 4]
    simp only [ha, hb, hc, dt, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero]
    simp
    ring
  have hD : 0 < a * c - b * b := hS.D
  have hbY : g 63 * a < (a * c - b * b) * ((Y + 1) * (Y + 1)) := hS.bY
  have hac : 0 ≤ a := dt_self_nonneg g 26
  have hapos : 0 < a := by
    rcases hac.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      rw [← h'] at hD
      nlinarith [sq_nonneg b]
  have hneg : ∀ i : Fin 5, (-x) * g (26 + i.val) + (-y) * g (31 + i.val) = -(x * g (26 + i.val) + y * g (31 + i.val)) :=
    fun i => by ring
  -- (3) every normalised point is certified
  have hPB : ∀ x' y' : ℤ, 0 ≤ y' → (y' = 0 → x' = 1) → (x' = x ∧ y' = y ∨ x' = -x ∧ y' = -y) →
      (∃ r ∈ T5V, ∃ s : SP, s.act u = T5Vec r) ∨ (1 : ℝ) / 5 ≤ ML u := by
    intro x' y' hy' hy0 hxy
    have hm' : dot u u = a * x' * x' + 2 * b * x' * y' + c * y' * y' := by
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hn
      · rw [hn]; ring
    have hgcd' : Int.gcd x' y' = 1 := by
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hgcd
      · simpa using hgcd
    have hw' : ∀ i : Fin 5, (x' * g (26 + i.val) + y' * g (31 + i.val)).natAbs = (u i).natAbs := by
      intro i
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [← key i]
      · rw [hneg i, Int.natAbs_neg, ← key i]
    have hlo : g 62 ≤ a * x' * x' + 2 * b * x' * y' + c * y' * y' := by rw [← hm']; exact hrg0.1
    have hhi : a * x' * x' + 2 * b * x' * y' + c * y' * y' ≤ g 63 := by rw [← hm']; exact hrg0.2
    have hcov : ∃ hh, ptR g a b c x' y' hh = true := by
      by_cases hy1 : y' = 0
      · have hx1 := hy0 hy1
        subst hy1
        subst hx1
        exact ⟨Nat.mod W 2048, hpt0⟩
      · have hypos : 0 < y' := lt_of_le_of_ne hy' (Ne.symm hy1)
        have hyY : y' ≤ Y := box_y (D := a * c - b * b) hD rfl hac hm' hrg0.2 hS.Y0 hy' hbY
        have e : ((y'.toNat : ℕ) : ℤ) = y' := Int.toNat_of_nonneg hy'
        obtain ⟨hh, hpp⟩ := rowsOk_sound g a b c hapos _ _ _ hrows y'.toNat (by omega) (by omega) x'
          (by rw [e]; exact hlo) (by rw [e]; exact hhi)
        rw [e] at hpp
        exact ⟨hh, hpp⟩
    obtain ⟨hh, hp⟩ := hcov
    exact ptR_sound g a b c x' y' u hnz hdist hw' hgcd' hlo hhi hh hp
  -- sign normalisation
  by_cases hp : 0 < y ∨ (y = 0 ∧ x = 1)
  · refine hPB x y (by rcases hp with h' | ⟨h', _⟩ <;> omega) ?_ (Or.inl ⟨rfl, rfl⟩)
    intro hz; rcases hp with h' | ⟨_, h'⟩ <;> omega
  · push_neg at hp
    obtain ⟨hy1, hy2⟩ := hp
    have hnone : y < 0 ∨ (y = 0 ∧ x = -1) := by
      by_cases hz : y = 0
      · right
        refine ⟨hz, ?_⟩
        have hg0 : Int.gcd x 0 = 1 := by rw [← hz]; exact hgcd
        have hx_abs : x.natAbs = 1 := by simpa using hg0
        have := hy2 hz
        omega
      · left; omega
    refine hPB (-x) (-y) (by rcases hnone with h' | ⟨h', _⟩ <;> omega) ?_ (Or.inr ⟨rfl, rfl⟩)
    intro hz; rcases hnone with h' | ⟨_, h'⟩ <;> omega

/-! ## The `InClass` form -/

theorem classLinesR_inClass (g : Nat → Int) (W : Nat) (h : classLinesR g W = true) (cl : T4Rec)
    (hl : ∀ i : Fin 3, cl.l i = fun a : Fin 5 => g (11 + 5 * i.val + a.val))
    (hrg : cl.ranges = (List.range (g 61).toNat).map fun j => (g (62 + 2 * j), g (63 + 2 * j)))
    (u : V5) (hprim : Primitive u) (hnz : ∀ i, u i ≠ 0) (hdist : ∀ i j, i ≠ j → |u i| ≠ |u j|) (hc : InClass cl u) :
    (∃ r ∈ T5V, ∃ s : SP, s.act u = T5Vec r) ∨ (1 : ℝ) / 5 ≤ ML u := by
  obtain ⟨h3, r, hr, hlo, hhi⟩ := hc
  have hd : ∀ i : Fin 3, ∑ j : Fin 5, g (11 + 5 * i.val + j.val) * u j = 0 := by
    intro i
    have := h3 i
    rw [hl i] at this
    exact this
  refine classLinesR_sound g W h u hprim hnz hdist (hd 0) (hd 1) (hd 2) ?_
  rw [hrg, List.mem_map] at hr
  obtain ⟨j, hj, rfl⟩ := hr
  exact ⟨j, List.mem_range.1 hj, hlo, hhi⟩

end

end Lin
end L5S4
end LRSpectrumFull
