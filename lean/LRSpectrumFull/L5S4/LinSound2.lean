/-
# L5S4.LinSound2 : the line-loop soundness theorem `classLinesB_sound` and its `InClass` form (stage S4 block 16)

See `LinSound.lean` for the outline.  This module extracts the structural facts of `structB`, the loop value at a point, the box
bounds, and proves

* `classLinesB_sound` : the statement for a record accessor `g`;
* `classLinesB_inClass` : the same for any `T4Rec` whose three rows and range list are read from the record (the shape of the
  `lines` clause of `TreeHyp`, with `C.t5` replaced by `T5V`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.LinSound

namespace LRSpectrumFull
namespace L5S4
namespace Lin

open Finset LRSpectrumFull.L5S3

noncomputable section

/-! ## 1. The structural facts -/

structure StructFacts (g : Nat → Int) : Prop where
  eq : ∀ i < 5, ∀ j < 5, g (26 + i) * g (36 + j) + g (31 + i) * g (41 + j) + g (46 + i) * g (11 + j) +
      g (51 + i) * g (16 + j) + g (56 + i) * g (21 + j) = if i = j then 1 else 0
  nr1 : 1 ≤ (g 61).toNat
  hi : ∀ j < (g 61).toNat, g (63 + 2 * j) ≤ g (63 + 2 * ((g 61).toNat - 1))
  D : 0 < dt g 26 26 * dt g 31 31 - dt g 26 31 * dt g 26 31
  X0 : 0 ≤ g (62 + 2 * (g 61).toNat)
  Y0 : 0 ≤ g (63 + 2 * (g 61).toNat)
  bx : g (63 + 2 * ((g 61).toNat - 1)) * dt g 31 31 <
    (dt g 26 26 * dt g 31 31 - dt g 26 31 * dt g 26 31) * ((g (62 + 2 * (g 61).toNat) + 1) * (g (62 + 2 * (g 61).toNat) + 1))
  bY : g (63 + 2 * ((g 61).toNat - 1)) * dt g 26 26 <
    (dt g 26 26 * dt g 31 31 - dt g 26 31 * dt g 26 31) * ((g (63 + 2 * (g 61).toNat) + 1) * (g (63 + 2 * (g 61).toNat) + 1))

theorem structB_facts (g : Nat → Int) (h : structB g = true) : StructFacts g := by
  unfold structB at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range, and_assoc] at h
  obtain ⟨_, _, _, _, _, _, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨fun i hi j hj => h7 i hi j hj, h8, h9, h10, h11, h12, h13, h14⟩

/-! ## 2. The loop value at a point -/

theorem loop_of (g : Nat → Int) (h : classLinesB g = true) (x y : Int) (hy : 0 ≤ y) (hy0 : y = 0 → x = 1)
    (hX : |x| ≤ g (62 + 2 * (g 61).toNat)) (hY : y ≤ g (63 + 2 * (g 61).toNat)) :
    lineB g (g 61).toNat (dt g 26 26) (dt g 26 31) (dt g 31 31) x y = true := by
  unfold classLinesB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨_, hloop⟩ := h
  by_cases hy1 : y = 0
  · have := hloop 0 (by omega)
    simp only [if_true] at this
    rw [hy1, hy0 hy1]
    exact this
  · have hyn : y.toNat < (g (63 + 2 * (g 61).toNat)).toNat + 1 := by omega
    have := hloop y.toNat hyn
    have hne : y.toNat ≠ 0 := by omega
    simp only [hne, if_false, List.all_eq_true, List.mem_range] at this
    have hx := this (x + g (62 + 2 * (g 61).toNat)).toNat (by have := abs_le.1 hX; omega)
    have e1 : (((x + g (62 + 2 * (g 61).toNat)).toNat : ℕ) : ℤ) = x + g (62 + 2 * (g 61).toNat) := by
      have := abs_le.1 hX; omega
    have e2 : ((y.toNat : ℕ) : ℤ) = y := by omega
    rw [e1, e2] at hx
    simpa using hx

/-! ## 3. The box -/

theorem box_x {a b c x y m nmax D X : ℤ} (hD : 0 < D) (hDe : D = a * c - b * b) (hc : 0 ≤ c)
    (hm : m = a * x * x + 2 * b * x * y + c * y * y) (hle : m ≤ nmax) (hX0 : 0 ≤ X)
    (hb : nmax * c < D * ((X + 1) * (X + 1))) : |x| ≤ X := by
  have ez : c * m = (c * y + b * x) ^ 2 + D * x ^ 2 := by rw [hm, hDe]; ring
  have h1 : c * m ≤ c * nmax := mul_le_mul_of_nonneg_left hle hc
  have h2 : D * x ^ 2 < D * (X + 1) ^ 2 := by nlinarith [sq_nonneg (c * y + b * x)]
  have h3 : x ^ 2 < (X + 1) ^ 2 := lt_of_mul_lt_mul_left h2 hD.le
  by_contra hcon
  push_neg at hcon
  have h4 : (X + 1) ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  rw [sq_abs] at h4
  linarith

theorem box_y {a b c x y m nmax D Y : ℤ} (hD : 0 < D) (hDe : D = a * c - b * b) (ha : 0 ≤ a)
    (hm : m = a * x * x + 2 * b * x * y + c * y * y) (hle : m ≤ nmax) (hY0 : 0 ≤ Y) (hy : 0 ≤ y)
    (hb : nmax * a < D * ((Y + 1) * (Y + 1))) : y ≤ Y := by
  have ez : a * m = (a * x + b * y) ^ 2 + D * y ^ 2 := by rw [hm, hDe]; ring
  have h1 : a * m ≤ a * nmax := mul_le_mul_of_nonneg_left hle ha
  have h2 : D * y ^ 2 < D * (Y + 1) ^ 2 := by nlinarith [sq_nonneg (a * x + b * y)]
  have h3 : y ^ 2 < (Y + 1) ^ 2 := lt_of_mul_lt_mul_left h2 hD.le
  by_contra hcon
  push_neg at hcon
  have h4 : (Y + 1) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  linarith

theorem dt_self_nonneg (g : Nat → Int) (o : Nat) : 0 ≤ dt g o o := by
  unfold dt
  nlinarith [sq_nonneg (g o), sq_nonneg (g (o + 1)), sq_nonneg (g (o + 2)), sq_nonneg (g (o + 3)), sq_nonneg (g (o + 4))]

/-! ## 4. The main theorem -/

theorem classLinesB_sound (g : Nat → Int) (h : classLinesB g = true) (u : V5) (hprim : Primitive u)
    (hnz : ∀ i, u i ≠ 0) (hdist : ∀ i j, i ≠ j → |u i| ≠ |u j|)
    (hl0 : ∑ j : Fin 5, g (11 + j.val) * u j = 0) (hl1 : ∑ j : Fin 5, g (16 + j.val) * u j = 0)
    (hl2 : ∑ j : Fin 5, g (21 + j.val) * u j = 0)
    (hr : ∃ j < (g 61).toNat, g (62 + 2 * j) ≤ dot u u ∧ dot u u ≤ g (63 + 2 * j)) :
    (∃ r ∈ T5V, ∃ s : SP, s.act u = T5Vec r) ∨ (1 : ℝ) / 5 ≤ ML u := by
  have hS := structB_facts g (by unfold classLinesB at h; simp only [Bool.and_eq_true] at h; exact h.1)
  set nr := (g 61).toNat with hnr
  set a := dt g 26 26 with ha
  set b := dt g 26 31 with hb
  set c := dt g 31 31 with hc
  set X := g (62 + 2 * nr) with hXd
  set Y := g (63 + 2 * nr) with hYd
  set nmax := g (63 + 2 * (nr - 1)) with hnm
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
  have hrg : ∃ j < nr, g (62 + 2 * j) ≤ a * x * x + 2 * b * x * y + c * y * y ∧
      a * x * x + 2 * b * x * y + c * y * y ≤ g (63 + 2 * j) := by
    rw [← hn]; exact hr
  have hmax : dot u u ≤ nmax := by
    obtain ⟨j, hj, _, h2⟩ := hr
    exact h2.trans (hS.hi j hj)
  have hDe : (a * c - b * b) = a * c - b * b := rfl
  have hD := hS.D
  have hbx := hS.bx
  have hbY := hS.bY
  have hac : 0 ≤ a := dt_self_nonneg g 26
  have hcc : 0 ≤ c := dt_self_nonneg g 31
  have bx' : |x| ≤ X := box_x (D := a * c - b * b) hD rfl hcc hn hmax hS.X0 hbx
  -- the facts for (x, y) and (-x, -y)
  have hnz' : ∀ i : Fin 5, x * g (26 + i.val) + y * g (31 + i.val) ≠ 0 := fun i => by rw [← key i]; exact hnz i
  have hd' : ∀ i j : Fin 5, i ≠ j → |x * g (26 + i.val) + y * g (31 + i.val)| ≠ |x * g (26 + j.val) + y * g (31 + j.val)| := by
    intro i j hij; rw [← key i, ← key j]; exact hdist i j hij
  have hneg : ∀ i : Fin 5, (-x) * g (26 + i.val) + (-y) * g (31 + i.val) = -(x * g (26 + i.val) + y * g (31 + i.val)) :=
    fun i => by ring
  have hnn : (-x) * (-x) = x * x := by ring
  have hrg' : ∃ j < nr, g (62 + 2 * j) ≤ a * (-x) * (-x) + 2 * b * (-x) * (-y) + c * (-y) * (-y) ∧
      a * (-x) * (-x) + 2 * b * (-x) * (-y) + c * (-y) * (-y) ≤ g (63 + 2 * j) := by
    have : a * (-x) * (-x) + 2 * b * (-x) * (-y) + c * (-y) * (-y) = a * x * x + 2 * b * x * y + c * y * y := by ring
    rw [this]; exact hrg
  -- (3) sign normalisation
  have hPB : ∀ x' y' : ℤ, (0 ≤ y') → (y' = 0 → x' = 1) → (x' = x ∧ y' = y ∨ x' = -x ∧ y' = -y) →
      pbB g x' y' = true := by
    intro x' y' hy' hy0 hxy
    have hgd : guardB g nr a b c x' y' = true := by
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact guard_of_facts g nr a b c _ _ hrg hgcd hnz' hd'
      · refine guard_of_facts g nr a b c _ _ hrg' (by simpa using hgcd) ?_ ?_
        · intro i; rw [hneg i]; exact neg_ne_zero.2 (hnz' i)
        · intro i j hij; rw [hneg i, hneg j, abs_neg, abs_neg]; exact hd' i j hij
    have hbox : |x'| ≤ X ∧ y' ≤ Y := by
      have hm' : dot u u = a * x' * x' + 2 * b * x' * y' + c * y' * y' := by
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hn
        · rw [hn]; ring
      refine ⟨box_x (D := a * c - b * b) hD rfl hcc hm' hmax hS.X0 hbx, ?_⟩
      exact box_y (D := a * c - b * b) hD rfl hac hm' hmax hS.Y0 hy' hbY
    have hlb := loop_of g h x' y' hy' hy0 hbox.1 hbox.2
    unfold lineB at hlb
    rw [hgd] at hlb
    simpa using hlb
  have hpos : pbB g x y = true ∨ pbB g (-x) (-y) = true := by
    by_cases hp : 0 < y ∨ (y = 0 ∧ x = 1)
    · left
      refine hPB x y (by rcases hp with h' | ⟨h', _⟩ <;> omega) ?_ (Or.inl ⟨rfl, rfl⟩)
      intro hz; rcases hp with h' | ⟨_, h'⟩ <;> omega
    · right
      push_neg at hp
      obtain ⟨hy1, hy2⟩ := hp
      have hy0 : 0 ≤ y ∨ y < 0 := by omega
      have hyle : y ≤ 0 ∨ 0 < y := by omega
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
  have hw : ∀ i : Fin 5, (x * g (26 + i.val) + y * g (31 + i.val)).natAbs = (u i).natAbs := fun i => by rw [← key i]
  have hw' : ∀ i : Fin 5, ((-x) * g (26 + i.val) + (-y) * g (31 + i.val)).natAbs = (u i).natAbs := fun i => by
    rw [hneg i, Int.natAbs_neg, ← key i]
  rcases hpos with hp | hp
  · exact pb_sound u hnz g x y hw hp
  · exact pb_sound u hnz g (-x) (-y) hw' hp

/-! ## 5. The `InClass` form -/

/-- every `T4Rec` whose rows and ranges are those of the record satisfies the `lines` clause (with `T5V` as the residual list). -/
theorem classLinesB_inClass (g : Nat → Int) (h : classLinesB g = true) (cl : T4Rec)
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
  refine classLinesB_sound g h u hprim hnz hdist (hd 0) (hd 1) (hd 2) ?_
  rw [hrg, List.mem_map] at hr
  obtain ⟨j, hj, rfl⟩ := hr
  exact ⟨j, List.mem_range.1 hj, hlo, hhi⟩

end

end Lin
end L5S4
end LRSpectrumFull
