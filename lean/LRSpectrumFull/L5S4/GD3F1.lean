/-
# L5S4.GD3F1 : flat (digit-accessor) leaf checker `leafOkF` and its bridge to `leafOk` (stage S4 block 14, part 1)

`leafOk` costs 115-295 ms per record in the kernel (S4M, section 4b).  Profile (S4N): the parse (`unpackL`, `parseAll`) about
a third, the class map (`mapOk`: `applySteps`, `LeqOkN`, `gOk`) a third, the `Finset`/`Decidable` facts about a quarter.
Here a record is an accessor `g : ℕ → ℤ` (in the data: 32-bit digits of ONE natural number per record, `dg`), the node is an
accessor `ng`, and every test is a plain `Int` expression.

* `recOf g` : the `LeafRec` read from the accessor (`parseLeaf z = recOf (z.getD · 0)` by `rfl`).
* `NodeAg n ng` : the accessor `ng` agrees with the node (checked once per node by `decide +kernel`).
* `leafOkF_sound` : `leafOkF ng g = true -> leafOk n (recOf g) = true` (kinds 1, 2; critical kind 0 is rejected by `leafOkF`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GD3K6
import LRSpectrumFull.L5S4.GBr2

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-- digit `k` of `N` (32-bit digits, bias `2^31`). -/
def dg (N k : ℕ) : ℤ := Int.subNatNat (Nat.mod (Nat.shiftRight N (Nat.mul 32 k)) 4294967296) 2147483648

def v5g (g : ℕ → ℤ) (o : ℕ) : V5 := fun i => g (o + i.val)

theorem gpOf_lt (g : ℕ → ℤ) (i : Fin 5) : (g (53 + i.val)).toNat % 5 < 5 := Nat.mod_lt _ (by norm_num)

/-- the leaf record read from an accessor (layout of `parseLeaf`). -/
def recOf (g : ℕ → ℤ) : LeafRec where
  t := (g 0, g 1, g 2)
  y := v5g g 3
  b := [v5g g 8, v5g g 13]
  r := [v5g g 18, v5g g 23]
  s := [v5g g 28, v5g g 33, v5g g 38]
  x3 := v5g g 43
  w3 := g 48
  kind := (g 49).toNat
  ck := if g 50 = 0 then 0 else 1
  rlo := g 51
  rhi := g 52
  gp := (fun i => ⟨(g (53 + i.val)).toNat % 5, gpOf_lt g i⟩, fun i => g (58 + i.val))
  u := [[g 63, g 64, g 65], [g 66, g 67, g 68], [g 69, g 70, g 71]]
  u' := [[g 72, g 73, g 74], [g 75, g 76, g 77], [g 78, g 79, g 80]]
  cl := [v5g g 81, v5g g 86, v5g g 91]
  steps := (List.range (g 96).toNat).map fun k => ((g (97 + 3 * k)).toNat, (g (98 + 3 * k)).toNat, g (99 + 3 * k))

theorem parseLeaf_eq (z : List ℤ) : parseLeaf z = recOf (fun k => z.getD k 0) := rfl

/-! ## flat arithmetic -/

def dt (a b : ℕ → ℤ) (o p : ℕ) : ℤ :=
  a o * b p + a (o + 1) * b (p + 1) + a (o + 2) * b (p + 2) + a (o + 3) * b (p + 3) + a (o + 4) * b (p + 4)

def mm (x W : ℤ) : ℤ := min (x % W) (W - x % W)

def wmF (g : ℕ → ℤ) (o : ℕ) (W : ℤ) : ℤ :=
  min (min (min (min (mm (g o) W) (mm (g (o + 1)) W)) (mm (g (o + 2)) W)) (mm (g (o + 3)) W)) (mm (g (o + 4)) W)

theorem wMin_eq (X : V5) (W : ℤ) :
    wMin X W = min (min (min (min (mm (X 0) W) (mm (X 1) W)) (mm (X 2) W)) (mm (X 3) W)) (mm (X 4) W) := by
  unfold wMin mm
  apply le_antisymm
  · have h := fun k : Fin 5 => Finset.inf'_le (fun a : Fin 5 => min (X a % W) (W - X a % W)) (Finset.mem_univ k)
    exact le_min (le_min (le_min (le_min (h 0) (h 1)) (h 2)) (h 3)) (h 4)
  · apply Finset.le_inf'
    intro a _
    fin_cases a <;> simp

theorem wmF_eq (g : ℕ → ℤ) (o : ℕ) (W : ℤ) : wMin (v5g g o) W = wmF g o W := by
  rw [wMin_eq]; rfl

/-- the node accessor layout: 0-4 `rows 0`, 5-9 `rows 1`, 10-24 `b 0..2`, 25 `M1`, 26 `W1`, 27 `M2`, 28 `W2`, 29 `G1`, 30 `G2`,
31 `e00`, 32 `e01`, 33 `e11`. -/
structure NodeAg (n : NodeW 2 3) (ng : ℕ → ℤ) : Prop where
  r0 : ∀ c : Fin 5, n.rows 0 c = ng c.val
  r1 : ∀ c : Fin 5, n.rows 1 c = ng (5 + c.val)
  b : ∀ (j : Fin 3) (c : Fin 5), n.b j c = ng (10 + 5 * j.val + c.val)
  m1 : wMin (n.wit 1).1 (n.wit 1).2 = ng 25
  w1 : (n.wit 1).2 = ng 26
  m2 : wMin (n.wit 2).1 (n.wit 2).2 = ng 27
  w2 : (n.wit 2).2 = ng 28
  g1 : leafG1 n = ng 29
  g2 : leafG2 n = ng 30
  e00 : dot (n.rows 0) (n.rows 0) = ng 31
  e01 : dot (n.rows 0) (n.rows 1) = ng 32
  e11 : dot (n.rows 1) (n.rows 1) = ng 33

def g3F (ng g : ℕ → ℤ) : ℤ :=
  ng 31 * (ng 33 * dt g g 3 3 - dt ng g 5 3 * dt ng g 5 3) - ng 32 * (ng 32 * dt g g 3 3 - dt ng g 5 3 * dt ng g 0 3) +
    dt ng g 0 3 * (ng 32 * dt ng g 5 3 - ng 33 * dt ng g 0 3)

def factsF (ng g : ℕ → ℤ) : Bool :=
  decide (dt ng g 10 3 = g 0) && decide (dt ng g 15 3 = g 1) && decide (dt ng g 20 3 = g 2) &&
  decide (dt g ng 8 0 = 0) && decide (dt g ng 8 5 = 0) && decide (dt g g 8 3 = 0) &&
  decide (dt g ng 13 0 = 0) && decide (dt g ng 13 5 = 0) && decide (dt g g 13 3 = 0) &&
  decide (dt ng g 0 28 = 1) && decide (dt ng g 0 33 = 0) && decide (dt ng g 0 38 = 0) &&
  decide (dt ng g 5 28 = 0) && decide (dt ng g 5 33 = 1) && decide (dt ng g 5 38 = 0) &&
  decide (dt g g 3 28 = 0) && decide (dt g g 3 33 = 0) && decide (dt g g 3 38 = 1) &&
  decide (dt g g 8 18 = 1) && decide (dt g g 8 23 = 0) && decide (dt g g 13 18 = 0) && decide (dt g g 13 23 = 1) &&
  decide (0 < g 48) && decide (g 48 ∣ dt ng g 0 43) && decide (g 48 ∣ dt ng g 5 43) && decide (g 48 ∣ dt g g 3 43) &&
  decide (g 48 < 5 * wmF g 43 (g 48))

theorem dt_eq (a b : V5) (A B : ℕ → ℤ) (o p : ℕ) (ha : ∀ c : Fin 5, a c = A (o + c.val)) (hb : ∀ c : Fin 5, b c = B (p + c.val)) :
    dot a b = dt A B o p := by
  simp only [dot, Fin.sum_univ_five, dt, ha, hb]
  rfl

theorem hN_r0 (n : NodeW 2 3) (y : V5) : hN (setRow n.rows 2 y) 0 = n.rows 0 := by
  rw [hN_setRow_lt _ _ _ _ (by norm_num)]; simp [hN]
theorem hN_r1 (n : NodeW 2 3) (y : V5) : hN (setRow n.rows 2 y) 1 = n.rows 1 := by
  rw [hN_setRow_lt _ _ _ _ (by norm_num)]; simp [hN]
theorem hN_r2 (n : NodeW 2 3) (y : V5) : hN (setRow n.rows 2 y) 2 = y := hN_setRow_eq _ _ _ (by norm_num)

theorem facts_of_F (n : NodeW 2 3) (ng g : ℕ → ℤ) (hag : NodeAg n ng) (h : factsF ng g = true) : (recOf g).facts n := by
  unfold factsF at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22,
    f23, f24, f25, f26, f27⟩ := h
  have eb0 : ∀ c : Fin 5, n.b 0 c = ng (10 + c.val) := fun c => by simpa using hag.b 0 c
  have eb1 : ∀ c : Fin 5, n.b 1 c = ng (15 + c.val) := fun c => by simpa using hag.b 1 c
  have eb2 : ∀ c : Fin 5, n.b 2 c = ng (20 + c.val) := fun c => by simpa using hag.b 2 c
  have er0 : ∀ c : Fin 5, n.rows 0 c = ng (0 + c.val) := fun c => by simpa using hag.r0 c
  have er1 : ∀ c : Fin 5, n.rows 1 c = ng (5 + c.val) := hag.r1
  have hy : ∀ c : Fin 5, (recOf g).y c = g (3 + c.val) := fun c => rfl
  have hb0 : ∀ c : Fin 5, bL (recOf g).b 0 c = g (8 + c.val) := fun c => rfl
  have hb1 : ∀ c : Fin 5, bL (recOf g).b 1 c = g (13 + c.val) := fun c => rfl
  have hq0 : ∀ c : Fin 5, hN (setRow n.rows 2 (recOf g).y) 0 c = ng (0 + c.val) := fun c => by rw [hN_r0, er0]
  have hq1 : ∀ c : Fin 5, hN (setRow n.rows 2 (recOf g).y) 1 c = ng (5 + c.val) := fun c => by rw [hN_r1, er1]
  have hq2 : ∀ c : Fin 5, hN (setRow n.rows 2 (recOf g).y) 2 c = g (3 + c.val) := fun c => by rw [hN_r2]; rfl
  have hs0 : ∀ c : Fin 5, sL (recOf g).s 0 c = g (28 + c.val) := fun c => rfl
  have hs1 : ∀ c : Fin 5, sL (recOf g).s 1 c = g (33 + c.val) := fun c => rfl
  have hs2 : ∀ c : Fin 5, sL (recOf g).s 2 c = g (38 + c.val) := fun c => rfl
  have ht0 : ∀ c : Fin 5, bL (recOf g).r 0 c = g (18 + c.val) := fun c => rfl
  have ht1 : ∀ c : Fin 5, bL (recOf g).r 1 c = g (23 + c.val) := fun c => rfl
  have hx : ∀ c : Fin 5, (recOf g).x3 c = g (43 + c.val) := fun c => rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (dt_eq _ _ ng g 10 3 eb0 hy).trans f1
  · exact (dt_eq _ _ ng g 15 3 eb1 hy).trans f2
  · exact (dt_eq _ _ ng g 20 3 eb2 hy).trans f3
  · intro i k
    fin_cases i <;> fin_cases k
    · exact (dt_eq _ _ g ng 8 0 hb0 hq0).trans f4
    · exact (dt_eq _ _ g ng 8 5 hb0 hq1).trans f5
    · exact (dt_eq _ _ g g 8 3 hb0 hq2).trans f6
    · exact (dt_eq _ _ g ng 13 0 hb1 hq0).trans f7
    · exact (dt_eq _ _ g ng 13 5 hb1 hq1).trans f8
    · exact (dt_eq _ _ g g 13 3 hb1 hq2).trans f9
  · intro i k
    fin_cases i <;> fin_cases k
    · exact (dt_eq _ _ ng g 0 28 hq0 hs0).trans (f10.trans (by decide))
    · exact (dt_eq _ _ ng g 0 33 hq0 hs1).trans (f11.trans (by decide))
    · exact (dt_eq _ _ ng g 0 38 hq0 hs2).trans (f12.trans (by decide))
    · exact (dt_eq _ _ ng g 5 28 hq1 hs0).trans (f13.trans (by decide))
    · exact (dt_eq _ _ ng g 5 33 hq1 hs1).trans (f14.trans (by decide))
    · exact (dt_eq _ _ ng g 5 38 hq1 hs2).trans (f15.trans (by decide))
    · exact (dt_eq _ _ g g 3 28 hq2 hs0).trans (f16.trans (by decide))
    · exact (dt_eq _ _ g g 3 33 hq2 hs1).trans (f17.trans (by decide))
    · exact (dt_eq _ _ g g 3 38 hq2 hs2).trans (f18.trans (by decide))
  · intro i k
    fin_cases i <;> fin_cases k
    · exact (dt_eq _ _ g g 8 18 hb0 ht0).trans (f19.trans (by decide))
    · exact (dt_eq _ _ g g 8 23 hb0 ht1).trans (f20.trans (by decide))
    · exact (dt_eq _ _ g g 13 18 hb1 ht0).trans (f21.trans (by decide))
    · exact (dt_eq _ _ g g 13 23 hb1 ht1).trans (f22.trans (by decide))
  · have hw : wMin (recOf g).x3 (recOf g).w3 = wmF g 43 (g 48) := wmF_eq g 43 (g 48)
    refine ⟨f23, ?_, ?_, ?_, ?_⟩
    · rw [dt_eq _ _ ng g 0 43 er0 hx]; exact f24
    · rw [dt_eq _ _ ng g 5 43 er1 hx]; exact f25
    · rw [dt_eq _ _ g g 3 43 hy hx]; exact f26
    · rw [hw]; exact (le_of_lt f27)

/-! ## the window test -/

theorem leafG3_eq (n : NodeW 2 3) (ng g : ℕ → ℤ) (hag : NodeAg n ng) : leafG3 n (v5g g 3) = g3F ng g := by
  have er0 : ∀ c : Fin 5, n.rows 0 c = ng (0 + c.val) := fun c => by simpa using hag.r0 c
  have hy : ∀ c : Fin 5, v5g g 3 c = g (3 + c.val) := fun c => rfl
  have h0 : hN n.rows 0 = n.rows 0 := by simp [hN]
  have h1 : hN n.rows 1 = n.rows 1 := by simp [hN]
  have p0 : dot (n.rows 0) (v5g g 3) = dt ng g 0 3 := dt_eq _ _ ng g 0 3 er0 hy
  have p1 : dot (n.rows 1) (v5g g 3) = dt ng g 5 3 := dt_eq _ _ ng g 5 3 hag.r1 hy
  have pp : dot (v5g g 3) (v5g g 3) = dt g g 3 3 := dt_eq _ _ g g 3 3 hy hy
  unfold leafG3 g3F
  rw [h0, h1, hag.e00, hag.e01, hag.e11, dot_comm' (n.rows 1) (n.rows 0), hag.e01, p0, p1, pp,
    dot_comm' (v5g g 3) (n.rows 1), p1, dot_comm' (v5g g 3) (n.rows 0), p0]

def winF (ng g : ℕ → ℤ) : Bool :=
  winOk (ng 29) (ng 30) (g3F ng g) (ng 25) (ng 26) (ng 27) (ng 28) (wmF g 43 (g 48)) (g 48) (g 51)
    (if g 49 = 1 then g 51 - 1 else g 52)

theorem leafWin_of_F (n : NodeW 2 3) (ng g : ℕ → ℤ) (hag : NodeAg n ng) (h : winF ng g = true) :
    leafWin n (recOf g) = true := by
  unfold leafWin
  have hk : ((recOf g).kind = 1) ↔ g 49 = 1 := by
    show (g 49).toNat = 1 ↔ g 49 = 1
    omega
  have e : (if (recOf g).kind = 1 then (recOf g).rlo - 1 else (recOf g).rhi) = (if g 49 = 1 then g 51 - 1 else g 52) := by
    by_cases h1 : g 49 = 1
    · rw [if_pos (hk.2 h1), if_pos h1]; rfl
    · rw [if_neg (fun h => h1 (hk.1 h)), if_neg h1]; rfl
  rw [e, hag.m1, hag.w1, hag.m2, hag.w2, hag.g1, hag.g2]
  show winOk (ng 29) (ng 30) (leafG3 n (v5g g 3)) (ng 25) (ng 26) (ng 27) (ng 28) (wMin (v5g g 43) (g 48)) (g 48) (g 51) _ = true
  rw [wmF_eq, leafG3_eq n ng g hag]
  exact h

/-! ## the class map -/

def stepF (i j : ℕ) (q : ℤ) (L : List ℤ) : List ℤ :=
  L.mapIdx fun p x => if p / 5 = i then x - q * L.getD (5 * j + p % 5) 0 else x

def applyF : List (ℕ × ℕ × ℤ) → List ℤ → List ℤ
  | [], L => L
  | (i, j, q) :: l, L => applyF l (stepF i j q L)

/-- the flat state `L` (rows 0-2, row-major) represents the first three rows of `A`. -/
def Rep (A : Fin 4 → V5) (L : List ℤ) : Prop :=
  L.length = 15 ∧ ∀ i < 3, ∀ c : Fin 5, L.getD (5 * i + c.val) 0 = hN A i c

theorem rep_step (A : Fin 4 → V5) (L : List ℤ) (i j : ℕ) (q : ℤ) (hi : i < 3) (hj : j < 3) (h : Rep A L) :
    Rep (elemRow i j q A) (stepF i j q L) := by
  obtain ⟨hl, hr⟩ := h
  refine ⟨by simp [stepF, hl], fun m hm c => ?_⟩
  have hlt : 5 * m + c.val < L.length := by have := c.isLt; omega
  have hd : (5 * m + c.val) / 5 = m := by have := c.isLt; omega
  have hmod : (5 * m + c.val) % 5 = c.val := by have := c.isLt; omega
  rw [hN_elemRow i j q A m (by omega) c]
  have e1 : L[5 * m + c.val] = hN A m c := by
    have := hr m hm c
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at this
  have e2 : L[5 * j + c.val]?.getD 0 = hN A j c := by
    rw [← List.getD_eq_getElem?_getD]; exact hr j hj c
  simp only [stepF, List.getD_eq_getElem?_getD, List.getElem?_mapIdx, List.getElem?_eq_getElem hlt, Option.map_some,
    Option.getD_some, hd, hmod]
  by_cases hmi : m = i
  · subst hmi; simp [e1, e2]
  · simp [hmi, e1]

theorem rep_apply (A : Fin 4 → V5) (L : List ℤ) (l : List (ℕ × ℕ × ℤ)) (hv : stepsValid 3 l = true) (h : Rep A L) :
    Rep (applySteps l A) (applyF l L) := by
  induction l generalizing A L with
  | nil => exact h
  | cons s l ih =>
    obtain ⟨i, j, q⟩ := s
    simp only [stepsValid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨⟨hi, hj⟩, -⟩, hl⟩ := hv
    exact ih _ _ hl (rep_step A L i j q hi hj h)

def gokF (g : ℕ → ℤ) : Bool :=
  decide ((g 53).toNat % 5 ≠ (g 54).toNat % 5) && decide ((g 53).toNat % 5 ≠ (g 55).toNat % 5) &&
  decide ((g 53).toNat % 5 ≠ (g 56).toNat % 5) && decide ((g 53).toNat % 5 ≠ (g 57).toNat % 5) &&
  decide ((g 54).toNat % 5 ≠ (g 55).toNat % 5) && decide ((g 54).toNat % 5 ≠ (g 56).toNat % 5) &&
  decide ((g 54).toNat % 5 ≠ (g 57).toNat % 5) && decide ((g 55).toNat % 5 ≠ (g 56).toNat % 5) &&
  decide ((g 55).toNat % 5 ≠ (g 57).toNat % 5) && decide ((g 56).toNat % 5 ≠ (g 57).toNat % 5) &&
  decide (g 58 = 1 ∨ g 58 = -1) && decide (g 59 = 1 ∨ g 59 = -1) && decide (g 60 = 1 ∨ g 60 = -1) &&
  decide (g 61 = 1 ∨ g 61 = -1) && decide (g 62 = 1 ∨ g 62 = -1)

theorem gok_of_F (g : ℕ → ℤ) (h : gokF g = true) : gOk (recOf g).gp := by
  unfold gokF at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨n01, n02, n03, n04, n12, n13, n14, n23, n24, n34, e0, e1, e2, e3, e4⟩ := h
  refine ⟨?_, ?_⟩
  · have hs : Function.Injective (fun i => ((recOf g).gp.1 i).val) :=
      inj_of_ne _ n01 n02 n03 n04 n12 n13 n14 n23 n24 n34
    exact fun i j h => hs (congrArg Fin.val h)
  · intro i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4

def tF (g : ℕ → ℤ) (L : List ℤ) (i c : ℕ) : ℤ := g (58 + c) * L.getD (5 * i + (g (53 + c)).toNat % 5) 0

def leqF (g : ℕ → ℤ) (L : List ℤ) : Bool :=
  (List.range 3).all fun i => (List.range 5).all fun c =>
    decide (tF g L i c = g (63 + 3 * i) * g (81 + c) + g (64 + 3 * i) * g (86 + c) + g (65 + 3 * i) * g (91 + c)) &&
    decide (g (81 + 5 * i + c) = g (72 + 3 * i) * tF g L 0 c + g (73 + 3 * i) * tF g L 1 c + g (74 + 3 * i) * tF g L 2 c)

def L0 (ng g : ℕ → ℤ) : List ℤ :=
  [ng 0, ng 1, ng 2, ng 3, ng 4, ng 5, ng 6, ng 7, ng 8, ng 9, g 3, g 4, g 5, g 6, g 7]

def mapF (ng g : ℕ → ℤ) : Bool :=
  stepsValid 3 (recOf g).steps && gokF g && leqF g (applyF (recOf g).steps (L0 ng g))

theorem rep0 (n : NodeW 2 3) (ng g : ℕ → ℤ) (hag : NodeAg n ng) : Rep (setRow n.rows 2 (v5g g 3)) (L0 ng g) := by
  refine ⟨rfl, fun i hi c => ?_⟩
  interval_cases i
  · rw [hN_r0, hag.r0 c]; fin_cases c <;> rfl
  · rw [hN_r1, hag.r1 c]; fin_cases c <;> rfl
  · rw [hN_r2]; fin_cases c <;> rfl

theorem leq_of_F (n : NodeW 2 3) (ng g : ℕ → ℤ) (hag : NodeAg n ng) (hg : gOk (recOf g).gp)
    (hv : stepsValid 3 (recOf g).steps = true) (h : leqF g (applyF (recOf g).steps (L0 ng g)) = true) :
    LeqOkN 3 (fun i => (gSP (recOf g).gp hg).act (applySteps (recOf g).steps (setRow n.rows 2 (recOf g).y) i))
      (rowsL (recOf g).cl) (matL (recOf g).u) (matL (recOf g).u') := by
  have hrep := rep_apply _ _ (recOf g).steps hv (rep0 n ng g hag)
  generalize hB : applySteps (recOf g).steps (setRow n.rows 2 (v5g g 3)) = B at hrep
  generalize hLf : applyF (recOf g).steps (L0 ng g) = Lf at hrep h
  have hB' : applySteps (recOf g).steps (setRow n.rows 2 (recOf g).y) = B := hB
  rw [hB']
  have thn : ∀ i < 3, ∀ c : Fin 5, hN (fun i => (gSP (recOf g).gp hg).act (B i)) i c = tF g Lf i c.val := by
    intro i hi c
    have e := hrep.2 i hi ((recOf g).gp.1 c)
    have hi4 : i < 4 := by omega
    simp only [hN, hi4, dif_pos, gSP_act, tF]
    rw [show (recOf g).gp.2 c = g (58 + c.val) from rfl]
    have e' : Lf.getD (5 * i + (g (53 + c.val)).toNat % 5) 0 = hN B i ((recOf g).gp.1 c) := e
    rw [e']
    simp [hN, hi4]
  unfold leqF at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  constructor
  · intro i hi c
    rw [thn i hi c]
    have := (h i hi c.val c.isLt).1
    interval_cases i <;> fin_cases c <;>
      simpa [Finset.sum_range_succ, matL, rowsL, recOf, v5g, hN] using this
  · intro i hi c
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [thn 0 (by norm_num) c, thn 1 (by norm_num) c, thn 2 (by norm_num) c]
    have := (h i hi c.val c.isLt).2
    interval_cases i <;> fin_cases c <;>
      simpa [matL, rowsL, recOf, v5g, hN] using this

theorem mapOk_of_F (n : NodeW 2 3) (ng g : ℕ → ℤ) (hag : NodeAg n ng) (h : mapF ng g = true) :
    mapOk n (recOf g) = true := by
  unfold mapF at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hv, hgk⟩, hl⟩ := h
  have hg := gok_of_F g hgk
  unfold mapOk
  rw [dif_pos hg]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hv, leq_of_F n ng g hag hg hv hl⟩

/-! ## the flat record checker and its soundness -/

/-- records of kind 1 (empty window) and 2 (class leaf); critical records (kind 0) are rejected. -/
def leafOkF (ng g : ℕ → ℤ) : Bool :=
  (decide (g 49 = 1) || decide (g 49 = 2)) && factsF ng g && winF ng g && (decide (g 49 = 1) || mapF ng g)

theorem strict_of_F (ng g : ℕ → ℤ) (h : factsF ng g = true) : g 48 < 5 * wmF g 43 (g 48) := by
  unfold factsF at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, f27⟩ := h
  exact f27

theorem leafOkF_sound (n : NodeW 2 3) (ng g : ℕ → ℤ) (hag : NodeAg n ng) (h : leafOkF ng g = true) :
    leafOk n (recOf g) = true := by
  unfold leafOkF at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hf⟩, hw⟩, hm⟩ := h
  have hk0 : (recOf g).kind ≠ 0 := by
    show (g 49).toNat ≠ 0
    omega
  unfold leafOk
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨facts_of_F n ng g hag hf, ?_⟩
  rw [if_neg hk0]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, leafWin_of_F n ng g hag hw⟩, ?_⟩
  · show g 48 < 5 * wMin (v5g g 43) (g 48)
    rw [wmF_eq]
    exact strict_of_F ng g hf
  · rcases hm with h1 | h2
    · left
      show (g 49).toNat = 1
      omega
    · exact Or.inr (mapOk_of_F n ng g hag h2)

end L5S4
end LRSpectrumFull
