/-
# L5S4.CheckT1 : the depth-1 checker (`StreamHyp.t1`) on the real certificate

Case-tree certificate, part 5.  Closes `StreamHyp'.t1` for the 26 depth-1 nodes of the real
certificate (`D1Data`, generated from `t1.bin` and `wp0a::child`):

1. `D1Raw.ok` (decidable) : the node identities `b.h = 0`, `h.s = 1`, `b.r = I`, the witness `x/w` of `M(L_1)`
   (`w > 0`, `w | h.x`, `c_1 > 1/5`), i.e. exactly the `NodeW 1 4` fields; `nodeOfRaw` builds the node from a record
   with `ok` (soundness of the node checker, by construction).
2. `chkAll` : every sorted vector with entries in `[0, 4]`, `gcd = 1`, `2 <= |h|^2 <= 18` is among the stored `h`
   (Boolean loop over the 3125 candidates, kernel `decide`); `T1Ok h -> h` is stored (`t1_complete`).
3. `d1_t1` : `T1Ok h -> exists n in R1d1, hN n.rows 0 = h`, with `R1d1` the set of the 26 stored nodes.
4. Controls (`ctl_*`): a corrupted record fails `ok`, a list with a vector removed fails `chkAll`.

No `sorry`, no `native_decide` (kernel `decide +kernel` only), no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.D1Data
import LRSpectrumFull.L5S4.NodeEx

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## 1. The node checker -/

/-- The checks of one depth-1 record (all integer, decidable). -/
def D1Raw.ok (r : D1Raw) : Prop :=
  (∀ i : Fin 4, dot (r.b i) r.h = 0) ∧ dot r.h r.s = 1 ∧
  (∀ i k : Fin 4, dot (r.b i) (r.r k) = if i = k then 1 else 0) ∧
  0 < r.w ∧ r.w ∣ dot r.h r.x ∧ r.w < 5 * wMin r.x r.w

instance (r : D1Raw) : Decidable r.ok := by unfold D1Raw.ok; infer_instance

def d1Rows (h : V5) : Fin 4 → V5 := fun i => if i.val = 0 then h else fun _ => 0

def d1Wit (r : D1Raw) : ℕ → V5 × ℤ := fun k => if k = 0 then ((fun _ => 1), 2) else (r.x, r.w)

theorem d1Id (r : D1Raw) (hr : r.ok) :
    NodeId (fun i : Fin 1 => hN (d1Rows r.h) i.val) r.b (fun _ => r.s) r.r := by
  have h0 : hN (d1Rows r.h) 0 = r.h := by simp [hN, d1Rows]
  refine ⟨fun i k => ?_, fun i k => ?_, fun i k => hr.2.2.1 i k⟩
  · have : k.val = 0 := by omega
    rw [this, h0]; exact hr.1 i
  · have e : i = k := Subsingleton.elim i k
    have : i.val = 0 := by omega
    rw [this, h0, e]; simpa using hr.2.1

theorem d1_c1 (r : D1Raw) (hr : r.ok) : 1 / 5 < cOf (r.x, r.w) := by
  obtain ⟨_, _, _, hw, _, hm⟩ := hr
  unfold cOf
  have hwq : (0 : ℚ) < (r.w : ℚ) := by exact_mod_cast hw
  have hmq : (r.w : ℚ) < 5 * (wMin r.x r.w : ℚ) := by exact_mod_cast hm
  show (1 : ℚ) / 5 < ((wMin r.x r.w : ℤ) : ℚ) / ((r.w : ℤ) : ℚ)
  rw [lt_div_iff₀ hwq]
  linarith

/-- The depth-1 node of a checked record. -/
def nodeOfRaw (r : D1Raw) (hr : r.ok) : NodeW 1 4 where
  rows := d1Rows r.h
  b := r.b
  s := fun _ => r.s
  r := r.r
  id := d1Id r hr
  wit := d1Wit r
  w0 := by simp [d1Wit]
  wok := by
    intro k hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · refine ⟨by simp [d1Wit], fun i hi => ?_⟩
      omega
    · refine ⟨by simpa [d1Wit] using hr.2.2.2.1, fun i hi => ?_⟩
      have : i.val = 0 := by omega
      have hi0 : i = 0 := Fin.ext this
      subst hi0
      simpa [d1Wit, d1Rows] using hr.2.2.2.2.1
  wge := by
    intro k hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · have : cOf (d1Wit r 0) = 1 / 2 := by simp [d1Wit, cOf, wMin]
      rw [this]; norm_num
    · have := d1_c1 r hr
      simpa [d1Wit] using this.le
  rk := ⟨1, by
    have hc := d1_c1 r hr
    have hc' : cOf (d1Wit r 1) = cOf (r.x, r.w) := by simp [d1Wit]
    simp only [radSet, Finset.mem_filter, Finset.mem_range, SArr, hc']
    refine ⟨by norm_num, ?_⟩
    have : ∑ i ∈ range 1, (if 1 ≤ i then (Gm (d1Rows r.h) i : ℚ) / (Gm (d1Rows r.h) (i + 1) : ℚ) else 0) = 0 := by
      simp
    rw [this]
    have hp : 0 < cOf (r.x, r.w) - 1 / 5 := by linarith
    nlinarith⟩

theorem nodeOfRaw_row0 (r : D1Raw) (hr : r.ok) : hN (nodeOfRaw r hr).rows 0 = r.h := by
  simp [nodeOfRaw, hN, d1Rows]

/-- The stored depth-1 nodes. -/
def R1d1 : Set (NodeW 1 4) := {n | ∃ r ∈ d1Data, ∃ hr : r.ok, n = nodeOfRaw r hr}

theorem d1Data_ok : ∀ r ∈ d1Data, r.ok := by decide +kernel

/-! ## 2. Completeness of the list -/

def d1Tup : List (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  d1Data.map fun r => (r.h 0, r.h 1, r.h 2, r.h 3, r.h 4)

def d1Chk (a0 a1 a2 a3 a4 : ℤ) : Bool :=
  decide (a0 ≤ a1) && decide (a1 ≤ a2) && decide (a2 ≤ a3) && decide (a3 ≤ a4) &&
  decide (2 ≤ a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4) &&
  decide (a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4 ≤ 18) &&
  decide (Nat.gcd (Nat.gcd (Nat.gcd (Nat.gcd a0.natAbs a1.natAbs) a2.natAbs) a3.natAbs) a4.natAbs = 1)

def d1Vals : List ℤ := [0, 1, 2, 3, 4]

/-- The loop of the checker: every candidate passing `d1Chk` is a stored vector. -/
def chkAllOf (L : List (ℤ × ℤ × ℤ × ℤ × ℤ)) : Bool :=
  d1Vals.all fun a0 => d1Vals.all fun a1 => d1Vals.all fun a2 => d1Vals.all fun a3 => d1Vals.all fun a4 =>
    !d1Chk a0 a1 a2 a3 a4 || L.contains (a0, a1, a2, a3, a4)

theorem chkAll_true : chkAllOf d1Tup = true := by decide +kernel

theorem d1Tup_length : d1Tup.length = 26 := by decide +kernel

theorem mem_vals {a : ℤ} (h0 : 0 ≤ a) (h4 : a ≤ 4) : a ∈ d1Vals := by
  unfold d1Vals
  interval_cases a <;> simp

theorem chkAll_sound {L : List (ℤ × ℤ × ℤ × ℤ × ℤ)} (hL : chkAllOf L = true) (a0 a1 a2 a3 a4 : ℤ)
    (h0 : a0 ∈ d1Vals) (h1 : a1 ∈ d1Vals) (h2 : a2 ∈ d1Vals) (h3 : a3 ∈ d1Vals) (h4 : a4 ∈ d1Vals)
    (hc : d1Chk a0 a1 a2 a3 a4 = true) : (a0, a1, a2, a3, a4) ∈ L := by
  unfold chkAllOf at hL
  simp only [List.all_eq_true] at hL
  have := hL a0 h0 a1 h1 a2 h2 a3 h3 a4 h4
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with h | h
  · rw [h] at hc; exact absurd hc (by decide)
  · simpa using h

theorem gcd_prim (h : V5) (hp : Primitive h) :
    Nat.gcd (Nat.gcd (Nat.gcd (Nat.gcd (h 0).natAbs (h 1).natAbs) (h 2).natAbs) (h 3).natAbs) (h 4).natAbs = 1 := by
  set g := Nat.gcd (Nat.gcd (Nat.gcd (Nat.gcd (h 0).natAbs (h 1).natAbs) (h 2).natAbs) (h 3).natAbs) (h 4).natAbs with hg
  have d4 : g ∣ (h 4).natAbs := Nat.gcd_dvd_right _ _
  have d3 : g ∣ (h 3).natAbs := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have d2 : g ∣ (h 2).natAbs := ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_right _ _)
  have d1 : g ∣ (h 1).natAbs :=
    (((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_right _ _)
  have d0 : g ∣ (h 0).natAbs :=
    (((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_left _ _)
  have key : ∀ i, (g : ℤ) ∣ h i := by
    intro i
    fin_cases i
    · exact Int.natCast_dvd.2 d0
    · exact Int.natCast_dvd.2 d1
    · exact Int.natCast_dvd.2 d2
    · exact Int.natCast_dvd.2 d3
    · exact Int.natCast_dvd.2 d4
  rcases hp g key with e | e
  · exact_mod_cast e
  · omega

theorem dot_five (h : V5) : dot h h = h 0 * h 0 + h 1 * h 1 + h 2 * h 2 + h 3 * h 3 + h 4 * h 4 := by
  simp [dot, Fin.sum_univ_five]

/-- Every depth-1 vector `T1Ok h` is a stored vector. -/
theorem t1_complete (h : V5) (hT : T1Ok h) : ∃ r ∈ d1Data, r.h = h := by
  obtain ⟨hs, hb, hp, h2, h18⟩ := hT
  have hge : ∀ i, 0 ≤ h i := fun i => (hs i i le_rfl).1
  have hmon : ∀ i j : Fin 5, i ≤ j → h i ≤ h j := fun i j hij => (hs i j hij).2
  have hc : d1Chk (h 0) (h 1) (h 2) (h 3) (h 4) = true := by
    rw [dot_five] at h2 h18
    have e01 := hmon 0 1 (by decide)
    have e12 := hmon 1 2 (by decide)
    have e23 := hmon 2 3 (by decide)
    have e34 := hmon 3 4 (by decide)
    have g1 := gcd_prim h hp
    simp [d1Chk, e01, e12, e23, e34, h2, h18, g1]
  have hm := chkAll_sound chkAll_true (h 0) (h 1) (h 2) (h 3) (h 4)
    (mem_vals (hge 0) (hb 0)) (mem_vals (hge 1) (hb 1)) (mem_vals (hge 2) (hb 2))
    (mem_vals (hge 3) (hb 3)) (mem_vals (hge 4) (hb 4)) hc
  unfold d1Tup at hm
  simp only [List.mem_map, Prod.mk.injEq] at hm
  obtain ⟨r, hr, e0, e1, e2, e3, e4⟩ := hm
  refine ⟨r, hr, ?_⟩
  funext i
  fin_cases i <;> simp [e0, e1, e2, e3, e4]

/-! ## 3. `StreamHyp'.t1` -/

/-- **The depth-1 checker is sound for `t1`.**  Every sorted depth-1 vector is the first row of a stored node. -/
theorem d1_t1 : ∀ h : V5, T1Ok h → ∃ n ∈ R1d1, hN n.rows 0 = h := by
  intro h hT
  obtain ⟨r, hr, e⟩ := t1_complete h hT
  have hok := d1Data_ok r hr
  exact ⟨nodeOfRaw r hok, ⟨r, hr, hok, rfl⟩, by rw [nodeOfRaw_row0, e]⟩

/-! ## 4. Planted controls -/

/-- A corrupted record (`b_0` changed): the node identities fail. -/
def badB : D1Raw := match d1Data with
  | r :: _ => { r with b := fun i => if i = 0 then ![1, 1, 1, 1, 1] else r.b i }
  | [] => default_d1
where default_d1 : D1Raw := { h := ![0, 0, 0, 0, 0], b := fun _ => ![0, 0, 0, 0, 0], s := ![0, 0, 0, 0, 0],
                               r := fun _ => ![0, 0, 0, 0, 0], x := ![0, 0, 0, 0, 0], w := 1 }

theorem ctl_badB : ¬ badB.ok := by decide +kernel

/-- A corrupted witness (`w` doubled so that `c_1 <= 1/5` fails the strict test). -/
def badW : D1Raw := match d1Data with
  | r :: _ => { r with w := 5 * r.w }
  | [] => badB.default_d1

theorem ctl_badW : ¬ badW.ok := by decide +kernel

/-- Dropping one stored vector breaks the completeness loop. -/
theorem ctl_dropped : chkAllOf (d1Tup.drop 1) = false := by decide +kernel

/-- Control on the Boolean candidate test: the unit vector and an over-long vector are rejected, a stored one accepted. -/
theorem ctl_chk : d1Chk 0 0 0 0 1 = false ∧ d1Chk 1 2 3 4 5 = false ∧ d1Chk 0 0 0 1 1 = true := by decide +kernel

end L5S4
end LRSpectrumFull
