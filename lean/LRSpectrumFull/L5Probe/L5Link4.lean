/-
# L5 probe: table-validity lemma for the mask-table checker V4, and the link `wit4 = true -> 1/5 <= ML`

* `tablesM_valid` (kernel): every set bit `a < 64` of slot `r < q` of the table of level `q` satisfies `okAt a q r`.
* `lvlM_spec`, `wit4_spec`: the V4 test is sound for the arithmetic predicate `okAt` (soundness only, no completeness).
* `ML_ge_of_wit4`: `wit4 v0 .. v4 = true` implies `1/5 <= ML (v0, .., v4)` for the project's `ML`.
* `chunk4_spec`: `chunk4 L = true` gives the floor `1/5` for every decoded tuple of `L`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5Probe.L5Var
import LRSpectrumFull.L5Probe.L5Link

namespace L5

open LRSpectrumFull

/-! ### table validity -/

def tableValid (p : Nat × Nat) : Bool :=
  decide (0 < p.1) &&
    (List.range p.1).all (fun r => (List.range 64).all (fun a =>
      !(Nat.testBit (slot p.2 p.1 r) a) || okAt a p.1 r))

theorem tablesM_valid : tablesM.all tableValid = true := by decide +kernel

#print axioms tablesM_valid

theorem slot_lt (T q v : Nat) : slot T q v < 2 ^ 64 := by
  unfold slot
  exact Nat.mod_lt _ (by decide)

theorem slot_bit_lt (T q v a : Nat) (h : (slot T q v).testBit a = true) : a < 64 := by
  by_contra hge
  have hge' : 64 ≤ a := Nat.le_of_not_lt hge
  have hlt : slot T q v < 2 ^ a :=
    lt_of_lt_of_le (slot_lt T q v) (Nat.pow_le_pow_right (by decide) hge')
  rw [Nat.testBit_lt_two_pow hlt] at h
  exact Bool.false_ne_true h

theorem okAt_mod (a q v : Nat) : okAt a q v = okAt a q (v % q) := by
  unfold okAt
  have : v * a % q = (v % q) * a % q := by
    rw [Nat.mul_mod v a q, Nat.mul_mod (v % q) a q, Nat.mod_mod]
  rw [this]

theorem slot_mod (T q v : Nat) : slot T q v = slot T q (v % q) := by
  unfold slot
  rw [Nat.mod_mod]

/-- one valid table: a set bit in the slot of `v` is a genuine `okAt` -/
theorem tableValid_spec {p : Nat × Nat} (hv : tableValid p = true) (v a : Nat)
    (h : (slot p.2 p.1 v).testBit a = true) : 0 < p.1 ∧ okAt a p.1 v = true := by
  unfold tableValid at hv
  rw [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hq, hall⟩ := hv
  refine ⟨hq, ?_⟩
  have hr : v % p.1 < p.1 := Nat.mod_lt _ hq
  have ha : a < 64 := slot_bit_lt _ _ _ _ h
  rw [List.all_eq_true] at hall
  have h1 := hall (v % p.1) (List.mem_range.mpr hr)
  rw [List.all_eq_true] at h1
  have h2 := h1 a (List.mem_range.mpr ha)
  rw [slot_mod] at h
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · rw [Bool.not_eq_true'] at h2
    rw [h] at h2
    exact absurd h2 (by decide)
  · rw [okAt_mod]; exact h2

/-! ### the V4 level test -/

theorem lvlM_spec {q T v0 v1 v2 v3 v4 : Nat} (hv : tableValid (q, T) = true)
    (h : lvlM q T v0 v1 v2 v3 v4 = true) :
    ∃ a, 0 < q ∧ okAt a q v0 = true ∧ okAt a q v1 = true ∧ okAt a q v2 = true ∧
      okAt a q v3 = true ∧ okAt a q v4 = true := by
  unfold lvlM at h
  rw [Bool.not_eq_true', Bool.eq_false_iff] at h
  have hne : Nat.land (Nat.land (Nat.land (Nat.land (slot T q v0) (slot T q v1)) (slot T q v2))
      (slot T q v3)) (slot T q v4) ≠ 0 := fun hh => h (by rw [hh]; exact Nat.beq_refl 0)
  obtain ⟨a, ha⟩ := Nat.exists_testBit_of_ne_zero hne
  have e : ∀ x y : Nat, (Nat.land x y).testBit a = (x.testBit a && y.testBit a) :=
    fun x y => Nat.testBit_and x y a
  rw [e, e, e, e] at ha
  simp only [Bool.and_eq_true] at ha
  obtain ⟨⟨⟨⟨b0, b1⟩, b2⟩, b3⟩, b4⟩ := ha
  have s0 := tableValid_spec (p := (q, T)) hv v0 a b0
  have s1 := tableValid_spec (p := (q, T)) hv v1 a b1
  have s2 := tableValid_spec (p := (q, T)) hv v2 a b2
  have s3 := tableValid_spec (p := (q, T)) hv v3 a b3
  have s4 := tableValid_spec (p := (q, T)) hv v4 a b4
  exact ⟨a, s0.1, s0.2, s1.2, s2.2, s3.2, s4.2⟩

theorem recAny_spec (v0 v1 v2 v3 v4 : Nat) :
    ∀ L : List (Nat × Nat), L.all tableValid = true →
      (List.rec (motive := fun _ => Bool) false
        (fun p _ ih => lvlM p.1 p.2 v0 v1 v2 v3 v4 || ih) L) = true →
      ∃ a q : Nat, 0 < q ∧ okAt a q v0 = true ∧ okAt a q v1 = true ∧ okAt a q v2 = true ∧
        okAt a q v3 = true ∧ okAt a q v4 = true := by
  intro L
  induction L with
  | nil =>
    intro _ h
    have h' : (false : Bool) = true := h
    exact absurd h' Bool.false_ne_true
  | cons p L ih =>
    intro hall h
    rw [List.all_cons, Bool.and_eq_true] at hall
    have h' : (lvlM p.1 p.2 v0 v1 v2 v3 v4 || List.rec (motive := fun _ => Bool) false
        (fun p _ ih => lvlM p.1 p.2 v0 v1 v2 v3 v4 || ih) L) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · obtain ⟨a, hq, r0, r1, r2, r3, r4⟩ := lvlM_spec (q := p.1) (T := p.2) hall.1 h'
      exact ⟨a, p.1, hq, r0, r1, r2, r3, r4⟩
    · exact ih hall.2 h'

theorem wit4_spec {v0 v1 v2 v3 v4 : Nat} (h : wit4 v0 v1 v2 v3 v4 = true) :
    ∃ a q : Nat, 0 < q ∧ okAt a q v0 = true ∧ okAt a q v1 = true ∧ okAt a q v2 = true ∧
      okAt a q v3 = true ∧ okAt a q v4 = true :=
  recAny_spec v0 v1 v2 v3 v4 tablesM tablesM_valid h

/-! ### link to the project's `ML` -/

theorem ML_ge_of_okAt (v : Fin 5 → ℕ) {a q : ℕ} (hq : 0 < q)
    (h0 : okAt a q (v 0) = true) (h1 : okAt a q (v 1) = true) (h2 : okAt a q (v 2) = true)
    (h3 : okAt a q (v 3) = true) (h4 : okAt a q (v 4) = true) :
    (1 : ℝ) / 5 ≤ ML (fun i => (v i : ℤ)) := by
  have key : ∀ i : Fin 5,
      (1 : ℝ) / 5 ≤ nearestIntDist ((((fun i => (v i : ℤ)) i : ℤ) : ℝ) * ((a : ℝ) / q)) := by
    intro i
    simp only [Int.cast_natCast]
    obtain ⟨j, hj⟩ := i
    have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hj5 with rfl | rfl | rfl | rfl | rfl
    · exact okAt_real hq h0
    · exact okAt_real hq h1
    · exact okAt_real hq h2
    · exact okAt_real hq h3
    · exact okAt_real hq h4
  have hg : (1 : ℝ) / 5 ≤ gap (fun i => (v i : ℤ)) ((a : ℝ) / q) := le_gap _ _ _ key
  exact le_trans hg (le_csSup (bddAbove_range_gap _) ⟨_, rfl⟩)

/-- **Link for V4.**  The mask-table test gives the floor `1/5` for the project's `ML`. -/
theorem ML_ge_of_wit4 (v : Fin 5 → ℕ) (h : wit4 (v 0) (v 1) (v 2) (v 3) (v 4) = true) :
    (1 : ℝ) / 5 ≤ ML (fun i => (v i : ℤ)) := by
  obtain ⟨a, q, hq, h0, h1, h2, h3, h4⟩ := wit4_spec h
  exact ML_ge_of_okAt v hq h0 h1 h2 h3 h4

theorem allR_spec (f : Nat → Bool) :
    ∀ L : List Nat, allR f L = true → ∀ n ∈ L, f n = true := by
  intro L
  induction L with
  | nil => intro _ n hn; exact absurd hn (by simp)
  | cons m L ih =>
    intro h n hn
    have h' : (f m && allR f L) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hn with rfl | hn
    · exact h'.1
    · exact ih h'.2 n hn

/-- decoded tuple of a packed `Nat` (base 1024) -/
def tupleOf (n : Nat) (i : Fin 5) : ℕ :=
  match i with
  | ⟨0, _⟩ => n % 1024
  | ⟨1, _⟩ => n / 1024 % 1024
  | ⟨2, _⟩ => n / 1048576 % 1024
  | ⟨3, _⟩ => n / 1073741824 % 1024
  | ⟨_, _⟩ => n / 1099511627776 % 1024

theorem chunk4_spec (L : List Nat) (h : chunk4 L = true) :
    ∀ n ∈ L, (1 : ℝ) / 5 ≤ ML (fun i => (tupleOf n i : ℤ)) := by
  intro n hn
  have hd : dec wit4 n = true := allR_spec _ L h n hn
  have hd' : wit4 (tupleOf n 0) (tupleOf n 1) (tupleOf n 2) (tupleOf n 3) (tupleOf n 4) = true := hd
  exact ML_ge_of_wit4 (tupleOf n) hd'

#print axioms ML_ge_of_witness
#print axioms ML_ge_of_wit4
#print axioms wit4_spec
#print axioms tableValid_spec
#print axioms chunk4_spec

end L5
