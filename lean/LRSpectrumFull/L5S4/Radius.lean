/-
# L5S4.Radius : E9, the division-form radius test of `lib.rs` versus `NodeBound`, and the rational witness evaluator

`lib.rs::radius_bound(ms, inv, r, C, ks)` is `min` over the `k ∈ ks` with `den_k > 0` of `C / den_k`,
`den_k = 4 m_k² − ∑_{k<i<r} inv_i`, `inv_i = gs[i-1]/gs[i]`, `m_k = c_k − 1/5`, with exact fractions; `children`
accepts `t` iff `q · bd < bn · g` where `bn/bd` is that minimum and `μ² = q/g`.  `cert.rs::check` computes
`c_k = witness_ok(l, x, w) = min_i ‖x_i / w‖` from the record `(x, w)`.

* Evaluator: `nd_rat` (`‖X/W‖ = min(X mod W, W − X mod W)/W`), `wMin`, `fmin_rat`, `WitnessOk`
  (= `witness_ok`: `W > 0` and `W ∣ h_i · X`, `i < k`), `stage_of_ok` (`WitnessOk → StageWitness` of the point `X/W`).
* Division form: `node_div_iff`, `int_lt_rat`, `accept_iff` : the integer comparison `q·bd < bn·g` with the fraction
  `bn/bd` of `radius_bound` is equivalent to `∀ k<d, 4 m_k² < S_k + C · (g/q)`, i.e. the node test of every stage.
* Bridge to the flag: `nodeRHS_rat` : `nodeRHS F d k` is the rational `ratRHS` in the leading Gram minors `G_i`
  (`G_{i-1}/G_i = inv_i = 1/μ_i²`), the numbers the generator keeps in `gs`.
* `nodeBound_to_rat` : `NodeBound F d` implies the checker's rational inequality at every checkable witness.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.Chain
import LRSpectrumFull.L5S3.Accepted

namespace LRSpectrumFull
namespace L5S4

open Finset LRSpectrumFull.L5S3

/-! ## evaluator -/

theorem fract_div_int (X W : ℤ) (hW : 0 < W) : Int.fract ((X : ℝ) / W) = ((X % W : ℤ) : ℝ) / W := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : (X : ℝ) = W * ((X / W : ℤ) : ℝ) + ((X % W : ℤ) : ℝ) := by
    exact_mod_cast (Int.mul_ediv_add_emod X W).symm
  have e : (X : ℝ) / W = ((X / W : ℤ) : ℝ) + ((X % W : ℤ) : ℝ) / W := by
    field_simp
    linarith
  rw [e, Int.fract_intCast_add]
  apply Int.fract_eq_self.2
  have h0 : (0 : ℤ) ≤ X % W := Int.emod_nonneg X hW.ne'
  have h2 : X % W < W := Int.emod_lt_of_pos X hW
  constructor
  · positivity
  · rw [div_lt_one hWr]; exact_mod_cast h2

theorem nd_rat (X W : ℤ) (hW : 0 < W) :
    nearestIntDist ((X : ℝ) / W) = ((min (X % W) (W - X % W) : ℤ) : ℝ) / W := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  unfold nearestIntDist
  rw [fract_div_int X W hW]
  push_cast
  rw [← min_div_div_right hWr.le]
  congr 1
  field_simp

/-- `min_i min(X_i mod W, W − X_i mod W)` (`witness_ok`'s `mn`). -/
def wMin (X : V5) (W : ℤ) : ℤ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a => min (X a % W) (W - X a % W))

theorem fmin_rat (X : V5) (W : ℤ) (hW : 0 < W) :
    fmin (fun a => (X a : ℝ) / W) = (wMin X W : ℝ) / W := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  apply le_antisymm
  · obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin 5))
      (fun a => min (X a % W) (W - X a % W))
    have := fmin_le_nd (fun a => (X a : ℝ) / W) a
    rw [nd_rat _ _ hW] at this
    unfold wMin
    rw [ha]
    exact this
  · unfold fmin
    apply Finset.le_inf'
    intro a _
    simp only
    rw [nd_rat _ _ hW]
    apply div_le_div_of_nonneg_right _ hWr.le
    exact_mod_cast Finset.inf'_le (fun a => min (X a % W) (W - X a % W)) (Finset.mem_univ a)

/-- `witness_ok`: `W > 0` and `h_i · X ≡ 0 (mod W)` for the first `k` rows. -/
def WitnessOk {v : V5} (F : FlagData v) (k : ℕ) (X : V5) (W : ℤ) : Prop :=
  0 < W ∧ ∀ i : Fin 4, i.val < k → W ∣ dot (F.h i) X

theorem stage_of_ok {v : V5} (F : FlagData v) (k : ℕ) (X : V5) (W : ℤ) (h : WitnessOk F k X W) :
    StageWitness F k (fun a => (X a : ℝ) / W) := by
  intro i hi
  obtain ⟨m, hm⟩ := h.2 i hi
  have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast h.1.ne'
  refine ⟨m, ?_⟩
  have e : ∑ j, (F.h i j : ℝ) * ((X j : ℝ) / W) = ((dot (F.h i) X : ℤ) : ℝ) / W := by
    simp only [dot, Int.cast_sum, Int.cast_mul, Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [e, hm]
  push_cast
  field_simp

/-! ## division form -/

theorem node_div_iff (m S C mu2 : ℚ) (hC : 0 < C) (hmu : 0 < mu2) :
    4 * m ^ 2 < S + C * (1 / mu2) ↔ (4 * m ^ 2 - S ≤ 0 ∨ mu2 < C / (4 * m ^ 2 - S)) := by
  have hpos : 0 < C * (1 / mu2) := by positivity
  by_cases hd : 4 * m ^ 2 - S ≤ 0
  · constructor
    · intro _; exact Or.inl hd
    · intro _; linarith
  · push_neg at hd
    constructor
    · intro h
      right
      rw [lt_div_iff₀ hd]
      have h1 : 4 * m ^ 2 - S < C * (1 / mu2) := by linarith
      have h2 : (4 * m ^ 2 - S) * mu2 < C * (1 / mu2) * mu2 := mul_lt_mul_of_pos_right h1 hmu
      have h3 : C * (1 / mu2) * mu2 = C := by field_simp
      linarith
    · rintro (h | h)
      · linarith
      · rw [lt_div_iff₀ hd] at h
        have h2 : mu2 * (4 * m ^ 2 - S) * (1 / mu2) < C * (1 / mu2) :=
          mul_lt_mul_of_pos_right h (by positivity)
        have h3 : mu2 * (4 * m ^ 2 - S) * (1 / mu2) = 4 * m ^ 2 - S := by field_simp
        linarith

theorem int_lt_rat (q g : ℤ) (b : ℚ) (hg : 0 < g) : q * (b.den : ℤ) < b.num * g ↔ (q : ℚ) / g < b := by
  have hgq : (0 : ℚ) < g := by exact_mod_cast hg
  have hdq : (0 : ℚ) < b.den := by exact_mod_cast b.den_pos
  conv_rhs => rw [← Rat.num_div_den b]
  rw [div_lt_div_iff₀ hgq hdq]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- The integer comparison of `children` (`q · bd < bn · g`, `bn/bd = min_{den_k>0} C/den_k`) is the node test of
every stage `k < d` (stages with `den_k ≤ 0` impose nothing and are automatically satisfied). -/
theorem accept_iff (d : ℕ) (m S : ℕ → ℚ) (C : ℚ) (hC : 0 < C) (q g : ℤ) (hg : 0 < g) (hq : 0 < q)
    (hK : ((range d).filter (fun k => 0 < 4 * (m k) ^ 2 - S k)).Nonempty) :
    (q * ((((range d).filter (fun k => 0 < 4 * (m k) ^ 2 - S k)).inf' hK
        (fun k => C / (4 * (m k) ^ 2 - S k))).den : ℤ)
      < (((range d).filter (fun k => 0 < 4 * (m k) ^ 2 - S k)).inf' hK
        (fun k => C / (4 * (m k) ^ 2 - S k))).num * g)
    ↔ ∀ k < d, 4 * (m k) ^ 2 < S k + C * (1 / ((q : ℚ) / g)) := by
  have hmu : (0 : ℚ) < (q : ℚ) / g := by
    have : (0 : ℚ) < q := by exact_mod_cast hq
    have : (0 : ℚ) < g := by exact_mod_cast hg
    positivity
  rw [int_lt_rat q g _ hg, Finset.lt_inf'_iff]
  constructor
  · intro h k hk
    rw [node_div_iff _ _ C _ hC hmu]
    by_cases hd : 0 < 4 * (m k) ^ 2 - S k
    · right; exact h k (Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hd⟩)
    · left; linarith
  · intro h k hk
    have hk' := Finset.mem_filter.1 hk
    have := (node_div_iff _ _ C _ hC hmu).1 (h k (Finset.mem_range.1 hk'.1))
    rcases this with h1 | h1
    · linarith [hk'.2]
    · exact h1

/-! ## bridge to the flag -/

/-- `C_d = ∑_{s<5-d} (4/3)^s` as a rational (`175/27, 37/9, 7/3, 1`). -/
def Cq (d : ℕ) : ℚ := ∑ s ∈ range (5 - d), (4 / 3 : ℚ) ^ s

/-- The right-hand side of the node test in the leading Gram minors `G`: `∑_{k ≤ i < d-1} G_i/G_{i+1} + C_d G_{d-1}/G_d`. -/
def ratRHS (G : ℕ → ℤ) (d k : ℕ) : ℚ :=
  (∑ i ∈ range (d - 1), if k ≤ i then (G i : ℚ) / (G (i + 1) : ℚ) else 0)
    + Cq d * ((G (d - 1) : ℚ) / (G d : ℚ))

theorem Dext_minors {v : V5} (F : FlagData v) (i : ℕ) (hi : i < 4) :
    Dext F i = (((leadMinor (gram F) (i + 1) : ℤ) : ℝ)) / ((leadMinor (gram F) i : ℤ) : ℝ) := by
  have h := Dext_lt F ⟨i, hi⟩
  simp only at h
  rw [h, Dq_minors_thm v F ⟨i, hi⟩]
  push_cast
  rfl

theorem nodeRHS_rat {v : V5} (F : FlagData v) (d k : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) :
    nodeRHS F d k = ((ratRHS (fun n => leadMinor (gram F) n) d k : ℚ) : ℝ) := by
  unfold nodeRHS ratRHS Cnode Cq
  push_cast
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_range.1 hi
    by_cases hk : k ≤ i
    · simp only [hk, if_true]
      rw [Dext_minors F i (by omega), one_div_div]
      simp
    · simp [hk]
  · rw [Dext_minors F (d - 1) (by omega), one_div_div]
    have : d - 1 + 1 = d := by omega
    rw [this]

/-- `NodeBound` at the checker's witness gives the checker's rational inequality: if `(X, W)` passes `witness_ok` for
stage `k < d` and `c = wMin/W ≥ 1/5`, then `4 (c − 1/5)² < ratRHS G d k` for `G` the leading Gram minors of the flag. -/
theorem nodeBound_to_rat {v : V5} (F : FlagData v) (d : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 4)
    (hNB : NodeBound F d) (k : ℕ) (hk : k < d) (X : V5) (W : ℤ) (hok : WitnessOk F k X W)
    (c : ℚ) (hcdef : c = ((wMin X W : ℤ) : ℚ) / ((W : ℤ) : ℚ)) (hc : (1 : ℚ) / 5 ≤ c) :
    4 * (c - 1 / 5) ^ 2 < ratRHS (fun n => leadMinor (gram F) n) d k := by
  have hW : (0 : ℝ) < W := by exact_mod_cast hok.1
  have hcast : ((c : ℚ) : ℝ) = (wMin X W : ℝ) / W := by rw [hcdef]; push_cast; ring
  have h := hNB k hk (fun a => (X a : ℝ) / W) ((c : ℚ) : ℝ)
    (stage_of_ok F k X W hok)
    (by have := (Rat.cast_le (K := ℝ)).2 hc; push_cast at this; exact this)
    (by rw [hcast, fmin_rat X W hok.1])
  rw [nodeRHS_rat F d k hd1 hd4] at h
  have h' : ((4 * (c - 1 / 5) ^ 2 : ℚ) : ℝ) < ((ratRHS (fun n => leadMinor (gram F) n) d k : ℚ) : ℝ) := by
    push_cast; exact h
  exact (Rat.cast_lt (K := ℝ)).1 h'

end L5S4
end LRSpectrumFull
