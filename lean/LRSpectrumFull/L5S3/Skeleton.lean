/-
# L5S3.Skeleton : statements of the flag-geometry chain for five speeds

Part A of the flag-geometry development.  Statements of the data and of the lemma chain;
the pieces not yet proved are NAMED HYPOTHESES (the fields of the `Prop`-structure `FlagGeometry`), not
`sorry` and not axioms.  Everything stated as a `theorem` here is proved from them.

Data over `ℤ^5`:  `V5`, `dot`, `Primitive`, `FlagData v` (integer rows `h` of a saturated basis of
`Λ = ℤ⁵ ∩ v^⊥`, integer right inverse `R` with `H R = I`, integer Gram matrix `gram`, rational LDL
certificate `Lq, Dq` with `Dq i = μ_i²`), `Greedy` (successive minimal projected Gram determinants),
`leadMinor` (integer Gram minors `G_j`).

Chain (flag transference lemma):
 1. `babai_round` (proved, `Babai.lean`)  -->  `stage_dist` (field; instantiation to the flag: WP3 rest)
 2. `ML_ge_of_close` (proved here)  :  `stage_dist` gives `stage_bound`
        `ML v ≥ f x - (1/2) sqrt (S_k)`  for every `x` with `H_k x ∈ ℤ`          (test (i), Lemma B)
 3. `stage_prune` (proved): `ML v < 1/5`, `1/5 ≤ c ≤ f x`  ==>  `4 (c - 1/5)² < S_k`  (stage bound with
    `m_k = M(L_k) - 1/5 ≥ 0`; `stage_prune_M` for `M(L_k)` itself when the sup is attained)
 4. test (ii) `ratio34` (field)  : `μ²_{i+1} ≥ (3/4) μ²_i`; iterated tail constants in `LayerStep.tail_sum`
 5. test (iii) `window_lo` (proved from the field), `leaf_strand` (proved): the leaf window for `μ_4²`.

Not here (what remains of S3): `flag_exists` with saturation, `Dq_minors`, `ratio34`, `covolume`,
`stage_dist` as theorems; integer-minor form `Ratio34Int`; the instantiation to the greedy flag of a real `v`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.MaxLoneliness
import LRSpectrumFull.ObsCrystallographic
import LRSpectrumFull.L5S3.Babai
import LRSpectrumFull.L5S3.LayerStep
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace LRSpectrumFull
namespace L5S3

open Finset

/-! ## Section 1: integer data over `ℤ^5` -/

/-- Integer speed vectors of five runners. -/
abbrev V5 := Fin 5 → ℤ

/-- Standard integer dot product. -/
def dot (a b : V5) : ℤ := ∑ i, a i * b i

/-- `v` is primitive: the only common integer divisors of the entries are `±1`. -/
def Primitive (v : V5) : Prop := ∀ d : ℤ, (∀ i, d ∣ v i) → d = 1 ∨ d = -1

/-- A saturated flag basis of `Λ = ℤ⁵ ∩ v^⊥` with its integer and rational certificates:
rows `h i ∈ Λ`, integer right inverse `R` (`H R = I₄`, saturation), and the LDL certificate
`G = Lq · diag Dq · Lqᵀ` of the integer Gram matrix over `ℚ` (`Dq i = μ_i²`). -/
structure FlagData (v : V5) where
  h : Fin 4 → V5
  R : Fin 5 → Fin 4 → ℤ
  hv : ∀ i, dot (h i) v = 0
  hR : ∀ i j : Fin 4, ∑ k : Fin 5, h i k * R k j = if i = j then 1 else 0
  Lq : Fin 4 → Fin 4 → ℚ
  Dq : Fin 4 → ℚ
  hLunit : ∀ i, Lq i i = 1
  hLlow : ∀ i j, i < j → Lq i j = 0
  hDpos : ∀ i, 0 < Dq i
  hLDL : ∀ i j, (dot (h i) (h j) : ℚ) = ∑ k, Lq i k * Dq k * Lq j k

/-- The integer Gram matrix of the flag basis. -/
def gram {v : V5} (F : FlagData v) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => dot (F.h i) (F.h j)

/-- Leading `j × j` minor `G_j` of an integer `4 × 4` matrix (padded with the identity so that no
dependent `Fin` arithmetic is needed; `G_0 = 1`). -/
def leadMinor (M : Matrix (Fin 4) (Fin 4) ℤ) (j : ℕ) : ℤ :=
  (Matrix.of fun a b : Fin 4 =>
    if a.val < j ∧ b.val < j then M a b else if a = b then 1 else 0).det

/-- Gram determinant of a list of vectors. -/
def gramDetList (l : List V5) : ℤ :=
  (Matrix.of fun a b : Fin l.length => dot (l.get a) (l.get b)).det

/-- `u` lies in the rational span of the first `j` rows of `h`. -/
def InQSpanPrefix (h : Fin 4 → V5) (j : ℕ) (u : V5) : Prop :=
  ∃ c : Fin 4 → ℚ, ∀ k : Fin 5,
    (u k : ℚ) = ∑ i : Fin 4, if i.val < j then c i * (h i k : ℚ) else 0

/-- Greedy flag: at each step `j < 4` the next row minimises the Gram determinant
(= squared distance to the span of the previous rows, up to the previous covolume) over all
vectors of `Λ` outside that span. -/
def Greedy (v : V5) (h : Fin 4 → V5) : Prop :=
  ∀ j : ℕ, j < 4 → ∀ u : V5, dot u v = 0 → ¬ InQSpanPrefix h j u →
    gramDetList ((List.ofFn h).take (j + 1)) ≤ gramDetList (((List.ofFn h).take j) ++ [u])

/-- Test (ii) in integer-minor form: `μ²_{j+1} ≥ (3/4) μ²_j`, i.e. `3 G_j² ≤ 4 G_{j+1} G_{j-1}`. -/
def Ratio34Int {v : V5} (F : FlagData v) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
    3 * (leadMinor (gram F) j) ^ 2 ≤ 4 * leadMinor (gram F) (j + 1) * leadMinor (gram F) (j - 1)

/-! ## Section 2: real data -/

/-- `f x = min_i ‖x_i‖` on `ℝ⁵`; `gap v t = f (v t)`. -/
noncomputable def fmin (x : Fin 5 → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => nearestIntDist (x i))

theorem gap_eq_fmin (v : V5) (t : ℝ) : gap v t = fmin (fun i => (v i : ℝ) * t) := rfl

theorem fmin_le_nd (x : Fin 5 → ℝ) (i : Fin 5) : fmin x ≤ nearestIntDist (x i) :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem fmin_le_half (x : Fin 5 → ℝ) : fmin x ≤ 1 / 2 :=
  (fmin_le_nd x 0).trans (nearestIntDist_le_half _)

/-- The tail sum `S_k = ∑_{i ≥ k} 1 / μ_{i+1}²` (0-based `i`). -/
noncomputable def Sk {v : V5} (F : FlagData v) (k : ℕ) : ℝ :=
  ∑ i : Fin 4, if k ≤ i.val then 1 / (F.Dq i : ℝ) else 0

theorem Sk_nonneg {v : V5} (F : FlagData v) (k : ℕ) : 0 ≤ Sk F k := by
  unfold Sk
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · have : (0 : ℝ) < (F.Dq i : ℝ) := by exact_mod_cast F.hDpos i
    positivity
  · exact le_refl _

/-- `x` is a point of the stage torus `T(L_k)`: `⟨h_i, x⟩ ∈ ℤ` for `i < k`. -/
def StageWitness {v : V5} (F : FlagData v) (k : ℕ) (x : Fin 5 → ℝ) : Prop :=
  ∀ i : Fin 4, i.val < k → ∃ n : ℤ, ∑ j, (F.h i j : ℝ) * x j = n

/-- `M(L_k) = sup { f x : x ∈ T(L_k) }` (a supremum; it is attained, a later compactness lemma). -/
noncomputable def Mlat {v : V5} (F : FlagData v) (k : ℕ) : ℝ :=
  sSup {y | ∃ x, StageWitness F k x ∧ y = fmin x}

theorem le_Mlat {v : V5} (F : FlagData v) (k : ℕ) (x : Fin 5 → ℝ) (hx : StageWitness F k x) :
    fmin x ≤ Mlat F k := by
  apply le_csSup
  · exact ⟨1 / 2, by rintro y ⟨x', _, rfl⟩; exact fmin_le_half x'⟩
  · exact ⟨x, hx, rfl⟩

/-! ## Section 3: the transference step (proved) -/

/-- If `x` is within `R` of `ℤ⁵ + ℝ v` (the point `z + t v`), then `ML v ≥ f x - R`. -/
theorem ML_ge_of_close (v : V5) (x : Fin 5 → ℝ) (z : V5) (t R : ℝ)
    (hR : 0 ≤ R) (h : ∑ j, (x j - z j - t * v j) ^ 2 ≤ R ^ 2) : fmin x - R ≤ ML v := by
  have hgap : fmin x - R ≤ gap v t := by
    apply le_gap
    intro i
    have hyi : |x i - z i - t * v i| ≤ R := by
      have h1 : (x i - z i - t * v i) ^ 2 ≤ R ^ 2 :=
        le_trans (Finset.single_le_sum (f := fun j => (x j - z j - t * v j) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)) h
      exact abs_le.mpr (abs_le_of_sq_le_sq' h1 hR)
    have h2 := ObsCrystallographic.nd_le_add (x i - z i) (t * v i - (x i - z i))
    have e1 : x i - z i + (t * v i - (x i - z i)) = (v i : ℝ) * t := by ring
    rw [e1] at h2
    have e2 : nearestIntDist (x i - z i) = nearestIntDist (x i) := by
      have := nearestIntDist_add_int (x i) (-(z i))
      simpa [sub_eq_add_neg] using this
    have e3 : |t * v i - (x i - z i)| = |x i - z i - t * v i| := by
      rw [abs_sub_comm]
    rw [e2, e3] at h2
    have := fmin_le_nd x i
    linarith
  exact hgap.trans (le_csSup (bddAbove_range_gap v) ⟨t, rfl⟩)

/-! ## Section 4: the chain, with the unproved pieces as named hypotheses -/

/-- Named hypotheses of the flag transference lemma (statements only; each is to be discharged by a
later block).  `stage_dist` is the instantiation of `babai_round` to the flag (needs: kernel of `H` is
`ℝ v`, `H R = I`, the LDL certificate). -/
structure FlagGeometry : Prop where
  /-- flag existence with saturation (integer, `Nat.find` on Gram determinants) -/
  flag_exists : ∀ v : V5, Primitive v → ∃ F : FlagData v, Greedy v F.h
  /-- the LDL diagonal is the ratio of consecutive integer Gram minors -/
  Dq_minors : ∀ (v : V5) (F : FlagData v) (i : Fin 4),
    F.Dq i = (leadMinor (gram F) (i.val + 1) : ℚ) / (leadMinor (gram F) i.val : ℚ)
  /-- test (ii): `μ²_{i+1} ≥ (3/4) μ²_i` for a greedy flag -/
  ratio34 : ∀ (v : V5) (F : FlagData v), Greedy v F.h → ∀ i : Fin 3,
    (3 / 4 : ℚ) * F.Dq i.castSucc ≤ F.Dq i.succ
  /-- covolume identity `∏ μ_i² = |v|²` (saturated basis of `v^⊥`, `v` primitive) -/
  covolume : ∀ (v : V5) (F : FlagData v), Primitive v → (∏ i, F.Dq i) = (dot v v : ℚ)
  /-- nearest-plane distance to `ℤ⁵ + ℝ v` at stage `k` (`babai_round` instantiated) -/
  stage_dist : ∀ (v : V5) (F : FlagData v) (k : ℕ) (x : Fin 5 → ℝ), Primitive v →
    StageWitness F k x →
    ∃ (z : V5) (t : ℝ), ∑ j, (x j - z j - t * v j) ^ 2 ≤ 1 / 4 * Sk F k

/-- Test (i), Lemma B: `ML v ≥ f x - (1/2) sqrt S_k` for `x ∈ T(L_k)`. -/
theorem stage_bound (G : FlagGeometry) (v : V5) (F : FlagData v) (k : ℕ) (x : Fin 5 → ℝ)
    (hv : Primitive v) (hx : StageWitness F k x) :
    fmin x - 1 / 2 * Real.sqrt (Sk F k) ≤ ML v := by
  obtain ⟨z, t, h⟩ := G.stage_dist v F k x hv hx
  have hS := Sk_nonneg F k
  apply ML_ge_of_close v x z t _ (by positivity)
  have : (1 / 2 * Real.sqrt (Sk F k)) ^ 2 = 1 / 4 * Sk F k := by
    rw [mul_pow, Real.sq_sqrt hS]; ring
  rw [this]; exact h

/-- Stage pruning: if `ML v < 1/5` and `x ∈ T(L_k)` has `f x ≥ c ≥ 1/5`, then `4 (c - 1/5)² < S_k`.
(The side condition `1/5 ≤ c`, i.e. `m_k ≥ 0`, is carried by the witness; no LRC input.) -/
theorem stage_prune (G : FlagGeometry) (v : V5) (F : FlagData v) (k : ℕ) (x : Fin 5 → ℝ)
    (hv : Primitive v) (hx : StageWitness F k x) (hlt : ML v < 1 / 5) (c : ℝ)
    (hc : 1 / 5 ≤ c) (hfc : c ≤ fmin x) : 4 * (c - 1 / 5) ^ 2 < Sk F k := by
  have hb := stage_bound G v F k x hv hx
  have hS := Sk_nonneg F k
  have h1 : 2 * (c - 1 / 5) < Real.sqrt (Sk F k) := by linarith
  have h2 : (2 * (c - 1 / 5)) ^ 2 < Real.sqrt (Sk F k) ^ 2 :=
    pow_lt_pow_left₀ h1 (by linarith) (by norm_num)
  rw [Real.sq_sqrt hS] at h2
  nlinarith

/-- The same with `m_k = M(L_k) - 1/5 ≥ 0` itself, assuming the supremum is attained. -/
theorem stage_prune_M (G : FlagGeometry) (v : V5) (F : FlagData v) (k : ℕ) (hv : Primitive v)
    (hlt : ML v < 1 / 5) (hatt : ∃ x, StageWitness F k x ∧ fmin x = Mlat F k)
    (hm : 1 / 5 ≤ Mlat F k) : 4 * (Mlat F k - 1 / 5) ^ 2 < Sk F k := by
  obtain ⟨x, hx, hxe⟩ := hatt
  exact stage_prune G v F k x hv hx hlt (Mlat F k) hm hxe.ge

/-- Test (iii), leaf strand: `4 (c - 1/5)² < 1 / μ_4²` (stage `k = 3`). -/
theorem leaf_strand (G : FlagGeometry) (v : V5) (F : FlagData v) (x : Fin 5 → ℝ)
    (hv : Primitive v) (hx : StageWitness F 3 x) (hlt : ML v < 1 / 5) (c : ℝ)
    (hc : 1 / 5 ≤ c) (hfc : c ≤ fmin x) : 4 * (c - 1 / 5) ^ 2 < 1 / (F.Dq 3 : ℝ) := by
  have h := stage_prune G v F 3 x hv hx hlt c hc hfc
  have e : Sk F 3 = 1 / (F.Dq 3 : ℝ) := by
    simp [Sk, Fin.sum_univ_four]
  rwa [e] at h

/-- Test (iii), lower window for `μ_4²`: `μ_4² ≥ (3/4) μ_3²` for a greedy flag. -/
theorem window_lo (G : FlagGeometry) (v : V5) (F : FlagData v) (hg : Greedy v F.h) :
    (3 / 4 : ℚ) * F.Dq 2 ≤ F.Dq 3 := G.ratio34 v F hg (2 : Fin 3)

end L5S3
end LRSpectrumFull
